// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The prover (SPEC.md §3–§8), phase by phase, on a leanVM 42422001 trace: `C1`, the challenges, Flock, the heap
//! and the quotients, `C2`, the values at `t`, the batching sumcheck, and the openings.
//!
//! It writes the stream the verifier reads (`crate::verifier::reduce`, through the contract's Keccak-256 chain) and
//! one WHIR opening per commitment. Before the batching sumcheck it runs the verifier itself on the stream so far
//! (weighted mode, which reads nothing after `ρ`) to learn the combined claims, as any prover may.

use std::time::Instant;

use fiat_shamir::merkle::Hash;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::layout::{Form, OP_BLAKE2S, OP_JUMP, SEP_MEM, tables};
use leanvm_flock_gas::transcript::{Checks, KeccakChannel, KeccakWriter, keccak_seed};
use primitives::field::{F64, F192};

use super::bus::{Bus, all_leaves, expected_root, heap};
use super::columns::{c1_polys, setup_polys};
use super::flock::FlockWitness;
use super::opening::{self, Committed};
use super::poly::{eval_e, eval_k, from_v, novel_from_values, subset_sums, to_v};
use super::quotients::{self, Quotient};
use super::stack::{Stack, c1_columns, c2_columns};
use super::trace::Trace;
use crate::claims::{Column, Combined, Commitment};
use crate::contract::NAME;
use crate::heap::Leaves;
use crate::stacks::StackLayout;
use crate::verifier::{Blake2s, Claims, Opening, chunks, reduce, sent_columns};

/// What a proof is: the verifier's stream (calldata after the selector and the public input) and one WHIR opening
/// per commitment, with the point claim it proves.
pub struct Proof {
    pub stream: Vec<u8>,
    pub openings: Vec<OpeningProof>,
}

pub struct OpeningProof {
    pub commitment: Commitment,
    pub root: Hash,
    pub vars: usize,
    pub placed: u64,
    pub point: Vec<F192>,
    pub value: F192,
    pub proof: fiat_shamir::transcript::Proof,
}

/// The `PCS_OPEN` layout word of each commitment (`crate::contract`'s).
pub fn layout_word(commitment: Commitment) -> u64 {
    match commitment {
        Commitment::C1 => 0x5501,
        Commitment::C2 => 0x5502,
        Commitment::Setup => 0x5503,
    }
}

/// Every quotient's degree against the count the verifier declares, every stack's size, and the time of each phase.
#[derive(Default, Debug)]
pub struct Report {
    pub phases: Vec<(&'static str, f64)>,
    /// (name, actual degree, the verifier's count, the extension's variables).
    pub quotients: Vec<(String, i64, u64, usize)>,
    /// (commitment, words placed, stack variables).
    pub stacks: Vec<(Commitment, u64, usize)>,
    /// Per relation family checked at `t` directly: (name, holds).
    pub checks: Vec<(String, bool)>,
    pub stream_bytes: usize,
    pub opening_bytes: Vec<usize>,
    /// Flock's claim on `A0`, `B0`: the point and the two values.
    pub flock: Option<(Vec<E>, E, E)>,
}

struct Clock {
    last: Instant,
}

impl Clock {
    fn lap(&mut self, report: &mut Report, name: &'static str) {
        let now = Instant::now();
        report.phases.push((name, (now - self.last).as_secs_f64()));
        self.last = now;
    }
}

/// The root's two 128-bit halves as the stream carries them: the 32 bytes as they are.
fn halves(root: &Hash) -> [E; 2] {
    let half = |b: &[u8]| {
        E::new(
            u64::from_be_bytes(b[8..16].try_into().unwrap()),
            u64::from_be_bytes(b[0..8].try_into().unwrap()),
            0,
        )
    };
    [half(&root[..16]), half(&root[16..])]
}

/// `tuple`'s fingerprint needs a sent value: one of its monomials reads an unsent column (`verifier::linearise`).
fn reads_unsent(tuple: &[Form], sent: &[bool]) -> bool {
    tuple.iter().any(|form| {
        form.terms()
            .any(|(monomial, c)| *c != E::default() && monomial.iter().any(|&i| !sent[i]))
    })
}

/// The degree of a tuple's fingerprint in the columns (`verifier::tuple_degree`).
fn tuple_degree(tuple: &[Form]) -> usize {
    tuple
        .iter()
        .flat_map(|form| form.terms().filter(|(_, c)| **c != E::default()).map(|(m, _)| m.len()))
        .max()
        .unwrap_or(0)
        .max(1)
}

/// The verifier's count of a table block's leaf quotient coefficients.
fn table_leaf_count(t: usize, n: u64, rows: u64) -> u64 {
    let table = &tables()[t];
    let pull = 1 + table.flushes.pull.iter().map(|tu| tuple_degree(tu)).sum::<usize>();
    let push: usize = table.flushes.push.iter().map(|tu| tuple_degree(tu)).sum();
    pull.max(push) as u64 * (n - 1) + (n - rows) - n + 1
}

/// The verifier's count of the constraint quotient's coefficients (`verifier::reduce`, step 5).
fn constraint_count(trace: &Trace) -> u64 {
    let mut degree = 0u64;
    for table in tables() {
        let r = trace.heights[table.opcode];
        let n = 1u64 << r;
        let rows = trace.rows[table.opcode];
        if table.opcode == OP_JUMP {
            degree = degree.max(n - 2);
        }
        let counts = table.count_columns().count() as u64;
        degree = degree.max((n - 1) * (1 + counts) + (n - rows) - n);
        if table.opcode == OP_BLAKE2S {
            degree = degree.max(r as u64 * (n / 2) - n);
        }
    }
    degree.max((1u64 << trace.log_memory) - 3) + 1
}

/// The prover's configuration.
#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub blake2s: Blake2s,
    pub claims: Claims,
    /// Check every combined claim against the committed stacks (slower).
    pub check: bool,
    /// Fill every stack's words past its blocks with pseudo-random words instead of zeros (a test that the verifier
    /// relies on nothing there).
    pub garbage: bool,
    /// Send these root halves for `C1` and `C2` instead of the commitments' (no opening can then verify): a
    /// byte-for-byte cross-check of the stream against a prover that commits nothing (`tests/prove_tiny.rs`).
    pub stand_in_roots: Option<[[E; 2]; 2]>,
}

/// Prove `trace`'s execution for the contract of `iv`; with Flock, from leanVM's Flock inputs `flock`.
pub fn prove(trace: &Trace, flock: Option<&FlockWitness>, iv: &[u8; 32], config: Config) -> Result<(Proof, Report), String> {
    let mut report = Report::default();
    let mut clock = Clock { last: Instant::now() };
    let shape = trace.shape();
    if shape.heights() != trace.heights {
        return Err(format!("leanVM's heights {:?} are not the verifier's {:?}", trace.heights, shape.heights()));
    }
    let public = trace.public_input();
    let mut writer = KeccakWriter::new(keccak_seed(&NAME, iv, &public));

    // 1. C1: every column in basis B, q_flock as values.
    let c1 = c1_polys(trace);
    let setup = setup_polys(trace);
    clock.lap(&mut report, "C1 and setup: inverse NTTs to basis B");
    let mut stack1 = Stack::new(StackLayout::new(&c1_columns(&shape)));
    stack1.put_k(Column::Qflock, &trace.qflock);
    for (t, columns) in c1.tables.iter().enumerate() {
        for (c, column) in columns.iter().enumerate() {
            stack1.put_k(Column::Table { table: t, column: c }, &column.b);
        }
        stack1.put_k(Column::Inverse(t), &c1.inverses[t].b);
    }
    for (k, column) in c1.memory.iter().enumerate() {
        stack1.put_k(Column::Memory(k), &column.b);
    }
    stack1.put_k(Column::BytecodeFinal, &c1.bytecode_final.b);
    let mut stack_f = super::setup::f_stack(&shape, &setup);
    if config.garbage {
        stack1.fill_unused(0xC1);
        stack_f.fill_unused(0xF0);
    }
    let committed1 = opening::commit(&stack1.words, stack1.layout.vars, stack1.placed());
    let committed_f = opening::commit(&stack_f.words, stack_f.layout.vars, stack_f.placed());
    report.stacks.push((Commitment::C1, stack1.placed(), stack1.layout.vars));
    report.stacks.push((Commitment::Setup, stack_f.placed(), stack_f.layout.vars));
    clock.lap(&mut report, "C1 and setup: WHIR commits");
    writer.send_root(config.stand_in_roots.map_or_else(|| halves(&committed1.root), |r| r[0]));

    // 2. The bus's and the constraints' challenges.
    let alphas: Vec<F192> = (0..4).map(|_| from_v(writer.sample())).collect();
    let beta = from_v(writer.sample());
    let gamma = from_v(writer.sample());

    // 3. Flock, on q_flock: leanVM's prover (`flock.rs`).
    if let Blake2s::Flock(variant) = config.blake2s {
        let witness = flock.ok_or("Flock needs leanVM's Flock inputs (flock.bin)")?;
        let log_n = leanvm_flock_gas::layout::BLAKE2S_R1CS_LOG_SIZE + trace.heights[OP_BLAKE2S];
        let out = super::flock::prove(&mut writer, witness, variant, log_n)?;
        report.flock = Some((out.matrices_point, out.a, out.b));
        clock.lap(&mut report, "Flock: zerocheck, lincheck, slices, matrices' reduction");
    }

    // 4. The heap.
    let bus = Bus::new(&alphas, beta);
    let leaves = all_leaves(trace, &bus)?;
    let layout = shape.heap();
    let heap_values = heap(&layout, &leaves);
    let root = expected_root(&bus, trace.log_bytecode);
    report.checks.push(("bus: the heap's root is the state boundary's ratio (push = pull)".into(), heap_values[1] == root));
    if heap_values[1] != root {
        return Err("the bus does not balance: the heap's root is not fp(final) / fp(initial)".into());
    }
    let mut heap_novel = heap_values.clone();
    novel_from_values(&mut heap_novel);
    let mut heap_b = heap_novel.clone();
    subset_sums(&mut heap_b);
    clock.lap(&mut report, "heap: leaves, products, inverse NTT");

    // 5. The quotients.
    let tree = quotients::tree(&heap_novel);
    report.quotients.push(("tree".into(), tree.degree, tree.count, layout.h + 1));
    clock.lap(&mut report, "quotient: tree");
    let mut leaf_quotients: Vec<(usize, Quotient)> = Vec::new();
    for (index, block) in layout.blocks.iter().enumerate() {
        let n = 1u64 << block.r;
        let values = match block.leaves {
            Leaves::Unused => continue,
            other => &leaves.iter().find(|(l, _)| *l == other).expect("leaves").1,
        };
        let mut r_novel = values.clone();
        novel_from_values(&mut r_novel);
        let (name, q) = match block.leaves {
            Leaves::Memory => ("leaf: memory".to_string(), quotients::memory_leaf(trace, &c1, &setup, &bus, &r_novel, n - 1)),
            Leaves::Bytecode => (
                "leaf: bytecode".to_string(),
                quotients::bytecode_leaf(trace, &c1, &setup, &bus, &r_novel, n - 1),
            ),
            Leaves::Table(t) => {
                let count = table_leaf_count(t, n, trace.rows[t]);
                (
                    format!("leaf: {}", leanvm_flock_gas::TABLE_NAMES[t]),
                    quotients::table_leaf(trace, t, &c1, &bus, &r_novel, count),
                )
            }
            Leaves::Unused => unreachable!(),
        };
        report
            .quotients
            .push((name, q.degree, q.count, quotients::extension_vars(q.count, block.r)));
        leaf_quotients.push((index, q));
    }
    clock.lap(&mut report, "quotients: leaves");
    let r_w = shape.constraint_vars();
    let lines = {
        let [a, b] = trace.public;
        [(F64(a[0]), F64(b[0])), (F64(a[1]), F64(b[1])), (F64::ZERO, F64::ZERO)]
    };
    let constraint = quotients::constraints(trace, &c1, gamma, r_w, constraint_count(trace), lines);
    report
        .quotients
        .push(("constraints Q_W".into(), constraint.degree, constraint.count, quotients::extension_vars(constraint.count, r_w)));
    clock.lap(&mut report, "quotient: constraints");
    for (name, degree, count, _) in &report.quotients {
        if *degree >= *count as i64 {
            return Err(format!("{name}: degree {degree} is not below the verifier's count {count}"));
        }
    }

    // 6. C2.
    let constraint_sizes = chunks(constraint.count);
    let leaf_sizes: Vec<(usize, Vec<usize>)> = leaf_quotients.iter().map(|(b, q)| (*b, chunks(q.count))).collect();
    let mut stack2 = Stack::new(StackLayout::new(&c2_columns(layout.h, &constraint_sizes, &leaf_sizes)));
    stack2.put_e(Column::Heap, &heap_b);
    let tree_chunks = tree.chunks_b(&[layout.h, 0]);
    stack2.put_e(Column::TreeQuotient(0), &tree_chunks[0]);
    stack2.put_e(Column::TreeQuotient(1), &tree_chunks[1]);
    let constraint_chunks = constraint.chunks_b(&constraint_sizes);
    for (c, chunk) in constraint_chunks.iter().enumerate() {
        stack2.put_e(Column::ConstraintQuotient(c), chunk);
    }
    for ((block, q), (_, sizes)) in leaf_quotients.iter().zip(&leaf_sizes) {
        for (chunk, part) in q.chunks_b(sizes).iter().enumerate() {
            stack2.put_e(Column::LeafQuotient { block: *block, chunk }, part);
        }
    }
    drop(leaf_quotients);
    clock.lap(&mut report, "C2: chunks in basis B");
    if config.garbage {
        stack2.fill_unused(0xC2);
    }
    let committed2 = opening::commit(&stack2.words, stack2.layout.vars, stack2.placed());
    report.stacks.push((Commitment::C2, stack2.placed(), stack2.layout.vars));
    clock.lap(&mut report, "C2: WHIR commit");
    writer.send_root(config.stand_in_roots.map_or_else(|| halves(&committed2.root), |r| r[1]));

    // 7. The point and the values at it, in the verifier's order.
    let t = from_v(writer.sample());
    let digit_count = layout.h.max(r_w + 4) + 2;
    let w: Vec<F192> = std::iter::successors(Some(t), |&x| Some(x * x + x)).take(digit_count).collect();
    let mut sent_values: Vec<F192> = Vec::new();
    let weights = &bus.weights;
    for table in tables() {
        let tcols = &c1.tables[table.opcode];
        let at: Vec<F192> = parallel::map_collect(tcols.len(), |c| primitives::multilinear::mle_eval(&tcols[c].b, &w[..tcols[c].vars()]));
        let mut sent = vec![false; table.width()];
        for c in sent_columns(&table) {
            sent_values.push(at[c]);
            sent[c] = true;
        }
        for (pulled, pushed) in table.flushes.pull.iter().zip(&table.flushes.push) {
            let fp = |tuple: &[Form]| super::fingerprint::Fingerprint::new(tuple, weights, beta).at_e(|c| at[c]);
            if reads_unsent(pulled, &sent) {
                sent_values.push(fp(pulled));
            }
            let difference: Vec<Form> = pushed
                .iter()
                .zip(pulled)
                .map(|(a, b)| {
                    let mut d = a.clone();
                    d.add_scaled(b, E::new(1, 0, 0));
                    d
                })
                .collect();
            if reads_unsent(&difference, &sent) {
                sent_values.push(fp(pushed));
            }
        }
    }
    let lm = trace.log_memory;
    let lb = trace.log_bytecode;
    let mem_at: Vec<F192> = c1.memory.iter().map(|c| eval_k(&c.b, &w[..lm])).collect();
    let address_at = eval_k(&setup.address.b, &w[..lm]);
    let memory_pull = beta
        + weights[0] * from_v(SEP_MEM)
        + weights[1] * address_at
        + weights[2] * mem_at[3]
        + (0..3).fold(F192::ZERO, |acc, k| acc + weights[3 + k] * mem_at[k]);
    sent_values.extend([mem_at[3], address_at, memory_pull]);
    let bytecode_final_at = eval_k(&c1.bytecode_final.b, &w[..lb]);
    let slots_at: Vec<F192> = setup.slots.iter().map(|s| eval_k(&s.b, &w[..lb])).collect();
    let bytecode_pull = beta
        + weights[2] * bytecode_final_at
        + (0..16).filter(|&s| s != 2).fold(F192::ZERO, |acc, s| acc + weights[s] * slots_at[s]);
    sent_values.extend([bytecode_final_at, bytecode_pull]);
    let heap_at = eval_e(&heap_b, &w);
    let constraint_at = {
        let mut factor = F192::ONE;
        let mut sum = F192::ZERO;
        for (chunk, &e) in constraint_chunks.iter().zip(&constraint_sizes) {
            sum += factor * eval_e(chunk, &w);
            factor *= w[e];
        }
        sum
    };
    sent_values.extend([heap_at, constraint_at]);
    for &v in &sent_values {
        writer.send(to_v(v));
    }
    clock.lap(&mut report, "values at t");

    // 8. ρ, and the combined claims: the verifier's own, on the stream so far.
    let rho = writer.sample();
    let combined: Vec<(Commitment, Combined<E>)> = {
        let mut channel = KeccakChannel::new(
            keccak_seed(&NAME, iv, &public),
            &writer.stream,
            Checks::Collect {
                zero: vec![],
                nonzero: vec![],
            },
        );
        let words: [E; 4] = std::array::from_fn(|k| E::new(u64::from_be_bytes(public[8 * k..8 * k + 8].try_into().unwrap()), 0, 0));
        let reduced = reduce(&shape, words, &mut channel, config.blake2s, Claims::Weighted).map_err(|e| format!("{e:?}"))?;
        channel.finish().map_err(|e| format!("the verifier reads the stream so far: {e:?}"))?;
        for (commitment, vars) in &reduced.stack_vars {
            let mine = match commitment {
                Commitment::C1 => stack1.layout.vars,
                Commitment::C2 => stack2.layout.vars,
                Commitment::Setup => stack_f.layout.vars,
            };
            if mine != *vars {
                return Err(format!("{commitment:?}: the verifier's stack has {vars} variables, the prover's {mine}"));
            }
        }
        reduced
            .openings
            .into_iter()
            .map(|(c, o)| match o {
                Opening::Weighted(claim) => (c, claim),
                Opening::Point { .. } => unreachable!("weighted mode"),
            })
            .collect()
    };
    let _ = rho;
    clock.lap(&mut report, "claims: the verifier's combination");

    let stacks_of = |c: Commitment| -> (&Stack, &Committed) {
        match c {
            Commitment::C1 => (&stack1, &committed1),
            Commitment::C2 => (&stack2, &committed2),
            Commitment::Setup => (&stack_f, &committed_f),
        }
    };
    let weights_dense: Vec<Vec<F192>> = combined
        .iter()
        .map(|(c, claim)| {
            let (stack, _) = stacks_of(*c);
            super::batch::dense_weight(claim, &stack.layout, stack.words.len())
        })
        .collect();
    if config.check {
        for ((c, claim), weight) in combined.iter().zip(&weights_dense) {
            let (stack, _) = stacks_of(*c);
            let sum = parallel::map_reduce(
                stack.words.len().div_ceil(1 << 14),
                || F192::ZERO,
                |chunk| {
                    let range = chunk << 14..((chunk + 1) << 14).min(stack.words.len());
                    range.fold(F192::ZERO, |acc, i| acc + weight[i].mul_base(stack.words[i]))
                },
                |a, b| a + b,
            );
            report
                .checks
                .push((format!("{c:?}: its {} relations, combined by ρ, hold", claim.relations), sum == from_v(claim.value)));
        }
    }
    clock.lap(&mut report, "claims: dense weights");

    // 9. The point claims: the batching sumcheck.
    let mut openings = Vec::new();
    match config.claims {
        Claims::Point => {
            let lambda = from_v(writer.sample());
            let stacks: Vec<(&[F64], usize)> = combined
                .iter()
                .map(|(c, _)| {
                    let (s, _) = stacks_of(*c);
                    (&s.words[..], s.layout.vars)
                })
                .collect();
            let (point, values) = super::batch::prove(&mut writer, &stacks, weights_dense, lambda);
            clock.lap(&mut report, "batching sumcheck");
            for ((c, _), &value) in combined.iter().zip(&values) {
                let (stack, committed) = stacks_of(*c);
                let p = point[..stack.layout.vars].to_vec();
                let proof = opening::open(&stack.words, committed, layout_word(*c), &p, value);
                openings.push(OpeningProof {
                    commitment: *c,
                    root: committed.root,
                    vars: committed.vars,
                    placed: committed.placed,
                    point: p,
                    value,
                    proof,
                });
            }
            clock.lap(&mut report, "openings: WHIR");
        }
        Claims::Weighted => return Err("weighted claims (extension W) have no opening here: use Claims::Point".into()),
    }
    report.stream_bytes = writer.stream.len();
    report.opening_bytes = openings
        .iter()
        .map(|o| 24 * o.proof.stream.len() + o.proof.merkle.iter().map(merkle_bytes).sum::<usize>())
        .collect();
    Ok((
        Proof {
            stream: writer.stream,
            openings,
        },
        report,
    ))
}

fn merkle_bytes(paths: &fiat_shamir::merkle::PrunedMerklePaths) -> usize {
    paths.leaf_data.iter().map(|row| 8 * row.len()).sum::<usize>() + 32 * paths.sibling_hashes.len()
}

/// Verify a proof: the verifier's `reduce` on the stream (its zero and nonzero checks held to account) and every
/// opening's WHIR proof, its point and value the ones the verifier leaves.
pub fn verify(trace_shape: &crate::verifier::Shape, iv: &[u8; 32], public: &[u8; 32], proof: &Proof, blake2s: Blake2s) -> Result<(), String> {
    let (reduced, zero, nonzero) =
        crate::contract::rust_verifier(trace_shape, iv, public, &proof.stream, blake2s, Claims::Point).map_err(|e| format!("reduce: {e:?}"))?;
    if let Some(i) = zero.iter().position(|x| *x != E::default()) {
        return Err(format!("check {i} of {} required zero is not", zero.len()));
    }
    if let Some(i) = nonzero.iter().position(|x| *x == E::default()) {
        return Err(format!("check {i} required nonzero is zero"));
    }
    if reduced.openings.len() != proof.openings.len() {
        return Err("one opening per commitment".into());
    }
    for ((commitment, opening), mine) in reduced.openings.iter().zip(&proof.openings) {
        let Opening::Point { point, value, bit_slice } = opening else {
            return Err("point claims".into());
        };
        if bit_slice.is_some() {
            return Err("no bit-slice claim on the main line".into());
        }
        if *commitment != mine.commitment || from_v(*value) != mine.value || point.iter().map(|&x| from_v(x)).collect::<Vec<_>>() != mine.point {
            return Err(format!("{commitment:?}: the opening is not of the verifier's claim"));
        }
        // The root: the stream's for C1 and C2; the setup's is the contract's constant (here, the prover's).
        let root_ok = match commitment {
            Commitment::C1 => reduced.roots[0] == halves(&mine.root),
            Commitment::C2 => reduced.roots[1] == halves(&mine.root),
            Commitment::Setup => true,
        };
        if !root_ok {
            return Err(format!("{commitment:?}: the opening's root is not the stream's"));
        }
        opening::verify(
            &mine.root,
            mine.vars,
            mine.placed,
            layout_word(*commitment),
            &mine.point,
            mine.value,
            &opening::wire_proof(&mine.proof),
        )
        .map_err(|e| format!("{commitment:?}: WHIR rejects: {e:?}"))?;
    }
    // Flock's claims on the fixed A0, B0 (the BLAKE2s R1CS): checked against the matrices themselves, as an honest
    // setup opening proves them (A0 and B0 are not committed here: PROVER.md).
    match (&reduced.matrices, blake2s) {
        (Some(claim), Blake2s::Flock(_)) => {
            let (a, b) = leanvm_flock_gas::matrices::matrix_values(&claim.point).map_err(|e| format!("{e:?}"))?;
            if (a, b) != (claim.a, claim.b) {
                return Err("Flock's claims on A0, B0 are not the matrices' values".into());
            }
        }
        (None, Blake2s::Omitted) => {}
        _ => return Err("Flock's matrices' claims".into()),
    }
    Ok(())
}
