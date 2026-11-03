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
use leanvm_flock_gas::transcript::{FsShape, KeccakWriter, keccak_seed, squares};
use primitives::field::{F64, F192};

use super::bus::{Bus, all_leaves, expected_root, heap};
use super::columns::{c1_polys, setup_polys};
use super::flock::{FlockWitness, Matrices};
use super::replay::Replay;
use super::opening::{self, Committed};
use super::poly::{eval_k, eval_limbs, from_v, novel_limbs, to_v};
use super::quotients::{self, Quotient};
use super::stack::{Stack, c1_columns, c2_columns};
use super::trace::Trace;
use super::weight::Weight;
use crate::claims::{Column, Combined, Commitment};
use crate::contract::{NAME, SetupRoots, contract_iv_for, layout_words};
use crate::heap::Leaves;
use crate::stacks::StackLayout;
use crate::verifier::{Blake2s, Claims, Opening, Shape, chunks, degree, reduce, sent_columns};

/// What a proof is: the verifier's stream (calldata after the selector and the public input) and one WHIR opening
/// per commitment, with the point claim it proves.
pub struct Proof {
    pub stream: Vec<u8>,
    pub openings: Vec<OpeningProof>,
}

pub struct OpeningProof {
    pub commitment: Commitment,
    pub root: Hash,
    /// Its `PCS_OPEN` layout word, which carries `vars` and `placed`.
    pub layout: [u8; 32],
    pub vars: usize,
    pub placed: u64,
    pub point: Vec<F192>,
    pub value: F192,
    pub proof: fiat_shamir::transcript::Proof,
}

/// The `PCS_OPEN` layout word of a commitment of `shape` (`contract::layout_words`, SPEC.md §13, F2).
pub fn layout_word(shape: &Shape, commitment: Commitment) -> [u8; 32] {
    let words = layout_words(shape);
    match commitment {
        Commitment::C1 => words[0],
        Commitment::C2 => words[1],
        Commitment::Setup => words[2],
    }
}

/// The stack's variables and placed words a layout word carries (bytes 24, and 25..32).
pub fn layout_shape(word: &[u8; 32]) -> (usize, u64) {
    let mut placed = [0u8; 8];
    placed[1..].copy_from_slice(&word[25..]);
    (word[24] as usize, u64::from_be_bytes(placed))
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
    /// Finer timings inside a phase, as text.
    pub notes: Vec<String>,
    /// The setup roots the proof's contract binds.
    pub roots: Option<SetupRoots>,
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

/// The root's two 128-bit halves as the stream carries them: its two scalars as WHIR's transcript has them
/// (`fiat_shamir::merkle::hash_to_scalars`, each the little-endian number of 16 of the hash's bytes, the opening's
/// first two scalars), each sent big-endian. The stream's 32 bytes are then the root's `PCS_OPEN` root word
/// (`leanvm_flock_gas::evm::machine::root_word`, each 16-byte half of the hash reversed), the word the contract
/// passes as it is; before, they were the hash's bytes as they are, a word a decoding `PCS_OPEN` reads as another
/// root (`crates/leanvm_rec/REVIEW-REC.md`, R1).
pub fn halves(root: &Hash) -> [E; 2] {
    fiat_shamir::merkle::hash_to_scalars(root).map(|s| E::new(s.c0, s.c1, s.c2))
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

/// The verifier's count of a table block's leaf quotient coefficients: sized for the height's fewest rows
/// (`Shape::least_rows`, SPEC.md §13, F1).
pub fn table_leaf_count(t: usize, r: usize) -> u64 {
    let table = &tables()[t];
    let n = 1u64 << r;
    let pull = 1 + table.flushes.pull.iter().map(|tu| tuple_degree(tu)).sum::<usize>();
    let push: usize = table.flushes.push.iter().map(|tu| tuple_degree(tu)).sum();
    degree(pull.max(push) as u64 * (n - 1) + (n - Shape::least_rows(r)), n) + 1
}

/// The verifier's count of the constraint quotient's coefficients (`verifier::reduce`, step 5).
pub fn constraint_count(trace: &Trace) -> u64 {
    let mut most = 0u64;
    for table in tables() {
        let r = trace.heights[table.opcode];
        let n = 1u64 << r;
        if table.opcode == OP_JUMP {
            most = most.max(degree(n, 2));
        }
        let counts = table.count_columns().count() as u64;
        most = most.max(degree((n - 1) * (1 + counts), n));
        if table.opcode == OP_BLAKE2S {
            most = most.max(degree(r as u64 * (n / 2), n));
        }
    }
    most.max(degree(1u64 << trace.log_memory, 3)) + 1
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
    /// The setup roots the contract's IV binds (SPEC.md §13, F2): `F`'s must be this program's and shape's
    /// (`setup::shape_roots`; at the reference shape `SetupRoots::REFERENCE`).
    pub roots: SetupRoots,
}

/// Prove `trace`'s execution (its rows placed: [`Trace::place`]) for the contract of the program's IV `iv` (the
/// contract's own binds the setup roots and the shape: `contract::contract_iv_for`, which also binds π1-rec's variant); with Flock, from leanVM's Flock
/// inputs `flock`, placed likewise.
pub fn prove(trace: &Trace, flock: Option<FlockWitness>, iv: &[u8; 32], config: Config) -> Result<(Proof, Report), String> {
    let mut report = Report::default();
    let mut clock = Clock { last: Instant::now() };
    if !trace.placed {
        return Err("the trace's rows are leanVM's order: place them first (Trace::place)".into());
    }
    let shape = trace.shape();
    if shape.heights() != trace.heights {
        return Err(format!("leanVM's heights {:?} are not the verifier's {:?}", trace.heights, shape.heights()));
    }
    shape
        .validate(matches!(config.blake2s, Blake2s::Flock(_)))
        .map_err(|e| format!("the shape: {e:?}"))?;
    let public = trace.public_input();

    // 1. C1: every column in basis B, q_flock as values.
    let c1 = c1_polys(trace);
    let setup = setup_polys(trace);
    clock.lap(&mut report, "C1 and setup: inverse NTTs to basis B");
    let mut stack1 = Stack::new(StackLayout::new(&c1_columns(&shape)));
    stack1.put_k(Column::Qflock, &trace.qflock);
    for (t, columns) in c1.tables.iter().enumerate() {
        for (c, column) in columns.iter().enumerate() {
            stack1.put_b(Column::Table { table: t, column: c }, &column.novel);
        }
        stack1.put_b(Column::Inverse(t), &c1.inverses[t].novel);
    }
    for (k, column) in c1.memory.iter().enumerate() {
        stack1.put_b(Column::Memory(k), &column.novel);
    }
    stack1.put_b(Column::BytecodeFinal, &c1.bytecode_final.novel);
    let mut stack_f = super::setup::f_stack(&shape, &setup);
    if config.garbage {
        stack1.fill_unused(0xC1);
        stack_f.fill_unused(0xF0);
    }
    let committed1 = opening::commit_keeping_codeword(&stack1.words, stack1.layout.vars, stack1.placed());
    let committed_f = opening::commit_keeping_codeword(&stack_f.words, stack_f.layout.vars, stack_f.placed());
    // The contract binds F's root (and opens F against it): it must be this program's and shape's. Garbage in the
    // unused words makes another F, which only a contract built for it accepts: that contract's roots are used. (The
    // stand-in roots' cross-check proves nothing.)
    let roots = if config.garbage {
        SetupRoots {
            f: committed_f.root,
            ..config.roots
        }
    } else {
        config.roots
    };
    if config.stand_in_roots.is_none() && committed_f.root != roots.f {
        return Err("the contract's F root is not this program's and shape's (prover::setup::f_root)".into());
    }
    report.roots = Some(roots);
    report.stacks.push((Commitment::C1, stack1.placed(), stack1.layout.vars));
    report.stacks.push((Commitment::Setup, stack_f.placed(), stack_f.layout.vars));
    clock.lap(&mut report, "C1 and setup: WHIR commits");

    // 0. The seed (the contract's IV binds the setup roots), then the six row counts (SPEC.md §13, F1), absorbed with
    // C1's root.
    let seed = keccak_seed(&NAME, &contract_iv_for(&shape, config.blake2s, iv, &roots), &public);
    let mut writer = KeccakWriter::new(seed);
    for &rows in &trace.rows {
        writer.send_integer(rows, 4);
    }
    writer.send_root(config.stand_in_roots.map_or_else(|| halves(&committed1.root), |r| r[0]));

    // 2. The bus's and the constraints' challenges; with π1-rec (`FsShape::Rec`, SPEC-REC.md §1.4) α is (c, c², c⁴,
    // c⁸) of one challenge c, squared in E as the verifier squares it.
    let alphas: Vec<F192> = match config.blake2s.fs() {
        FsShape::Main => (0..4).map(|_| from_v(writer.sample())).collect(),
        FsShape::Rec | FsShape::Rec2 | FsShape::Rec3 => squares(writer.sample(), 4).into_iter().map(from_v).collect(),
    };
    let beta = from_v(writer.sample());
    let gamma = from_v(writer.sample());

    // 3. Flock, on q_flock (`flock.rs`). On the point-claim ABI with the slices sent, its matrices' reduction runs in
    // the batching sumcheck (SPEC.md §13, lever 4a), as `verifier::reduce` has it.
    let mut pending = None;
    let mut slices_end = None;
    // The slices, when the stream does not carry them (extension B, `Slices::Claim`).
    let mut flock_slices: Option<Vec<E>> = None;
    if let Blake2s::Flock(variant) = config.blake2s {
        let witness = flock.ok_or("Flock needs leanVM's Flock inputs (flock.bin)")?;
        let log_n = leanvm_flock_gas::layout::BLAKE2S_R1CS_LOG_SIZE + trace.heights[OP_BLAKE2S];
        let deferred = config.claims == Claims::Point;
        let out = super::flock::prove(&mut writer, &witness, variant, log_n, deferred)?;
        // leanVM's Flock buffers (2 GB at 1,000 signatures) are not needed past here.
        drop(witness);
        slices_end = Some(out.slices_end);
        if variant.slices == leanvm_flock_gas::flock_min::Slices::Claim {
            flock_slices = Some(out.slices.clone());
        }
        report.notes.push(format!("Flock's zerocheck and lincheck: {:.3} s", out.reduction_secs));
        if variant.skip != leanvm_flock_gas::flock_min::PACKING {
            for (stage, secs) in std::mem::take(&mut *lv42_flock::zerocheck::skip::STAGES.lock().expect("the stages")) {
                report.notes.push(format!("  the skip's zerocheck, {stage}: {secs:.3} s"));
            }
        }
        match out.matrices {
            Matrices::Done { point, a, b } => report.flock = Some((point, a, b)),
            Matrices::Pending(p) => pending = Some(p),
            Matrices::Walked => {}
        }
        clock.lap(&mut report, "Flock: zerocheck, lincheck, slices");
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
    let heap_novel = novel_limbs(&heap_values);
    drop(heap_values);
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
        let r_novel = novel_limbs(values);
        let (name, q) = match block.leaves {
            Leaves::Memory => ("leaf: memory".to_string(), quotients::memory_leaf(trace, &c1, &setup, &bus, &r_novel, n - 1)),
            Leaves::Bytecode => (
                "leaf: bytecode".to_string(),
                quotients::bytecode_leaf(trace, &c1, &setup, &bus, &r_novel, n - 1),
            ),
            Leaves::Table(t) => {
                let count = table_leaf_count(t, block.r);
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
    let constraint = quotients::constraints(trace, &c1, gamma, constraint_count(trace), lines);
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
    for (limb, novel) in heap_novel.iter().enumerate() {
        quotient::ntt::subset_sums_from(novel, stack2.limb_mut(Column::Heap, limb));
    }
    drop(heap_novel);
    let mut put = |q: &Quotient, sizes: &[usize], column: &dyn Fn(usize) -> Column| {
        for chunk in 0..sizes.len() {
            for limb in 0..3 {
                q.chunk_b(sizes, chunk, limb, stack2.limb_mut(column(chunk), limb));
            }
        }
    };
    put(&tree, &[layout.h, 0], &Column::TreeQuotient);
    put(&constraint, &constraint_sizes, &Column::ConstraintQuotient);
    for ((block, q), (_, sizes)) in leaf_quotients.iter().zip(&leaf_sizes) {
        put(q, sizes, &|chunk| Column::LeafQuotient { block: *block, chunk });
    }
    drop((tree, constraint, leaf_quotients));
    clock.lap(&mut report, "C2: chunks in basis B");
    if config.garbage {
        stack2.fill_unused(0xC2);
    }
    let committed2 = opening::commit_keeping_codeword(&stack2.words, stack2.layout.vars, stack2.placed());
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
        let b = |c: usize| stack1.k(Column::Table { table: table.opcode, column: c });
        let at: Vec<F192> = parallel::map_collect(tcols.len(), |c| primitives::multilinear::mle_eval(b(c), &w[..tcols[c].vars()]));
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
    let mem_at: Vec<F192> = (0..4).map(|k| eval_k(stack1.k(Column::Memory(k)), &w[..lm])).collect();
    let address_at = eval_k(&setup.address.b, &w[..lm]);
    let memory_pull = beta
        + weights[0] * from_v(SEP_MEM)
        + weights[1] * address_at
        + weights[2] * mem_at[3]
        + (0..3).fold(F192::ZERO, |acc, k| acc + weights[3 + k] * mem_at[k]);
    sent_values.extend([mem_at[3], address_at, memory_pull]);
    let bytecode_final_at = eval_k(stack1.k(Column::BytecodeFinal), &w[..lb]);
    let slots_at: Vec<F192> = setup.slots.iter().map(|s| eval_k(&s.b, &w[..lb])).collect();
    let bytecode_pull = beta
        + weights[2] * bytecode_final_at
        + (0..16).filter(|&s| s != 2).fold(F192::ZERO, |acc, s| acc + weights[s] * slots_at[s]);
    sent_values.extend([bytecode_final_at, bytecode_pull]);
    let heap_at = eval_limbs(stack2.limbs(Column::Heap), &w);
    let constraint_at = {
        let mut factor = F192::ONE;
        let mut sum = F192::ZERO;
        for (c, &e) in constraint_sizes.iter().enumerate() {
            sum += factor * eval_limbs(stack2.limbs(Column::ConstraintQuotient(c)), &w);
            factor *= w[e];
        }
        sum
    };
    sent_values.extend([heap_at, constraint_at]);
    for &v in &sent_values {
        writer.send(to_v(v));
    }
    clock.lap(&mut report, "values at t");

    // Past the values at t, the proof reads the stacks and their commitments alone (the heap and the quotients are
    // in C2's stack since step 6).
    drop((c1, setup, leaves));

    // 8. ρ, and the combined claims: the verifier's own, on the stream so far, in weighted mode (which reads nothing
    // after ρ). With the matrices' reduction pending, weighted mode reads it after the slices: `Replay` serves it there,
    // an honest prover's at fixed challenges, outside the chain (`replay.rs`).
    let rho = writer.sample();
    let combined: Vec<(Commitment, Combined<E>)> = {
        let (insert_at, scalars, samples) = match (&pending, slices_end) {
            (Some(p), Some(at)) => {
                let challenges = super::replay::challenges(p.rounds());
                (at, p.off_chain(&challenges)?, challenges)
            }
            _ => (0, Vec::new(), Vec::new()),
        };
        let mut channel = Replay::new(seed, &writer.stream, insert_at, scalars, samples);
        let words: [E; 4] = std::array::from_fn(|k| E::new(u64::from_be_bytes(public[8 * k..8 * k + 8].try_into().unwrap()), 0, 0));
        let reduced = reduce(&shape, words, &mut channel, config.blake2s, Claims::Weighted).map_err(|e| format!("{e:?}"))?;
        channel.finish().map_err(|e| format!("the verifier reads the stream so far: {e}"))?;
        report.checks.push(("the verifier's checks on the stream so far (weighted mode)".into(), channel.checks_hold()));
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
                // Without the slices (extension B), weighted mode adds their combination's terms to C1's claim; point
                // mode makes it the batch's terminal instead, a bit-slice claim of C1's call. Its terms leave C1's
                // claim here, and their part of its value, `Σ coefficient s_twist` at the true slices (the
                // combination holds: an honest prover's at the inserted challenges).
                Opening::Weighted(mut claim) if c == Commitment::C1 && flock_slices.is_some() => {
                    let slices = flock_slices.as_ref().expect("the slices");
                    let mut part = E::default();
                    claim.terms.retain(|&(column, _, twist, coefficient)| {
                        let bits = column == Column::QflockBits;
                        if bits {
                            part += coefficient * slices[twist as usize];
                        }
                        !bits
                    });
                    claim.value += part;
                    (c, claim)
                }
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
    let weights: Vec<Weight> = combined
        .iter()
        .map(|(c, claim)| Weight::new(claim, &stacks_of(*c).0.layout))
        .collect();
    clock.lap(&mut report, "claims: weights");
    if config.check {
        for ((c, claim), weight) in combined.iter().zip(&weights) {
            let sum = weight.sum(&stacks_of(*c).0.words);
            report
                .checks
                .push((format!("{c:?}: its {} relations, combined by ρ, hold", claim.relations), sum == from_v(claim.value)));
        }
        clock.lap(&mut report, "claims: the combined-claims check (test only)");
    }

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
            let fs = config.blake2s.fs();
            let narrow = matches!(fs, FsShape::Rec2 | FsShape::Rec3);
            let (point, values, matrices) = if fs == FsShape::Rec3 {
                // π1-rec3: the batch two variables a round (SPEC-POINTS.md), its claim the combined claims' values.
                let target: F192 = combined
                    .iter()
                    .rev()
                    .fold(F192::ZERO, |acc, (_, claim)| acc * lambda + from_v(claim.value));
                if pending.is_some() {
                    return Err("π1-rec3's paired batch has no matrices' reduction".into());
                }
                let (point, values) = super::batch::prove_pairs(&mut writer, &stacks, weights, lambda, target)?;
                (point, values, None)
            } else {
                super::batch::prove(&mut writer, &stacks, weights, lambda, pending.as_ref(), narrow)?
            };
            if let Some(claim) = matrices {
                report.flock = Some(claim);
            }
            clock.lap(&mut report, "batching sumcheck");
            for ((c, _), &value) in combined.iter().zip(&values) {
                let (stack, committed) = stacks_of(*c);
                let p = point[..stack.layout.vars].to_vec();
                let layout = layout_word(&shape, *c);
                if layout_shape(&layout) != (committed.vars, committed.placed) {
                    return Err(format!(
                        "{c:?}: the layout word's stack {:?} is not the committed one ({}, {})",
                        layout_shape(&layout),
                        committed.vars,
                        committed.placed
                    ));
                }
                let proof = opening::open(&stack.words, committed, &layout, &p, value);
                openings.push(OpeningProof {
                    commitment: *c,
                    root: committed.root,
                    layout,
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
/// opening's WHIR proof, its point and value the ones the verifier leaves, its layout word the contract's.
///
/// The contract binds `roots` in its IV (`contract::rust_verifier_with`), and the setup opening's root must be its
/// `F`.
///
/// With extension B (`Slices::Claim`), `C1`'s call also carries a bit-slice claim, which a WHIR opening cannot prove
/// (`PCS_OPEN` would ring-switch it): it is returned, for the caller to check against `q_flock`.
pub fn verify(
    trace_shape: &crate::verifier::Shape,
    iv: &[u8; 32],
    roots: &SetupRoots,
    public: &[u8; 32],
    proof: &Proof,
    blake2s: Blake2s,
) -> Result<Option<Combined<E>>, String> {
    let mut unproven = None;
    let (reduced, zero, nonzero) =
        crate::contract::rust_verifier_with(trace_shape, iv, roots, public, &proof.stream, blake2s, Claims::Point)
            .map_err(|e| format!("reduce: {e:?}"))?;
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
        if let Some(claim) = bit_slice {
            let ext_b = matches!(blake2s, Blake2s::Flock(v) if v.slices == leanvm_flock_gas::flock_min::Slices::Claim);
            if *commitment != Commitment::C1 || !ext_b {
                return Err("a bit-slice claim is extension B's, on C1".into());
            }
            unproven = Some(claim.clone());
        }
        if *commitment != mine.commitment || from_v(*value) != mine.value || point.iter().map(|&x| from_v(x)).collect::<Vec<_>>() != mine.point {
            return Err(format!("{commitment:?}: the opening is not of the verifier's claim"));
        }
        // The root: the stream's for C1 and C2; the setup's is the contract's constant.
        let root_ok = match commitment {
            Commitment::C1 => reduced.roots[0] == halves(&mine.root),
            Commitment::C2 => reduced.roots[1] == halves(&mine.root),
            Commitment::Setup => mine.root == roots.f,
        };
        if !root_ok {
            return Err(format!("{commitment:?}: the opening's root is not the stream's (or the contract's)"));
        }
        let layout = layout_word(trace_shape, *commitment);
        if mine.layout != layout {
            return Err(format!("{commitment:?}: the opening's layout word is not the contract's"));
        }
        opening::verify(&mine.root, &layout, &mine.point, mine.value, &opening::wire_proof(&mine.proof))
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
        (None, Blake2s::Flock(v)) if v.slices == leanvm_flock_gas::flock_min::Slices::TowerWalk => {}
        _ => return Err("Flock's matrices' claims".into()),
    }
    Ok(unproven)
}
