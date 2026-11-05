// Part of this repository. The driver follows crates/leanvm_univariate/src/prover/prove.rs (its stacks, WHIR
// commits, batching sumcheck and openings, reused); Flock is that crate's `prove_keccak` (leanVM 42422001's Flock,
// vendored as crates/lv42_flock). MIT OR Apache-2.0; see NOTICE.md.
//! π1's prover, phase by phase, from the glue's cells (`slh_dsa::glue::Glue::witness`): Flock's blocks, `W` and
//! `Q_link`, `C1`; `α, β, γ`; Flock; `h`, `q`, `q_gate`, `C2`; `t` and the five values; the verifier's own relations
//! on the stream so far; the batching sumcheck; three WHIR openings. And [`verify`]: the verifier with the openings.

use std::time::Instant;

use fiat_shamir::merkle::Hash;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::flock_min::WalkedCircuit;
use leanvm_flock_gas::transcript::{Checks, KeccakChannel, KeccakWriter};
use leanvm_univariate::claims::{Column, Commitment};
use leanvm_univariate::prover::batch::prove_pairs;
use leanvm_univariate::prover::flock::{FlockWitness, prove_keccak};
use leanvm_univariate::prover::opening::{self, Committed};
use leanvm_univariate::prover::poly::{from_v, to_v};
use leanvm_univariate::prover::prove::halves;
use leanvm_univariate::prover::stack::Stack;
use leanvm_univariate::prover::weight::Weight;
use leanvm_univariate::verifier::Opening;
use primitives::field::{F64, F192};
use quotient::circuit::Circuit;
use quotient::domain::{self, point};
use quotient::ntt;

use crate::quotients::{copy_and_gate, link_quotient, port_table};
use crate::verifier::{front, reduce};
use crate::{
    H, OpeningProof, Params, Proof, SIGMA, W, copy_chunks, gate_chunks, iv, layout_word, layouts, link_chunks,
    public_words, q_copy, q_gate, q_link, seed,
};

/// The setup: the glue's wiring `σ` (each cell's successor, and its polynomial's coefficients), its stack and
/// commitment, and the IV that binds its root.
pub struct Setup {
    pub params: Params,
    pub sigma: Vec<u32>,
    pub sigma_novel: Vec<F64>,
    pub stack: Stack,
    pub committed: Committed,
    pub root: Hash,
    pub iv: [u8; 32],
}

impl Setup {
    pub fn new(p: &Params, circuit: &Circuit) -> Self {
        assert_eq!(circuit.log_rows, p.log_rows, "the glue's rows");
        assert_eq!(circuit.port_region, (p.port_start(), p.port_start()), "the glue's port region");
        let mut sigma_novel = parallel::map_collect(circuit.sigma.len(), |i| point(circuit.sigma[i] as usize));
        ntt::coefficients(&mut sigma_novel, F64::ZERO);
        let layout = layouts(p).remove(2).1;
        let mut stack = Stack::new(layout);
        stack.put_b(SIGMA, &sigma_novel);
        let committed = opening::commit(&stack.words, stack.layout.vars, stack.placed());
        let root = committed.root;
        Self {
            params: *p,
            sigma: circuit.sigma.clone(),
            sigma_novel,
            stack,
            committed,
            root,
            iv: iv(p, &root),
        }
    }
}

/// The prover's options.
#[derive(Clone, Copy, Debug, Default)]
pub struct Config {
    /// Check every combined claim against the committed stacks (slower).
    pub check: bool,
    /// Prove even when the witness is not one (ports that are not Keccak-f's, a statement that does not hold), for
    /// tests that the verifier rejects what follows.
    pub force: bool,
}

/// Each phase's seconds, the checks made, and the proof's sizes.
#[derive(Default, Debug)]
pub struct Report {
    pub phases: Vec<(&'static str, f64)>,
    pub checks: Vec<(String, bool)>,
    pub stream_bytes: usize,
    pub opening_bytes: Vec<usize>,
    /// (commitment, words placed, stack variables).
    pub stacks: Vec<(Commitment, u64, usize)>,
}

struct Clock(Instant);

impl Clock {
    fn lap(&mut self, report: &mut Report, name: &'static str) {
        let now = Instant::now();
        report.phases.push((name, (now - self.0).as_secs_f64()));
        self.0 = now;
    }
}

/// A quotient's novel coefficients in its chunks (zero past them).
fn chunked<T: Copy + Default>(novel: &[T], sizes: &[usize]) -> Vec<Vec<T>> {
    let mut at = 0;
    sizes
        .iter()
        .map(|&e| {
            let mut chunk = vec![T::default(); 1 << e];
            let end = novel.len().min(at + (1 << e));
            if at < end {
                chunk[..end - at].copy_from_slice(&novel[at..end]);
            }
            at += 1 << e;
            chunk
        })
        .collect()
}

/// Write an `E`-column's `B` coefficients, from its novel ones, limb by limb.
fn put_e_novel(stack: &mut Stack, column: Column, novel: &[F192]) {
    for limb in 0..3 {
        let words: Vec<F64> = parallel::map_collect(novel.len(), |i| F64([novel[i].c0, novel[i].c1, novel[i].c2][limb]));
        ntt::subset_sums_from(&words, stack.limb_mut(column, limb));
    }
}

/// The public words' combination the copy argument's sum must be: words 0..4 the statement's halves, word 4 the
/// constant 1 (`crates/quotient`'s target).
fn target(pk: &[u8; 32], msg: &[u8; 32], gamma: F192) -> F192 {
    let w = public_words(pk, msg);
    let half = |h: usize| F192::new(w[2 * h + 1], w[2 * h], 0);
    let g2 = gamma * gamma;
    half(0) + gamma * half(1) + g2 * (half(2) + gamma * half(3)) + g2 * g2
}

fn merkle_bytes(paths: &fiat_shamir::merkle::PrunedMerklePaths) -> usize {
    paths.leaf_data.iter().map(|row| 8 * row.len()).sum::<usize>() + 32 * paths.sibling_hashes.len()
}

/// Prove the statement `(pk, msg)` from the glue's `cells` (`Glue::witness`: its gates, wires and ports checked).
pub fn prove(
    setup: &Setup,
    pk: &[u8; 32],
    msg: &[u8; 32],
    cells: &[F64],
    config: Config,
) -> Result<(Proof, Report), String> {
    let p = &setup.params;
    let (m, n) = (p.m(), p.n());
    if cells.len() != n {
        return Err(format!("{} cells, not 2^{m}", cells.len()));
    }
    let mut report = Report::default();
    let mut clock = Clock(Instant::now());

    // 1. Flock's blocks: block b's input lanes are its ports' C cells.
    let start = p.port_start();
    let inputs: Vec<[u64; 25]> = (0..p.blocks())
        .map(|b| std::array::from_fn(|q| cells[4 * (start + slh_dsa::glue::port_index(b, q)) + 2].0))
        .collect();
    let (z, a, b, z_lincheck) = lv42_flock::keccak::generate_witness_with_ab_packed_and_lincheck(&inputs, p.blocks_log);
    let qflock: Vec<F64> = parallel::map_collect(z.len(), |i| F64(z[i]));
    let flock = FlockWitness {
        n_blocks: p.blocks(),
        z,
        a,
        b,
        z_lincheck,
    };
    let port = port_table(p, &qflock);
    let ports_hold = port[..] == cells[n / 2..];
    report.checks.push(("the glue's ports are q_flock's port words".into(), ports_hold));
    if !ports_hold && !config.force {
        return Err("the glue's ports are not Keccak-f of their inputs (q_flock's port words)".into());
    }
    clock.lap(&mut report, "witness: Flock's blocks (Keccak-f, packed, stripes)");

    // 2. W and the link's quotient; C1.
    let mut w_novel = cells.to_vec();
    ntt::coefficients(&mut w_novel, F64::ZERO);
    clock.lap(&mut report, "W: coefficients");
    let (link, link_fits) = link_quotient(p, &w_novel, &port);
    report.checks.push(("Q_link is a polynomial of its count".into(), link_fits));
    if !link_fits && !config.force {
        return Err("the link's quotient is not a polynomial: the ports are not q_flock's".into());
    }
    drop(port);
    clock.lap(&mut report, "Q_link: W and ℓ_q on 2^23 points, inverse NTT");
    let all = layouts(p);
    let mut stack1 = Stack::new(all[0].1.clone());
    stack1.put_k(Column::Qflock, &qflock);
    drop(qflock);
    stack1.put_b(W, &w_novel);
    for (c, chunk) in chunked(&link, &link_chunks(p)).iter().enumerate() {
        stack1.put_b(q_link(c), chunk);
    }
    drop(link);
    let committed1 = opening::commit_keeping_codeword(&stack1.words, stack1.layout.vars, stack1.placed());
    report.stacks.push((Commitment::C1, stack1.placed(), stack1.layout.vars));
    clock.lap(&mut report, "C1: stack, WHIR commit");

    // 3. The transcript: the seed, C1, the copy argument's challenges.
    let seed = seed(&setup.iv, pk, msg);
    let mut writer = KeccakWriter::new(seed);
    writer.send_root(halves(&committed1.root));
    let [alpha, beta, gamma] = [(); 3].map(|_| from_v(writer.sample()));

    // 4. Flock.
    prove_keccak(&mut writer, &flock, p.flock, p.flock_log_n())?;
    drop(flock);
    clock.lap(&mut report, "Flock: zerocheck, lincheck, slices");

    // 5. h, q, q_gate; C2.
    let cg = copy_and_gate(p, cells, &setup.sigma, &setup.sigma_novel, &w_novel, [alpha, beta, gamma]);
    let holds = cg.sum == target(pk, msg, gamma);
    report.checks.push(("the copy argument's sum is the statement's (word 6 is zero)".into(), holds));
    report.checks.push(("q and q_gate are polynomials of their counts".into(), cg.fits));
    if !holds && !config.force {
        return Err("the statement does not hold: the public words are not (PK, M) with word 6 zero".into());
    }
    if !cg.fits && !config.force {
        return Err("a quotient of the glue is not a polynomial: the cells are not a witness".into());
    }
    clock.lap(&mut report, "quotient: h, q, q_gate");
    let mut stack2 = Stack::new(all[1].1.clone());
    put_e_novel(&mut stack2, H, &cg.h);
    for (c, chunk) in chunked(&cg.q, &copy_chunks(p)).iter().enumerate() {
        put_e_novel(&mut stack2, q_copy(c), chunk);
    }
    for (c, chunk) in chunked(&cg.q_gate, &gate_chunks(p)).iter().enumerate() {
        stack2.put_b(q_gate(c), chunk);
    }
    drop(cg);
    let committed2 = opening::commit_keeping_codeword(&stack2.words, stack2.layout.vars, stack2.placed());
    report.stacks.push((Commitment::C2, stack2.placed(), stack2.layout.vars));
    report.stacks.push((Commitment::Setup, setup.stack.placed(), setup.stack.layout.vars));
    writer.send_root(halves(&committed2.root));
    clock.lap(&mut report, "C2: stack, WHIR commit");

    // 6. t and the values at t: the four row polynomials A_j (B coefficients: from the novel ones a_j, A_j the sum
    // of the a_j' with j' ⊆ j), and σ(t).
    let t = from_v(writer.sample());
    let digits: Vec<F192> = std::iter::successors(Some(t), |&x| Some(x * x + x)).take(m + 1).collect();
    let a: Vec<F192> = (0..4).map(|j| domain::evaluate(&w_novel, j, 4, &digits[2..m])).collect();
    let rows = [a[0], a[0] + a[1], a[0] + a[2], a[0] + a[1] + a[2] + a[3]];
    let next = domain::evaluate(&setup.sigma_novel, 0, 1, &digits[..m]);
    for &v in rows.iter().chain([&next]) {
        writer.send(to_v(v));
    }
    drop(w_novel);
    clock.lap(&mut report, "values at t");

    // 7. The verifier's own relations on the stream so far (ρ drawn by both).
    let combined = {
        let mut channel = KeccakChannel::new(
            seed,
            &writer.stream,
            Checks::Collect {
                zero: vec![],
                nonzero: vec![],
            },
        );
        let public = public_words(pk, msg).map(|w| E::new(w, 0, 0));
        let front = front::<E, _, leanvm_flock_gas::keccak_flock::Keccak>(p, public, &mut channel, true)
            .map_err(|e| format!("the verifier on the stream so far: {e:?}"))?;
        channel.finish().map_err(|e| format!("the verifier reads the stream so far: {e:?}"))?;
        let Checks::Collect { zero, nonzero } = &channel.checks else { unreachable!() };
        let fine = zero.iter().all(|x| *x == E::default()) && nonzero.iter().all(|x| *x != E::default());
        report.checks.push(("the verifier's checks on the stream so far (Flock's terminal)".into(), fine));
        if !fine && !config.force {
            return Err("Flock's terminal fails on the stream so far".into());
        }
        front.combined
    };
    let _rho = writer.sample();
    let stacks: [(&Stack, &Committed); 3] = [(&stack1, &committed1), (&stack2, &committed2), (&setup.stack, &setup.committed)];
    let of = |c: Commitment| match c {
        Commitment::C1 => 0,
        Commitment::C2 => 1,
        Commitment::Setup => 2,
    };
    let weights: Vec<Weight> = combined.iter().map(|(c, claim)| Weight::new(claim, &stacks[of(*c)].0.layout)).collect();
    clock.lap(&mut report, "claims: relations, weights");
    if config.check {
        for ((c, claim), weight) in combined.iter().zip(&weights) {
            let sum = weight.sum(&stacks[of(*c)].0.words);
            report.checks.push((format!("{c:?}: its {} relations, combined by ρ, hold", claim.relations), sum == from_v(claim.value)));
        }
        clock.lap(&mut report, "claims: the combined claims' check (test only)");
    }

    // 8. The batching sumcheck: π1-rec3's pairs.
    let lambda = from_v(writer.sample());
    let target: F192 = combined.iter().rev().fold(F192::ZERO, |acc, (_, claim)| acc * lambda + from_v(claim.value));
    let words: Vec<(&[F64], usize)> = combined
        .iter()
        .map(|(c, _)| {
            let s = stacks[of(*c)].0;
            (&s.words[..], s.layout.vars)
        })
        .collect();
    let (point, values) = prove_pairs(&mut writer, &words, weights, lambda, target)?;
    clock.lap(&mut report, "batching sumcheck");

    // 9. The openings.
    let mut openings = Vec::new();
    for ((c, _), &value) in combined.iter().zip(&values) {
        let (stack, committed) = stacks[of(*c)];
        let at = point[..stack.layout.vars].to_vec();
        let layout = layout_word(p, *c, &stack.layout);
        let proof = opening::open(&stack.words, committed, &layout, &at, value);
        openings.push(OpeningProof {
            commitment: *c,
            root: committed.root,
            point: at,
            value,
            proof,
        });
    }
    clock.lap(&mut report, "openings: WHIR");
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

/// Verify a proof of `(pk, msg)` against the setup's root: the verifier on the stream (its checks enforced, the
/// Keccak block's terminal `T`), then every opening: its point and value the verifier's claim, its root the stream's
/// (the setup's for the setup), its layout word the verifier's, and leanVM's WHIR verifier.
pub fn verify<T: WalkedCircuit>(
    p: &Params,
    setup_root: &Hash,
    pk: &[u8; 32],
    msg: &[u8; 32],
    proof: &Proof,
) -> Result<(), String> {
    let seed = seed(&iv(p, setup_root), pk, msg);
    let mut channel = KeccakChannel::new(seed, &proof.stream, Checks::Enforce);
    let public = public_words(pk, msg).map(|w| E::new(w, 0, 0));
    let reduced = reduce::<E, _, T>(p, public, &mut channel).map_err(|e| format!("reduce: {e:?}"))?;
    channel.finish().map_err(|e| format!("the stream: {e:?}"))?;
    if reduced.openings.len() != proof.openings.len() {
        return Err("one opening per stack".into());
    }
    let all = layouts(p);
    for ((commitment, opening), mine) in reduced.openings.iter().zip(&proof.openings) {
        let Opening::Point { point, value, bit_slice: None } = opening else {
            return Err("point claims".into());
        };
        let point: Vec<F192> = point.iter().map(|&x| from_v(x)).collect();
        if *commitment != mine.commitment || from_v(*value) != mine.value || point != mine.point {
            return Err(format!("{commitment:?}: the opening is not of the verifier's claim"));
        }
        let root_ok = match commitment {
            Commitment::C1 => reduced.roots[0] == halves(&mine.root),
            Commitment::C2 => reduced.roots[1] == halves(&mine.root),
            Commitment::Setup => mine.root == *setup_root,
        };
        if !root_ok {
            return Err(format!("{commitment:?}: the opening's root is not the stream's (or the setup's)"));
        }
        let layout = &all.iter().find(|(c, _)| c == commitment).expect("a layout").1;
        let word = layout_word(p, *commitment, layout);
        opening::verify(&mine.root, &word, &mine.point, mine.value, &opening::wire_proof(&mine.proof))
            .map_err(|e| format!("{commitment:?}: WHIR rejects: {e:?}"))?;
    }
    Ok(())
}
