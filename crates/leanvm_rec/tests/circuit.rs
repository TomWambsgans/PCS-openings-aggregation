// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Milestone R2 (SPEC-REC.md §7, steps 2–6): `π2`'s circuit compiled from `π1`'s recorded verifier, its witness from
//! the real 1,000-signature proofs (`crates/leanvm_univariate/tests/vectors/`: π1-rec's `main_line_rec`, and the
//! main line's).
//!
//! - every position's pull equals its push, and the public side holds (`spec::Circuit::check`);
//! - the circuit's calls, on its public inputs, are exactly the vector's `PCS_OPEN` inputs;
//! - every digest and every element is `eval::evaluate`'s;
//! - a flipped stream byte, a changed public input, a changed witness word are each caught;
//! - the layout's counts: `N`, the fill, the regions, the blocks and the selector pairs.
//!
//! `cargo test --release -p leanvm_rec --test circuit -- --nocapture --test-threads 1`

#[path = "../../leanvm_univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_flock_gas::evm::record::Node;
use leanvm_flock_gas::field::K;
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_flock_gas::transcript::keccak_seed;
use leanvm_rec::circuit::compile::{Compiled, Inputs, Layout, pi2};
use leanvm_rec::circuit::spec::Failure;
use leanvm_rec::eval::{Value, evaluate};
use leanvm_univariate::Claims;
use leanvm_univariate::contract::{NAME, Recorded, record_verifier};

const STREAM_AT: usize = 4 + 32;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn vector(name: &str) -> vectors::Vector {
    let path = format!(
        "{}/../leanvm_univariate/tests/vectors/{name}.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    vectors::read(&std::fs::read_to_string(&path).expect("a committed vector"))
}

fn compiled(recorded: &Recorded, layout: Layout, iv: [u8; 32], public: [u8; 32], stream: &[u8]) -> Compiled {
    let c = pi2(
        recorded,
        layout,
        &Inputs {
            program_iv: PROGRAM_IV,
            public,
            stream,
        },
    );
    assert_eq!(c.pi1_iv, iv, "the circuit's seed hashes the recorded verifier's contract IV");
    c
}

/// Keccak-f's positions a permutation, by layout (SPEC-REC.md §2.4.1, §2.6; D16v's `kd` rows as measured by
/// `circuit::tests::d16_rows_a_permutation`).
fn keccak_positions(layout: Layout) -> usize {
    match layout {
        Layout::D16v => 16 * (1536 + 6144 + 160 + 344),
        Layout::D32v => 32 * 25 * 64,
    }
}

fn report(name: &str, layout: &str, c: &Compiled) {
    let s = &c.finished.stats;
    println!(
        "{name} {layout}: N = 2^{} ({} positions used, {:.1}%), {} rows, {} blocks, {} selector pairs, {} regions",
        s.log_n,
        s.positions_used,
        100.0 * s.fill(),
        s.rows_used,
        s.blocks,
        s.pairs,
        s.rows.len()
    );
    println!(
        "  Keccak-256 calls {}, Keccak-f {}, packings {}, free bits (alone, with a copy) {:?}, E units (ended, forwarded) mul {:?} add {:?} square {:?}",
        c.keccak_calls, c.permutations, c.packings, c.free_bits, c.arith[0], c.arith[1], c.arith[2]
    );
    println!(
        "  values {}, free {}, junk {}, free ends {}, dead slots {}, kappa {}, ports {}, forwards placed {} / unplaced {}",
        s.values,
        s.free_values,
        s.junk,
        s.free_ends,
        s.dead_slots,
        s.kappa,
        s.ports,
        s.forwards_placed,
        s.forwards_unplaced
    );
    println!(
        "  rows in blocks (padding included) {}, the verifier's formulas: {} terms, {} products; quotient 15N = 2^{:.2} words",
        s.rows_in_blocks,
        s.formula_terms,
        s.formula_products,
        (15.0f64).log2() + s.log_n as f64
    );
    let w = 1usize << s.log_width;
    for (region, rows) in &s.rows {
        println!("  {region:<22} {rows:>9} rows {:>10} positions", rows * w);
    }
}

/// `(log N, the fill's bounds)` expected (SPEC-REC.md §2.4.5, §2.6: D16v × π1-rec `2^24` at 86%, D32v × π1 `2^23`
/// at 84%).
fn run(name: &str, layout: Layout, log_n: u8, fill: (f64, f64)) {
    let v = vector(name);
    let blake2s = vectors::blake2s_of(&v.config);
    let recorded = record_verifier(&v.shape, blake2s, Claims::Point);
    let stream = v.calldata[STREAM_AT..].to_vec();
    let iv = recorded.iv(&PROGRAM_IV);
    let c = compiled(&recorded, layout, iv, v.public, &stream);
    let s = &c.finished.stats;
    report(name, &format!("{layout:?}"), &c);
    // The counts: N, the fill, Keccak-f's positions, a block or two a region.
    assert_eq!(s.log_n, log_n, "{name} {layout:?}: N");
    assert!(
        fill.0 <= s.fill() && s.fill() <= fill.1,
        "{name} {layout:?}: the fill {}",
        s.fill()
    );
    let keccak: usize = s
        .rows
        .iter()
        .filter(|(r, _)| r.starts_with("keccak"))
        .map(|(_, &n)| n)
        .sum();
    assert_eq!(
        keccak << s.log_width,
        c.permutations * keccak_positions(layout),
        "{name}: Keccak-f's positions"
    );
    assert!(
        s.blocks <= 2 * s.rows.len(),
        "{name}: at most two blocks a region on average"
    );
    let circuit = &c.finished.circuit;
    let w = &c.finished.witness;

    // Every pull equals its push, and the public side holds.
    assert_eq!(
        circuit.check(w, &c.public),
        Ok(()),
        "{name} {layout:?}: the circuit holds"
    );
    // The calls on the public inputs are the vector's PCS_OPEN inputs in PCS_OPEN's ABI (REVIEW-REC.md M1: each
    // root word `machine::root_word` of the hash π1's own contract passes as it is).
    let abi: Vec<Vec<u8>> = v
        .calls
        .iter()
        .map(|input| {
            let mut x = input.clone();
            let raw: [u8; 32] = x[..32].try_into().expect("a root");
            x[..32].copy_from_slice(&leanvm_flock_gas::evm::machine::root_word(&raw));
            x
        })
        .collect();
    assert_eq!(circuit.call_inputs(&c.public), abi, "{name}: the calls are the vector's");
    assert_eq!(
        circuit.public_from_calls(v.public, &abi).as_ref(),
        Some(&c.public),
        "{name}: the public inputs are read back from the calls"
    );
    // The digests and the elements are the evaluator's.
    let seed = keccak_seed(&NAME, &iv, &v.public);
    let values = evaluate(&c.expanded, seed, &v.public, &stream);
    for (&id, digest) in &c.digests {
        let mut bytes = [0u8; 32];
        for (i, &d) in digest.iter().enumerate() {
            bytes[i / 8] |= (c.finished.words[d as usize].0 as u8) << (i % 8);
        }
        assert_eq!(Value::State(bytes), values[id as usize], "{name}: digest of node {id}");
    }
    for (&id, limbs) in &c.limbs {
        let x = values[id as usize].e();
        let words = limbs.map(|l| c.finished.words[l as usize]);
        assert_eq!(
            words,
            [K(x.c0), K(x.c1), K(x.c2)],
            "{name}: the limbs of node {id} ({:?})",
            c.expanded.nodes[id as usize]
        );
    }
    println!("  checked: {} digests, {} elements", c.digests.len(), c.limbs.len());

    // A changed public input is caught.
    let mut other = c.public.clone();
    other.statement[5] ^= 1;
    assert!(
        matches!(circuit.check(w, &other), Err(Failure::Public { .. })),
        "{name}: the statement"
    );
    let mut other = c.public.clone();
    other.elements[3].c1 ^= 1 << 7;
    assert!(
        matches!(circuit.check(w, &other), Err(Failure::Public { .. })),
        "{name}: an element"
    );
    let mut other = c.public.clone();
    other.roots[1][9] ^= 1;
    assert!(
        matches!(circuit.check(w, &other), Err(Failure::Public { .. })),
        "{name}: a root"
    );
    // A changed witness word at wired positions is caught.
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let wired: Vec<usize> = (0..circuit.n()).filter(|&i| circuit.sigma[i] as usize != i).collect();
    for _ in 0..30 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let i = wired[seed as usize % wired.len()];
        let mut bad = w.clone();
        bad[i] = bad[i] + K(1 << (seed % 64));
        assert!(
            circuit.check(&bad, &c.public).is_err(),
            "{name}: a change at {i} is caught"
        );
    }
    // A flipped stream byte (hashed, and in the middle) gives another witness the public side rejects.
    let mut mutated = stream.clone();
    mutated[stream.len() / 2] ^= 1;
    let m = compiled(&recorded, layout, iv, v.public, &mutated);
    assert_eq!(
        m.finished.circuit.sigma, circuit.sigma,
        "the circuit does not depend on the proof"
    );
    assert_eq!(
        m.finished.circuit.kappa, circuit.kappa,
        "the circuit does not depend on the proof"
    );
    assert!(
        matches!(
            circuit.check(&m.finished.witness, &c.public),
            Err(Failure::Public { .. })
        ),
        "{name}: a flipped stream byte is caught"
    );
    let zero_checks = recorded.graph.zero.len();
    let nodes = c.expanded.nodes.iter().filter(|n| matches!(n, Node::Mul(..))).count();
    println!("  mutations caught; {zero_checks} zero checks, {nodes} products in the expanded graph");
}

/// The recommendation: D16v on π1-rec, `2^24` positions, the quotient `15N = 2^27.91` words, under `2^28`.
#[test]
fn pi1_rec_d16v() {
    deep(|| run("main_line_rec", Layout::D16v, 24, (0.80, 0.90)));
}

/// π1-rec2 (SPEC-REC.md §12): the walk of the BLAKE2s circuit in π1's verifier, no claims on `A0`, `B0`: still `2^24`.
#[test]
fn pi1_rec2_d16v() {
    deep(|| run("main_line_rec2", Layout::D16v, 24, (0.80, 0.99)));
}

/// π1-rec3 (SPEC-REC.md §12, SPEC-POINTS.md): π1-rec2 with the batch two variables a round: still `2^24`.
#[test]
fn pi1_rec3_d16v() {
    deep(|| run("main_line_rec3", Layout::D16v, 24, (0.80, 0.99)));
}

#[test]
fn pi1_rec_d32v() {
    deep(|| run("main_line_rec", Layout::D32v, 23, (0.60, 0.75)));
}

/// D16v on the main line does not fit `2^24` (131 permutations): `2^25`, a quotient of `2^28.91` words.
#[test]
fn main_line_d16v() {
    deep(|| run("main_line", Layout::D16v, 25, (0.45, 0.60)));
}

/// The fallback: D32v on the main line, `2^23` positions, `Q` `2^26.91`.
#[test]
fn main_line_d32v() {
    deep(|| run("main_line", Layout::D32v, 23, (0.80, 0.90)));
}
