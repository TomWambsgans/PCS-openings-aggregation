// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! One opening timed alone, at `C1`'s shape on the 1,000-signature trace (`2^27` variables, 50 lanes of `2^21`
//! words), from a commitment that keeps its codeword and from one that does not (the same proof), and checked with
//! the verifier. `BENCH_TRACING=1` prints WHIR's own spans:
//! `cargo test --release -p leanvm_univariate --test prove_openings -- --ignored --nocapture`.

use leanvm_univariate::prover::opening;
use primitives::field::{F64, F192};

#[test]
#[ignore]
fn opening_at_the_reference_shape() {
    parallel::init();
    bench::init_tracing_from_env();
    let (vars, lanes) = (27usize, 50usize);
    let mut state = 7u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut words: Vec<F64> = (0..1usize << vars).map(|_| F64(next())).collect();
    let point: Vec<F192> = (0..vars).map(|_| F192::new(next(), next(), next())).collect();
    words[lanes << (vars - opening::LANE_FOLD)..].fill(F64::ZERO);
    let value = primitives::multilinear::mle_eval_par(&words, &point);
    words.truncate(lanes << (vars - opening::LANE_FOLD));
    let placed = words.len() as u64;
    // A layout word carrying the stack's variables and placed words (`contract::layout_word`'s bytes 24..32).
    let mut layout = [0u8; 32];
    layout[24] = vars as u8;
    layout[25..].copy_from_slice(&placed.to_be_bytes()[1..]);
    let mut proofs = Vec::new();
    for keep in [false, true] {
        let started = std::time::Instant::now();
        let committed = if keep {
            opening::commit_keeping_codeword(&words, vars, placed)
        } else {
            opening::commit(&words, vars, placed)
        };
        println!(
            "  commit (codeword kept: {keep}) {:.3} s",
            started.elapsed().as_secs_f64()
        );
        let started = std::time::Instant::now();
        let proof = opening::open(&words, &committed, &layout, &point, value);
        println!(
            "  open (codeword kept: {keep}) {:.3} s",
            started.elapsed().as_secs_f64()
        );
        opening::verify(&committed.root, &layout, &point, value, &opening::wire_proof(&proof)).expect("verifies");
        proofs.push(proof);
    }
    let same = |a: &fiat_shamir::transcript::Proof, b: &fiat_shamir::transcript::Proof| {
        a.stream == b.stream
            && a.merkle.len() == b.merkle.len()
            && a.merkle
                .iter()
                .zip(&b.merkle)
                .all(|(x, y)| x.leaf_data == y.leaf_data && x.sibling_hashes == y.sibling_hashes)
    };
    assert!(same(&proofs[0], &proofs[1]), "the same proof");
}
