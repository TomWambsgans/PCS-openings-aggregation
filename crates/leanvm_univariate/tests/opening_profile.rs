// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Where a WHIR opening of `A0` (`2^28` words, the BLAKE2s R1CS) spends its time (ignored): its density, the commit,
//! and the opening with leanVM's tracing spans printed.
//!
//! `cargo test --release -p leanvm_univariate --test opening_profile -- --ignored --nocapture`

use leanvm_univariate::prover::opening;
use primitives::field::F192;

#[test]
#[ignore]
fn a0_opening_profile() {
    parallel::init();
    let started = std::time::Instant::now();
    let (a0, _) = leanvm_univariate::prover::matrices::setup_matrices();
    let nonzero = a0.iter().filter(|w| !w.is_zero()).count();
    println!(
        "A0 built in {:.2} s: {nonzero} nonzero words of {} (2^{:.1})",
        started.elapsed().as_secs_f64(),
        a0.len(),
        (nonzero as f64).log2()
    );
    let started = std::time::Instant::now();
    let committed = opening::commit(&a0, 28, 1 << 28);
    println!("committed in {:.2} s", started.elapsed().as_secs_f64());
    let point: Vec<F192> = (0..28u64).map(|i| F192::new(0x9e37_79b9 ^ i, i * 7 + 1, 3 * i + 5)).collect();
    let value = primitives::multilinear::mle_eval_par(&a0, &point);
    let layout = leanvm_univariate::contract::layout_word(&leanvm_univariate::Shape {
        log_memory: 21,
        log_bytecode: 19,
        table_rows: [183266, 195439, 223851, 137591, 80937, 202025],
    }, 0x5504, 28, 1 << 28);
    bench::trace::init_tracing();
    let started = std::time::Instant::now();
    let proof = opening::open(&a0, &committed, &layout, &point, value);
    println!("opened in {:.2} s", started.elapsed().as_secs_f64());
    opening::verify(&committed.root, &layout, &point, value, &opening::wire_proof(&proof)).expect("verifies");
}
