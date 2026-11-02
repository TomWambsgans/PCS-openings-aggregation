// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The prover on real leanVM 42422001 traces (`src/prover/dump`, PROVER.md): SPEC.md's identities on the domain, the
//! quotients' degrees, every combined relation at `t`, the verifier's acceptance of the proof, and its rejection of
//! mutated proofs.
//!
//! `LEANVM_TRACE=<dir of one trace>` (the directory `trace_dump.rs` wrote), then
//! `cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture`.

use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_univariate::prover::check::on_domain;
use leanvm_univariate::prover::prove::{Config, prove, verify};
use leanvm_univariate::prover::trace::Trace;
use leanvm_univariate::{Blake2s, Claims};
use primitives::field::F192;

fn trace() -> Option<Trace> {
    let dir = std::env::var("LEANVM_TRACE").ok()?;
    let started = std::time::Instant::now();
    let trace = Trace::load(std::path::Path::new(&dir)).expect("a trace");
    println!("trace {dir}: loaded in {:.2} s, rows {:?}, heights {:?}", started.elapsed().as_secs_f64(), trace.rows, trace.heights);
    Some(trace)
}

#[test]
#[ignore]
fn identities_hold_on_the_domain() {
    let Some(trace) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to check");
        return;
    };
    parallel::init();
    let alphas = [F192::new(3, 1, 4), F192::new(1, 5, 9), F192::new(2, 6, 5), F192::new(3, 5, 8)];
    let checks = on_domain(&trace, &alphas, F192::new(9, 7, 9));
    let mut failed = false;
    for c in &checks {
        println!("{:>9} / {:>9} fail: {}", c.failures, c.tested, c.name);
        failed |= c.failures > 0 && !c.name.contains("informative");
    }
    assert!(!failed, "an identity fails on the domain");
}

#[test]
#[ignore]
fn proves_and_verifies() {
    let Some(trace) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to prove");
        return;
    };
    parallel::init();
    let config = Config {
        blake2s: Blake2s::Omitted,
        claims: Claims::Point,
        check: true,
    };
    let started = std::time::Instant::now();
    let (proof, report) = prove(&trace, &PROGRAM_IV, config).expect("a proof");
    let total = started.elapsed().as_secs_f64();
    for (phase, secs) in &report.phases {
        println!("  {secs:8.3} s  {phase}");
    }
    println!("  {total:8.3} s  total; peak RSS {:.2} GB", bench::peak_rss_bytes() as f64 / 1e9);
    for (name, degree, count, m) in &report.quotients {
        println!("  quotient {name}: degree {degree}, the verifier's count {count} (2^{:.3}), extension 2^{m}", (*count as f64).log2());
    }
    for (c, placed, vars) in &report.stacks {
        println!("  stack {c:?}: {placed} words placed (2^{:.3}), 2^{vars}", (*placed as f64).log2());
    }
    for (name, ok) in &report.checks {
        println!("  check {}: {name}", if *ok { "ok  " } else { "FAIL" });
    }
    println!("  stream {} bytes; openings {:?} bytes", report.stream_bytes, report.opening_bytes);
    assert!(report.checks.iter().all(|(_, ok)| *ok));
    let shape = trace.shape();
    let public = trace.public_input();
    let started = std::time::Instant::now();
    verify(&shape, &PROGRAM_IV, &public, &proof, Blake2s::Omitted).expect("the verifier accepts");
    println!("  verified (reduce + 3 WHIR openings) in {:.3} s", started.elapsed().as_secs_f64());

    // Mutations: a value at t, a root byte, a sumcheck round, a final value, an opening's value.
    let mut rejected = 0;
    let len = proof.stream.len();
    for &at in &[0usize, 40, len / 2, len - 30, len - 100] {
        let mut bad = proof.stream.clone();
        bad[at] ^= 1;
        let mutated = leanvm_univariate::prover::prove::Proof {
            stream: bad,
            openings: proof
                .openings
                .iter()
                .map(|o| leanvm_univariate::prover::prove::OpeningProof {
                    commitment: o.commitment,
                    root: o.root,
                    vars: o.vars,
                    placed: o.placed,
                    point: o.point.clone(),
                    value: o.value,
                    proof: o.proof.clone(),
                })
                .collect(),
        };
        let verdict = verify(&shape, &PROGRAM_IV, &public, &mutated, Blake2s::Omitted);
        println!("  stream byte {at} flipped: {}", verdict.as_ref().err().map_or("ACCEPTED".to_string(), |e| e.clone()));
        rejected += verdict.is_err() as usize;
    }
    assert_eq!(rejected, 5, "every mutation is rejected");
}
