// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The prover on real leanVM 42422001 traces (`src/prover/dump`, PROVER.md): SPEC.md's identities on the domain, the
//! quotients' degrees, every combined relation at `t`, the Rust verifier's and the EVM contract's acceptance of the
//! proof (the contract's `PCS_OPEN` calls being exactly the claims the WHIR openings prove), and the rejection of
//! mutated proofs.
//!
//! `LEANVM_TRACE=<dir of one trace>` (the directory `trace_dump.rs` wrote), then, built with
//! `RUSTFLAGS="-C target-cpu=native"` as leanVM is,
//! `cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1`.

use leanvm_flock_gas::evm::codegen::word;
use leanvm_flock_gas::evm::machine::{PcsOpen, call, element_word};
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{calldata, compile_verifier, record_verifier};
use leanvm_univariate::prover::check::on_domain;
use leanvm_univariate::prover::poly::to_v;
use leanvm_univariate::prover::prove::{Config, OpeningProof, Proof, layout_word, prove, verify};
use leanvm_univariate::prover::trace::Trace;
use leanvm_univariate::{Blake2s, Claims};
use primitives::field::F192;

fn trace() -> Option<Trace> {
    let dir = std::env::var("LEANVM_TRACE").ok()?;
    let started = std::time::Instant::now();
    let trace = Trace::load(std::path::Path::new(&dir)).expect("a trace");
    println!(
        "trace {dir}: loaded in {:.2} s, rows {:?}, heights {:?}, memory 2^{}, bytecode 2^{}",
        started.elapsed().as_secs_f64(),
        trace.rows,
        trace.heights,
        trace.log_memory,
        trace.log_bytecode
    );
    Some(trace)
}

/// Run `f` on a thread with a deep stack: the code generator recurses along the graph.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn copy(proof: &Proof, stream: Vec<u8>) -> Proof {
    Proof {
        stream,
        openings: proof
            .openings
            .iter()
            .map(|o| OpeningProof {
                commitment: o.commitment,
                root: o.root,
                vars: o.vars,
                placed: o.placed,
                point: o.point.clone(),
                value: o.value,
                proof: o.proof.clone(),
            })
            .collect(),
    }
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
        garbage: false,
    };
    let started = std::time::Instant::now();
    let (proof, report) = prove(&trace, &PROGRAM_IV, config).expect("a proof");
    let total = started.elapsed().as_secs_f64();
    for (phase, secs) in &report.phases {
        println!("  {secs:8.3} s  {phase}");
    }
    println!("  {total:8.3} s  total; peak RSS {:.2} GB", bench::peak_rss_bytes() as f64 / 1e9);
    for (name, degree, count, m) in &report.quotients {
        println!(
            "  quotient {name}: degree {degree}, the verifier's count {count} (2^{:.3}), extension 2^{m}",
            (*count as f64).log2()
        );
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

    // The contract on the real calldata: its PCS_OPEN mock attests exactly the three claims the openings prove (the
    // setup's root being the contract's constant).
    let mut pcs = PcsOpen::default();
    for o in &proof.openings {
        let root = match o.commitment {
            Commitment::Setup => word([0x1111, 0x2222, 0x3333]),
            _ => o.root,
        };
        let mut input = root.to_vec();
        for n in [layout_word(o.commitment), 1] {
            let mut b = [0u8; 32];
            b[24..].copy_from_slice(&n.to_be_bytes());
            input.extend(b);
        }
        for &x in o.point.iter().chain([&o.value]) {
            input.extend(element_word(to_v(x)));
        }
        pcs.register(input);
    }
    let data = calldata(&public, &proof.stream);
    let stream = proof.stream.clone();
    let (accepted, rejected, gas) = deep(move || {
        let recorded = record_verifier(&shape, Blake2s::Omitted, Claims::Point);
        assert_eq!(recorded.stream_len, stream.len(), "the contract's stream is the proof's");
        let contract = compile_verifier(&recorded, &PROGRAM_IV, false);
        let ok = call(&contract.code, &[], &data, &pcs);
        let mut bad = data.clone();
        let last = bad.len() - 1;
        bad[last] ^= 1;
        let no = call(&contract.code, &[], &bad, &pcs);
        (ok.output.clone(), no.output.is_some(), ok.execution)
    });
    println!("  the contract returns {accepted:02x?} on the real proof, {gas} gas of execution");
    assert_eq!(accepted.as_deref(), Some(&word([1, 0, 0])[..]), "the contract accepts the real proof");
    assert!(!rejected, "the contract rejects a mutated proof");

    // Mutations: a root, a value at t, the middle, a final value, a sumcheck round.
    let mut refused = 0;
    let len = proof.stream.len();
    for &at in &[0usize, 40, len / 2, len - 30, len - 100] {
        let mut bad = proof.stream.clone();
        bad[at] ^= 1;
        let verdict = verify(&trace.shape(), &PROGRAM_IV, &public, &copy(&proof, bad), Blake2s::Omitted);
        println!(
            "  stream byte {at} flipped: {}",
            verdict.as_ref().err().map_or("ACCEPTED".to_string(), |e| e.clone())
        );
        refused += verdict.is_err() as usize;
    }
    assert_eq!(refused, 5, "every mutation is rejected");
}

/// The verifier relies on nothing in the stacks' words past their blocks: filled with pseudo-random words, the
/// proof is accepted all the same.
#[test]
#[ignore]
fn unused_words_are_not_relied_on() {
    let Some(trace) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to prove");
        return;
    };
    parallel::init();
    let config = Config {
        blake2s: Blake2s::Omitted,
        claims: Claims::Point,
        check: true,
        garbage: true,
    };
    let (proof, report) = prove(&trace, &PROGRAM_IV, config).expect("a proof");
    for (c, placed, vars) in &report.stacks {
        println!("  stack {c:?}: words {placed}.. up to its last lane pseudo-random (2^{vars})");
    }
    assert!(report.checks.iter().all(|(_, ok)| *ok));
    verify(&trace.shape(), &PROGRAM_IV, &trace.public_input(), &proof, Blake2s::Omitted).expect("accepted");
    println!("  accepted");
}
