// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The prover on real leanVM 42422001 traces (`src/prover/dump`, PROVER.md): SPEC.md's identities on the domain, the
//! quotients' degrees, every combined relation at `t`, the Rust verifier's and the EVM contract's acceptance of the
//! proof (the contract's `PCS_OPEN` calls being exactly the claims the WHIR openings prove, and Flock's `A0`, `B0`
//! claims the matrices' values), and the rejection of mutated proofs.
//!
//! `LEANVM_TRACE=<dir of one trace>` (the directory `trace_dump.rs` wrote), then, built with
//! `RUSTFLAGS="-C target-cpu=native"` as leanVM is,
//! `cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1`.

use leanvm_flock_gas::evm::codegen::word;
use leanvm_flock_gas::evm::machine::{PcsOpen, call, element_word};
use leanvm_flock_gas::layout::OP_BLAKE2S;
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{SetupRoots, calldata, compile_verifier, layout_words, record_verifier};
use leanvm_univariate::prover::check::on_domain;
use leanvm_univariate::prover::flock::FlockWitness;
use leanvm_univariate::prover::opening;
use leanvm_univariate::prover::poly::to_v;
use leanvm_univariate::prover::prove::{Config, OpeningProof, Proof, prove, verify};
use leanvm_univariate::prover::trace::{Trace, placement};
use leanvm_univariate::{Blake2s, Claims, FLOCK_LEANVM_SKIP, FLOCK_MAIN, Shape};
use primitives::field::F192;

fn dir() -> Option<std::path::PathBuf> {
    std::env::var("LEANVM_TRACE").ok().map(std::path::PathBuf::from)
}

/// The trace, its rows placed at the verifier's positions (`Trace::place`), and the placement's time.
fn trace() -> Option<(Trace, f64)> {
    let dir = dir()?;
    let started = std::time::Instant::now();
    let mut trace = Trace::load(&dir).expect("a trace");
    let loaded = started.elapsed().as_secs_f64();
    let started = std::time::Instant::now();
    parallel::init();
    trace.place();
    let placed = started.elapsed().as_secs_f64();
    println!(
        "trace {}: loaded in {loaded:.2} s, placed in {placed:.2} s, rows {:?}, heights {:?}, memory 2^{}, bytecode 2^{}",
        dir.display(),
        trace.rows,
        trace.heights,
        trace.log_memory,
        trace.log_bytecode
    );
    Some((trace, placed))
}

/// The reference shape (1,000 signatures, memory `2^21`, bytecode `2^19`): its setup root is the contract's
/// `SetupRoots::REFERENCE.f`, which `contract::rust_verifier` binds whatever the shape.
fn is_reference(shape: &Shape) -> bool {
    shape.log_memory == 21 && shape.log_bytecode == 19 && shape.heights() == [18, 18, 18, 18, 17, 18]
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
                layout: o.layout,
                vars: o.vars,
                placed: o.placed,
                point: o.point.clone(),
                value: o.value,
                proof: o.proof.clone(),
            })
            .collect(),
    }
}

fn number(n: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..].copy_from_slice(&n.to_be_bytes());
    b
}

#[test]
#[ignore]
fn identities_hold_on_the_domain() {
    let Some((trace, _)) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to check");
        return;
    };
    let alphas = [F192::new(3, 1, 4), F192::new(1, 5, 9), F192::new(2, 6, 5), F192::new(3, 5, 8)];
    let checks = on_domain(&trace, &alphas, F192::new(9, 7, 9));
    let mut failed = false;
    for c in &checks {
        println!("{:>9} / {:>9} fail: {}", c.failures, c.tested, c.name);
        failed |= c.failures > 0 && !c.name.contains("informative");
    }
    assert!(!failed, "an identity fails on the domain");
}

/// Prove, verify (Rust and EVM), mutate.
fn end_to_end(blake2s: Blake2s) {
    let Some((trace, mut placing)) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to prove");
        return;
    };
    let flock = match blake2s {
        Blake2s::Flock(_) => {
            let mut witness = FlockWitness::load(&dir().expect("a trace")).expect("Flock's inputs");
            let started = std::time::Instant::now();
            witness.place(&placement(trace.rows[OP_BLAKE2S], trace.heights[OP_BLAKE2S]));
            placing += started.elapsed().as_secs_f64();
            Some(witness)
        }
        Blake2s::Omitted => None,
    };
    let config = Config {
        blake2s,
        claims: Claims::Point,
        check: true,
        garbage: false,
        stand_in_roots: None,
        roots: SetupRoots::REFERENCE,
    };
    let started = std::time::Instant::now();
    let (proof, report) = prove(&trace, flock.as_ref(), &PROGRAM_IV, config).expect("a proof");
    let total = started.elapsed().as_secs_f64();
    drop(flock);
    println!("  {placing:8.3} s  placement: the rows (and Flock's instances) at the verifier's positions");
    for (phase, secs) in &report.phases {
        println!("  {secs:8.3} s  {phase}");
    }
    println!(
        "  {:8.3} s  total ({total:.3} s and the placement); peak RSS {:.2} GB",
        total + placing,
        bench::peak_rss_bytes() as f64 / 1e9
    );
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
    // The proof's fingerprint: a change of the prover that keeps the proof keeps this line.
    println!(
        "  stream keccak {}",
        leanvm_univariate::prover::setup::hex(&leanvm_flock_gas::transcript::keccak256(&proof.stream))
    );
    assert!(report.checks.iter().all(|(_, ok)| *ok));
    let shape = trace.shape();
    let public = trace.public_input();
    let started = std::time::Instant::now();
    let reference = is_reference(&shape);
    verify(&shape, &PROGRAM_IV, &public, &proof, blake2s, reference).expect("the verifier accepts");
    println!(
        "  verified (reduce + 3 WHIR openings) in {:.3} s; the setup's root {} the contract's",
        started.elapsed().as_secs_f64(),
        if reference { "is" } else { "is this shape's, not (the verifier binds the reference shape's)" }
    );

    // The contract on the real calldata: its PCS_OPEN mock attests exactly the claims the openings prove (the setup's
    // root being the contract's constant, the layout words the contract's) and Flock's A0, B0 claims, which are the
    // matrices' values.
    let words = layout_words(&shape);
    let roots = SetupRoots::REFERENCE;
    let mut inputs: Vec<Vec<u8>> = Vec::new();
    for o in &proof.openings {
        let root = match o.commitment {
            Commitment::Setup => roots.f,
            _ => o.root,
        };
        let mut input = root.to_vec();
        input.extend(o.layout);
        input.extend(number(1));
        for &x in o.point.iter().chain([&o.value]) {
            input.extend(element_word(to_v(x)));
        }
        inputs.push(input);
    }
    if let Some((point, a, b)) = &report.flock {
        for (root, layout, value) in [(roots.a0, words[3], *a), (roots.b0, words[4], *b)] {
            let mut input = root.to_vec();
            input.extend(layout);
            input.extend(number(1));
            for &x in point.iter().chain([&value]) {
                input.extend(element_word(x));
            }
            inputs.push(input);
        }
    }
    let attesting = |skip: Option<usize>| {
        let mut pcs = PcsOpen::default();
        for (k, input) in inputs.iter().enumerate() {
            if Some(k) != skip {
                pcs.register(input.clone());
            }
        }
        pcs
    };
    let blocks: Vec<PcsOpen> = std::iter::once(attesting(None)).chain((0..inputs.len()).map(|k| attesting(Some(k)))).collect();
    let data = calldata(&public, &proof.stream);
    let stream = proof.stream.clone();
    let (accepted, rejected, gas, linked) = deep(move || {
        let recorded = record_verifier(&shape, blake2s, Claims::Point);
        assert_eq!(recorded.stream_len, stream.len(), "the contract's stream is the proof's");
        // The measuring build, word for word against the Rust verifier, on this accepting stream.
        leanvm_univariate::contract::parity(&shape, &PROGRAM_IV, &public, &stream, blake2s, Claims::Point);
        let contract = compile_verifier(&recorded, &PROGRAM_IV, false);
        let one = word([1, 0, 0]);
        let accepts = |data: &[u8], block: &PcsOpen| call(&contract.code, &[], data, block).output.as_deref() == Some(&one[..]);
        let ok = call(&contract.code, &[], &data, &blocks[0]);
        let mut bad = data.clone();
        let last = bad.len() - 1;
        bad[last] ^= 1;
        let mut rejected = accepts(&bad, &blocks[0]) as usize;
        // Every call must be attested.
        rejected += blocks[1..].iter().filter(|b| accepts(&data, b)).count();
        // The deployable verifying build (crates/evm_link, contracts of at most 24,576 bytes), likewise.
        use leanvm_flock_gas::evm::codegen::{Ending, Entry, compile_deployable};
        let call_words = leanvm_univariate::contract::calls(&recorded);
        let ending = Ending::PcsOpen(call_words.iter().map(Vec::len).collect());
        let entry = Entry {
            name: leanvm_univariate::contract::NAME,
            iv: leanvm_univariate::contract::contract_iv(&recorded.shape, &PROGRAM_IV, &recorded.roots),
            stream_len: recorded.stream_len,
            measure: false,
        };
        let real = compile_deployable(&recorded.graph, &call_words.concat(), &ending, &entry, 24_576);
        let deployed = leanvm_flock_gas::evm::contract::deploy(&real, &[]);
        let linked = |data: &[u8], block: &PcsOpen| {
            deployed.chain.call(deployed.address, data, block).output.as_deref() == Some(&one[..])
        };
        let linked_ok = linked(&data, &blocks[0]) && !linked(&bad, &blocks[0]) && blocks[1..].iter().all(|b| !linked(&data, b));
        (ok.output.clone(), rejected, ok.execution, (deployed.contracts.len(), linked_ok))
    });
    println!(
        "  the contract returns {:?} on the real proof, {gas} gas of execution; parity with the Rust verifier; the \
         deployable build ({} contracts) accepts it: {}",
        accepted.as_ref().map(|o| o[31]),
        linked.0,
        linked.1
    );
    assert_eq!(accepted.as_deref(), Some(&word([1, 0, 0])[..]), "the contract accepts the real proof");
    assert_eq!(rejected, 0, "the contract rejects a mutated proof, and a proof with one call not attested");
    assert!(linked.1, "the deployable build accepts the real proof, and rejects the mutations");

    // Flock's two setup claims, opened: A0 and B0 committed with WHIR (2^28 words each) and opened at the claim's point.
    if let Some((point, a, b)) = &report.flock {
        let started = std::time::Instant::now();
        let [(a0, a0c), (b0, b0c)] = leanvm_univariate::prover::setup::matrices();
        println!("  A0, B0 built and committed in {:.2} s", started.elapsed().as_secs_f64());
        let point: Vec<F192> = point.iter().map(|&x| leanvm_univariate::prover::poly::from_v(x)).collect();
        let layouts = layout_words(&trace.shape());
        for (name, layout, root, words, committed, value) in
            [("A0", layouts[3], roots.a0, a0, a0c, *a), ("B0", layouts[4], roots.b0, b0, b0c, *b)]
        {
            assert_eq!(committed.root, root, "{name}: the contract's root");
            let value = leanvm_univariate::prover::poly::from_v(value);
            assert_eq!(primitives::multilinear::mle_eval_par(&words, &point), value, "{name} at the claim's point");
            let started = std::time::Instant::now();
            let proof = opening::open(&words, &committed, &layout, &point, value);
            let open = started.elapsed().as_secs_f64();
            drop(words);
            opening::verify(&committed.root, &layout, &point, value, &opening::wire_proof(&proof))
                .expect("the setup opening verifies");
            println!(
                "  {name}: root {}, opened in {open:.2} s, verified",
                leanvm_univariate::prover::setup::hex(&committed.root)
            );
        }
    }

    // Mutations: a root, a value early on, the middle, a final value, a sumcheck round.
    let mut refused = 0;
    let len = proof.stream.len();
    for &at in &[0usize, 40, len / 2, len - 30, len - 100] {
        let mut bad = proof.stream.clone();
        bad[at] ^= 1;
        let verdict = verify(&trace.shape(), &PROGRAM_IV, &public, &copy(&proof, bad), blake2s, reference);
        println!(
            "  stream byte {at} flipped: {}",
            verdict.as_ref().err().map_or("ACCEPTED".to_string(), |e| e.clone())
        );
        refused += verdict.is_err() as usize;
    }
    assert_eq!(refused, 5, "every mutation is rejected");
}

#[test]
#[ignore]
fn proves_and_verifies() {
    end_to_end(Blake2s::Omitted);
}

/// With BLAKE2s's argument: leanVM's Flock prover (skip 6, the slices sent), the matrices' reduction, the ring
/// switch's weight on `q_flock`.
#[test]
#[ignore]
fn proves_and_verifies_with_flock() {
    end_to_end(Blake2s::Flock(FLOCK_LEANVM_SKIP));
}

/// The main line: Flock (a′), its skip of 3 and the ring map in tower order (`FLOCK_MAIN`).
#[test]
#[ignore]
fn proves_and_verifies_main_line() {
    end_to_end(Blake2s::Flock(FLOCK_MAIN));
}

/// The setup roots a contract for this trace's program and shape is generated with (review M1's F2): `F` from the
/// program and the shape, `A0` and `B0` from Flock's BLAKE2s R1CS.
#[test]
#[ignore]
fn setup_roots() {
    let Some((trace, _)) = trace() else {
        println!("LEANVM_TRACE is not set: no program");
        return;
    };
    let started = std::time::Instant::now();
    let setup = leanvm_univariate::prover::columns::setup_polys(&trace);
    let roots = leanvm_univariate::prover::setup::roots(&trace.shape(), &setup);
    use leanvm_univariate::prover::setup::hex;
    println!("  shape {:?}", trace.shape());
    println!("  F  {}", hex(&roots.f));
    println!("  A0 {}", hex(&roots.a0));
    println!("  B0 {}", hex(&roots.b0));
    println!("  in {:.2} s", started.elapsed().as_secs_f64());
}

/// The verifier relies on nothing in the stacks' words past their blocks: filled with pseudo-random words, the
/// proof is accepted all the same.
#[test]
#[ignore]
fn unused_words_are_not_relied_on() {
    let Some((trace, _)) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to prove");
        return;
    };
    let config = Config {
        blake2s: Blake2s::Omitted,
        claims: Claims::Point,
        check: true,
        garbage: true,
        stand_in_roots: None,
        roots: SetupRoots::REFERENCE,
    };
    let (proof, report) = prove(&trace, None, &PROGRAM_IV, config).expect("a proof");
    for (c, placed, vars) in &report.stacks {
        println!("  stack {c:?}: words {placed}.. up to its last lane pseudo-random (2^{vars})");
    }
    assert!(report.checks.iter().all(|(_, ok)| *ok));
    let reference = is_reference(&trace.shape());
    verify(&trace.shape(), &PROGRAM_IV, &trace.public_input(), &proof, Blake2s::Omitted, reference).expect("accepted");
    println!("  accepted");
}
