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
use leanvm_flock_gas::evm::machine::{PcsOpen, call, element_word, root_of_word};
use leanvm_flock_gas::layout::OP_BLAKE2S;
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{SetupRoots, calldata, compile_verifier, layout_words, record_verifier_with};
use leanvm_univariate::prover::check::on_domain;
use leanvm_univariate::prover::flock::FlockWitness;
use leanvm_univariate::prover::opening;
use leanvm_univariate::prover::poly::to_v;
use leanvm_univariate::prover::prove::{Config, OpeningProof, Proof, prove, verify};
use leanvm_univariate::prover::trace::{Trace, placement};
use leanvm_univariate::{Blake2s, Claims, FLOCK_LEANVM_SKIP, FLOCK_MAIN, FLOCK_REC, FLOCK_REC2, FLOCK_REC3};
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

mod vectors;
use vectors::{deployable, name_of as vector_name};

/// The allocator leanVM's own CLI and benches run on (jemalloc, freed pages kept: `bench::Jemalloc`), so that the
/// prover is measured as leanVM's is; on glibc's every large buffer faults its pages in again.
#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

/// Whether `Σ_terms μ eq(p, u) bit_twist(q_u) = κ` on `q_flock` (extension B's bit-slice claim): per point, the
/// GF(2)-linear `ℓ(y) = Σ_i μ_i bit_i(y)` by byte tables, then its multilinear at the point, low half by a table.
fn bit_slice_holds(claim: &leanvm_univariate::claims::Combined<leanvm_flock_gas::field::E>, qflock: &[primitives::field::F64]) -> bool {
    use leanvm_univariate::prover::poly::from_v;
    let mut total = F192::ZERO;
    for (p, point) in claim.points.iter().enumerate() {
        let mu: Vec<(usize, F192)> = claim
            .terms
            .iter()
            .filter(|t| t.1 == p)
            .map(|&(column, _, twist, c)| {
                assert_eq!(column, leanvm_univariate::claims::Column::QflockBits);
                (twist as usize, from_v(c))
            })
            .collect();
        if mu.is_empty() {
            continue;
        }
        let tables: Vec<[F192; 256]> = (0..8)
            .map(|byte| {
                std::array::from_fn(|v| {
                    mu.iter()
                        .filter(|(i, _)| i / 8 == byte && v >> (i % 8) & 1 == 1)
                        .fold(F192::ZERO, |acc, &(_, c)| acc + c)
                })
            })
            .collect();
        let point: Vec<F192> = point.iter().map(|&x| from_v(x)).collect();
        assert_eq!(1usize << point.len(), qflock.len(), "a point on q_flock's words");
        let low = point.len() / 2;
        let eq_low = primitives::multilinear::eq_table(&point[..low]);
        let eq_high = primitives::multilinear::eq_table(&point[low..]);
        total += parallel::map_reduce(
            eq_high.len(),
            || F192::ZERO,
            |h| {
                let words = &qflock[h << low..(h + 1) << low];
                let inner = words.iter().zip(&eq_low).fold(F192::ZERO, |acc, (w, &e)| {
                    let l = (0..8).fold(F192::ZERO, |s, b| s + tables[b][(w.0 >> (8 * b)) as usize & 0xff]);
                    acc + e * l
                });
                eq_high[h] * inner
            },
            |a, b| a + b,
        );
    }
    total == from_v(claim.value)
}

/// The setup roots of the trace's contract: its program's and shape's `F`, the R1CS's `A0`, `B0`. At the reference
/// shape (1,000 signatures) they are `SetupRoots::REFERENCE`, the gas reports' (checked).
fn contract_roots(trace: &Trace) -> SetupRoots {
    let roots = leanvm_univariate::prover::setup::shape_roots(&trace.shape(), &leanvm_univariate::prover::columns::setup_polys(trace));
    let shape = trace.shape();
    if shape.log_memory == 21 && shape.log_bytecode == 19 && shape.heights() == [18, 18, 18, 18, 17, 18] {
        assert_eq!(roots, SetupRoots::REFERENCE, "the reference shape's roots are the code's");
    }
    roots
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

/// `PCS_OPEN`'s root word (`crates/evm/src/machine.rs`: `s_0 · 2^128 + s_1`) of the root a WHIR opening is of, read
/// off the opening itself: its first two scalars, each 128 bits.
fn whir_word(opening_stream: &[F192]) -> [u8; 32] {
    let mut word = [0u8; 32];
    for (h, s) in opening_stream[..2].iter().enumerate() {
        assert_eq!(s.c2, 0, "a root scalar is 128-bit");
        word[16 * h..16 * h + 8].copy_from_slice(&s.c1.to_be_bytes());
        word[16 * h + 8..16 * h + 16].copy_from_slice(&s.c0.to_be_bytes());
    }
    word
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
    let roots = contract_roots(&trace);
    let config = Config {
        blake2s,
        claims: Claims::Point,
        check: true,
        garbage: false,
        stand_in_roots: None,
        roots,
    };
    let started = std::time::Instant::now();
    let (proof, report) = prove(&trace, flock, &PROGRAM_IV, config).expect("a proof");
    let total = started.elapsed().as_secs_f64();
    println!("  {placing:8.3} s  placement: the rows (and Flock's instances) at the verifier's positions");
    for (phase, secs) in &report.phases {
        println!("  {secs:8.3} s  {phase}");
    }
    for note in &report.notes {
        println!("  note: {note}");
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
    // The openings' fingerprint (their Debug form: the WHIR streams and Merkle paths), for prover changes that must
    // keep the proof byte for byte.
    println!(
        "  openings keccak {}",
        leanvm_univariate::prover::setup::hex(&leanvm_flock_gas::transcript::keccak256(
            format!("{:?}", proof.openings.iter().map(|o| (&o.root, &o.proof)).collect::<Vec<_>>()).as_bytes()
        ))
    );
    assert!(report.checks.iter().all(|(_, ok)| *ok));
    let shape = trace.shape();
    let public = trace.public_input();
    let started = std::time::Instant::now();
    let unproven = verify(&shape, &PROGRAM_IV, &roots, &public, &proof, blake2s).expect("the verifier accepts");
    println!(
        "  verified (reduce + 3 WHIR openings) in {:.3} s; the contract binds F {}",
        started.elapsed().as_secs_f64(),
        leanvm_univariate::prover::setup::hex(&roots.f)
    );
    // Extension B: C1's call also claims Σ_i μ_i ẑ(i, p) = κ of q_flock, which PCS_OPEN would ring-switch; WHIR
    // cannot open it, so it is checked here on the committed q_flock.
    let ext_b = unproven.is_some();
    if let Some(claim) = &unproven {
        assert!(bit_slice_holds(claim, &trace.qflock), "the bit-slice claim holds on q_flock");
        println!("  extension B: the bit-slice claim on C1 holds on the committed q_flock (PCS_OPEN's to prove)");
    }

    // The roots the openings are of, from the prover's output: each WHIR opening's first two scalars are its
    // commitment's root's (`hash_to_scalars`), and the stream carries C1's and C2's as those scalars, so that the
    // stream's 32 bytes are the root's `PCS_OPEN` word (machine.rs: `s_0 · 2^128 + s_1`; REVIEW-REC.md R1).
    let order: Vec<Commitment> = proof.openings.iter().map(|o| o.commitment).collect();
    assert_eq!(order, [Commitment::C1, Commitment::C2, Commitment::Setup], "the calls' order");
    let mut whir_roots: Vec<[u8; 32]> = Vec::new();
    for o in &proof.openings {
        let scalars = fiat_shamir::merkle::hash_to_scalars(&o.root);
        assert_eq!(o.proof.stream[..2], scalars, "{:?}: the WHIR opening's first two scalars are its root's", o.commitment);
        if o.commitment == Commitment::C1 {
            // After the six row counts.
            assert_eq!(proof.stream[24..56], whir_word(&o.proof.stream), "C1's root word in the stream");
        }
        whir_roots.push(o.root);
    }
    if report.flock.is_some() {
        whir_roots.extend([roots.a0, roots.b0]);
    }

    // The contract on the real calldata: its PCS_OPEN mock attests exactly the claims the openings prove (C1's and
    // C2's root words their WHIR openings' first two scalars, the setup's root the contract's constant, the hash as it
    // is; the layout words the contract's) and Flock's A0, B0 claims, which are the matrices' values.
    let words = layout_words(&shape);
    let mut inputs: Vec<Vec<u8>> = Vec::new();
    for o in &proof.openings {
        let root = match o.commitment {
            Commitment::Setup => roots.f,
            _ => whir_word(&o.proof.stream),
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
    let data = calldata(&public, &proof.stream);
    let stream = proof.stream.clone();
    let opened = whir_roots.clone();
    let (accepted, rejected, gas, linked, calls) = deep(move || {
        let recorded = record_verifier_with(&shape, blake2s, Claims::Point, &roots);
        assert_eq!(recorded.stream_len, stream.len(), "the contract's stream is the proof's");
        // The measuring build, word for word against the Rust verifier, on this accepting stream.
        leanvm_univariate::contract::parity_with(&shape, &PROGRAM_IV, &roots, &public, &stream, blake2s, Claims::Point);
        let contract = compile_verifier(&recorded, &PROGRAM_IV, false);
        // The calls the contract makes are the claims the openings prove; with extension B, C1's also carries the
        // bit-slice claim (its claim count 2, its words after the point claim's).
        let calls = call(&contract.code, &[], &data, &PcsOpen::attesting_all(0)).pcs_calls;
        assert_eq!(calls.len(), inputs.len(), "one call per claim the openings prove");
        for (k, (made, proven)) in calls.iter().zip(&inputs).enumerate() {
            if ext_b && k == 0 {
                assert_eq!(made[..64], proven[..64], "C1's root and layout");
                assert_eq!(made[64..96], number(2), "C1's two claims");
                assert_eq!(made[96..proven.len()], proven[96..], "C1's point claim");
            } else {
                assert_eq!(made, proven, "call {k}: the opening's claim");
            }
        }
        // C1's and C2's calls, read as a decoding PCS_OPEN reads them (machine.rs: the root word, then the root it
        // names), are of the roots the prover committed. The setup's constants are the hashes as they are (π1's own
        // contract; π2 passes their root words, REVIEW-REC.md R1).
        for (k, (made, root)) in calls.iter().zip(&opened).enumerate().take(2) {
            let word: [u8; 32] = made[..32].try_into().expect("a root word");
            assert_eq!(&root_of_word(&word), root, "call {k}: PCS_OPEN reads the root the opening is of");
        }
        let attesting = |skip: Option<usize>| {
            let mut pcs = PcsOpen::default();
            for (k, input) in calls.iter().enumerate() {
                if Some(k) != skip {
                    pcs.register(input.clone());
                }
            }
            pcs
        };
        let blocks: Vec<PcsOpen> = std::iter::once(attesting(None)).chain((0..calls.len()).map(|k| attesting(Some(k)))).collect();
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
        let deployed = deployable(&recorded);
        let linked = |data: &[u8], block: &PcsOpen| deployed.chain.call(deployed.address, data, block);
        let linked_run = linked(&data, &blocks[0]);
        let linked_ok = linked_run.output.as_deref() == Some(&one[..])
            && linked(&bad, &blocks[0]).output.is_none()
            && blocks[1..].iter().all(|b| linked(&data, b).output.is_none());
        let deployed_gas = linked_run.execution;
        (ok.output.clone(), rejected, ok.execution, (deployed.contracts.len(), linked_ok, deployed_gas), calls)
    });
    println!(
        "  the contract returns {:?} on the real proof, {gas} gas of execution; parity with the Rust verifier; the \
         deployable build ({} contracts) accepts it: {}, {} gas of execution",
        accepted.as_ref().map(|o| o[31]),
        linked.0,
        linked.1,
        linked.2
    );
    assert_eq!(accepted.as_deref(), Some(&word([1, 0, 0])[..]), "the contract accepts the real proof");
    // The Rust→EVM test vector (tests/vectors/): the calldata, the calls PCS_OPEN attests, the verdict and the gas.
    if let Ok(out) = std::env::var("WRITE_VECTORS") {
        let name = vector_name(blake2s);
        let text = vectors::write(&vectors::Vector {
            config: name.to_string(),
            shape,
            public,
            calldata: calldata(&public, &proof.stream),
            calls: calls.clone(),
            whir_roots,
            accepts: true,
            gas_straight: gas,
            gas_deployed: linked.2,
            contracts: linked.0,
        });
        let path = std::path::Path::new(&out).join(format!("{name}.txt"));
        std::fs::write(&path, text).expect("the vector file");
        println!("  test vector written to {}", path.display());
    }
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
        let verdict = verify(&trace.shape(), &PROGRAM_IV, &roots, &public, &copy(&proof, bad), blake2s);
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

/// π1-rec (`crates/leanvm_rec/SPEC-REC.md` §1.4): the main line with the bus's `α` and Flock's zerocheck eq point
/// derived as squares of one challenge each (`FLOCK_REC`, `FsShape::Rec`). The same stream layout and claims.
#[test]
#[ignore]
fn proves_and_verifies_main_line_rec() {
    end_to_end(Blake2s::Flock(FLOCK_REC));
}

/// π1-rec2 (`crates/leanvm_rec/SPEC-REC.md` §12): π1-rec with Flock's lincheck terminal checked by the circuit's walk
/// (`FLOCK_REC2`, `Slices::TowerWalk`): no matrices' reduction, three claims (`C1`, `C2`, `F`).
#[test]
#[ignore]
fn proves_and_verifies_main_line_rec2() {
    end_to_end(Blake2s::Flock(FLOCK_REC2));
}

/// π1-rec3 (`crates/leanvm_rec/SPEC-REC.md` §12, `SPEC-POINTS.md`): π1-rec2 with the batching sumcheck two variables a
/// round, 14 narrow challenges for the claims' 27 coordinates (`FLOCK_REC3`, `FsShape::Rec3`).
#[test]
#[ignore]
fn proves_and_verifies_main_line_rec3() {
    end_to_end(Blake2s::Flock(FLOCK_REC3));
}

/// Extension B: Flock (a), its skip of 4, the slices not sent, the matrices' reduction in the batch whose terminal
/// is a bit-slice claim of C1's call (`FLOCK_BIT_SLICE`). WHIR proves the point claims; the bit-slice claim, which
/// `PCS_OPEN` would ring-switch, is checked on `q_flock` directly.
#[test]
#[ignore]
fn proves_and_verifies_ext_b() {
    end_to_end(Blake2s::Flock(leanvm_univariate::FLOCK_BIT_SLICE));
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
        roots: contract_roots(&trace),
    };
    let (proof, report) = prove(&trace, None, &PROGRAM_IV, config).expect("a proof");
    for (c, placed, vars) in &report.stacks {
        println!("  stack {c:?}: words {placed}.. up to its last lane pseudo-random (2^{vars})");
    }
    assert!(report.checks.iter().all(|(_, ok)| *ok));
    // F's unused words hold garbage too: the contract that accepts is the one built for that F.
    let roots = report.roots.expect("the proof's roots");
    verify(&trace.shape(), &PROGRAM_IV, &roots, &trace.public_input(), &proof, Blake2s::Omitted).expect("accepted");
    println!("  accepted");
}
