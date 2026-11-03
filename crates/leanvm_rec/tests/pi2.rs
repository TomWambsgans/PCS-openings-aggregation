// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π2's PIOP (`src/pi2`, `PI2.md`), end to end on synthetic circuits built with the interface, D16v and D32v:
//!
//! - `small_*`: the honest proof's four claims hold and its three openings verify (`quotient::opening::verify`, what
//!   `PCS_OPEN` checks); a witness that breaks one copy, one formula or one public element leaves a false claim; a
//!   flipped byte of the stream gives claims the openings do not prove;
//! - `the_interface_example`: the circuit compiler's own example (`circuit::spec::example`), padded, through the
//!   adapter;
//! - `contract_*`: the verifier compiled to EVM is the Rust verifier word for word, straight and deployable, and
//!   accepts the honest proof with `PCS_OPEN` attesting its claims, and rejects a flipped byte;
//! - `gas_report` (ignored): the contract at the target shapes, D16v (`N = 2^24`) and D32v (`N = 2^23`);
//! - `prove_target` (ignored): the prover at a target shape.
//!
//! `cargo test --release -p leanvm_rec --test pi2 -- --nocapture` (and `--ignored gas_report`).

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

use leanvm_flock_gas::evm::machine::element_word;
use leanvm_rec::circuit::spec::{self, CallWord};
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::circuit::{Circuit, NONE};
use leanvm_rec::pi2::contract::{self, Instance, calldata, number, record_verifier, sample_stream};
use leanvm_rec::pi2::prover::{
    self, PublicValue, Setup, claims_hold, open, prove, prove_with, public_scalars, verify_openings,
};
use leanvm_rec::pi2::synth::{self, Built, Design};
use leanvm_rec::pi2::verifier::{Spec, to_f192};
use primitives::field::{F64, F192};

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

const PI1_IV: [u8; 32] = [0x11; 32];

struct Fixture {
    circuit: Circuit,
    witness: Vec<F64>,
    public_input: [u8; 32],
    values: Vec<PublicValue>,
    spec: Spec,
    setup: Setup,
    iv: [u8; 32],
}

fn fixture(circuit: Circuit, witness: Vec<F64>, public_input: [u8; 32], values: Vec<PublicValue>) -> Fixture {
    let public = public_scalars(&public_input, &values);
    circuit
        .check(&witness, &public, F192::new(0x1234, 0x5678, 0x9abc))
        .expect("the witness satisfies the circuit");
    let spec = Spec::of(&circuit);
    let setup = Setup::new(&circuit);
    let iv = prover::iv(&PI1_IV, &circuit.digest(), &setup.root(), circuit.log_n);
    Fixture {
        circuit,
        witness,
        public_input,
        values,
        spec,
        setup,
        iv,
    }
}

fn built(design: &Design) -> Fixture {
    let Built {
        circuit,
        witness,
        public_input,
        values,
        ..
    } = synth::build(design, 0x5eed);
    fixture(circuit, witness, public_input, values)
}

/// Positions whose value nothing constrains: pull-less ones, and spare self-loops no formula reads.
fn unconstrained(circuit: &Circuit) -> Vec<bool> {
    let pair_of = circuit.pair_of();
    let pulls = circuit.pulls();
    let width = circuit.width();
    let mut read = vec![false; circuit.n()];
    for (i, &p) in pair_of.iter().enumerate() {
        if p != NONE {
            let row = i & !(width - 1);
            for c in circuit.formulas[circuit.pairs[p as usize].formula].cells() {
                read[row + c] = true;
            }
        }
    }
    (0..circuit.n())
        .map(|i| !pulls[i] || (pair_of[i] == NONE && circuit.sigma[i] as usize == i && !read[i]))
        .collect()
}

fn honest_and_mutated(f: &Fixture, mutations: usize) {
    let proved = prove(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &f.values,
        &f.witness,
    );
    assert_eq!(
        claims_hold(&proved, &f.setup),
        [true; 4],
        "the honest proof's claims hold"
    );
    let stream = proved.stream.clone();
    println!(
        "2^{} positions, rows of {}: {} pairs, {} groups, {} public terms; stream {} B; prover {:?}",
        f.circuit.log_n,
        f.circuit.width(),
        f.circuit.pairs.len(),
        f.spec.groups.len(),
        f.circuit.public.len(),
        stream.len(),
        proved.timings
    );
    let (reduced, roots, openings) = open(proved, &f.setup);
    assert_eq!(
        verify_openings(f.circuit.log_n, &reduced, &roots, &f.setup.root(), &openings),
        Ok(())
    );

    // A flipped byte of the stream: the claims are not the ones the openings prove.
    for at in [0, stream.len() / 2, stream.len() - 1] {
        let mut bad = stream.clone();
        bad[at] ^= 0x20;
        let other = leanvm_rec::pi2::verifier::verify(&f.spec, &f.iv, &f.public_input, &bad).expect("the length");
        assert!(
            verify_openings(f.circuit.log_n, &other, &roots, &f.setup.root(), &openings).is_err(),
            "byte {at} flipped"
        );
    }

    // Witnesses that break one push: some claim is false.
    let free = unconstrained(&f.circuit);
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut tried = 0;
    while tried < mutations {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let i = (state % f.circuit.n() as u64) as usize;
        if free[i] {
            continue;
        }
        tried += 1;
        let mut bad = f.witness.clone();
        bad[i] += F64(1 + (state >> 40));
        let proved = prove_with(
            &f.circuit,
            &f.spec,
            &f.setup,
            &f.iv,
            &f.public_input,
            &f.values,
            &bad,
            false,
        );
        let holds = claims_hold(&proved, &f.setup);
        assert!(holds.contains(&false), "position {i} changed: {holds:?}");
    }
    // A public element changed.
    let mut values = f.values.clone();
    let k = values
        .iter()
        .position(|v| matches!(v, PublicValue::Scalar(_)))
        .expect("an element");
    if let PublicValue::Scalar(x) = &mut values[k] {
        *x += F192::new(0, 1, 0);
    }
    let proved = prove_with(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &values,
        &f.witness,
        false,
    );
    assert!(
        claims_hold(&proved, &f.setup).contains(&false),
        "a public element changed"
    );
    let mut public_input = f.public_input;
    public_input[3] ^= 4;
    let proved = prove_with(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &public_input,
        &f.values,
        &f.witness,
        false,
    );
    assert!(
        claims_hold(&proved, &f.setup).contains(&false),
        "the public input changed"
    );
}

#[test]
fn small_d16v() {
    honest_and_mutated(&built(&synth::small_d16v(11)), 24);
}

#[test]
fn small_d32v() {
    honest_and_mutated(&built(&synth::small_d32v(12)), 24);
}

/// The circuit compiler's example (`N = 32`), on `2^log_n` positions: the rows past it in no block (forwards, self-loops
/// of 0), the ports' tags moved past the new `N`.
fn padded_example(log_n: u8) -> (spec::Circuit, spec::Witness, spec::PublicInputs) {
    let (mut c, mut w, public) = spec::example();
    let (old, n) = (c.n(), 1usize << log_n);
    c.sigma = c
        .sigma
        .iter()
        .map(|&s| {
            if (s as usize) < old {
                s
            } else {
                s - old as u32 + n as u32
            }
        })
        .chain(old as u32..n as u32)
        .collect();
    c.log_n = log_n;
    w.resize(n, leanvm_flock_gas::field::K(0));
    (c, w, public)
}

#[test]
fn the_interface_example() {
    let (c, w, public) = padded_example(11);
    assert_eq!(c.check(&w, &public), Ok(()));
    let circuit = adapt::adapt(&c);
    let (public_input, values) = adapt::public_values(&public);
    let f = fixture(circuit, adapt::witness(&w), public_input, values);
    let proved = prove(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &f.values,
        &f.witness,
    );
    assert_eq!(claims_hold(&proved, &f.setup), [true; 4]);
    let (reduced, roots, openings) = open(proved, &f.setup);
    assert_eq!(
        verify_openings(f.circuit.log_n, &reduced, &roots, &f.setup.root(), &openings),
        Ok(())
    );
    // The value the port binds, changed: a false claim.
    let mut other = public.clone();
    other.elements[0] = leanvm_flock_gas::field::E::new(1, 0, 0);
    let (_, values) = adapt::public_values(&other);
    let proved = prove_with(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &values,
        &f.witness,
        false,
    );
    assert!(claims_hold(&proved, &f.setup).contains(&false));
}

/// π1's calls for a small circuit: five calls of the real ones' kinds (constants, the two roots, elements).
fn small_pi1() -> Vec<Vec<CallWord>> {
    let c = |b: u8| CallWord::Const([b; 32]);
    let n = |k: u64| CallWord::Const(number(k));
    vec![
        vec![
            CallWord::Root(0),
            c(1),
            n(1),
            CallWord::Element(0),
            CallWord::Element(1),
            CallWord::Element(2),
        ],
        vec![
            CallWord::Root(1),
            c(2),
            n(1),
            CallWord::Element(0),
            CallWord::Element(1),
            CallWord::Element(1),
        ],
        vec![c(9), c(3), n(1), CallWord::Element(0), CallWord::Element(2)],
        vec![c(8), c(4), n(1), CallWord::Element(2), c(0), CallWord::Element(1)],
        vec![c(7), c(5), n(1), CallWord::Element(2), c(0), CallWord::Element(0)],
    ]
}

fn contract_checks(design: Design) {
    deep(move || {
        let f = built(&design);
        let pi1 = small_pi1();
        let inst = Instance {
            spec: &f.spec,
            iv: f.iv,
            setup_root: f.setup.root(),
            pi1: &pi1,
        };
        let recorded = record_verifier(&f.spec);
        let proved = prove(
            &f.circuit,
            &f.spec,
            &f.setup,
            &f.iv,
            &f.public_input,
            &f.values,
            &f.witness,
        );
        let stream = proved.stream.clone();
        assert_eq!(stream.len(), recorded.stream_len);
        // Word for word, on the honest stream and on a random one.
        let words = contract::parity(&inst, &recorded, &f.public_input, &stream);
        contract::parity(&inst, &recorded, &[0x5a; 32], &sample_stream(stream.len(), 7));
        let parts = contract::parity_deployable(&inst, &recorded, &f.public_input, &stream);
        println!("parity: {words} words, deployable in {parts} contract(s)");

        // The honest proof: the contract calls PCS_OPEN with π1's calls and the claims the openings prove.
        let (reduced, roots, openings) = open(proved, &f.setup);
        assert_eq!(
            verify_openings(f.circuit.log_n, &reduced, &roots, &f.setup.root(), &openings),
            Ok(())
        );
        let expected: Vec<Vec<u8>> = contract::expected_calls(&inst, &recorded, &reduced, &stream)
            .into_iter()
            .map(|words| words.concat())
            .collect();
        let data = calldata(&f.public_input, &stream);
        let (accepted, calls) = contract::run(&inst, &recorded, &data, &expected);
        assert!(accepted, "the contract accepts the honest proof");
        assert_eq!(calls, expected);
        // π2's calls are the claims `opening::verify` accepted: their words, read back.
        let pi2 = &calls[pi1.len()..];
        let word = |input: &[u8], k: usize| -> [u8; 32] { input[32 * k..32 * k + 32].try_into().unwrap() };
        assert_eq!(word(&pi2[0], 3), element_word(reduced.witness.0[0]));
        assert_eq!(word(&pi2[1], 2), number(2), "Q's two claims in one call");
        let _ = to_f192;
        for at in [36, data.len() / 2, data.len() - 1] {
            let mut bad = data.clone();
            bad[at] ^= 1;
            assert!(
                !contract::run(&inst, &recorded, &bad, &expected).0,
                "calldata byte {at} flipped"
            );
        }
    });
}

#[test]
fn contract_d16v() {
    contract_checks(synth::small_d16v(11));
}

#[test]
fn contract_d32v() {
    contract_checks(synth::small_d32v(12));
}

/// The contract at a target shape: built from the synthetic circuit's verifier (its gas depends on the shape alone:
/// the pairs, the formulas, the public side), π1-rec's real calls appended.
fn target_report(name: &str, design: Design) {
    let name = name.to_string();
    deep(move || {
        let built = synth::build(&design, 0x7a);
        let circuit = &built.circuit;
        let spec = Spec::of(circuit);
        let pi1 = leanvm_rec::pi2::pi1::pi1_calls();
        println!(
            "{name}: 2^{} positions ({:.1}% of the rows used), rows of {}: {} pairs ({} pull-less), {} groups, {} formulas, blocks up to 2^{} rows, {} public terms, {} reads; π1: {} calls, {} roots, {} elements",
            circuit.log_n,
            100.0 * built.used_rows as f64 / circuit.rows() as f64,
            circuit.width(),
            circuit.pairs.len(),
            spec.pull_less.len(),
            spec.groups.len(),
            circuit.formulas.len(),
            spec.max_log_rows(),
            circuit.public.len(),
            circuit.reads.len(),
            pi1.calls.len(),
            pi1.roots,
            pi1.elements
        );
        assert!(
            pi1.roots <= 2 && pi1.elements <= 51,
            "the synthetic circuit's public data hold π1's"
        );
        let inst = Instance {
            spec: &spec,
            iv: [0x33; 32],
            setup_root: [0x44; 32],
            pi1: &pi1.calls,
        };
        let recorded = record_verifier(&spec);
        let report = contract::measure(&inst, &recorded, true);
        print!("{}", report.table(&name));
        let stream = sample_stream(recorded.stream_len, 11);
        contract::parity(&inst, &recorded, &[0x5a; 32], &stream);
        let parts = contract::parity_deployable(&inst, &recorded, &[0x5a; 32], &stream);
        println!("{name}: parity straight and deployable ({parts} contracts)");
    });
}

#[test]
#[ignore]
fn gas_report() {
    target_report("D16v, N = 2^24 (pi1-rec)", synth::target_d16v());
    target_report("D32v, N = 2^23 (pi1 main line)", synth::target_d32v());
}

fn peak_memory() -> String {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.to_string()))
        .unwrap_or_default()
}

/// The prover at a target shape: `PI2_TARGET=d16v` (default) or `d32v`, scaled to `2^PI2_LOG_N` positions if set (the
/// same pairs, formulas and public side, smaller blocks).
#[test]
#[ignore]
fn prove_target() {
    let target = match std::env::var("PI2_TARGET").as_deref() {
        Ok("d32v") => synth::target_d32v(),
        _ => synth::target_d16v(),
    };
    let design = match std::env::var("PI2_LOG_N").ok().and_then(|v| v.parse().ok()) {
        Some(log_n) => synth::scaled(&target, log_n),
        None => target,
    };
    let start = std::time::Instant::now();
    let f = built(&design);
    println!(
        "2^{} positions, {} pairs, {} groups: built, checked, setup committed in {:.1} s; {}",
        f.circuit.log_n,
        f.circuit.pairs.len(),
        f.spec.groups.len(),
        start.elapsed().as_secs_f64(),
        peak_memory()
    );
    let start = std::time::Instant::now();
    let proved = prove(
        &f.circuit,
        &f.spec,
        &f.setup,
        &f.iv,
        &f.public_input,
        &f.values,
        &f.witness,
    );
    let proving = start.elapsed().as_secs_f64();
    for (step, s) in &proved.timings {
        println!("   {s:>7.2} s  {step}");
    }
    let start = std::time::Instant::now();
    let (reduced, roots, openings) = open(proved, &f.setup);
    let opening = start.elapsed().as_secs_f64();
    println!("prove {proving:.1} s, open {opening:.1} s; {}", peak_memory());
    assert_eq!(
        verify_openings(f.circuit.log_n, &reduced, &roots, &f.setup.root(), &openings),
        Ok(())
    );
}
