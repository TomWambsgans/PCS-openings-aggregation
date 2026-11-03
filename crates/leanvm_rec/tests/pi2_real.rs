// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π2 on the real instance (SPEC-REC.md §7 R3, `PI2.md` §5): the circuit compiled from π1's recorded verifier with the
//! witness of the real 1,000-signature proof (`crates/leanvm_univariate/tests/vectors/main_line_rec.txt`, π1-rec; and
//! `main_line.txt`), through the adapter (`pi2::adapt`):
//!
//! - `real_gas`: the contract's gas on the real circuits, D16v × π1-rec and D32v × π1-rec / π1 (the verifier's gas
//!   depends on the circuit alone), parity with the Rust verifier, straight and deployable;
//! - `real_end_to_end` (`PI2_LAYOUT=d16v|d32v`, `PI2_VECTOR=main_line_rec|main_line`): π2's prover on the real witness,
//!   its three openings verified (`quotient::opening::verify`, what `PCS_OPEN` checks), and the contract accepting the
//!   proof with `PCS_OPEN` attesting exactly its nine calls: π1's five (the vector's inputs, which π1's openings
//!   prove) and π2's three; a flipped calldata byte is rejected.
//!
//! `cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture --test-threads 1`

#![allow(clippy::needless_range_loop)]

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

#[path = "../../leanvm_univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_rec::circuit::compile::{Compiled, Inputs, Layout, pi2};
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::contract::{self, Instance, calldata, record_verifier, sample_stream};
use leanvm_rec::pi2::prover::{self, Setup, claims_hold, open, prove, public_scalars, verify_openings};
use leanvm_rec::pi2::verifier::Spec;
use leanvm_univariate::Claims;
use leanvm_univariate::contract::{SetupRoots, contract_iv};
use primitives::field::F192;

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

/// The real circuit and witness, and π1's contract IV.
fn real(name: &str, layout: Layout) -> (vectors::Vector, Compiled, [u8; 32]) {
    let v = vector(name);
    let recorded = leanvm_univariate::contract::record_verifier(&v.shape, vectors::blake2s_of(&v.config), Claims::Point);
    let iv = contract_iv(&v.shape, &PROGRAM_IV, &SetupRoots::REFERENCE);
    let stream = v.calldata[STREAM_AT..].to_vec();
    let c = pi2(
        &recorded,
        layout,
        &Inputs {
            iv,
            public: v.public,
            stream: &stream,
        },
    );
    (v, c, iv)
}

fn peak_memory() -> String {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.trim().to_string()))
        .unwrap_or_default()
}

fn gas(name: &str, layout: Layout) {
    let (_, c, pi1_iv) = real(name, layout);
    let circuit = adapt::adapt(&c.finished.circuit);
    let spec = Spec::of(&circuit);
    let terms: usize = spec.groups.iter().map(|g| g.formula.lin.terms.len() + 2 * g.formula.products.len()).sum();
    let products: usize = spec.groups.iter().map(|g| g.formula.products.len()).sum();
    println!(
        "{name} × {layout:?}: 2^{} positions, {} pairs ({} pull-less, the holes), {} groups ({} formula terms, {} products), blocks up to 2^{} rows, {} public terms, {} reads; π1: {} calls",
        circuit.log_n,
        circuit.pairs.len(),
        spec.pull_less.len(),
        spec.groups.len(),
        terms,
        products,
        spec.max_log_rows(),
        circuit.public.len(),
        circuit.reads.len(),
        c.finished.circuit.calls.len()
    );
    // The setup root does not change the gas: a placeholder, as the univariate contract's reports.
    let inst = Instance {
        spec: &spec,
        iv: prover::iv(&pi1_iv, &circuit.digest(), &[0x44; 32], circuit.log_n),
        setup_root: [0x44; 32],
        pi1: &c.finished.circuit.calls,
    };
    let recorded = record_verifier(&spec);
    let report = contract::measure(&inst, &recorded, true);
    print!("{}", report.table(&format!("{name} × {layout:?} (real circuit)")));
    let stream = sample_stream(recorded.stream_len, 13);
    contract::parity(&inst, &recorded, &[0x5a; 32], &stream);
    let parts = contract::parity_deployable(&inst, &recorded, &[0x5a; 32], &stream);
    println!("parity: straight and deployable ({parts} contracts)\n");
}

#[test]
#[ignore]
fn real_gas() {
    deep(|| {
        gas("main_line_rec", Layout::D16v);
        gas("main_line_rec", Layout::D32v);
        gas("main_line", Layout::D32v);
    });
}

#[test]
#[ignore]
fn real_end_to_end() {
    deep(|| {
        let layout = match std::env::var("PI2_LAYOUT").as_deref() {
            Ok("d32v") => Layout::D32v,
            _ => Layout::D16v,
        };
        let name = std::env::var("PI2_VECTOR").unwrap_or_else(|_| "main_line_rec".into());
        let start = std::time::Instant::now();
        let (v, c, pi1_iv) = real(&name, layout);
        assert_eq!(c.finished.circuit.check(&c.finished.witness, &c.public), Ok(()));
        assert_eq!(c.finished.circuit.call_inputs(&c.public), v.calls, "π1's calls are the vector's");
        let circuit = adapt::adapt(&c.finished.circuit);
        let witness = adapt::witness(&c.finished.witness);
        let (public_input, values) = adapt::public_values(&c.public);
        drop(c.expanded);
        let calls = c.finished.circuit.calls.clone();
        circuit
            .check(&witness, &public_scalars(&public_input, &values), F192::new(3, 5, 7))
            .expect("the adapted circuit holds");
        let spec = Spec::of(&circuit);
        println!(
            "{name} × {layout:?}: compiled, adapted, checked in {:.1} s; {}",
            start.elapsed().as_secs_f64(),
            peak_memory()
        );
        let start = std::time::Instant::now();
        let setup = Setup::new(&circuit);
        let iv = prover::iv(&pi1_iv, &circuit.digest(), &setup.root(), circuit.log_n);
        println!("setup committed in {:.1} s", start.elapsed().as_secs_f64());

        let start = std::time::Instant::now();
        let proved = prove(&circuit, &spec, &setup, &iv, &public_input, &values, &witness);
        let proving = start.elapsed().as_secs_f64();
        for (step, s) in &proved.timings {
            println!("   {s:>7.2} s  {step}");
        }
        assert_eq!(claims_hold(&proved, &setup), [true; 4], "the claims hold on the tables");
        let stream = proved.stream.clone();
        let start = std::time::Instant::now();
        let (reduced, roots, openings) = open(proved, &setup);
        let opening = start.elapsed().as_secs_f64();
        println!("prove {proving:.1} s, open {opening:.1} s; {}", peak_memory());
        assert_eq!(verify_openings(circuit.log_n, &reduced, &roots, &setup.root(), &openings), Ok(()));

        // The contract: π1's five calls (the vector's inputs) and π2's three, attested exactly.
        let inst = Instance {
            spec: &spec,
            iv,
            setup_root: setup.root(),
            pi1: &calls,
        };
        let recorded = record_verifier(&spec);
        let expected: Vec<Vec<u8>> = contract::expected_calls(&inst, &recorded, &reduced, &stream)
            .into_iter()
            .map(|words| words.concat())
            .collect();
        assert_eq!(&expected[..5], &v.calls[..], "π1's calls, from π2's public data, are the vector's");
        let data = calldata(&public_input, &stream);
        let (accepted, made) = contract::run(&inst, &recorded, &data, &expected);
        assert!(accepted, "the contract accepts π2's proof of π1-rec's real proof");
        assert_eq!(made, expected, "the nine claims in eight calls");
        for at in [4, 40, 40 + 64, data.len() - 30, data.len() - 1] {
            let mut bad = data.clone();
            bad[at] ^= 1;
            assert!(!contract::run(&inst, &recorded, &bad, &expected).0, "calldata byte {at} flipped");
        }
        contract::parity(&inst, &recorded, &public_input, &stream);
        println!(
            "end to end: π1's real proof → π2's proof ({} B of calldata) → the contract accepts, PCS_OPEN attesting its 9 claims",
            data.len()
        );
    });
}
