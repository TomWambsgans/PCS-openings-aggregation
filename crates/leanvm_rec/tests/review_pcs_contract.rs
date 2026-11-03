// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Review (REVIEW-REC.md): π2's contract and Rust verifier against each other, and against the openings, on every
//! calldata region, on the synthetic circuits of `tests/pi2.rs` (D16v and D32v):
//!
//! - a flipped byte in each region (the public input, π1's roots, its elements, the other public reads, `W`'s and
//!   `Q`'s roots, every value sent): the contract's checked values and `PCS_OPEN` words are the Rust verifier's (the
//!   parity build), the **verifying** build calls `PCS_OPEN` with exactly the Rust verifier's inputs (attest-all
//!   mock), and the honest openings do not prove π2's claims on the mutated stream;
//! - each value sent flipped: which claims become false on the honest tables;
//! - the calldata one byte longer or shorter, another selector: the verifying build reverts even with every call
//!   attested, and the Rust verifier rejects.
//!
//! `cargo test --release -p leanvm_rec --test review_pcs_contract -- --nocapture --test-threads 1`

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

use leanvm_flock_gas::evm::codegen::word;
use leanvm_flock_gas::evm::machine::{PcsOpen, call};
use leanvm_flock_gas::field::E;
use leanvm_rec::circuit::spec::CallWord;
use leanvm_rec::pi2::circuit::Read;
use leanvm_rec::pi2::contract::{self, Instance, calldata, compile_verifier, number, record_verifier};
use leanvm_rec::pi2::prover::{self, Proved, Setup, prove, verify_openings};
use leanvm_rec::pi2::synth::{self, Built, Design};
use leanvm_rec::pi2::verifier::{self, Reduced, Spec, claim};
use quotient::opening::Table;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// π1's calls for a small circuit (as tests/pi2.rs): constants, the two roots, elements.
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

/// Each claim on the tables, by evaluation: `W`, `Q`'s identity, `Q`'s sum, the setup.
fn holds(witness: &Table, quotient: &Table, setup: &Setup, r: &Reduced<E>) -> [bool; 4] {
    let h = |t: &Table, c: &(Vec<E>, E)| {
        let c = claim(c);
        t.eval(&c.point) == c.value
    };
    [
        h(witness, &r.witness),
        h(quotient, &r.quotient),
        h(quotient, &r.sum),
        h(&setup.table, &r.setup),
    ]
}

/// A `PCS_OPEN` input of π2's, decoded: the root (the word is `contract::root_word`: each 16-byte half of the hash
/// reversed), the layout its id names among `known`, and the claims (a word's low 192 bits; its top 64 must be zero).
fn decode<'a>(
    input: &[u8],
    known: &[&'a quotient::opening::Layout],
) -> (fiat_shamir::merkle::Hash, &'a quotient::opening::Layout, Vec<quotient::opening::Claim>) {
    let word = |k: usize| -> [u8; 32] { input[32 * k..32 * k + 32].try_into().unwrap() };
    let mut hash = word(0);
    hash[..16].reverse();
    hash[16..].reverse();
    assert_eq!(contract::root_word(&hash), word(0));
    let layout = *known
        .iter()
        .find(|l| quotient::opening::layout_id(l) == word(1))
        .expect("a layout PCS_OPEN knows");
    let k = u64::from_be_bytes(word(2)[24..].try_into().unwrap()) as usize;
    assert!(word(2)[..24].iter().all(|&b| b == 0));
    assert_eq!(input.len(), 32 * (3 + k * (layout.vars + 1)), "the input's length");
    let element = |w: [u8; 32]| {
        assert!(w[..8].iter().all(|&b| b == 0), "an element word's top 64 bits");
        let limb = |i: usize| u64::from_be_bytes(w[24 - 8 * i..32 - 8 * i].try_into().unwrap());
        primitives::field::F192::new(limb(0), limb(1), limb(2))
    };
    let claims = (0..k)
        .map(|c| {
            let at = 3 + c * (layout.vars + 1);
            quotient::opening::Claim {
                point: (0..layout.vars).map(|j| element(word(at + j))).collect(),
                value: element(word(at + layout.vars)),
            }
        })
        .collect();
    (hash, layout, claims)
}

/// Named byte ranges of the stream: the public reads, the roots, the values.
fn regions(spec: &Spec) -> Vec<(String, usize, usize)> {
    let mut out = vec![];
    let mut at = 0;
    let (mut roots, mut scalars, mut ints) = (0, 0, 0);
    for r in &spec.reads {
        let (name, len) = match r {
            Read::Root => {
                roots += 1;
                (format!("public root {}", roots - 1), 32)
            }
            Read::Scalar => {
                scalars += 1;
                (format!("public element {}", scalars - 1), 24)
            }
            Read::Integer(b) => {
                ints += 1;
                (format!("public integer {}", ints - 1), *b as usize)
            }
        };
        out.push((name, at, len));
        at += len;
    }
    out.push(("W root".into(), at, 32));
    at += 32;
    out.push(("Q root".into(), at, 32));
    at += 32;
    for k in 0..spec.values() {
        let name = match k {
            k if k < (1 << spec.log_row) => format!("a_{k}"),
            k if k == (1 << spec.log_row) => "σ(t)".into(),
            k if k == (1 << spec.log_row) + 1 => "κ(t)".into(),
            _ => "h(t)".into(),
        };
        out.push((name, at, 24));
        at += 24;
    }
    out
}

fn check(design: Design) {
    deep(move || {
        let Built {
            circuit,
            witness,
            public_input,
            values,
            ..
        } = synth::build(&design, 0x5eed);
        let spec = Spec::of(&circuit);
        let setup = Setup::new(&circuit);
        let iv = prover::iv(&[0x11; 32], &circuit.digest(), &setup.root(), circuit.log_n);
        let pi1 = small_pi1();
        let inst = Instance {
            spec: &spec,
            iv,
            setup_root: setup.root(),
            pi1: &pi1,
        };
        let recorded = record_verifier(&spec);
        let proved: Proved = prove(&circuit, &spec, &setup, &iv, &public_input, &values, &witness);
        let stream = proved.stream.clone();
        assert_eq!(stream.len(), recorded.stream_len);
        let regions = regions(&spec);
        let (_, last, len) = regions.last().unwrap().clone();
        assert_eq!(last + len, stream.len(), "the regions cover the stream");
        let verifying = compile_verifier(&inst, &recorded, false);

        // The honest tables, kept for evaluating claims on mutated streams.
        let Proved {
            witness: (wt, wc),
            quotient: (qt, qc),
            reduced,
            ..
        } = proved;
        assert_eq!(holds(&wt, &qt, &setup, &reduced), [true; 4]);
        let roots = [wc.root, qc.root];
        let openings = prover::Openings {
            witness: quotient::opening::open(&wt, &wc, &[claim(&reduced.witness)]),
            quotient: quotient::opening::open(&qt, &qc, &[claim(&reduced.quotient), claim(&reduced.sum)]),
            setup: quotient::opening::open(&setup.table, &setup.committed, &[claim(&reduced.setup)]),
        };
        assert_eq!(
            verify_openings(circuit.log_n, &reduced, &roots, &setup.root(), &openings),
            Ok(())
        );

        // Every region: first, middle and last byte flipped.
        let mut flips: Vec<(String, usize)> = vec![];
        for (name, at, len) in &regions {
            for k in [0, len / 2, len - 1] {
                flips.push((name.clone(), at + k));
            }
        }
        let mut tried = 0;
        for (name, at) in &flips {
            let mut bad = stream.clone();
            bad[*at] ^= 0x41;
            // (a) word for word: the parity build's checked values and PCS_OPEN words, the Rust verifier's.
            contract::parity(&inst, &recorded, &public_input, &bad);
            // (b) the verifying build, every call attested: it calls PCS_OPEN with exactly the Rust verifier's inputs.
            let (rust, _, _) = contract::rust_verifier(&inst, &public_input, &bad).expect("the length");
            let expected: Vec<Vec<u8>> = contract::expected_calls(&inst, &recorded, &rust, &bad)
                .into_iter()
                .map(|w| w.concat())
                .collect();
            let outcome = call(
                &verifying.code,
                &[],
                &calldata(&public_input, &bad),
                &PcsOpen::attesting_all(0),
            );
            assert_eq!(outcome.output.as_deref(), Some(&word([1, 0, 0])[..]), "{name} @ {at}");
            assert_eq!(outcome.pcs_calls, expected, "{name} @ {at}: the verifying build's calls");
            // (c) the honest openings do not prove π2's claims on the mutated stream.
            assert!(
                verify_openings(circuit.log_n, &rust, &roots, &setup.root(), &openings).is_err(),
                "{name} @ {at}: the honest openings prove the mutated claims"
            );
            let h = holds(&wt, &qt, &setup, &rust);
            if name.starts_with('a') || name.contains("(t)") {
                println!("   {name} flipped (byte {at}): claims W / Q / Σ / setup hold: {h:?}");
            }
            assert!(h.contains(&false), "{name} @ {at}: every claim holds");
            tried += 1;
        }
        // The public input.
        for k in [0usize, 13, 31] {
            let mut pi = public_input;
            pi[k] ^= 0x41;
            contract::parity(&inst, &recorded, &pi, &stream);
            let (rust, _, _) = contract::rust_verifier(&inst, &pi, &stream).expect("the length");
            assert!(verify_openings(circuit.log_n, &rust, &roots, &setup.root(), &openings).is_err());
            tried += 1;
        }
        // Lengths and selector: the verifying build reverts with every call attested; the Rust verifier rejects.
        let mut longer = calldata(&public_input, &stream);
        longer.push(0);
        let shorter = calldata(&public_input, &stream[..stream.len() - 1]);
        let mut selector = calldata(&public_input, &stream);
        selector[0] ^= 1;
        for (name, data) in [("one byte longer", &longer), ("one byte shorter", &shorter), ("selector", &selector)] {
            let outcome = call(&verifying.code, &[], data, &PcsOpen::attesting_all(0));
            assert!(outcome.output.is_none(), "{name}: the contract does not revert");
            assert!(outcome.pcs_calls.is_empty(), "{name}: PCS_OPEN was called");
        }
        assert!(verifier::verify(&spec, &iv, &public_input, &[&stream[..], &[0]].concat()).is_err());
        assert!(verifier::verify(&spec, &iv, &public_input, &stream[..stream.len() - 1]).is_err());
        // The honest calldata: accepted with every call attested.
        let outcome = call(
            &verifying.code,
            &[],
            &calldata(&public_input, &stream),
            &PcsOpen::attesting_all(0),
        );
        assert_eq!(outcome.output.as_deref(), Some(&word([1, 0, 0])[..]));
        assert_eq!(outcome.pcs_calls.len(), 8);
        // π2's three calls, decoded as a precompile following crates/evm's ABI would (root word = s_0 2^128 + s_1,
        // the layout by its id, k, then k claims of `vars + 1` element words), are what `opening::verify` accepts.
        let l = prover::layouts(circuit.log_n);
        let proofs = [&openings.witness, &openings.quotient, &openings.setup];
        for (input, proof) in outcome.pcs_calls[pi1.len()..].iter().zip(proofs) {
            let (hash, layout, claims) = decode(input, &[&l.witness, &l.quotient, &l.setup]);
            quotient::opening::verify(layout, &hash, &claims, &quotient::opening::wire_proof(proof))
                .expect("a decoded call of π2's is what its opening proves");
        }
        assert_eq!(decode(&outcome.pcs_calls[pi1.len() + 1], &[&l.quotient]).2.len(), 2);
        println!(
            "2^{} positions, rows of {}: {} mutations, each the Rust verifier's word for word (parity and verifying builds) and rejected by the openings; lengths ±1 and the selector revert",
            circuit.log_n,
            circuit.width(),
            tried
        );
    });
}

#[test]
fn review_parity_every_region_d16v() {
    check(synth::small_d16v(11));
}

#[test]
fn review_parity_every_region_d32v() {
    check(synth::small_d32v(12));
}
