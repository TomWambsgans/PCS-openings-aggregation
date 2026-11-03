// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The Rust→EVM test vectors (milestone 3), replayed with no prover and no trace: each file of `tests/vectors/` holds
//! a real proof's calldata (1,000 leanXMSS signatures), the `PCS_OPEN` inputs the contract calls with (which the
//! proof's WHIR openings prove), and the verdict and gas it was recorded with. The straight contract and the
//! deployable one (its parts of at most 24,576 bytes) are built from the verifier for the vector's shape and
//! configuration, then:
//!
//! - both accept the calldata, at the recorded gas, when `PCS_OPEN` attests exactly the recorded inputs, and call it
//!   with exactly those inputs, in order;
//! - both revert on mutations: a byte of the stream flipped (a root, a Flock scalar, a value at `t`, a round of the
//!   batching sumcheck, the last byte), a row count changed, the public input changed, one call left unattested, a
//!   byte of an attested input flipped.
//!
//! `main_line_rec.txt` is π1-rec's (`FLOCK_REC`, `crates/leanvm_rec/SPEC-REC.md` §1.4). The two Fiat–Shamir shapes do
//! not cross: the main line's contract rejects π1-rec's proof, and π1-rec's the main line's, even with `PCS_OPEN`
//! attesting every call.
//!
//! `cargo test --release -p leanvm_univariate --test evm_vectors -- --nocapture`

mod vectors;

use leanvm_flock_gas::evm::codegen::word;
use leanvm_flock_gas::evm::machine::{PcsOpen, call};
use leanvm_univariate::Claims;
use leanvm_univariate::contract::{compile_verifier, record_verifier};
use vectors::{PROGRAM_IV, Vector, blake2s_of, deployable, read};

/// Run `f` on a thread with a deep stack: the code generator recurses along the graph.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn attesting(calls: &[Vec<u8>]) -> PcsOpen {
    let mut pcs = PcsOpen::default();
    for input in calls {
        pcs.register(input.clone());
    }
    pcs
}

/// Calldata after the selector (4 bytes) and the public input (32): the stream.
const STREAM_AT: usize = 4 + 32;

fn replay(v: Vector) {
    let blake2s = blake2s_of(&v.config);
    let recorded = record_verifier(&v.shape, blake2s, Claims::Point);
    assert_eq!(STREAM_AT + recorded.stream_len, v.calldata.len(), "{}: the calldata is the shape's", v.config);
    let straight = compile_verifier(&recorded, &PROGRAM_IV, false);
    let deployed = deployable(&recorded);
    assert_eq!(deployed.contracts.len(), v.contracts, "{}: the deployable build's contracts", v.config);
    let one = word([1, 0, 0]);
    let block = attesting(&v.calls);
    let run_straight = |data: &[u8], block: &PcsOpen| call(&straight.code, &[], data, block);
    let run_deployed = |data: &[u8], block: &PcsOpen| deployed.chain.call(deployed.address, data, block);

    for (build, outcome, gas) in [
        ("straight", run_straight(&v.calldata, &block), v.gas_straight),
        ("deployed", run_deployed(&v.calldata, &block), v.gas_deployed),
    ] {
        assert_eq!(outcome.output.as_deref() == Some(&one[..]), v.accepts, "{} {build}: the verdict", v.config);
        assert_eq!(outcome.pcs_calls, v.calls, "{} {build}: the calls are the recorded inputs", v.config);
        assert_eq!(outcome.execution, gas, "{} {build}: the gas of execution", v.config);
        println!("{} {build}: accepts, {gas} gas of execution, {} PCS_OPEN calls", v.config, v.calls.len());
    }

    // Mutations, each of which both builds must revert on.
    let stream_len = recorded.stream_len;
    let mut mutants: Vec<(String, Vec<u8>, PcsOpen)> = Vec::new();
    let flip = |at: usize| {
        let mut data = v.calldata.clone();
        data[at] ^= 1;
        data
    };
    for (what, at) in [
        ("a row count", STREAM_AT + 3),
        ("C1's root", STREAM_AT + 24 + 5),
        ("a scalar a third in", STREAM_AT + stream_len / 3),
        ("a scalar half way", STREAM_AT + stream_len / 2),
        ("a batching round", STREAM_AT + stream_len - 200),
        ("the last byte", STREAM_AT + stream_len - 1),
        ("the public input", 4 + 7),
    ] {
        mutants.push((format!("{what} flipped"), flip(at), attesting(&v.calls)));
    }
    for k in 0..v.calls.len() {
        let mut calls = v.calls.clone();
        calls.remove(k);
        mutants.push((format!("call {k} not attested"), v.calldata.clone(), attesting(&calls)));
        let mut calls = v.calls.clone();
        let last = calls[k].len() - 1;
        calls[k][last] ^= 1;
        mutants.push((format!("call {k}'s attested value flipped"), v.calldata.clone(), attesting(&calls)));
    }
    for (what, data, block) in &mutants {
        assert!(run_straight(data, block).output.is_none(), "{} straight: {what} must revert", v.config);
        assert!(run_deployed(data, block).output.is_none(), "{} deployed: {what} must revert", v.config);
    }
    println!("{}: {} mutations revert on both builds", v.config, mutants.len());
}

/// The main line's and π1-rec's contracts each reject the other's real proof: same stream layout, other challenges,
/// so their checks fail, even with every `PCS_OPEN` call attested.
#[test]
fn fiat_shamir_shapes_do_not_cross() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/vectors");
    let load = |name: &str| read(&std::fs::read_to_string(dir.join(format!("{name}.txt"))).expect("a vector"));
    for (proof, contract) in [("main_line", "main_line_rec"), ("main_line_rec", "main_line")] {
        let (v, other) = (load(proof), load(contract));
        deep(move || {
            let recorded = record_verifier(&other.shape, blake2s_of(&other.config), Claims::Point);
            assert_eq!(STREAM_AT + recorded.stream_len, v.calldata.len(), "the same stream layout");
            let straight = compile_verifier(&recorded, &PROGRAM_IV, false);
            let deployed = deployable(&recorded);
            let one = word([1, 0, 0]);
            let all = PcsOpen::attesting_all(0);
            let own = call(&straight.code, &[], &other.calldata, &all);
            assert_eq!(own.output.as_deref(), Some(&one[..]), "{contract}'s contract accepts its own proof");
            assert!(
                call(&straight.code, &[], &v.calldata, &all).output.is_none(),
                "{contract}'s straight build rejects {proof}'s proof"
            );
            assert!(
                deployed.chain.call(deployed.address, &v.calldata, &all).output.is_none(),
                "{contract}'s deployable build rejects {proof}'s proof"
            );
            println!("{contract}'s contract (both builds) rejects {proof}'s real proof, every call attested");
        });
    }
}

/// Every vector file, replayed.
#[test]
fn vectors_replay_on_both_builds() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/vectors");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("tests/vectors")
        .map(|e| e.expect("an entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "txt"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "the vectors are committed");
    for path in files {
        let text = std::fs::read_to_string(&path).expect("a vector");
        let v = read(&text);
        println!("{}: {} calldata bytes", path.display(), v.calldata.len());
        deep(move || replay(v));
    }
}
