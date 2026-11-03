// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π2's verifier as `formal/RecStatement` transcribes it (`leanvm_rec::lean_statement`), on π2's real circuit for
//! π1-rec3's 1,000-signature proof (`crates/leanvm_univariate/tests/vectors/main_line_rec3.txt`), D16v:
//!
//! - `statement_data_is_current` (ignored: it compiles the real circuit and commits its setup, about 8 GB): the
//!   checked-in `formal/RecStatement/RecStatement/Data.lean` is what `lean_statement::render` writes now;
//!   `UPDATE_LEAN=1` rewrites it.
//! - `lean_statement_vectors` (ignored; `REC_STATEMENT_OUT=<path>`, about 12 GB): the same check, then π2's real proof
//!   of π1-rec3's proof, and the vectors of `formal/RecStatement`'s differential runner: the real proof, its stream
//!   with one byte flipped at many places (π1's roots, its elements, `W`'s and `Q`'s roots, every value), under other
//!   public inputs, truncated and extended, and pseudo-random streams (`REC_STATEMENT_COUNT`, default 24), each with
//!   every value of the Rust verifier and every `PCS_OPEN` input; on each, the compiled contract (revm, every call
//!   attested) calls `PCS_OPEN` with exactly the Rust's inputs.
//!
//! `RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_rec --test lean_statement -- --ignored --nocapture`

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

#[path = "../../leanvm_univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_flock_gas::evm::machine::{PcsOpen, call};
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_rec::circuit::compile::{Inputs, Layout, pi2};
use leanvm_rec::circuit::spec::CallWord;
use leanvm_rec::lean_statement::{Constants, header, render, vector};
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::circuit::Circuit;
use leanvm_rec::pi2::contract::{self, Instance, Recorded, calldata, record_verifier, sample_stream};
use leanvm_rec::pi2::prover::{PublicValue, Setup, prove};
use leanvm_rec::pi2::verifier::Spec;
use leanvm_univariate::Claims;
use primitives::field::F64;

const STREAM_AT: usize = 4 + 32;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn data_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../formal/RecStatement/RecStatement/Data.lean")
}

/// The real instance: the adapted circuit, its witness and public values, π1's calls and contract IV.
struct Real {
    circuit: Circuit,
    witness: Vec<F64>,
    public_input: [u8; 32],
    values: Vec<PublicValue>,
    calls: Vec<Vec<CallWord>>,
    pi1_iv: [u8; 32],
}

fn real() -> Real {
    let file = format!(
        "{}/../leanvm_univariate/tests/vectors/main_line_rec3.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    let v = vectors::read(&std::fs::read_to_string(&file).expect("the committed vector"));
    assert_eq!(v.config, "main_line_rec3");
    let recorded =
        leanvm_univariate::contract::record_verifier(&v.shape, vectors::blake2s_of(&v.config), Claims::Point);
    let stream = v.calldata[STREAM_AT..].to_vec();
    let c = pi2(
        &recorded,
        Layout::D16v,
        &Inputs {
            program_iv: PROGRAM_IV,
            public: v.public,
            stream: &stream,
        },
    );
    let circuit = adapt::adapt(&c.finished.circuit);
    let witness = adapt::witness(&c.finished.witness);
    let (public_input, values) = adapt::public_values(&c.public);
    Real {
        circuit,
        witness,
        public_input,
        values,
        calls: c.finished.circuit.calls.clone(),
        pi1_iv: c.pi1_iv,
    }
}

/// The data file for `real`, checked against the checked-in one (or written, with `UPDATE_LEAN=1`).
fn check_data(real: &Real, setup: &Setup) {
    let rendered = render(
        &real.circuit,
        &real.calls,
        &Constants {
            pi1_iv: real.pi1_iv,
            setup_root: setup.root(),
            digest: real.circuit.digest(),
        },
    );
    let path = data_path();
    if std::env::var_os("UPDATE_LEAN").is_some() {
        std::fs::write(&path, &rendered).expect("the Lean data written");
        return;
    }
    let current = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        current == rendered,
        "{} is stale: run `UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_statement -- --ignored statement_data_is_current`",
        path.display()
    );
}

/// The checked-in Lean data is π2's real circuit's: `UPDATE_LEAN=1` rewrites it.
#[test]
#[ignore]
fn statement_data_is_current() {
    deep(|| {
        let real = real();
        let setup = Setup::new(&real.circuit);
        check_data(&real, &setup);
    });
}

/// The compiled contract on `calldata`, every well-formed `PCS_OPEN` call attested: the inputs it called with.
fn contract_calls(inst: &Instance, recorded: &Recorded, data: &[u8]) -> Vec<Vec<u8>> {
    let code = contract::compile_verifier(inst, recorded, false).code;
    let mut block = PcsOpen::decoding(contract::registry(inst));
    block.attest_all = true;
    call(&code, &[], data, &block).pcs_calls
}

#[test]
#[ignore]
fn lean_statement_vectors() {
    let Ok(path) = std::env::var("REC_STATEMENT_OUT") else {
        eprintln!("REC_STATEMENT_OUT unset: nothing written");
        return;
    };
    let count: u64 = std::env::var("REC_STATEMENT_COUNT").map_or(24, |n| n.parse().expect("a count"));
    let text = deep(move || {
        let real = real();
        let setup = Setup::new(&real.circuit);
        check_data(&real, &setup);
        let spec = Spec::of(&real.circuit);
        let inst = Instance::new(&real.circuit, &spec, setup.root(), &real.pi1_iv, &real.calls);
        let recorded = record_verifier(&spec);
        let proved = prove(
            &real.circuit,
            &spec,
            &setup,
            &inst.iv,
            &real.public_input,
            &real.values,
            &real.witness,
        );
        let stream = proved.stream.clone();
        drop(proved);
        let public = real.public_input;
        let run = |name: &str, public: &[u8; 32], stream: &[u8]| -> String {
            let made = (stream.len() == recorded.stream_len)
                .then(|| contract_calls(&inst, &recorded, &calldata(public, stream)));
            vector(name, &inst, &recorded, public, stream, made.as_deref())
        };
        let mut out = String::from(
            "# formal/RecStatement's differential vectors (crates/leanvm_rec/tests/lean_statement.rs): pi2's real circuit for pi1-rec3, D16v\n",
        );
        out.push_str(&header(&inst, &recorded));
        out.push_str(&run("real", &public, &stream));
        // One byte flipped: π1's roots, its elements (the pair challenges and the values), W's and Q's roots, the
        // fold values and ξ, the last byte.
        let (w_at, q_at) = (recorded.roots_at[2], recorded.roots_at[3]);
        let values_at = q_at + 32;
        let mut flips = vec![0, 31, 32, 63, 64, 64 + 23, 64 + 24 * 7 + 3, 64 + 24 * 13 + 20, w_at - 1];
        flips.extend([w_at, w_at + 17, q_at, q_at + 31]);
        flips.extend((0..spec.values()).map(|k| values_at + 24 * k + (5 * k) % 24));
        flips.push(stream.len() - 1);
        for &at in &flips {
            let mut bad = stream.clone();
            bad[at] ^= 1 << (at % 8);
            out.push_str(&run(&format!("flip{at}"), &public, &bad));
        }
        // The real stream under other public inputs.
        for k in 0..3usize {
            let mut other = public;
            other[(5 + 11 * k) % 32] ^= 0x40;
            out.push_str(&run(&format!("public{k}"), &other, &stream));
        }
        // Truncated and extended streams: the length's errors.
        for cut in [1usize, 24, 500] {
            out.push_str(&run(&format!("truncate{cut}"), &public, &stream[..stream.len() - cut]));
        }
        for extra in [1usize, 24] {
            let mut long = stream.clone();
            long.extend(std::iter::repeat_n(0x5a, extra));
            out.push_str(&run(&format!("extend{extra}"), &public, &long));
        }
        // Pseudo-random streams and public inputs.
        for seed in 0..count {
            let random = sample_stream(stream.len(), 0x51a7 + seed);
            let public: [u8; 32] = sample_stream(32, 0x9e11 + seed).try_into().expect("32 bytes");
            out.push_str(&run(&format!("random{seed}"), &public, &random));
        }
        out
    });
    std::fs::write(path, text).expect("the vectors written");
}
