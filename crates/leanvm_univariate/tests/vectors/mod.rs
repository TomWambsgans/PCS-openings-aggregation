// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The Rust→EVM test vectors (`tests/vectors/*.txt`, milestone 3): a real proof's calldata, the `PCS_OPEN` inputs
//! the contract calls with (which the openings prove), the verdict and the gas, straight and deployed. Written by
//! `tests/prove_real.rs` (`WRITE_VECTORS=<dir>`), replayed by `tests/evm_vectors.rs` with no prover and no trace.
//!
//! The format is lines of `key value`, the bytes in lowercase hex: `config`, `shape` (`log_memory log_bytecode` and
//! the six row counts), `public`, `calldata`, one `pcs_open` line per call in call order, one `whir_root` line per
//! call in call order (the root of the commitment the call opens, as the prover committed it: the hash whose two
//! scalars, `hash_to_scalars`, are its WHIR opening's first two; written by the prover's run, not read off the
//! contract's calls), `accepts`, `gas_straight`, `gas_deployed`, `contracts`; `#` starts a comment.

#![allow(dead_code)]

use leanvm_flock_gas::evm::codegen::{Ending, Entry, compile_deployable};
use leanvm_flock_gas::evm::contract::{Deployed, deploy};
use leanvm_univariate::contract::{NAME, Recorded, calls};
use leanvm_univariate::{Blake2s, FLOCK_BIT_SLICE, FLOCK_LEANVM_SKIP, FLOCK_MAIN, FLOCK_REC, FLOCK_REC2, FLOCK_REC3, Shape};

/// The program's IV the vectors' contracts are built with (`leanvm_flock_gas::shapes::PROGRAM_IV`).
pub use leanvm_flock_gas::shapes::PROGRAM_IV;

pub struct Vector {
    pub config: String,
    pub shape: Shape,
    pub public: [u8; 32],
    pub calldata: Vec<u8>,
    pub calls: Vec<Vec<u8>>,
    /// The roots of the commitments the calls open, in call order, from the prover's output (its commitments' and
    /// the setup's): what a real `PCS_OPEN` opens, whatever the contract encodes.
    pub whir_roots: Vec<[u8; 32]>,
    pub accepts: bool,
    pub gas_straight: u64,
    pub gas_deployed: u64,
    pub contracts: usize,
}

/// The configurations by name (`main_line_rec`: π1-rec, the main line with its Fiat–Shamir shape `FsShape::Rec`).
pub fn blake2s_of(config: &str) -> Blake2s {
    match config {
        "omitted" => Blake2s::Omitted,
        "main_line" => Blake2s::Flock(FLOCK_MAIN),
        "main_line_rec" => Blake2s::Flock(FLOCK_REC),
        "main_line_rec2" => Blake2s::Flock(FLOCK_REC2),
        "main_line_rec3" => Blake2s::Flock(FLOCK_REC3),
        "leanvm_skip" => Blake2s::Flock(FLOCK_LEANVM_SKIP),
        "ext_b" => Blake2s::Flock(FLOCK_BIT_SLICE),
        other => panic!("no configuration {other}"),
    }
}

pub fn name_of(blake2s: Blake2s) -> &'static str {
    match blake2s {
        Blake2s::Omitted => "omitted",
        Blake2s::Flock(v) if v == FLOCK_MAIN => "main_line",
        Blake2s::Flock(v) if v == FLOCK_REC => "main_line_rec",
        Blake2s::Flock(v) if v == FLOCK_REC2 => "main_line_rec2",
        Blake2s::Flock(v) if v == FLOCK_REC3 => "main_line_rec3",
        Blake2s::Flock(v) if v == FLOCK_LEANVM_SKIP => "leanvm_skip",
        Blake2s::Flock(v) if v == FLOCK_BIT_SLICE => "ext_b",
        Blake2s::Flock(_) => "flock",
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(text: &str) -> Vec<u8> {
    assert!(text.len().is_multiple_of(2), "whole bytes");
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).expect("hex"))
        .collect()
}

pub fn write(v: &Vector) -> String {
    let mut out = String::new();
    out.push_str("# leanvm_univariate Rust->EVM test vector (tests/vectors/mod.rs): a real proof, 1,000 leanXMSS signatures\n");
    out.push_str(&format!("config {}\n", v.config));
    let rows: Vec<String> = v.shape.table_rows.iter().map(u64::to_string).collect();
    out.push_str(&format!("shape {} {} {}\n", v.shape.log_memory, v.shape.log_bytecode, rows.join(" ")));
    out.push_str(&format!("public {}\n", hex(&v.public)));
    out.push_str(&format!("calldata {}\n", hex(&v.calldata)));
    for call in &v.calls {
        out.push_str(&format!("pcs_open {}\n", hex(call)));
    }
    for root in &v.whir_roots {
        out.push_str(&format!("whir_root {}\n", hex(root)));
    }
    out.push_str(&format!("accepts {}\n", v.accepts));
    out.push_str(&format!("gas_straight {}\n", v.gas_straight));
    out.push_str(&format!("gas_deployed {}\n", v.gas_deployed));
    out.push_str(&format!("contracts {}\n", v.contracts));
    out
}

pub fn read(text: &str) -> Vector {
    let mut v = Vector {
        config: String::new(),
        shape: Shape {
            log_memory: 0,
            log_bytecode: 0,
            table_rows: [0; 6],
        },
        public: [0; 32],
        calldata: Vec::new(),
        calls: Vec::new(),
        whir_roots: Vec::new(),
        accepts: false,
        gas_straight: 0,
        gas_deployed: 0,
        contracts: 0,
    };
    for line in text.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
        let (key, value) = line.split_once(' ').expect("key value");
        match key {
            "config" => v.config = value.to_string(),
            "shape" => {
                let n: Vec<u64> = value.split(' ').map(|x| x.parse().expect("a number")).collect();
                v.shape = Shape {
                    log_memory: n[0] as usize,
                    log_bytecode: n[1] as usize,
                    table_rows: n[2..8].try_into().expect("six counts"),
                };
            }
            "public" => v.public = unhex(value).try_into().expect("32 bytes"),
            "calldata" => v.calldata = unhex(value),
            "pcs_open" => v.calls.push(unhex(value)),
            "whir_root" => v.whir_roots.push(unhex(value).try_into().expect("32 bytes")),
            "accepts" => v.accepts = value == "true",
            "gas_straight" => v.gas_straight = value.parse().expect("a number"),
            "gas_deployed" => v.gas_deployed = value.parse().expect("a number"),
            "contracts" => v.contracts = value.parse().expect("a number"),
            other => panic!("no key {other}"),
        }
    }
    v
}

/// A call of π1's own contract in `PCS_OPEN`'s ABI (`crates/evm/src/machine.rs`; `crates/leanvm_rec/REVIEW-REC.md`
/// M1, R1), as π2's contract makes it: `C1`'s and `C2`'s root words are the stream's bytes, the ABI's already; a
/// setup root's (`F`, `A0`, `B0`: layout codes `0x5503..=0x5505`, the layout word's bytes 22..24) is the hash as it
/// is, its word `root_word` of it.
pub fn pi1_abi(input: &[u8]) -> Vec<u8> {
    let mut x = input.to_vec();
    let code = u16::from_be_bytes([x[32 + 22], x[32 + 23]]);
    if (0x5503..=0x5505).contains(&code) {
        let raw: [u8; 32] = x[..32].try_into().expect("a root");
        x[..32].copy_from_slice(&leanvm_flock_gas::evm::machine::root_word(&raw));
    }
    x
}

/// The deployable verifying build of `recorded` (`crates/evm_link`: contracts of at most 24,576 bytes), deployed.
pub fn deployable(recorded: &Recorded) -> Deployed {
    let call_words = calls(recorded);
    let ending = Ending::PcsOpen(call_words.iter().map(Vec::len).collect());
    let entry = Entry {
        name: NAME,
        iv: recorded.iv(&PROGRAM_IV),
        stream_len: recorded.stream_len,
        measure: false,
    };
    let real = compile_deployable(&recorded.graph, &call_words.concat(), &ending, &entry, 24_576);
    deploy(&real, &[])
}
