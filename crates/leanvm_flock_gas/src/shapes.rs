// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The proofs the gas is measured for: leaf aggregates of leanXMSS signatures by leanVM 42422001's aggregation
//! guest (`crates/rec_aggregation/guests/lean_ethereum.py`), proved by leanVM's `leanvm gas-dump` (`dump/`), with
//! `--log-inv-rate 1` as leanVM's README benchmark. Their announced sizes, as the proofs announce them.

use crate::{N_TABLES, Shape};

/// The aggregation guest's stacked bytecode: `2^23` words, whatever the signatures.
pub const BYTECODE_LEN: usize = 1 << 23;

/// The aggregation guest's Fiat-Shamir IV (`Bytecode::fiat_shamir_iv`, the BLAKE2s of the R1CS digest and of the
/// stacked bytecode), which the contract's Keccak seed also takes.
pub const PROGRAM_IV: [u8; 32] = [
    0xb5, 0x41, 0x04, 0x5c, 0x98, 0x65, 0x5d, 0xb5, 0xa8, 0xaa, 0xc6, 0x1e, 0xfd, 0xb0, 0xad, 0xea, 0x1e, 0xaf, 0xab,
    0x5f, 0x51, 0x02, 0xa4, 0xe3, 0xf9, 0x3d, 0xf9, 0xc7, 0x53, 0x27, 0x1e, 0x1e,
];

/// One measured proof.
#[derive(Clone, Copy, Debug)]
pub struct Workload {
    pub name: &'static str,
    pub xmss: usize,
    pub shape: Shape,
    /// What the leanVM proof is: its stream's scalars, of which the PIOP's (before the stacked opening), the VM's
    /// cycles, and the committed words.
    pub stream_elements: usize,
    pub piop_elements: usize,
    pub cycles: u64,
    pub log2_committed: f64,
}

const fn shape(log_memory: u64, table_rows: [u64; N_TABLES]) -> Shape {
    Shape {
        log_memory,
        table_rows,
        log_inv_rate: 1,
        bytecode_len: BYTECODE_LEN,
    }
}

/// Table rows in leanVM's order: XOR, MUL, SET, DEREF, JUMP, BLAKE2S.
pub const WORKLOADS: [Workload; 5] = [
    Workload {
        name: "xmss32",
        xmss: 32,
        shape: shape(16, [6060, 6490, 11768, 4703, 2699, 6489]),
        stream_elements: 918,
        piop_elements: 831,
        cycles: 38_209,
        log2_committed: 21.778,
    },
    Workload {
        name: "xmss128",
        xmss: 128,
        shape: shape(18, [23629, 25224, 32804, 17879, 10468, 25881]),
        stream_elements: 974,
        piop_elements: 887,
        cycles: 135_885,
        log2_committed: 23.611,
    },
    Workload {
        name: "xmss400",
        xmss: 400,
        shape: shape(20, [73426, 78352, 92398, 55231, 32463, 80825]),
        stream_elements: 1093,
        piop_elements: 990,
        cycles: 412_695,
        log2_committed: 25.492,
    },
    Workload {
        name: "xmss1290",
        xmss: 1290,
        shape: shape(22, [236343, 252019, 287373, 177391, 104394, 260605]),
        stream_elements: 1169,
        piop_elements: 1048,
        cycles: 1_318_125,
        log2_committed: 26.676,
    },
    Workload {
        name: "xmss2000",
        xmss: 2000,
        shape: shape(22, [366327, 390501, 442955, 274831, 161790, 404025]),
        stream_elements: 1207,
        piop_elements: 1104,
        cycles: 2_040_429,
        log2_committed: 27.524,
    },
];

/// leanVM's README benchmark: 1,290 leanXMSS signatures.
pub fn benchmark() -> &'static Workload {
    WORKLOADS.iter().find(|w| w.xmss == 1290).expect("the benchmark")
}
