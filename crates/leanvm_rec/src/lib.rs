// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Recursion for the univariate leanVM 42422001 verifier (`SPEC-REC.md`), milestone R1: what the outer proof `π2`
//! must prove, measured on the inner verifier's recorded graph.
//!
//! `π1` is `crates/leanvm_univariate`'s proof. Its verifier, run on the recorder's symbol, is a graph
//! (`leanvm_flock_gas::evm::record`): the stream's reads, the Keccak-256 chain, `E`'s additions and products, the
//! checks, and the `PCS_OPEN` claims. That graph is the circuit `π2` proves, PCS openings excluded.
//!
//! - [`count`]: the graph's live nodes by kind, the Keccak-256 calls and their permutations, the packings between
//!   bytes and `E`, the checks, and the claims' points.
//! - [`eval`]: the graph evaluated on a real proof's calldata, every node's value: the witness `π2`'s prover starts
//!   from, checked against the recorded `PCS_OPEN` inputs of the committed test vectors.

#![forbid(unsafe_code)]

pub mod count;
pub mod eval;
pub mod fs;

use leanvm_univariate::Shape;

/// The reference workload (`crates/leanvm_univariate/SPEC.md` §1): 1,000 leanXMSS signatures, 1,023,109 cycles.
pub const REFERENCE: Shape = Shape {
    log_memory: 21,
    log_bytecode: 19,
    table_rows: [183_266, 195_439, 223_851, 137_591, 80_937, 202_025],
};

/// Keccak-256's rate in bytes.
pub const KECCAK_RATE: usize = 136;

/// Keccak-f\[1600\] permutations of one Keccak-256 of `len` bytes: pad10*1 adds at least one byte.
pub fn permutations(len: usize) -> usize {
    len / KECCAK_RATE + 1
}
