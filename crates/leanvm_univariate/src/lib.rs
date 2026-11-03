// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! A univariate PIOP for leanVM 42422001's statement, for the EVM: SPEC.md.
//!
//! [`verifier::reduce`] is the verifier, generic over the scalar it computes on: on `E` with the Keccak-256 chain it
//! is the contract's verifier in Rust; on the recorder's symbol it is the graph [`contract`] compiles to EVM code.

#![forbid(unsafe_code)]

pub mod claims;
pub mod contract;
pub mod domain;
pub mod heap;
pub mod prover;
pub mod stacks;
pub mod verifier;

pub use leanvm_flock_gas::transcript::FsShape;
pub use verifier::{
    Blake2s, Claims, FLOCK_BIT_SLICE, FLOCK_LEANVM_SKIP, FLOCK_MAIN, FLOCK_REC, FLOCK_REC2, FLOCK_REC3, Opening, Reduced, Shape, reduce,
};
