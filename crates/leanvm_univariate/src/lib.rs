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
pub mod verifier;

pub use verifier::{Blake2s, Reduced, Shape, reduce};
