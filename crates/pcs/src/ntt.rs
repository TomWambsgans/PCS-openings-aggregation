// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit c445e3d51a5a85031df47240595698f3b24897bf, file crates/pcs/src/ntt.rs.
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and NOTICE.md at the repository root).
// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The additive NTT (Lin-Chung-Han novel polynomial basis) WHIR commits with.

pub mod additive_ntt_f64;
pub use additive_ntt_f64::{AdditiveNttF64, RowSink, transpose_lane_major};
pub(crate) use additive_ntt_f64::{prefetch, transposed_butterfly_lanes};
