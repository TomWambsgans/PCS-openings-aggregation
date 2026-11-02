// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/pcs/src/lib.rs.
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and NOTICE.md at the repository root).
// Part of this repository. The parts of leanVM's `crates/pcs` (commit 42422001) that flock's prover uses: the
// packing constants, the GF(2^8) additive NTT and its inverse table, one inner product. MIT OR Apache-2.0; see
// NOTICE.md.
//! leanVM 42422001's `pcs`, the subset flock's prover needs (`crates/lv42_flock`).

pub mod ntt;
pub mod pack;
pub mod ring_switch;
