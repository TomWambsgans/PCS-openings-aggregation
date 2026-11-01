// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6 (`flock::quotient`). MIT OR Apache-2.0; see NOTICE.md.
//! Zero-knowledge Merkle membership with Keccak-256, reduced to four multilinear evaluation claims by five field
//! elements and no sumcheck: the protocol of leanVM's `flock::quotient` (`doc/quotient/main.tex` there), on a
//! circuit of one χ gate on bits, its claims opened by leanVM's WHIR.

pub mod circuit;
pub mod domain;
pub mod opening;
pub mod protocol;
pub mod statement;
pub mod transcript;
