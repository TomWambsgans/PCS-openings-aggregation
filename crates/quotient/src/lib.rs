// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6 (`flock::quotient`). MIT OR Apache-2.0; see NOTICE.md.
//! Merkle membership with Keccak-256, zero knowledge through the hidden layouts of [`opening`] (`HIDING.md`: the
//! hiding conditions are checked exactly at random challenges; their proof for all challenges is in progress),
//! reduced to four multilinear evaluation claims by five field elements and no sumcheck: the protocol of leanVM's `flock::quotient` (`doc/quotient/main.tex` there), on a
//! circuit of one χ gate on bits, its claims opened by leanVM's WHIR.

pub mod circuit;
pub mod domain;
#[cfg(test)]
mod hiding;
pub mod opening;
pub mod protocol;
pub mod statement;
pub mod transcript;
