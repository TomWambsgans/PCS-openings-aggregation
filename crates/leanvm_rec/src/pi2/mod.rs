// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π2's PIOP (SPEC-REC.md §2.3, §4, §7 R3; `PI2.md`): the virtual-push copy argument on the Cantor subspace, one
//! quotient identity at `t`, four claims in three `PCS_OPEN` calls, for rows of `2^r` positions (D16v `r = 4`, D32v
//! `r = 5`).
//!
//! - [`circuit`]: the circuit as the PIOP sees it (pairs, formulas, `σ`, `κ`, the public side);
//! - [`adapt`]: the circuit compiler's interface (`crate::circuit::spec`) as that circuit;
//! - [`synth`]: synthetic circuits and their witnesses (the tests, the target shapes);
//! - [`prover`]: the prover, its tables committed and opened with leanVM's WHIR;
//! - [`verifier`]: the verifier, generic over the scalar;
//! - [`contract`]: the verifier compiled to EVM, its calls of `PCS_OPEN` (π1's five, then π2's three), its gas;
//! - [`pi1`]: π1-rec's calls, from its recorded verifier.

pub mod adapt;
pub mod circuit;
pub mod contract;
pub mod pi1;
pub mod prover;
pub mod synth;
pub mod verifier;
