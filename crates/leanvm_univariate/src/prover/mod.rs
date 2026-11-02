// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The prover of SPEC.md (milestone 2; `PROVER.md`): on an execution trace of leanVM 42422001 (its own execution
//! and witness generation, dumped by `dump/`), the stream the verifier reads and one WHIR opening per commitment.
//!
//! - [`trace`]: the trace leanVM wrote;
//! - [`poly`]: the Cantor subspaces' transforms (vectorized in `quotient::ntt`), basis `B`, the extension cosets;
//! - [`columns`]: `C1`'s and the setup's polynomials;
//! - [`fingerprint`], [`prints`], [`bus`]: the bus's fingerprints (one point at a time, and eight), leaves and
//!   product heap;
//! - [`quotients`]: the tree, leaf and constraint quotients;
//! - [`stack`]: the three stacks, as the verifier's layouts place the columns;
//! - [`batch`]: the batching sumcheck (point-claim ABI);
//! - [`opening`]: the point claims proven with leanVM's WHIR;
//! - [`replay`]: the verifier's combined claims on the point-claim stream;
//! - [`prove`]: the driver, and [`check`]: the identities on the domain.

pub mod batch;
pub mod bus;
pub mod check;
pub mod columns;
pub mod fingerprint;
pub mod flock;
pub mod matrices;
pub mod opening;
pub mod poly;
pub mod prints;
pub mod prove;
pub mod quotients;
pub mod replay;
pub mod setup;
pub mod stack;
pub mod trace;
