-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Node
import Implementation.Graph
import Implementation.Arith
import Implementation.Interp
import Implementation.Program
import Implementation.Field
import Implementation.Semantics
import Implementation.Blocks
import Implementation.Reduce
import Implementation.Claims
import Implementation.Constants
import Implementation.Calldata
import Implementation.Leaves
import Implementation.Verifier
import Implementation.Frobenius
import Implementation.Model

/-!
# The implementation is the model (layer F5)

The EVM contract and the Rust verifier are generated from one recorded operation graph
(`crates/evm/src/record.rs`). `Implementation/Graph.lean` is that graph, written by the Rust
(`crates/evm/src/lean.rs`, whose test fails when the file is stale); `Interp.lean` interprets it on
calldata as the bytecode generator compiles each node (EVM words, `XOR`, `FIELD_MUL`, `KECCAK256`
of `MSTORE`d words, `CALLDATALOAD`, shifts and masks) for any hash `H`.

Proved here, for any field `F` with `F192`'s limb representation (`IsF192`: `XOR` is `+`,
`FIELD_MUL` is `*`, one is `(1, 0, 0)`; the Frobenius node is then `x^(2^64)`, `frobOK`):

* `Program.reduceIds_eq`, `Program.checkId_eq` (kernel evaluation): the Lean transcription of
  `quotient::protocol::reduce` finds every node it asks for in the graph and gives exactly the
  contract's output words and its nonzero check;
* `reduceIds_spec`, `checkId_spec`: those nodes hold `reduce`'s formulas over `F` (per-node
  semantics `val_add`, `val_mul`, `val_frob`, `val_const`; the inversion by the norm is `x⁻¹`);
* `witness_eq`, `wiring_eq`, `quotient_eq`, `sum_eq`, `check_eq`: the formulas are the claims and the
  denominator of `claims_iff_accepts_ofCantor` on `membershipParams`, with the graph's constants
  checked by computation (`consts`, `basis`);
* `leafVals_calldataOf`: on calldata, the leaves are the statement's halves and the challenges of
  `Wire.verifyWith`'s Keccak-256 chain, byte for byte;
* `graph_reaches_iff`, `graph_words`, `graph_is_verifier` (**F5**): the contract reaches its calls
  of `PCS_OPEN` exactly when the denominators do not vanish, hands it the model's claims, and with
  those claims true of the tables is exactly the model's `Wire.verifyWith` (deployed `Wire`,
  `wire`) accepting, but for the challenges where some `1 + w_k(t)` vanishes.

Tested, not proved: the bytecode computes the graph (`crates/evm`'s parity tests against the Rust
verifier and `Implementation/Diff.lean` against this interpreter), and that `F192`'s Rust
arithmetic is `mulE` (the differential test; F0c's `formal/Field` proves the field's laws for
CompPoly's arithmetic, not yet tied to `mulE`).
-/

/-- info: 'Implementation.Program.reduceIds_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Implementation.Program.reduceIds_eq

/-- info: 'Implementation.Program.checkId_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Implementation.Program.checkId_eq

/-- info: 'Implementation.reduceIds_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.reduceIds_spec

/-- info: 'Implementation.quotient_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.quotient_eq

/-- info: 'Implementation.consts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.consts

/-- info: 'Implementation.frobOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.frobOK

/-- info: 'Implementation.leafVals_calldataOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.leafVals_calldataOf

/-- info: 'Implementation.graph_reaches_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.graph_reaches_iff

/-- info: 'Implementation.graph_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.graph_words

/-- info: 'Implementation.graph_is_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Implementation.graph_is_verifier
