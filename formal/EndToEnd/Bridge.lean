-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit
import Bridge.Circuit.Secret
import Bridge.Circuit.Outputs
import Bridge.Opening
import Bridge.Chain
import Bridge.Verifier
import Bridge.Extractor
import Bridge.Claims
import Bridge.Ntt
import Bridge.Setup
import Bridge.Facts

/-!
# The bridge: the statement's definitions are the proof layers'

`formal/Statement` (`PcsQuotient`) states the end theorems about its own transcriptions of the Rust;
the proofs (`formal/Circuit`, `QuotientSecurity`, `QuotientRpm`, `WhirBridge`, `Compose`,
`Completeness`, `Implementation`) are about theirs. Each file here proves a part of the statement's
definitions equal to the proofs', for general arguments (nothing of the `2^22`-row circuit or of a
`2^24`-entry table is ever evaluated):

* `Bridge/Circuit.lean` (`Bridge/Circuit/*.lean`): the statement's `membership 22` is F0b's
  `PcsCircuit.membership` (`membership_eq`; `membership_rows`, `membership_inputs`,
  `membership_sigma`, `membership_inputs_lt`), proved builder step by builder step; the secret the
  input rows' bits spell is F0b's (`Circuit/Secret.lean`, `secretMatches`); the computation
  (`Circuit.outputs`, `Circuit.cells`) and the inputs of a secret are F0b's (`Circuit/Outputs.lean`,
  `outputs_eq`, `membership_cells`, `membershipInputs_eq`, `secretOfInputs_membershipInputs`).
* `Bridge/Opening.lean`: the openings are F2's (`WhirBridge`): the layouts (`layoutTr_*Layout`), a
  claim's weight and the gadget's (`stackWeight_eq`, `gadgetWeight_eq`, `stackClaims_eq`), the seed's
  bytes (`encoding_eq`, `claimBytes_eq`, `openingPrefix_eq`), the check itself for every monad
  (`openingWith_eq`; `openingWith_eq_ourVerifier`: F2's `ourVerifier` with the early stop, its two
  calls answered over `F`), the read-back of a hidden table (`readEntry_eq`).
* `Bridge/Chain.lean`: the reduction's Keccak-256 chain (label, roots, values, challenges) is F4's
  `chainWith` (`Compose`, F4a's bytes), then the statement's claims (`reduceWith_eq`).
* `Bridge/Claims/*.lean`: the reduction's claims `claimsAt 22` are `Compose.Reduce.reduce` at the
  statement's constants `statementConsts` (`claimsAt_eq_reduce`); those constants are `beta()`'s and
  `row_vanishing(24)`'s and meet `reduce`'s hypotheses (`isCantor_statementConsts`,
  `rowVanishing_statementConsts`, by kernel evaluation, `rowVanishing 24` in 22 steps).
* `Bridge/Verifier.lean`: the statement's verifier is `Soundness.verifyES` (F4's chain and the three
  openings with the statement's early stops), for every monad and permutation
  (`verifyWith_eq_verifyES`, `verifierBridge_of_claims`).
* `Bridge/Ntt.lean`: the statement's additive transform (`Domain.values`, `Domain.coefficients`)
  evaluates and interpolates F1's novel-basis table polynomial on the Cantor points, for every size.
* `Bridge/Setup.lean`: the circuit's commitment (`setupWith`, `setupTreeWith`) is mumbai's tree of the
  wiring column's `stackWord` (`setupWith_eq`, `setupTreeWith_eq`, `wiringSetup_eq`), and that column's
  polynomial carries `σ` (`setupBridge`).
* `Bridge/Extractor.lean`: the extractor's read-back of the witness table is F4's table of the stack
  (`witnessEntries_eq`), its cells are F1's cells of that table (`cells_eq`), its input bits are the
  computation's (`inputBits_eq`).
* `Bridge/Facts.lean`: the three facts knowledge soundness takes (`formal/EndToEnd/Soundness/
  Hypotheses.lean`), proved at the statement's constants with nothing left: `setupBridge_final`,
  `verifierBridge_final`, `readsSecret_final`.

Two definitions of the statement were changed for the bridge, each the same function where it is
run deployed: the openings' layout identifier is the constant `Layout.id` (the deployed Keccak-256 of
the layout's encoding, as F2's `openingPrefix` and the Rust's `layout_id`; bytes-identical over
Keccak-f[1600], `Bridge.openingSponge_deployed`), and `membership` reads its builder's run by
projections rather than a pattern match (which the kernel reduced only by evaluating the run).

**Building.** Lib `Bridge` of this package; on a machine with the leanerVM checkout at
`formal/leanervm` (see the lakefile): `lake build Bridge` (about 6 minutes beyond the proof layers,
`Bridge/Claims/Tau.lean`'s stepwise elimination most of it).
-/
