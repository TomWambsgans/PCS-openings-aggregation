-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit
import Bridge.Opening
import Bridge.Chain
import Bridge.Verifier
import Bridge.Extractor
import Bridge.Claims.Reduce
import Bridge.Ntt
import Bridge.Setup
import Bridge.Facts

/-!
# The bridge: the statement's definitions are the proof layers'

`formal/Statement` (`PcsQuotient`) states the end theorems about its own transcriptions of the Rust;
the proofs (`formal/Circuit`, `QuotientSecurity`, `QuotientRpm`, `WhirBridge`, `Compose`,
`Completeness`, `Implementation`) are about theirs. Each file here proves one part of the statement's
definitions equal to the proofs' (see `README.md` of this package):

* `Bridge/Circuit.lean` (`Bridge/Circuit/*.lean`): the statement's `membership 22` is F0b's
  `PcsCircuit.membership` (`membership_eq`; rows, inputs, `σ`), proved for general builder steps,
  never evaluating the `2^22`-row run.
* `Bridge/Opening.lean`: the openings (layouts, weights, gadget, seed bytes, the check itself, the
  read-back of a hidden table) are F2's (`WhirBridge`).
* `Bridge/Chain.lean`: the reduction's Keccak-256 chain (label, roots, values, challenges) is F4's
  `chainWith` (`Compose`, F4a's bytes), then the statement's claims (`reduceWith_eq`).
* `Bridge/Verifier.lean`: the statement's verifier is `Soundness.verifyES` (F4's chain and three
  openings with the statement's early stops), given the claims (`verifyWith_eq_verifyES`,
  `verifierBridge_of_claims`: `Soundness.VerifierBridge`).
* `Bridge/Extractor.lean`: the extractor's read-back of the witness table is F4's table of the stack
  (`witnessEntries_eq`).
* `Bridge/Ntt.lean`: the statement's additive transform (`Domain.values`, `Domain.coefficients`)
  evaluates and interpolates F1's novel-basis table polynomial on the Cantor points, for every size.
* `Bridge/Setup.lean`: the circuit's commitment (`setupWith`, `setupTreeWith`) is mumbai's tree of the
  wiring column's `stackWord`, and that column's polynomial carries `σ` (`setupBridge`).
* `Bridge/Claims/*.lean`: the statement's reduction claims `claimsAt 22` are `Compose.Reduce.reduce`
  at the statement's constants `statementConsts` (`claimsAt_eq_reduce`), and those constants are
  `beta()`'s and `row_vanishing(24)`'s (kernel evaluation, stepwise).
* `Bridge/Facts.lean`: the three facts `formal/EndToEnd/Soundness/Hypotheses.lean` takes, at
  `statementConsts`.
-/
