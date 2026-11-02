-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit
import Bridge.Opening
import Bridge.Chain
import Bridge.Verifier
import Bridge.Extractor

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
-/
