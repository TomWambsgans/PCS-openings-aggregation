-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Opening
import Bridge.Chain

/-!
# The bridge: the statement's definitions are the proof layers'

`formal/Statement` (`PcsQuotient`) states the end theorems about its own transcriptions of the Rust;
the proofs (`formal/Circuit`, `QuotientSecurity`, `QuotientRpm`, `WhirBridge`, `Compose`,
`Completeness`, `Implementation`) are about theirs. Each file here proves one part of the statement's
definitions equal to the proofs' (see `README.md` of this package):

* `Bridge/Opening.lean`: the openings (layouts, weights, gadget, seed bytes, the check itself, the
  read-back of a hidden table) are F2's (`WhirBridge`).
* `Bridge/Chain.lean`: the reduction's Keccak-256 chain (label, roots, values, challenges) is F4's
  `chainWith` (`Compose`, F4a's bytes), then the statement's claims (`reduceWith_eq`).
-/
