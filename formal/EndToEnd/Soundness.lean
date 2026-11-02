-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.Defs
import Soundness.Hypotheses
import Soundness.Cost
import Soundness.RpmV
import Soundness.TreeLog
import Soundness.MerkleWord
import Soundness.F1Step
import Soundness.Extract
import Soundness.EarlyStop
import Soundness.Final

/-!
# Knowledge soundness of the deployed membership proof, end to end

**`Soundness.knowledgeSoundness : PcsQuotient.KnowledgeSoundness Soundness.ksBound`**
(`Soundness/Final.lean`): the end statement of `formal/Statement` (`PcsQuotient/Security.lean`), for
the Statement's explicit, computable extractor, proved from the proof layers with no hypothesis.

| File | What |
|---|---|
| `Defs.lean` | The deployed objects: the limbs, the wire, the proof's conversion (`convP`, `convAdv`), the verifier with the Statement's early stops (`verifyES`, `ourVerifierEarly`), the setup tree's log (`treeTr`). |
| `Hypotheses.lean` | The three bridge facts (`SetupBridge`, `VerifierBridge`, `ReadsSecret`), proved in `formal/EndToEnd/Bridge` (`Bridge.Facts`). |
| `Cost.lean` | The deployed verifier's calls of `π`: at most `(6 + 3 · 10122) · 2^32` (`cost_verifyD_deployD`; `Compose/Rpm.lean`'s `hOπ`). |
| `RpmV.lean` | `Compose`'s random-permutation theorem with the verifier's cost as a whole, at the deployed claim maps (`knowledgeSoundness_rust_rpm`, `ksBound`). |
| `TreeLog.lean` | The setup's Keccak-256 log is its tree's evaluations (`loggedKC_stackSetup`). |
| `MerkleWord.lean` | The Statement's committed word (mumbai's `committedLeaves`) is Compose's (`merkleWord`). |
| `F1Step.lean` | A satisfying first message proves membership (`provesMembership_of_sat`); the reduction's own check (`reductionCheck_of_reduce`). |
| `Extract.lean` | If Compose's list holds a witness, the Statement's extractor finds a secret (`extractor_of_mem`). |
| `EarlyStop.lean` | The verifier with early stops accepts at most as often as Compose's (`es_le`); a malformed proof is rejected (`verifier_malformed`). |
| `Final.lean` | The experiments' coupling (`prEvent_le_of_continuations`, `step_le`) and **`knowledgeSoundness`**. |
-/
