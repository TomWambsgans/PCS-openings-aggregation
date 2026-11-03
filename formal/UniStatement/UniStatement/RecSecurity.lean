-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statements' form is `Security.lean`'s
-- (`UniKnowledgeSoundness`, `UniCompleteness`); the verifier is `Rec.lean`'s `verifyWithFs` at π1-rec3
-- (`crates/leanvm_univariate`'s `FLOCK_REC3`, `leanvm-rec` 4247e37).
module

public import UniStatement.Rec
public import UniStatement.Security

/-!
# Knowledge soundness and completeness of π1-rec3, against leanVM 42422001's relation

Statements only. They are `Security.lean`'s, with the deployed verifier replaced by **π1-rec3's**
(`crates/leanvm_rec/SPEC-REC.md` §12 item 8; `Rec.lean`):

* the contract's IV binds the variant (`contractIvForWith … (.flock flockMain) .rec3 true`: the main line's
  preimage with `fs-rec3`, the skip `3` and the slices' code `4` appended);
* the verifier is `verifyWithFs … .rec3 true`: the run (`reduceWithFs`: `α = (c, c², c⁴, c⁸)`, Flock's zerocheck
  coordinates after the seven fixed ones as squares of one challenge, Flock's lincheck terminal walked, the batch
  two variables a round with narrow challenges), then **three** `PCS_OPEN` calls (`C1`, `C2`, the setup); `A0`,
  `B0` are not opened (the proof's `a0`, `b0` are not read).

The setup, the extractor (`uniExtractor`: `C1`'s word under the root the stream names, the relation at the proof's
row counts), the adversary, the experiments' shape and the relation are `Security.lean`'s, unchanged: the setup
still commits `A0`, `B0` (the IV hashes their roots), though the verifier never opens them.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics (KeccakState)
open LeanVM.Extraction
open OracleComp OracleSpec Common
open scoped ENNReal

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **π1-rec3's IV** over `F` (`contract_iv_for` at `FLOCK_REC3`). -/
def Deployment.ivRec3With (D : Deployment) (roots : SetupRoots) : m (List UInt8) :=
  contractIvForWith F D.shape (.flock flockMain) .rec3 true D.programIv roots

/-- **π1-rec3's deployed verifier** over `F` on the setup's roots: its IV, then `verifyWithFs` at `.rec3` with the
walk (three calls). -/
def Deployment.verifierRec3With (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) : m Bool := do
  verifyWithFs F D.shape (← D.ivRec3With F roots) roots input proof .rec3 true

end With

/-- **π1-rec3's knowledge-soundness experiment**: the setup over `π`, the adversary given its roots (its queries
logged), then π1-rec3's verifier over `π`. -/
noncomputable def uniSoundnessExperimentRec3 (D : Deployment) (A : UniAdversary) : ProbComp UniOutcome :=
  runWithRandomPermutation do
    let trees ← setupTreesWith queryPermutation D
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let accepted ← D.verifierRec3With queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript)

/-- **Knowledge soundness of π1-rec3 for the extractor `ext`**, error `ε Q` for `Q` calls of `π` and `π⁻¹`. -/
def UniKnowledgeSoundnessRec3With (D : Deployment) (ext : UniExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : UniAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← uniSoundnessExperimentRec3 D A}[UniBreaksKnowledgeSoundness D ext z] ≤ ε Q

/-- **Knowledge soundness of π1-rec3** against leanVM 42422001's relation, for the explicit extractor
`uniExtractor`. -/
def UniKnowledgeSoundnessRec3 (D : Deployment) (ε : ℕ → ℝ≥0∞) : Prop :=
  UniKnowledgeSoundnessRec3With D (uniExtractor D) ε

/-- **π1-rec3's completeness experiment**: the setup, the prover's proof, π1-rec3's verdict, over `π`. -/
noncomputable def uniCompletenessExperimentRec3 (D : Deployment) (P : UniProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← setupTreesWith queryPermutation D
    match ← P input rows q with
    | none => return false
    | some proof => D.verifierRec3With queryPermutation trees.roots input proof

/-- **Completeness of π1-rec3 for the prover `P`**: its proof of a public input with an `M3Honest` stack, at row
counts that fit the shape, is rejected with probability at most `δ`. -/
def UniCompletenessRec3 (D : Deployment) (P : UniProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    Pr{let v ← uniCompletenessExperimentRec3 D P input rows q}[v = false] ≤ δ

end UniStatement

end

/-- info: 'UniStatement.UniKnowledgeSoundnessRec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.UniKnowledgeSoundnessRec3

/-- info: 'UniStatement.UniCompletenessRec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.UniCompletenessRec3
