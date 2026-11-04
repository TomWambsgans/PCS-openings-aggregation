-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Non-vacuity of the recursive verifier's end theorems (`STATEMENT_REVIEW.md`, findings 1 and 5). Run from
-- `formal/EndToEnd` on h1, after `lake build RecCompose`:
--   systemd-run --scope -q -p MemoryMax=10G lake env lean ../RecCompose/Review/NonVacuity.lean
import RecCompose.RealDeployment
import RecCompose.FsClosed
import RecCompose.Pi2AlphaEnd
import UniSound.Ids.Deployed

/-!
# The end theorems' hypotheses are inhabited, given the evaluations

From the run-checked inputs only (`GraphsAgree`, `IvChecked`, `DigestChecked`, `SetupRootChecked`, each a `Prop`
about compiled values, checked by evaluation: `RecGraphTest/Pi1Check.lean`, `rec-real-check`):

* `real`: `RecDeployment.Real` of a concrete deployment, `realDeployment prog0 rfl`;
* `circuits`, `viewChecked`: a `Pi2Circuits` of it (the Lean compiler's circuits at every 32-byte IV) and its
  `Pi2ViewChecked`, with `hroots` by `rfl`;
* `inhabited`: so the premises of `recKnowledgeSoundness2_closed`, `recKnowledgeSoundness_closed(_fs)`,
  `Pi2Alpha.recCompleteness2_pi2_rec3_closed` and `_fs` are jointly satisfiable;
* `soundness2`, `Pi2Alpha.nonVacuity_completeness2`: those end theorems at this deployment, with no hypothesis left but the four
  evaluated ones.

`prog0` is any program of the reference shape's size (`2^19` instructions, all `xor 0 0 0`): `Real` does not pin the
program, and every program of that size gives a real deployment.
-/

namespace RecCompose.NonVacuity

open RecStatement
open scoped ENNReal

/-- A program of the reference shape's size. -/
def prog0 : Lv42.Semantics.Program where
  logSize := UniStatement.reference.logBytecode
  logSize_le := by rw [UniSound.Ids.reference_eq]; decide
  code := fun _ ↦ .xor 0 0 0

/-- The concrete deployment. -/
abbrev D0 : RecDeployment := realDeployment prog0 rfl

variable (hg : GraphsAgree) (hiv : IvChecked) (hd : DigestChecked) (hs : SetupRootChecked)

include hg hd hs in
theorem real : D0.Real := realDeployment_real prog0 rfl hg hd hs

/-- The compiled circuits of `D0`. -/
abbrev circuits : Pi2Circuits D0 := pi2Circuits_real prog0 rfl hg hiv

include hg hiv in
theorem viewChecked : Pi2ViewChecked (circuits hg hiv) := pi2ViewChecked_real prog0 rfl hg hiv

include hg hiv hd hs in
/-- **The hypotheses are jointly inhabited.** -/
theorem inhabited : ∃ (D : RecDeployment) (_ : D.Real) (C : Pi2Circuits D),
    C.rootsAt = RecGraph.Emitted.rootsAt ∧ GraphsAgree ∧ Pi2ViewChecked C :=
  ⟨D0, real hg hd hs, circuits hg hiv, rfl, hg, viewChecked hg hiv⟩

include hg hiv hd hs in
/-- **π2's part at `D0`**, from the evaluated inputs only. -/
theorem soundness2 : RecKnowledgeSoundness2 D0 pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  recKnowledgeSoundness2_closed D0 (real hg hd hs) (circuits hg hiv) rfl hg (viewChecked hg hiv)

end RecCompose.NonVacuity

namespace RecCompose.Pi2Alpha

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2O
open scoped ENNReal

/-- **π2's completeness at `D0`**, from the evaluated inputs only. -/
theorem nonVacuity_completeness2 (hg : GraphsAgree) (hiv : IvChecked) (hd : DigestChecked)
    (hs : SetupRootChecked) :
    RecCompleteness2 NonVacuity.D0 (pi1Rec3Prover NonVacuity.D0)
      (pi2Prover NonVacuity.D0 (NonVacuity.circuits hg hiv)
        (pi2Facts (NonVacuity.real hg hd hs) (NonVacuity.circuits hg hiv) (NonVacuity.viewChecked hg hiv))
        PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_pi2_rec3_closed (NonVacuity.real hg hd hs) (NonVacuity.circuits hg hiv)
    (NonVacuity.viewChecked hg hiv) rfl hg

end RecCompose.Pi2Alpha

#print axioms RecCompose.NonVacuity.inhabited
#print axioms RecCompose.NonVacuity.soundness2
#print axioms RecCompose.Pi2Alpha.nonVacuity_completeness2
