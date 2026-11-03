-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The discharge follows `Closed.lean` (the main line's):
-- `weightMle_ref`, `layoutVarsSmall_reference`, the batch the verifier's (`flockGood`, inside `uniFinal3`).
import UniSound.Rec3.FinalLink3
import UniSound.Rec3.Closed3

/-!
# π1-rec3's last link at the reference deployment

**`uniFinal3_ref`**: `UniFinal3` at the reference deployment for π1-rec3's Flock `flock3Ref D hw`, identity model
`ids3Ref D hD hw`, batch `pairBatchRec3 13` and code-level link `code3Ref D hD hw`. It is `uniFinal3` with the main
line's hypotheses discharged as `Closed.lean` discharges them: the weights multilinear off the merge polynomial's roots
(`Closed.weightMle_ref`, the main line's `WeightMle` at Flock's main-line instance, which `ids3Of` reads at the
expanded transcripts), the stacks below `256` variables (`layoutVarsSmall_reference`). The identity model's batch is
the verifier's inside `uniFinal3` (`main3Out_aligned`, `flockGood`), so no `BatchIsVerifiers` remains.

**`uniKnowledgeSoundness_rec3_of_walk`**: with it, `Closed3.lean`'s `uniKnowledgeSoundness_rec3_of_final` leaves only
the walk's fact `hw` (and leanVM's program IV).
-/

namespace UniSound.Rec3Ref

open UniStatement LeanVM.Parameters FlockSound.Uni UniSound.Ids
open scoped ENNReal

/-- **π1-rec3's last link at the reference deployment.** -/
theorem uniFinal3_ref (D : Deployment) (hD : D.shape = reference)
    (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    UniFinal3 D (flock3Ref D hw) (ids3Ref D hD hw) (pairBatchRec3 13) (code3Ref D hD hw) :=
  uniFinal3 D (busBound D.shape) (idsHyps_ref D hD) 50708397 135
    (idsGaps_ref D hD (flockSoundInstance _) 50708397 135 (idsRemainingRef D hD _)) (tx_of_flockTx _) hw 13
    (batchVars_ref3 D hD) (nV_ref3 D hD hw) (UniSound.Closed.weightMle_ref D hD) (layoutVarsSmall_reference D hD)

/-- **π1-rec3 at the reference deployment, from the walk's fact**: `uniKnowledgeSoundness_rec3_of_final` with the
last link `uniFinal3_ref`. -/
theorem uniKnowledgeSoundness_rec3_of_walk (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    UniKnowledgeSoundnessRec3 D (uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_rec3_of_final D hD hIv hw (uniFinal3_ref D hD hw)

end UniSound.Rec3Ref

/-- info: 'UniSound.Rec3Ref.uniFinal3_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniFinal3_ref

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_of_walk
