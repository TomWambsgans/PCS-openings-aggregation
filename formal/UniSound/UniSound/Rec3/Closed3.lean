-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `formal/UniStatement`'s
-- `UniKnowledgeSoundnessRec3` (`RecSecurity.lean`); the assembly follows `Closed.lean` (the main line's).
import UniSound.Rec3.Numbers3
import UniSound.Rec3.CodeLink3

/-!
# Knowledge soundness of π1-rec3 at the reference deployment

**`uniKnowledgeSoundness_rec3_of_code`**: for every deployment at the reference shape with leanVM's program IV,
π1-rec3's verifier (`verifierRec3With`: `verifyWithFs … .rec3 true`, three openings) is knowledge sound for
`uniExtractor`, with error `uniBound3 (2^35/|E|) Q`, at most `2^-61` for `Q ≤ 2^64` (`2^-61.93` at `Q = 2^64`,
`EndToEnd/Review/UniRec3Numbers.py`), given the walk's fact `hw`, a code-level link `C` whose chain program names the
stream's roots (`hroots`), and the last link `hFin`. The Fiat–Shamir layer is `fsLayer3_holds` (proved), its numbers
`Numbers3.lean`'s; the identity model, Flock and the batch `Ref3.lean`'s.
-/

namespace UniSound.Rec3Ref

open UniStatement LeanVM.Parameters FlockSound.Uni UniSound.Ids
open scoped ENNReal

/-- **π1-rec3 at the reference deployment, from the walk, the code-level link and the last link.** -/
theorem uniKnowledgeSoundness_rec3_of_code (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) (hw : WalkSpec (D.shape.heights.getD opBlake2s 0))
    (C : UniCode3 D (flock3Ref D hw) (ids3Ref D hD hw).nV 13)
    (hroots : ∀ input rows (done : Done) (tl : List E), ((C.prog input rows).out done tl).roots =
      (((done.getD 0 default).1.1).getD default,
        ((done.getD ((flock3Ref D hw).prog.rounds.length + 1) default).1.1).getD default))
    (hFin : UniFinal3 D (flock3Ref D hw) (ids3Ref D hD hw) (pairBatchRec3 13) C) :
    UniKnowledgeSoundnessRec3 D (uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_rec3_ref D hD hw C hFin
    (fsLayer3_holds D (flock3Ref D hw) _ 13 C (uniShapes_reference D hD)
      (layoutVarsSmall_reference D hD) (uniIv3_of D hIv)
      (hnQ_rec3 _ _ _ (by rw [hκ_reference D hD]; decide))
      (hnv_rec3 _ _ _ (by
        show nVOf D.shape ≤ 2 ^ 30
        rw [nVOf_eq_of D.shape (by have h : tablesReads + 7 ≤ 122 := valsCount_le; omega)]
        exact valsCount_le.trans (by decide)))
      (uniOutRoots3_of D (flock3Ref D hw) _ 13 C hroots))

theorem nV_ref3 (D : Deployment) (hD : D.shape = reference) (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    (ids3Ref D hD hw).nV = valsCount := by
  show nVOf D.shape = valsCount
  exact nVOf_eq_of D.shape (by have h : tablesReads + 7 ≤ 122 := valsCount_le; omega)

/-- **π1-rec3's code-level link at the reference** (`uniCode3At`). -/
noncomputable def code3Ref (D : Deployment) (hD : D.shape = reference)
    (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    UniCode3 D (flock3Ref D hw) (ids3Ref D hD hw).nV 13 :=
  uniCode3At D (flock3Ref D hw) rfl _ 13 (nV_ref3 D hD hw) (by rw [hD, varsOf_reference])

/-- **π1-rec3 at the reference deployment, from the walk and the last link.** -/
theorem uniKnowledgeSoundness_rec3_of_final (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) (hw : WalkSpec (D.shape.heights.getD opBlake2s 0))
    (hFin : UniFinal3 D (flock3Ref D hw) (ids3Ref D hD hw) (pairBatchRec3 13) (code3Ref D hD hw)) :
    UniKnowledgeSoundnessRec3 D (uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_rec3_of_code D hD hIv hw (code3Ref D hD hw)
    (uniCode3At_roots D (flock3Ref D hw) rfl _ 13 (nV_ref3 D hD hw) (by rw [hD, varsOf_reference])) hFin

end UniSound.Rec3Ref

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_of_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_of_code

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_of_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_of_final
