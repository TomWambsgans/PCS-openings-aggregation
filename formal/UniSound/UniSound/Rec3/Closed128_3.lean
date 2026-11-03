-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `formal/UniStatement`'s
-- `UniKnowledgeSoundnessRec3` (`RecSecurity.lean`); the assembly is `Closed3.lean`'s with the `≥ 128`-bit layer.
import UniSound.Rec3.FinalRef3
import UniSound.Rec3.FsFinal128_3
import UniSound.Rec3.Final128_3

/-!
# Knowledge soundness of π1-rec3 at the reference deployment, at `≥ 128` bits

**`uniKnowledgeSoundness_rec3_128_of_walk`**: for every deployment at the reference shape with leanVM's program IV,
π1-rec3's verifier is knowledge sound for `uniExtractor` with error `uniBound128 (2^35/|E|) Q` at `Q` calls of `π`
and `π⁻¹`, at most `2^-64` for `Q ≤ 2^64` (`2^-64.494` at `Q = 2^64`: 128.49 bits,
`EndToEnd/Review/UniRec3Numbers.py`), given the walk's fact `hw` only. It is `uniKnowledgeSoundness3_128` with
Flock (`flock3Ref`), the identity model (`ids3Ref`), the batch (`pairBatchRec3 13`), the code-level link
(`code3Ref`, its roots `uniCode3At_roots`), the last link (`uniFinal3_ref`), the `≥ 128`-bit Fiat–Shamir layer
(`fsLayer128_3_holds`) and the reference numbers (`Ref3.lean`, `Numbers3.lean`).
-/

namespace UniSound.Rec3Ref

open UniStatement LeanVM.Parameters FlockSound.Uni UniSound.Ids
open scoped ENNReal

/-- **π1-rec3 at the reference deployment, at `≥ 128` bits, from the walk's fact.** -/
theorem uniKnowledgeSoundness_rec3_128_of_walk (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    UniKnowledgeSoundnessRec3 D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundness3_128 (flock3Ref D hw) (ids3Ref D hD hw) (pairBatchRec3 13) (code3Ref D hD hw)
    (uniFinal3_ref D hD hw)
    (fsLayer128_3_holds D (flock3Ref D hw) _ 13 (code3Ref D hD hw) (uniShapes_reference D hD)
      (layoutVarsSmall_reference D hD) (uniIv3_of D hIv)
      (hnQ_rec3 _ _ _ (by rw [hκ_reference D hD]; decide))
      (hnv_rec3 _ _ _ (by rw [nV_ref3 D hD hw]; exact valsCount_le.trans (by decide)))
      (uniOutRoots3_of D (flock3Ref D hw) _ 13 (code3Ref D hD hw)
        (uniCode3At_roots D (flock3Ref D hw) rfl _ 13 (nV_ref3 D hD hw) (by rw [hD, varsOf_reference]))))
    (hMain_ref3 D hD hw) (hFl_ref3 D hD hw) (hdeg_ref3 D hD hw) (hrel_ref3 D hD hw)
    (pairBatchRec3_errPair 13) (pairBatchRec3_errLast 13)

end UniSound.Rec3Ref

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_128_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_128_of_walk
