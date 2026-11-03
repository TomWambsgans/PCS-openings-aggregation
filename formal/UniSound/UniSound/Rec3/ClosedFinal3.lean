-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `formal/UniStatement`'s
-- `UniKnowledgeSoundnessRec3` (`RecSecurity.lean`).
import UniSound.Rec3.ClosedRec3
import FlockSoundUni.Walk

/-!
# Knowledge soundness of π1-rec3, closed: no hypothesis

**`uniKnowledgeSoundness_closed_rec3`**: for every deployment at the reference shape (`reference`: 1,000 signatures,
heights `18 18 18 18 17 18`, memory `2^21`, bytecode `2^19`) with leanVM's program IV, and every program, π1-rec3's
verifier (`Deployment.verifierRec3With`: `verifyWithFs … .rec3 true`, three `PCS_OPEN` calls) is knowledge sound
against leanVM 42422001's relation for the explicit extractor `uniExtractor`, with error `uniBound128 (2^35/|E|) Q` at
`Q` calls of `π` and `π⁻¹`, at most `2^-64` for `Q ≤ 2^64` (`2^-64.494` at `Q = 2^64`: 128.49 bits,
`EndToEnd/Review/UniRec3Numbers.py`, exact rationals). **No hypothesis.**

It is `uniKnowledgeSoundness_closed_rec3_of_rows` (`ClosedRec3.lean`) with the circuit walk's specification
`rowValues_spec` (`FlockSoundUni/Walk.lean`: `blake2sRowValues w` is `A0 w`, `B0 w` of Lv42's BLAKE2s R1CS).
`uniKnowledgeSoundness_closed_rec3_61` is the same at the bound `uniBound3` (three openings' doom terms, `2^-61`).
-/

namespace UniSound.Rec3Ref

open UniStatement LeanVM.Parameters FlockSound.Uni
open scoped ENNReal

/-- **The circuit walk's specification**, proved (`rowValues_spec`). -/
theorem rowsSpec_holds : RowsSpec := fun cw hcw j ↦ rowValues_spec cw hcw j

/-- **Knowledge soundness of π1-rec3 for leanVM 42422001, closed**: for every deployment at the reference shape with
leanVM's program IV (and every program), π1-rec3's verifier is knowledge sound for the explicit extractor
`uniExtractor`, with error `uniBound128 (2^35 / |E|) Q` at `Q` calls of `π` and `π⁻¹`, at most `2^-64` for
`Q ≤ 2^64`. No hypothesis. -/
theorem uniKnowledgeSoundness_closed_rec3 (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundnessRec3 D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundness_closed_rec3_of_rows rowsSpec_holds D hD hIv

/-- **The same at the three openings' `uniBound3`** (`≤ 2^-61` for `Q ≤ 2^64`). No hypothesis. -/
theorem uniKnowledgeSoundness_closed_rec3_61 (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundnessRec3 D (uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_closed_rec3_61_of_rows rowsSpec_holds D hD hIv

end UniSound.Rec3Ref

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3_61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3_61
