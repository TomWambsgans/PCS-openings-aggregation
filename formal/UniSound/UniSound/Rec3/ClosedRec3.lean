-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `formal/UniStatement`'s
-- `UniKnowledgeSoundnessRec3` (`RecSecurity.lean`).
import UniSound.Rec3.Closed128_3
import UniSound.Rec3.Closed3
import FlockSoundUni.WalkAlg

/-!
# Knowledge soundness of π1-rec3, closed

**`uniKnowledgeSoundness_closed_rec3_of_rows`**: for every deployment at the reference shape with leanVM's program IV,
π1-rec3's verifier is knowledge sound for `uniExtractor` with error `uniBound128 (2^35/|E|) Q` at `Q` calls of `π`
and `π⁻¹`, at most `2^-64` for `Q ≤ 2^64` (128.49 bits), given only `RowsSpec`, the BLAKE2s circuit walk's
specification (`blake2sRowValues w` is `A0 w`, `B0 w`); the walk's lemma follows from it (`walkLemma_of_rows`,
`walkSpec_of`). `uniKnowledgeSoundness_closed_rec3_61_of_rows`: the same at the `≥ 61`-bit bound `uniBound3`.
-/

namespace UniSound.Rec3Ref

open UniStatement LeanVM.Parameters FlockSound.Uni
open scoped ENNReal

/-- **π1-rec3 at the reference deployment, at `≥ 128` bits, from the circuit walk's specification.** -/
theorem uniKnowledgeSoundness_closed_rec3_of_rows (hR : RowsSpec) (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundnessRec3 D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundness_rec3_128_of_walk D hD hIv (walkSpec_of (walkLemma_of_rows hR))

/-- **π1-rec3 at the reference deployment, at the `uniBound3` bound, from the circuit walk's specification.** -/
theorem uniKnowledgeSoundness_closed_rec3_61_of_rows (hR : RowsSpec) (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundnessRec3 D (uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_rec3_of_walk D hD hIv (walkSpec_of (walkLemma_of_rows hR))

end UniSound.Rec3Ref

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3_of_rows
