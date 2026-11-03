-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Final3.lean`'s `uniKnowledgeSoundness3` and
-- `uniKnowledgeSoundness3_bits` with the Fiat–Shamir layer at `≥ 128` bits (`FsLayer128_3`), as the main line's
-- `Closed128.lean`'s `uniKnowledgeSoundness128`.
import UniSound.Rec3.Final3
import UniSound.Rec3.Fs128_3

/-!
# Knowledge soundness of π1-rec3 at `≥ 128` bits, from its named links

**`uniKnowledgeSoundness3_128`**: `uniKnowledgeSoundness3_bits` with `FsLayer128_3` in place of `FsLayer3`: under
π1-rec3's Flock phase `F3`, the identity model `I`, the batch `BR`, the code-level links `C`, `hFin` and the layer
`hFs`, every round's error at most `2^35 / |E|`, π1-rec3's verifier is knowledge sound for `uniExtractor` with
error `uniBound128 (2^35 / |E|) Q`, **at most `2^-64` for `Q ≤ 2^64`** (`uniBound128_le_bits35`; `2^-64.494` at
`Q = 2^64`, 128.49 bits as `Q / ε`: `EndToEnd/Review/UniRec3Numbers.py`, exact rationals). The PIOP is
`uniPiop3 F3 I BR` (`PiopSound3.lean`), its errors `uniErr3_le`, its first state `hpre_uniPiop3`, its last link
`hlink_uniPiop3` (`Final3.lean`). `fsLayer128_3_holds` (`FsFinal128_3.lean`) gives `hFs`.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

variable {D : Deployment} {κ : ℕ} (F3 : FlockSound3 κ) {np : ℕ} (I : UniIds3 D F3 np) (BR : PairBatch np)

/-- **Knowledge soundness of π1-rec3 at `≥ 128` bits**: under the same hypotheses as `uniKnowledgeSoundness3_bits`
with the Fiat–Shamir layer at `≥ 128` bits, the error `uniBound128 (2^35 / |E|)`, at most `2^-64` for every adversary
of at most `2^64` calls of `π` and `π⁻¹`. -/
theorem uniKnowledgeSoundness3_128 (C : UniCode3 D F3 I.nV np) (hFin : UniFinal3 D F3 I BR C)
    (hFs : FsLayer128_3 D F3 I.nV np C)
    (hMain : I.errMain ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, F3.err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 35) (hrel : I.nRel + 2 ≤ 2 ^ 35)
    (hP : BR.errPair ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hL : BR.errLast ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) :
    UniKnowledgeSoundnessRec3 D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  ⟨hFs (uniPiop3 F3 I BR) _ (uniErr3_le F3 I BR _ hMain hFl
      (ENNReal.div_le_div_right (Nat.cast_le.mpr hdeg) _)
      (ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _) hP hL)
    (hpre_uniPiop3 F3 I BR) (hlink_uniPiop3 F3 I BR C hFin), uniBound128_le_bits35⟩

end UniSound

/-- info: 'UniSound.uniKnowledgeSoundness3_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness3_128
