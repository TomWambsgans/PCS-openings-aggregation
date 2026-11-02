-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Openings
import QuotientRpm.Rpm

/-!
# The numbers

The list factor times the round error, at the sizes of `quotient::protocol` (a field of `2^192`
elements, `2^24` cells, eight words):

* with leanerVM's generic list bound `L ≤ 2^18` for both roots and identities of degree at most
  `2^28` (`Params.ofCantor_identity_le_margin`), at most `2^-128` (`listError_le_generic`, from
  F1's margin `roundError_mul_sq_le`);
* with the certified lists of the deployed codes, `7908` candidates per witness root
  (`log_n = 25`) and `3564` per quotient root (`log_n = 28`), `WhirBridge.candidates_ours`, and
  identities of degree at most `2^29`, at most `2^-138` (`listError_le_certified`):
  `7908 · 3564 = 28,184,112 < 2^25` pairs, each round at most `2^-163`.

`knowledgeSoundness_composed_bits`: the composed bound is then the openings' terms plus
`(Q + 6 + QV) (2^-128 + 4 (Q + 6 + QV) / 2^256)`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}

/-- **The generic margin**: lists of at most `2^18`, identities of degree at most `2^28`. -/
theorem listError_le_generic (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28) {L₁ L₂ : ℕ} (h₁ : L₁ ≤ 2 ^ 18)
    (h₂ : L₂ ≤ 2 ^ 18) :
    (listFactor L₁ L₂ : ℝ≥0∞) * (roundError P B : ℝ≥0∞) ≤ ((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) := by
  have hm := roundError_mul_sq_le (P := P) (B := B) hq hN hw hd (2 ^ 18) le_rfl
  have hf : listFactor L₁ L₂ ≤ (2 ^ 18) ^ 2 := by
    unfold listFactor
    refine max_le (h₁.trans (by norm_num)) ?_
    rw [_root_.sq]
    exact Nat.mul_le_mul h₁ h₂
  have hf' : (listFactor L₁ L₂ : ℝ≥0) ≤ ((2 ^ 18 : ℕ) : ℝ≥0) ^ 2 := by exact_mod_cast hf
  calc (listFactor L₁ L₂ : ℝ≥0∞) * (roundError P B : ℝ≥0∞)
      = (((listFactor L₁ L₂ : ℝ≥0) * roundError P B : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
    _ ≤ (((((2 ^ 18 : ℕ) : ℝ≥0) ^ 2 * roundError P B) : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast mul_le_mul_of_nonneg_right hf' zero_le
    _ ≤ ((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hm

/-- **The certified lists**: `7908` witness candidates and `3564` quotient candidates per root,
identities of degree at most `2^29`. -/
theorem listError_le_certified (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 29) {L₁ L₂ : ℕ} (h₁ : L₁ ≤ 7908)
    (h₂ : L₂ ≤ 3564) :
    (listFactor L₁ L₂ : ℝ≥0∞) * (roundError P B : ℝ≥0∞) ≤ ((1 / 2 ^ 138 : ℝ≥0) : ℝ≥0∞) := by
  have hr := roundError_le (P := P) (B := B) hq hN hw hd
  have hf : listFactor L₁ L₂ ≤ 2 ^ 25 := by
    unfold listFactor
    refine max_le (h₁.trans (by norm_num)) ((Nat.mul_le_mul h₁ h₂).trans (by norm_num))
  have hf' : (listFactor L₁ L₂ : ℝ≥0) ≤ 2 ^ 25 := by exact_mod_cast hf
  have key : (listFactor L₁ L₂ : ℝ≥0) * roundError P B ≤ 1 / 2 ^ 138 :=
    calc (listFactor L₁ L₂ : ℝ≥0) * roundError P B ≤ 2 ^ 25 * (1 / 2 ^ 163) :=
          mul_le_mul hf' hr zero_le zero_le
      _ = 1 / 2 ^ 138 := by
          rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul,
            ← pow_add]
  calc (listFactor L₁ L₂ : ℝ≥0∞) * (roundError P B : ℝ≥0∞)
      = (((listFactor L₁ L₂ : ℝ≥0) * roundError P B : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
    _ ≤ ((1 / 2 ^ 138 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast key

variable (W : Wire P B) (C₁ : ListCommit B.Msg₁) (C₂ : ListCommit B.Msg₂) {O : Type}

/-- **The composed bound at the sizes of `quotient::protocol`**, with lists of at most `2^18`:
the openings' terms plus `(Q + 6 + QV) (2^-128 + 4 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_composed_bits (hq : Fintype.card F = 2 ^ 192)
    (hN : P.nCells = 2 ^ 24) (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (h₁ : C₁.bound ≤ 2 ^ 18) (h₂ : C₂.bound ≤ 2 ^ 18)
    (A : OracleComp HashSpec (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp HashSpec Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      WitnessDoomed C₁ z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      QuotientDoomed W C₂ z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[Breaks W C₁ z] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
        4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_composed W C₁ C₂ A openings Q QV hQ hV εW εσ εQ hW hσ hQd).trans ?_
  gcongr
  exact listError_le_generic hq hN hw hd h₁ h₂

end Compose
