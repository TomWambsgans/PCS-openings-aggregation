-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Bits.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.RoundByRound

/-!
# 128 bits

At the sizes of `flock::quotient` (a field of `2^192` elements, `2^22` cells, eight public words,
identities of degree below `2^27`), every challenge's error is below `2^-128`.
-/

set_option linter.unusedSectionVars false

open NNReal

namespace QuotientSecurity

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable (P : Params F) (B : P.Bounds)

theorem div_le_two_pow {a q : ℕ} (hq : 0 < q) (h : a * 2 ^ 128 ≤ q) :
    ((a : ℝ≥0) / (q : ℝ≥0)) ≤ 1 / 2 ^ 128 := by
  have hq' : (0 : ℝ≥0) < (q : ℝ≥0) := by exact_mod_cast hq
  rw [div_le_div_iff₀ hq' (by positivity), one_mul]
  exact_mod_cast h

/-- **128 bits of round-by-round soundness.** -/
theorem rbrError_le (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 22)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 27) (i : (pSpec P B).ChallengeIdx) :
    rbrError P B i ≤ 1 / 2 ^ 128 := by
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have h27 : B.identity * 2 ^ 128 ≤ Fintype.card F := by
    rw [hq]
    exact (Nat.mul_le_mul_right (2 ^ 128) hd).trans (by norm_num)
  unfold rbrError
  split
  · exact div_le_two_pow hpos (by rw [hq, hN, hw]; norm_num)
  · exact div_le_two_pow hpos h27
  · exact div_le_two_pow hpos (by rw [hq]; norm_num)

end QuotientSecurity
