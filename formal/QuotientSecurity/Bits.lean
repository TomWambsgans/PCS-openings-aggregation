-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Bits.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.RoundByRound

/-!
# 128 bits

At the sizes of `quotient::protocol` (a field of `2^192` elements, `N = 2^24` cells, eight public
words, identities of degree at most `2^29`), every challenge's error is below `2^-128`: the first
`(4 N + 8) / q = (2^26 + 8) / 2^192`, about `2^-166`; the second at most `2^29 / 2^192 = 2^-163`
(on the instance the identities have degree `11 * 2^24 + 8 < 2^28`, so `2^-164`); the third
`3 / 2^192`.

**The margin.** Instantiated with WHIR without an out-of-domain sample at the first level, each
challenge must also be union-bounded over the Johnson lists of the commitments it follows: the
first and the third over one list, the second over two. With lists of at most `L ≤ 2^18` words
(leanerVM's generic list hypothesis) and identities of degree at most `2^28`, every challenge's
error times `L^2` is still at most `2^-128` (`rbrError_mul_sq_le`, `rbrError_list_margin`): the
first `2^36 (2^26 + 8) / 2^192 < 2^-129`, the second `2^36 * 2^28 / 2^192 = 2^-128`, the third
`3 * 2^36 / 2^192`.
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

theorem mul_div_le_two_pow {k a q : ℕ} (hq : 0 < q) (h : k * a * 2 ^ 128 ≤ q) :
    (k : ℝ≥0) * ((a : ℝ≥0) / (q : ℝ≥0)) ≤ 1 / 2 ^ 128 := by
  rw [← mul_div_assoc, ← Nat.cast_mul]
  exact div_le_two_pow hq h

/-- **128 bits of round-by-round soundness.** -/
theorem rbrError_le (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 29) (i : (pSpec P B).ChallengeIdx) :
    rbrError P B i ≤ 1 / 2 ^ 128 := by
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have h29 : B.identity * 2 ^ 128 ≤ Fintype.card F := by
    rw [hq]
    exact (Nat.mul_le_mul_right (2 ^ 128) hd).trans (by norm_num)
  unfold rbrError
  split
  · exact div_le_two_pow hpos (by rw [hq, hN, hw]; norm_num)
  · exact div_le_two_pow hpos h29
  · exact div_le_two_pow hpos (by rw [hq]; norm_num)

/-- **The margin for the lists.** With identities of degree at most `2^28` and any `L ≤ 2^18` (the
size of a level-0 Johnson list under leanerVM's generic list hypothesis), every challenge's error
times `L^2` is at most `2^-128`. -/
theorem rbrError_mul_sq_le (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28) (L : ℕ) (hL : L ≤ 2 ^ 18)
    (i : (pSpec P B).ChallengeIdx) : (L : ℝ≥0) ^ 2 * rbrError P B i ≤ 1 / 2 ^ 128 := by
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hL2 : L ^ 2 ≤ 2 ^ 36 := (Nat.pow_le_pow_left hL 2).trans (by norm_num)
  rw [← Nat.cast_pow]
  unfold rbrError
  split
  · refine mul_div_le_two_pow hpos ?_
    rw [hq, hN, hw]
    calc L ^ 2 * (4 * 2 ^ 24 + 8) * 2 ^ 128 ≤ 2 ^ 36 * (4 * 2 ^ 24 + 8) * 2 ^ 128 := by gcongr
      _ ≤ 2 ^ 192 := by norm_num
  · refine mul_div_le_two_pow hpos ?_
    rw [hq]
    calc L ^ 2 * B.identity * 2 ^ 128 ≤ 2 ^ 36 * 2 ^ 28 * 2 ^ 128 := by gcongr
      _ ≤ 2 ^ 192 := by norm_num
  · refine mul_div_le_two_pow hpos ?_
    rw [hq]
    calc L ^ 2 * 3 * 2 ^ 128 ≤ 2 ^ 36 * 3 * 2 ^ 128 := by gcongr
      _ ≤ 2 ^ 192 := by norm_num

/-- **The margin, challenge by challenge.** For any `L ≤ 2^18`: the first challenge `(α, β, γ)`
and the third `ρ`, each followed by one list, have error times `L` at most `2^-128`; the second
`t`, followed by two, has error times `L^2` at most `2^-128`. -/
theorem rbrError_list_margin (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28) (L : ℕ) (hL : L ≤ 2 ^ 18) :
    (L : ℝ≥0) * rbrError P B ⟨⟨1, by norm_num⟩, rfl⟩ ≤ 1 / 2 ^ 128 ∧
      (L : ℝ≥0) ^ 2 * rbrError P B ⟨⟨3, by norm_num⟩, rfl⟩ ≤ 1 / 2 ^ 128 ∧
      (L : ℝ≥0) * rbrError P B ⟨⟨5, by norm_num⟩, rfl⟩ ≤ 1 / 2 ^ 128 := by
  have hLL : (L : ℝ≥0) ≤ (L : ℝ≥0) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero L
  have h := rbrError_mul_sq_le P B hq hN hw hd L hL
  exact ⟨(mul_le_mul_left hLL _).trans (h _), h _, (mul_le_mul_left hLL _).trans (h _)⟩

end QuotientSecurity
