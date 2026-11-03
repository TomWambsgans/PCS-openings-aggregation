-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The form follows
-- `formal/QuotientSecurity/Bits.lean`.
import RecPiop.Rounds

/-!
# The errors in bits, at π2's shape

At `N = 2^24` positions, rows of `16` (D16v), the three four-limb ports (the statement and π1's two
roots; `d_j = 1`, the other ports `0`, `RecPiop.Ports`), `|F| = 2^192`, and the candidate lists of
`W` and `Q` (`L_W = 9,952`, `L_Q = 3,564`), ListChainU's factors times `piop`'s errors are:

* the copy argument `(α, β, γ)`, over `L_W`: `9952 (3·2^24 + 2)/2^192 ≤ 2^-153` (`bits_copy`; 153.13);
* the identity at `t`, over `L_W L_Q`: `9952·3564 (5·2^24 − 1)/2^192 ≤ 2^-140` (`bits_t`; 140.60);
* `W`'s fold at `ρ`, over `L_W L_Q`: `9952·3564·15/2^192 ≤ 2^-163` (`bits_rho`; 163.01).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset
open scoped ENNReal

theorem nat_div_le_inv_pow {a c k : ℕ} (hc : 0 < c) (h : a * 2 ^ k ≤ c) :
    (a : ℝ≥0∞) / (c : ℝ≥0∞) ≤ 1 / 2 ^ k := by
  rw [ENNReal.div_le_iff (Nat.cast_ne_zero.mpr hc.ne') (ENNReal.natCast_ne_top _), one_div,
    ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
  exact_mod_cast h

theorem mul_div_le_inv_pow {L a c k : ℕ} (hc : 0 < c) (h : L * a * 2 ^ k ≤ c) :
    (L : ℝ≥0∞) * ((a : ℝ≥0∞) / (c : ℝ≥0∞)) ≤ 1 / 2 ^ k := by
  rw [← mul_div_assoc, ← Nat.cast_mul]
  exact nat_div_le_inv_pow hc h

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F] [Fintype F]

theorem N_of_logN {G : Circuit F} (hN : G.logN = 24) : G.N = 2 ^ 24 := by
  unfold Circuit.N
  rw [hN]

/-- **The copy argument, over `W`'s list: 153 bits.** -/
theorem bits_copy (G : Circuit F) (hN : G.logN = 24) (d : ℕ → ℕ)
    (hd : ∑ j ∈ range G.nP, d j = 3) (hF : Fintype.card F = 2 ^ 192) :
    ((9952 : ℕ) : ℝ≥0∞) * err G d 0 ≤ 1 / 2 ^ 153 := by
  unfold err
  rw [ite_eq_left rfl, hF, N_of_logN hN, hd]
  exact mul_div_le_inv_pow (by positivity) (by norm_num)

/-- **The identity at `t`, over `W`'s and `Q`'s lists: 140 bits.** -/
theorem bits_t (G : Circuit F) (hN : G.logN = 24) (d : ℕ → ℕ) (hF : Fintype.card F = 2 ^ 192) :
    ((9952 * 3564 : ℕ) : ℝ≥0∞) * err G d 1 ≤ 1 / 2 ^ 140 := by
  unfold err
  rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_eq_left rfl, hF, N_of_logN hN]
  exact mul_div_le_inv_pow (by positivity) (by norm_num)

/-- **`W`'s fold at `ρ`, over `W`'s and `Q`'s lists: 163 bits.** -/
theorem bits_rho (G : Circuit F) (hW : G.logW = 4) (d : ℕ → ℕ) (hF : Fintype.card F = 2 ^ 192) :
    ((9952 * 3564 : ℕ) : ℝ≥0∞) * err G d 2 ≤ 1 / 2 ^ 163 := by
  unfold err
  rw [ite_eq_right (by decide : (2 : ℕ) ≠ 0), ite_eq_right (by decide : (2 : ℕ) ≠ 1), hF, hW]
  exact mul_div_le_inv_pow (by positivity) (by norm_num)

end RecPiop
