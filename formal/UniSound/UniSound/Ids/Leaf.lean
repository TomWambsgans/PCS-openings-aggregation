-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Cvec

/-!
# The identities on the domain: claims at moved points, the restriction, the padded leaf

* `colPoly_eval_congr`: a column's claim depends only on its point's values, so the tree's
  `T(s(X))`, `T(X + 1)` and the root's `T(1)` are `T` at `s(x)`, `x + 1`, `1` (`digitP_eval_sq`,
  `digitP_eval_add_one`).
* `mixP_eval_pointE`: **the restriction** (SPEC §2): at `ω_k`, `k < 2^r`, a heap block's mixed point is
  the digits of `ω_{pos + k}` (`pos` aligned), so `R_b(ω_k) = T(ω_{pos + k})`.
* `active_of_leaf`, `padding_of_leaf`: **the padded leaf** (F1, times `Z_act`):
  `w_r A + Z² (R + 1) = 0` as polynomials gives, where `w_r` and `Z` vanish, `A = 0` — the derivative,
  `w_r' = 1` and `(Z²)' = 0` in characteristic two — and where only `w_r` does, `R = 1`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

theorem getD_map_range (f : ℕ → E) {n l : ℕ} (hl : l < n) : ((List.range n).map f).getD l 0 = f l := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

/-- **A column's claim depends only on its point's values.** -/
theorem colPoly_eval_congr (L : StackLayout) (V : ℕ) (C : Stk) (col : Column) (P P' : ℕ → Polynomial E)
    (x y : E) (h : ∀ l, (P l).eval x = (P' l).eval y) :
    (colPoly L V C col P).eval x = (colPoly L V C col P').eval y := by
  unfold colPoly
  rw [eval_listSum, eval_listSum, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun b _ ↦ ?_
  simp only [Function.comp_apply, Polynomial.eval_mul, eval_C]
  congr 1
  rw [eval_mlP _ _ _ x ((List.range b.2.1).map fun l ↦ (P l).eval x) (fun l hl ↦ (getD_map_range (fun l ↦ (P l).eval x) hl).symm),
    eval_mlP _ _ _ y ((List.range b.2.1).map fun l ↦ (P l).eval x)
      (fun l hl ↦ by rw [getD_map_range (fun l ↦ (P l).eval x) hl, h l])]

theorem digitP_eval_sq (l : ℕ) (x : E) :
    (digitP l).eval (QuotientSecurity.sq x) = (digitP (l + 1)).eval x := by
  rw [eval_digitP, eval_digitP, Function.iterate_succ_apply]

theorem sq_iterate_one (l : ℕ) : QuotientSecurity.sq^[l] (1 : E) = if l = 0 then 1 else 0 := by
  rcases l with _ | l
  · rfl
  · rw [Function.iterate_succ_apply, Heap.sq_one', QuotientSecurity.sq_iterate_zero]
    simp

theorem digitP_eval_add_one (l : ℕ) (x : E) :
    (digitP l).eval (x + 1) = (if l = 0 then digitP 0 + 1 else digitP l).eval x := by
  rw [eval_digitP, QuotientSecurity.sq_iterate_add, sq_iterate_one]
  split_ifs with hl
  · subst hl; simp [digitP]
  · rw [add_zero, eval_digitP]

theorem digitP_eval_one (l : ℕ) : (digitP l).eval (1 : E) = (if l = 0 then (1 : Polynomial E) else 0).eval 0 := by
  rw [eval_digitP, sq_iterate_one]
  split_ifs <;> simp

/-! ## The restriction -/

theorem shiftRight_xor (a b l : ℕ) : (a ^^^ b) >>> l = (a >>> l) ^^^ (b >>> l) :=
  Nat.eq_of_testBit_eq fun j ↦ by simp [Nat.testBit_shiftRight, Nat.testBit_xor]

theorem pointE_xor (h : BetaCantor) {a b : ℕ} (ha : a < 2 ^ 24) (hb : b < 2 ^ 24) :
    pointE (a ^^^ b) = pointE a + pointE b := by
  rw [pointE_eq_omega h (Nat.xor_lt_two_pow ha hb), pointE_eq_omega h ha, pointE_eq_omega h hb,
    Heap.omega_xor]

theorem shiftRight_lt {a l : ℕ} (ha : a < 2 ^ 24) : a >>> l < 2 ^ 24 :=
  lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) ha

/-- **The restriction at `ω_k`**: a block's mixed point is the digits of `ω_{pos + k}`. -/
theorem mixP_eval_pointE (h : BetaCantor) (b : Block) {k : ℕ} (hal : 2 ^ b.r ∣ b.position)
    (hk : k < 2 ^ b.r) (hpk : b.position + k < 2 ^ 24) (l : ℕ) :
    (mixP b l).eval (pointE k) = (digitP l).eval (pointE (b.position + k)) := by
  have hk24 : k < 2 ^ 24 := by omega
  have hp24 : b.position < 2 ^ 24 := by omega
  rw [eval_digitP_pointE h l hpk, Heap.add_eq_xor_of_dvd hal hk, shiftRight_xor,
    pointE_xor h (shiftRight_lt hp24) (shiftRight_lt hk24)]
  unfold mixP
  split_ifs with hl
  · rw [Polynomial.eval_add, eval_C, eval_digitP_pointE h l hk24, add_comm]
  · rw [eval_C, show k >>> l = 0 by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega))),
      pointE_zero, add_zero]

/-! ## The padded leaf -/

theorem two_eq_zero_poly : (2 : Polynomial E) = 0 := CharTwo.two_eq_zero

theorem derivative_sq_eq_zero (Z : Polynomial E) : derivative (Z ^ 2) = 0 := by
  rw [derivative_pow]
  have : (C ((2 : ℕ) : E)) = 0 := by
    rw [show ((2 : ℕ) : E) = 2 by norm_num, CharTwo.two_eq_zero, C_0]
  rw [this, zero_mul, zero_mul]

/-- **Where `w_r` and `Z` vanish, `A` does** (`w_r A + Z² (R + 1) = 0`, `w_r' = 1`). -/
theorem active_of_leaf (A R Z wr : Polynomial E) (θ : E) (h0 : wr * A + Z ^ 2 * (R + 1) = 0)
    (hw : wr.eval θ = 0) (hw' : (derivative wr).eval θ = 1) (hZ : Z.eval θ = 0) : A.eval θ = 0 := by
  have hd := congrArg (fun p ↦ (derivative p).eval θ) h0
  simp only [derivative_add, derivative_mul, derivative_sq_eq_zero, derivative_zero, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, hw, hw', hZ, eval_zero, zero_mul, add_zero, one_mul,
    zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hd
  exact hd

/-- **Where only `w_r` vanishes, `R = 1`.** -/
theorem padding_of_leaf (A R Z wr : Polynomial E) (θ : E) (h0 : wr * A + Z ^ 2 * (R + 1) = 0)
    (hw : wr.eval θ = 0) (hZ : Z.eval θ ≠ 0) : R.eval θ = 1 := by
  have he := congrArg (Polynomial.eval θ) h0
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, hw, eval_one, zero_mul,
    zero_add, eval_zero] at he
  exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hZ))

/-- A table's leaf identity in the form `w_r A + Z² (R + 1)`. -/
theorem leaf_form (R P P' Q Z wr : Polynomial E) :
    R * (P * wr + Z ^ 2) + Q * (wr * Z) + P' * wr + Z ^ 2 = wr * (R * P + Q * Z + P') + Z ^ 2 * (R + 1) := by
  ring

end UniSound.Ids
