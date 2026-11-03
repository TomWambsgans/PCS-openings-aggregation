-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.DomainDigits

/-!
# The subspace polynomials `w_l` in `Polynomial E` (milestone 4, the domain facts)

`wP l` is Mathlib's `w_l`: `wP 0 = X`, `wP (l+1) = wP l ^ 2 + wP l` (the computable `UniComplete.wPoly` is
CompPoly's; this one is for proofs). Here:

* `wP_monic`, `wP_natDegree`: monic of degree `2^l`; `wP_eval`: `(wP l).eval t = s^l(t)`, the digit
  (`wP_eval_digits`: `= (digits t n).getD l 0`, `l < n`);
* `linProd S = Π_{j ∈ S} (X − ω_j)` for a set `S` of indices below `2^32`, and `eq_linProd`: a monic
  polynomial of degree `|S|` vanishing on `{ω_j : j ∈ S}` is `linProd S` (`ω` is injective on `[0, 2^32)`);
* `wP_eq_prod`: **`wP l = Π_{i < 2^l} (X − ω_i)`** for `l ≤ 32`, so its roots are exactly `V_l`
  (`wP_eval_eq_zero_iff`);
* `wP_dvd`: `wP l ∣ wP m`, `l ≤ m`; `wP_eq_mul`: `wP m = wP l · Π_{j=l}^{m−1} (wP j + 1)`, and
  `wP_divByMonic_eval`: `(wP m /ₘ wP l).eval t = vanishingRatio (digits t n) l m`, `m ≤ n`.
-/

namespace UniComplete.Domain

open LeanVM.Parameters UniStatement Finset Polynomial

/-- **The subspace polynomials** `w_0 = X`, `w_{l+1} = w_l² + w_l`. -/
noncomputable def wP : ℕ → E[X]
  | 0 => X
  | l + 1 => wP l ^ 2 + wP l

theorem wP_zero : wP 0 = X := rfl

theorem wP_succ (l : ℕ) : wP (l + 1) = wP l ^ 2 + wP l := rfl

theorem wP_monic_natDegree (l : ℕ) : (wP l).Monic ∧ (wP l).natDegree = 2 ^ l := by
  induction l with
  | zero => exact ⟨monic_X, by rw [wP_zero, natDegree_X, pow_zero]⟩
  | succ l ih =>
    obtain ⟨hm, hd⟩ := ih
    have hsq : (wP l ^ 2).natDegree = 2 ^ (l + 1) := by rw [natDegree_pow, hd, pow_succ, mul_comm]
    have hlt : (wP l).natDegree < (wP l ^ 2).natDegree := by
      rw [hsq, hd, pow_succ]; have := Nat.one_le_two_pow (n := l); omega
    refine ⟨?_, ?_⟩
    · rw [wP_succ]
      exact (hm.pow 2).add_of_left (degree_lt_degree hlt)
    · rw [wP_succ, natDegree_add_eq_left_of_natDegree_lt hlt, hsq]

/-- **`w_l` is monic.** -/
theorem wP_monic (l : ℕ) : (wP l).Monic := (wP_monic_natDegree l).1

/-- **`w_l` has degree `2^l`.** -/
theorem wP_natDegree (l : ℕ) : (wP l).natDegree = 2 ^ l := (wP_monic_natDegree l).2

/-- **`w_l(t) = s^l(t)`.** -/
theorem wP_eval (t : E) (l : ℕ) : (wP l).eval t = (fun x : E ↦ x * x + x)^[l] t := by
  induction l with
  | zero => simp [wP_zero]
  | succ l ih => rw [wP_succ, eval_add, eval_pow, ih, Function.iterate_succ_apply', pow_two]

/-- **`w_l(t)` is the digit `l`**, `l < n`. -/
theorem wP_eval_digits (t : E) {l n : ℕ} (hl : l < n) : (wP l).eval t = (digits t n).getD l 0 := by
  rw [wP_eval, digits_getD t hl]

/-- `w_l(ω_i) = ω_{i >> l}`, `i < 2^32`. -/
theorem wP_eval_pointE (l : ℕ) {i : ℕ} (hi : i < 2 ^ 32) : (wP l).eval (pointE i) = pointE (i >>> l) := by
  rw [wP_eval, sq_iterate_pointE l hi]

/-! ### Products of linear factors at the domain's points -/

/-- `Π_{j ∈ S} (X − ω_j)`. -/
noncomputable def linProd (S : Finset ℕ) : E[X] := ∏ j ∈ S, (X - C (pointE j))

theorem linProd_monic (S : Finset ℕ) : (linProd S).Monic :=
  monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C (pointE j)

theorem linProd_natDegree (S : Finset ℕ) : (linProd S).natDegree = S.card := by
  rw [linProd, natDegree_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C (pointE j)]
  simp

/-- **`Π_{j ∈ S} (X − ω_j)` vanishes at `ω_i` exactly for `i ∈ S`** (indices below `2^32`). -/
theorem linProd_eval_pointE_eq_zero_iff {S : Finset ℕ} (hS : ∀ j ∈ S, j < 2 ^ 32) {i : ℕ}
    (hi : i < 2 ^ 32) : (linProd S).eval (pointE i) = 0 ↔ i ∈ S := by
  rw [linProd, eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [eval_sub, eval_X, eval_C, sub_eq_zero, pointE_eq_iff hi (hS j hj)] at h
    exact h ▸ hj
  · intro h
    exact ⟨i, h, by rw [eval_sub, eval_X, eval_C, sub_self]⟩

/-- **A monic polynomial of degree `|S|` vanishing at `{ω_j : j ∈ S}` is `Π_{j ∈ S} (X − ω_j)`.** -/
theorem eq_linProd {p : E[X]} {S : Finset ℕ} (hp : p.Monic) (hdeg : p.natDegree = S.card)
    (hS : ∀ j ∈ S, j < 2 ^ 32) (hroot : ∀ j ∈ S, p.eval (pointE j) = 0) : p = linProd S := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hmap : linProd S = ((S.val.map pointE).map fun a ↦ X - C a).prod := by
    rw [linProd, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hnd : (S.val.map pointE).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy h ↦ pointE_injOn (hS x hx) (hS y hy) h) S.nodup
  have hle : S.val.map pointE ≤ p.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp ha
    exact (mem_roots hp0).mpr (hroot j hj)
  have hdvd : linProd S ∣ p := by
    rw [hmap]
    exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hp0 _).mpr hle
  exact eq_of_monic_of_dvd_of_natDegree_le (linProd_monic S) hp hdvd
    (by rw [hdeg, linProd_natDegree])

theorem linProd_dvd {S T : Finset ℕ} (h : S ⊆ T) : linProd S ∣ linProd T :=
  Finset.prod_dvd_prod_of_subset S T _ h

/-- `Π_T = Π_S · Π_{T \ S}`, so `Π_T /ₘ Π_S = Π_{T \ S}`. -/
theorem linProd_divByMonic {S T : Finset ℕ} (h : S ⊆ T) : linProd T /ₘ linProd S = linProd (T \ S) := by
  rw [show linProd T = linProd S * linProd (T \ S) by
      rw [linProd, linProd, linProd, mul_comm, Finset.prod_sdiff h],
    mul_divByMonic_cancel_left _ (linProd_monic S)]

/-! ### `w_l` is the subspace polynomial of `V_l` -/

/-- **`w_l = Π_{i < 2^l} (X − ω_i)`**, `l ≤ 32`. -/
theorem wP_eq_linProd {l : ℕ} (hl : l ≤ 32) : wP l = linProd (range (2 ^ l)) := by
  have hb : ∀ j ∈ range (2 ^ l), j < 2 ^ 32 := fun j hj ↦
    lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.pow_le_pow_right (by norm_num) hl)
  refine eq_linProd (wP_monic l) (by rw [wP_natDegree, Finset.card_range]) hb fun j hj ↦ ?_
  rw [wP_eval_pointE l (hb j hj), Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Finset.mem_range.mp hj),
    pointE_zero]

/-- **`w_l = Π_{i < 2^l} (X − C ω_i)`**, `l ≤ 32`. -/
theorem wP_eq_prod {l : ℕ} (hl : l ≤ 32) : wP l = ∏ i ∈ range (2 ^ l), (X - C (pointE i)) :=
  wP_eq_linProd hl

/-- **The roots of `w_l` are exactly `V_l`**, `l ≤ 32`. -/
theorem wP_eval_eq_zero_iff {l : ℕ} (hl : l ≤ 32) (t : E) :
    (wP l).eval t = 0 ↔ ∃ i < 2 ^ l, t = pointE i := by
  rw [wP_eq_prod hl, eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at h
    exact ⟨i, Finset.mem_range.mp hi, h⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mpr hi, by rw [eval_sub, eval_X, eval_C, sub_self]⟩

/-- **`w_{l+k} = w_l · Π_{j=l}^{l+k−1} (w_j + 1)`.** -/
theorem wP_eq_mul (l k : ℕ) : wP (l + k) = wP l * ∏ j ∈ Ico l (l + k), (wP j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, wP_succ, Finset.prod_Ico_succ_top (by omega), ← mul_assoc, ← ih]
    ring

/-- **`w_l ∣ w_m`**, `l ≤ m`. -/
theorem wP_dvd {l m : ℕ} (h : l ≤ m) : wP l ∣ wP m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [wP_eq_mul]
  exact dvd_mul_right _ _

/-- **`w_m /ₘ w_l` at `t` is `vanishingRatio`** of `t`'s digits, `l ≤ m ≤ n`. -/
theorem wP_divByMonic_eval {l m n : ℕ} (h : l ≤ m) (hn : m ≤ n) (t : E) :
    (wP m /ₘ wP l).eval t = vanishingRatio (digits t n) l m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [wP_eq_mul, mul_divByMonic_cancel_left _ (wP_monic l), eval_prod, vanishingRatio_digits t hn]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [eval_add, eval_one, wP_eval]

end UniComplete.Domain

/-- info: 'UniComplete.Domain.wP_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.wP_monic

/-- info: 'UniComplete.Domain.wP_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.wP_natDegree

/-- info: 'UniComplete.Domain.wP_eval_digits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.wP_eval_digits

/-- info: 'UniComplete.Domain.wP_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.wP_eq_prod

/-- info: 'UniComplete.Domain.wP_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.wP_eval_eq_zero_iff

/-- info: 'UniComplete.Domain.wP_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.wP_dvd

/-- info: 'UniComplete.Domain.wP_divByMonic_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.wP_divByMonic_eval
