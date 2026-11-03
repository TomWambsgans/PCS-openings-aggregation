-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHPoly

/-!
# The tree quotient divides exactly and fits (milestone 4, the heap's layer)

For a heap of `2^h` values `v` (`1 ≤ h ≤ 28`) whose inner nodes are the products of their children
(`v_p = v_{2p} v_{2p+1}`, `1 ≤ p < 2^(h−1)`), with `T` the polynomial of `v` on `V_h` (`T(ω_i) = v_i`):

* `treeNumerator_eq`: the prover's numerator is `w_1 (T(s(X)) + T(X) T(X + 1))` (`compSNovel`, `shiftOneNovel`
  are the compositions, `AlgHPoly`);
* `treeNumerator_eval_pointE`: it vanishes on `V_h`: at `ω_i`, `i < 2`, `w_1` does; at `i ≥ 2`,
  `s(ω_i) = ω_{i >> 1}` and `ω_i + 1 = ω_{i xor 1}` are `i`'s parent and sibling;
* **`wP_dvd_treeNumerator`**: so `w_h` divides it, and **`treeNumerator_eq_mul`**: `N = w_h · Q_tree`
  (`treeQuotient` is the exact quotient);
* **`natDegree_treeQuotient_lt`**: `deg Q_tree ≤ 2^h < 2^h + 2^0`, the sizes `[h, 0]` of its two chunks.

`wP_dvd_of_eval`: a polynomial vanishing on `V_l` (`l ≤ 32`) is a multiple of `w_l` (its roots are the
`2^l` distinct points). `getD_set!`: `Array.set!`'s entries.
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

/-- **A polynomial vanishing on `V_l` is a multiple of `w_l`** (`l ≤ 32`). -/
theorem wP_dvd_of_eval {l : ℕ} (hl : l ≤ 32) {p : E[X]} (hp : ∀ i < 2 ^ l, p.eval (pointE i) = 0) :
    wP l ∣ p := by
  by_cases hp0 : p = 0
  · rw [hp0]; exact dvd_zero _
  have hS : ∀ j ∈ range (2 ^ l), j < 2 ^ 32 := fun j hj ↦
    lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.pow_le_pow_right (by norm_num) hl)
  rw [Domain.wP_eq_linProd hl]
  have hmap : Domain.linProd (range (2 ^ l)) =
      (((range (2 ^ l)).val.map pointE).map fun a ↦ X - C a).prod := by
    rw [Domain.linProd, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hnd : ((range (2 ^ l)).val.map pointE).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy h ↦ Domain.pointE_injOn (hS x hx) (hS y hy) h) (range (2 ^ l)).nodup
  have hle : (range (2 ^ l)).val.map pointE ≤ p.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp ha
    exact (mem_roots hp0).mpr (hp j (Finset.mem_range.mp hj))
  rw [hmap]
  exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hp0 _).mpr hle

/-- `ω_i + 1 = ω_{i xor 1}`. -/
theorem pointE_one : pointE 1 = 1 := by
  rw [← Domain.omega_basisE, Heap.omega_one Domain.basisE (by norm_num)]

theorem pointE_add_one (i : ℕ) : pointE i + 1 = pointE (i ^^^ 1) := by
  rw [Domain.pointE_xor, pointE_one]

/-- `s(ω_i) = ω_{i >> 1}` (`i < 2^32`). -/
theorem pointE_s {i : ℕ} (hi : i < 2 ^ 32) : pointE i ^ 2 + pointE i = pointE (i >>> 1) := by
  rw [← Domain.wP_eval_pointE 1 hi, wP_succ, wP_zero]
  simp

theorem tp_wPoly_one : tp (wPoly 1) = X ^ 2 + X := by rw [tp_wPoly, wP_succ, wP_zero]

/-- **The tree's numerator** is `w_1 (T(s(X)) + T(X) T(X + 1))`, `T = tp (ofNovel h d)`. -/
theorem treeNumerator_eq {h : ℕ} (hh : 1 ≤ h) (d : Array E) :
    tp (treeNumerator h d) = (X ^ 2 + X) * ((tp (ofNovel h d)).comp (X ^ 2 + X) +
      tp (ofNovel h d) * (tp (ofNovel h d)).comp (X + 1)) := by
  rw [treeNumerator, tp_mul, tp_add, tp_mul, tp_wPoly_one, tp_ofNovel_compSNovel, tp_ofNovel_shiftOneNovel hh]

/-- The tree identity on the heap's values: every inner node `1 ≤ p < 2^(h−1)` is its children's product. -/
def TreeValues (h : ℕ) (v : Array E) : Prop :=
  ∀ p, 1 ≤ p → p < 2 ^ (h - 1) → v.getD p 0 = v.getD (2 * p) 0 * v.getD (2 * p + 1) 0

/-- **The tree's numerator vanishes on `V_h`.** -/
theorem treeNumerator_eval_pointE {h : ℕ} (hh : 1 ≤ h) (h28 : h ≤ 28) {v : Array E} (hv : v.size = 2 ^ h)
    (htree : TreeValues h v) {i : ℕ} (hi : i < 2 ^ h) :
    (tp (treeNumerator h (novelOfValuesE h v))).eval (pointE i) = 0 := by
  have hi32 : i < 2 ^ 32 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [treeNumerator_eq hh]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, eval_comp, Polynomial.eval_pow, eval_X,
    Polynomial.eval_one]
  rw [pointE_s hi32, pointE_add_one]
  by_cases hi2 : i < 2
  · rw [show i >>> 1 = 0 by rw [Nat.shiftRight_one]; omega, Domain.pointE_zero, zero_mul]
  · have hp1 : i >>> 1 < 2 ^ h := lt_of_le_of_lt (by rw [Nat.shiftRight_one]; omega) hi
    have hx : i ^^^ 1 < 2 ^ h := Nat.xor_lt_two_pow hi (Nat.one_lt_two_pow (by omega))
    rw [eval_ofNovel_novelOfValuesE h28 hv hp1, eval_ofNovel_novelOfValuesE h28 hv hi,
      eval_ofNovel_novelOfValuesE h28 hv hx]
    have hpar : i >>> 1 < 2 ^ (h - 1) := by
      rw [Nat.shiftRight_one]
      have : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    have ht := htree (i >>> 1) (by rw [Nat.shiftRight_one]; omega) hpar
    have hsib : v.getD i 0 * v.getD (i ^^^ 1) 0 = v.getD (2 * (i >>> 1)) 0 * v.getD (2 * (i >>> 1) + 1) 0 := by
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
      · obtain ⟨p, hp⟩ : ∃ p, i = 2 * p := ⟨i / 2, by omega⟩
        have hs : i >>> 1 = p := by rw [Nat.shiftRight_one]; omega
        have e2 : i ^^^ 1 = 2 * p + 1 := by rw [hp, Heap.two_mul_xor_one]
        rw [hs, e2, ← hp]
      · obtain ⟨p, hp⟩ : ∃ p, i = 2 * p + 1 := ⟨i / 2, by omega⟩
        have hs : i >>> 1 = p := by rw [Nat.shiftRight_one]; omega
        have e2 : i ^^^ 1 = 2 * p := by
          rw [hp, ← Heap.two_mul_xor_one, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [hs, e2, ← hp, mul_comm]
    rw [hsib, ← ht, CharTwo.add_self_eq_zero, mul_zero]

/-- **`w_h` divides the tree's numerator.** -/
theorem wP_dvd_treeNumerator {h : ℕ} (hh : 1 ≤ h) (h28 : h ≤ 28) {v : Array E} (hv : v.size = 2 ^ h)
    (htree : TreeValues h v) : wP h ∣ tp (treeNumerator h (novelOfValuesE h v)) :=
  wP_dvd_of_eval (by omega) fun _ hi ↦ treeNumerator_eval_pointE hh h28 hv htree hi

theorem tp_treeQuotient (h : ℕ) (d : Array E) :
    tp (treeQuotient h d) = tp (treeNumerator h d) /ₘ wP h := by
  rw [treeQuotient, tp_divM _ _ (by rw [tp_wPoly]; exact wP_monic h), tp_wPoly]

/-- An exact division: `p = q · (p /ₘ q)` when the monic `q` divides `p`. -/
theorem eq_mul_divByMonic_of_dvd {p q : E[X]} (hq : q.Monic) (hd : q ∣ p) : p = q * (p /ₘ q) := by
  have := modByMonic_add_div p q
  rw [(modByMonic_eq_zero_iff_dvd hq).mpr hd, zero_add] at this
  exact this.symm

/-- **The tree quotient is exact**: `N = w_h · Q_tree`. -/
theorem treeNumerator_eq_mul {h : ℕ} (hh : 1 ≤ h) (h28 : h ≤ 28) {v : Array E} (hv : v.size = 2 ^ h)
    (htree : TreeValues h v) :
    tp (treeNumerator h (novelOfValuesE h v)) = wP h * tp (treeQuotient h (novelOfValuesE h v)) := by
  rw [tp_treeQuotient]
  exact eq_mul_divByMonic_of_dvd (wP_monic h) (wP_dvd_treeNumerator hh h28 hv htree)

/-- The tree's numerator has degree at most `2^(h+1)`. -/
theorem natDegree_treeNumerator_le {h : ℕ} (hh : 1 ≤ h) (d : Array E) :
    (tp (treeNumerator h d)).natDegree ≤ 2 ^ (h + 1) := by
  have hT : (tp (ofNovel h d)).natDegree ≤ 2 ^ h - 1 := by have := natDegree_tp_ofNovel_lt h d; omega
  rw [treeNumerator_eq hh]
  set T := tp (ofNovel h d)
  have hs : (X ^ 2 + X : E[X]).natDegree = 2 := by
    rw [← tp_wPoly_one, tp_wPoly, wP_natDegree]; norm_num
  have h1 : (X + 1 : E[X]).natDegree = 1 := natDegree_X_add_C 1
  have hc1 : (T.comp (X ^ 2 + X)).natDegree ≤ 2 * (2 ^ h - 1) := by
    rw [natDegree_comp, hs]; omega
  have hc2 : (T * T.comp (X + 1)).natDegree ≤ 2 * (2 ^ h - 1) := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_comp, h1]; omega
  refine (natDegree_mul_le).trans ?_
  rw [hs]
  have := (natDegree_add_le _ _).trans (max_le hc1 hc2)
  have hp : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
  have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  omega

/-- **The tree quotient fits its two chunks** `[h, 0]`: degree `≤ 2^h`. -/
theorem natDegree_treeQuotient_lt {h : ℕ} (hh : 1 ≤ h) (d : Array E) :
    (tp (treeQuotient h d)).natDegree < ([h, 0].map (2 ^ ·)).sum := by
  rw [tp_treeQuotient, natDegree_divByMonic _ (wP_monic h), wP_natDegree]
  have := natDegree_treeNumerator_le hh d
  have hp : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero]
  omega

/-! ### `Array.set!` -/

theorem getD_set! (a : Array E) {i : ℕ} (j : ℕ) (x : E) (hi : i < a.size) :
    (a.set! i x).getD j 0 = if j = i then x else a.getD j 0 := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  by_cases hj : j = i
  · subst hj
    rw [Array.getElem?_setIfInBounds_self_of_lt hi, ite_pos_of rfl]
    rfl
  · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hj), ite_neg_of hj]

theorem getD_set!_of_le (a : Array E) {i : ℕ} (j : ℕ) (x : E) (hi : a.size ≤ i) :
    (a.set! i x).getD j 0 = a.getD j 0 := by
  rw [Array.set!_eq_setIfInBounds]
  simp [Array.setIfInBounds, show ¬ i < a.size by omega]

end UniComplete.AlgH
