-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.DomainBasis

/-!
# The digits `w_l(t)` (milestone 4, the domain facts)

`UniStatement.digits t n` (`digits`, SPEC.md §2) is the list `w_0(t), …, w_{n−1}(t)`, `w_0 = t`,
`w_{l+1} = w_l² + w_l`:

* `digits_eq`: it is `(List.range n).map (s^[·] t)`, `s(x) = x·x + x`, for every `n` (so its length is `n`);
* `digits_getD`: `(digits t n).getD l 0 = s^[l] t` for `l < n`; at a point of the domain,
  `(digits (pointE i) n).getD l 0 = pointE (i >>> l)` (`digits_pointE`, `i < 2^32`, `Heap.sq_iterate_omega`);
* `vanishingRatio_digits`: `vanishingRatio (digits t n) r m = Π_{j=r}^{m−1} (w_j(t) + 1)` for `m ≤ n`.
-/

namespace UniComplete.Domain

open LeanVM.Parameters UniStatement Finset

/-- The step of `digits`' fold. -/
theorem digits_fold (t : E) (m : ℕ) :
    ((List.range m).foldl (fun (ws : Array E) _ ↦
      let w := ws.back?.getD t
      ws.push (w * w + w)) #[t]).toList =
      (List.range (m + 1)).map fun l ↦ (fun x : E ↦ x * x + x)^[l] t := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hA : (List.range m).foldl (fun (ws : Array E) _ ↦
      let w := ws.back?.getD t
      ws.push (w * w + w)) #[t] = A at ih
    have hback : A.back?.getD t = (fun x : E ↦ x * x + x)^[m] t := by
      rw [← Array.getLast?_toList, ih, List.getLast?_eq_getElem?]
      simp only [List.length_map, List.length_range, Nat.add_sub_cancel, List.getElem?_map,
        List.getElem?_range (Nat.lt_succ_self m), Option.map_some, Option.getD_some]
    simp only [Array.toList_push, hback, ih]
    rw [List.range_succ (n := m + 1), List.map_append, List.map_singleton,
      Function.iterate_succ_apply' (fun x : E ↦ x * x + x) (m)]

/-- **The digits**: `digits t n = [w_0(t), …, w_{n−1}(t)]`, `w_l = s^l`. -/
theorem digits_eq (t : E) (n : ℕ) :
    digits t n = (List.range n).map fun l ↦ (fun x : E ↦ x * x + x)^[l] t := by
  unfold digits
  rw [digits_fold]
  rcases n with _ | n
  · rfl
  · rw [Nat.add_sub_cancel, List.take_of_length_le (by simp)]

theorem length_digits (t : E) (n : ℕ) : (digits t n).length = n := by
  rw [digits_eq, List.length_map, List.length_range]

/-- **Digit `l` of `t`** is `s^l(t)`, `l < n`. -/
theorem digits_getD (t : E) {l n : ℕ} (hl : l < n) :
    (digits t n).getD l 0 = (fun x : E ↦ x * x + x)^[l] t := by
  rw [digits_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
  rfl

/-- **The digits at a point of the domain**: `w_l(ω_i) = ω_{i >> l}`, `i < 2^32`. -/
theorem digits_pointE {i : ℕ} (hi : i < 2 ^ 32) {l n : ℕ} (hl : l < n) :
    (digits (pointE i) n).getD l 0 = pointE (i >>> l) := by
  rw [digits_getD _ hl, sq_iterate_pointE l hi]

/-- A product fold is the product of the mapped list. -/
theorem foldl_mul_eq_prod {M : Type*} [CommMonoid M] (h : ℕ → M) (L : List ℕ) (a : M) :
    L.foldl (fun acc j ↦ acc * h j) a = a * (L.map h).prod := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- A list product over `range` is a `Finset` product. -/
theorem prod_map_range {M : Type*} [CommMonoid M] (h : ℕ → M) (n : ℕ) :
    ((List.range n).map h).prod = ∏ k ∈ range n, h k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

/-- A list product over `range'` is a product over `Ico`. -/
theorem prod_map_range' {M : Type*} [CommMonoid M] (h : ℕ → M) (r n : ℕ) :
    ((List.range' r n).map h).prod = ∏ j ∈ Ico r (r + n), h j := by
  rw [List.range'_eq_map_range, List.map_map, prod_map_range, Finset.prod_Ico_eq_prod_range,
    Nat.add_sub_cancel_left]
  rfl

/-- **The ratio of digits' polynomials, at the digits**: `vanishingRatio (digits t n) r m =
Π_{j=r}^{m−1} (w_j(t) + 1)`, `m ≤ n` (`w_m / w_r`). -/
theorem vanishingRatio_digits (t : E) {r m n : ℕ} (hm : m ≤ n) :
    vanishingRatio (digits t n) r m = ∏ j ∈ Ico r m, ((fun x : E ↦ x * x + x)^[j] t + 1) := by
  unfold vanishingRatio
  rw [foldl_mul_eq_prod, one_mul]
  rcases Nat.lt_or_ge m r with hmr | hmr
  · rw [Nat.sub_eq_zero_of_le hmr.le, Finset.Ico_eq_empty_of_le hmr.le]
    simp
  · rw [prod_map_range', Nat.add_sub_cancel' hmr]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_Ico] at hj
    rw [digits_getD t (by omega)]

end UniComplete.Domain

/-- info: 'UniComplete.Domain.digits_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.digits_getD

/-- info: 'UniComplete.Domain.digits_pointE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.digits_pointE

/-- info: 'UniComplete.Domain.vanishingRatio_digits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.vanishingRatio_digits
