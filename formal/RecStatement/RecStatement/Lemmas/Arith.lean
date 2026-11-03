-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Core
import RecPiop.Rounds

/-!
# The verifier's arithmetic, step by step

What each step of `CoreSpec.run` computes, over any field:

* `fraction xs` is `(Σ_{i} Π_{j ≠ i} x_j, Π x_j)`: `N/D = Σ 1/x_i` when no `x_i` vanishes (`fraction_snd`,
  `fraction_fst`, `fraction_div`);
* the digits are `w_l = s^l(t)` (`digitsList_getD`), `sqIter x i = x^(2^i)` (`sqIter_eq`), the powers of `γ`
  (`powersList_getD`), the digits' inverses down from `1/w_{m+2}` are `1/w_l` (`wInvsList_getD`);
* **`W`'s fold** is `RecPiop.foldAt` (`foldW_eq_foldAt`): `Σ_k eq(ρ⃗, k) a_k` at `ρ⃗ = (ρ, ρ², …)`;
* **the row's cells by the siblings' fold** are `RecPiop.cellsOf` (`cellsList_eq_cellsOf`, `PI2.md` §9 lever 3a): the odd
  child, the even one plus the difference, is the parent folded at `z + 1 = w_l + ω_{2k+1}`, which needs
  `ω_{2k+1} = ω_{2k} + 1` (`β_0 = 1`: `Heap.omega_xor_one`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop

variable {F : Type} [Field F]

/-! ## Fractions -/

theorem foldl_fraction_snd (ys : List F) (nd : F × F) :
    (ys.foldl (fun nd y ↦ (nd.1 * y + nd.2, nd.2 * y)) nd).2 = nd.2 * ys.prod := by
  induction ys generalizing nd with
  | nil => simp
  | cons y ys ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

theorem foldl_fraction_fst (ys : List F) (nd : F × F) (hd : nd.2 ≠ 0) (hy : ∀ y ∈ ys, y ≠ 0) :
    (ys.foldl (fun nd y ↦ (nd.1 * y + nd.2, nd.2 * y)) nd).1 =
      nd.2 * ys.prod * (nd.1 / nd.2 + (ys.map (·⁻¹)).sum) := by
  induction ys generalizing nd with
  | nil => simp only [List.foldl_nil, List.prod_nil, List.map_nil, List.sum_nil, mul_one, add_zero]; field_simp
  | cons y ys ih =>
    have hy0 : y ≠ 0 := hy y List.mem_cons_self
    rw [List.foldl_cons, ih _ (mul_ne_zero hd hy0) fun z hz ↦ hy z (List.mem_cons_of_mem _ hz)]
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    field_simp
    ring

/-- A fraction's denominator is the product. -/
theorem fraction_snd (xs : List F) (h : xs ≠ []) : (fraction xs).2 = xs.prod := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs => rw [fraction, foldl_fraction_snd, List.prod_cons]

/-- A fraction's numerator is the product times the sum of the inverses. -/
theorem fraction_fst (xs : List F) (h : xs ≠ []) (hx : ∀ x ∈ xs, x ≠ 0) :
    (fraction xs).1 = xs.prod * (xs.map (·⁻¹)).sum := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs =>
    have hx0 : x ≠ 0 := hx x List.mem_cons_self
    rw [fraction, foldl_fraction_fst _ _ hx0 fun z hz ↦ hx z (List.mem_cons_of_mem _ hz)]
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    field_simp

/-- **`N/D = Σ 1/x_i`.** -/
theorem fraction_div (xs : List F) (h : xs ≠ []) (hx : ∀ x ∈ xs, x ≠ 0) :
    (fraction xs).1 / (fraction xs).2 = (xs.map (·⁻¹)).sum := by
  have hp : xs.prod ≠ 0 := List.prod_ne_zero (fun h0 ↦ hx 0 h0 rfl)
  rw [fraction_fst xs h hx, fraction_snd xs h]
  field_simp

theorem fraction_singleton (x : F) : fraction [x] = (1, x) := rfl

/-! ## Digits, squares, powers -/

theorem digitsList_getD (t : F) {count l : ℕ} (hl : l < count) :
    (digitsList t count).getD l 0 = QuotientSecurity.sq^[l] t := by
  simp [digitsList, List.getD_eq_getElem?_getD, hl]

theorem digitsList_length (t : F) (count : ℕ) : (digitsList t count).length = count := by
  simp [digitsList]

theorem sqIter_eq (x : F) (i : ℕ) : sqIter x i = x ^ (2 ^ i) := by
  induction i generalizing x with
  | zero => simp [sqIter]
  | succ i ih =>
    have e : sqIter x (i + 1) = sqIter (x * x) i := Function.iterate_succ_apply _ _ _
    rw [e, ih, ← pow_two, ← pow_mul, pow_succ, mul_comm]

theorem powersList_getD (γ : F) {n k : ℕ} (hk : k < n) : (powersList γ n).getD k 0 = γ ^ k := by
  simp [powersList, List.getD_eq_getElem?_getD, hk]

/-- `sq` vanishes at zero. -/
theorem sq_iterate_zero (k : ℕ) : QuotientSecurity.sq^[k] (0 : F) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, show QuotientSecurity.sq (0 : F) = 0 by
      simp [QuotientSecurity.sq], ih]

/-- A digit is nonzero below a nonzero digit: `w_{l+1} = w_l (1 + w_l)`. -/
theorem digit_ne_zero_of_le {t : F} {l L : ℕ} (hl : l ≤ L) (h : QuotientSecurity.sq^[L] t ≠ 0) :
    QuotientSecurity.sq^[l] t ≠ 0 := by
  intro h0
  apply h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, h0,
    sq_iterate_zero]

/-! ## The digits' inverses -/

/-- The fold that prepends `(1 + w_l) · head`, from `l = j − 1` down to `0`. -/
theorem foldl_wInvs (w : List F) (g : ℕ → F) :
    ∀ (j : ℕ) (acc : List F), (∀ l < j, (1 + w.getD l 0) * g (l + 1) = g l) → acc.headD 0 = g j →
      (List.range j).reverse.foldl (fun acc l ↦ ((1 + w.getD l 0) * acc.headD 0) :: acc) acc =
        (List.range j).map g ++ acc
  | 0, acc, _, _ => by simp
  | j + 1, acc, hg, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons,
      foldl_wInvs w g j _ (fun l hl ↦ hg l (by omega)) (by rw [List.headD_cons, h, hg j (by omega)]), h,
      hg j (by omega), List.map_append, List.map_singleton, List.append_assoc, List.singleton_append]

/-- `w_{l+1} = w_l (1 + w_l)`. -/
theorem sq_eq_mul (x : F) : QuotientSecurity.sq x = x * (1 + x) := by
  unfold QuotientSecurity.sq; ring

/-- **The digits' inverses**: down from `1/w_{top}`, `1/w_l = (1 + w_l)/w_{l+1}`. -/
theorem wInvsList_getD (t : F) {top : ℕ} (w : List F) (hw : ∀ l ≤ top, w.getD l 0 = QuotientSecurity.sq^[l] t)
    (htop : QuotientSecurity.sq^[top] t ≠ 0) {l : ℕ} (hl : l ≤ top) :
    (wInvsList w top (w.getD top 0)⁻¹).getD l 0 = (w.getD l 0)⁻¹ := by
  have hg : ∀ l < top, (1 + w.getD l 0) * (w.getD (l + 1) 0)⁻¹ = (w.getD l 0)⁻¹ := by
    intro l hl'
    rw [hw l hl'.le, hw (l + 1) hl', Function.iterate_succ_apply', sq_eq_mul]
    have h1 : QuotientSecurity.sq^[l] t * (1 + QuotientSecurity.sq^[l] t) ≠ 0 := by
      have h := digit_ne_zero_of_le (l := l + 1) (Nat.succ_le_of_lt hl') htop
      rwa [Function.iterate_succ_apply', sq_eq_mul] at h
    have h2 : 1 + QuotientSecurity.sq^[l] t ≠ 0 := right_ne_zero_of_mul h1
    rw [mul_inv, ← mul_assoc, mul_comm (1 + _), mul_assoc, mul_inv_cancel₀ h2, mul_one]
  have e := foldl_wInvs w (fun l ↦ (w.getD l 0)⁻¹) top [(w.getD top 0)⁻¹] hg rfl
  unfold wInvsList
  rw [e]
  rcases Nat.lt_or_ge l top with hlt | hge
  · rw [List.getD_append _ _ _ _ (by simpa using hlt)]
    simp [List.getD_eq_getElem?_getD, hlt]
  · have : l = top := by omega
    subst this
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

/-! ## `W`'s fold -/

section Folds

variable [CharP F 2] [DecidableEq F]

theorem eqPow_succ_low (r : ℕ) (ρ : F) {k : ℕ} (hk : k < 2 ^ r) :
    eqPow (r + 1) ρ k = eqPow r ρ k * (1 + ρ ^ (2 ^ r)) := by
  unfold eqPow
  rw [Finset.prod_range_succ, Nat.testBit_eq_false_of_lt hk]
  simp

theorem eqPow_succ_high (r : ℕ) (ρ : F) {k : ℕ} (hk : k < 2 ^ r) :
    eqPow (r + 1) ρ (2 ^ r + k) = eqPow r ρ k * ρ ^ (2 ^ r) := by
  unfold eqPow
  rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hk]
  simp only [Bool.not_false, ite_true]
  congr 1
  refine Finset.prod_congr rfl fun l hl ↦ ?_
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hl)]

/-- One level of `W`'s fold. -/
def foldWLevel (rhos : List F) (cur : List F) (l : ℕ) : List F :=
  (List.range (2 ^ l)).map fun j ↦ cur.getD j 0 + rhos.getD l 0 * (cur.getD j 0 + cur.getD (j + 2 ^ l) 0)

theorem foldW_succ (rhos : List F) (r : ℕ) (a : List F) :
    foldW rhos (r + 1) a = foldW rhos r (foldWLevel rhos a r) := by
  unfold foldW
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons]
  rfl

/-- **`W`'s fold is `foldAt`**: `Σ_k eq(ρ⃗, k) a_k` at `ρ⃗ = (ρ, ρ², ρ⁴, …)`. -/
theorem foldW_eq_foldAt (ρ : F) (rhos : List F) :
    ∀ (r : ℕ) (a : List F), (∀ l < r, rhos.getD l 0 = ρ ^ (2 ^ l)) →
      foldW rhos r a = foldAt r (fun k ↦ a.getD k 0) ρ
  | 0, a, _ => by simp [foldW, foldAt, eqPow]
  | r + 1, a, h => by
    rw [foldW_succ, foldW_eq_foldAt ρ rhos r _ fun l hl ↦ h l (by omega)]
    unfold foldAt
    rw [show 2 ^ (r + 1) = 2 ^ r + 2 ^ r by ring, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    rw [eqPow_succ_low r ρ hk', eqPow_succ_high r ρ hk', ← h r (by omega)]
    simp only [foldWLevel, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk',
      Option.map_some, Option.getD_some, Nat.add_comm (2 ^ r) k]
    ring

/-! ## The row's cells -/

/-- The levels `r − 1, …, 0` of the row's fold, from a layer. -/
def foldFrom (ω : ℕ → F) (w : List F) (L : List (List F)) (r : ℕ) : List (List F) :=
  (List.range r).reverse.foldl (fun layer l ↦ foldLevel ω w l layer) L

theorem foldFrom_succ (ω : ℕ → F) (w : List F) (L : List (List F)) (r : ℕ) :
    foldFrom ω w L (r + 1) = foldFrom ω w (foldLevel ω w r L) r := by
  unfold foldFrom
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons]

theorem flatMap_pair_length {α : Type} (A B : ℕ → α) :
    ∀ n, ((List.range n).flatMap fun k ↦ [A k, B k]).length = 2 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_pair_length A B n]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil]
    ring

theorem flatMap_pair_getD {α : Type} (A B : ℕ → α) (d : α) :
    ∀ n k, k < n → ((List.range n).flatMap fun k ↦ [A k, B k]).getD (2 * k) d = A k ∧
      ((List.range n).flatMap fun k ↦ [A k, B k]).getD (2 * k + 1) d = B k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge k n with hk | hk
    · have hl := flatMap_pair_length A B n
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact flatMap_pair_getD A B d n k hk
    · have : k = n := by omega
      subst this
      have hl := flatMap_pair_length A B k
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
      simp

theorem foldLevel_length (ω : ℕ → F) (w : List F) (l : ℕ) (layer : List (List F)) :
    (foldLevel ω w l layer).length = 2 * layer.length := flatMap_pair_length _ _ _

theorem foldFrom_length (ω : ℕ → F) (w : List F) :
    ∀ (r : ℕ) (L : List (List F)), (foldFrom ω w L r).length = L.length * 2 ^ r
  | 0, L => by simp [foldFrom]
  | r + 1, L => by rw [foldFrom_succ, foldFrom_length ω w r, foldLevel_length, pow_succ]; ring

/-- A child of the fold: the parent at `z = w_l + ω(2k)` (even) or `z + 1` (odd). -/
theorem foldLevel_getD (ω : ℕ → F) (w : List F) (l : ℕ) (layer : List (List F)) {k : ℕ} (hk : k < layer.length)
    {j : ℕ} (hj : j < 2 ^ l) :
    ((foldLevel ω w l layer).getD (2 * k) []).getD j 0 = (layer.getD k []).getD j 0 + (w.getD l 0 + ω (2 * k)) *
        ((layer.getD k []).getD j 0 + (layer.getD k []).getD (j + 2 ^ l) 0) ∧
      ((foldLevel ω w l layer).getD (2 * k + 1) []).getD j 0 = (layer.getD k []).getD j 0 +
        (w.getD l 0 + ω (2 * k) + 1) * ((layer.getD k []).getD j 0 + (layer.getD k []).getD (j + 2 ^ l) 0) := by
  obtain ⟨h0, h1⟩ := flatMap_pair_getD _ _ [] layer.length k hk
  unfold foldLevel
  refine ⟨?_, ?_⟩
  · rw [h0]
    simp [List.getD_eq_getElem?_getD, hj]
  · rw [h1]
    simp [List.getD_eq_getElem?_getD, hj]
    ring

/-- **The siblings' fold, from any layer**: after the levels `r − 1, …, 0`, child `q`'s cell is
`Σ_h p_h Π_{i<r} (z_i or 1 + z_i)`, `z_i = w_i + ω(q >> i)`, `p` its ancestor `q >> r`. -/
theorem foldFrom_getD (ω : ℕ → F) (hω : ∀ k, ω (2 * k + 1) = ω (2 * k) + 1) (w : List F) :
    ∀ (r : ℕ) (L : List (List F)) (q : ℕ), q < L.length * 2 ^ r →
      ((foldFrom ω w L r).getD q []).getD 0 0 =
        ∑ h ∈ range (2 ^ r), (L.getD (q >>> r) []).getD h 0 *
          ∏ i ∈ range r, (if h.testBit i then w.getD i 0 + ω (q >>> i) else 1 + (w.getD i 0 + ω (q >>> i)))
  | 0, L, q, _ => by simp [foldFrom]
  | r + 1, L, q, hq => by
    have e : (foldLevel ω w r L).length * 2 ^ r = L.length * 2 ^ (r + 1) := by
      rw [foldLevel_length, pow_succ]; ring
    rw [foldFrom_succ, foldFrom_getD ω hω w r _ q (by rw [e]; exact hq)]
    have hQ : q >>> (r + 1) = (q >>> r) / 2 := by
      simp only [Nat.shiftRight_eq_div_pow, pow_succ, Nat.div_div_eq_div_mul]
    obtain ⟨k, b, hb, hQk, hk1⟩ : ∃ k b, b < 2 ∧ q >>> r = 2 * k + b ∧ q >>> (r + 1) = k :=
      ⟨q >>> (r + 1), (q >>> r) % 2, Nat.mod_lt _ (by norm_num), by rw [hQ]; omega, rfl⟩
    have hk : k < L.length := by
      rw [← hk1, Nat.shiftRight_eq_div_pow]
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr hq
    have hchild : ∀ j < 2 ^ r, ((foldLevel ω w r L).getD (q >>> r) []).getD j 0 =
        (L.getD k []).getD j 0 + (w.getD r 0 + ω (q >>> r)) *
          ((L.getD k []).getD j 0 + (L.getD k []).getD (j + 2 ^ r) 0) := by
      intro j hj
      obtain ⟨h0, h1⟩ := foldLevel_getD ω w r L hk hj
      rw [hQk]
      rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
      · rw [Nat.add_zero, h0]
      · rw [h1, hω, add_assoc]
    rw [hk1, show 2 ^ (r + 1) = 2 ^ r + 2 ^ r by ring, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h hh ↦ ?_
    have hh' := Finset.mem_range.mp hh
    have hprod : ∏ i ∈ range r, (if (2 ^ r + h).testBit i then w.getD i 0 + ω (q >>> i)
        else 1 + (w.getD i 0 + ω (q >>> i))) =
        ∏ i ∈ range r, (if h.testBit i then w.getD i 0 + ω (q >>> i) else 1 + (w.getD i 0 + ω (q >>> i))) :=
      Finset.prod_congr rfl fun i hi ↦ by rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hi)]
    rw [hchild h hh', Finset.prod_range_succ, Finset.prod_range_succ, hprod, Nat.testBit_eq_false_of_lt hh',
      Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hh', Nat.add_comm (2 ^ r) h]
    simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
    ring

theorem getD_map_getD (L : List (List F)) (x : ℕ) : (L.map (·.getD 0 0)).getD x 0 = (L.getD x []).getD 0 0 := by
  rcases Nat.lt_or_ge x L.length with h | h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- **The row's cells by the siblings' fold are `cellsOf`** (`PI2.md` §9 lever 3a): `v_x = Σ_k a_k eq(k, z⃗)`,
`z_l = w_l(t) + ω(x >> l)`. -/
theorem cellsList_eq_cellsOf (ω : ℕ → F) (hω : ∀ k, ω (2 * k + 1) = ω (2 * k) + 1) (t : F) {r : ℕ} (w : List F)
    (hw : ∀ l < r, w.getD l 0 = QuotientSecurity.sq^[l] t) (a : List F) {x : ℕ} (hx : x < 2 ^ r) :
    (cellsList ω w r a).getD x 0 = cellsOf r ω (fun k ↦ a.getD k 0) t x := by
  have e : cellsList ω w r a = (foldFrom ω w [a] r).map (·.getD 0 0) := rfl
  rw [e, getD_map_getD, foldFrom_getD ω hω w r [a] x (by simpa using hx)]
  have hx0 : x >>> r = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hx
  rw [hx0]
  unfold cellsOf
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [List.getD_cons_zero]
  congr 1
  refine Finset.prod_congr rfl fun l hl ↦ ?_
  rw [hw l (Finset.mem_range.mp hl)]

end Folds

end RecStatement
