-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The closed form is
-- `crates/leanvm_rec/src/pi2/verifier.rs`'s (`subspace_coefficients`, `zero_coset`, the public side's coset,
-- `PI2.md` §9 lever 3c; its unit test `the_zero_coset_sum_is_its_closed_form`).
import RecStatement.Lemmas.Subspace

/-!
# The zero coset's closed form

`PI2.md` §9 lever 3c: the zero checks' public terms have the tags of an aligned coset `c + V_k`, and their sum
`Σ_{u ∈ V_k} 1/(Y + βu)`, `Y = α + β ω_c`, is computed as `β^(2^k − 1) / F(Y)` with
`F(Y) = Σ_{i ≤ k} a_i Y^(2^i) β^(2^k − 2^i)`, `a_i` the coefficients of `V_k`'s subspace polynomial
`w_k = s^k = Σ a_i X^(2^i)` (`subspaceCoeffsF`). On a Cantor basis:

* `w_k = Π_{u<2^k} (X + ω_u)` (`prod_omega_eq_digitPoly`, `RecPiop.Circuit.zV_eq_digitPoly`) and its
  coefficients are `subspaceCoeffsF k` (`digitPoly_eq_coeffs`), the first and the last `1`;
* homogenised, `Π_u (X + β ω_u) = Σ_i a_i β^(2^k − 2^i) X^(2^i)` (`prod_scaled_poly`), so `F(Y)` is the product
  of the coset's denominators;
* its derivative is `a_0 β^(2^k − 1) = β^(2^k − 1)` (characteristic two), and the logarithmic derivative of a
  product is the sum of the inverses: **`coset_closed`**.
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Polynomial Finset QuotientSecurity RecPiop

variable {F : Type} [Field F] [CharP F 2]

/-! ## The coefficients of `w_k` -/

theorem subspaceStep_getD (a : List F) (i : ℕ) :
    (subspaceStep a).getD i 0 =
      (if i = 0 then 0 else a.getD (i - 1) 0 * a.getD (i - 1) 0) + a.getD i 0 := by
  by_cases hi : i < a.length + 1
  · unfold subspaceStep
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  · have h1 : a.getD (i - 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
    have h2 : a.getD i 0 = 0 := List.getD_eq_default _ _ (by omega)
    rw [h1, h2, List.getD_eq_default (subspaceStep a) (0 : F) (by simp [subspaceStep]; omega)]
    simp

theorem subspaceCoeffsF_succ (k : ℕ) :
    (subspaceCoeffsF (k + 1) : List F) = subspaceStep (subspaceCoeffsF k) := by
  unfold subspaceCoeffsF
  rw [List.range_succ, List.foldl_append]
  rfl

theorem subspaceCoeffsF_length (k : ℕ) : (subspaceCoeffsF k : List F).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [subspaceCoeffsF_succ, subspaceStep, List.length_map, List.length_range, ih]

theorem subspaceCoeffsF_zero (k : ℕ) : (subspaceCoeffsF k : List F).getD 0 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [subspaceCoeffsF_succ, subspaceStep_getD, ite_eq_left rfl, zero_add, ih]

theorem subspaceCoeffsF_top (k : ℕ) : (subspaceCoeffsF k : List F).getD k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [subspaceCoeffsF_succ, subspaceStep_getD, ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel, ih,
      List.getD_eq_default (subspaceCoeffsF k : List F) (0 : F) (by rw [subspaceCoeffsF_length]),
      mul_one, add_zero]

/-- **`w_k = s^k = Σ_{i ≤ k} a_i X^(2^i)`**, `a = subspaceCoeffsF k`. -/
theorem digitPoly_eq_coeffs (k : ℕ) :
    (digitPoly k : F[X]) = ∑ i ∈ range (k + 1), C ((subspaceCoeffsF k : List F).getD i 0) * X ^ (2 ^ i) := by
  induction k with
  | zero => simp [digitPoly, subspaceCoeffsF]
  | succ k ih =>
    obtain ⟨a, ha⟩ : ∃ a, a = (subspaceCoeffsF k : List F) := ⟨_, rfl⟩
    rw [← ha] at ih
    have hlen : a.length = k + 1 := by rw [ha, subspaceCoeffsF_length]
    have hsq : (digitPoly k : F[X]) ^ 2 =
        ∑ i ∈ range (k + 1), C (a.getD i 0 * a.getD i 0) * X ^ (2 ^ (i + 1)) := by
      rw [ih, sum_pow_char]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow, ← C_pow, ← pow_mul, pow_succ 2 i, pow_two]
    rw [digitPoly, add_comp, X_pow_comp, X_comp, hsq, subspaceCoeffsF_succ, ← ha]
    simp only [subspaceStep_getD, C_add, add_mul, sum_add_distrib]
    rw [sum_range_succ' _ (k + 1), sum_range_succ (fun i => C (a.getD i 0) * X ^ (2 ^ i)) (k + 1), ← ih,
      List.getD_eq_default a (0 : F) (show a.length ≤ k + 1 by omega), ite_eq_left rfl]
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, C_0, zero_mul, add_zero]

/-- **`Π_{u<2^k} (X + ω_u) = w_k`** on a Cantor basis of at least `k` vectors. -/
theorem prod_omega_eq_digitPoly {n : ℕ} (B : CantorBasis F n) {k : ℕ} (hk : k ≤ n) :
    ∏ u ∈ range (2 ^ k), (X + C (Heap.omega B u)) = (digitPoly k : F[X]) := by
  classical
  exact RecPiop.Circuit.zV_eq_digitPoly
    (⟨k, 0, [], [], fun _ => 0, fun _ => 0, []⟩ : RecPiop.Circuit F) B hk

theorem sum_comp' {ι : Type} (s : Finset ι) (f : ι → F[X]) (q : F[X]) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, add_comp, ih]

/-- **Homogenised**: `Π_u (X + β ω_u) = Σ_{i ≤ k} a_i β^(2^k − 2^i) X^(2^i)`. -/
theorem prod_scaled_poly {n : ℕ} (B : CantorBasis F n) {k : ℕ} (hk : k ≤ n) (β : F) :
    ∏ u ∈ range (2 ^ k), (X + C (β * Heap.omega B u)) =
      ∑ i ∈ range (k + 1), C ((subspaceCoeffsF k : List F).getD i 0 * β ^ (2 ^ k - 2 ^ i)) * X ^ (2 ^ i) := by
  by_cases hβ : β = 0
  · subst hβ
    simp only [zero_mul, C_0, add_zero, prod_const, card_range]
    rw [sum_range_succ, subspaceCoeffsF_top, Nat.sub_self, pow_zero, mul_one, C_1, one_mul,
      sum_eq_zero fun i hi => ?_, zero_add]
    have : 0 < 2 ^ k - 2 ^ i := Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (mem_range.mp hi))
    rw [zero_pow this.ne', mul_zero, C_0, zero_mul]
  · have e1 : ∀ u, X + C (β * Heap.omega B u) = C β * (X + C (Heap.omega B u)).comp (C β⁻¹ * X) := by
      intro u
      rw [add_comp, X_comp, C_comp, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hβ, C_1, one_mul, ← C_mul]
    rw [prod_congr rfl fun u _ => e1 u, prod_mul_distrib, prod_const, card_range, ← Polynomial.prod_comp,
      prod_omega_eq_digitPoly B hk, digitPoly_eq_coeffs, sum_comp', mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hle : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by rw [mem_range] at hi; omega)
    rw [mul_comp, C_comp, X_pow_comp, mul_pow, pow_sub₀ β hβ hle, ← inv_pow]
    simp only [C_mul, C_pow]
    ring

/-- `Π_u (Y + β ω_u) = Σ_{i ≤ k} a_i β^(2^k − 2^i) Y^(2^i)`. -/
theorem prod_scaled {n : ℕ} (B : CantorBasis F n) {k : ℕ} (hk : k ≤ n) (β Y : F) :
    ∏ u ∈ range (2 ^ k), (Y + β * Heap.omega B u) =
      ∑ i ∈ range (k + 1), (subspaceCoeffsF k : List F).getD i 0 * β ^ (2 ^ k - 2 ^ i) * Y ^ (2 ^ i) := by
  have h := congrArg (eval Y) (prod_scaled_poly B hk β)
  simpa [eval_prod, eval_finsetSum] using h

/-- **Its derivative is `β^(2^k − 1)`** (characteristic two: only `X = X^(2^0)` survives). -/
theorem derivative_prod_scaled {n : ℕ} (B : CantorBasis F n) {k : ℕ} (hk : k ≤ n) (β : F) :
    derivative (∏ u ∈ range (2 ^ k), (X + C (β * Heap.omega B u))) = C (β ^ (2 ^ k - 1)) := by
  rw [prod_scaled_poly B hk, derivative_sum, sum_range_succ', sum_eq_zero fun i _ => ?_, zero_add]
  · rw [derivative_C_mul, derivative_X_pow, subspaceCoeffsF_zero, one_mul]
    simp
  · have two : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [derivative_C_mul, derivative_X_pow, Nat.cast_pow, Nat.cast_ofNat, two,
      zero_pow (Nat.succ_ne_zero i), C_0, zero_mul, mul_zero]

/-! ## The steps of `cosetSum` -/

theorem sqIter_pow (x : F) : ∀ i, sqIter x i = x ^ (2 ^ i)
  | 0 => by simp [sqIter]
  | i + 1 => by
    show (fun y : F => y * y)^[i + 1] x = _
    rw [Function.iterate_succ_apply']
    show (fun y : F => y * y)^[i] x * (fun y : F => y * y)^[i] x = _
    rw [show (fun y : F => y * y)^[i] x = x ^ (2 ^ i) from sqIter_pow x i, ← pow_add, pow_succ 2 i,
      mul_two]

/-- `bRestList β k = [β^(2^k − 2^0), …, β^(2^k − 2^(k−1)), 1]`. -/
theorem bRestList_eq (β : F) (k : ℕ) :
    bRestList β k = (List.range k).map (fun i => β ^ (2 ^ k - 2 ^ i)) ++ [1] := by
  have key : ∀ d ≤ k, List.foldr (fun i acc => (if i + 1 = k then sqIter β i else acc.headD 1 * sqIter β i) :: acc)
      [1] (List.range' (k - d) d) = (List.range' (k - d) d).map (fun i => β ^ (2 ^ k - 2 ^ i)) ++ [1] := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have e : List.range' (k - (d + 1)) (d + 1) = (k - (d + 1)) :: List.range' (k - d) d := by
        rw [List.range'_succ, show k - (d + 1) + 1 = k - d by omega]
      rw [e, List.foldr_cons, ih (by omega), List.map_cons, List.cons_append]
      congr 1
      have ha : 2 ^ (k - d) = 2 * 2 ^ (k - (d + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      have hle : 2 ^ (k - d) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [sqIter_pow]
      by_cases h0 : d = 0
      · subst h0
        rw [ite_eq_left (by omega)]
        congr 1
        rw [Nat.sub_zero] at ha
        omega
      · rw [ite_eq_right (by omega)]
        obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        rw [List.range'_succ, List.map_cons, List.cons_append, List.headD_cons, ← pow_add]
        congr 1
        omega
  unfold bRestList
  rw [List.foldl_reverse, List.range_eq_range']
  have := key k le_rfl
  rw [Nat.sub_self] at this
  exact this

theorem foldl_add_range (g : ℕ → F) (init : F) (k : ℕ) :
    (List.range k).foldl (fun f i => f + g i) init = init + ∑ i ∈ range k, g i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, sum_range_succ]; simp [add_assoc]

theorem getD_map_range_append {g : ℕ → F} {k i : ℕ} (hi : i < k) (d : F) (t : List F) :
    ((List.range k).map g ++ t).getD i d = g i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hi]), List.getElem?_map,
    List.getElem?_range hi]
  rfl

theorem cosetSum_fst (ω : ℕ → F) (α β : F) (tag k : ℕ) (a : List F) :
    (cosetSum ω α β tag k a).1 = β ^ (2 ^ k - 1) := by
  show (bRestList β k).headD 1 = _
  rw [bRestList_eq]
  rcases k with _ | k
  · simp
  · rw [List.range_succ_eq_map, List.map_cons, List.cons_append, List.headD_cons, pow_zero]

theorem cosetSum_snd (ω : ℕ → F) (α β : F) (tag k : ℕ) (a : List F) (htop : a.getD k 0 = 1) :
    (cosetSum ω α β tag k a).2 =
      ∑ i ∈ range (k + 1), a.getD i 0 * β ^ (2 ^ k - 2 ^ i) * (α + β * ω tag) ^ (2 ^ i) := by
  show (List.range k).foldl (fun f i ↦ f + a.getD i 0 * (sqIter (α + β * ω tag) i * (bRestList β k).getD i 1))
    (sqIter (α + β * ω tag) k) = _
  rw [foldl_add_range, sum_range_succ, htop, Nat.sub_self, pow_zero, sqIter_pow]
  have e : ∀ i ∈ range k, a.getD i 0 * (sqIter (α + β * ω tag) i * (bRestList β k).getD i 1) =
      a.getD i 0 * β ^ (2 ^ k - 2 ^ i) * (α + β * ω tag) ^ (2 ^ i) := by
    intro i hi
    rw [mem_range] at hi
    rw [sqIter_pow, bRestList_eq, getD_map_range_append hi]
    ring
  rw [sum_congr rfl e]
  ring

/-! ## The closed form -/

/-- **The zero coset's closed form** (`PI2.md` §9 lever 3c): `F(Y) = Π_u (Y + β ω_u)` and
`Σ_u 1/(Y + β ω_u) = β^(2^k−1)/F(Y)`, `Y = α + β ω_c`. -/
theorem coset_closed {n : ℕ} (B : CantorBasis F n) {k : ℕ} (hkn : k ≤ n) (α β : F) {tag : ℕ}
    (htag : 2 ^ k ∣ tag) :
    (cosetSum (Heap.omega B) α β tag k (subspaceCoeffsF k)).2 =
        ∏ u ∈ range (2 ^ k), (α + β * Heap.omega B (tag + u)) ∧
      ((cosetSum (Heap.omega B) α β tag k (subspaceCoeffsF k)).2 ≠ 0 →
        (cosetSum (Heap.omega B) α β tag k (subspaceCoeffsF k)).1 /
            (cosetSum (Heap.omega B) α β tag k (subspaceCoeffsF k)).2 =
          ∑ u ∈ range (2 ^ k), (α + β * Heap.omega B (tag + u))⁻¹) := by
  have hY : ∀ u ∈ range (2 ^ k), α + β * Heap.omega B (tag + u) =
      (α + β * Heap.omega B tag) + β * Heap.omega B u := by
    intro u hu
    rw [add_eq_xor_of_dvd htag (mem_range.mp hu), Heap.omega_xor]
    ring
  have h2 : (cosetSum (Heap.omega B) α β tag k (subspaceCoeffsF k)).2 =
      ∏ u ∈ range (2 ^ k), (α + β * Heap.omega B (tag + u)) := by
    rw [cosetSum_snd _ _ _ _ _ _ (subspaceCoeffsF_top k), prod_congr rfl hY, prod_scaled B hkn]
  refine ⟨h2, fun hne => ?_⟩
  have hs : ∑ u ∈ range (2 ^ k), (α + β * Heap.omega B (tag + u))⁻¹ =
      ∑ u ∈ range (2 ^ k), ((α + β * Heap.omega B tag) + β * Heap.omega B u)⁻¹ :=
    sum_congr rfl fun u hu => by rw [hY u hu]
  rw [cosetSum_fst, h2, prod_congr rfl hY, hs]
  rw [h2, prod_congr rfl hY] at hne
  generalize α + β * Heap.omega B tag = Y at hne ⊢
  -- The logarithmic derivative at `Y`.
  have hder := congrArg (eval Y) (derivative_prod_scaled B hkn β)
  rw [derivative_prod_finset, eval_C, eval_finsetSum] at hder
  simp only [derivative_X_add_C, mul_one, eval_prod, eval_add, eval_X, eval_C] at hder
  have hterm : ∀ u ∈ range (2 ^ k), ∏ v ∈ (range (2 ^ k)).erase u, (Y + β * Heap.omega B v) =
      (∏ v ∈ range (2 ^ k), (Y + β * Heap.omega B v)) * (Y + β * Heap.omega B u)⁻¹ := by
    intro u hu
    have hu0 : Y + β * Heap.omega B u ≠ 0 := (prod_ne_zero_iff.mp hne) u hu
    rw [← prod_erase_mul _ _ hu, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  rw [sum_congr rfl hterm, ← mul_sum] at hder
  rw [div_eq_iff hne, ← hder, mul_comm]
