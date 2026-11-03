-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The basis-B encoding is
-- `crates/leanvm_univariate`'s (SPEC.md §2).
import UniSound.Final

/-!
# The univariate identities' polynomials: digits, the basis `B`, claims at polynomial points

SPEC.md §2: a column of `2^r` rows is committed as its coefficients `c_x` in the basis
`B_x = Π_{l<r} (w_l if x_l else 1 + w_l)`, `w_0 = X`, `w_{l+1} = w_l² + w_l` (`digitP`), so its value at `t`
is the multilinear extension of the coefficients at the digits `(w_0(t), …, w_{r−1}(t))` — the claim the
verifier states. More generally a claim at a point whose coordinates are polynomials in `t` (the digits, the
digits of `s(t)` or `t + 1`, a heap block's mixed point, `q_flock`'s slot at `y(t)`) is the value at `t` of
the polynomial `mlP f n pt = Σ_{x<2^n} f(x) Π_l (pt_l if x_l else 1 + pt_l)` (`eval_mlP`).

Everything here is generic: no shape, no basis, no evaluation.
-/

namespace UniSound.Ids

open Polynomial Finset LeanVM.Parameters UniStatement

/-! ## Digits -/

/-- **The digit `w_l` as a polynomial**: `w_0 = X`, `w_{l+1} = w_l² + w_l`. -/
noncomputable def digitP : ℕ → Polynomial E
  | 0 => X
  | l + 1 => digitP l * digitP l + digitP l

/-- `s(x) = x² + x` on `E`, as `QuotientSecurity.sq`. -/
theorem sq_def (x : E) : QuotientSecurity.sq x = x * x + x := rfl

theorem eval_digitP (l : ℕ) (t : E) : (digitP l).eval t = QuotientSecurity.sq^[l] t := by
  induction l generalizing t with
  | zero => simp [digitP]
  | succ l ih =>
    rw [Function.iterate_succ_apply', ← ih]
    simp [digitP, sq_def]

/-- The verifier's digits are the digit polynomials' values: `(digits t n)[l] = w_l(t)`, `l < n`. -/
theorem digits_getD (t : E) (n l : ℕ) (hl : l < n) :
    (digits t n).getD l 0 = (digitP l).eval t := by
  rw [eval_digitP]
  unfold digits
  have key : ∀ (m : ℕ), ((List.range m).foldl (fun (ws : Array E) _ ↦
      let w := ws.back?.getD t
      ws.push (w * w + w)) #[t]).toList = (List.range (m + 1)).map fun k ↦ QuotientSecurity.sq^[k] t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [List.range_succ (n := m + 1), List.map_append]
      have hback : ((List.range m).foldl (fun (ws : Array E) _ ↦
          let w := ws.back?.getD t
          ws.push (w * w + w)) #[t]).back?.getD t = QuotientSecurity.sq^[m] t := by
        rw [← Array.getLast?_toList, ih, List.getLast?_map, List.getLast?_range]
        simp
      simp only [Array.toList_push, ih, hback, List.map_cons, List.map_nil]
      congr 2
      rw [Function.iterate_succ_apply']
      rfl
  rw [key, List.take_of_length_le (by simp; omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- In characteristic two `w_l' = 1`: `w_{l+1}' = 2 w_l w_l' + w_l' = w_l'`. -/
theorem derivative_digitP (l : ℕ) : derivative (digitP l) = 1 := by
  induction l with
  | zero => simp only [digitP, derivative_X]
  | succ l ih =>
    simp only [digitP, derivative_add, derivative_mul, ih, mul_one, one_mul]
    have h2 : (2 : Polynomial E) = 0 := CharTwo.two_eq_zero
    linear_combination (digitP l) * h2

theorem natDegree_digitP (l : ℕ) : (digitP l).natDegree ≤ 2 ^ l := by
  induction l with
  | zero => simp [digitP]
  | succ l ih =>
    simp only [digitP]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_mul_le).trans ?_) (ih.trans ?_))
    · rw [pow_succ]; omega
    · rw [pow_succ]; omega

/-! ## Claims at polynomial points -/

/-- The factor of a basis element on one coordinate: `p` if the bit is set, else `1 + p`. -/
noncomputable def bFac (b : Bool) (p : Polynomial E) : Polynomial E := if b then p else 1 + p

/-- **A multilinear claim at a polynomial point**: `Σ_{x<2^n} f(x) Π_{l<n} (pt_l if x_l else 1 + pt_l)`. -/
noncomputable def mlP (f : ℕ → E) (n : ℕ) (pt : ℕ → Polynomial E) : Polynomial E :=
  ∑ x ∈ range (2 ^ n), C (f x) * ∏ l ∈ range n, bFac (x.testBit l) (pt l)

theorem eval_bFac (b : Bool) (p : Polynomial E) (t : E) :
    (bFac b p).eval t = 1 + p.eval t + if b then 1 else 0 := by
  cases b
  · simp [bFac]
  · simp only [bFac, ite_true]
    have : (1 : E) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [add_right_comm, this, zero_add]

/-- **The claim's value**: `(mlP f n pt)(t) = Σ_x eq(pt(t), x) f(x)` (`cubeEq`). -/
theorem eval_mlP (f : ℕ → E) (n : ℕ) (pt : ℕ → Polynomial E) (t : E) (p : List E)
    (hp : ∀ l < n, (pt l).eval t = p.getD l 0) :
    (mlP f n pt).eval t = ∑ x ∈ range (2 ^ n), cubeEq p n x * f x := by
  unfold mlP cubeEq
  rw [eval_finsetSum]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [Polynomial.eval_mul, eval_C, eval_prod, mul_comm]
  congr 1
  refine prod_congr rfl fun l hl ↦ ?_
  rw [eval_bFac, hp l (mem_range.mp hl)]

theorem natDegree_bFac (b : Bool) (p : Polynomial E) : (bFac b p).natDegree ≤ p.natDegree := by
  cases b
  · simp only [bFac]
    exact (natDegree_add_le _ _).trans (max_le (by simp) le_rfl)
  · simp [bFac]

/-- A claim's polynomial has degree at most the sum of its coordinates'. -/
theorem natDegree_mlP_le (f : ℕ → E) (n : ℕ) (pt : ℕ → Polynomial E) :
    (mlP f n pt).natDegree ≤ ∑ l ∈ range n, (pt l).natDegree := by
  unfold mlP
  refine natDegree_sum_le_of_forall_le _ _ fun x _ ↦ ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  exact sum_le_sum fun l _ ↦ natDegree_bFac _ _

/-- The digits' sum: `Σ_{l<n} 2^l = 2^n − 1 < 2^n`. -/
theorem sum_two_pow_lt (n : ℕ) : ∑ l ∈ range n, 2 ^ l < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

/-- A claim at the digits has degree below `2^n` (the basis `B` spans the polynomials of degree
`< 2^n`). -/
theorem natDegree_mlP_digits_lt (f : ℕ → E) (n : ℕ) : (mlP f n digitP).natDegree < 2 ^ n := lt_of_le_of_lt ((natDegree_mlP_le f n digitP).trans (sum_le_sum fun l _ ↦ natDegree_digitP l))
    (sum_two_pow_lt n)

end UniSound.Ids
