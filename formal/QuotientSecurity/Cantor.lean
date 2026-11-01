-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Cantor.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Encoding

/-!
# The Cantor basis, and tables as the polynomials they hold

`S(x) = x^2 + x` is additive in characteristic 2. A Cantor basis has `beta 0 = 1` and
`S(beta (k+1)) = beta k`; the point of a cell is the sum of the basis vectors of its bits, and
its digit `k` is `S` applied `k` times. This file proves that these digits are triangular in the
bits, so the sum over the cells of a polynomial is the top entry of its table; that a table's
polynomial evaluates to the table's digit expansion; and how one more coordinate of a table
chooses between its two halves.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]

/-- `S(x) = x^2 + x`. -/
def sq (x : F) : F := x * x + x

theorem sq_add (x y : F) : sq (x + y) = sq x + sq y := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  unfold sq
  linear_combination (x * y) * two

theorem sq_zero : sq (0 : F) = 0 := by simp [sq]

theorem sq_iterate_zero (k : ℕ) : sq^[k] (0 : F) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, sq_zero, ih]

theorem sq_iterate_add (k : ℕ) (x y : F) : sq^[k] (x + y) = sq^[k] x + sq^[k] y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, sq_add, ih]

theorem sq_iterate_sum {ι : Type*} (s : Finset ι) (f : ι → F) (k : ℕ) :
    sq^[k] (∑ i ∈ s, f i) = ∑ i ∈ s, sq^[k] (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sq_iterate_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sq_iterate_add, ih]

/-- A Cantor basis of `n` vectors. A finite field has one only up to its degree, so the recurrence
is asked below `n`. -/
structure CantorBasis (F : Type*) [Field F] (n : ℕ) where
  β : ℕ → F
  zero : β 0 = 1
  succ : ∀ k, k + 1 < n → sq (β (k + 1)) = β k

variable {n : ℕ} (B : CantorBasis F n)

/-- `S` applied `k` times to a basis vector is the basis vector `k` below, or zero. -/
theorem CantorBasis.iterate (k j : ℕ) (hj : j < n) :
    sq^[k] (B.β j) = if k ≤ j then B.β (j - k) else 0 := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases j with
    | zero =>
      have : sq (B.β 0) = 0 := by rw [B.zero]; simp [sq, CharTwo.add_self_eq_zero]
      rw [this, sq_iterate_zero]
      simp
    | succ j =>
      rw [B.succ j hj, ih j (Nat.lt_of_succ_lt hj)]
      simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- The point of a cell: the sum of the basis vectors of its bits. -/
def CantorBasis.point {m : ℕ} (x : Fin m → Bool) : F := ∑ j : Fin m, if x j then B.β j else 0

/-- What the bits above `k` add to digit `k`. -/
def CantorBasis.above {m : ℕ} (k : Fin m) (x : Fin m → Bool) : F :=
  ∑ j : Fin m, if k < j ∧ x j = true then B.β (j - k) else 0

/-- **The digits of a Cantor basis are triangular**: digit `k` of a cell is its bit `k` plus a
function of its higher bits. -/
theorem CantorBasis.digit_eq {m : ℕ} (hm : m ≤ n) (k : Fin m) (x : Fin m → Bool) :
    sq^[(k : ℕ)] (B.point x) = (if x k then 1 else 0) + B.above k x := by
  unfold CantorBasis.point CantorBasis.above
  rw [sq_iterate_sum]
  have hterm : ∀ j : Fin m, sq^[(k : ℕ)] (if x j then B.β j else 0)
      = (if j = k then (if x k then 1 else 0) else 0)
        + (if k < j ∧ x j = true then B.β (j - k) else 0) := by
    intro j
    by_cases hx : x j = true
    · rw [if_pos hx, B.iterate _ _ (lt_of_lt_of_le j.2 hm)]
      rcases lt_trichotomy j k with h | h | h
      · have h1 : ¬ (k : ℕ) ≤ j := not_le.mpr h
        simp [h1, h.ne, not_lt.mpr h.le]
      · subst h
        simp [hx, B.zero]
      · have h1 : (k : ℕ) ≤ j := le_of_lt h
        simp [h1, h.ne', h, hx]
    · have hx' : x j = false := by simpa using hx
      rw [if_neg hx, sq_iterate_zero]
      by_cases hjk : j = k
      · subst hjk; simp [hx']
      · simp [hjk, hx']
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
  simp

theorem CantorBasis.above_congr {m : ℕ} (k : Fin m) (x x' : Fin m → Bool)
    (h : ∀ j, k < j → x j = x' j) : B.above k x = B.above k x' := by
  unfold CantorBasis.above
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : k < j
  · rw [h j hj]
  · simp [hj]

/-- **The claim at the point of all ones is the sum over the cells of a Cantor basis.** -/
theorem CantorBasis.sum_cells {m : ℕ} (hm : m ≤ n) (c : (Fin m → Bool) → F) :
    ∑ x : Fin m → Bool, digitsEval c (fun k => sq^[(k : ℕ)] (B.point x)) = mle c (fun _ => 1) := by
  rw [← sum_digitsEval c (fun k x => B.above k x) (fun k x x' h => B.above_congr k x x' h)]
  exact Finset.sum_congr rfl fun x _ => by
    congr 1
    funext k
    exact B.digit_eq hm k x

/-! ## The polynomial a table holds -/

/-- Digit `k` as a polynomial: `X^2 + X` composed `k` times. -/
noncomputable def digitPoly : ℕ → F[X]
  | 0 => X
  | k + 1 => (X ^ 2 + X).comp (digitPoly k)

theorem digitPoly_eval (k : ℕ) (t : F) : (digitPoly k).eval t = sq^[k] t := by
  induction k generalizing t with
  | zero => simp [digitPoly]
  | succ k ih =>
    rw [digitPoly, eval_comp, ih, Function.iterate_succ_apply']
    simp [sq, pow_two]

/-- The polynomial of a table: its entries on the products of digits. -/
noncomputable def tablePoly {m : ℕ} (c : (Fin m → Bool) → F) : F[X] :=
  ∑ b, C (c b) * ∏ k : Fin m, (if b k then digitPoly (k : ℕ) else 1)

theorem tablePoly_eval {m : ℕ} (c : (Fin m → Bool) → F) (t : F) :
    (tablePoly c).eval t = digitsEval c (fun k => sq^[(k : ℕ)] t) := by
  unfold tablePoly digitsEval
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · exact digitPoly_eval _ t
  · simp

/-- **A claim on a table is an evaluation of its polynomial.** At the point built from `t`, the
table's multilinear extension is its polynomial's value at `t` over the product of the
`1 + w_k(t)`, when none of these is zero. -/
theorem mle_eq_tablePoly_eval {m : ℕ} (c : (Fin m → Bool) → F) (t : F)
    (ht : ∀ k : Fin m, 1 + sq^[(k : ℕ)] t ≠ 0) :
    mle c (fun k => sq^[(k : ℕ)] t / (1 + sq^[(k : ℕ)] t))
      = (tablePoly c).eval t / ∏ k : Fin m, (1 + sq^[(k : ℕ)] t) := by
  rw [tablePoly_eval]
  exact mle_eq_digitsEval_div c _ ht

/-- **The sum over the cells is the claim at the point of all ones**, for a table's polynomial. -/
theorem sum_tablePoly {m : ℕ} (hm : m ≤ n) (c : (Fin m → Bool) → F) :
    ∑ x : Fin m → Bool, (tablePoly c).eval (B.point x) = mle c (fun _ => 1) := by
  rw [← B.sum_cells hm c]
  exact Finset.sum_congr rfl fun x _ => tablePoly_eval c _

/-! ## One more coordinate -/

/-- **A free coordinate chooses between two halves.** A table in one more variable is two tables;
at the coordinate `e` its extension is `(1 + e)` times the first's plus `e` times the second's. -/
theorem mle_snoc {m : ℕ} (c : (Fin (m + 1) → Bool) → F) (u : Fin m → F) (e : F) :
    mle c (Fin.snoc u e)
      = (1 + e) * mle (fun b => c (Fin.snoc b false)) u
        + e * mle (fun b => c (Fin.snoc b true)) u := by
  unfold mle
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 1) => Bool), Fintype.sum_prod_type]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  rw [Finset.mul_sum, Finset.mul_sum, add_comm]
  congr 1 <;> exact Finset.sum_congr rfl fun b _ => by ring

end QuotientSecurity
