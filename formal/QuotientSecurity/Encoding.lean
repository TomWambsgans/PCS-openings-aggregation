-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Encoding.lean. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib

/-!
# A multilinear claim is a univariate evaluation

A table of `2^m` entries holds the coefficients `c` of a polynomial in the basis of products of
digits `w_k`. Its multilinear extension at the point `u_k = w_k / (1 + w_k)` is the polynomial's
value divided by the product of the `1 + w_k`. This is the identity that turns the verifier's
claims on tables into the evaluations the security proofs speak of.
-/

open Finset

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2] {m : ℕ}

/-- The multilinear extension of a table at `u`: entry `b` weighs the product of `u_k` where
`b_k` is set and of `1 + u_k` elsewhere. -/
def mle (c : (Fin m → Bool) → F) (u : Fin m → F) : F :=
  ∑ b, c b * ∏ k, (if b k then u k else 1 + u k)

/-- The polynomial of coefficients `c` at a point whose digits are `w`. -/
def digitsEval (c : (Fin m → Bool) → F) (w : Fin m → F) : F :=
  ∑ b, c b * ∏ k, (if b k then w k else 1)

/-- **A claim is an evaluation.** -/
theorem mle_eq_digitsEval_div (c : (Fin m → Bool) → F) (w : Fin m → F)
    (hw : ∀ k, 1 + w k ≠ 0) :
    mle c (fun k => w k / (1 + w k)) = digitsEval c w / ∏ k, (1 + w k) := by
  unfold mle digitsEval
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_div_assoc, ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · rfl
  · rw [eq_div_iff (hw k), add_mul, one_mul, div_mul_cancel₀ _ (hw k), add_assoc,
      CharTwo.add_self_eq_zero, add_zero]

/-- At the point of all ones, the extension is the last entry: the top coefficient. -/
theorem mle_ones (c : (Fin m → Bool) → F) : mle c (fun _ => 1) = c fun _ => true := by
  unfold mle
  rw [Finset.sum_eq_single fun _ => true]
  · simp
  · intro b _ hb
    obtain ⟨k, hk⟩ : ∃ k, b k = false := by
      by_contra h
      push_neg at h
      exact hb (funext fun k => by simpa using h k)
    rw [Finset.prod_eq_zero (Finset.mem_univ k), mul_zero]
    simp [hk, CharTwo.add_self_eq_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The top entry is the sum over the cells

The cells are indexed by their bits, and digit `k` of a cell is its bit `k` plus something that
depends on the higher bits only: this is `w_k(B(i)) = i_k + sum_{j > k} beta_{j - k} i_j` for a
Cantor basis. Then the sum over the cells of a polynomial given by its coefficients is its top
coefficient. -/

/-- A product of triangular digits, some of them left out, sums to one if none is left out and
to zero otherwise. -/
theorem sum_prod_triangular : ∀ (m : ℕ) (g : Fin m → (Fin m → Bool) → F)
    (_hg : ∀ k x x', (∀ j, k < j → x j = x' j) → g k x = g k x') (b : Fin m → Bool),
    ∑ x : Fin m → Bool, ∏ k, (if b k then (if x k then 1 else 0) + g k x else 1)
      = if ∀ k, b k = true then 1 else 0
  | 0, _, _, b => by simp
  | m + 1, g, hg, b => by
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => Bool), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fintype.sum_bool]
    -- The digits above the lowest do not see the lowest bit.
    have hrest : ∀ (x0 : Bool) (xs : Fin m → Bool) (k : Fin m),
        g k.succ (Fin.cons x0 xs) = g k.succ (Fin.cons false xs) := by
      intro x0 xs k
      refine hg k.succ _ _ fun j hj => ?_
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp
        (lt_of_le_of_lt (Fin.zero_le _) hj))
      simp
    have hzero : ∀ (x0 : Bool) (xs : Fin m → Bool),
        g 0 (Fin.cons x0 xs) = g 0 (Fin.cons false xs) := by
      intro x0 xs
      refine hg 0 _ _ fun j hj => ?_
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp hj)
      simp
    simp only [hrest true, hzero true]
    have ih := sum_prod_triangular m (fun k xs => g k.succ (Fin.cons false xs))
      (fun k x x' h => hg k.succ _ _ fun j hj => by
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp
          (lt_of_le_of_lt (Fin.zero_le _) hj))
        simpa using h j' (Fin.succ_lt_succ_iff.mp hj))
      (fun k => b k.succ)
    by_cases h0 : b 0 = true
    · simp only [h0, if_true, Bool.false_eq_true, if_false, zero_add]
      have : ∀ xs : Fin m → Bool,
          (1 + g 0 (Fin.cons false xs)) *
              ∏ k : Fin m, (if b k.succ then (if xs k then 1 else 0) + g k.succ (Fin.cons false xs)
                else 1)
            + g 0 (Fin.cons false xs) *
              ∏ k : Fin m, (if b k.succ then (if xs k then 1 else 0) + g k.succ (Fin.cons false xs)
                else 1)
          = ∏ k : Fin m, (if b k.succ then (if xs k then 1 else 0) + g k.succ (Fin.cons false xs)
              else 1) := by
        intro xs
        rw [← add_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero, one_mul]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun xs _ => this xs, ih]
      refine if_congr ?_ rfl rfl
      constructor
      · intro h k
        refine Fin.cases h0 (fun j => h j) k
      · intro h k
        exact h k.succ
    · have hb0 : b 0 = false := by simpa using h0
      simp only [hb0, Bool.false_eq_true, if_false, one_mul]
      rw [CharTwo.add_self_eq_zero, if_neg fun h => h0 (h 0)]

/-- **The claim at the point of all ones is the sum over the cells**: the polynomial of
coefficients `c`, summed over cells whose digits are triangular, is its top coefficient. -/
theorem sum_digitsEval (c : (Fin m → Bool) → F) (g : Fin m → (Fin m → Bool) → F)
    (hg : ∀ k x x', (∀ j, k < j → x j = x' j) → g k x = g k x') :
    ∑ x : Fin m → Bool, digitsEval c (fun k => (if x k then 1 else 0) + g k x)
      = mle c (fun _ => 1) := by
  rw [mle_ones]
  unfold digitsEval
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single fun _ => true]
  · rw [sum_prod_triangular m g hg fun _ => true]
    simp
  · intro b _ hb
    rw [sum_prod_triangular m g hg b, if_neg, mul_zero]
    intro h
    exact hb (funext h)
  · intro h; exact absurd (Finset.mem_univ _) h

end QuotientSecurity
