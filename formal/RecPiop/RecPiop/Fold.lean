-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib

/-!
# `W`'s fold at `ρ`: the claim binds the fold values

`PI2.md` §2: `W`'s claim is at `(ρ, ρ², ρ⁴, …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, its value
`Σ_k eq(ρ⃗, k)·a_k` (`foldAt`), the fold values `a_k` sent before `ρ`. The weights
`eq(ρ⃗, k) = Π_{l<r} (ρ^{2^l} if bit `l` of `k`, else `1 + ρ^{2^l}`)` are polynomials in `ρ`
(`eqPowPoly`) that are **unitriangular** (REVIEW-REC.md: `eq(ρ⃗, k) = Σ_{j ⊇ k} ρ^j` in
characteristic two): splitting on the top bit, the fold of `r + 1` bits is `A + X^{2^r}(A + B)`, `A`
and `B` the folds of the two halves, both of degree below `2^r` (`foldPoly_succ`). So the fold
polynomial of a nonzero vector is nonzero, of degree at most `2^r − 1` (`foldPoly_ne_zero`,
`natDegree_foldPoly_le`), and **two different vectors of fold values give the same claim at at
most `2^r − 1` points `ρ`** (`card_foldAt_eq_le`).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial

variable {F : Type} [Field F] [CharP F 2]

/-- **The weight of fold value `k`** at `(ρ, ρ², …)`, as a polynomial in `ρ`. -/
noncomputable def eqPowPoly (r k : ℕ) : F[X] :=
  ∏ l ∈ range r, if k.testBit l then X ^ (2 ^ l) else 1 + X ^ (2 ^ l)

/-- The weight at `ρ`. -/
def eqPow (r : ℕ) (ρ : F) (k : ℕ) : F :=
  ∏ l ∈ range r, if k.testBit l then ρ ^ (2 ^ l) else 1 + ρ ^ (2 ^ l)

/-- **`W`'s claim's value**: `Σ_{k < 2^r} eq(ρ⃗, k)·a_k`. -/
def foldAt (r : ℕ) (a : ℕ → F) (ρ : F) : F := ∑ k ∈ range (2 ^ r), eqPow r ρ k * a k

/-- The claim's value as a polynomial in `ρ`. -/
noncomputable def foldPoly (r : ℕ) (a : ℕ → F) : F[X] :=
  ∑ k ∈ range (2 ^ r), C (a k) * eqPowPoly r k

theorem foldPoly_eval (r : ℕ) (a : ℕ → F) (ρ : F) : (foldPoly r a).eval ρ = foldAt r a ρ := by
  unfold foldPoly foldAt eqPowPoly eqPow
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_prod, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem foldAt_sub (r : ℕ) (a b : ℕ → F) (ρ : F) :
    foldAt r a ρ - foldAt r b ρ = foldAt r (fun k => a k - b k) ρ := by
  unfold foldAt
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **A weight of `r + 1` bits**: the weight of the low `r` bits times the top bit's factor. -/
theorem eqPowPoly_succ_low (r : ℕ) {k : ℕ} (hk : k < 2 ^ r) :
    (eqPowPoly (r + 1) k : F[X]) = eqPowPoly r k * (1 + X ^ (2 ^ r)) := by
  unfold eqPowPoly
  rw [Finset.prod_range_succ, Nat.testBit_eq_false_of_lt hk]
  simp only [Bool.false_eq_true, ite_false]

theorem eqPowPoly_succ_high (r : ℕ) {k : ℕ} (hk : k < 2 ^ r) :
    (eqPowPoly (r + 1) (2 ^ r + k) : F[X]) = eqPowPoly r k * X ^ (2 ^ r) := by
  unfold eqPowPoly
  rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hk]
  simp only [Bool.not_false, ite_true]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hl)]

/-- **The fold of `r + 1` bits from its halves**: `A + X^{2^r}(A + B)`. -/
theorem foldPoly_succ (r : ℕ) (a : ℕ → F) :
    foldPoly (r + 1) a = foldPoly r a + X ^ (2 ^ r) * (foldPoly r a + foldPoly r fun k => a (2 ^ r + k)) := by
  unfold foldPoly
  rw [pow_succ, mul_two, Finset.sum_range_add]
  calc _ = ∑ k ∈ range (2 ^ r), (C (a k) * eqPowPoly r k + X ^ (2 ^ r) * (C (a k) * eqPowPoly r k)) +
        ∑ k ∈ range (2 ^ r), X ^ (2 ^ r) * (C (a (2 ^ r + k)) * eqPowPoly r k) := by
        congr 1 <;> refine Finset.sum_congr rfl fun k hk => ?_
        · rw [eqPowPoly_succ_low r (Finset.mem_range.mp hk)]; ring
        · rw [eqPowPoly_succ_high r (Finset.mem_range.mp hk)]; ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- `A + X^d B = 0` with `A` of degree below `d` forces `A = 0` and `B = 0`. -/
theorem eq_zero_of_add_X_pow_mul {A B : F[X]} {d : ℕ} (hA : A.natDegree < d)
    (h : A + X ^ d * B = 0) : A = 0 ∧ B = 0 := by
  have hA0 : A = 0 := by
    ext j
    rw [coeff_zero]
    by_cases hj : j < d
    · have := congrArg (fun p => coeff p j) h
      simp only [coeff_add, coeff_X_pow_mul', coeff_zero] at this
      rwa [ite_eq_right (by omega), add_zero] at this
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨hA0, ?_⟩
  rw [hA0, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ X_ne_zero)

/-- **The fold polynomial's degree and kernel**: at most `2^r − 1`, and zero only for the zero
vector of fold values. -/
theorem foldPoly_spec : ∀ (r : ℕ) (a : ℕ → F),
    (foldPoly r a).natDegree ≤ 2 ^ r - 1 ∧ (foldPoly r a = 0 → ∀ k < 2 ^ r, a k = 0)
  | 0, a => by
    have e : foldPoly 0 a = C (a 0) := by simp [foldPoly, eqPowPoly]
    refine ⟨by rw [e, natDegree_C]; exact Nat.zero_le _, fun h k hk => ?_⟩
    rw [e, C_eq_zero] at h
    rw [show k = 0 by simpa using hk]
    exact h
  | r + 1, a => by
    obtain ⟨hA, hA0⟩ := foldPoly_spec r a
    obtain ⟨hB, hB0⟩ := foldPoly_spec r fun k => a (2 ^ r + k)
    have hp : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hsum : (foldPoly r a + foldPoly r fun k => a (2 ^ r + k)).natDegree ≤ 2 ^ r - 1 :=
      natDegree_add_le_of_degree_le hA hB
    refine ⟨?_, fun h k hk => ?_⟩
    · rw [foldPoly_succ]
      refine natDegree_add_le_of_degree_le (hA.trans (by rw [pow_succ]; omega)) ?_
      refine (natDegree_mul_le_of_le (natDegree_X_pow_le _) hsum).trans ?_
      rw [pow_succ]
      omega
    · rw [foldPoly_succ] at h
      obtain ⟨h1, h2⟩ := eq_zero_of_add_X_pow_mul (by omega) h
      rw [h1, zero_add] at h2
      by_cases hlt : k < 2 ^ r
      · exact hA0 h1 k hlt
      · have := hB0 h2 (k - 2 ^ r) (by rw [pow_succ] at hk; omega)
        rwa [show 2 ^ r + (k - 2 ^ r) = k by omega] at this

/-- **`W`'s claim binds the fold values.** Two vectors of fold values that differ below `2^r` give
the same claim at at most `2^r − 1` points `ρ`. -/
theorem card_foldAt_eq_le [Fintype F] [DecidableEq F] (r : ℕ) {a b : ℕ → F}
    (hne : ∃ k < 2 ^ r, a k ≠ b k) :
    (univ.filter fun ρ => foldAt r a ρ = foldAt r b ρ).card ≤ 2 ^ r - 1 := by
  obtain ⟨hdeg, hker⟩ := foldPoly_spec r fun k => a k - b k
  have hne0 : foldPoly r (fun k => a k - b k) ≠ 0 := fun h => by
    obtain ⟨k, hk, hab⟩ := hne
    exact hab (sub_eq_zero.mp (hker h k hk))
  refine (Finset.card_le_card fun ρ hρ => ?_).trans
    ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdeg))
  rw [Multiset.mem_toFinset, mem_roots hne0, IsRoot.def, foldPoly_eval, ← foldAt_sub,
    (Finset.mem_filter.mp hρ).2, sub_self]

end RecPiop
