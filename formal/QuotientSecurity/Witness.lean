-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Witness.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Cells

/-!
# Every assignment of the cells is a first message's

Given any values for the cells, there are four row polynomials whose cells are those values. So
the honest prover exists for every witness, and the relation the extractor is held to is about
all assignments, not about a subset a message can reach.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Params F)

namespace Params

/-- An element fixed by the fourth power is one of the four shifts. -/
theorem eq_shift_of_pow_four {z : F} (hz : z ^ 4 + z = 0) : ∃ c : Fin 4, z = shift P.θ c := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hprod : z * (z + 1) * (z + P.θ) * (z + P.θ + 1) = 0 := by
    linear_combination hz + ((P.θ + 1) * z ^ 3 + P.θ * z ^ 2 - z) * two + (z ^ 2 + z) * P.hθ
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact ⟨0, by simpa [shift] using h⟩
      · exact ⟨1, by simpa [shift] using CharTwo.add_eq_zero.mp h⟩
    · exact ⟨2, by simpa [shift] using CharTwo.add_eq_zero.mp h⟩
  · refine ⟨3, ?_⟩
    have : z + (P.θ + 1) = 0 := by rw [← h]; ring
    simpa [shift] using CharTwo.add_eq_zero.mp this

/-- Distinct rows have distinct row values. -/
theorem rowPoly_injOn : Set.InjOn (fun x : P.T => (rowPoly : F[X]).eval (x : F)) Set.univ := by
  rintro ⟨x, hx⟩ - ⟨y, hy⟩ - h
  simp only [rowPoly, eval_add, eval_pow, eval_X] at h
  have h4 : (x + y) ^ 4 = x ^ 4 + y ^ 4 := by
    have := add_pow_char_pow (R := F) (p := 2) (n := 2) x y
    simpa using this
  have hz : (x + y) ^ 4 + (x + y) = 0 := by
    rw [h4]
    have : x ^ 4 + y ^ 4 + (x + y) = (x ^ 4 + x) + (y ^ 4 + y) := by ring
    rw [this, h]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨c, hc⟩ := P.eq_shift_of_pow_four hz
  have hxy : x + shift P.θ 0 = y + shift P.θ c := by
    rw [← hc]
    simp only [shift, Matrix.cons_val_zero, add_zero]
    rw [add_comm x y, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  exact Subtype.ext (P.hT x hx y hy 0 c hxy).1

/-- A polynomial of degree below 4 in the digit basis. -/
theorem digit_expansion (p : F[X]) (hp : p.natDegree < 4) :
    p = C (p.coeff 0) * digit 0 + C (p.coeff 1 + p.coeff 2 + p.coeff 3) * digit 1
      + C (p.coeff 2 + p.coeff 3) * digit 2 + C (p.coeff 3) * digit 3 := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsum := p.as_sum_range' 4 hp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← C_mul_X_pow_eq_monomial]
    at hsum
  have hd : (digit 0 : F[X]) = 1 ∧ (digit 1 : F[X]) = X ∧ (digit 2 : F[X]) = X ^ 2 + X ∧
      (digit 3 : F[X]) = (X ^ 2 + X) * X := ⟨rfl, rfl, rfl, rfl⟩
  rw [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]
  conv_lhs => rw [hsum]
  simp only [C_add, pow_zero, pow_one, mul_one]
  have c2 : (2 : F[X]) = 0 := by
    have h : (C (2 : F) : F[X]) = 0 := by rw [two, C_0]
    rwa [C_ofNat] at h
  linear_combination (-(C (p.coeff 2) * X) - C (p.coeff 3) * X - C (p.coeff 3) * X ^ 2) * c2

/-- **Every assignment of the cells is a first message's.** -/
theorem exists_witness (w : P.T × Fin 4 → F) : ∃ g : Witness F, cells P g = w := by
  classical
  -- Per row: the polynomial of degree below 4 through the row's four cells.
  set p : P.T → F[X] := fun x =>
    Lagrange.interpolate univ (fun c : Fin 4 => (x : F) + shift P.θ c) (fun c => w (x, c)) with hp
  have hnodes : ∀ x : P.T, Set.InjOn (fun c : Fin 4 => (x : F) + shift P.θ c)
      ((univ : Finset (Fin 4)) : Set (Fin 4)) := fun x c _ d _ h =>
    (P.hT x x.2 x x.2 c d h).2
  have hdeg : ∀ x, (p x).natDegree < 4 := fun x => by
    have h : (p x).degree < ((univ : Finset (Fin 4)).card : WithBot ℕ) :=
      Lagrange.degree_interpolate_lt _ (hnodes x)
    by_cases h0 : p x = 0
    · rw [h0]; simp
    · exact (natDegree_lt_iff_degree_lt h0).mpr (lt_of_lt_of_eq h (by simp))
  set a : P.T → Fin 4 → F := fun x =>
    ![(p x).coeff 0, (p x).coeff 1 + (p x).coeff 2 + (p x).coeff 3,
      (p x).coeff 2 + (p x).coeff 3, (p x).coeff 3] with ha
  refine ⟨fun j => Lagrange.interpolate univ (fun x : P.T => (rowPoly : F[X]).eval (x : F))
    (fun x => a x j), ?_⟩
  funext ⟨x, c⟩
  have hrow : ∀ j, (Lagrange.interpolate univ (fun x : P.T => (rowPoly : F[X]).eval (x : F))
      (fun x => a x j)).eval ((rowPoly : F[X]).eval (x : F)) = a x j := fun j =>
    Lagrange.eval_interpolate_at_node _ (fun y _ z _ h => P.rowPoly_injOn (Set.mem_univ y)
      (Set.mem_univ z) h) (Finset.mem_univ x)
  simp only [cells, cellPoly, eval_finsetSum, eval_mul, eval_comp, eval_add, eval_X, eval_C, hrow]
  have hexp := congrArg (fun q : F[X] => q.eval ((x : F) + shift P.θ c))
    (digit_expansion (p x) (hdeg x))
  simp only [eval_add, eval_mul, eval_C] at hexp
  have hval : (p x).eval ((x : F) + shift P.θ c) = w (x, c) :=
    Lagrange.eval_interpolate_at_node _ (hnodes x) (Finset.mem_univ c)
  rw [← hval, hexp, Fin.sum_univ_four]
  simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

end Params

end QuotientSecurity
