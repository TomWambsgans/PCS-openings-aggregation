-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Cells.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Protocol

/-!
# What a consistent second message says on the cells

If both identities hold as polynomials and no denominator vanishes on a cell, then every row's
gate holds and the sum's polynomial is, on the cells, the logarithmic derivatives plus the
weighted public cells.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Params F)

namespace Params

theorem theta_pow_four : P.θ ^ 4 = P.θ := by
  have h := P.hθ
  have h2 : P.θ * P.θ = P.θ + 1 := by
    have : P.θ * P.θ + (P.θ + 1) = 0 := by rw [← h]; ring
    exact CharTwo.add_eq_zero.mp this
  have h4 : P.θ ^ 4 = (P.θ * P.θ) * (P.θ * P.θ) := by ring
  rw [h4, h2]
  have : (P.θ + 1) * (P.θ + 1) = P.θ * P.θ + 1 + (P.θ + P.θ) := by ring
  rw [this, CharTwo.add_self_eq_zero, add_zero, h2, add_assoc, CharTwo.add_self_eq_zero,
    add_zero]

theorem shift_pow_four (c : Fin 4) : shift P.θ c ^ 4 = shift P.θ c := by
  fin_cases c
  · simp [shift]
  · simp [shift]
  · simpa [shift] using P.theta_pow_four
  · simp only [shift]
    show (P.θ + 1) ^ 4 = P.θ + 1
    have : (P.θ + 1) ^ 4 = P.θ ^ 4 + 1 := by
      have h := add_pow_char_pow (R := F) (p := 2) (n := 2) P.θ 1
      simpa using h
    rw [this, P.theta_pow_four]

/-- A row is the same at its four cells. -/
theorem rowPoly_eval_add_shift (x : F) (c : Fin 4) :
    (rowPoly : F[X]).eval (x + shift P.θ c) = (rowPoly : F[X]).eval x + (shift P.θ c + shift P.θ c)
      := by
  have h := add_pow_char_pow (R := F) (p := 2) (n := 2) x (shift P.θ c)
  simp only [rowPoly, eval_add, eval_pow, eval_X]
  have h' : (x + shift P.θ c) ^ 4 = x ^ 4 + shift P.θ c ^ 4 := by simpa using h
  rw [h', P.shift_pow_four]
  ring

theorem rowPoly_eval_shift (x : F) (c : Fin 4) :
    (rowPoly : F[X]).eval (x + shift P.θ c) = (rowPoly : F[X]).eval x := by
  rw [P.rowPoly_eval_add_shift, CharTwo.add_self_eq_zero, add_zero]

/-- The polynomial of the `X` role, at any cell, is that cell's value. -/
theorem cellPoly_zero_eval_pt (g : Witness F) (i : P.T × Fin 4) :
    (cellPoly P g 0).eval (P.pt i) = cells P g i := by
  simp only [cellPoly, cells, pt, eval_finsetSum, eval_mul, eval_comp, eval_add, eval_X, eval_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [P.rowPoly_eval_shift]
  simp [shift]

theorem cellPoly_eval_row (g : Witness F) (x : P.T) (c : Fin 4) :
    (cellPoly P g c).eval (x : F) = cells P g (x, c) := rfl

theorem gate_eval (a b c d : F[X]) (t : F) :
    (gate (C P.θ) a b c d).eval t = gate P.θ (a.eval t) (b.eval t) (c.eval t) (d.eval t) := by
  simp [gate]

theorem pt_row (x : P.T) : P.pt (x, 0) = x := by simp [pt, shift]

theorem dPoly_eval_pt (g : Witness F) (α β : F) (i : P.T × Fin 4) :
    (dPoly P g α β).eval (P.pt i) = α + cells P g i + β * P.pt i := by
  simp [dPoly, cellPoly_zero_eval_pt]

theorem dNextPoly_eval_pt (g : Witness F) (α β : F) (i : P.T × Fin 4) :
    (dNextPoly P g α β).eval (P.pt i) = α + cells P g i + β * P.pt (P.σ i) := by
  simp only [dNextPoly, eval_add, eval_mul, eval_C, cellPoly_zero_eval_pt]
  rw [show P.sigmaPoly.eval (P.pt i) = P.pt (P.σ i) from P.hσ i]

/-- A consistent second message, where no denominator vanishes on a cell: every gate holds, and
the logarithmic derivatives plus the weighted public words sum to the target. -/
theorem consistent_on_cells (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F)
    (α β γ : F) (h : P.Consistent stmt g R α β γ)
    (hd : ∀ i, α + cells P g i + β * P.pt i ≠ 0)
    (hd' : ∀ i, α + cells P g i + β * P.pt (P.σ i) ≠ 0) :
    (∀ x : P.T, gate P.θ (cells P g (x, 0)) (cells P g (x, 1)) (cells P g (x, 2))
        (cells P g (x, 3)) = 0) ∧
      logSum P.pt P.σ (cells P g) α β + ∑ J : Fin P.words, γ ^ (J : ℕ) * P.wordSum J (cells P g)
        = P.target stmt γ := by
  obtain ⟨hcopy, hgate, htop⟩ := h
  constructor
  · intro x
    have h0 := congrArg (fun p : F[X] => p.eval (x : F)) hgate
    simp only [gateDefect, eval_add, eval_mul, eval_zero, P.hRows x x.2, zero_mul, zero_add]
      at h0
    have hx := P.pt_row x
    have h1 : (dPoly P g α β).eval (x : F) ≠ 0 := by
      rw [← hx, dPoly_eval_pt]; exact hd _
    have h2 : (dNextPoly P g α β).eval (x : F) ≠ 0 := by
      rw [← hx, dNextPoly_eval_pt]; exact hd' _
    have h3 := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero h1 h2)
    rw [gatePoly, gate_eval] at h3
    exact h3
  · have hpoint : ∀ i : P.T × Fin 4, R.h₀.eval (P.pt i)
        = (α + cells P g i + β * P.pt i)⁻¹ + (α + cells P g i + β * P.pt (P.σ i))⁻¹
          + (P.pub γ).eval (P.pt i) * cells P g i := by
      intro i
      have h0 := congrArg (fun p : F[X] => p.eval (P.pt i)) hcopy
      have hv : P.vCells.eval (P.pt i) = 0 := P.hCells i.1.1 i.1.2 i.2
      simp only [copyDefect, copyPoly, Quotients.h, eval_add, eval_mul, eval_zero, hv, zero_mul,
        add_zero, dPoly_eval_pt, dNextPoly_eval_pt, cellPoly_zero_eval_pt] at h0
      have e1 := hd i
      have e2 := hd' i
      set d := α + cells P g i + β * P.pt i
      set d' := α + cells P g i + β * P.pt (P.σ i)
      have h1 : d * d' * R.h₀.eval (P.pt i)
          = d + d' + (P.pub γ).eval (P.pt i) * cells P g i * (d * d') :=
        CharTwo.add_eq_zero.mp h0
      have h2 : R.h₀.eval (P.pt i)
          = (d + d' + (P.pub γ).eval (P.pt i) * cells P g i * (d * d')) / (d * d') := by
        rw [eq_div_iff (mul_ne_zero e1 e2), mul_comm, h1]
      rw [h2]
      field_simp
      ring
    rw [← htop, Quotients.top, Finset.sum_congr rfl fun i _ => hpoint i, Finset.sum_add_distrib,
      ← P.hPub γ (cells P g)]
    rfl

end Params

end QuotientSecurity
