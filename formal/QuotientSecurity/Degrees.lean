-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Degrees.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Protocol

/-!
# The degree of the two identities

A table has a size, so the polynomials of the messages have bounded degrees, and so do the two
identities: this is what the second challenge's error is counted in.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F] (P : Params F)

namespace Params

/-- Bounds on the degrees of the fixed polynomials and of what the two messages hold. -/
structure Bounds where
  /-- The four row polynomials of the first message. -/
  witness : ℕ
  /-- The five polynomials of the second message. -/
  quotient : ℕ
  /-- The wiring polynomial, the public weight, and the two vanishing polynomials. -/
  sigma : ℕ
  pub : ℕ
  cells : ℕ
  rows : ℕ
  hSigma : P.sigmaPoly.natDegree ≤ sigma
  hPub : ∀ γ, (P.pub γ).natDegree ≤ pub
  hCells : P.vCells.natDegree ≤ cells
  hRows : P.vRows.natDegree ≤ rows

variable {P} (B : P.Bounds)

/-- A first message within the bounds. -/
def Bounds.Msg₁ (B : P.Bounds) : Type _ :=
  { g : Params.Witness F // ∀ j, (g j).natDegree ≤ B.witness }

/-- A second message within the bounds. -/
def Bounds.Msg₂ (B : P.Bounds) : Type _ :=
  { R : Params.Quotients F // R.h₀.natDegree ≤ B.quotient ∧ R.hHigh.natDegree ≤ B.quotient ∧
      R.q.natDegree ≤ B.quotient ∧ R.qGate.natDegree ≤ B.quotient ∧
      R.junk.natDegree ≤ B.quotient }

/-- The degree of a cell's polynomial, of a denominator, and of the two identities. -/
def Bounds.cell (B : P.Bounds) : ℕ := 3 + B.witness * 4

def Bounds.denominator (B : P.Bounds) : ℕ := B.cell + B.sigma + 1

def Bounds.identity (B : P.Bounds) : ℕ :=
  2 * B.denominator + B.cells + B.rows + B.quotient + B.pub + 4 * B.cell

theorem natDegree_digit_le (j : Fin 4) : (digit j : F[X]).natDegree ≤ 3 := by
  fin_cases j
  · show (1 : F[X]).natDegree ≤ 3
    simp
  · show (X : F[X]).natDegree ≤ 3
    exact natDegree_X_le.trans (by norm_num)
  · show (X ^ 2 + X : F[X]).natDegree ≤ 3
    compute_degree
    norm_num
  · show ((X ^ 2 + X) * X : F[X]).natDegree ≤ 3
    compute_degree

theorem natDegree_cellPoly_le (g : B.Msg₁) (c : Fin 4) :
    (cellPoly P g.1 c).natDegree ≤ B.cell := by
  unfold cellPoly Bounds.cell
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine natDegree_mul_le_of_le ?_ ?_
  · refine natDegree_comp_le.trans ?_
    have h1 := natDegree_digit_le (F := F) j
    have h2 : (X + C (shift P.θ c) : F[X]).natDegree ≤ 1 := by compute_degree
    calc (digit j : F[X]).natDegree * (X + C (shift P.θ c)).natDegree ≤ 3 * 1 :=
          Nat.mul_le_mul h1 h2
      _ = 3 := by norm_num
  · refine natDegree_comp_le.trans ?_
    have h2 : (rowPoly : F[X]).natDegree ≤ 4 := by unfold rowPoly; compute_degree
    exact Nat.mul_le_mul (g.2 j) h2

theorem natDegree_dPoly_le (g : B.Msg₁) (α β : F) :
    (dPoly P g.1 α β).natDegree ≤ B.denominator := by
  have hc := natDegree_cellPoly_le B g 0
  unfold dPoly Bounds.denominator
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
  · rw [natDegree_C]; omega
  · omega
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by omega))

theorem natDegree_dNextPoly_le (g : B.Msg₁) (α β : F) :
    (dNextPoly P g.1 α β).natDegree ≤ B.denominator := by
  have hc := natDegree_cellPoly_le B g 0
  have hs := B.hSigma
  unfold dNextPoly Bounds.denominator
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
  · rw [natDegree_C]; omega
  · omega
  · exact (natDegree_C_mul_le _ _).trans (by omega)

theorem natDegree_gatePoly_le (g : B.Msg₁) : (gatePoly P g.1).natDegree ≤ 4 * B.cell := by
  have h := fun c => natDegree_cellPoly_le B g c
  have hbit : ∀ c, (cellPoly P g.1 c * (C P.θ * cellPoly P g.1 c + C P.θ * C P.θ)).natDegree
      ≤ 2 * B.cell := by
    intro c
    refine (natDegree_mul_le_of_le (h c) (natDegree_add_le_of_degree_le
      ((natDegree_C_mul_le _ _).trans (h c)) ?_)).trans (by omega)
    rw [← C_mul, natDegree_C]; omega
  have hcarry : (cellPoly P g.1 2 * cellPoly P g.1 2 + cellPoly P g.1 2).natDegree
      ≤ 2 * B.cell :=
    natDegree_add_le_of_degree_le
      ((natDegree_mul_le_of_le (h 2) (h 2)).trans (by omega)) ((h 2).trans (by omega))
  unfold gatePoly gate
  simp only
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_) ?_
  · exact (h 3).trans (by omega)
  · exact (hbit 0).trans (by omega)
  · exact (hbit 1).trans (by omega)
  · exact hcarry.trans (by omega)
  · refine (natDegree_C_mul_le _ _).trans (natDegree_add_le_of_degree_le ?_ ?_)
    · exact (natDegree_mul_le_of_le (hbit 0) (hbit 1)).trans (by omega)
    · exact (natDegree_mul_le_of_le hcarry
        (natDegree_add_le_of_degree_le (hbit 0) (hbit 1))).trans (by omega)

theorem natDegree_copyDefect_le (g : B.Msg₁) (R : B.Msg₂) (α β γ : F) :
    (copyDefect P g.1 R.1 α β γ).natDegree ≤ B.identity := by
  have hd := natDegree_dPoly_le B g α β
  have hd' := natDegree_dNextPoly_le B g α β
  have hc := natDegree_cellPoly_le B g 0
  have hp := B.hPub γ
  have hv := B.hCells
  obtain ⟨h0, h1, h2, -, -⟩ := R.2
  unfold copyDefect copyPoly Quotients.h Bounds.identity
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_)
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_)
  · refine (natDegree_mul_le_of_le (natDegree_mul_le_of_le hd hd')
      (natDegree_add_le_of_degree_le (n := B.cells + B.quotient) (h0.trans (by omega))
        (natDegree_mul_le_of_le hv h1))).trans (by omega)
  · exact (natDegree_mul_le_of_le hv h2).trans (by omega)
  · omega
  · omega
  · exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hp hc)
      (natDegree_mul_le_of_le hd hd')).trans (by omega)

theorem natDegree_gateDefect_le (g : B.Msg₁) (R : B.Msg₂) (α β : F) :
    (gateDefect P g.1 R.1 α β).natDegree ≤ B.identity := by
  have hd := natDegree_dPoly_le B g α β
  have hd' := natDegree_dNextPoly_le B g α β
  have hg := natDegree_gatePoly_le B g
  have hv := B.hCells
  have hr := B.hRows
  obtain ⟨-, -, -, h3, h4⟩ := R.2
  unfold gateDefect Bounds.identity
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine (natDegree_mul_le_of_le hr (natDegree_add_le_of_degree_le
      (n := 2 * B.denominator + B.cells + B.quotient) ?_ ?_)).trans (by omega)
    · exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hd hd') h3).trans (by omega)
    · exact (natDegree_mul_le_of_le hv h4).trans (by omega)
  · exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hd hd') hg).trans (by omega)

end Params

end QuotientSecurity
