-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Completeness.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.RoundThree

/-!
# Completeness

The honest second message exists and is consistent with the first, and then the verifier's four
claims are true at every challenge it does not reject. So for an honest prover the verdict is a
function of the challenges and of the five values sent: this is what lets a simulator give it.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] [Fintype F]

/-- A polynomial vanishing at distinct points is divisible by their vanishing polynomial. -/
theorem prod_X_sub_C_dvd {ι : Type*} [Fintype ι] (v : ι → F) (hv : Function.Injective v)
    (p : F[X]) (hp : ∀ i, p.eval (v i) = 0) : (∏ i, (X - C (v i))) ∣ p := by
  refine Finset.prod_dvd_of_coprime (fun i _ j _ hij => ?_) fun i _ => ?_
  · exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr fun h => hij (hv h)).isUnit
  · exact dvd_iff_isRoot.mpr (hp i)

variable (P : Params F)

namespace Params

/-- The two vanishing polynomials are exactly those of the cells and of the rows. -/
structure Exact : Prop where
  cells : P.vCells = ∏ i : P.T × Fin 4, (X - C (P.pt i))
  rows : P.vRows = ∏ x : P.T, (X - C (x : F))

/-- The value the sum's polynomial takes at a cell. -/
noncomputable def sumValue (g : Witness F) (α β γ : F) (i : P.T × Fin 4) : F :=
  (α + cells P g i + β * P.pt i)⁻¹ + (α + cells P g i + β * P.pt (P.σ i))⁻¹
    + (P.pub γ).eval (P.pt i) * cells P g i

/-- The honest second message: the interpolation of the sum's values, and the two quotients. -/
noncomputable def honest (g : Witness F) (α β γ : F) : Quotients F where
  h₀ := Lagrange.interpolate univ P.pt (sumValue P g α β γ)
  hHigh := 0
  q := (dPoly P g α β * dNextPoly P g α β * Lagrange.interpolate univ P.pt (sumValue P g α β γ)
    + copyPoly P g α β γ) / P.vCells
  qGate := gatePoly P g / P.vRows
  junk := 0

variable {P}

theorem honest_h₀_eval (g : Witness F) (α β γ : F) (i : P.T × Fin 4) :
    (honest P g α β γ).h₀.eval (P.pt i) = sumValue P g α β γ i :=
  Lagrange.eval_interpolate_at_node _ (P.pt_injective.injOn) (Finset.mem_univ i)

/-- **The honest second message is consistent.** -/
theorem honest_consistent (hE : P.Exact) (stmt : Fin P.words → F) (g : Witness F) (α β γ : F)
    (hsat : P.Sat stmt (cells P g))
    (hd : ∀ i, α + cells P g i + β * P.pt i ≠ 0)
    (hd' : ∀ i, α + cells P g i + β * P.pt (P.σ i) ≠ 0) :
    P.Consistent stmt g (honest P g α β γ) α β γ := by
  obtain ⟨hgate, hcopy, hwords⟩ := hsat
  have hc0 : P.vCells ≠ 0 := by
    rw [hE.cells]; exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _
  have hr0 : P.vRows ≠ 0 := by
    rw [hE.rows]; exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _
  refine ⟨?_, ?_, ?_⟩
  · -- The copy identity: its numerator vanishes on the cells.
    set p := dPoly P g α β * dNextPoly P g α β * (honest P g α β γ).h₀ + copyPoly P g α β γ with hp
    have hdvd : P.vCells ∣ p := by
      rw [hE.cells]
      refine prod_X_sub_C_dvd P.pt P.pt_injective p fun i => ?_
      have e1 := hd i
      have e2 := hd' i
      simp only [hp, copyPoly, eval_add, eval_mul, dPoly_eval_pt, dNextPoly_eval_pt,
        cellPoly_zero_eval_pt, honest_h₀_eval]
      simp only [sumValue]
      set d := α + cells P g i + β * P.pt i
      set d' := α + cells P g i + β * P.pt (P.σ i)
      have : d * d' * (d⁻¹ + d'⁻¹ + (P.pub γ).eval (P.pt i) * cells P g i)
          = d + d' + (P.pub γ).eval (P.pt i) * cells P g i * (d * d') := by
        field_simp
        ring
      rw [this]
      exact CharTwo.add_self_eq_zero _
    have hq : P.vCells * (honest P g α β γ).q = p := EuclideanDomain.mul_div_cancel' hc0 hdvd
    show dPoly P g α β * dNextPoly P g α β * (honest P g α β γ).h P + P.vCells * (honest P g α β γ).q
      + copyPoly P g α β γ = 0
    have hh : (honest P g α β γ).h P = (honest P g α β γ).h₀ := by simp [Quotients.h, honest]
    rw [hh, hq, hp]
    have : dPoly P g α β * dNextPoly P g α β * (honest P g α β γ).h₀
        + (dPoly P g α β * dNextPoly P g α β * (honest P g α β γ).h₀ + copyPoly P g α β γ)
        + copyPoly P g α β γ
        = (dPoly P g α β * dNextPoly P g α β * (honest P g α β γ).h₀
            + dPoly P g α β * dNextPoly P g α β * (honest P g α β γ).h₀)
          + (copyPoly P g α β γ + copyPoly P g α β γ) := by ring
    rw [this, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  · -- The gate identity: the gate vanishes on the rows.
    have hdvd : P.vRows ∣ gatePoly P g := by
      rw [hE.rows]
      refine prod_X_sub_C_dvd (fun x : P.T => (x : F)) Subtype.val_injective _ fun x => ?_
      rw [gatePoly, gate_eval]
      exact hgate x
    have hq : P.vRows * (honest P g α β γ).qGate = gatePoly P g :=
      EuclideanDomain.mul_div_cancel' hr0 hdvd
    show P.vRows * (dPoly P g α β * dNextPoly P g α β * (honest P g α β γ).qGate
        + P.vCells * (honest P g α β γ).junk) + dPoly P g α β * dNextPoly P g α β * gatePoly P g = 0
    have hj : (honest P g α β γ).junk = 0 := rfl
    rw [hj, mul_zero, add_zero, ← hq]
    have : P.vRows * (dPoly P g α β * dNextPoly P g α β * (honest P g α β γ).qGate)
        = dPoly P g α β * dNextPoly P g α β * (P.vRows * (honest P g α β γ).qGate) := by ring
    rw [this]
    exact CharTwo.add_self_eq_zero _
  · -- The sum: the copies cancel, the public words remain.
    rw [Quotients.top, Finset.sum_congr rfl fun i _ => honest_h₀_eval g α β γ i]
    unfold sumValue
    rw [Finset.sum_add_distrib]
    have hlog := logSum_eq_zero_of_copy P.pt P.σ (cells P g) hcopy α β
    unfold logSum at hlog
    rw [hlog, zero_add]
    refine (P.hPub γ (cells P g)).trans ?_
    exact Finset.sum_congr rfl fun J _ => by rw [hwords J]

theorem accept_algebra {d d' v vR H q qg j copies gt ρ : F} (hne : (d * d' + v) * vR ≠ 0)
    (h1 : d * d' * H + v * q = copies) (h2 : vR * (d * d' * qg + v * j) = d * d' * gt) :
    (1 + ρ) * ((1 + v / (d * d' + v)) * H + v / (d * d' + v) * q)
        + ρ * ((1 + v / (d * d' + v)) * qg + v / (d * d' + v) * j)
      = ((1 + ρ) * copies * vR + ρ * (d * d') * gt) / ((d * d' + v) * vR) := by
  have hden : d * d' + v ≠ 0 := left_ne_zero_of_mul hne
  have hvR0 : vR ≠ 0 := right_ne_zero_of_mul hne
  have he : 1 + v / (d * d' + v) = d * d' / (d * d' + v) := by
    rw [eq_div_iff hden, add_mul, one_mul, div_mul_cancel₀ _ hden, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  rw [he, eq_div_iff hne]
  have : ((1 + ρ) * (d * d' / (d * d' + v) * H + v / (d * d' + v) * q)
        + ρ * (d * d' / (d * d' + v) * qg + v / (d * d' + v) * j)) * ((d * d' + v) * vR)
      = (1 + ρ) * (d * d' * H + v * q) * vR + ρ * (vR * (d * d' * qg + v * j)) := by
    field_simp
  rw [this, h1, h2]
  ring

/-- **A consistent message makes the four claims true**, at every challenge the verifier does
not reject, with the values an honest prover sends. -/
theorem accepts_of_consistent (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F)
    (α β γ t ρ : F) (h : P.Consistent stmt g R α β γ)
    (hne : ((α + (cellPoly P g 0).eval t + β * t) * (α + (cellPoly P g 0).eval t
        + β * P.sigmaPoly.eval t) + P.vCells.eval t) * P.vRows.eval t ≠ 0) :
    P.Accepts stmt g R α β γ t (opened g t) (P.sigmaPoly.eval t) ρ := by
  obtain ⟨hcopy, hgate, htop⟩ := h
  have hcd := congrArg (fun p : F[X] => p.eval t) hcopy
  have hgd := congrArg (fun p : F[X] => p.eval t) hgate
  simp only [copyDefect, copyPoly, gateDefect, gatePoly, dPoly, dNextPoly, eval_add, eval_mul,
    eval_C, eval_X, eval_zero, gate_eval] at hcd hgd
  refine ⟨rfl, rfl, ?_, ?_, htop⟩
  · have e := fun c => cellAt_opened P g t c
    rw [e 0]
    exact hne
  · have e := fun c => cellAt_opened P g t c
    rw [e 0, e 1, e 2, e 3]
    exact accept_algebra hne (CharTwo.add_eq_zero.mp hcd) (CharTwo.add_eq_zero.mp hgd)

end Params

end QuotientSecurity
