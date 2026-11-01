-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/RoundThree.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Cells

/-!
# The third challenge

If the identities do not hold at `t`, then whatever five values the prover sends, the verifier's
claims are true for at most three `ρ`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] (P : Params F)

/-- The weights of the witness claim separate four values: a nonzero difference passes for at
most three `ρ`. -/
theorem card_opening_le (δ : Fin 4 → F) (hδ : δ ≠ 0) :
    (univ.filter fun ρ : F => ∑ j, Params.opening ρ j * δ j = 0).card ≤ 3 := by
  classical
  set Q : F[X] := C (δ 0) + C (δ 0 + δ 1) * X + C (δ 0 + δ 2) * X ^ 2
    + C (δ 0 + δ 1 + δ 2 + δ 3) * X ^ 3 with hQ
  have heval : ∀ ρ : F, Q.eval ρ = ∑ j, Params.opening ρ j * δ j := by
    intro ρ
    simp only [hQ, Params.opening, Fin.sum_univ_four, eval_add, eval_mul, eval_C, eval_X,
      eval_pow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hδ
    have c0 := congrArg (fun p : F[X] => p.coeff 0) h
    have c1 := congrArg (fun p : F[X] => p.coeff 1) h
    have c2 := congrArg (fun p : F[X] => p.coeff 2) h
    have c3 := congrArg (fun p : F[X] => p.coeff 3) h
    simp only [hQ, coeff_add, coeff_C_mul, coeff_C_zero, coeff_X_pow, coeff_X, coeff_zero,
      coeff_C] at c0 c1 c2 c3
    norm_num at c0 c1 c2 c3
    have d1 : δ 1 = 0 := by simpa [c0] using c1
    have d2 : δ 2 = 0 := by simpa [c0] using c2
    have d3 : δ 3 = 0 := by simpa [c0, d1, d2] using c3
    funext j
    fin_cases j <;> simp [c0, d1, d2, d3]
  have hdeg : Q.natDegree ≤ 3 := by rw [hQ]; compute_degree
  calc _ ≤ Q.roots.toFinset.card := Finset.card_le_card fun ρ hρ => by
        rw [Finset.mem_filter] at hρ
        rw [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def, heval]
        exact hρ.2
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' Q
    _ ≤ 3 := hdeg

namespace Params

/-- The four values an honest prover sends at `t`. -/
noncomputable def opened (g : Witness F) (t : F) : Fin 4 → F :=
  fun j => ((g j).comp rowPoly).eval t

theorem cellAt_opened (g : Witness F) (t : F) (c : Fin 4) :
    cellAt P (opened g t) t c = (cellPoly P g c).eval t := by
  simp only [cellAt, opened, cellPoly, eval_finsetSum, eval_mul, eval_comp, eval_add, eval_X,
    eval_C]

/-- With the true five values, an accepted `ρ` is a root of an affine function that the two
identities' defects at `t` define. -/
theorem accepts_opened (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F)
    (α β γ t ρ : F)
    (h : P.Accepts stmt g R α β γ t (opened g t) (P.sigmaPoly.eval t) ρ) :
    P.vRows.eval t ≠ 0 ∧ R.top P = P.target stmt γ ∧
      (1 + ρ) * (P.vRows.eval t * (copyDefect P g R α β γ).eval t)
        + ρ * (gateDefect P g R α β).eval t = 0 := by
  obtain ⟨-, -, hne, heq, htop⟩ := h
  simp only [cellAt_opened] at hne heq
  set x := (cellPoly P g 0).eval t with hx
  set d := α + x + β * t with hd
  set d' := α + x + β * P.sigmaPoly.eval t with hd'
  set v := P.vCells.eval t with hv
  set vR := P.vRows.eval t with hvR
  set gt := gate x ((cellPoly P g 1).eval t) ((cellPoly P g 2).eval t)
    ((cellPoly P g 3).eval t) with hgt
  have hden : d * d' + v ≠ 0 := left_ne_zero_of_mul hne
  have hvR0 : vR ≠ 0 := right_ne_zero_of_mul hne
  refine ⟨hvR0, htop, ?_⟩
  have he : 1 + v / (d * d' + v) = d * d' / (d * d' + v) := by
    rw [eq_div_iff hden, add_mul, one_mul, div_mul_cancel₀ _ hden, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  rw [he] at heq
  set H := (R.h P).eval t
  have hmul := congrArg (fun z => z * ((d * d' + v) * vR)) heq
  simp only [div_mul_cancel₀ _ hne] at hmul
  have hl : ((1 + ρ) * (d * d' / (d * d' + v) * H + v / (d * d' + v) * R.q.eval t)
        + ρ * (d * d' / (d * d' + v) * R.qGate.eval t + v / (d * d' + v) * R.junk.eval t))
        * ((d * d' + v) * vR)
      = (1 + ρ) * (d * d' * H + v * R.q.eval t) * vR
        + ρ * (d * d' * R.qGate.eval t + v * R.junk.eval t) * vR := by
    field_simp
  rw [hl] at hmul
  have hcd : (copyDefect P g R α β γ).eval t
      = d * d' * H + v * R.q.eval t + (d + d' + (P.pub γ).eval t * x * (d * d')) := by
    simp only [copyDefect, copyPoly, dPoly, dNextPoly, eval_add, eval_mul, eval_C, eval_X]
    rfl
  have hgd : (gateDefect P g R α β).eval t
      = vR * (d * d' * R.qGate.eval t + v * R.junk.eval t) + d * d' * gt := by
    simp only [gateDefect, gatePoly, dPoly, dNextPoly, eval_add, eval_mul, eval_C, eval_X,
      gate_eval]
    rfl
  rw [hcd, hgd]
  have : (1 + ρ) * (vR * (d * d' * H + v * R.q.eval t + (d + d' + (P.pub γ).eval t * x * (d * d'))))
        + ρ * (vR * (d * d' * R.qGate.eval t + v * R.junk.eval t) + d * d' * gt)
      = ((1 + ρ) * (d * d' * H + v * R.q.eval t) * vR
          + ρ * (d * d' * R.qGate.eval t + v * R.junk.eval t) * vR)
        + ((1 + ρ) * (d + d' + (P.pub γ).eval t * x * (d * d')) * vR + ρ * (d * d') * gt) := by
    ring
  rw [this, hmul]
  exact CharTwo.add_self_eq_zero _

open Classical in
/-- **The third challenge.** If the identities do not hold at `t`, the verifier's four claims are
true for at most three `ρ`, whatever the prover sends. -/
theorem card_accepts_le (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F)
    (α β γ t : F) (h : ¬ P.ConsistentAt stmt g R α β γ t) (a : Fin 4 → F) (s : F) :
    (univ.filter fun ρ : F => P.Accepts stmt g R α β γ t a s ρ).card ≤ 3 := by
  by_cases ha : a = opened g t
  · by_cases hs : P.sigmaPoly.eval t = s
    · subst ha hs
      set A := P.vRows.eval t * (copyDefect P g R α β γ).eval t with hA
      set B := (gateDefect P g R α β).eval t with hB
      have hsub : (univ.filter fun ρ : F =>
          P.Accepts stmt g R α β γ t (opened g t) (P.sigmaPoly.eval t) ρ) ⊆ {A / (A + B)} := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hvR, htop, hroot⟩ := P.accepts_opened stmt g R α β γ t ρ hρ.2
        have hAB : A + B ≠ 0 := by
          intro h0
          have hA0 : A = 0 := by
            have : (1 + ρ) * A + ρ * B = A + ρ * (A + B) := by ring
            rw [this, h0, mul_zero, add_zero] at hroot
            exact hroot
          have hB0 : B = 0 := by rw [hA0, zero_add] at h0; exact h0
          exact h ⟨(mul_eq_zero.mp hA0).resolve_left hvR, hB0, htop⟩
        rw [Finset.mem_singleton, eq_div_iff hAB]
        have : (1 + ρ) * A + ρ * B = ρ * (A + B) + A := by ring
        rw [this] at hroot
        exact CharTwo.add_eq_zero.mp hroot
      exact (Finset.card_le_card hsub).trans (by simp)
    · have : (univ.filter fun ρ : F => P.Accepts stmt g R α β γ t a s ρ) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun ρ _ hρ => hs hρ.2.1
      rw [this]; simp
  · set δ : Fin 4 → F := fun j => opened g t j + a j with hδ
    have hδ0 : δ ≠ 0 := by
      intro h0
      apply ha
      funext j
      exact (CharTwo.add_eq_zero.mp (congrFun h0 j)).symm
    refine le_trans (Finset.card_le_card fun ρ hρ => ?_) (card_opening_le δ hδ0)
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 := hρ.2.1
    have : ∑ j, opening ρ j * δ j
        = ∑ j, opening ρ j * ((g j).comp rowPoly).eval t + ∑ j, opening ρ j * a j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hδ]; simp [opened]; ring
    rw [this, h1]
    exact CharTwo.add_self_eq_zero _

end Params

end QuotientSecurity
