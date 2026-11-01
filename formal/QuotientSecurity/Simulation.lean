-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Simulation.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Completeness
import QuotientSecurity.ZeroKnowledge

/-!
# The honest verifier's view is simulated

The witness's row polynomials are over the small field `K`, each committed with a mask: the rows'
vanishing polynomial times three uniform coefficients. Beyond its own challenges the verifier
sees the five values sent and whether its four claims are true. This file proves that this view
has exactly the distribution a simulator without the witness produces: four values uniform in the field the challenge's row lies in, the
wiring's public value, and the verdict the verifier's own nonzero check gives.
-/

set_option linter.unusedSectionVars false

open Polynomial Module

namespace QuotientSecurity

variable {K E : Type} [Field K] [Field E] [Algebra K E]

/-- A mask, as a polynomial: three coefficients on `1, X, X^2 + X`, the first three polynomials
of the novel basis, as the prover lays them in its table. -/
noncomputable def maskPoly (m : Fin 3 → K) : K[X] :=
  C (m 0) + C (m 1) * X + C (m 2) * (X ^ 2 + X)

/-- The same mask on `1, X, X^2`. -/
def rebase (m : Fin 3 → K) : Fin 3 → K := ![m 0, m 1 + m 2, m 2]

theorem rebase_bijective : Function.Bijective (rebase (K := K)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun m => ![m 0, m 1 - m 2, m 2], ?_, ?_⟩
  · intro m; funext i; fin_cases i <;> simp [rebase]
  · intro m; funext i; fin_cases i <;> simp [rebase]

theorem maskPoly_eq (m : Fin 3 → K) :
    maskPoly m = C (rebase m 0) + C (rebase m 1) * X + C (rebase m 2) * X ^ 2 := by
  simp only [maskPoly, rebase, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, C_add]
  ring

/-- The first message: each row polynomial plus the vanishing polynomial times its mask. -/
noncomputable def committed (gK : Fin 4 → K[X]) (van : K[X]) (m : Fin 4 → Fin 3 → K) :
    Params.Witness E :=
  fun j => (gK j + van * maskPoly (m j)).map (algebraMap K E)

theorem committed_comp_eval (gK : Fin 4 → K[X]) (van : K[X]) (m : Fin 4 → Fin 3 → K) (j : Fin 4)
    (x : E) :
    ((committed (E := E) gK van m j).comp rowPoly).eval x
      = maskedValue (aeval (rowPoly.eval x) (gK j)) (aeval (rowPoly.eval x) van) (rowPoly.eval x)
        (rebase (m j)) := by
  rw [eval_comp, committed, eval_map_algebraMap, maskPoly_eq, aeval_masked]

variable [DecidableEq E] [CharP E 2] [Fintype E] (P : Params E)

/-- The masks do not move the cells, the vanishing polynomial being zero on the rows. -/
theorem cells_committed (gK : Fin 4 → K[X]) (van : K[X])
    (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0) (m m' : Fin 4 → Fin 3 → K) :
    P.cells (committed gK van m) = P.cells (committed gK van m') := by
  funext i
  simp only [Params.cells, Params.cellPoly, eval_finsetSum, eval_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [committed_comp_eval, committed_comp_eval, maskedValue, maskedValue, hvan i.1]
  simp

/-- The verifier's own check on what it received: the product it inverts is not zero. -/
def NotRejected (α β t : E) (a : Fin 4 → E) : Prop :=
  ((α + P.cellAt a t 0 + β * t) * (α + P.cellAt a t 0 + β * P.sigmaPoly.eval t)
    + P.vCells.eval t) * P.vRows.eval t ≠ 0

/-- **For an honest prover the verdict is the verifier's own check.** -/
theorem accepts_iff_notRejected (hE : P.Exact) (stmt : Fin P.words → E) (g : Params.Witness E)
    (α β γ t ρ : E) (hsat : P.Sat stmt (P.cells g))
    (hd : ∀ i, α + P.cells g i + β * P.pt i ≠ 0)
    (hd' : ∀ i, α + P.cells g i + β * P.pt (P.σ i) ≠ 0) :
    P.Accepts stmt g (Params.honest P g α β γ) α β γ t (Params.opened g t) (P.sigmaPoly.eval t) ρ
      ↔ NotRejected P α β t (Params.opened g t) := by
  constructor
  · intro h
    exact h.2.2.1
  · intro h
    refine Params.accepts_of_consistent stmt g _ α β γ t ρ
      (Params.honest_consistent hE stmt g α β γ hsat hd hd') ?_
    have e := Params.cellAt_opened P g t 0
    unfold NotRejected at h
    rw [e] at h
    exact h

section View

variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]
  [SampleableType E]

open Classical in
/-- What the verifier sees beyond its challenges: the four values, the wiring's value, and
whether its four claims are true of the two messages. -/
noncomputable def realView (stmt : Fin P.words → E) (gK : Fin 4 → K[X]) (van : K[X])
    (α β γ t ρ : E) : ProbComp ((Fin 4 → E) × E × Bool) :=
  (fun m : Fin 4 → Fin 3 → K =>
    let g : Params.Witness E := committed gK van m
    (Params.opened g t, P.sigmaPoly.eval t,
      decide (P.Accepts stmt g (Params.honest P g α β γ) α β γ t (Params.opened g t)
        (P.sigmaPoly.eval t) ρ))) <$> ($ᵗ (Fin 4 → Fin 3 → K))

open Classical in
/-- The simulator, which has neither the witness nor the masks. -/
noncomputable def simView (α β t : E) : ProbComp ((Fin 4 → E) × E × Bool) :=
  (fun a : Fin 4 → E => (a, P.sigmaPoly.eval t, decide (NotRejected P α β t a))) <$>
    simValues (K := K) (rowPoly.eval t)

/-- **Honest-verifier zero knowledge.** For challenges at which no denominator vanishes on a
cell, and whose row is not a root of the vanishing polynomial, the view of the verifier has
exactly the simulator's distribution. -/
theorem realView_eq_simView (h3 : finrank K E = 3) (hE : P.Exact) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X])
    (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0)))
    (α β γ t ρ : E)
    (hd : ∀ i, α + P.cells (committed gK van 0) i + β * P.pt i ≠ 0)
    (hd' : ∀ i, α + P.cells (committed gK van 0) i + β * P.pt (P.σ i) ≠ 0)
    (hu : aeval (rowPoly.eval t) van ≠ 0)
    (v : (Fin 4 → E) × E × Bool) :
    Pr{let x ← realView P stmt gK van α β γ t ρ}[x = v]
      = Pr{let x ← simView (K := K) P α β t}[x = v] := by
  classical
  obtain ⟨h, hh⟩ : ∃ h : (Fin 4 → E) → (Fin 4 → E) × E × Bool,
      h = fun a => (a, P.sigmaPoly.eval t, decide (NotRejected P α β t a)) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : (Fin 4 → Fin 3 → K) → Fin 4 → E, A = fun m j =>
      maskedValue (aeval (rowPoly.eval t) (gK j)) (aeval (rowPoly.eval t) van) (rowPoly.eval t)
        (m j) := ⟨_, rfl⟩
  obtain ⟨Reb, hReb⟩ : ∃ Reb : (Fin 4 → Fin 3 → K) → Fin 4 → Fin 3 → K,
      Reb = fun m j => rebase (m j) := ⟨_, rfl⟩
  have hRebBij : Function.Bijective Reb := by
    subst hReb
    constructor
    · intro m m' hm
      funext j
      exact rebase_bijective.injective (congrFun hm j)
    · intro m
      choose m' hm' using fun j => rebase_bijective.surjective (m j)
      exact ⟨m', funext hm'⟩
  have hpoint : ∀ m : Fin 4 → Fin 3 → K,
      (Params.opened (committed (E := E) gK van m) t, P.sigmaPoly.eval t,
        decide (P.Accepts stmt (committed gK van m) (Params.honest P (committed gK van m) α β γ)
          α β γ t (Params.opened (committed gK van m) t) (P.sigmaPoly.eval t) ρ))
        = h (A (Reb m)) := by
    intro m
    have hc := cells_committed P gK van hvan m 0
    have hopen : Params.opened (committed (E := E) gK van m) t = A (Reb m) := by
      subst hA hReb
      funext j
      exact committed_comp_eval gK van m j t
    have hiff := accepts_iff_notRejected P hE stmt (committed gK van m) α β γ t ρ
      (by rw [hc]; exact hsat) (by rw [hc]; exact hd) (by rw [hc]; exact hd')
    rw [← hopen, hh]
    exact Prod.ext rfl (Prod.ext rfl (decide_eq_decide.mpr hiff))
  have hview : realView P stmt gK van α β γ t ρ
      = (h ∘ A) <$> (Reb <$> ($ᵗ (Fin 4 → Fin 3 → K))) := by
    unfold realView
    rw [Functor.map_map]
    exact congrArg (· <$> ($ᵗ (Fin 4 → Fin 3 → K))) (funext hpoint)
  have hreb : (Reb <$> ($ᵗ (Fin 4 → Fin 3 → K))) =ᵈ ($ᵗ (Fin 4 → Fin 3 → K) : ProbComp _) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective hRebBij
  have e1 : Pr{let x ← realView P stmt gK van α β γ t ρ}[x = v]
      = Pr{let x ← (h ∘ A) <$> ($ᵗ (Fin 4 → Fin 3 → K))}[x = v] := by
    rw [hview]
    exact (hreb.map (h ∘ A)).prEvent_eq (· = v)
  have e2 : (h ∘ A) <$> ($ᵗ (Fin 4 → Fin 3 → K))
      = h <$> realValues (K := K) (fun j => aeval (rowPoly.eval t) (gK j))
          (aeval (rowPoly.eval t) van) (rowPoly.eval t) := by
    unfold realValues
    rw [Functor.map_map, hA]
    rfl
  have e3 : simView (K := K) P α β t = h <$> simValues (K := K) (rowPoly.eval t) := by
    rw [hh]; rfl
  rw [e1, e2, e3]
  exact ((evalDistEq_iff_forall_prEvent_eq_output.mpr
    (realValues_eq_simValues h3 gK van _ hu)).map h).prEvent_eq (· = v)

end View

end QuotientSecurity
