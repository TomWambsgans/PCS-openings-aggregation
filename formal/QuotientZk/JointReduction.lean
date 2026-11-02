-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Simulation
import QuotientSecurity.Distance
import QuotientZk.JointCore

/-!
# The reduction's messages in the joint view (F1)

The reduction's messages are the four values `a_j = G_j(r)` of the masked witness polynomials at
the row `r = t^4 + t` of the challenge `t`, and the wiring's value `σ(t)`, which is public: the
pair `redMsgs`, a function of the masks `m` (`committed gK van m`). F1 (`realView_eq_simView`)
proves that at every challenge good for the witness (`Good`: no denominator vanishes on a cell, and
the vanishing polynomial is not zero at the row) the four values are uniform in `E`, or in `K`
when the row lies in `K`, whatever the witness.

`simRed` is that simulator as a plain definition: it reads `t` only, decides whether the row lies
in `K` with a public test `inK`, and computes `σ(t)` with a public evaluation `sigmaAt` of the
wiring polynomial (F1's `simView` is `noncomputable`: it decides membership classically and
evaluates a Mathlib polynomial). `redMsgs_evalDistEq` is F1's theorem for it, and
`prob_not_good_le` F1's bound on the bad challenges, `zkError = (2N + 4 deg) / |E|`.
-/

open OracleComp Polynomial Module QuotientSecurity
open scoped NNReal

namespace QuotientZk.Joint

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]

/-- The row of a point: `rowPoly = X^4 + X` at `t`. -/
def rowOf (t : E) : E := t ^ 4 + t

theorem rowPoly_eval (t : E) : (rowPoly : E[X]).eval t = rowOf t := by
  simp [rowPoly, rowOf]

/-- **The reduction's messages**: the four values at `t` of the committed polynomials (the witness's
row polynomials plus the vanishing polynomial times the masks `m`), and the wiring's value. -/
noncomputable def redMsgs (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (t : E)
    (m : Fin 4 → Fin 3 → K) : (Fin 4 → E) × E :=
  (Params.opened (committed (E := E) gK van m) t, P.sigmaPoly.eval t)

section Sim

variable [SampleableType K] [SampleableType E]

/-- The simulator's four values: uniform in `K` (embedded) when the row lies in `K`, which the
public test `inK` decides, and uniform in `E` otherwise. -/
def simValuesC (inK : E → Bool) (r : E) : ProbComp (Fin 4 → E) :=
  if inK r then (fun (a : Fin 4 → K) (j : Fin 4) => algebraMap K E (a j)) <$> ($ᵗ (Fin 4 → K))
  else $ᵗ (Fin 4 → E)

/-- **The simulator of the reduction's messages**, from `t` only: the four values, and the wiring
polynomial's value `sigmaAt t`. -/
def simRed (inK : E → Bool) (sigmaAt : E → E) (t : E) : ProbComp ((Fin 4 → E) × E) :=
  (fun a => (a, sigmaAt t)) <$> simValuesC (K := K) inK (rowOf t)

end Sim

section Theorem

variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]

/-- `simRed` is F1's simulator. -/
theorem simValues_eq_simValuesC (inK : E → Bool)
    (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E)) (t : E) :
    simValues (K := K) ((rowPoly : E[X]).eval t) = simValuesC (K := K) inK (rowOf t) := by
  classical
  rw [rowPoly_eval]
  unfold simValues simValuesC
  by_cases hr : rowOf t ∈ Set.range (algebraMap K E)
  · rw [if_pos hr, if_pos ((hinK _).mpr hr)]
  · rw [if_neg hr, if_neg fun h => hr ((hinK _).mp h)]

/-- **F1 for the reduction's messages.** At a challenge good for the witness, the messages under
uniform masks have the distribution of `simRed`. -/
theorem redMsgs_evalDistEq (P : Params E) (h3 : finrank K E = 3) (hE : P.Exact)
    (stmt : Fin P.words → E) (gK : Fin 4 → K[X]) (van : K[X])
    (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0)))
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P.sigmaPoly.eval t)
    (ch : E × E × E) (t : E) (hgood : Good (P := P) gK van ch t) :
    redMsgs P gK van t <$> ($ᵗ (Fin 4 → Fin 3 → K)) =ᵈ simRed (K := K) inK sigmaAt t := by
  classical
  obtain ⟨hd, hd', hu⟩ := hgood
  have hEq : realView P stmt gK van ch.1 ch.2.1 ch.2.2 t 0 =ᵈ simView (K := K) P ch.1 ch.2.1 t :=
    evalDistEq_iff_forall_prEvent_eq_output.mpr
      (realView_eq_simView P h3 hE stmt gK van hvan hsat ch.1 ch.2.1 ch.2.2 t 0 hd hd' hu)
  have hmap := hEq.map (fun x => (x.1, x.2.1))
  have e1 : (fun x : (Fin 4 → E) × E × Bool => (x.1, x.2.1)) <$>
      realView P stmt gK van ch.1 ch.2.1 ch.2.2 t 0 =
        redMsgs P gK van t <$> ($ᵗ (Fin 4 → Fin 3 → K)) := by
    unfold realView
    rw [Functor.map_map]
    rfl
  have e2 : (fun x : (Fin 4 → E) × E × Bool => (x.1, x.2.1)) <$>
      simView (K := K) P ch.1 ch.2.1 t =
        (fun a => (a, P.sigmaPoly.eval t)) <$> simValues (K := K) ((rowPoly : E[X]).eval t) := by
    unfold simView
    rw [Functor.map_map]
  rw [← e1]
  refine hmap.trans ?_
  rw [e2, simValues_eq_simValuesC inK hinK t, simRed, hsig]

/-- **F1's bad challenges**: for uniform `((α, β, γ), t)`, not good with probability at most
`zkError = (2N + 4 deg van) / |E|`. -/
theorem prob_not_good_le (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (hvan0 : van ≠ 0) :
    Pr{let c ← $ᵗ ((E × E × E) × E)}[¬ Good (P := P) gK van c.1 c.2] ≤
      (zkError P van : ENNReal) := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have h := card_not_good_le (P := P) gK van hvan0
  have hq : 0 < Fintype.card E := Fintype.card_pos
  have hcard : Fintype.card ((E × E × E) × E) = Fintype.card E ^ (3 + 1) := by
    simp only [Fintype.card_prod]
    ring
  rw [hcard]
  unfold zkError
  exact_mod_cast card_div_le hq h

/-- At the protocol's sizes (`2^24` cells, `deg van ≤ 2^22`, `|E| = 2^192`), `zkError` is at most
`3·2^24 / 2^192 < 2^-166`. -/
theorem zkError_le_166 (P : Params E) (hq : Fintype.card E = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (van : K[X]) (hdeg : van.natDegree ≤ 2 ^ 22) : (zkError P van : ENNReal) ≤ 1 / 2 ^ 166 := by
  unfold zkError
  have h : ((2 * P.nCells + 4 * van.natDegree : ℕ) : ℝ≥0) / (Fintype.card E : ℝ≥0) ≤ 1 / 2 ^ 166 := by
    have hq' : (0 : ℝ≥0) < (Fintype.card E : ℝ≥0) := by exact_mod_cast Fintype.card_pos
    rw [div_le_div_iff₀ hq' (by positivity), one_mul, hq, hN]
    have : (2 * 2 ^ 24 + 4 * van.natDegree) * 2 ^ 166 ≤ 2 ^ 192 := by
      calc (2 * 2 ^ 24 + 4 * van.natDegree) * 2 ^ 166 ≤ (2 * 2 ^ 24 + 4 * 2 ^ 22) * 2 ^ 166 := by
            gcongr
        _ ≤ 2 ^ 192 := by norm_num
    exact_mod_cast this
  calc ((((2 * P.nCells + 4 * van.natDegree : ℕ) : ℝ≥0) / (Fintype.card E : ℝ≥0) : ℝ≥0) : ENNReal)
      ≤ ((1 / 2 ^ 166 : ℝ≥0) : ENNReal) := ENNReal.coe_le_coe.mpr h
    _ = 1 / 2 ^ 166 := by simp

end Theorem

end QuotientZk.Joint
