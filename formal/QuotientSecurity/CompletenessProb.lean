-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/CompletenessProb.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Distance

/-!
# Completeness, as a probability

The honest prover against the random oracle, from any oracle state: the verifier's verdict on
its proof is false with probability at most the zero knowledge bound (a handle the oracle was
asked about, a challenge at which a denominator vanishes on a cell or the masks do not hide) plus
the fraction of points at which the product the verifier inverts is zero.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp Polynomial Module NNReal

namespace QuotientSecurity

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
variable {P : Params E} {H : Type} [SampleableType E] [SampleableType H]
variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]

omit [DecidableEq E] [CharP E 2] [Fintype E] [SampleableType E] [Fintype K] [DecidableEq K]
  [FiniteDimensional K E] [SampleableType K] in
/-- A committed polynomial is as large as its row polynomial or the masked vanishing one. -/
theorem natDegree_committed_le (gK : Fin 4 → K[X]) (van : K[X]) (m : Fin 4 → Fin 3 → K)
    (j : Fin 4) :
    (committed (E := E) gK van m j).natDegree ≤ max (gK j).natDegree (van.natDegree + 2) := by
  have hmask : (maskPoly (m j)).natDegree ≤ 2 := by
    unfold maskPoly
    compute_degree
  unfold committed
  refine natDegree_map_le.trans ((natDegree_add_le _ _).trans (max_le_max le_rfl ?_))
  exact natDegree_mul_le.trans (by omega)

/-- The product the verifier inverts, as a polynomial in the point. -/
noncomputable def rejectPoly (P : Params E) (g : Params.Witness E) (α β : E) : E[X] :=
  (Params.dPoly P g α β * Params.dNextPoly P g α β + P.vCells) * P.vRows

theorem rejectPoly_eval (g : Params.Witness E) (α β t : E) :
    (rejectPoly P g α β).eval t
      = ((α + P.cellAt (Params.opened g t) t 0 + β * t)
          * (α + P.cellAt (Params.opened g t) t 0 + β * P.sigmaPoly.eval t)
        + P.vCells.eval t) * P.vRows.eval t := by
  simp [rejectPoly, Params.dPoly, Params.dNextPoly, Params.cellAt_opened]

theorem rejectPoly_ne_zero (hE : P.Exact) (g : Params.Witness E) (α β : E) (i₀ : P.T × Fin 4)
    (hd : α + P.cells g i₀ + β * P.pt i₀ ≠ 0)
    (hd' : α + P.cells g i₀ + β * P.pt (P.σ i₀) ≠ 0) : rejectPoly P g α β ≠ 0 := by
  refine mul_ne_zero (fun h => ?_) ?_
  · have h' := congrArg (fun p : E[X] => p.eval (P.pt i₀)) h
    simp only [eval_add, eval_mul, eval_zero, Params.dPoly_eval_pt, Params.dNextPoly_eval_pt] at h'
    have hc : P.vCells.eval (P.pt i₀) = 0 := P.hCells i₀.1.1 i₀.1.2 i₀.2
    rw [hc, add_zero] at h'
    exact mul_ne_zero hd hd' h'
  · rw [hE.rows]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _

theorem natDegree_rejectPoly_le (Bd : P.Bounds) (g : Bd.Msg₁) (α β : E) :
    (rejectPoly P g.1 α β).natDegree ≤ Bd.identity := by
  have h1 := Params.natDegree_dPoly_le Bd g α β
  have h2 := Params.natDegree_dNextPoly_le Bd g α β
  have h3 : (Params.dPoly P g.1 α β * Params.dNextPoly P g.1 α β + P.vCells).natDegree
      ≤ max (2 * Bd.denominator) Bd.cells :=
    natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by omega)) (Bd.hCells.trans (by omega))
  unfold rejectPoly Params.Bounds.identity
  exact natDegree_mul_le.trans (by have := Bd.hRows; omega)

/-- Under good challenges, the open experiment's verdict is rarely false. -/
theorem prob_rejected_open (hE : P.Exact) (c₀ : (ofFn (ZAnswer P H)).QueryCache)
    (stmt : Fin P.words → E) (gK : Fin 4 → K[X]) (van : K[X])
    (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0))) (i₀ : P.T × Fin 4) (Bd : P.Bounds)
    (hg : ∀ m j, (committed (E := E) gK van m j).natDegree ≤ Bd.witness) :
    Pr{let o ← openNI c₀ stmt gK van}[Good (P := P) gK van o.1.ch o.1.t ∧ o.1.verdict = false]
      ≤ (Bd.identity : ENNReal) / (Fintype.card E : ENNReal) := by
  classical
  unfold openNI challenges
  simp only [bind_assoc, pure_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun m => prEvent_bind_le_of_forall_le _ _ _ fun c₁ =>
    prEvent_bind_le_of_forall_le _ _ _ fun c₂ => prEvent_bind_le_of_forall_le _ _ _ fun ch => ?_
  have hcells := cells_committed P gK van hvan m 0
  by_cases hgood : (∀ i, ch.1 + P.cells (committed gK van 0) i + ch.2.1 * P.pt i ≠ 0) ∧
      (∀ i, ch.1 + P.cells (committed gK van 0) i + ch.2.1 * P.pt (P.σ i) ≠ 0)
  · have hd : ∀ i, ch.1 + P.cells (committed gK van m) i + ch.2.1 * P.pt i ≠ 0 := by
      rw [hcells]; exact hgood.1
    have hd' : ∀ i, ch.1 + P.cells (committed gK van m) i + ch.2.1 * P.pt (P.σ i) ≠ 0 := by
      rw [hcells]; exact hgood.2
    have hsat' : P.Sat stmt (P.cells (committed gK van m)) := by rw [hcells]; exact hsat
    have hR0 := rejectPoly_ne_zero hE (committed gK van m) ch.1 ch.2.1 i₀ (hd i₀) (hd' i₀)
    have hRdeg := natDegree_rejectPoly_le Bd ⟨committed gK van m, hg m⟩ ch.1 ch.2.1
    refine (prEvent_bind_le_prEvent_of_support _ _
      (fun t : E => (rejectPoly P (committed gK van m) ch.1 ch.2.1).eval t = 0) _
      fun t _ ht => prEvent_eq_zero_of_forall_mem_support _ _ fun y hy => ?_).trans ?_
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
      obtain ⟨ρ, -, rfl⟩ := hy
      rintro ⟨-, hv⟩
      refine ht ?_
      have hacc : ¬ P.Accepts stmt (committed gK van m)
          (Params.honest P (committed gK van m) ch.1 ch.2.1 ch.2.2) ch.1 ch.2.1 ch.2.2 t
          (Params.opened (committed gK van m) t) (P.sigmaPoly.eval t) ρ := by
        have : (viewAt stmt gK van m ch t ρ).2.2 = false := hv
        simpa [viewAt] using this
      rw [accepts_iff_notRejected P hE stmt _ ch.1 ch.2.1 ch.2.2 t ρ hsat' hd hd'] at hacc
      rw [rejectPoly_eval]
      exact not_not.mp hacc
    · rw [SampleableType.prEvent_uniformSample]
      refine ENNReal.div_le_div_right ?_ _
      have hsub : (Finset.univ.filter fun t : E =>
          (rejectPoly P (committed gK van m) ch.1 ch.2.1).eval t = 0)
          ⊆ (rejectPoly P (committed gK van m) ch.1 ch.2.1).roots.toFinset := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [Multiset.mem_toFinset, mem_roots hR0, IsRoot.def]
        exact ht.2
      exact_mod_cast (Finset.card_le_card hsub).trans
        ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hRdeg))
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun y hy => ?_) zero_le
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨t, -, ρ, -, rfl⟩ := hy
    rintro ⟨hG, -⟩
    exact hgood ⟨hG.1, hG.2.1⟩

variable [Fintype H] [DecidableEq H]

/-- **Completeness.** From any oracle state, the honest prover's proof gets a false verdict with
probability at most the zero knowledge bound plus `identity / q`. -/
theorem completeness_prob (hE : P.Exact) (c₀ : (ofFn (ZAnswer P H)).QueryCache)
    (stmt : Fin P.words → E) (U : Finset H) (hU : ∀ c₁, c₁ ∉ U → Fresh c₀ stmt c₁)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan0 : van ≠ 0)
    (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0))) (i₀ : P.T × Fin 4) (Bd : P.Bounds)
    (hg : ∀ m j, (committed (E := E) gK van m j).natDegree ≤ Bd.witness) :
    Pr{let o ← realNI c₀ stmt gK van}[o.1.verdict = false]
      ≤ zkBound P van U + (Bd.identity : ENNReal) / (Fintype.card E : ENNReal) := by
  classical
  have hrealFresh : Pr{let o ← realNI c₀ stmt gK van}[¬ Fresh c₀ stmt o.1.c₁]
      ≤ (U.card : ENNReal) / (Fintype.card H : ENNReal) := by
    unfold realNI
    refine prEvent_bind_le_of_forall_le _ _ _ fun m => ?_
    refine prob_handle_le U (Fresh c₀ stmt) hU _
      (fun o : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache => o.1.c₁) fun c₁ y hy => ?_
    rw [mem_support_bind_iff] at hy
    obtain ⟨c₂, -, hy⟩ := hy
    exact run_proverRO_handle c₀ stmt gK van m c₁ c₂ y hy
  have hopenGood : Pr{let o ← openNI c₀ stmt gK van}[¬ Good (P := P) gK van o.1.ch o.1.t]
      ≤ (zkError P van : ENNReal) := by
    unfold openNI
    refine prEvent_bind_le_of_forall_le _ _ _ fun m => ?_
    refine prob_not_good_le gK van hvan0 _ fun c o ho => ?_
    rw [support_pure, Set.mem_singleton_iff] at ho
    subst ho
    exact ⟨rfl, rfl⟩
  have h1 : Pr{let o ← realNI c₀ stmt gK van}[o.1.verdict = false]
      ≤ Pr{let o ← realNI c₀ stmt gK van}[Fresh c₀ stmt o.1.c₁ ∧ o.1.verdict = false]
        + Pr{let o ← realNI c₀ stmt gK van}[¬ Fresh c₀ stmt o.1.c₁] :=
    prEvent_le_add_of_imp_or fun o _ ho => by
      by_cases hf : Fresh c₀ stmt o.1.c₁
      · exact Or.inl ⟨hf, ho⟩
      · exact Or.inr hf
  have h2 := probEvent_and_congr (realNI c₀ stmt gK van) (openNI c₀ stmt gK van)
    (fun o => Fresh c₀ stmt o.1.c₁) (fun o => o.1.verdict = false)
    (fun o hf => realNI_eq_openNI c₀ stmt gK van o hf)
  have h3 : Pr{let o ← openNI c₀ stmt gK van}[Fresh c₀ stmt o.1.c₁ ∧ o.1.verdict = false]
      ≤ Pr{let o ← openNI c₀ stmt gK van}[
            Good (P := P) gK van o.1.ch o.1.t ∧ o.1.verdict = false]
        + Pr{let o ← openNI c₀ stmt gK van}[¬ Good (P := P) gK van o.1.ch o.1.t] :=
    prEvent_le_add_of_imp_or fun o _ ho => by
      by_cases hG : Good (P := P) gK van o.1.ch o.1.t
      · exact Or.inl ⟨hG, ho.2⟩
      · exact Or.inr hG
  rw [h2] at h1
  refine (h1.trans (add_le_add (h3.trans (add_le_add
    (prob_rejected_open hE c₀ stmt gK van hvan hsat i₀ Bd hg) hopenGood)) hrealFresh)).trans
    (le_of_eq ?_)
  unfold zkBound
  ring

end QuotientSecurity
