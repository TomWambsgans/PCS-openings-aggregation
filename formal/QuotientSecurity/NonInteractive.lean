-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/NonInteractive.lean. MIT OR Apache-2.0; see NOTICE.md.
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import QuotientSecurity.Simulation
import QuotientSecurity.RoundOne

/-!
# Zero knowledge of the non-interactive proof, in the random-oracle model

Commitments are ideal and hiding: a commitment is a uniformly random handle, and the verifier
learns of the tables only whether its four claims are true. The transcript's hash is a random
oracle on what it has absorbed: the statement and the handles, then the five values.

The real experiment runs the honest prover against a lazily sampled oracle that may already
hold answers (whatever anyone asked of it before, the statement and the witness possibly chosen
from them) and outputs the proof, the verdict, the challenges and the oracle's final table. The simulator has no witness:
it samples the handles, the challenges and four values (uniform in the field the row of `t`
lies in), computes the verdict from the verifier's
own check, and programs the oracle with its challenges. The two outputs have the same
probability at every outcome whose first handle is fresh (the oracle was never asked about it)
and whose challenges are good for the witness: no denominator vanishes on a cell, and the row of
`t` is not a root of the rows' vanishing polynomial.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp Polynomial Module

namespace QuotientSecurity

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
variable (P : Params E) (H : Type)

/-- What the hash has absorbed when it gives a challenge: the statement and one handle, both
handles, then also the five values. -/
inductive ZKey
  | first (stmt : Fin P.words → E) (c₁ : H)
  | second (stmt : Fin P.words → E) (c₁ c₂ : H)
  | third (stmt : Fin P.words → E) (c₁ c₂ : H) (a : Fin 4 → E) (s : E)

def ZAnswer : ZKey P H → Type
  | .first .. => E × E × E
  | .second .. => E
  | .third .. => E

noncomputable instance : DecidableEq (ZKey P H) := Classical.decEq _

instance [SampleableType E] : ∀ k, SampleableType (ZAnswer P H k)
  | .first .. => (inferInstance : SampleableType (E × E × E))
  | .second .. => (inferInstance : SampleableType E)
  | .third .. => (inferInstance : SampleableType E)

/-- A proof with its verdict and the challenges the oracle gave. -/
structure Outcome where
  c₁ : H
  c₂ : H
  a : Fin 4 → E
  s : E
  verdict : Bool
  ch : E × E × E
  t : E
  ρ : E

variable {P H}

/-- The oracle's table after a proof: what it held, and the proof's three challenges. -/
noncomputable def table (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (c₁ c₂ : H) (a : Fin 4 → E) (s : E) (ch : E × E × E) (t ρ : E) :
    (ofFn (ZAnswer P H)).QueryCache :=
  ((c₀.cacheQuery (ZKey.first stmt c₁) ch).cacheQuery (ZKey.second stmt c₁ c₂) t).cacheQuery
    (ZKey.third stmt c₁ c₂ a s) ρ

/-- What a view of the interactive proof becomes: the outcome and the oracle's table. -/
noncomputable def assemble (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (c : H × H × (E × E × E) × E × E) (v : (Fin 4 → E) × E × Bool) :
    Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache :=
  (⟨c.1, c.2.1, v.1, v.2.1, v.2.2, c.2.2.1, c.2.2.2.1, c.2.2.2.2⟩,
    table c₀ stmt c.1 c.2.1 v.1 v.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)

/-- A handle is fresh for an oracle state: the oracle holds no answer for a hash input that
starts with the statement and this handle. -/
def Fresh (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E) (c₁ : H) : Prop :=
  c₀ (ZKey.first stmt c₁) = none ∧ (∀ c₂, c₀ (ZKey.second stmt c₁ c₂) = none) ∧
    ∀ c₂ a s, c₀ (ZKey.third stmt c₁ c₂ a s) = none

variable [SampleableType E] [SampleableType H]

/-- One query of a key the oracle has not seen draws its answer and records it. -/
theorem run_query_bind_fresh {α : Type} (k : ZKey P H)
    (f : ZAnswer P H k → OracleComp (ofFn (ZAnswer P H)) α)
    (c : (ofFn (ZAnswer P H)).QueryCache) (hc : c k = none) :
    (simulateQ randomOracle (liftM ((ofFn (ZAnswer P H)).query k) >>= f)).run c
      = ($ᵗ (ZAnswer P H k)) >>= fun u => (simulateQ randomOracle (f u)).run (c.cacheQuery k u) := by
  rw [simulateQ_query_bind, StateT.run_bind]
  have h := randomOracle.run_eq (spec₀ := ofFn (ZAnswer P H)) k c
  rw [hc] at h
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map] at h ⊢
  erw [h]
  simp [bind_assoc]

/-- Whatever the oracle holds, an output of a query followed by `f` is an output of `f` at some
answer and some oracle state. -/
theorem support_run_query_bind {α : Type} (k : ZKey P H)
    (f : ZAnswer P H k → OracleComp (ofFn (ZAnswer P H)) α)
    (c : (ofFn (ZAnswer P H)).QueryCache) (y : α × (ofFn (ZAnswer P H)).QueryCache)
    (hy : y ∈ support ((simulateQ randomOracle
      (liftM ((ofFn (ZAnswer P H)).query k) >>= f)).run c)) :
    ∃ u cNext, y ∈ support ((simulateQ randomOracle (f u)).run cNext) := by
  rw [simulateQ_query_bind, StateT.run_bind] at hy
  have h := randomOracle.run_eq (spec₀ := ofFn (ZAnswer P H)) k c
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map] at h hy
  erw [h] at hy
  cases hck : c k with
  | none =>
    rw [hck] at hy
    simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hy
    obtain ⟨u, -, hu⟩ := hy
    exact ⟨u, _, hu⟩
  | some u =>
    rw [hck] at hy
    simp only [pure_bind] at hy
    exact ⟨u, _, hy⟩

section Experiments

variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]

/-- The interactive view at given masks: the four values, the wiring's value, the verdict. -/
noncomputable def viewAt (stmt : Fin P.words → E) (gK : Fin 4 → K[X]) (van : K[X])
    (m : Fin 4 → Fin 3 → K) (ch : E × E × E) (t ρ : E) : (Fin 4 → E) × E × Bool :=
  let g : Params.Witness E := committed gK van m
  (Params.opened g t, P.sigmaPoly.eval t,
    @decide (P.Accepts stmt g (Params.honest P g ch.1 ch.2.1 ch.2.2) ch.1 ch.2.1 ch.2.2 t
      (Params.opened g t) (P.sigmaPoly.eval t) ρ) (Classical.propDecidable _))

/-- The honest prover, its masks and handles chosen, against the oracle. -/
noncomputable def proverRO (stmt : Fin P.words → E) (gK : Fin 4 → K[X]) (van : K[X])
    (m : Fin 4 → Fin 3 → K) (c₁ c₂ : H) :
    OracleComp (ofFn (ZAnswer P H)) (Outcome (E := E) H) :=
  liftM ((ofFn (ZAnswer P H)).query (ZKey.first stmt c₁)) >>= fun (ch : E × E × E) =>
  liftM ((ofFn (ZAnswer P H)).query (ZKey.second stmt c₁ c₂)) >>= fun (t : E) =>
  liftM ((ofFn (ZAnswer P H)).query (ZKey.third stmt c₁ c₂
    (viewAt stmt gK van m ch t 0).1 (viewAt stmt gK van m ch t 0).2.1)) >>= fun (ρ : E) =>
  pure ⟨c₁, c₂, (viewAt stmt gK van m ch t ρ).1, (viewAt stmt gK van m ch t ρ).2.1,
    (viewAt stmt gK van m ch t ρ).2.2, ch, t, ρ⟩

/-- **The real experiment**: masks and handles, then the prover against the random oracle in
the state `c₀`. It outputs the outcome and the oracle's table. -/
noncomputable def realNI (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) :
    ProbComp (Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache) :=
  ($ᵗ (Fin 4 → Fin 3 → K)) >>= fun m => ($ᵗ H) >>= fun c₁ => ($ᵗ H) >>= fun c₂ =>
    (simulateQ randomOracle (proverRO stmt gK van m c₁ c₂)).run c₀

/-- The handles and the three challenges, uniform. -/
noncomputable def challenges : ProbComp (H × H × (E × E × E) × E × E) :=
  ($ᵗ H) >>= fun c₁ => ($ᵗ H) >>= fun c₂ => ($ᵗ (E × E × E)) >>= fun ch =>
    ($ᵗ E) >>= fun t => ($ᵗ E) >>= fun ρ => pure (c₁, c₂, ch, t, ρ)

open Classical in
/-- **The simulator**: no witness. It draws the handles, the challenges and four values, takes
the verifier's own check for the verdict, and programs the oracle with its challenges. -/
noncomputable def simNI (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E) :
    ProbComp (Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache) :=
  (challenges (E := E) (H := H)) >>= fun c =>
    simValues (K := K) (rowPoly.eval c.2.2.2.1) >>= fun a =>
    pure (assemble c₀ stmt c
      (a, P.sigmaPoly.eval c.2.2.2.1, decide (NotRejected P c.2.2.1.1 c.2.2.1.2.1 c.2.2.2.1 a)))

/-- The real experiment with the oracle's three answers drawn in the open, as it runs when the
first handle is fresh. -/
noncomputable def openNI (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) :
    ProbComp (Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache) :=
  ($ᵗ (Fin 4 → Fin 3 → K)) >>= fun m => (challenges (E := E) (H := H)) >>= fun c =>
    pure (assemble c₀ stmt c (viewAt stmt gK van m c.2.2.1 c.2.2.2.1 c.2.2.2.2))

/-- With a fresh first handle, the prover's three queries are three fresh draws. -/
theorem run_proverRO_fresh (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (m : Fin 4 → Fin 3 → K) (c₁ c₂ : H)
    (hf : Fresh c₀ stmt c₁) :
    (simulateQ randomOracle (proverRO stmt gK van m c₁ c₂)).run c₀
      = ($ᵗ (E × E × E)) >>= fun ch => ($ᵗ E) >>= fun t => ($ᵗ E) >>= fun ρ =>
          pure (assemble c₀ stmt (c₁, c₂, ch, t, ρ) (viewAt stmt gK van m ch t ρ)) := by
  obtain ⟨h1, h2, h3⟩ := hf
  unfold proverRO
  refine (run_query_bind_fresh (ZKey.first stmt c₁) _ c₀ h1).trans ?_
  refine bind_congr fun ch => ?_
  refine (run_query_bind_fresh (ZKey.second stmt c₁ c₂) _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (by intro h; cases h)]; exact h2 c₂)).trans ?_
  refine bind_congr fun t => ?_
  refine (run_query_bind_fresh (ZKey.third stmt c₁ c₂ _ _) _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (by intro h; cases h),
      QueryCache.cacheQuery_of_ne _ _ (by intro h; cases h)]; exact h3 c₂ _ _)).trans ?_
  refine bind_congr fun ρ => ?_
  rfl

/-- Whatever the oracle holds, the prover's outcome carries its first handle. -/
theorem run_proverRO_handle (c : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (m : Fin 4 → Fin 3 → K) (c₁ c₂ : H)
    (y : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache)
    (hy : y ∈ support ((simulateQ randomOracle (proverRO stmt gK van m c₁ c₂)).run c)) :
    y.1.c₁ = c₁ := by
  unfold proverRO at hy
  obtain ⟨ch, ca, hy⟩ := support_run_query_bind _ _ _ _ hy
  obtain ⟨t, cb, hy⟩ := support_run_query_bind _ _ _ _ hy
  obtain ⟨ρ, cc, hy⟩ := support_run_query_bind _ _ _ _ hy
  rw [simulateQ_pure] at hy
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
  rw [hy]

/-- At an outcome whose first handle is fresh, the real experiment is the open one. -/
theorem realNI_eq_openNI (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X])
    (o : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache) (hf : Fresh c₀ stmt o.1.c₁) :
    Pr{let x ← realNI c₀ stmt gK van}[x = o] = Pr{let x ← openNI c₀ stmt gK van}[x = o] := by
  unfold realNI openNI challenges
  simp only [bind_assoc, pure_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun m => prEvent_bind_congr _ _ _ _ _ fun c₁ => ?_
  by_cases hc : o.1.c₁ = c₁
  · rw [hc] at hf
    refine prEvent_bind_congr _ _ _ _ _ fun c₂ => ?_
    rw [run_proverRO_fresh c₀ stmt gK van m c₁ c₂ hf]
  · have hl : Pr{let x ← (($ᵗ H) >>= fun c₂ =>
        (simulateQ randomOracle (proverRO stmt gK van m c₁ c₂)).run c₀)}[x = o] = 0 := by
      refine (prEvent_eq_zero_of_not_mem_support _) fun hmem => hc ?_
      rw [mem_support_bind_iff] at hmem
      obtain ⟨c₂, -, hy⟩ := hmem
      exact run_proverRO_handle c₀ stmt gK van m c₁ c₂ o hy
    have hr : Pr{let x ← (($ᵗ H) >>= fun c₂ => ($ᵗ (E × E × E)) >>= fun ch =>
        ($ᵗ E) >>= fun t => ($ᵗ E) >>= fun ρ => (pure (assemble c₀ stmt (c₁, c₂, ch, t, ρ)
          (viewAt stmt gK van m ch t ρ)) : ProbComp _))}[x = o] = 0 := by
      refine (prEvent_eq_zero_of_not_mem_support _) fun hmem => hc ?_
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
      obtain ⟨c₂, -, ch, -, t, -, ρ, -, rfl⟩ := hmem
      rfl
    rw [hl, hr]

/-- The challenges that are good for a witness: no denominator vanishes on a cell, and the row of
`t` is not a root of the vanishing polynomial. -/
def Good (gK : Fin 4 → K[X]) (van : K[X]) (ch : E × E × E) (t : E) : Prop :=
  (∀ i, ch.1 + P.cells (committed gK van 0) i + ch.2.1 * P.pt i ≠ 0) ∧
    (∀ i, ch.1 + P.cells (committed gK van 0) i + ch.2.1 * P.pt (P.σ i) ≠ 0) ∧
    aeval (rowPoly.eval t) van ≠ 0

theorem not_mem_support_assemble {α : Type} (mx : ProbComp α)
    (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (c : H × H × (E × E × E) × E × E) (g : α → (Fin 4 → E) × E × Bool)
    (o : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache)
    (h : ¬ (o.1.ch = c.2.2.1 ∧ o.1.t = c.2.2.2.1)) :
    Pr{let y ← mx >>= fun x => pure (assemble c₀ stmt c (g x))}[y = o] = 0 := by
  refine (prEvent_eq_zero_of_not_mem_support _) fun hmem => h ?_
  rw [mem_support_bind_iff] at hmem
  obtain ⟨x, -, hx⟩ := hmem
  rw [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨rfl, rfl⟩

/-- **Zero knowledge of the non-interactive proof.** Whatever the oracle held before, at every
outcome whose first handle is fresh and whose challenges are good for the witness, the real
experiment and the simulator's have the same probability: the proof, its verdict, its challenges
and the oracle's table together. -/
theorem realNI_eq_simNI (h3 : finrank K E = 3) (hE : P.Exact)
    (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X])
    (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0)))
    (o : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache)
    (hfresh : Fresh c₀ stmt o.1.c₁) (hgood : Good (P := P) gK van o.1.ch o.1.t) :
    Pr{let x ← realNI c₀ stmt gK van}[x = o] = Pr{let x ← simNI (K := K) c₀ stmt}[x = o] := by
  classical
  rw [realNI_eq_openNI c₀ stmt gK van o hfresh]
  unfold openNI
  refine ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq (· = o)).trans ?_
  unfold simNI
  refine prEvent_bind_congr _ _ _ _ _ fun c => ?_
  by_cases hc : o.1.ch = c.2.2.1 ∧ o.1.t = c.2.2.2.1
  · obtain ⟨hch, ht⟩ := hc
    rw [hch, ht] at hgood
    obtain ⟨hd, hd', hu⟩ := hgood
    have h1 : (($ᵗ (Fin 4 → Fin 3 → K)) >>= fun m =>
          (pure (assemble c₀ stmt c (viewAt stmt gK van m c.2.2.1 c.2.2.2.1 c.2.2.2.2)) :
            ProbComp _))
        = assemble c₀ stmt c <$> realView P stmt gK van c.2.2.1.1 c.2.2.1.2.1 c.2.2.1.2.2
            c.2.2.2.1 c.2.2.2.2 := by
      unfold realView
      rw [Functor.map_map, map_eq_bind_pure_comp]
      rfl
    have h2 : (simValues (K := K) (rowPoly.eval c.2.2.2.1) >>= fun a =>
          (pure (assemble c₀ stmt c (a, P.sigmaPoly.eval c.2.2.2.1,
            decide (NotRejected P c.2.2.1.1 c.2.2.1.2.1 c.2.2.2.1 a))) : ProbComp _))
        = assemble c₀ stmt c <$> simView (K := K) P c.2.2.1.1 c.2.2.1.2.1 c.2.2.2.1 := by
      unfold simView
      rw [Functor.map_map, map_eq_bind_pure_comp]
      rfl
    rw [h1, h2]
    exact ((evalDistEq_iff_forall_prEvent_eq_output.mpr
      (realView_eq_simView P h3 hE stmt gK van hvan hsat _ _ _ _ _ hd hd' hu)).map _).prEvent_eq
        (· = o)
  · rw [not_mem_support_assemble _ c₀ stmt c _ o hc, not_mem_support_assemble _ c₀ stmt c _ o hc]

open Classical in
/-- **Few challenges are not good.** Of the `q^4` values of `(α, β, γ, t)`, at most
`(2 N + 4 deg) q^3` are not good for a witness: a denominator vanishing on one of the `N` cells,
or `t` in a row that is a root of the vanishing polynomial, of degree `deg`. -/
theorem card_not_good_le (gK : Fin 4 → K[X]) (van : K[X]) (hvan0 : van ≠ 0) :
    (Finset.univ.filter fun x : (E × E × E) × E => ¬ Good (P := P) gK van x.1 x.2).card
      ≤ (2 * P.nCells + 4 * van.natDegree) * Fintype.card E ^ 3 := by
  set w := P.cells (committed gK van 0) with hw
  set Z := Finset.univ.filter fun p : E × E × E =>
    ∃ i, p.1 + w i + p.2.1 * P.pt i = 0 ∨ p.1 + w i + p.2.1 * P.pt (P.σ i) = 0 with hZ
  have hZcard : Z.card ≤ 2 * P.nCells * Fintype.card E ^ 2 := card_zero_le P.pt P.σ w
  set p : E[X] := (van.map (algebraMap K E)).comp rowPoly with hp
  have hrow : (rowPoly : E[X]).natDegree = 4 := by
    unfold rowPoly
    compute_degree!
  have hp0 : p ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h1 | ⟨-, h2⟩
    · exact hvan0 ((Polynomial.map_eq_zero _).mp h1)
    · have := congrArg natDegree h2
      rw [hrow, natDegree_C] at this
      exact absurd this (by norm_num)
  set R := Finset.univ.filter fun t : E => aeval (rowPoly.eval t) van = 0 with hR
  have hRcard : R.card ≤ 4 * van.natDegree := by
    have hsub : R ⊆ p.roots.toFinset := by
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def, hp, eval_comp, eval_map_algebraMap]
      exact ht.2
    calc R.card ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := card_roots' p
      _ ≤ (van.map (algebraMap K E)).natDegree * (rowPoly : E[X]).natDegree := natDegree_comp_le
      _ ≤ van.natDegree * 4 := by rw [hrow]; exact Nat.mul_le_mul_right 4 natDegree_map_le
      _ = 4 * van.natDegree := mul_comm _ _
  have hsub : (Finset.univ.filter fun x : (E × E × E) × E => ¬ Good (P := P) gK van x.1 x.2)
      ⊆ (Z ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ R) := by
    rintro ⟨ch, t⟩ hx
    rw [Finset.mem_filter] at hx
    have hng := hx.2
    simp only [Good, not_and_or, not_forall, not_not] at hng
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true, true_and, hZ, hR,
      Finset.mem_filter]
    rcases hng with ⟨i, hi⟩ | ⟨i, hi⟩ | h
    · exact Or.inl ⟨i, Or.inl hi⟩
    · exact Or.inl ⟨i, Or.inr hi⟩
    · exact Or.inr h
  calc _ ≤ ((Z ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ R) : Finset ((E × E × E) × E)).card :=
        Finset.card_le_card hsub
    _ ≤ (Z ×ˢ (Finset.univ : Finset E)).card
          + ((Finset.univ : Finset (E × E × E)) ×ˢ R).card := Finset.card_union_le _ _
    _ ≤ 2 * P.nCells * Fintype.card E ^ 2 * Fintype.card E
          + Fintype.card E ^ 3 * (4 * van.natDegree) := by
        rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
          Fintype.card_prod, Fintype.card_prod]
        have : Fintype.card E * (Fintype.card E * Fintype.card E) = Fintype.card E ^ 3 := by ring
        rw [this]
        gcongr
    _ = (2 * P.nCells + 4 * van.natDegree) * Fintype.card E ^ 3 := by ring

end Experiments

end QuotientSecurity
