-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s run invariants and sizes (`Common.inv_of_mem_support_run`,
-- `Common.size_le_of_mem_support_run`).
import QuotientZk.Rom.Merkle
import QuotientZk.Rom.Entropy

/-!
# The bound on `MBad`

In the simulator's world with the honest view (`implView σ (view s σ)`), the run depends on the
secret `s` only through the view, and the private positions are unopened. `MBad` asks that an
unopened row be one of the inputs the cache holds (the oracle's initial entries `c₀` and the
inputs logged since, at most one per operation), or equal another unopened row. If every unopened
row keeps its entropy given the view (`δ` per value, `δ₂` per pair of positions), then
(`prEvent_mBad_le`):

  `Pr[MBad] ≤ N · (|c₀| + Q) · δ + N² · δ₂`

for `N` positions of secret tables and `Q` operations in all (the prover's and the
distinguisher's).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

variable {S I O M K X Pf : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
  [DecidableEq K] [DecidableEq X] [Inhabited I]
variable (P : Proto S I O M K X)

/-! ## Invariants of the simulator's runs -/

/-- What the simulator's runs keep: private positions are unopened and distinct, and the cache
holds only the initial inputs and the logged ones. -/
def ViewInv (σ : List O) (keys : List I) (st : St I O K X) : Prop :=
  (∀ e ∈ st.priv, P.opened σ e.1.1 e.1.2 = false) ∧ (st.priv.map Prod.fst).Nodup ∧
    ∀ r, (st.cache r).isSome → r ∈ keys ∨ r ∈ st.log

theorem viewInv_cacheQuery (σ : List O) (keys : List I) (st : St I O K X) (t : I) (u : O)
    (h : List O) (b : Bool) (hst : ViewInv P σ keys st) :
    ViewInv P σ keys { st with
      cache := st.cache.cacheQuery t u
      hist := h
      log := t :: st.log
      fs := b } := by
  obtain ⟨h1, h2, h3⟩ := hst
  refine ⟨h1, h2, fun r hr => ?_⟩
  by_cases hrt : r = t
  · subst hrt; exact Or.inr List.mem_cons_self
  · have : (st.cache r).isSome := by simpa [QueryCache.cacheQuery, hrt] using hr
    rcases h3 r this with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem roStep_viewInv (σ : List O) (keys : List I) (t : I) (st : St I O K X)
    (hst : ViewInv P σ keys st) : ∀ z ∈ support (roStep (K := K) (X := X) t st),
      ViewInv P σ keys z.2 := by
  intro z hz
  unfold roStep at hz
  cases h : st.cache t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hst
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact viewInv_cacheQuery P σ keys st t u st.hist st.fs hst

theorem implView_viewInv (σ : List O) (keys : List I) (v : View M I K X) (t : Op I K X)
    (st : St I O K X) (hst : ViewInv P σ keys st) :
    ∀ z ∈ support ((implView P σ v t).run st), ViewInv P σ keys z.2 := by
  intro z hz
  cases t with
  | pub t => exact roStep_viewInv P σ keys t st hst z hz
  | msg =>
    simp only [implView, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hst
  | leaf k x =>
    simp only [implView, StateT.run] at hz
    by_cases h1 : st.hist.length < P.cK k
    · simp only [h1, ite_true, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hst
    · simp only [h1, ite_false] at hz
      by_cases h2 : P.opened σ k x = true
      · simp only [h2, ite_true] at hz
        exact roStep_viewInv P σ keys _ st hst z hz
      · simp only [h2, Bool.false_eq_true, ite_false] at hz
        cases hl : st.priv.lookup (k, x) with
        | some u =>
          simp only [hl, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hst
        | none =>
          simp only [hl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨u, -, rfl⟩ := hz
          obtain ⟨i1, i2, i3⟩ := hst
          refine ⟨fun e he => ?_, ?_, i3⟩
          · rcases List.mem_append.mp he with he | he
            · exact i1 e he
            · rw [List.mem_singleton] at he
              subst he
              simpa using h2
          · rw [List.map_append, List.nodup_append]
            refine ⟨i2, List.nodup_singleton _, fun a ha b hb hab => ?_⟩
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            subst hb hab
            rw [lookup_eq_find?, Option.map_eq_none_iff, List.find?_eq_none] at hl
            obtain ⟨e, he, heq⟩ := List.mem_map.mp ha
            exact hl e he (by simp [heq])
  | chal t =>
    simp only [implView, StateT.run] at hz
    split_ifs at hz
    · simp only [progStep, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact viewInv_cacheQuery P σ keys st t _ _ _ hst
    · exact roStep_viewInv P σ keys t st hst z hz

theorem init_cache_isSome (c₀ : List (I × O)) (r : I)
    (h : ((St.init (K := K) (X := X) c₀).cache r).isSome) : r ∈ c₀.map Prod.fst := by
  induction c₀ with
  | nil => simp [St.init] at h
  | cons e c₀ ih =>
    simp only [St.init, List.foldr_cons] at h ih
    by_cases hr : r = e.1
    · subst hr; exact List.mem_cons_self
    · have := ih (by simpa [QueryCache.cacheQuery, hr] using h)
      exact List.mem_cons_of_mem _ this

theorem viewInv_init (σ : List O) (c₀ : List (I × O)) :
    ViewInv P σ (c₀.map Prod.fst) (St.init (K := K) (X := X) c₀) :=
  ⟨by simp [St.init], by simp [St.init], fun r hr => Or.inl (init_cache_isSome c₀ r hr)⟩

/-! ## Counting -/

theorem queryCost_of_total {α : Type} {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (oa : OracleComp spec α) (n : ℕ) (h : IsTotalQueryBound oa n) :
    Common.QueryCostAtMost oa (fun _ => 1) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [Common.isWeightBound_query_bind_iff]
    exact ⟨h.1, fun u => ih u (n - 1) (h.2 u)⟩

theorem implView_log (σ : List O) (v : View M I K X) (t : Op I K X) (st : St I O K X) :
    ∀ z ∈ support ((implView P σ v t).run st), z.2.log.length ≤ st.log.length + 1 := by
  have hro : ∀ (r : I) (st : St I O K X), ∀ z ∈ support (roStep (K := K) (X := X) r st),
      z.2.log.length ≤ st.log.length + 1 := by
    intro r st z hz
    unfold roStep at hz
    cases h : st.cache r with
    | some u =>
      simp only [h, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
    | none =>
      simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      simp
  intro z hz
  cases t with
  | pub t => exact hro t st z hz
  | msg =>
    simp only [implView, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst hz; simp
  | leaf k x =>
    simp only [implView, StateT.run] at hz
    split_ifs at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
    · exact hro _ st z hz
    · cases hl : st.priv.lookup (k, x) with
      | some u =>
        simp only [hl, support_pure, Set.mem_singleton_iff] at hz
        subst hz; simp
      | none =>
        simp only [hl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨u, -, rfl⟩ := hz
        simp
  | chal t =>
    simp only [implView, StateT.run] at hz
    split_ifs at hz
    · simp only [progStep, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
    · exact hro t st z hz

/-! ## The bound -/

/-- **The bound on `MBad`.** For any challenges `σ` and any computation of at most `Q` operations
run by the simulator's implementation with the honest view, from an oracle holding `c₀`: if every
unopened row keeps its entropy given the view, `MBad` has probability at most
`N (|c₀| + Q) δ + N² δ₂`, `N` the number of positions. -/
theorem prEvent_mBad_le [SampleableType S] [Fintype (K × X)] (σ : List O) (c₀ : List (I × O))
    {α : Type} (oa : OracleComp (OpSpec I O M K X) α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (δ δ₂ : ℝ≥0∞)
    (hent : ∀ k x, P.opened σ k x = false → ∀ v y,
      Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = y] ≤
        δ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hent₂ : ∀ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false → (k, x) ≠ (k', x') →
      ∀ v, Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = P.rows s σ k' x'] ≤
        δ₂ * Pr{let s ← $ᵗ S}[P.view s σ = v]) :
    Pr{let x ← (do
        let s ← $ᵗ S
        let z ← (simulateQ (implView P σ (P.view s σ)) oa).run (St.init c₀)
        return (s, z))}[MBad (P.rows x.1 σ) x.2.2] ≤
      (Fintype.card (K × X) * (c₀.length + Q) : ℕ) * δ +
        (Fintype.card (K × X) ^ 2 : ℕ) * δ₂ := by
  classical
  set N := Fintype.card (K × X)
  set keys := c₀.map Prod.fst
  set R := fun v : View M I K X => (simulateQ (implView P σ v) oa).run (St.init c₀)
  have hinv : ∀ v, ∀ z ∈ support (R v), ViewInv P σ keys z.2 := fun v =>
    Common.inv_of_mem_support_run (implView P σ v) (ViewInv P σ keys)
      (fun t st hst => implView_viewInv P σ keys v t st hst) oa (viewInv_init P σ c₀)
  have hlog : ∀ v, ∀ z ∈ support (R v), z.2.log.length ≤ Q := by
    intro v z hz
    have := Common.size_le_of_mem_support_run (implView P σ v) (fun _ => True) (fun _ => 1)
      (fun st => st.log.length) (fun _ _ _ _ _ => trivial)
      (fun t st _ z hz => implView_log P σ v t st z hz) oa Q (queryCost_of_total oa Q hQ)
      (s₀ := St.init c₀) trivial z hz
    simpa [St.init] using this
  have hpriv : ∀ v, ∀ z ∈ support (R v), (z.2.priv.map Prod.fst).length ≤ N := fun v z hz =>
    List.Nodup.length_le_card (hinv v z hz).2.1
  -- the candidates
  let fA : (α × St I O K X) → List ((K × X) × I) := fun z =>
    (z.2.priv.map Prod.fst) ×ˢ (keys ++ z.2.log)
  let fB : (α × St I O K X) → List ((K × X) × (K × X)) := fun z =>
    (z.2.priv.map Prod.fst) ×ˢ (z.2.priv.map Prod.fst)
  have hA := prEvent_hit_le (S := S) (fun s => P.view s σ) R fA
    (fun s w => P.rows s σ w.1.1 w.1.2 = w.2) (fun w => P.opened σ w.1.1 w.1.2 = false)
    (N * (c₀.length + Q)) δ (fun w hw v => hent w.1.1 w.1.2 hw v w.2)
    (fun s z hz w hw => by
      obtain ⟨hw1, -⟩ := List.mem_product.mp hw
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hw1
      rw [← heq]
      exact (hinv _ z hz).1 e he)
    (fun s z hz => by
      simp only [fA, List.length_product, List.length_append, List.length_map, keys]
      have h1 := hpriv _ z hz
      have h2 := hlog _ z hz
      simp only [List.length_map] at h1
      exact Nat.mul_le_mul h1 (by omega))
  have hB := prEvent_hit_le (S := S) (fun s => P.view s σ) R fB
    (fun s w => w.1 ≠ w.2 ∧ P.rows s σ w.1.1 w.1.2 = P.rows s σ w.2.1 w.2.2)
    (fun w => P.opened σ w.1.1 w.1.2 = false ∧ P.opened σ w.2.1 w.2.2 = false)
    (N ^ 2) δ₂ (fun w hw v => by
      by_cases hne : w.1 = w.2
      · simp only [hne, ne_eq, not_true_eq_false, false_and]
        simp
      · refine le_trans (prEvent_mono ($ᵗ S)
          (fun s => P.view s σ = v ∧ (w.1 ≠ w.2 ∧ P.rows s σ w.1.1 w.1.2 = P.rows s σ w.2.1 w.2.2))
          (fun s => P.view s σ = v ∧ P.rows s σ w.1.1 w.1.2 = P.rows s σ w.2.1 w.2.2)
          fun s h => ⟨h.1, h.2.2⟩) ?_
        exact hent₂ w.1.1 w.1.2 w.2.1 w.2.2 hw.1 hw.2 hne v)
    (fun s z hz w hw => by
      obtain ⟨hw1, hw2⟩ := List.mem_product.mp hw
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hw1
      obtain ⟨e', he', heq'⟩ := List.mem_map.mp hw2
      rw [← heq, ← heq']
      exact ⟨(hinv _ z hz).1 e he, (hinv _ z hz).1 e' he'⟩)
    (fun s z hz => by
      simp only [fB, List.length_product]
      have h1 := hpriv _ z hz
      rw [sq]
      exact Nat.mul_le_mul h1 h1)
  -- `MBad` is one of the two hits
  have himp : ∀ x ∈ support (do
        let s ← $ᵗ S
        let z ← R (P.view s σ)
        return (s, z)), MBad (P.rows x.1 σ) x.2.2 →
      (∃ w ∈ fA x.2, P.rows x.1 σ w.1.1 w.1.2 = w.2) ∨
        (∃ w ∈ fB x.2, w.1 ≠ w.2 ∧ P.rows x.1 σ w.1.1 w.1.2 = P.rows x.1 σ w.2.1 w.2.2) := by
    intro x hx hbad
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨s, -, z, hz, rfl⟩ := hx
    obtain ⟨e, he, hb⟩ := hbad
    rcases hb with hc | ⟨e', he', hne, heq⟩
    · left
      refine ⟨(e.1, P.rows s σ e.1.1 e.1.2), ?_, rfl⟩
      refine List.mem_product.mpr ⟨List.mem_map_of_mem he, ?_⟩
      rcases (hinv _ z hz).2.2 _ hc with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ h
    · right
      exact ⟨(e'.1, e.1), List.mem_product.mpr ⟨List.mem_map_of_mem he', List.mem_map_of_mem he⟩,
        hne, heq⟩
  calc _ ≤ Pr{let x ← (do
          let s ← $ᵗ S
          let z ← R (P.view s σ)
          return (s, z))}[(∃ w ∈ fA x.2, P.rows x.1 σ w.1.1 w.1.2 = w.2) ∨
            (∃ w ∈ fB x.2, w.1 ≠ w.2 ∧
              P.rows x.1 σ w.1.1 w.1.2 = P.rows x.1 σ w.2.1 w.2.2)] :=
        prEvent_mono_of_support _ _ _ himp
    _ ≤ _ := (prEvent_or_le _ _ _).trans (add_le_add (by exact_mod_cast hA) (by exact_mod_cast hB))

end QuotientZk
