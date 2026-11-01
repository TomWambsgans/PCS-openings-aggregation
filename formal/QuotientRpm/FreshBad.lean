-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The induction and the restriction to finitely many inputs follow VCVio's `prEvent_freshBadQuery_le`
-- and `prEvent_randomOracle_le_of_bad_queries` (https://github.com/Verified-zkEVM/VCVio, commit afa6593f,
-- `VCVio/OracleComp/QueryTracking/RandomOracle/FreshQuery.lean`, Apache-2.0); here the bad event of a
-- fresh query sees the inputs asked before it.
import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-!
# Bad fresh queries, given what was asked before

A random oracle's table is sampled at once (`evalDist_simulateQ_randomOracle_run'_eq_completeTable`),
and a computation then runs deterministically against it. Each query not asked before is *fresh*;
`bad H x T` tests a fresh query `x` against the inputs `H` asked before it and the whole table
`T`, so it may look at answers not yet asked (`FreshBad`). If, given any cache of fewer than `N`
inputs and any fresh input, the table completing the cache is bad with probability at most `ε`,
a computation of at most `n ≤ N` queries meets a bad fresh query with probability at most `n ε`
(`prEvent_freshBad_le`); and an event that implies one, on every table, has at most that
probability against the lazily sampled oracle (`prEvent_randomOracle_le_of_freshBad`), the inputs
any infinite: the computation is restricted to the finitely many it can ask together with a set
`S₀` of inputs the bad event may look at.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace QuotientRpm

/-- **Some fresh input of a list is bad**: an input of `xs` that is neither in `H` nor earlier
in `xs`, tested with those inputs and the table `T`. -/
def FreshBad {D τ : Type} [DecidableEq D] (bad : Finset D → D → τ → Prop) (T : τ) :
    Finset D → List D → Prop
  | _, [] => False
  | H, x :: xs => (x ∉ H ∧ bad H x T) ∨ FreshBad bad T (insert x H) xs

section Lists

variable {D τ : Type} [DecidableEq D]

theorem freshBad_append (bad : Finset D → D → τ → Prop) (T : τ) :
    ∀ (H : Finset D) (xs ys : List D),
      FreshBad bad T H (xs ++ ys) ↔ FreshBad bad T H xs ∨ FreshBad bad T (H ∪ xs.toFinset) ys
  | H, [], ys => by simp [FreshBad]
  | H, x :: xs, ys => by
    simp only [List.cons_append, FreshBad, freshBad_append bad T (insert x H) xs ys,
      List.toFinset_cons, Finset.insert_union, Finset.union_insert, or_assoc]

/-- A fresh input of a list mapped by an embedding, for the bad event read through it. -/
theorem freshBad_map {D' τ' : Type} [DecidableEq D'] (e : D' ↪ D) (bad : Finset D → D → τ → Prop)
    (F : τ' → τ) (T' : τ') : ∀ (H : Finset D') (xs : List D'),
      FreshBad bad (F T') (H.map e) (xs.map e) ↔
        FreshBad (fun H' x' g' => bad (H'.map e) (e x') (F g')) T' H xs
  | H, [] => by simp [FreshBad]
  | H, x :: xs => by
    simp only [List.map_cons, FreshBad, Finset.mem_map' e, ← Finset.map_insert,
      freshBad_map e bad F T' (insert x H) xs]

/-- The inputs of `L` before the first occurrence of `z`. -/
def before : List D → D → Finset D
  | [], _ => ∅
  | x :: xs, z => if x = z then ∅ else insert x (before xs z)

/-- **No bad fresh input**: each input of `L` (not in `H`) is not bad given the inputs before its
first occurrence. -/
theorem not_bad_before (bad : Finset D → D → τ → Prop) (T : τ) :
    ∀ (H : Finset D) (L : List D), ¬ FreshBad bad T H L → ∀ y ∈ L, y ∉ H →
      ¬ bad (H ∪ before L y) y T
  | H, [], _, y, hy, _ => by simp at hy
  | H, x :: xs, h, y, hy, hH => by
    simp only [FreshBad, not_or, not_and] at h
    by_cases hxy : x = y
    · subst hxy
      simpa [before] using h.1 hH
    · have hy' : y ∈ xs := (List.mem_cons.mp hy).resolve_left (Ne.symm hxy)
      have := not_bad_before bad T (insert x H) xs h.2 y hy' (by simp [Ne.symm hxy, hH])
      simpa [before, hxy, Finset.insert_union, Finset.union_insert] using this

theorem not_mem_before_self : ∀ (L : List D) (y : D), y ∉ before L y
  | [], _ => by simp [before]
  | x :: xs, y => by
    by_cases hxy : x = y
    · simp [before, hxy]
    · simp only [before, hxy, ite_false, Finset.mem_insert, not_or]
      exact ⟨Ne.symm hxy, not_mem_before_self xs y⟩

theorem mem_of_mem_before : ∀ (L : List D) (y z : D), y ∈ before L z → y ∈ L
  | [], _, _, h => by simp [before] at h
  | x :: xs, y, z, h => by
    by_cases hxz : x = z
    · simp [before, hxz] at h
    · simp only [before, hxz, ite_false, Finset.mem_insert] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_before xs y z h)

/-- Of two distinct inputs of `L`, one comes first. -/
theorem before_trichotomy : ∀ (L : List D) (y z : D), y ∈ L → z ∈ L → y ≠ z →
    y ∈ before L z ∨ z ∈ before L y
  | [], _, _, hy, _, _ => by simp at hy
  | x :: xs, y, z, hy, hz, hyz => by
    by_cases hxz : x = z
    · subst hxz
      right
      simp [before, Ne.symm hyz]
    · by_cases hxy : x = y
      · subst hxy
        left
        simp [before, hxz]
      · have hy' : y ∈ xs := (List.mem_cons.mp hy).resolve_left (Ne.symm hxy)
        have hz' : z ∈ xs := (List.mem_cons.mp hz).resolve_left (Ne.symm hxz)
        rcases before_trichotomy xs y z hy' hz' hyz with h | h
        · left
          simp [before, hxz, h]
        · right
          simp [before, hxy, h]

/-- What comes before an input that comes before `z` comes before `z`. -/
theorem before_subset_of_mem : ∀ (L : List D) (y z : D), y ∈ before L z → before L y ⊆ before L z
  | [], _, _, h => by simp [before] at h
  | x :: xs, y, z, h => by
    by_cases hxz : x = z
    · simp [before, hxz] at h
    · simp only [before, hxz, ite_false, Finset.mem_insert] at h ⊢
      by_cases hxy : x = y
      · simp [hxy]
      · simp only [hxy, ite_false]
        rcases h with h | h
        · exact absurd h.symm hxy
        · exact Finset.insert_subset_insert _ (before_subset_of_mem xs y z h)

/-- Coming before is not symmetric. -/
theorem not_mem_before_of_mem_before {L : List D} {y z : D} (h : y ∈ before L z) :
    z ∉ before L y := fun h' =>
  not_mem_before_self L y (before_subset_of_mem L z y h' h)

end Lists

section Finite

variable {D α : Type} {R : D → Type} [DecidableEq D]

/-- The inputs a cache holds. -/
def cacheDom [Fintype D] (c : (OracleSpec.ofFn R).QueryCache) : Finset D :=
  Finset.univ.filter fun d => (c d).isSome

theorem mem_cacheDom [Fintype D] {c : (OracleSpec.ofFn R).QueryCache} {d : D} :
    d ∈ cacheDom c ↔ c d ≠ none := by
  simp [cacheDom, Option.isSome_iff_ne_none]

theorem cacheDom_cacheQuery [Fintype D] (c : (OracleSpec.ofFn R).QueryCache) (t : D) (u : R t) :
    cacheDom (c.cacheQuery t u) = insert t (cacheDom c) := by
  ext d
  by_cases h : d = t
  · subst h
    simp [mem_cacheDom]
  · simp [mem_cacheDom, h]

@[simp] theorem cacheDom_empty [Fintype D] : cacheDom (∅ : (OracleSpec.ofFn R).QueryCache) = ∅ := by
  ext d
  simp [mem_cacheDom]

/-- A bad fresh query of `oa` run against the table that completes `c` with `g`, the inputs
of `c` asked before. (The table comes before the cache, so that an event `fun g => …` over it is
not eta-reduced to a partial application.) -/
def FreshBadRun [Fintype D] (bad : Finset D → D → (∀ d, R d) → Prop)
    (oa : OracleComp (OracleSpec.ofFn R) α) (g : ∀ d, R d) (c : (OracleSpec.ofFn R).QueryCache) :
    Prop :=
  FreshBad bad (completeTable c g) (cacheDom c) ((tableQueryLog oa (completeTable c g)).map Sigma.fst)

variable [Fintype D]

theorem freshBadRun_query_bind_of_some (bad : Finset D → D → (∀ d, R d) → Prop) (t : D)
    (k : R t → OracleComp (OracleSpec.ofFn R) α) (c : (OracleSpec.ofFn R).QueryCache)
    (g : ∀ d, R d) {u : R t} (hc : c t = some u) :
    FreshBadRun bad (liftM ((OracleSpec.ofFn R).query t) >>= k) g c ↔ FreshBadRun bad (k u) g c := by
  have hval : completeTable c g t = u := by simp [completeTable, hc]
  have hmem : t ∈ cacheDom c := by simp [mem_cacheDom, hc]
  simp only [FreshBadRun, tableQueryLog_query_bind, List.map_cons, FreshBad, hval,
    Finset.insert_eq_of_mem hmem, hmem, not_true_eq_false, false_and, false_or]

theorem freshBadRun_query_bind_of_none (bad : Finset D → D → (∀ d, R d) → Prop) (t : D)
    (k : R t → OracleComp (OracleSpec.ofFn R) α) (c : (OracleSpec.ofFn R).QueryCache)
    (g : ∀ d, R d) (hc : c t = none) :
    FreshBadRun bad (liftM ((OracleSpec.ofFn R).query t) >>= k) g c ↔
      bad (cacheDom c) t (completeTable c g) ∨
        FreshBadRun bad (k (completeTable c g t)) g (c.cacheQuery t (completeTable c g t)) := by
  have hmem : t ∉ cacheDom c := by simp [mem_cacheDom, hc]
  simp only [FreshBadRun, tableQueryLog_query_bind, List.map_cons, FreshBad, hmem,
    not_false_eq_true, true_and, completeTable_cacheQuery_value, cacheDom_cacheQuery]

theorem freshBadRun_update_of_some (bad : Finset D → D → (∀ d, R d) → Prop)
    (oa : OracleComp (OracleSpec.ofFn R) α) (c : (OracleSpec.ofFn R).QueryCache) (g : ∀ d, R d)
    {t : D} {v : R t} (hc : c t = some v) (u : R t) :
    FreshBadRun bad oa (Function.update g t u) c ↔ FreshBadRun bad oa g c := by
  simp only [FreshBadRun, completeTable_update_of_some c g hc u]

variable [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]

/-- Expose a fresh answer before the rest of the run. -/
theorem prEvent_freshBadRun_suffix (bad : Finset D → D → (∀ d, R d) → Prop) (t : D)
    (k : R t → OracleComp (OracleSpec.ofFn R) α) (c : (OracleSpec.ofFn R).QueryCache)
    (hc : c t = none) :
    Pr{let g ← $ᵗ (∀ d, R d)}[FreshBadRun bad (k (completeTable c g t)) g
      (c.cacheQuery t (completeTable c g t))] =
    Pr{let u ← $ᵗ (R t); let g ← $ᵗ (∀ d, R d)}[FreshBadRun bad (k u) g (c.cacheQuery t u)] := by
  rw [prEvent_uniformTable_update t]
  have hval (g : (d : D) → R d) (u : R t) : completeTable c (Function.update g t u) t = u := by
    simp [completeTable, hc]
  simp_rw [hval, freshBadRun_update_of_some _ _ _ _ (QueryCache.cacheQuery_self _ _ _)]

/-- **At most `n ε`.** Against a uniform table completing a cache `c` of `|c|` inputs, a
computation of at most `n` queries, `|c| + n ≤ N`, asks a bad fresh input with probability at
most `n ε`, when every fresh input given any cache of fewer than `N` inputs is bad with
probability at most `ε`. -/
theorem prEvent_freshBad_le (bad : Finset D → D → (∀ d, R d) → Prop) (ε : ℝ≥0∞) (N : ℕ)
    (hbad : ∀ (c : (OracleSpec.ofFn R).QueryCache) (t : D), c t = none → (cacheDom c).card < N →
      Pr{let g ← $ᵗ (∀ d, R d)}[bad (cacheDom c) t (completeTable c g)] ≤ ε)
    (oa : OracleComp (OracleSpec.ofFn R) α) : ∀ (n : ℕ), IsTotalQueryBound oa n →
      ∀ (c : (OracleSpec.ofFn R).QueryCache), (cacheDom c).card + n ≤ N →
        Pr{let g ← $ᵗ (∀ d, R d)}[FreshBadRun bad oa g c] ≤ n * ε := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ c _
    simp [FreshBadRun, FreshBad]
  | query_bind t k ih =>
    intro n hn c hc
    obtain ⟨hn1, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    cases hct : c t with
    | some u =>
      simp_rw [freshBadRun_query_bind_of_some bad t k c _ hct]
      exact (ih u (n - 1) (hk u) c (by omega)).trans (by gcongr; omega)
    | none =>
      have hmem : t ∉ cacheDom c := by simp [mem_cacheDom, hct]
      simp_rw [freshBadRun_query_bind_of_none bad t k c _ hct]
      refine (prEvent_or_le _ _ _).trans ?_
      have hfirst := hbad c t hct (by omega)
      have hrest : Pr{let g ← $ᵗ (∀ d, R d)}[FreshBadRun bad (k (completeTable c g t)) g
          (c.cacheQuery t (completeTable c g t))] ≤ ((n - 1 : ℕ) : ℝ≥0∞) * ε := by
        rw [prEvent_freshBadRun_suffix bad t k c hct]
        simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, id_eq] using
          (prEvent_bind_le_of_forall_le ($ᵗ (R t))
            (fun u => (fun g => FreshBadRun bad (k u) g (c.cacheQuery t u)) <$>
              ($ᵗ (∀ d, R d))) id
            (fun u => by
              simpa using ih u (n - 1) (hk u) (c.cacheQuery t u)
                (by rw [cacheDom_cacheQuery, Finset.card_insert_of_notMem hmem]; omega)))
      calc _ ≤ ε + ((n - 1 : ℕ) : ℝ≥0∞) * ε := add_le_add hfirst hrest
        _ = n * ε := by
          conv_lhs => lhs; rw [← one_mul ε]
          rw [← add_mul, ← Nat.cast_one, ← Nat.cast_add]
          congr 2
          omega

end Finite

/-! ## Infinitely many inputs -/

section Infinite

variable {D Rg α : Type} [DecidableEq D]

theorem isTotalQueryBound_restrictQueries [Finite Rg] (S : Finset D)
    (oa : OracleComp (D →ₒ Rg) α) (h : AllQueriesSatisfy oa (· ∈ S)) :
    ∀ n, IsTotalQueryBound oa n → IsTotalQueryBound (restrictQueries S oa h) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; trivial
  | query_bind t k ih =>
    intro n hb
    exact ⟨hb.1, fun u => ih u (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) _ (hb.2 u)⟩

omit [DecidableEq D] in
theorem restrictCache_empty (S : Finset D) :
    restrictCache S (∅ : (D →ₒ Rg).QueryCache) = ∅ := by
  ext d
  rfl

variable [Fintype Rg] [Nonempty Rg] [SampleableType Rg]

/-- **Bad fresh queries bound an event of the lazily sampled oracle.** If an event of the output
implies, on every table, a bad fresh query of the computation; and if, for every finite set of
inputs `S ⊇ S₀`, every cache on `S` of fewer than `n` inputs and every fresh input in `S`, the
table that completes the cache uniformly on `S` (and is fixed elsewhere) makes the input bad with
probability at most `ε`: then the event has probability at most `n ε` for a computation of at
most `n` queries. -/
theorem prEvent_randomOracle_le_of_freshBad (oa : OracleComp (D →ₒ Rg) α) (n : ℕ)
    (hn : IsTotalQueryBound oa n) (S₀ : Set D) (hS₀ : S₀.Finite) (event : α → Prop)
    (bad : Finset D → D → (D → Rg) → Prop) (ε : ℝ≥0∞)
    (hbad : ∀ S : Finset D, (∀ d ∈ S₀, d ∈ S) →
      ∀ (c : (OracleSpec.ofFn fun d : ↥S => (fun _ : D => Rg) d.1).QueryCache) (t : ↥S),
        c t = none → (cacheDom c).card < n →
        Pr{let g ← $ᵗ (↥S → Rg)}[bad ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
          (extendTable (R := fun _ : D => Rg) S (completeTable c g))] ≤ ε)
    (htrace : ∀ T : D → Rg, event (evalWithAnswerFn (QueryImpl.ofFn T) oa) →
      FreshBad bad T ∅ ((tableQueryLog oa T).map Sigma.fst)) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤ n * ε := by
  classical
  let S := possibleQueryKeys oa ∪ hS₀.toFinset
  have hS : AllQueriesSatisfy oa (· ∈ S) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun d hd => Finset.mem_union_left _ hd
  let small := restrictQueries S oa hS
  have hrun : (simulateQ randomOracle small).run' ∅ = (simulateQ randomOracle oa).run' ∅ := by
    rw [← randomOracle_restrictQueries S oa hS ∅, restrictCache_empty]
  rw [← hrun]
  let : MeasurableSpace α := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable small ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq event]
  simp only [prEvent_norm]
  let e : ↥S ↪ D := Function.Embedding.subtype (· ∈ S)
  let bad' : Finset ↥S → ↥S → (↥S → Rg) → Prop := fun H' x' g' =>
    bad (H'.map e) x'.1 (extendTable (R := fun _ : D => Rg) S g')
  -- On every table on `S`, the event gives a bad fresh query of the restricted computation.
  have htrace' : ∀ g : ↥S → Rg, event (evalWithAnswerFn (QueryImpl.ofFn g) small) →
      FreshBadRun bad' small g ∅ := by
    intro g hev
    have hg : (fun d : ↥S => extendTable (R := fun _ : D => Rg) S g d.1) = g :=
      funext (extendTable_subtype (R := fun _ : D => Rg) S g)
    have heval := evalWithAnswerFn_restrictQueries S oa hS (extendTable (R := fun _ : D => Rg) S g)
    rw [hg] at heval
    have h := htrace (extendTable S g) (heval ▸ hev)
    have hlog := tableQueryLog_restrictQueries S oa hS (extendTable (R := fun _ : D => Rg) S g)
    rw [hg] at hlog
    rw [← hlog, List.map_map] at h
    have hm : (Sigma.fst ∘ fun q : (Σ _ : ↥S, Rg) => (⟨q.1.1, q.2⟩ : Σ _ : D, Rg)) =
        e ∘ Sigma.fst := rfl
    rw [hm, ← List.map_map, show (∅ : Finset D) = (∅ : Finset ↥S).map e from rfl] at h
    have h' := (freshBad_map e bad (extendTable (R := fun _ : D => Rg) S) g ∅ _).mp h
    simp only [FreshBadRun, completeTable_empty, cacheDom_empty]
    exact h'
  refine (prEvent_mono _ _ _ htrace').trans ?_
  exact prEvent_freshBad_le (D := ↥S) (R := fun _ => Rg) bad' ε n
    (fun c t hct hcard => hbad S (fun d hd => Finset.mem_union_right _ (hS₀.mem_toFinset.mpr hd))
      c t hct hcard) small n
    (isTotalQueryBound_restrictQueries S oa hS n hn) ∅ (by simp)

end Infinite

end QuotientRpm
