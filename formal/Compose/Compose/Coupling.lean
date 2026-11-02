-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.AdversaryLog
import WhirBridge.Verifier

/-!
# The logged run is the random oracle's run, and its transcript is the oracle's cache

The composition reads the oracle's cache at the end of each opening (F2's `ours_sound` is an event
of `romExperiment`'s cache) through the transcripts the run logs (`loggedKC`). Two facts make that
exact:

* **`map_run_loggedKC`**: logging changes nothing of the run against the lazily sampled oracle,
  the result and the cache included;
* **`consistent_run_loggedKC`**: on every outcome, the cache's Keccak-256 answers are the
  transcript's (`Consistent`), when they were so at the start.

So an event of the cache at the end of a stage is an event of the transcripts the run outputs.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Protocol.Rom (romExperiment)

/-- The digest a transcript records for an input (its first entry), as a digest. -/
def lookTr (tr : Transcript) (x : List UInt8) : Option Digest :=
  (tr.find? fun e => decide (e.1 = x)).map fun e => LeanVM.Digest.ofRpm e.2

/-- The cache's Keccak-256 answers are the transcript's. -/
def Consistent (tr : Transcript) (c : KeccakCalls.QueryCache) : Prop :=
  ∀ x, c (.inl x) = lookTr tr x

theorem lookTr_append (tr : Transcript) (e : List UInt8 × Bytes32) (y : List UInt8) :
    lookTr (tr ++ [e]) y = match lookTr tr y with
      | some d => some d
      | none => if e.1 = y then some (LeanVM.Digest.ofRpm e.2) else none := by
  unfold lookTr
  rw [List.find?_append]
  cases hf : tr.find? fun e => decide (e.1 = y) with
  | some _ => rfl
  | none =>
    by_cases he : e.1 = y
    · simp [he]
    · simp [he]

/-- One query keeps the cache's answers the transcript's. -/
theorem consistent_step {tr : Transcript} {c : KeccakCalls.QueryCache} (hc : Consistent tr c)
    (t : List UInt8 ⊕ KeccakState) (u : KeccakCalls t) {c' : KeccakCalls.QueryCache}
    (hc' : (c t = some u ∧ c' = c) ∨ (c t = none ∧ c' = c.cacheQuery t u)) :
    Consistent (tr ++ (inlEntry ⟨t, u⟩).toList) c' := by
  intro y
  cases t with
  | inr s =>
    show c' (.inl y) = lookTr (tr ++ []) y
    rw [List.append_nil, ← hc y]
    rcases hc' with ⟨-, he⟩ | ⟨-, he⟩
    · rw [he]
    · rw [he]
      exact QueryCache.cacheQuery_of_ne _ _ (by simp)
  | inl x =>
    show c' (.inl y) = lookTr (tr ++ [(x, toB u)]) y
    rw [lookTr_append, ← hc y]
    rcases hc' with ⟨hx, he⟩ | ⟨hx, he⟩
    · rw [he]
      cases hy : c (.inl y) with
      | some d => rfl
      | none =>
        have hne : x ≠ y := fun e => by rw [e, hy] at hx; cases hx
        simp [hne]
    · rw [he]
      by_cases hxy : x = y
      · subst hxy
        rw [hx, QueryCache.cacheQuery_self]
        simp [LeanVM.Rpm.digestOfRpm_toRpm]
      · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using Ne.symm hxy)]
        cases c (.inl y) <;> simp [hxy]

/-- **On every outcome of the logged run, the cache's answers are the transcript's.** -/
theorem consistent_run_loggedKC {α : Type} (v : OracleComp KeccakCalls α) :
    ∀ (tr : Transcript) (c : KeccakCalls.QueryCache), Consistent tr c →
      ∀ z ∈ support ((simulateQ randomOracle ((simulateQ logImplKC v).run tr)).run c),
        Consistent z.1.2 z.2 := by
  induction v using OracleComp.inductionOn with
  | pure a =>
    intro tr c hc z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hc
  | query_bind t k ih =>
    intro tr c hc z hz
    rw [loggedKC_run_query_bind, LeanVM.Protocol.Rom.run_simulateQ_bind,
      simulateQ_spec_query, randomOracle.run_eq] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    cases hct : c t with
    | some u =>
      rw [hct] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ih u _ _ (consistent_step hc t u (Or.inl ⟨hct, rfl⟩)) z hz
    | none =>
      rw [hct] at hp
      rw [mem_support_bind_iff] at hp
      obtain ⟨u, -, hu⟩ := hp
      simp only [support_pure, Set.mem_singleton_iff] at hu
      subst hu
      exact ih u _ _ (consistent_step hc t u (Or.inr ⟨hct, rfl⟩)) z hz

/-- **Logging changes nothing of the run**: the result and the cache are the unlogged run's. -/
theorem map_run_loggedKC {α : Type} (v : OracleComp KeccakCalls α) :
    ∀ (tr : Transcript) (c : KeccakCalls.QueryCache),
      (fun z => (z.1.1, z.2)) <$> (simulateQ randomOracle ((simulateQ logImplKC v).run tr)).run c =
        (simulateQ randomOracle v).run c := by
  induction v using OracleComp.inductionOn with
  | pure a =>
    intro tr c
    simp
  | query_bind t k ih =>
    intro tr c
    rw [loggedKC_run_query_bind, LeanVM.Protocol.Rom.run_simulateQ_bind,
      LeanVM.Protocol.Rom.run_simulateQ_bind, map_bind]
    refine bind_congr fun p => ?_
    exact ih p.1 _ p.2

/-! ## Events of a stage's cache, as events of its transcript -/

/-- The cache a transcript records: its Keccak-256 answers, and nothing else. -/
def cacheOfTr (tr : Transcript) : KeccakCalls.QueryCache :=
  QueryCache.ofFn fun d => match d with
    | .inl x => lookTr tr x
    | .inr _ => none

theorem cacheOfTr_inl (tr : Transcript) (x : List UInt8) :
    cacheOfTr tr (.inl x) = lookTr tr x := rfl

theorem consistent_nil : Consistent [] ∅ := fun _ => rfl

/-- An event that reads the cache's Keccak-256 answers only. -/
def ReadsInl {α : Type} (E : α → Bool → KeccakCalls.QueryCache → Prop) : Prop :=
  ∀ a b (c c' : KeccakCalls.QueryCache), (∀ x, c (.inl x) = c' (.inl x)) → (E a b c ↔ E a b c')

/-- **An adversary followed by a verifier, logged**: an event of the result and of the cache the
transcript records has the probability of the same event of `romExperiment` and its cache. -/
theorem prEvent_loggedPrefix {α : Type} (Apre : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) (E : α → Bool → KeccakCalls.QueryCache → Prop)
    (hE : ReadsInl E) :
    Pr{let z ← (simulateQ randomOracle ((simulateQ logImplKC
        (Apre >>= fun a => (a, ·) <$> V a)).run [])).run' ∅}[E z.1.1 z.1.2 (cacheOfTr z.2)] =
      Pr{let z ← romExperiment Apre V}[E z.1.1 z.1.2 z.2] := by
  rw [StateT.run'_eq, prEvent_map]
  refine (prEvent_congr_of_support _
    (fun z : ((α × Bool) × Transcript) × KeccakCalls.QueryCache =>
      E z.1.1.1 z.1.1.2 (cacheOfTr z.1.2))
    (fun z => E z.1.1.1 z.1.1.2 z.2) fun z hz => hE _ _ _ _
    fun x => (consistent_run_loggedKC _ [] ∅ consistent_nil z hz x).symm).trans ?_
  refine (prEvent_map _ (fun z : ((α × Bool) × Transcript) × KeccakCalls.QueryCache =>
    (z.1.1, z.2)) (fun w => E w.1.1 w.1.2 w.2)).symm.trans ?_
  rw [map_run_loggedKC]
  rfl

/-- Logging changes no event of the result. -/
theorem prEvent_run'_loggedKC {α : Type} (v : OracleComp KeccakCalls α) (tr : Transcript)
    (c : KeccakCalls.QueryCache) (E : α → Prop) :
    Pr{let z ← (simulateQ randomOracle ((simulateQ logImplKC v).run tr)).run' c}[E z.1] =
      Pr{let z ← (simulateQ randomOracle v).run' c}[E z] := by
  rw [StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map]
  refine (prEvent_map _ (fun z : (α × Transcript) × KeccakCalls.QueryCache => (z.1.1, z.2))
    (fun w => E w.1)).symm.trans ?_
  rw [map_run_loggedKC]

/-- **A continuation that keeps the result changes no event of it.** -/
theorem prEvent_run'_bind_keep {α β : Type} (mx : OracleComp KeccakCalls α)
    (g : α → OracleComp KeccakCalls β) (c : KeccakCalls.QueryCache) (E : α → Prop) :
    Pr{let z ← (simulateQ randomOracle (mx >>= fun x => (x, ·) <$> g x)).run' c}[E z.1] =
      Pr{let z ← (simulateQ randomOracle mx).run' c}[E z] := by
  rw [StateT.run'_eq, LeanVM.Protocol.Rom.run_simulateQ_bind, prEvent_map, StateT.run'_eq,
    prEvent_map]
  have h : ∀ p : α × KeccakCalls.QueryCache,
      Pr{let y ← (simulateQ randomOracle ((p.1, ·) <$> g p.1)).run p.2}[E y.1.1] =
        Pr{let y ← (pure p : ProbComp (α × KeccakCalls.QueryCache))}[E y.1] := by
    intro p
    rw [simulateQ_map, StateT.run_map, prEvent_map]
    rw [prEvent_congr_of_support (pure p : ProbComp (α × KeccakCalls.QueryCache)) _
      (fun _ => E p.1) fun y hy => by
        simp only [support_pure, Set.mem_singleton_iff] at hy
        rw [hy]]
    show Pr{let _ ← (simulateQ randomOracle (g p.1)).run p.2}[E p.1] =
      Pr{let _ ← (pure p : ProbComp (α × KeccakCalls.QueryCache))}[E p.1]
    classical
    by_cases hp : E p.1
    · rw [prEvent_const_of_lossless _ (prEvent_true_eq_one _) hp,
        prEvent_const_of_lossless _ (prEvent_true_eq_one _) hp]
    · rw [prEvent_const_of_not _ hp, prEvent_const_of_not _ hp]
  rw [prEvent_bind_congr _ _ _ _ _ h, bind_pure]

end Compose
