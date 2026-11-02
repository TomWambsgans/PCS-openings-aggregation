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

end Compose
