-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The bad-query engine for dependent answer types (`prEvent_randomOracle_le_of_freshBad_dep`)
-- generalises `formal/QuotientRpm/FreshBad.lean`'s `prEvent_randomOracle_le_of_freshBad`, which
-- follows VCVio's `prEvent_randomOracle_le_of_bad_queries` (https://github.com/Verified-zkEVM/VCVio,
-- commit afa6593f, Apache-2.0). The model is leanerVM `mumbai`'s (https://github.com/Verified-zkEVM/leanerVM,
-- commit 6175f1a0, MIT OR Apache-2.0): `KeccakCalls`, `callKeccak256`, `Digest.toRpm`.
import Compose.Openings
import LeanVM.Protocol.WithHash
import Common.Lanes

/-!
# The composition in mumbai's two-oracle model

F2's `family_sound` lives in leanerVM `mumbai`'s random-oracle model `KeccakCalls`: Keccak-256
(`Bytes → Digest`, queries `.inl x`) and Keccak-f[1600] (`KeccakState → KeccakState`, queries
`.inr s`), two independent lazily sampled oracles. This file moves the reduction's list argument
there, so that the chain, the Merkle trees and the openings are answered by **one** oracle model:

* **the engine** (`prEvent_randomOracle_le_of_freshBad_dep`): `QuotientRpm`'s bad-fresh-query
  bound for answer types that depend on the input (`KeccakCalls` is `Sum.elim` of the two);
* **the view** (`viewT`, `viewH`): Keccak-256's answers as 32 bytes (`Digest.toRpm`), on the
  Keccak-256 inputs; a query is bad when it is Keccak-256's and `listBad` of the view
  (`kcBad`); Keccak-f's queries are never bad (`freshBad_kc`);
* **the pushforward** (`prEvent_view`): a uniform table of both oracles on a finite set, read
  through the view, is a uniform table of 32-byte answers on its Keccak-256 inputs; so each
  fresh query is bad with probability at most `listBad`'s bound (`prob_kcBad`);
* **the experiment** (`kcExperiment`): the adversary, the chain over Keccak-256
  (`hash256`), then any computation of both oracles (the openings), with the transcript of the
  Keccak-256 queries (`loggedKC`).

**`knowledgeSoundness_list_kc`** and **`knowledgeSoundness_composed_kc`**: the bounds of
`ListChain.lean` and `Openings.lean`, in mumbai's model.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params

/-! ## The engine, for answers whose type depends on the input -/

/-- The uniform table on a finite set of inputs, for dependent answer types. -/
noncomputable local instance instSampleablePiSubtype {D : Type} {R : D → Type} [∀ d, Fintype (R d)]
    [∀ d, Nonempty (R d)] (S : Finset D) : SampleableType ((d : ↥S) → R d.1) :=
  SampleableType.piOfFintype _

section Engine

variable {D : Type} {R : D → Type} [DecidableEq D]

theorem isTotalQueryBound_restrictQueries_dep [∀ d, Finite (R d)] (S : Finset D) {α : Type}
    (oa : OracleComp (OracleSpec.ofFn R) α) (h : AllQueriesSatisfy oa (· ∈ S)) :
    ∀ n, IsTotalQueryBound oa n → IsTotalQueryBound (restrictQueries S oa h) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; trivial
  | query_bind t k ih =>
    intro n hb
    exact ⟨hb.1, fun u => ih u (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) _ (hb.2 u)⟩

omit [DecidableEq D] in
theorem restrictCache_empty_dep (S : Finset D) :
    restrictCache S (∅ : (OracleSpec.ofFn R).QueryCache) = ∅ := by
  ext d
  rfl

variable [∀ d, Fintype (R d)] [∀ d, Nonempty (R d)] [∀ d, SampleableType (R d)]

/-- **Bad fresh queries bound an event of the lazily sampled oracle, for dependent answer
types**: `QuotientRpm.prEvent_randomOracle_le_of_freshBad` with `R d` in place of one type. -/
theorem prEvent_randomOracle_le_of_freshBad_dep {α : Type}
    (oa : OracleComp (OracleSpec.ofFn R) α) (n : ℕ) (hn : IsTotalQueryBound oa n) (S₀ : Set D)
    (hS₀ : S₀.Finite) (event : α → Prop) (bad : Finset D → D → (∀ d, R d) → Prop) (ε : ℝ≥0∞)
    (hbad : ∀ S : Finset D, (∀ d ∈ S₀, d ∈ S) →
      ∀ (c : (OracleSpec.ofFn fun d : ↥S => R d.1).QueryCache) (t : ↥S),
        c t = none → (cacheDom c).card < n →
        Pr{let g ← $ᵗ ((d : ↥S) → R d.1)}[bad ((cacheDom c).map
          (Function.Embedding.subtype (· ∈ S))) t.1 (extendTable S (completeTable c g))] ≤ ε)
    (htrace : ∀ T : (∀ d, R d), event (evalWithAnswerFn (QueryImpl.ofFn T) oa) →
      FreshBad bad T ∅ ((tableQueryLog oa T).map Sigma.fst)) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤ n * ε := by
  classical
  let S := possibleQueryKeys oa ∪ hS₀.toFinset
  have hS : AllQueriesSatisfy oa (· ∈ S) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun d hd => Finset.mem_union_left _ hd
  let small := restrictQueries S oa hS
  have hrun : (simulateQ randomOracle small).run' ∅ = (simulateQ randomOracle oa).run' ∅ := by
    rw [← randomOracle_restrictQueries S oa hS ∅, restrictCache_empty_dep]
  rw [← hrun]
  let : MeasurableSpace α := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable small ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq event]
  simp only [prEvent_norm]
  let e : ↥S ↪ D := Function.Embedding.subtype (· ∈ S)
  let bad' : Finset ↥S → ↥S → ((d : ↥S) → R d.1) → Prop := fun H' x' g' =>
    bad (H'.map e) x'.1 (extendTable S g')
  have htrace' : ∀ g : (d : ↥S) → R d.1, event (evalWithAnswerFn (QueryImpl.ofFn g) small) →
      FreshBadRun bad' small g ∅ := by
    intro g hev
    have hg : (fun d : ↥S => extendTable S g d.1) = g := funext (extendTable_subtype S g)
    have heval := evalWithAnswerFn_restrictQueries S oa hS (extendTable S g)
    rw [hg] at heval
    have h := htrace (extendTable S g) (heval ▸ hev)
    have hlog := tableQueryLog_restrictQueries S oa hS (extendTable S g)
    rw [hg] at hlog
    rw [← hlog, List.map_map] at h
    have hm : (Sigma.fst ∘ fun q : (Σ d : ↥S, R d.1) => (⟨q.1.1, q.2⟩ : Σ d : D, R d)) =
        e ∘ Sigma.fst := rfl
    rw [hm, ← List.map_map, show (∅ : Finset D) = (∅ : Finset ↥S).map e from rfl] at h
    have h' := (freshBad_map e bad (extendTable S) g ∅ _).mp h
    simp only [FreshBadRun, completeTable_empty, cacheDom_empty]
    exact h'
  refine (prEvent_mono _ _ _ htrace').trans ?_
  exact prEvent_freshBad_le (D := ↥S) (R := fun d => R d.1) bad' ε n
    (fun c t hct hcard => hbad S (fun d hd => Finset.mem_union_right _ (hS₀.mem_toFinset.mpr hd))
      c t hct hcard) small n (isTotalQueryBound_restrictQueries_dep S oa hS n hn) ∅ (by simp)

end Engine

end Compose
