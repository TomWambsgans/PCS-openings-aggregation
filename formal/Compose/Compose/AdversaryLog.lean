-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The step from the whole transcript to the adversary's follows leanerVM `mumbai`'s
-- `Sound.prEvent_logged2_root_le` (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0,
-- MIT OR Apache-2.0, `lean_vm/LeanVM/Protocol/EndToEnd/Sound/Extractor.lean`): a fresh answer of
-- the verifier that is a root the adversary announced costs `1/2^256` per root and query.
import Compose.ComposedKC
import Compose.Extract

/-!
# The extractor reads the adversary's queries only

`TwoOracle.lean`'s extractor reads the transcript of every Keccak-256 query of the run: the
adversary's, the chain's and the openings'. Here the experiment logs **the adversary's queries
only** (`advExperiment`: `loggedKC A`, then the chain and the openings unlogged), and the
extractor (`adversaryExtractor`) is an explicit, computable function of the adversary's query log
(its Keccak-256 inputs and answers) and the proof: climb the witness table's Merkle tree from the
proof's first root through the log's answers, and decode.

The verifier's queries can change what a root commits to only if one of their fresh answers is
the root itself, or a digest an earlier input refers to (the latter is `ListChain.lean`'s `Coll`).
A fresh Keccak-256 answer after the adversary's last query that is one of the two roots the
adversary announced is a bad query (`rootBad`), of probability at most `2/2^256` (`prob_rootBad`):
the adversary's run, hence its roots, is fixed by the answers already asked (`run_congr`).
Without it, the candidates read off the adversary's log are those read off the whole run's
(`ListCommit.stable`), and `TwoOracle.lean`'s trace applies (`trace_adv`).

**`knowledgeSoundness_list_adv`**, **`knowledgeSoundness_composed_adv`**,
**`knowledgeSoundness_merkle_adv`**: the bounds of `ComposedKC.lean`, the collision term
`4 (Q + 6 + QV)` becoming `5 (Q + 6 + QV)`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol LeanVM.Semantics

/-! ## Generalities -/

/-- A bad fresh query for one predicate is one for a weaker. -/
theorem freshBad_mono {D τ : Type} [DecidableEq D] {b b' : Finset D → D → τ → Prop}
    (h : ∀ H x T, b H x T → b' H x T) (T : τ) :
    ∀ (H : Finset D) (L : List D), FreshBad b T H L → FreshBad b' T H L
  | _, [], hb => hb
  | H, x :: xs, hb => by
    rcases hb with ⟨hx, hbx⟩ | hb
    · exact Or.inl ⟨hx, h _ _ _ hbx⟩
    · exact Or.inr (freshBad_mono h T _ xs hb)

theorem before_append_of_mem {D : Type} [DecidableEq D] {y : D} :
    ∀ (l₁ l₂ : List D), y ∈ l₁ → before (l₁ ++ l₂) y = before l₁ y
  | [], _, h => by simp at h
  | x :: xs, l₂, h => by
    simp only [List.cons_append, before]
    split
    · rfl
    · rename_i hxy
      rw [before_append_of_mem xs l₂ ((List.mem_cons.mp h).resolve_left (Ne.symm hxy))]

theorem subset_before_append {D : Type} [DecidableEq D] {y : D} :
    ∀ (l₁ l₂ : List D), y ∉ l₁ → ∀ q ∈ l₁, q ∈ before (l₁ ++ l₂) y
  | [], _, _, q, hq => by simp at hq
  | x :: xs, l₂, h, q, hq => by
    have hxy : x ≠ y := fun e => h (e ▸ List.mem_cons_self)
    simp only [List.cons_append, before, hxy, ↓reduceIte, Finset.mem_insert]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inl rfl
    · exact Or.inr (subset_before_append xs l₂ (fun h' => h (List.mem_cons_of_mem _ h')) q hq)

/-- **A run reads only the table's answers to its queries.** -/
theorem run_congr {D : Type} {R : D → Type} {α : Type} (oa : OracleComp (OracleSpec.ofFn R) α)
    (T T' : ∀ d, R d) (h : ∀ q ∈ (tableQueryLog oa T).map Sigma.fst, T q = T' q) :
    evalWithAnswerFn (QueryImpl.ofFn T) oa = evalWithAnswerFn (QueryImpl.ofFn T') oa ∧
      tableQueryLog oa T = tableQueryLog oa T' := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind] at h
    have ht : T t = T' t := h t (by simp)
    have h' : ∀ q ∈ (tableQueryLog (k (T t)) T).map Sigma.fst, T q = T' q :=
      fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [ht] at h'
    obtain ⟨he, hl⟩ := ih (T' t) h'
    refine ⟨?_, ?_⟩
    · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      rw [ht]
      exact he
    · rw [tableQueryLog_query_bind, tableQueryLog_query_bind, ht, hl]

/-! ## The experiment and the bad events -/

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) (C₁ : ListCommit B.Msg₁)
  (C₂ : ListCommit B.Msg₂) {O β : Type}


variable {W C₁ C₂} in
/-- No collision makes the order of the queries the order of what they refer to. -/
theorem refers_before {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBad W C₁ C₂) T ∅ L) :
    ∀ y ∈ L, ∀ z ∈ L, Refers z (T y) → y ∈ before L z := by
  have nb : ∀ y ∈ L, ¬ listBad W C₁ C₂ (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad W C₁ C₂) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz h
  by_contra hb
  by_cases hyz : y = z
  · subst hyz
    exact nb y hy (Or.inl (Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩))
  · rcases before_trichotomy L y z hy hz hyz with h' | h'
    · exact hb h'
    · exact nb y hy (Or.inl (Or.inr ⟨z, Finset.mem_insert_of_mem h', h⟩))


/-- **The experiment whose transcript is the adversary's**: the adversary, its Keccak-256 queries
and answers logged; then the chain and the openings, unlogged. -/
def advExperiment (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Run F O β × Transcript) :=
  loggedKC A >>= fun pt => chainWith W hash256 pt.1.1 >>= fun ch => post pt.1 ch >>= fun b =>
    pure (⟨pt.1.1, pt.1.2, ch, b⟩, pt.2)

/-- **The extractor**: an explicit, computable function of the adversary's Keccak-256 query log
(inputs and answers) and the proof: the witness table's Merkle tree climbed down from the proof's
first root through the log's answers, then decoded. -/
def adversaryExtractor (c₁ : TableCode B.Msg₁) (log : Transcript) (π : RootProof F) :
    List B.Msg₁ :=
  c₁.dec (merkleWord (histOfTr log) (tableOfTr log) c₁.height c₁.leafLen π.r₁)

/-- **A fresh Keccak-256 answer after the adversary's last query is one of its roots.** -/
def rootBad (A : OracleComp KeccakCalls (RootProof F × O))
    (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  match d with
  | .inl x => (∀ q ∈ (tableQueryLog A T).map Sigma.fst, q ∈ H) ∧
      (viewT T x = (evalWithAnswerFn (QueryImpl.ofFn T) A).1.r₁ ∨
        viewT T x = (evalWithAnswerFn (QueryImpl.ofFn T) A).1.r₂)
  | .inr _ => False

/-- A bad query: `kcBad`, or a fresh answer that is an announced root. -/
def advBad (A : OracleComp KeccakCalls (RootProof F × O))
    (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  kcBad W C₁ C₂ H d T ∨ rootBad A H d T

/-! ## The new bad event has probability `2/2^256` -/

theorem prEvent_bytes32_eq_le (a : Bytes32) :
    Pr{let u ← $ᵗ Bytes32}[u = a] ≤ (1 : ℝ≥0∞) / 2 ^ 256 := by
  classical
  rw [SampleableType.prEvent_uniformSample, card_bytes32]
  have : (Finset.univ.filter fun u : Bytes32 => u = a).card = 1 := by
    rw [Finset.filter_eq' Finset.univ a]
    simp
  rw [this]
  norm_num

theorem prob_rootBad (A : OracleComp KeccakCalls (RootProof F × O))
    (S : Finset (List UInt8 ⊕ KeccakState))
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[rootBad A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤ (2 : ℝ≥0∞) / 2 ^ 256 := by
  classical
  set Hm := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
    -- Two completions of the cache agree on the inputs asked.
    have hagree : ∀ g g', ∀ q ∈ Hm, extendTable S (completeTable c g) q =
        extendTable S (completeTable c g') q := by
      intro g g' q hq
      obtain ⟨⟨q', hq'S⟩, hq'c, rfl⟩ := Finset.mem_map.mp hq
      rw [show (Function.Embedding.subtype (· ∈ S)) ⟨q', hq'S⟩ = (⟨q', hq'S⟩ : ↥S).1 from rfl,
        extendTable_subtype, extendTable_subtype]
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (mem_cacheDom.mp hq'c)
      simp [completeTable, hv]
    by_cases hex : ∃ g₀, ∀ q ∈ (tableQueryLog A (extendTable S (completeTable c g₀))).map
        Sigma.fst, q ∈ Hm
    · obtain ⟨g₀, hg₀⟩ := hex
      set π₀ := (evalWithAnswerFn (QueryImpl.ofFn (extendTable S (completeTable c g₀))) A).1
      have hx : x ∈ viewH S := mem_viewH.mpr hd
      -- On the event, the roots are the fixed ones.
      refine (prEvent_mono _ _ (fun g => viewG S g ⟨x, hx⟩ = π₀.r₁ ∨
        viewG S g ⟨x, hx⟩ = π₀.r₂) ?_).trans ?_
      · intro g hg
        obtain ⟨hq, hroot⟩ := hg
        have hc := run_congr A (extendTable S (completeTable c g₀))
          (extendTable S (completeTable c g)) fun q hq' => hagree g₀ g q (hg₀ q hq')
        have hfresh : viewT (extendTable S (completeTable c g)) x = viewG S g ⟨x, hx⟩ := by
          show toB (extendTable S (completeTable c g) (⟨.inl x, hd⟩ : ↥S).1) = _
          rw [extendTable_subtype]
          simp [completeTable, ht, viewG]
        rw [hfresh, ← hc.1] at hroot
        exact hroot
      · rw [prEvent_view S (fun h => h ⟨x, hx⟩ = π₀.r₁ ∨ h ⟨x, hx⟩ = π₀.r₂)]
        refine (prEvent_or_le _ _ _).trans ?_
        have h1 := (prEvent_cell (⟨x, hx⟩ : ↥(viewH S)) (fun u : Bytes32 => u = π₀.r₁)).trans
          (prEvent_bytes32_eq_le π₀.r₁)
        have h2 := (prEvent_cell (⟨x, hx⟩ : ↥(viewH S)) (fun u : Bytes32 => u = π₀.r₂)).trans
          (prEvent_bytes32_eq_le π₀.r₂)
        refine (add_le_add h1 h2).trans (le_of_eq ?_)
        rw [ENNReal.div_add_div_same]
        norm_num
    · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
      intro g h
      exact hex ⟨g, h.1⟩

/-- **Each fresh query is bad with probability at most
`(4 |H| + 5) / 2^256 + max L₁ (L₁ L₂) · roundError`.** -/
theorem prob_advBad (A : OracleComp KeccakCalls (RootProof F × O))
    (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[advBad W C₁ C₂ A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((4 * (cacheDom c).card + 5 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (listFactor C₁.bound C₂.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) := by
  refine (prEvent_or_le _ _ _).trans ((add_le_add (prob_kcBad W C₁ C₂ S hS₀ c t ht)
    (prob_rootBad A S c t ht)).trans (le_of_eq ?_))
  rw [add_comm (((4 * (cacheDom c).card + 3 : ℕ) : ℝ≥0∞) / 2 ^ 256), add_assoc,
    ENNReal.div_add_div_same, add_comm]
  congr 2
  push_cast
  ring

/-! ## The trace -/

/-- The run: the adversary, then the chain and the openings. Its queries are those of
`TwoOracle.lean`'s run. -/
theorem advExperiment_run (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (T : KTable) :
    tableQueryLog (advExperiment W A post) T = tableQueryLog (kcRun W A post) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (advExperiment W A post) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (kcRun W A post),
          (tableQueryLog A T).filterMap inlEntry) := by
  have hl := log_loggedKC_run T A []
  have he := eval_loggedKC_run T A []
  rw [List.nil_append] at he
  constructor
  · simp only [advExperiment, kcRun, loggedKC, tableQueryLog_bind, tableQueryLog_pure, hl, he]
  · simp only [advExperiment, kcRun, loggedKC, evalWithAnswerFn_bind, evalWithAnswerFn_pure, he]

theorem advExperiment_queryBound (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (advExperiment W A post) (Q + 6 + QV) := by
  have h : ∀ pt : (RootProof F × O) × Transcript, IsTotalQueryBound
      (chainWith W hash256 pt.1.1 >>= fun ch => post pt.1 ch >>= fun b =>
        (pure (⟨pt.1.1, pt.1.2, ch, b⟩, pt.2) : OracleComp KeccakCalls (Run F O β × Transcript)))
        (6 + (QV + 0)) :=
    fun pt => isTotalQueryBound_bind (chain_queryBound_kc W pt.1.1) fun ch =>
      isTotalQueryBound_bind (hV pt.1 ch) fun b =>
        (trivial : IsTotalQueryBound (pure (⟨pt.1.1, pt.1.2, ch, b⟩, pt.2) :
          OracleComp KeccakCalls (Run F O β × Transcript)) 0)
  have := isTotalQueryBound_bind (isTotalQueryBound_loggedKC_run A Q [] hQ) h
  rwa [Nat.add_zero, ← Nat.add_assoc] at this

theorem mem_filterMap_getLeft? {x : List UInt8} {l : List (List UInt8 ⊕ KeccakState)} :
    x ∈ l.filterMap Sum.getLeft? ↔ Sum.inl x ∈ l := by
  simp

open Classical in
/-- **The trace, with the adversary's transcript**: on every table of both oracles, a run whose
candidates, read off the adversary's queries, satisfy the claims while the witness candidate
fails the relation asks a bad fresh query. -/
theorem trace_adv (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (T : KTable)
    (hwin : ListWins W C₁ C₂ (evalWithAnswerFn (QueryImpl.ofFn T) (advExperiment W A post))) :
    FreshBad (advBad W C₁ C₂ A) T ∅
      ((tableQueryLog (advExperiment W A post) T).map Sigma.fst) := by
  obtain ⟨hlogE, hevalE⟩ := advExperiment_run W A post T
  obtain ⟨hL, heval⟩ := kcRun_run W A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set π := p.1
  rw [hlogE]
  rw [hevalE, heval] at hwin
  set lg := tableQueryLog (kcRun W A post) T
  set lA := tableQueryLog A T
  set Lk := lg.map Sigma.fst
  set L := Lk.filterMap Sum.getLeft?
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft?
  set tr : Transcript := lA.filterMap inlEntry
  -- The adversary's queries come first.
  have hLsplit : ∃ rest, L = LA ++ rest := by
    refine ⟨?_, ?_⟩
    swap
    · simp only [L, LA, hL, List.filterMap_append]
      exact rfl
  obtain ⟨rest, hLA⟩ := hLsplit
  have htrH : histOfTr tr = LA.toFinset := by
    simp only [histOfTr, tr, LA, map_fst_filterMap_inlEntry]
  have htrT : ∀ d ∈ histOfTr tr, tableOfTr tr d = viewT T d := by
    intro d hd
    refine tableOfTr_eq (viewT T) tr (fun e he => ?_) d (by simpa [histOfTr] using hd)
    obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he
    obtain ⟨d', u⟩ := q
    cases d' with
    | inl x =>
      simp only [inlEntry, Option.some.injEq] at hqe
      subst hqe
      have := tableQueryLog_snd_dep T _ _ hq
      simp only at this
      simp [viewT, this]
    | inr s => simp [inlEntry] at hqe
  obtain ⟨g, hg, R, hR, hacc, hsat⟩ := hwin
  simp only at hg hR hacc hsat
  rw [C₁.congr _ _ _ _ htrT, htrH] at hg
  rw [C₂.congr _ _ _ _ htrT, htrH] at hR
  by_contra hnb
  have hk : ¬ FreshBad (kcBad W C₁ C₂) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBad A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBad W C₁ C₂) (viewT T) ∅ L := fun h =>
    hk (freshBad_kc W C₁ C₂ T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := refers_before hl
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, (viewT T w = π.r₁ ∨ viewT T w = π.r₂) → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBad A) T ∅ Lk hr (.inl w) hwk (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    rw [hL]
    exact subset_before_append _ _ hwA' q hq
  -- So the candidates read off the adversary's queries are those read off the run's.
  have hstab : ∀ {M : Type} (C : ListCommit M) (r : Bytes32), (r = π.r₁ ∨ r = π.r₂) →
      C.cands LA.toFinset (viewT T) r = C.cands L.toFinset (viewT T) r := by
    intro M C r hr'
    refine (C.stable LA.toFinset L.toFinset (viewT T) r (fun w hw => ?_) (fun w hw hwr => ?_)
      (fun y hy w hw h => ?_)).symm
    · rw [hLA]
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hw))
    · refine List.mem_toFinset.mpr (hroot w (List.mem_toFinset.mp hw) ?_)
      rcases hr' with rfl | rfl
      · exact Or.inl hwr
      · exact Or.inr hwr
    · have hyA := List.mem_toFinset.mp hy
      have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
      have hb := hord w (List.mem_toFinset.mp hw) y hyL h
      rw [hLA, before_append_of_mem LA rest hyA] at hb
      exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  rw [hstab C₁ π.r₁ (Or.inl rfl)] at hg
  rw [hstab C₂ π.r₂ (Or.inr rfl)] at hR
  refine hl (trace_core W C₁ C₂ L (viewT T) π g R (fun y hy => ?_) hg hR hacc hsat)
  simp only [L, hL, List.filterMap_append]
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [show ∀ (a b c d e f : List UInt8), [(Sum.inl a : List UInt8 ⊕ KeccakState), .inl b, .inl c,
      .inl d, .inl e, .inl f] = [a, b, c, d, e, f].map Sum.inl from fun _ _ _ _ _ _ => rfl,
    filterMap_getLeft?_map_inl]
  exact hy

/-! ## Knowledge soundness with the adversary's transcript -/

/-- **The reduction's list argument, the candidates read off the adversary's queries only.** -/
theorem knowledgeSoundness_list_adv (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (advExperiment W A post)).run' ∅}[ListWins W C₁ C₂ z] ≤
      ((Q + 6 + QV : ℕ) : ℝ≥0∞) * ((listFactor C₁.bound C₂.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) + 5 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (advExperiment W A post)
    (Q + 6 + QV) (advExperiment_queryBound W A post Q QV hQ hV)
    (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
    (Set.finite_range _) (ListWins W C₁ C₂) (advBad W C₁ C₂ A) _ (fun S hS c t ht hcard => ?_)
    (fun T h => trace_adv W C₁ C₂ A post T h)
  have hS' : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
    fun v => hS _ ⟨v, rfl⟩
  refine (prob_advBad W C₁ C₂ A S hS' c t ht).trans ?_
  rw [add_comm]
  gcongr
  have : 4 * (cacheDom c).card + 5 ≤ 5 * (Q + 6 + QV) := by omega
  calc ((4 * (cacheDom c).card + 5 : ℕ) : ℝ≥0∞) ≤ ((5 * (Q + 6 + QV) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast this
    _ = 5 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- **Knowledge soundness of the reduction composed with the openings, the extractor reading the
adversary's queries only**, in mumbai's two-oracle model. -/
theorem knowledgeSoundness_composed_adv (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      WitnessDoomed C₁ z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      QuotientDoomed W C₂ z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[Breaks W C₁ z] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * ((listFactor C₁.bound C₂.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) + 5 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set mx := (simulateQ randomOracle (advExperiment W A openings)).run' ∅
  have hL := knowledgeSoundness_list_adv W C₁ C₂ A openings Q QV hQ hV
  refine (prEvent_mono mx _ _ (breaks_imp W C₁ C₂)).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add hW ((prEvent_or_le _ _ _).trans (add_le_add hσ
    ((prEvent_or_le _ _ _).trans (add_le_add hQd hL))))).trans ?_
  simp only [add_assoc, le_refl]

/-- **The composed statement, the extractor an explicit function of the adversary's query log and
the proof** (`adversaryExtractor`), at the sizes of `quotient::protocol`: the openings' terms plus
`(Q + 6 + QV) (2^-128 + 5 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_merkle_adv (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) (h₁ : c₁.bound ≤ 2 ^ 18)
    (h₂ : c₂.bound ≤ 2 ^ 18)
    (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      WitnessDoomed c₁.commit z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      QuotientDoomed W c₂.commit z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
        Accepted (P := P) z ∧ ∀ g ∈ adversaryExtractor c₁ z.2 z.1.proof,
          ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
        5 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_composed_adv W c₁.commit c₂.commit A openings Q QV hQ hV εW εσ εQ hW
    hσ hQd).trans ?_
  gcongr
  exact listError_le_generic hq hN hw hd h₁ h₂

end Compose
