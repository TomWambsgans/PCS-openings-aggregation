-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Generalises `formal/Compose/Compose/TwoOracle.lean` and `AdversaryLog.lean` of this repository
-- (the list chain in leanerVM `mumbai`'s two-oracle model, https://github.com/Verified-zkEVM/leanerVM,
-- commit 6175f1a0, MIT OR Apache-2.0; the extractor reading the adversary's queries, after mumbai's
-- `Sound.prEvent_logged2_root_le`) to the `k`-round chain of `ListChainK.lean`; the proofs follow
-- theirs, and their lemmas (`prEvent_randomOracle_le_of_freshBad_dep`, the view, `run_congr`,
-- `prEvent_bytes32_eq_le`, the logging lemmas) are reused as they are.
import Compose.ListChainK
import Compose.AdversaryLog

/-!
# The `k`-round list chain in mumbai's two-oracle model, the extractor reading the adversary's
queries

The experiment (`expK`): the adversary (any computation of Keccak-256 and Keccak-f[1600]), its
Keccak-256 queries and answers logged (`loggedKC`); then the verifier (`verK`): the chain of
`ListChainK.lean` over Keccak-256 (`hash256`) on the statement and messages the proof carries
(`view`), then any computation `post` of both oracles (the openings). It has the shape of
`ListChainKRpm.lean`'s two-oracle game (`kcGameG`), so the random-permutation transfer applies to
it as it is.

**What wins** (`ListWinsK`): the messages fit the rounds and some candidates of the rounds' roots,
**read off the adversary's log** (its Keccak-256 inputs and answers), make the opened transcript
lost at the start and won at the end.

A query is bad (`advBadK`) when it is a Keccak-256 query bad for `listBadK` on the view
(`kcBadK`, `TwoOracle.lean`'s view), or when it is asked after the adversary's last query and its
answer is one of the roots the adversary announced (`rootBadK`, at most one per round). So each
fresh query is bad with probability at most `(4 |H| + 3 + k) / 2^256 + maxErrK` (`prob_advBadK`),
and a winning run asks one (`trace_advK`: without `rootBadK` the candidates read off the
adversary's log are those read off the whole run's, `ListCommit.stable`).

**`knowledgeSoundness_listK_adv`**: an adversary of at most `Q` queries, a `post` of at most `QV`,
win with probability at most `N (maxErrK + 5 N / 2^256)`, `N = Q + nQ + QV`, `nQ` the chain's
queries (the label and one per challenge).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics

/-! ## The experiment -/

section Exp

variable {F St M Pf β : Type} [SampleableType F]
variable (K : ChainSpec F St) (C : ℕ → ListCommit M) (R : Piop K M)
  (view : Pf → St × List (RMsg F))

/-- **The verifier after the adversary**: the chain on the statement and messages the proof
carries, then `post` (the openings). -/
def verK (post : Pf → List (List F) → OracleComp KeccakCalls β) (π : Pf) :
    OracleComp KeccakCalls (List (List F) × β) :=
  K.chain hash256 (view π).1 (view π).2 >>= fun ch => post π ch >>= fun b => pure (ch, b)

/-- An outcome: the proof, the challenges and what `post` returns, the adversary's transcript. -/
abbrev OutK (Pf F β : Type) := (Pf × (List (List F) × β)) × Transcript

/-- **The experiment**: the adversary, its Keccak-256 queries logged, then the verifier. -/
def expK (A : OracleComp KeccakCalls Pf) (post : Pf → List (List F) → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (OutK Pf F β) :=
  loggedKC A >>= fun pt => verK K view post pt.1 >>= fun v => pure ((pt.1, v), pt.2)

/-- The run, unlogged. -/
def runK (A : OracleComp KeccakCalls Pf) (post : Pf → List (List F) → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Pf × (List (List F) × β)) :=
  A >>= fun p => verK K view post p >>= fun v => pure (p, v)

/-- **What wins the list game**: the messages fit the rounds, and some candidates of the rounds'
roots, read off the adversary's transcript, make the opened transcript lost at the start and won
at the end. -/
def ListWinsK (z : OutK Pf F β) : Prop :=
  FitsAll K.rounds (view z.1.1).2 ∧ ∃ cs, List.Forall₂ (· ∈ ·) cs
    (candLists C (histOfTr z.2) (tableOfTr z.2) 0 (view z.1.1).2) ∧
      R.LostWon (view z.1.1).1 (opened cs (view z.1.1).2 z.1.2.1)

/-- The roots the messages of the rounds carry. -/
def ChainSpec.rootsK (ms : List (RMsg F)) : List Bytes32 :=
  (ms.take K.rounds.length).filterMap Prod.fst

theorem ChainSpec.length_rootsK_le (ms : List (RMsg F)) :
    (K.rootsK ms).length ≤ K.rounds.length :=
  (List.length_filterMap_le _ _).trans (List.length_take_le _ _)

/-! ## The bad events -/

/-- **A bad query of both oracles**: a Keccak-256 query bad for the view; never a Keccak-f
query. -/
def kcBadK (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) :
    Prop :=
  match d with
  | .inl x => listBadK K C R (viewH H) x (viewT T)
  | .inr _ => False

/-- **A fresh Keccak-256 answer after the adversary's last query is one of its roots.** -/
def rootBadK (A : OracleComp KeccakCalls Pf) (H : Finset (List UInt8 ⊕ KeccakState))
    (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  match d with
  | .inl x => (∀ q ∈ (tableQueryLog A T).map Sigma.fst, q ∈ H) ∧
      viewT T x ∈ K.rootsK (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).2
  | .inr _ => False

/-- A bad query: `kcBadK`, or a fresh answer that is an announced root. -/
def advBadK (A : OracleComp KeccakCalls Pf) (H : Finset (List UInt8 ⊕ KeccakState))
    (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  kcBadK K C R H d T ∨ rootBadK K view A H d T

theorem freshBad_kcK (T : KTable) : ∀ (H : Finset (List UInt8 ⊕ KeccakState))
    (L : List (List UInt8 ⊕ KeccakState)),
    FreshBad (listBadK K C R) (viewT T) (viewH H) (L.filterMap Sum.getLeft?) →
      FreshBad (kcBadK K C R) T H L
  | _, [], h => by simp [FreshBad] at h
  | H, .inl x :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, FreshBad] at h ⊢
    rcases h with ⟨hx, hb⟩ | h
    · exact Or.inl ⟨fun hm => hx (mem_viewH.mpr hm), hb⟩
    · refine Or.inr (freshBad_kcK T _ L ?_)
      rwa [viewH_insert_inl]
  | H, .inr s :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, FreshBad] at h ⊢
    refine Or.inr (freshBad_kcK T _ L ?_)
    rwa [viewH_insert_inr]

/-! ## Each fresh query is bad with small probability -/

variable [Fintype F] [DecidableEq F]

/-- **Each fresh query of both oracles is bad for the view with probability at most
`(4 |H| + 3) / 2^256 + maxErrK`.** -/
theorem prob_kcBadK (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[kcBadK K C R
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((4 * (cacheDom c).card + 3 : ℕ) : ℝ≥0∞) / 2 ^ 256 + maxErrK K C R := by
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
    have hx : x ∈ viewH S := mem_viewH.mpr hd
    have hS₁ : ∀ v : Bytes32, v.toList ∈ viewH S := fun v => mem_viewH.mpr (hS₀ v)
    have hc₁ : viewC S c ⟨x, hx⟩ = none := by simp [viewC, ht]
    have hH : histOf (viewC S c) ⊆ viewH S := fun y hy => (mem_histOf.mp hy).1
    have hev : ∀ g, kcBadK K C R ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) (.inl x)
        (extendTable S (completeTable c g)) ↔
        listBadK K C R (histOf (viewC S c)) x (tableOf (viewC S c) (viewG S g)) := by
      intro g
      show listBadK K C R _ x _ ↔ _
      rw [← histOf_viewC]
      exact listBadK_congr K C R (fun y hy => viewT_extendTable c g (hH hy))
        (viewT_extendTable c g hx) (fun v => viewT_extendTable c g (hS₁ v))
    refine (prEvent_mono _ _ (fun g => listBadK K C R (histOf (viewC S c)) x
      (tableOf (viewC S c) (viewG S g))) fun g h => (hev g).mp h).trans ?_
    rw [prEvent_view S (fun h => listBadK K C R (histOf (viewC S c)) x (tableOf (viewC S c) h))]
    refine (prob_listBadK K C R hS₁ (viewC S c) ⟨x, hx⟩ hc₁).trans ?_
    gcongr
    have hcard : (histOf (viewC S c)).card ≤ (cacheDom c).card := by
      rw [histOf_viewC]
      refine (Finset.card_le_card_of_injOn
        (t := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))) Sum.inl (fun y hy => ?_)
        Sum.inl_injective.injOn).trans (Finset.card_map (Function.Embedding.subtype (· ∈ S))).le
      exact mem_viewH.mp hy
    omega

/-- **A fresh answer is one of the adversary's roots with probability at most `k / 2^256`.** -/
theorem prob_rootBadK (A : OracleComp KeccakCalls Pf) (S : Finset (List UInt8 ⊕ KeccakState))
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[rootBadK K view A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤ (K.rounds.length : ℝ≥0∞) / 2 ^ 256 := by
  classical
  set Hm := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
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
      obtain ⟨rs₀, hrs₀⟩ : ∃ l, l = K.rootsK (view (evalWithAnswerFn
        (QueryImpl.ofFn (extendTable S (completeTable c g₀))) A)).2 := ⟨_, rfl⟩
      have hx : x ∈ viewH S := mem_viewH.mpr hd
      refine (prEvent_mono _ _ (fun g => ∃ r ∈ rs₀, viewG S g ⟨x, hx⟩ = r) ?_).trans ?_
      · intro g hg
        obtain ⟨hq, hroot⟩ := hg
        have hc := run_congr A (extendTable S (completeTable c g₀))
          (extendTable S (completeTable c g)) fun q hq' => hagree g₀ g q (hg₀ q hq')
        have hfresh : viewT (extendTable S (completeTable c g)) x = viewG S g ⟨x, hx⟩ := by
          show toB (extendTable S (completeTable c g) (⟨.inl x, hd⟩ : ↥S).1) = _
          rw [extendTable_subtype]
          simp [completeTable, ht, viewG]
        rw [hfresh, ← hc.1, ← hrs₀] at hroot
        exact ⟨_, hroot, rfl⟩
      · rw [prEvent_view S (fun h => ∃ r ∈ rs₀, h ⟨x, hx⟩ = r)]
        have hone : ∀ r : Bytes32, Pr{let h ← $ᵗ (↥(viewH S) → Bytes32)}[h ⟨x, hx⟩ = r] ≤
            (1 : ℝ≥0∞) / 2 ^ 256 := fun r =>
          (prEvent_cell (⟨x, hx⟩ : ↥(viewH S)) (fun u : Bytes32 => u = r)).trans
            (prEvent_bytes32_eq_le r)
        refine (prEvent_exists_mem_le _ _ _ rs₀ fun r _ => hone r).trans ?_
        rw [mul_one_div]
        gcongr
        rw [hrs₀]
        exact_mod_cast K.length_rootsK_le _
    · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
      intro g h
      exact hex ⟨g, h.1⟩

/-- **Each fresh query is bad with probability at most
`(4 |H| + 3 + k) / 2^256 + maxErrK`.** -/
theorem prob_advBadK (A : OracleComp KeccakCalls Pf) (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[advBadK K C R view A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((4 * (cacheDom c).card + 3 + K.rounds.length : ℕ) : ℝ≥0∞) / 2 ^ 256 + maxErrK K C R := by
  refine (prEvent_or_le _ _ _).trans ((add_le_add (prob_kcBadK K C R S hS₀ c t ht)
    (prob_rootBadK K view A S c t ht)).trans (le_of_eq ?_))
  rw [add_comm (((4 * (cacheDom c).card + 3 : ℕ) : ℝ≥0∞) / 2 ^ 256), add_assoc,
    ENNReal.div_add_div_same, add_comm]
  congr 2
  push_cast
  ring

/-! ## The run against a table -/

/-- **The chain against a table**: it asks the chain's inputs and returns their answers. -/
theorem runM_run (T : KTable) : ∀ (y : List UInt8) (es : List (List UInt8)),
    (tableQueryLog (runM hash256 y es) T).map Sigma.fst = (allIn (viewT T) y es).map Sum.inl ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (runM hash256 y es) = (allIn (viewT T) y es).map (viewT T)
  | y, [] => by
    simp only [runM, hash256, callKeccak256, bind_assoc, pure_bind, tableQueryLog_query_bind,
      tableQueryLog_pure, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_pure, allIn, List.map_cons, List.map_nil]
    refine ⟨?_, ?_⟩ <;> trivial
  | y, e :: es => by
    obtain ⟨ih1, ih2⟩ := runM_run T (stepIn (viewT T y) e) es
    simp only [runM, hash256, callKeccak256, bind_assoc, pure_bind,
      tableQueryLog_bind, tableQueryLog_pure, List.append_nil, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure, allIn, List.map_cons]
    refine ⟨?_, ?_⟩
    · exact congrArg (List.cons _) ih1
    · exact congrArg (List.cons _) ih2

theorem isTotalQueryBound_runM : ∀ (y : List UInt8) (es : List (List UInt8)),
    IsTotalQueryBound (runM hash256 y es) (es.length + 1)
  | y, [] => by
    simp only [runM, hash256, callKeccak256, bind_assoc, pure_bind]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩
  | y, e :: es => by
    simp only [runM, hash256, callKeccak256, bind_assoc, pure_bind]
    refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun u => ?_⟩
    have := isTotalQueryBound_bind
      (ob := fun rest => (pure (toB u :: rest) : OracleComp KeccakCalls (List Bytes32))) (n₂ := 0)
      (isTotalQueryBound_runM (stepIn (toB u) e) es) fun _ => trivial
    simpa using this

theorem nSteps_ge_length : ∀ rs : List RoundSpec, rs.length ≤ nSteps rs
  | [] => le_rfl
  | s :: rs => by simp only [List.length_cons, nSteps]; have := nSteps_ge_length rs; omega

theorem isTotalQueryBound_verK (post : Pf → List (List F) → OracleComp KeccakCalls β) (QV : ℕ)
    (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) (π : Pf) :
    IsTotalQueryBound (verK K view post π) (K.nQ + QV) := by
  have h := isTotalQueryBound_bind
    (ob := fun sts => post π (K.chalsOf sts) >>= fun b =>
      (pure (K.chalsOf sts, b) : OracleComp KeccakCalls (List (List F) × β)))
    (isTotalQueryBound_runM (K.label (view π).1) (absorbs K.lim K.rounds (view π).2)) fun sts =>
      isTotalQueryBound_bind (ob := fun b =>
        (pure (K.chalsOf sts, b) : OracleComp KeccakCalls (List (List F) × β))) (n₂ := 0)
        (hV π (K.chalsOf sts)) fun _ => trivial
  rw [length_absorbs] at h
  have e : verK K view post π = runM hash256 (K.label (view π).1)
      (absorbs K.lim K.rounds (view π).2) >>= fun sts => post π (K.chalsOf sts) >>= fun b =>
        pure (K.chalsOf sts, b) := by
    simp [verK, ChainSpec.chain, bind_map_left]
  rw [e, ChainSpec.nQ]
  simpa using h

theorem expK_queryBound (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (expK K view A post) (Q + K.nQ + QV) := by
  have h : ∀ pt : Pf × Transcript, IsTotalQueryBound (verK K view post pt.1 >>= fun v =>
      (pure ((pt.1, v), pt.2) : OracleComp KeccakCalls (OutK Pf F β))) (K.nQ + QV + 0) :=
    fun pt => isTotalQueryBound_bind (isTotalQueryBound_verK K view post QV hV pt.1) fun v =>
      (trivial : IsTotalQueryBound (pure ((pt.1, v), pt.2) :
        OracleComp KeccakCalls (OutK Pf F β)) 0)
  have := isTotalQueryBound_bind (isTotalQueryBound_loggedKC_run A Q [] hQ) h
  rwa [Nat.add_zero, ← Nat.add_assoc] at this

/-- The experiment against a table: the run's queries, and the adversary's transcript. -/
theorem expK_run (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable) :
    tableQueryLog (expK K view A post) T = tableQueryLog (runK K view A post) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (expK K view A post) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (runK K view A post),
          (tableQueryLog A T).filterMap inlEntry) := by
  have hl := log_loggedKC_run T A []
  have he := eval_loggedKC_run T A []
  rw [List.nil_append] at he
  constructor
  · simp only [expK, runK, loggedKC, tableQueryLog_bind, tableQueryLog_pure, hl, he]
  · simp only [expK, runK, loggedKC, evalWithAnswerFn_bind, evalWithAnswerFn_pure, he]

/-- The run against a table: the adversary's queries, the chain's inputs, the openings'. -/
theorem runK_run (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let ch := chalsT K.lim (viewT T) (K.label (view p).1) K.rounds (view p).2
    (tableQueryLog (runK K view A post) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          ((allIn (viewT T) (K.label (view p).1) (absorbs K.lim K.rounds (view p).2)).map
            Sum.inl ++ (tableQueryLog (post p ch) T).map Sigma.fst) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (runK K view A post) =
        (p, (ch, evalWithAnswerFn (QueryImpl.ofFn T) (post p ch))) := by
  intro p ch
  obtain ⟨h1, h2⟩ := runM_run T (K.label (view p).1) (absorbs K.lim K.rounds (view p).2)
  have hch : K.chalsOf ((allIn (viewT T) (K.label (view p).1)
      (absorbs K.lim K.rounds (view p).2)).map (viewT T)) = ch := by
    simp only [ChainSpec.chalsOf, ch, chalsT]
    congr 2
    cases allIn (viewT T) (K.label (view p).1) (absorbs K.lim K.rounds (view p).2) <;> rfl
  constructor
  · simp only [runK, verK, ChainSpec.chain, tableQueryLog_bind, tableQueryLog_pure,
      List.map_append, List.append_nil, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind]
    rw [h1, h2, hch]
  · simp only [runK, verK, ChainSpec.chain, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rw [h2, hch]

/-! ## The trace -/

variable {K C R} in
/-- No collision makes the order of the queries the order of what they refer to. -/
theorem refers_beforeK {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBadK K C R) T ∅ L) :
    ∀ y ∈ L, ∀ z ∈ L, Refers z (T y) → y ∈ before L z := by
  have nb : ∀ y ∈ L, ¬ listBadK K C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadK K C R) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz h
  by_contra hb
  by_cases hyz : y = z
  · subst hyz
    exact nb y hy (Or.inl (Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩))
  · rcases before_trichotomy L y z hy hz hyz with h' | h'
    · exact hb h'
    · exact nb y hy (Or.inl (Or.inr ⟨z, Finset.mem_insert_of_mem h', h⟩))

open Classical in
/-- **The trace, with the adversary's transcript**: on every table of both oracles, a run whose
candidates, read off the adversary's queries, make the transcript lost at the start and won at
the end asks a bad fresh query. -/
theorem trace_advK (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable)
    (hwin : ListWinsK K C R view (evalWithAnswerFn (QueryImpl.ofFn T) (expK K view A post))) :
    FreshBad (advBadK K C R view A) T ∅ ((tableQueryLog (expK K view A post) T).map Sigma.fst) := by
  obtain ⟨hlogE, hevalE⟩ := expK_run K view A post T
  obtain ⟨hL, heval⟩ := runK_run K view A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set s := (view p).1
  set ms := (view p).2
  rw [hlogE]
  rw [hevalE, heval] at hwin
  set lg := tableQueryLog (runK K view A post) T
  set lA := tableQueryLog A T
  set Lk := lg.map Sigma.fst
  set L := Lk.filterMap Sum.getLeft?
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft?
  set tr : Transcript := lA.filterMap inlEntry
  have hLsplit : ∃ rest, L = LA ++ rest := by
    refine ⟨?_, ?_⟩
    swap
    · simp only [L, LA, Lk, hL, List.filterMap_append]
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
  obtain ⟨hfit, cs, hcs, hlw⟩ := hwin
  simp only at hfit hcs hlw
  rw [candLists_congr C htrT, htrH] at hcs
  by_contra hnb
  have hk : ¬ FreshBad (kcBadK K C R) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadK K C R) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcK K C R T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := refers_beforeK hl
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ K.rootsK ms → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBadK K view A) T ∅ Lk hr (.inl w) hwk (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    simp only [Lk, lg, hL]
    exact subset_before_append _ _ hwA' q hq
  -- So the candidates read off the adversary's queries are those read off the run's.
  have hstab : ∀ {N : Type} (Cn : ListCommit N) (r : Bytes32), r ∈ K.rootsK ms →
      Cn.cands LA.toFinset (viewT T) r = Cn.cands L.toFinset (viewT T) r := by
    intro N Cn r hr'
    refine (Cn.stable LA.toFinset L.toFinset (viewT T) r (fun w hw => ?_) (fun w hw hwr => ?_)
      (fun y hy w hw h => ?_)).symm
    · rw [hLA]
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hw))
    · exact List.mem_toFinset.mpr (hroot w (List.mem_toFinset.mp hw) (hwr ▸ hr'))
    · have hyA := List.mem_toFinset.mp hy
      have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
      have hb := hord w (List.mem_toFinset.mp hw) y hyL h
      rw [hLA, before_append_of_mem LA rest hyA] at hb
      exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  have hms : ms.take K.rounds.length = ms := List.take_of_length_le (le_of_eq hfit.length_eq)
  rw [candLists_stable C 0 ms fun m hm r hr k => hstab (C k) r (by
    simp only [ChainSpec.rootsK, hms]
    exact List.mem_filterMap.mpr ⟨m, hm, hr⟩)] at hcs
  refine hl (trace_coreK K C R L (viewT T) s ms cs hfit (fun y hy => ?_) hcs hlw)
  simp only [L, Lk, lg, hL, List.filterMap_append]
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [filterMap_getLeft?_map_inl]
  exact hy

/-! ## Knowledge soundness of the list game -/

/-- **The `k`-round list game, the candidates read off the adversary's queries only**, in
mumbai's two-oracle model: at most `N (maxErrK + 5 N / 2^256)`, `N = Q + nQ + QV`. -/
theorem knowledgeSoundness_listK_adv (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (expK K view A post)).run' ∅}[ListWinsK K C R view z] ≤
      ((Q + K.nQ + QV : ℕ) : ℝ≥0∞) * (maxErrK K C R +
        5 * ((Q + K.nQ + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (expK K view A post)
    (Q + K.nQ + QV) (expK_queryBound K view A post Q QV hQ hV)
    (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
    (Set.finite_range _) (ListWinsK K C R view) (advBadK K C R view A) _
    (fun S hS c t ht hcard => ?_) (fun T h => trace_advK K C R view A post T h)
  have hS' : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
    fun v => hS _ ⟨v, rfl⟩
  refine (prob_advBadK K C R view A S hS' c t ht).trans ?_
  rw [add_comm]
  gcongr
  have hk : K.rounds.length < K.nQ := by
    have := nSteps_ge_length K.rounds
    simp only [ChainSpec.nQ]
    omega
  have : 4 * (cacheDom c).card + 3 + K.rounds.length ≤ 5 * (Q + K.nQ + QV) := by omega
  calc ((4 * (cacheDom c).card + 3 + K.rounds.length : ℕ) : ℝ≥0∞)
      ≤ ((5 * (Q + K.nQ + QV) : ℕ) : ℝ≥0∞) := by exact_mod_cast this
    _ = 5 * ((Q + K.nQ + QV : ℕ) : ℝ≥0∞) := by push_cast; ring

end Exp

end Compose
