-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Generalises `formal/Compose/Compose/ListChainKAdv.lean` (the experiment, the adversary's log, the
-- trace through `ListCommit.stable`), `ListChainKComposed.lean` (`breaksK_imp`) and
-- `ListChainKDoom.lean` (the openings' stages, their doom by F2, `trace_whir`,
-- `knowledgeSoundness_listChainK_closed`) of this repository to `ListChainU.lean`'s chain; their
-- proofs are followed step by step, and their definitions and lemmas that do not read the chain
-- (the openings, the stages, the doom terms, the list game `ListWinsK`, `rootBadK`) are reused.
import Compose.ListChainU

/-!
# The chain over any encoding with WHIR openings: the doom terms discharged

`ListChainKDoom.lean`'s `knowledgeSoundness_listChainK_closed` for `ListChainU.lean`'s chain
(`ChainSpecU`): the verifier runs the chain (`verU`, `U.chain` over Keccak-256), then the
openings (`opsRun`, F2's `opening::verify` for each `WhirOp`); the experiment logs the adversary's
Keccak-256 queries (`expU`).

* **The bad events** (`advBadU`): a Keccak-256 query bad for `listBadU` on the view (`kcBadU`), or
  a fresh answer after the adversary's last query that is one of its roots (`rootBadK`); each fresh
  query is bad with probability at most
  `(|H| + nRf (|H| + 1) + k) / 2^256 + tagBound + maxErrK` (`prob_advBadU`).
* **The trace** (`trace_advU`): a run winning the list game (`ListWinsK`, on the candidates read
  off the adversary's log) asks a bad fresh query; `breaksU_imp`: a broken run has a doomed
  opening or wins the list game, **with the protocol's last state needed only for candidates that
  are `none` at the rounds without a root** (the candidates the lists hold there).
* **`knowledgeSoundness_listChainU_closed`**: for the setup (any computation of the oracles, `QS`
  queries) then the adversary (`Q` queries), the verifier accepts while no candidate of round
  `0`'s root, read off their queries, satisfies the first round's state with probability at most

  `doomSum ops (QS + Q + nQ) + N (maxErrK + tagBound + (nRf + 2) N / 2^256)`,
  `N = QS + Q + nQ + Σ_k QO_k`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Protocol.Rom (romExperiment romExperiment_map)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The experiment -/

section Exp

variable {F St M Pf β : Type} [SampleableType F]
variable (U : ChainSpecU F St) (C : ℕ → ListCommit M) (R : Piop U.K M)
  (view : Pf → St × List (RMsg F))

/-- **The verifier after the adversary**: the chain on the statement and messages the proof
carries, then `post` (the openings). -/
def verU (post : Pf → List (List F) → OracleComp KeccakCalls β) (π : Pf) :
    OracleComp KeccakCalls (List (List F) × β) :=
  U.chain hash256 (view π).1 (view π).2 >>= fun ch => post π ch >>= fun b => pure (ch, b)

/-- **The experiment**: the adversary, its Keccak-256 queries logged, then the verifier. -/
def expU (A : OracleComp KeccakCalls Pf) (post : Pf → List (List F) → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (OutK Pf F β) :=
  loggedKC A >>= fun pt => verU U view post pt.1 >>= fun v => pure ((pt.1, v), pt.2)

/-- The run, unlogged. -/
def runU (A : OracleComp KeccakCalls Pf) (post : Pf → List (List F) → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Pf × (List (List F) × β)) :=
  A >>= fun p => verU U view post p >>= fun v => pure (p, v)

/-! ## The bad events -/

/-- **A bad query of both oracles**: a Keccak-256 query bad for the view; never a Keccak-f
query. -/
def kcBadU (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) :
    Prop :=
  match d with
  | .inl x => listBadU U C R (viewH H) x (viewT T)
  | .inr _ => False

/-- A bad query: `kcBadU`, or a fresh answer that is an announced root. -/
def advBadU (A : OracleComp KeccakCalls Pf) (H : Finset (List UInt8 ⊕ KeccakState))
    (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  kcBadU U C R H d T ∨ rootBadK U.K view A H d T

theorem freshBad_kcU (T : KTable) : ∀ (H : Finset (List UInt8 ⊕ KeccakState))
    (L : List (List UInt8 ⊕ KeccakState)),
    FreshBad (listBadU U C R) (viewT T) (viewH H) (L.filterMap Sum.getLeft?) →
      FreshBad (kcBadU U C R) T H L
  | _, [], h => by simp [FreshBad] at h
  | H, .inl x :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, FreshBad] at h ⊢
    rcases h with ⟨hx, hb⟩ | h
    · exact Or.inl ⟨fun hm => hx (mem_viewH.mpr hm), hb⟩
    · refine Or.inr (freshBad_kcU T _ L ?_)
      rwa [viewH_insert_inl]
  | H, .inr s :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, FreshBad] at h ⊢
    refine Or.inr (freshBad_kcU T _ L ?_)
    rwa [viewH_insert_inr]

/-! ## The run against a table -/

theorem isTotalQueryBound_chainU (s : St) (ms : List (RMsg F)) :
    IsTotalQueryBound (U.chain hash256 s ms) U.K.nQ := by
  have h := isTotalQueryBound_runM (U.label s) (U.absorbsS s U.K.rounds ms)
  rw [ChainSpecU.absorbsS, length_absorbsI] at h
  show IsTotalQueryBound (U.K.chalsOf <$> runM hash256 (U.label s) (U.absorbsS s U.K.rounds ms))
    (nSteps U.K.rounds + 1)
  exact (isQueryBound_map_iff _ _ _ _ _).mpr h

/-- The experiment against a table: the run's queries, and the adversary's transcript. -/
theorem expU_run (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable) :
    tableQueryLog (expU U view A post) T = tableQueryLog (runU U view A post) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (expU U view A post) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (runU U view A post),
          (tableQueryLog A T).filterMap inlEntry) := by
  have hl := log_loggedKC_run T A []
  have he := eval_loggedKC_run T A []
  rw [List.nil_append] at he
  constructor
  · simp only [expU, runU, loggedKC, tableQueryLog_bind, tableQueryLog_pure, hl, he]
  · simp only [expU, runU, loggedKC, evalWithAnswerFn_bind, evalWithAnswerFn_pure, he]

/-- The run against a table: the adversary's queries, the chain's inputs, the openings'. -/
theorem runU_run (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let ch := U.chalsT (viewT T) (view p).1 U.K.rounds (view p).2
    (tableQueryLog (runU U view A post) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          ((allIn (viewT T) (U.label (view p).1) (U.absorbsS (view p).1 U.K.rounds (view p).2)).map
            Sum.inl ++ (tableQueryLog (post p ch) T).map Sigma.fst) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (runU U view A post) =
        (p, (ch, evalWithAnswerFn (QueryImpl.ofFn T) (post p ch))) := by
  intro p ch
  obtain ⟨h1, h2⟩ := runM_run T (U.label (view p).1) (U.absorbsS (view p).1 U.K.rounds (view p).2)
  have hch : U.K.chalsOf ((allIn (viewT T) (U.label (view p).1)
      (U.absorbsS (view p).1 U.K.rounds (view p).2)).map (viewT T)) = ch := by
    simp only [ChainSpec.chalsOf, ch, ChainSpecU.chalsT, chalsTI, ChainSpecU.absorbsS]
    congr 2
    cases allIn (viewT T) (U.label (view p).1) (absorbsI (U.encAt (view p).1) 0 U.K.rounds
      (view p).2) <;> rfl
  constructor
  · simp only [runU, verU, ChainSpecU.chain, tableQueryLog_bind, tableQueryLog_pure,
      List.map_append, List.append_nil, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind]
    rw [h1, h2, hch]
  · simp only [runU, verU, ChainSpecU.chain, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rw [h2, hch]

/-! ## The trace -/

open Classical in
/-- **The trace, with the adversary's transcript**: on every table of both oracles, a run whose
candidates, read off the adversary's queries, make the transcript lost at the start and won at
the end asks a bad fresh query. -/
theorem trace_advU (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable)
    (hwin : ListWinsK U.K C R view (evalWithAnswerFn (QueryImpl.ofFn T) (expU U view A post))) :
    FreshBad (advBadU U C R view A) T ∅ ((tableQueryLog (expU U view A post) T).map Sigma.fst) := by
  obtain ⟨hlogE, hevalE⟩ := expU_run U view A post T
  obtain ⟨hL, heval⟩ := runU_run U view A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set s := (view p).1
  set ms := (view p).2
  rw [hlogE]
  rw [hevalE, heval] at hwin
  set lg := tableQueryLog (runU U view A post) T
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
  have hk : ¬ FreshBad (kcBadU U C R) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK U.K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadU U C R) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcU U C R T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := rf_beforeU hl
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ U.K.rootsK ms → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBadK U.K view A) T ∅ Lk hr (.inl w) hwk
      (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    simp only [Lk, lg, hL]
    exact subset_before_append _ _ hwA' q hq
  -- So the candidates read off the adversary's queries are those read off the run's.
  have hstab : ∀ {N : Type} (Cn : ListCommit N) (r : Bytes32), r ∈ U.K.rootsK ms →
      Cn.cands LA.toFinset (viewT T) r = Cn.cands L.toFinset (viewT T) r := by
    intro N Cn r hr'
    refine (Cn.stable LA.toFinset L.toFinset (viewT T) r (fun w hw => ?_) (fun w hw hwr => ?_)
      (fun y hy w hw h => ?_)).symm
    · rw [hLA]
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hw))
    · exact List.mem_toFinset.mpr (hroot w (List.mem_toFinset.mp hw) (hwr ▸ hr'))
    · have hyA := List.mem_toFinset.mp hy
      have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
      have hb := hord w (List.mem_toFinset.mp hw) y hyL (U.refers_rf _ _ h)
      rw [hLA, before_append_of_mem LA rest hyA] at hb
      exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  have hms : ms.take U.K.rounds.length = ms := List.take_of_length_le (le_of_eq hfit.length_eq)
  rw [candLists_stable C 0 ms fun m hm r hr k => hstab (C k) r (by
    simp only [ChainSpec.rootsK, hms]
    exact List.mem_filterMap.mpr ⟨m, hm, hr⟩)] at hcs
  refine hl (trace_coreU U C R L (viewT T) s ms cs hfit (fun y hy => ?_) hcs hlw)
  simp only [L, Lk, lg, hL, List.filterMap_append]
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [filterMap_getLeft?_map_inl]
  exact hy

/-! ## Each fresh query is bad with small probability -/

variable [Fintype F] [DecidableEq F]

/-- **Each fresh query of both oracles is bad for the view with probability at most
`(|H| + nRf (|H| + 1)) / 2^256 + tagBound + maxErrK`.** -/
theorem prob_kcBadU (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[kcBadU U C R
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      (((cacheDom c).card + U.nRf * ((cacheDom c).card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        U.tagBound + maxErrK U.K C R := by
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
    have hev : ∀ g, kcBadU U C R ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) (.inl x)
        (extendTable S (completeTable c g)) ↔
        listBadU U C R (histOf (viewC S c)) x (tableOf (viewC S c) (viewG S g)) := by
      intro g
      show listBadU U C R _ x _ ↔ _
      rw [← histOf_viewC]
      exact listBadU_congr U C R (fun y hy => viewT_extendTable c g (hH hy))
        (viewT_extendTable c g hx) (fun v => viewT_extendTable c g (hS₁ v))
    refine (prEvent_mono _ _ (fun g => listBadU U C R (histOf (viewC S c)) x
      (tableOf (viewC S c) (viewG S g))) fun g h => (hev g).mp h).trans ?_
    rw [prEvent_view S (fun h => listBadU U C R (histOf (viewC S c)) x (tableOf (viewC S c) h))]
    refine (prob_listBadU U C R hS₁ (viewC S c) ⟨x, hx⟩ hc₁).trans ?_
    have hcard : (histOf (viewC S c)).card ≤ (cacheDom c).card := by
      rw [histOf_viewC]
      refine (Finset.card_le_card_of_injOn
        (t := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))) Sum.inl (fun y hy => ?_)
        Sum.inl_injective.injOn).trans (Finset.card_map (Function.Embedding.subtype (· ∈ S))).le
      exact mem_viewH.mp hy
    have hle : (histOf (viewC S c)).card + U.nRf * ((histOf (viewC S c)).card + 1) ≤
        (cacheDom c).card + U.nRf * ((cacheDom c).card + 1) := by
      have := Nat.mul_le_mul_left U.nRf (Nat.add_le_add_right hcard 1)
      omega
    exact add_le_add (add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hle) _) le_rfl) le_rfl

/-- **Each fresh query is bad with probability at most
`(|H| + nRf (|H| + 1) + k) / 2^256 + tagBound + maxErrK`.** -/
theorem prob_advBadU (A : OracleComp KeccakCalls Pf) (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[advBadU U C R view A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      (((cacheDom c).card + U.nRf * ((cacheDom c).card + 1) + U.K.rounds.length : ℕ) : ℝ≥0∞) /
        2 ^ 256 + U.tagBound + maxErrK U.K C R := by
  refine (prEvent_or_le _ _ _).trans ((add_le_add (prob_kcBadU U C R S hS₀ c t ht)
    (prob_rootBadK U.K view A S c t ht)).trans (le_of_eq ?_))
  rw [Nat.cast_add (R := ℝ≥0∞) ((cacheDom c).card + U.nRf * ((cacheDom c).card + 1))
    U.K.rounds.length, ENNReal.add_div]
  ring

end Exp

/-! ## A broken run has a doomed opening or wins the list game -/

section Imp

variable {F St M Pf β : Type} [SampleableType F]
variable (K : ChainSpec F St) (C : ℕ → ListCommit M) (R : Piop K M)
  (view : Pf → St × List (RMsg F)) (Op : OpeningsK Pf F β M)

/-- **A broken run has a doomed opening, or wins the list game** (`breaksK_imp`), the protocol's
last state needed only of candidates `none` at the rounds without a root. -/
theorem breaksU_imp
    (hfit : ∀ π ch b, Op.check π ch b → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch b (cs : List (Option M)), Op.check π ch b →
      cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → Op.good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (K.spec i).root = false → cs[i] = none) → Op.goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (z : OutK Pf F β) (h : BreaksK K C R view Op z) :
    (∃ i < K.rounds.length, (K.spec i).root ∧ DoomK C view Op i z) ∨ DoomSK Op z ∨
      ListWinsK K C R view z := by
  obtain ⟨⟨hchk, hacc, haccS⟩, hext⟩ := h
  by_contra hno
  simp only [not_or, not_exists, not_and] at hno
  obtain ⟨hD, hS, hL⟩ := hno
  have hgS : Op.goodS z.1.1 z.1.2.1 := by
    by_contra hc
    exact hS ⟨haccS, hc⟩
  have hf := hfit _ _ _ hchk
  have hlen := hf.length_eq
  set H := histOfTr z.2
  set T := tableOfTr z.2
  set ms := (view z.1.1).2
  -- A candidate satisfying each root's opening's claims, `none` at the other rounds.
  have hex : ∀ i (hi : i < (candLists C H T 0 ms).length),
      ∃ c ∈ (candLists C H T 0 ms)[i], ((K.spec i).root → Op.good i z.1.1 z.1.2.1 c) ∧
        ((K.spec i).root = false → c = none) := by
    intro i hi
    rw [getElem_candLists, Nat.zero_add]
    have hik : i < K.rounds.length := by rw [length_candLists, hlen] at hi; exact hi
    by_cases hr : (K.spec i).root
    · have hg : ∃ c ∈ optC (C i) H T (ms.getD i (none, [])), Op.good i z.1.1 z.1.2.1 c := by
        by_contra hc
        push Not at hc
        exact hD i hik hr ⟨hacc i hik hr, fun c hc' => hc c hc'⟩
      obtain ⟨c, hc, hgc⟩ := hg
      exact ⟨c, hc, fun _ => hgc, fun h => absurd h (by simp [hr])⟩
    · have hfi := fitsAll_getD hf i hik
      have hnone : (ms.getD i (none, [])).1 = none := by
        rw [ChainSpec.spec] at hr
        obtain ⟨hfi1, -⟩ := hfi
        cases h1 : (ms.getD i (none, [])).1 with
        | none => rfl
        | some _ =>
          rw [h1] at hfi1
          exact absurd hfi1.symm (by simpa using hr)
      refine ⟨none, ?_, fun h' => absurd h' hr, fun _ => rfl⟩
      unfold optC
      rw [hnone]
      simp
  obtain ⟨cs, hcs, hcsP⟩ := exists_forall₂_of_forall _ _ hex
  have hcl : cs.length = K.rounds.length := by
    rw [hcs.length_eq, length_candLists, hlen]
  obtain ⟨p, m, c, hpe, hpost⟩ := hlink z.1.1 z.1.2.1 z.1.2.2 cs hchk hcl
    (fun i h hr => (hcsP i h).1 hr) (fun i h hr => (hcsP i h).2 hr) hgS
  exact hL ⟨hf, cs, hcs, lostWon_of_extract R C H T _ cs ms _ p m c hcs
    (fun c₀ hc₀ => hext c₀ hc₀) hpe hpost⟩

end Imp

/-! ## The experiment with each opening's stage logged -/

section Stages

variable {F St M Pf : Type} [SampleableType F]
variable (U : ChainSpecU F St) (C : ℕ → ListCommit M) (R : Piop U.K M)
  (view : Pf → St × List (RMsg F))

/-- The adversary, its queries logged, then the chain. -/
def preU (A : OracleComp KeccakCalls Pf) : OracleComp KeccakCalls (PreK Pf F) :=
  loggedKC A >>= fun pt => U.chain hash256 (view pt.1).1 (view pt.1).2 >>= fun ch =>
    pure (pt.1, ch, pt.2)

/-- **The experiment, every opening's stage logged.** -/
def expWU (ops : List (WhirOp Pf F M)) (A : OracleComp KeccakCalls Pf) :
    OracleComp KeccakCalls (PreK Pf F × Stg) :=
  stagesK view ops 0 ((fun x => (x, stg₀)) <$> preU U view A)

/-- **The logged experiment, its stage logs dropped, is `expU` with the openings.** -/
theorem map_expWU (ops : List (WhirOp Pf F M)) (A : OracleComp KeccakCalls Pf) :
    (fun z => projS z.1 (verdOf z.2)) <$> expWU U view ops A =
      verdFn <$> expU U view A (opsRun view ops) := by
  rw [expWU, map_stagesK view ops 0 _ projS, bind_map_left]
  simp only [verdOf_stg₀, writeV_zero, preU, expU, verU, bind_assoc, pure_bind, map_bind,
    map_pure]
  refine bind_congr fun pt => bind_congr fun ch => ?_
  rw [map_eq_bind_pure_comp]
  rfl

theorem isTotalQueryBound_preU (A : OracleComp KeccakCalls Pf) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) : IsTotalQueryBound (preU U view A) (QA + U.K.nQ) := by
  have h := isTotalQueryBound_bind
    (ob := fun pt : Pf × Transcript => U.chain hash256 (view pt.1).1 (view pt.1).2 >>= fun ch =>
      (pure (pt.1, ch, pt.2) : OracleComp KeccakCalls (PreK Pf F)))
    (isTotalQueryBound_loggedKC_run A QA [] hA) fun pt =>
      isTotalQueryBound_bind
        (ob := fun ch => (pure (pt.1, ch, pt.2) : OracleComp KeccakCalls (PreK Pf F))) (n₂ := 0)
        (isTotalQueryBound_chainU U (view pt.1).1 (view pt.1).2) fun _ => trivial
  rwa [Nat.add_zero] at h

theorem isTotalQueryBound_expWU (ops : List (WhirOp Pf F M)) (A : OracleComp KeccakCalls Pf)
    (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    IsTotalQueryBound (expWU U view ops A) (QA + U.K.nQ + (ops.map fun o => o.S.QO).sum) :=
  isTotalQueryBound_stagesK view ops 0 _ _
    ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_preU U view A QA hA))

theorem preU_run (A : OracleComp KeccakCalls Pf) (T : KTable) :
    tableQueryLog (preU U view A) T = tableQueryLog A T ++
        tableQueryLog (U.chain hash256 (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1
          (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).2) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (preU U view A) =
        (evalWithAnswerFn (QueryImpl.ofFn T) A,
          evalWithAnswerFn (QueryImpl.ofFn T) (U.chain hash256
            (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1
            (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).2),
          (tableQueryLog A T).filterMap inlEntry) := by
  obtain ⟨hl, he⟩ := run_logged A T
  have hl' : tableQueryLog (loggedKC A) T = tableQueryLog A T := hl
  have he' : evalWithAnswerFn (QueryImpl.ofFn T) (loggedKC A) =
      (evalWithAnswerFn (QueryImpl.ofFn T) A, (tableQueryLog A T).filterMap inlEntry) := he
  constructor
  · simp only [preU, tableQueryLog_bind, hl', he', tableQueryLog_pure, List.append_nil]
  · simp only [preU, evalWithAnswerFn_bind, he', evalWithAnswerFn_pure]

/-! ## The trace -/

variable [Fintype F] [DecidableEq F]

open Classical in
/-- **The trace of the logged experiment**: on every table of both oracles, a run that breaks
knowledge soundness while no opening is doomed at its end asks a bad fresh query. -/
theorem trace_whirU {σ : Type} (ops : List (WhirOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (hok : ∀ o ∈ ops, WhirOp.OK tc good setup fix o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll U.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = U.K.rounds.length →
      (∀ i (h : i < cs.length), (U.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (U.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (T : KTable)
    (hev : BreaksOK U.K (fun i => (tc i).commit) R view check
        (fun v => ∀ k < ops.length, v k = true)
        (projS (evalWithAnswerFn (QueryImpl.ofFn T) (expWU U view ops (withSetupG setup fix A₀))).1
          (verdOf (evalWithAnswerFn (QueryImpl.ofFn T)
            (expWU U view ops (withSetupG setup fix A₀))).2)) ∧
      ¬ DoomAt view ops 0 (evalWithAnswerFn (QueryImpl.ofFn T)
        (expWU U view ops (withSetupG setup fix A₀)))) :
    FreshBad (advBadU U (fun i => (tc i).commit) R view (withSetupG setup fix A₀)) T ∅
      ((tableQueryLog (expWU U view ops (withSetupG setup fix A₀)) T).map Sigma.fst) := by
  -- The run's parts, against the table.
  obtain ⟨hsl, hse⟩ := withSetupG_run setup fix A₀ T
  obtain ⟨hpl, hpe⟩ := preU_run U view (withSetupG setup fix A₀) T
  have hproj0 := congrArg (evalWithAnswerFn (QueryImpl.ofFn T))
    (map_expWU U view ops (withSetupG setup fix A₀))
  have hlog0 := congrArg (fun oa => tableQueryLog oa T)
    (map_expWU U view ops (withSetupG setup fix A₀))
  simp only [evalWithAnswerFn_map] at hproj0
  simp only [tableQueryLog_map] at hlog0
  have hzl0 := stagesK_log view T ops 0
    ((fun x => (x, stg₀)) <$> preU U view (withSetupG setup fix A₀))
  have hz10 := stagesK_fst view T ops 0
    ((fun x => (x, stg₀)) <$> preU U view (withSetupG setup fix A₀))
  have hzat0 := stagesK_at view T ops 0
    ((fun x => (x, stg₀)) <$> preU U view (withSetupG setup fix A₀))
  have hX₀l0 := tableQueryLog_map T (fun x => (x, stg₀)) (preU U view (withSetupG setup fix A₀))
  simp only [evalWithAnswerFn_map, hpe, Nat.zero_add] at hzl0 hz10 hzat0
  rw [hpl] at hX₀l0
  rw [hX₀l0] at hzl0 hzat0
  set A := withSetupG setup fix A₀ with hAdef
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set z := evalWithAnswerFn (QueryImpl.ofFn T) (expWU U view ops A) with hz
  set zK := evalWithAnswerFn (QueryImpl.ofFn T) (expU U view A (opsRun view ops)) with hzK
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A with hp
  set ch := evalWithAnswerFn (QueryImpl.ofFn T) (U.chain hash256 (view p).1 (view p).2) with hch
  set lA := tableQueryLog A T with hlA
  set lC := tableQueryLog (U.chain hash256 (view p).1 (view p).2) T with hlC
  set tA : Transcript := lA.filterMap inlEntry with htA
  have hproj : projS z.1 (verdOf z.2) = verdFn zK := hproj0
  have hlogW : tableQueryLog (expWU U view ops A) T =
      tableQueryLog (expU U view A (opsRun view ops)) T := hlog0
  have hz1 : z.1 = (p, ch, tA) := hz10
  have hzl : tableQueryLog (expWU U view ops A) T =
      (lA ++ lC) ++ tableQueryLog (opsRun view ops p ch) T := hzl0
  have hzat : ∀ m (hm : m < ops.length) (o : WhirOp Pf F M), ops[m] = o →
      z.2 m = (evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier o.S.L o.S.R
          (WhirOp.input view o p ch)),
        ((lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).filterMap
          inlEntry) := hzat0
  -- `expU`'s outcome.
  have hK11 : zK.1.1 = p := by
    have := congrArg (fun w : OutK Pf F (ℕ → Bool) => w.1.1) hproj
    simp only [projS, verdFn, hz1] at this
    exact this.symm
  have hK121 : zK.1.2.1 = ch := by
    have := congrArg (fun w : OutK Pf F (ℕ → Bool) => w.1.2.1) hproj
    simp only [projS, verdFn, hz1] at this
    exact this.symm
  have hK2 : zK.2 = tA := by
    have := congrArg (fun w : OutK Pf F (ℕ → Bool) => w.2) hproj
    simp only [projS, verdFn, hz1] at this
    exact this.symm
  -- The event.
  obtain ⟨hB, hnd⟩ := hev
  have hverd : ∀ m < ops.length, (z.2 m).1 = true := fun m hm => hB.2.1 m hm
  have hBK : BreaksOK U.K CC R view check (fun bs => ∀ k < ops.length, bs.getD k false = true)
      zK := by
    have h := hB
    rw [hproj] at h
    exact h
  have hcheck : check p ch := by
    have := hBK.1
    rwa [hK11, hK121] at this
  have hnotdoom : ∀ m (hm : m < ops.length), ¬ EOp view ops[m] z.1 (z.2 m) := by
    intro m hm
    have := not_doomAt view ops 0 z hnd m hm
    rwa [Nat.zero_add] at this
  -- No bad fresh query, from here on.
  by_contra hnb
  set Lk := (tableQueryLog (expWU U view ops A) T).map Sigma.fst with hLkdef
  set L := Lk.filterMap Sum.getLeft? with hLdef
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft? with hLAdef
  have hk : ¬ FreshBad (kcBadU U CC R) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK U.K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadU U CC R) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcU U CC R T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := rf_beforeU hl
  have hinj : Set.InjOn (viewT T) ↑L.toFinset := injOn_of_not_freshBadU hl
  have hLk : Lk = lA.map Sigma.fst ++
      ((lC ++ tableQueryLog (opsRun view ops p ch) T).map Sigma.fst) := by
    rw [hLkdef, hzl]
    simp only [List.map_append, List.append_assoc]
  obtain ⟨rest, hLA⟩ : ∃ rest, L = LA ++ rest :=
    ⟨_, by rw [hLdef, hLk, List.filterMap_append]⟩
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ U.K.rootsK (view p).2 → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBadK U.K view A) T ∅ Lk hr (.inl w) hwk
      (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    rw [hLk]
    exact subset_before_append _ _ hwA' q hq
  -- A history between the adversary's and the run's reads the adversary's word.
  have hstab : ∀ (H : List (List UInt8)), (∀ y ∈ LA, y ∈ H) → (∀ y ∈ H, y ∈ L) →
      ∀ r ∈ U.K.rootsK (view p).2, ∀ ht ℓ,
        merkleWord H.toFinset (viewT T) ht ℓ r = merkleWord LA.toFinset (viewT T) ht ℓ r := by
    intro H hAH hHL r hr' ht ℓ
    refine merkleWord_stable (H := LA.toFinset) (H' := H.toFinset) (T := viewT T) (r := r)
      (fun y hy => List.mem_toFinset.mpr (hAH y (List.mem_toFinset.mp hy)))
      (fun w hw hwr => List.mem_toFinset.mpr
        (hroot w (hHL w (List.mem_toFinset.mp hw)) (hwr ▸ hr')))
      (fun y hy w hw h => ?_) ht ℓ
    have hyA := List.mem_toFinset.mp hy
    have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
    have hb := hord w (hHL w (List.mem_toFinset.mp hw)) y hyL (U.refers_rf _ _ h)
    rw [hLA, before_append_of_mem LA rest hyA] at hb
    exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  -- The stages' histories.
  set Hm : ℕ → List (List UInt8) := fun m =>
    (((lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).map
      Sigma.fst).filterMap Sum.getLeft? with hHm
  have hHmL : ∀ m, ∀ y ∈ Hm m, y ∈ L := by
    intro m y hy
    obtain ⟨rest', hrest'⟩ := opsRun_log_take view T p ch ops (m + 1)
    have hL' : L = (((lA ++ lC) ++ (tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T ++
        rest')).map Sigma.fst).filterMap Sum.getLeft? := by
      rw [hLdef, hLkdef, hzl, hrest']
    rw [hL']
    have hy' : y ∈ (((lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).map
        Sigma.fst).filterMap Sum.getLeft? := hy
    simp only [List.map_append, List.filterMap_append, List.mem_append] at hy' ⊢
    tauto
  have hLAHm : ∀ m, ∀ y ∈ LA, y ∈ Hm m := by
    intro m y hy
    show y ∈ (((lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).map
      Sigma.fst).filterMap Sum.getLeft?
    rw [List.map_append, List.map_append, List.filterMap_append, List.filterMap_append]
    exact List.mem_append_left _ (List.mem_append_left _ hy)
  have hinjm : ∀ m, Set.InjOn (viewT T) ↑(Hm m).toFinset := fun m =>
    hinj.mono fun y hy => List.mem_toFinset.mpr (hHmL m y (List.mem_toFinset.mp hy))
  -- An undoomed opening has a candidate of its stage's word satisfying its claims.
  have hcand : ∀ m (hm : m < ops.length) (o : WhirOp Pf F M), ops[m] = o →
      ∃ q ∈ Candidates o.S.L.logN o.S.R (code₀ o.S.L.logN o.S.R).thr
          (Rom.extract (ansOf (Hm m).toFinset (viewT T)) (ofB (WhirOp.root view o p))
            (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold)),
        ∀ cl ∈ (o.cl p ch).claims, o.S.L.tableEval q cl.point = cl.value := by
    intro m hm o ho
    have hv := hverd m hm
    have hd := hnotdoom m hm
    rw [ho] at hd
    rw [hzat m hm o ho] at hv hd
    rw [hz1] at hd
    have hOD : ¬ OpeningDoomed o.S.L o.S.R (WhirOp.input view o p ch)
        (cacheOfTr (((lA ++ lC) ++
          tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).filterMap inlEntry)) :=
      fun h => hd ⟨hv, h⟩
    unfold OpeningDoomed at hOD
    push Not at hOD
    obtain ⟨q, hq, hqc⟩ := hOD
    have hsnd : ∀ e ∈ (lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T,
        e.2 = T e.1 := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · exact tableQueryLog_snd_dep T _ e he
        · exact tableQueryLog_snd_dep T _ e he
      · exact tableQueryLog_snd_dep T _ e he
    rw [cacheOfTr_eq_ansOf T _ hsnd] at hq
    exact ⟨q, hq, hqc⟩
  -- Every round with a root has a candidate, read off the adversary's queries, that is good.
  have htrH : histOfTr tA = LA.toFinset := by
    simp only [histOfTr, htA, hLAdef, map_fst_filterMap_inlEntry]
  have htrT : ∀ d ∈ histOfTr tA, tableOfTr tA d = viewT T d := by
    intro d hd
    refine tableOfTr_eq (viewT T) tA (fun e he => ?_) d (by simpa [histOfTr] using hd)
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
  have hfit' := hfit p ch hcheck
  have hD : ∀ i < U.K.rounds.length, (U.K.spec i).root →
      ¬ DoomK CC view (opW ops check good goodS) i zK := by
    intro i hi hri hDK
    obtain ⟨o, hoops, rd, htgt⟩ := hcov i hi hri
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : WhirOp.OK tc good setup fix o := hok o hoops
    obtain ⟨r, hmr, hrr⟩ := exists_root_of_fits U.K hfit' i hi hri
    unfold WhirOp.OK at hokO
    rw [htgt] at hokO
    obtain ⟨hht, hlf, hcomp, hgood⟩ := hokO
    have hroot_o : WhirOp.root view o p = r := by
      unfold WhirOp.root
      rw [htgt]
      show ((msgK view p i).1).getD (Vector.replicate 32 0) = r
      simp only [msgK]
      rw [hmr]
      rfl
    rw [hroot_o] at hq
    have hword := candidates_congr (μ := o.S.L.logN) (R := o.S.R)
      (A := (code₀ o.S.L.logN o.S.R).thr)
      (W := Rom.extract (ansOf (Hm m).toFinset (viewT T)) (ofB r) (rootHeight o.S.L.logN o.S.R)
        (2 ^ laneFold))
      (W' := wordOfMerkle (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold)
        (merkleWord (Hm m).toFinset (viewT T) (rootHeight o.S.L.logN o.S.R) (8 * 2 ^ laneFold)
          (toB (ofB r))))
      fun v hv => (wordOfMerkle_eq_extract (hinjm m) _ _ _ hv).symm
    have htoB : toB (ofB r) = r := LeanVM.Rpm.digestToRpm_ofRpm _
    rw [hword, htoB, hstab (Hm m) (hLAHm m) (hHmL m) r hrr] at hq
    have hmem : rd q ∈ (tc i).dec
        (merkleWord LA.toFinset (viewT T) (tc i).height (tc i).leafLen r) :=
      hcomp _ q (by rw [hht, hlf]; exact hq)
    have hgq : good i p ch (some (rd q)) := hgood p ch q hqc
    obtain ⟨-, hdoom⟩ := hDK
    refine hdoom (some (rd q)) ?_ ?_
    · rw [hK2, hK11, optC_congr (CC i) htrT, htrH]
      unfold optC
      simp only [msgK] at hmr ⊢
      rw [hmr]
      exact List.mem_map.mpr ⟨rd q, hmem, rfl⟩
    · rw [hK11, hK121]
      exact hgq
  -- Every setup opening's stack satisfies its claims.
  have hSH : ∀ o ∈ ops, WhirOp.SetupHolds o p ch := by
    intro o hoops
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : WhirOp.OK tc good setup fix o := hok o hoops
    unfold WhirOp.SetupHolds
    unfold WhirOp.OK at hokO
    rcases htg : o.tgt with ⟨i, rd⟩ | ⟨root, q₀⟩
    · trivial
    · rw [htg] at hokO
      obtain ⟨word, hhon, hsw⟩ := hokO
      have hsub : ∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst →
          x ∈ (Hm m).toFinset := by
        intro x hx
        refine List.mem_toFinset.mpr (hLAHm m x (mem_filterMap_getLeft?.mpr ?_))
        rw [hsl, List.map_append]
        exact List.mem_append_left _ hx
      have hroot_o : WhirOp.root view o p = root p := by
        unfold WhirOp.root
        rw [htg]
      rw [hroot_o, hse] at hq
      have hword := candidates_congr (μ := o.S.L.logN) (R := o.S.R)
        (A := (code₀ o.S.L.logN o.S.R).thr)
        (W := Rom.extract (ansOf (Hm m).toFinset (viewT T))
          (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup)
            (evalWithAnswerFn (QueryImpl.ofFn T)
              (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup))))))
          (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold))
        (W' := word) fun v hv => hsw T (Hm m).toFinset
          (evalWithAnswerFn (QueryImpl.ofFn T) (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)))
          hsub (hinjm m) v hv
      rw [hword] at hq
      have hq₀ := candidates_honest o.S.adm hhon hq
      subst hq₀
      exact hqc
  have hgS : goodS p ch := hS p ch hSH
  -- The list game, then a bad fresh query.
  have hBK' := breaksK_of_breaksOK U.K CC R view ops check good goodS zK hBK
  rcases breaksU_imp U.K CC R view (opW ops check good goodS) (fun π ch' _ h => hfit π ch' h)
      (fun π ch' _ cs h hl' hg hn hs => hlink π ch' cs h hl' hg hn hs) zK hBK' with
    ⟨i, hi, hri, hDK⟩ | hDS | hwin
  · exact hD i hi hri hDK
  · obtain ⟨-, hng⟩ := hDS
    refine hng ?_
    show goodS zK.1.1 zK.1.2.1
    rw [hK11, hK121]
    exact hgS
  · have := trace_advU U CC R view A (opsRun view ops) T hwin
    rw [← hlogW] at this
    exact hnb this

/-! ## Knowledge soundness with the openings' terms discharged -/

/-- **Knowledge soundness of the chain over any encoding with WHIR openings, every opening's doom
discharged by F2**, in mumbai's two-oracle model (`knowledgeSoundness_listChainK_closed` for
`ChainSpecU`): the verifier accepts while no candidate of round `0`'s root read off the
adversary's (and the setup's) queries satisfies the first round's state with probability at most

`doomSum ops (QS + Q + nQ) + N (maxErrK + tagBound + (nRf + 2) N / 2^256)`,
`N = QS + Q + nQ + Σ_k QO_k`. -/
theorem knowledgeSoundness_listChainU_closed {σ : Type} (ops : List (WhirOp Pf F M))
    (tc : ℕ → TableCode M) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) (A₀ : σ → OracleComp KeccakCalls Pf)
    (QS Q : ℕ) (hSq : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hok : ∀ o ∈ ops, WhirOp.OK tc good setup fix o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll U.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = U.K.rounds.length →
      (∀ i (h : i < cs.length), (U.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (U.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c) :
    Pr{let z ← (simulateQ randomOracle
        (expU U view (withSetupG setup fix A₀) (opsRun view ops))).run' ∅}[
        BreaksOK U.K (fun i => (tc i).commit) R view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true) z] ≤
      doomSum ops (QS + Q + U.K.nQ) +
        ((QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) *
          (maxErrK U.K (fun i => (tc i).commit) R + U.tagBound +
            (((U.nRf + 2) * (QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum) : ℕ) : ℝ≥0∞) /
              2 ^ 256) := by
  set A := withSetupG setup fix A₀ with hAdef
  have hA : IsTotalQueryBound A (QS + Q) :=
    isTotalQueryBound_withSetupG setup fix A₀ QS Q hSq hQ
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set accF : (ℕ → Bool) → Prop := fun v => ∀ k < ops.length, v k = true with haccF
  set N := QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum with hN
  -- The event on the logged experiment.
  have h1 : Pr{let z ← (simulateQ randomOracle (expU U view A (opsRun view ops))).run' ∅}[
        BreaksOK U.K CC R view check (fun bs => ∀ k < ops.length, bs.getD k false = true) z] =
      Pr{let z ← (simulateQ randomOracle (expWU U view ops A)).run' ∅}[
        BreaksOK U.K CC R view check accF (projS z.1 (verdOf z.2))] := by
    calc _ = Pr{let z ← (simulateQ randomOracle (expU U view A (opsRun view ops))).run' ∅}[
          BreaksOK U.K CC R view check accF (verdFn z)] := rfl
      _ = Pr{let w ← verdFn <$> (simulateQ randomOracle (expU U view A (opsRun view ops))).run' ∅}[
          BreaksOK U.K CC R view check accF w] := (prEvent_map _ _ _).symm
      _ = Pr{let w ← (simulateQ randomOracle (verdFn <$> expU U view A (opsRun view ops))).run' ∅}[
          BreaksOK U.K CC R view check accF w] := by rw [run'_simulateQ_map]
      _ = Pr{let w ← (simulateQ randomOracle ((fun z => projS z.1 (verdOf z.2)) <$>
            expWU U view ops A)).run' ∅}[BreaksOK U.K CC R view check accF w] := by
          rw [map_expWU]
      _ = _ := by rw [run'_simulateQ_map, prEvent_map]
  rw [h1]
  set mx := (simulateQ randomOracle (expWU U view ops A)).run' ∅
  refine (prEvent_mono mx _ (fun z => DoomAt view ops 0 z ∨
    (BreaksOK U.K CC R view check accF (projS z.1 (verdOf z.2)) ∧ ¬ DoomAt view ops 0 z))
    fun z h => ?_).trans ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_))
  · by_cases hd : DoomAt view ops 0 z
    · exact Or.inl hd
    · exact Or.inr ⟨h, hd⟩
  · exact prEvent_doomAt_le view ops 0 _ (QS + Q + U.K.nQ)
      ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_preU U view A (QS + Q) hA))
  · refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (expWU U view ops A)
      N (isTotalQueryBound_expWU U view ops A _ hA)
      (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
      (Set.finite_range _) _ (advBadU U CC R view A) _ (fun S hS' c t ht hcard => ?_)
      (fun T h => trace_whirU U R view ops tc check good goodS setup fix A₀ hok hcov hS hfit
        hlink T h)
    have hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS' _ ⟨v, rfl⟩
    refine (prob_advBadU U CC R view A S hS₀ c t ht).trans ?_
    have hk : U.K.rounds.length < U.K.nQ := by
      have := nSteps_ge_length U.K.rounds
      simp only [ChainSpec.nQ]
      omega
    have hNle : (cacheDom c).card + U.nRf * ((cacheDom c).card + 1) + U.K.rounds.length ≤
        (U.nRf + 2) * N := by
      have hc1 : (cacheDom c).card + 1 ≤ N := hcard
      have h2 : U.nRf * ((cacheDom c).card + 1) ≤ U.nRf * N := Nat.mul_le_mul_left _ hc1
      have h3 : U.K.rounds.length ≤ N := by omega
      nlinarith
    calc (((cacheDom c).card + U.nRf * ((cacheDom c).card + 1) + U.K.rounds.length : ℕ) :
          ℝ≥0∞) / 2 ^ 256 + U.tagBound + maxErrK U.K CC R
        ≤ (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 + U.tagBound + maxErrK U.K CC R :=
          add_le_add (add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hNle) _) le_rfl) le_rfl
      _ = maxErrK U.K CC R + U.tagBound + (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 := by ring

end Stages

end Compose
