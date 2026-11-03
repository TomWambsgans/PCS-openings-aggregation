-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/Compose/Compose/ListChainUDoom.lean` of this repository step by step (its bad
-- events, trace and end theorem) over `ListChainU128.lean`'s `listBadU'`, on the run with its whole
-- Keccak-256 transcript (`Final128Defs.lean`'s `expL`); what does not read the tag or the stages
-- (`verU`, `expU`, `runU`, `expU_run`, `runU_run`, `breaksU_imp`, `preU`, `preU_run`) is reused.
import Compose.ListChainU128
import Compose.Final128Defs

/-!
# The chain over any encoding with WHIR openings, the seed separated by a pair of answers

`ListChainUDoom.lean`'s `knowledgeSoundness_listChainU_closed` pays `N · tagBound = N · 2^-128`
for the tag separating the seed from a step's input, and reads each opening's doom at the end of
its own stage. Here:

* **the bad events** are `listBadU'`'s (`kcBadU'`, `advBadU'`): a collision, a bad round, a fresh
  answer after the adversary's last query that is one of its roots; no tag
  (`prob_advBadU'`: `(|H| + nRf (|H| + 1) + k) / 2^256 + maxErrK`);
* **the seed** (`hlab`): the label's first 32 bytes are `tag ‖` the first `32 − |tag|` bytes of an
  answer `w` the adversary asked (the univariate `name ‖ iv[0:16]`, `iv` the contract IV, a
  Keccak-256 answer). An answer of the run equal to them makes, with `w`'s, a pair of the whole
  run's transcript (`PairTr`); without one, `trace_coreU'`'s `hseed` holds;
* **the doom** is read at the end of the run (`DoomF`, `expL`): an undoomed opening has a candidate
  of the word under its root read off the whole history, which is the adversary's word
  (`trace_whirU'`). The stages are not needed.

**`knowledgeSoundness_listChainU_closed128`**: the verifier accepts while no candidate of round
`0`'s root, read off the setup's and the adversary's queries, satisfies the first round's state with
probability at most

  `Pr[DoomF] + Pr[PairTr tag] + N (maxErrK + (nRf + 2) N / 2^256)`,
  `N = QS + Q + nQ + Σ_k QO_k`,

both events of `expL view (preU …) ops` (bounded once for all openings in `FirstDoom.lean`, and by
`2 N² / 2^256` in `SeedPair.lean`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The bad events -/

section Exp

variable {F St M Pf β : Type} [SampleableType F]
variable (U : ChainSpecU F St) (C : ℕ → ListCommit M) (R : Piop U.K M)
  (view : Pf → St × List (RMsg F))

/-- **A bad query of both oracles**: a Keccak-256 query bad for `listBadU'` on the view; never a
Keccak-f query. -/
def kcBadU' (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) :
    Prop :=
  match d with
  | .inl x => listBadU' U C R (viewH H) x (viewT T)
  | .inr _ => False

/-- A bad query: `kcBadU'`, or a fresh answer that is an announced root. -/
def advBadU' (A : OracleComp KeccakCalls Pf) (H : Finset (List UInt8 ⊕ KeccakState))
    (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  kcBadU' U C R H d T ∨ rootBadK U.K view A H d T

theorem freshBad_kcU' (T : KTable) : ∀ (H : Finset (List UInt8 ⊕ KeccakState))
    (L : List (List UInt8 ⊕ KeccakState)),
    FreshBad (listBadU' U C R) (viewT T) (viewH H) (L.filterMap Sum.getLeft?) →
      FreshBad (kcBadU' U C R) T H L
  | _, [], h => by simp [FreshBad] at h
  | H, .inl x :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, FreshBad] at h ⊢
    rcases h with ⟨hx, hb⟩ | h
    · exact Or.inl ⟨fun hm => hx (mem_viewH.mpr hm), hb⟩
    · refine Or.inr (freshBad_kcU' T _ L ?_)
      rwa [viewH_insert_inl]
  | H, .inr s :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, FreshBad] at h ⊢
    refine Or.inr (freshBad_kcU' T _ L ?_)
    rwa [viewH_insert_inr]

/-! ## The trace -/

open Classical in
/-- **The trace, with the adversary's transcript** (`trace_advU` for `listBadU'`): on every table
of both oracles, a run whose log holds no answer equal to the label's first 32 bytes (`hseed`) and
whose candidates, read off the adversary's queries, make the transcript lost at the start and won
at the end asks a bad fresh query. -/
theorem trace_advU' (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable)
    (hseed : ∀ z ∈ ((tableQueryLog (expU U view A post) T).map Sigma.fst).filterMap Sum.getLeft?,
      (viewT T z).toList ≠ (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1).take 32)
    (hwin : ListWinsK U.K C R view (evalWithAnswerFn (QueryImpl.ofFn T) (expU U view A post))) :
    FreshBad (advBadU' U C R view A) T ∅
      ((tableQueryLog (expU U view A post) T).map Sigma.fst) := by
  obtain ⟨hlogE, hevalE⟩ := expU_run U view A post T
  obtain ⟨hL, heval⟩ := runU_run U view A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set s := (view p).1
  set ms := (view p).2
  rw [hlogE] at hseed ⊢
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
  have hk : ¬ FreshBad (kcBadU' U C R) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK U.K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadU' U C R) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcU' U C R T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := rf_beforeU' hl
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
  refine hl (trace_coreU' U C R L (viewT T) s ms cs hfit (fun y hy => ?_) hcs hlw hseed)
  simp only [L, Lk, lg, hL, List.filterMap_append]
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [filterMap_getLeft?_map_inl]
  exact hy

/-! ## Each fresh query is bad with small probability -/

variable [Fintype F] [DecidableEq F]

/-- **Each fresh query of both oracles is bad for the view with probability at most
`(|H| + nRf (|H| + 1)) / 2^256 + maxErrK`.** -/
theorem prob_kcBadU' (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[kcBadU' U C R
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      (((cacheDom c).card + U.nRf * ((cacheDom c).card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        maxErrK U.K C R := by
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
    have hev : ∀ g, kcBadU' U C R ((cacheDom c).map (Function.Embedding.subtype (· ∈ S)))
        (.inl x) (extendTable S (completeTable c g)) ↔
        listBadU' U C R (histOf (viewC S c)) x (tableOf (viewC S c) (viewG S g)) := by
      intro g
      show listBadU' U C R _ x _ ↔ _
      rw [← histOf_viewC]
      exact listBadU'_congr U C R (fun y hy => viewT_extendTable c g (hH hy))
        (viewT_extendTable c g hx) (fun v => viewT_extendTable c g (hS₁ v))
    refine (prEvent_mono _ _ (fun g => listBadU' U C R (histOf (viewC S c)) x
      (tableOf (viewC S c) (viewG S g))) fun g h => (hev g).mp h).trans ?_
    rw [prEvent_view S (fun h => listBadU' U C R (histOf (viewC S c)) x (tableOf (viewC S c) h))]
    refine (prob_listBadU' U C R hS₁ (viewC S c) ⟨x, hx⟩ hc₁).trans ?_
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
    exact add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hle) _) le_rfl

/-- **Each fresh query is bad with probability at most
`(|H| + nRf (|H| + 1) + k) / 2^256 + maxErrK`.** -/
theorem prob_advBadU' (A : OracleComp KeccakCalls Pf) (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[advBadU' U C R view A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      (((cacheDom c).card + U.nRf * ((cacheDom c).card + 1) + U.K.rounds.length : ℕ) : ℝ≥0∞) /
        2 ^ 256 + maxErrK U.K C R := by
  refine (prEvent_or_le _ _ _).trans ((add_le_add (prob_kcBadU' U C R S hS₀ c t ht)
    (prob_rootBadK U.K view A S c t ht)).trans (le_of_eq ?_))
  rw [Nat.cast_add (R := ℝ≥0∞) ((cacheDom c).card + U.nRf * ((cacheDom c).card + 1))
    U.K.rounds.length, ENNReal.add_div]
  ring

end Exp

/-! ## The run with its whole transcript -/

section Run

variable {F St M Pf : Type} [SampleableType F]

/-- The openings make at most `Σ_k QO_k` queries. -/
theorem isTotalQueryBound_opsRun' (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)),
      IsTotalQueryBound (opsRun view ops π ch) (ops.map fun o => o.S.QO).sum
  | [], _, _ => trivial
  | o :: os, π, ch => by
    simp only [opsRun, List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind (o.S.queries _) fun _ =>
      (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_opsRun' view os π ch)

/-- **The run with its whole transcript makes at most `QX + Σ_k QO_k` queries.** -/
theorem isTotalQueryBound_expL (view : Pf → St × List (RMsg F))
    (X : OracleComp KeccakCalls (PreK Pf F)) (ops : List (WhirOp Pf F M)) (QX : ℕ)
    (hX : IsTotalQueryBound X QX) :
    IsTotalQueryBound (expL view X ops) (QX + (ops.map fun o => o.S.QO).sum) := by
  unfold expL
  exact isTotalQueryBound_loggedKC_run _ _ [] (isTotalQueryBound_bind hX fun x =>
    (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_opsRun' view ops x.1 x.2.1))

/-- A Keccak-256 input of a log against a table is in the log's transcript with the table's
answer. -/
theorem mem_filterMap_inlEntry (T : KTable)
    (l : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d)) (hl : ∀ q ∈ l, q.2 = T q.1)
    {x : List UInt8} (hx : Sum.inl x ∈ l.map Sigma.fst) :
    (x, viewT T x) ∈ l.filterMap inlEntry := by
  obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hx
  refine List.mem_filterMap.mpr ⟨q, hq, ?_⟩
  obtain ⟨d, u⟩ := q
  simp only at hqx
  subst hqx
  have hu := hl _ hq
  simp only at hu
  subst hu
  rfl

end Run

/-! ## The trace of the run with its whole transcript -/

section Trace

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (U : ChainSpecU F St) (R : Piop U.K M) (view : Pf → St × List (RMsg F))

open Classical in
/-- **The trace of the run with its whole transcript**: on every table of both oracles, a run that
breaks knowledge soundness while no opening is doomed at the end of the run (`DoomF`) and no two
answers of its transcript make a pair (`PairTr`) asks a bad fresh query, when the label's first 32
bytes are `tag ‖` the first bytes of an answer the adversary asked (`hlabT`). Doom read at the
run's end: an undoomed opening's candidate is read off the whole history `L`, whose word under a
root of the adversary is the adversary's (`hstab` at `H = L`). -/
theorem trace_whirU' {σ : Type} (ops : List (WhirOp Pf F M)) (tc : ℕ → TableCode M)
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
    (tag : List UInt8) (T : KTable)
    (hlabT : ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map Sigma.fst ∧
      (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length))
    (hev : BreaksOK U.K (fun i => (tc i).commit) R view check
        (fun bs => ∀ k < ops.length, bs.getD k false = true)
        (evalWithAnswerFn (QueryImpl.ofFn T)
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).1 ∧
      ¬ DoomF view ops (evalWithAnswerFn (QueryImpl.ofFn T)
          (expL view (preU U view (withSetupG setup fix A₀)) ops)) ∧
      ¬ PairTr tag (evalWithAnswerFn (QueryImpl.ofFn T)
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).2) :
    FreshBad (advBadU' U (fun i => (tc i).commit) R view (withSetupG setup fix A₀)) T ∅
      ((tableQueryLog (expL view (preU U view (withSetupG setup fix A₀)) ops) T).map
        Sigma.fst) := by
  -- The run's parts, against the table.
  obtain ⟨hsl, hse⟩ := withSetupG_run setup fix A₀ T
  obtain ⟨hpl, hpe⟩ := preU_run U view (withSetupG setup fix A₀) T
  set A := withSetupG setup fix A₀ with hAdef
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A with hp
  set ch := evalWithAnswerFn (QueryImpl.ofFn T) (U.chain hash256 (view p).1 (view p).2) with hch
  set lA := tableQueryLog A T with hlA
  set lC := tableQueryLog (U.chain hash256 (view p).1 (view p).2) T with hlC
  set lO := tableQueryLog (opsRun view ops p ch) T with hlO
  set bs := evalWithAnswerFn (QueryImpl.ofFn T) (opsRun view ops p ch) with hbs
  set tA : Transcript := lA.filterMap inlEntry with htA
  set Y := preU U view A >>= fun x => opsOut x <$> opsRun view ops x.1 x.2.1 with hY
  have hYl : tableQueryLog Y T = (lA ++ lC) ++ lO := by
    rw [hY, tableQueryLog_bind, tableQueryLog_map, hpl, hpe]
  have hYe : evalWithAnswerFn (QueryImpl.ofFn T) Y = ((p, (ch, bs)), tA) := by
    rw [hY, evalWithAnswerFn_bind, evalWithAnswerFn_map, hpe]
    rfl
  obtain ⟨hLl, hLe⟩ := run_logged Y T
  have hlogL : tableQueryLog (expL view (preU U view A) ops) T = (lA ++ lC) ++ lO := by
    rw [← hYl]
    exact hLl
  have hevalL : evalWithAnswerFn (QueryImpl.ofFn T) (expL view (preU U view A) ops) =
      (((p, (ch, bs)), tA), ((lA ++ lC) ++ lO).filterMap inlEntry) := by
    rw [← hYl, ← hYe]
    exact hLe
  have hYU : Y = expU U view A (opsRun view ops) := (expU_eq U view A ops).symm
  have hlogU : tableQueryLog (expU U view A (opsRun view ops)) T = (lA ++ lC) ++ lO := by
    rw [← hYU]
    exact hYl
  set zK := evalWithAnswerFn (QueryImpl.ofFn T) (expU U view A (opsRun view ops)) with hzK
  have hzKe : zK = ((p, (ch, bs)), tA) := by
    rw [hzK, ← hYU]
    exact hYe
  have hK11 : zK.1.1 = p := by rw [hzKe]
  have hK121 : zK.1.2.1 = ch := by rw [hzKe]
  have hK2 : zK.2 = tA := by rw [hzKe]
  -- Every entry of the run's log holds the table's answer.
  have hsnd : ∀ e ∈ (lA ++ lC) ++ lO, e.2 = T e.1 := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · exact tableQueryLog_snd_dep T _ e he
      · exact tableQueryLog_snd_dep T _ e he
    · exact tableQueryLog_snd_dep T _ e he
  -- The event.
  obtain ⟨hB, hnd, hnp⟩ := hev
  rw [hevalL] at hB hnd hnp
  have hBK : BreaksOK U.K CC R view check (fun bs => ∀ k < ops.length, bs.getD k false = true)
      zK := by
    rw [hzKe]
    exact hB
  have hcheck : check p ch := hB.1
  have hverd : ∀ k < ops.length, bs.getD k false = true := hB.2.1
  have hnotdoom : ∀ m (hm : m < ops.length), ¬ OpeningDoomed ops[m].S.L ops[m].S.R
      (WhirOp.input view ops[m] p ch) (cacheOfTr (((lA ++ lC) ++ lO).filterMap inlEntry)) :=
    fun m hm hD => hnd ⟨m, hm, hverd m hm, hD⟩
  -- No bad fresh query, from here on.
  rw [hlogL]
  by_contra hnb
  set Lk := ((lA ++ lC) ++ lO).map Sigma.fst with hLkdef
  set L := Lk.filterMap Sum.getLeft? with hLdef
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft? with hLAdef
  have hk : ¬ FreshBad (kcBadU' U CC R) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK U.K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadU' U CC R) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcU' U CC R T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := rf_beforeU' hl
  have hinj : Set.InjOn (viewT T) ↑L.toFinset := injOn_of_not_freshBadU' hl
  have hLk : Lk = lA.map Sigma.fst ++ ((lC ++ lO).map Sigma.fst) := by
    rw [hLkdef]
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
  have hLAL : ∀ y ∈ LA, y ∈ L := fun y hy => by
    rw [hLA]
    exact List.mem_append_left _ hy
  -- An undoomed opening has a candidate of the run's word satisfying its claims.
  have hcand : ∀ m (hm : m < ops.length) (o : WhirOp Pf F M), ops[m] = o →
      ∃ q ∈ Candidates o.S.L.logN o.S.R (code₀ o.S.L.logN o.S.R).thr
          (Rom.extract (ansOf L.toFinset (viewT T)) (ofB (WhirOp.root view o p))
            (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold)),
        ∀ cl ∈ (o.cl p ch).claims, o.S.L.tableEval q cl.point = cl.value := by
    intro m hm o ho
    have hd := hnotdoom m hm
    rw [ho] at hd
    unfold OpeningDoomed at hd
    push Not at hd
    obtain ⟨q, hq, hqc⟩ := hd
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
      (W := Rom.extract (ansOf L.toFinset (viewT T)) (ofB r) (rootHeight o.S.L.logN o.S.R)
        (2 ^ laneFold))
      (W' := wordOfMerkle (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold)
        (merkleWord L.toFinset (viewT T) (rootHeight o.S.L.logN o.S.R) (8 * 2 ^ laneFold)
          (toB (ofB r))))
      fun v hv => (wordOfMerkle_eq_extract hinj _ _ _ hv).symm
    have htoB : toB (ofB r) = r := LeanVM.Rpm.digestToRpm_ofRpm _
    rw [hword, htoB, hstab L hLAL (fun y hy => hy) r hrr] at hq
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
          x ∈ L.toFinset := by
        intro x hx
        refine List.mem_toFinset.mpr (hLAL x (mem_filterMap_getLeft?.mpr ?_))
        rw [hsl, List.map_append]
        exact List.mem_append_left _ hx
      have hroot_o : WhirOp.root view o p = root p := by
        unfold WhirOp.root
        rw [htg]
      rw [hroot_o, hse] at hq
      have hword := candidates_congr (μ := o.S.L.logN) (R := o.S.R)
        (A := (code₀ o.S.L.logN o.S.R).thr)
        (W := Rom.extract (ansOf L.toFinset (viewT T))
          (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup)
            (evalWithAnswerFn (QueryImpl.ofFn T)
              (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup))))))
          (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold))
        (W' := word) fun v hv => hsw T L.toFinset
          (evalWithAnswerFn (QueryImpl.ofFn T) (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)))
          hsub hinj v hv
      rw [hword] at hq
      have hq₀ := candidates_honest o.S.adm hhon hq
      subst hq₀
      exact hqc
  have hgS : goodS p ch := hS p ch hSH
  -- The seed: no answer of the run is the label's first 32 bytes, else a pair.
  have hseed : ∀ z ∈ ((tableQueryLog (expU U view A (opsRun view ops)) T).map
      Sigma.fst).filterMap Sum.getLeft?,
      (viewT T z).toList ≠ (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1).take 32 := by
    obtain ⟨w, hwA, hw⟩ := hlabT
    intro z hz hzl
    rw [hlogU] at hz
    refine hnp ⟨(z, viewT T z), mem_filterMap_inlEntry T _ hsnd (mem_filterMap_getLeft?.mp hz),
      (w, viewT T w), mem_filterMap_inlEntry T _ hsnd ?_, ?_⟩
    · rw [List.map_append, List.map_append]
      exact List.mem_append_left _ (List.mem_append_left _ hwA)
    · exact hzl.trans hw
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
  · have := trace_advU' U CC R view A (opsRun view ops) T hseed hwin
    rw [hlogU] at this
    exact hnb this

/-! ## Knowledge soundness, the seed separated by a pair of answers -/

/-- **Knowledge soundness of the chain over any encoding with WHIR openings, at `≥ 128` bits**
(`knowledgeSoundness_listChainU_closed` with no tag term and every opening's doom read at the end
of the run): the verifier accepts while no candidate of round `0`'s root read off the adversary's
(and the setup's) queries satisfies the first round's state with probability at most

`Pr[DoomF] + Pr[PairTr tag] + N (maxErrK + (nRf + 2) N / 2^256)`,
`N = QS + Q + nQ + Σ_k QO_k`,

the two events of the run with its whole Keccak-256 transcript (`expL`), when the label's first 32
bytes are `tag ‖` the first `32 − |tag|` bytes of an answer the adversary (or the setup) asked
(`hlab`). -/
theorem knowledgeSoundness_listChainU_closed128 {σ : Type} (ops : List (WhirOp Pf F M))
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
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (tag : List UInt8)
    (hlab : ∀ T : KTable, ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map
        Sigma.fst ∧
      (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length)) :
    Pr{let z ← (simulateQ randomOracle
        (expU U view (withSetupG setup fix A₀) (opsRun view ops))).run' ∅}[
        BreaksOK U.K (fun i => (tc i).commit) R view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true) z] ≤
      Pr{let z ← (simulateQ randomOracle
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[DoomF view ops z] +
      Pr{let z ← (simulateQ randomOracle
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[PairTr tag z.2] +
      ((QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) *
        (maxErrK U.K (fun i => (tc i).commit) R +
          (((U.nRf + 2) * (QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum) : ℕ) : ℝ≥0∞) /
            2 ^ 256) := by
  set A := withSetupG setup fix A₀ with hAdef
  have hA : IsTotalQueryBound A (QS + Q) :=
    isTotalQueryBound_withSetupG setup fix A₀ QS Q hSq hQ
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set accL : List Bool → Prop := fun bs => ∀ k < ops.length, bs.getD k false = true with haccL
  set N := QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum with hN
  -- The event on the run with its whole transcript.
  have h1 : Pr{let z ← (simulateQ randomOracle (expU U view A (opsRun view ops))).run' ∅}[
        BreaksOK U.K CC R view check accL z] =
      Pr{let z ← (simulateQ randomOracle (expL view (preU U view A) ops)).run' ∅}[
        BreaksOK U.K CC R view check accL z.1] := by
    rw [expL, prEvent_run'_loggedKC _ [] ∅ (fun w => BreaksOK U.K CC R view check accL w),
      expU_eq]
  rw [h1]
  set mx := (simulateQ randomOracle (expL view (preU U view A) ops)).run' ∅ with hmx
  refine (prEvent_mono mx _ (fun z => DoomF view ops z ∨ PairTr tag z.2 ∨
    (BreaksOK U.K CC R view check accL z.1 ∧ ¬ DoomF view ops z ∧ ¬ PairTr tag z.2))
    fun z h => ?_).trans ((prEvent_or_le _ _ _).trans ?_)
  · by_cases hd : DoomF view ops z
    · exact Or.inl hd
    · by_cases hpt : PairTr tag z.2
      · exact Or.inr (Or.inl hpt)
      · exact Or.inr (Or.inr ⟨h, hd, hpt⟩)
  rw [add_assoc]
  refine add_le_add le_rfl ((prEvent_or_le _ _ _).trans (add_le_add le_rfl ?_))
  refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (expL view (preU U view A) ops)
    N (isTotalQueryBound_expL view (preU U view A) ops _ (isTotalQueryBound_preU U view A _ hA))
    (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
    (Set.finite_range _) _ (advBadU' U CC R view A) _ (fun S hS' c t ht hcard => ?_)
    (fun T h => trace_whirU' U R view ops tc check good goodS setup fix A₀ hok hcov hS hfit
      hlink tag T (hlab T) h)
  have hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
    fun v => hS' _ ⟨v, rfl⟩
  refine (prob_advBadU' U CC R view A S hS₀ c t ht).trans ?_
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
        ℝ≥0∞) / 2 ^ 256 + maxErrK U.K CC R
      ≤ (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 + maxErrK U.K CC R :=
        add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hNle) _) le_rfl
    _ = maxErrK U.K CC R + (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 := by ring

end Trace

end Compose

/-- info: 'Compose.prob_advBadU'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prob_advBadU'

/-- info: 'Compose.trace_whirU'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_whirU'

/-- info: 'Compose.knowledgeSoundness_listChainU_closed128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainU_closed128
