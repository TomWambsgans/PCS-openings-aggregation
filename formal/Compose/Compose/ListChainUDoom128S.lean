-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/Compose/Compose/ListChainUDoom128.lean` of this repository (`trace_whirU'`,
-- `knowledgeSoundness_listChainU_closed128`), with two generalisations for π2's verifier
-- (`formal/RecCompose`): the setup's openings' stacks read off the proof, and the protocol a function of
-- the setup's output.
import Compose.ListChainUDoom128

/-!
# The chain with WHIR openings, the setup's stacks and the protocol read off the setup

`ListChainUDoom128.lean`'s `knowledgeSoundness_listChainU_closed128` fixes two things in advance that
π2's verifier (`formal/RecCompose`) reads off the setup:

* **a setup opening's stack** (`Tgt.setup root q₀`: `q₀` fixed). π2's setup table (`κ`, `κ + σ`) is the
  circuit's for π1's contract IV, a function of π1's setup roots, which the setup computes over `π`. Here
  each opening has an **optional stack read off the proof** (`stk o : Option (Pf → Column _)`, the proof
  carrying the setup's roots): `some f`, the setup committed `f π` under the opening's root
  (`WhirOp.OKP`) and the opening's claims hold of it (`WhirOp.SetupHoldsP`); `none`, an opening nothing is
  concluded of (its acceptance is required, its doom charged; π1's three openings, which π2's contract
  makes before its own);
* **the protocol** (`R : Piop U.K M`): π2's PIOP is the compiled circuit's at π1's contract IV and the
  setup's tables, a function of the setup's roots. Here `R : σ → Piop U.K M`, read at the setup's output
  (`sOf` of the proof, `hsOf`). A fresh query's bad event reads the protocol at the setup's output when
  the setup's queries are all in the history (`advBadS`), else at `default` (no query of the setup is a
  label, `hlabel`, so before the setup's end no input parses as a chain step and the protocol is not read).

**`knowledgeSoundness_listChainU_closed128S`**: the bound of `knowledgeSoundness_listChainU_closed128`,
`maxErrK` bounded uniformly over the setup's outputs (`hme`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

section Defs

variable {F St M Pf : Type} [SampleableType F]

/-- **What the openings need, the setup's stacks read off the proof**: a round's opening as `WhirOp.OK`'s;
a setup opening with a stack `f` (`stk o = some f`), that the setup's queries make the word under its root
the honest encoding of `f` at the proof the setup fixes; a setup opening without one, nothing. -/
def WhirOp.OKP {σ : Type} (tc : ℕ → TableCode M) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : WhirOp Pf F M) → Option (Pf → Column o.S.L.logN)) (o : WhirOp Pf F M) : Prop :=
  match o.tgt with
  | .round i read => (tc i).height = rootHeight o.S.L.logN o.S.R ∧
      (tc i).leafLen = 8 * 2 ^ laneFold ∧
      (∀ w q, q ∈ Candidates o.S.L.logN o.S.R (code₀ o.S.L.logN o.S.R).thr
        (wordOfMerkle (tc i).height (2 ^ laneFold) w) → read q ∈ (tc i).dec w) ∧
      ∀ π ch q, (∀ cl ∈ (o.cl π ch).claims, o.S.L.tableEval q cl.point = cl.value) →
        good i π ch (some (read q))
  | .setup root _ => ∀ f, stk o = some f →
      ∀ (T : KTable) (H : Hist) (p : Pf),
        (∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → x ∈ H) →
          Set.InjOn (viewT T) ↑H →
            ∃ word : Word, HonestWord o.S.L.logN o.S.R word
                (f (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)) ∧
              ∀ v < 2 ^ rootHeight o.S.L.logN o.S.R,
                Rom.extract (ansOf H (viewT T))
                  (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)))
                  (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold) v = word v

/-- **A setup opening's stack satisfies its claims**, when it has one (nothing for a round's opening or a
setup opening without a stack). -/
def WhirOp.SetupHoldsP (stk : (o : WhirOp Pf F M) → Option (Pf → Column o.S.L.logN))
    (o : WhirOp Pf F M) (π : Pf) (ch : List (List F)) : Prop :=
  match o.tgt with
  | .round _ _ => True
  | .setup _ _ => ∀ f, stk o = some f → ∀ cl ∈ (o.cl π ch).claims, o.S.L.tableEval (f π) cl.point = cl.value

end Defs

/-! ## Helpers: tables, the setup's output, the transfer of a fresh bad query -/

section Helpers

/-- **Tables agreeing on a run's queries give the same log and result.** -/
theorem tableQueryLog_congr_agree {D : Type} {R : D → Type} {α : Type}
    (oa : OracleComp (OracleSpec.ofFn R) α) (g g' : ∀ d, R d) :
    (∀ q ∈ (tableQueryLog oa g).map Sigma.fst, g q = g' q) →
      tableQueryLog oa g' = tableQueryLog oa g ∧
        evalWithAnswerFn (QueryImpl.ofFn g') oa = evalWithAnswerFn (QueryImpl.ofFn g) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _; simp
  | query_bind t k ih =>
    intro h
    simp only [tableQueryLog_query_bind, List.map_cons, List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨ht, hk⟩ := h
    obtain ⟨e1, e2⟩ := ih (g t) hk
    simp only [tableQueryLog_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      QueryImpl.ofFn_apply]
    rw [← ht]
    exact ⟨by rw [e1], e2⟩

open Classical in
/-- **The setup's output, read off a history**: its output against the table when the history holds
every query it makes there, else `default`. -/
noncomputable def setupAt {σ : Type} [Inhabited σ] (setup : OracleComp KeccakCalls σ)
    (H : Finset (List UInt8 ⊕ KeccakState)) (T : KTable) : σ :=
  if ∀ q ∈ (tableQueryLog setup T).map Sigma.fst, q ∈ H then
    evalWithAnswerFn (QueryImpl.ofFn T) setup else default

theorem setupAt_of_sub {σ : Type} [Inhabited σ] (setup : OracleComp KeccakCalls σ)
    (H : Finset (List UInt8 ⊕ KeccakState)) (T : KTable)
    (h : ∀ q ∈ (tableQueryLog setup T).map Sigma.fst, q ∈ H) :
    setupAt setup H T = evalWithAnswerFn (QueryImpl.ofFn T) setup := by
  classical
  unfold setupAt
  rw [ite_eq_left h]

/-- **The setup's output read off a history depends on the table only there.** -/
theorem setupAt_congr {σ : Type} [Inhabited σ] (setup : OracleComp KeccakCalls σ)
    (H : Finset (List UInt8 ⊕ KeccakState)) (T T' : KTable) (hT : ∀ q ∈ H, T q = T' q) :
    setupAt setup H T = setupAt setup H T' := by
  classical
  unfold setupAt
  by_cases h : ∀ q ∈ (tableQueryLog setup T).map Sigma.fst, q ∈ H
  · obtain ⟨hl, he⟩ := tableQueryLog_congr_agree setup T T' fun q hq => hT q (h q hq)
    have h' : ∀ q ∈ (tableQueryLog setup T').map Sigma.fst, q ∈ H := by
      rw [hl]
      exact h
    rw [ite_eq_left h, ite_eq_left h', he]
  · by_cases h' : ∀ q ∈ (tableQueryLog setup T').map Sigma.fst, q ∈ H
    · obtain ⟨hl, -⟩ := tableQueryLog_congr_agree setup T' T fun q hq => (hT q (h' q hq)).symm
      refine absurd ?_ h
      rw [hl]
      exact h'
    · rw [ite_eq_right h, ite_eq_right h']

/-- **A fresh bad query for one predicate is one for another** that it implies at every history the
list builds. -/
theorem freshBad_transfer {D τ : Type} [DecidableEq D] {b₁ b₂ : Finset D → D → τ → Prop} (T : τ) :
    ∀ (L : List D) (H : Finset D), FreshBad b₁ T H L →
      (∀ (k : ℕ) (hk : k < L.length), b₁ (H ∪ (L.take k).toFinset) L[k] T →
        b₂ (H ∪ (L.take k).toFinset) L[k] T) →
      FreshBad b₂ T H L
  | [], _, h, _ => h
  | x :: xs, H, h, hb => by
    rcases h with ⟨hx, h⟩ | h
    · left
      refine ⟨hx, ?_⟩
      have := hb 0 (by simp) (by simpa using h)
      simpa using this
    · right
      refine freshBad_transfer T xs (insert x H) h fun k hk h' => ?_
      have e : H ∪ ((x :: xs).take (k + 1)).toFinset = insert x H ∪ (xs.take k).toFinset := by
        rw [List.take_succ_cons, List.toFinset_cons, Finset.union_insert, Finset.insert_union]
      have := hb (k + 1) (by simpa using hk) (by rw [e]; simpa using h')
      rw [e] at this
      simpa using this

theorem mem_prevIn_self (T : Table) (y : List UInt8) (l : List (List UInt8)) (e : List UInt8) :
    y ∈ prevIn T y (l ++ [e]) := by
  cases l <;> simp [prevIn]

/-- **Without a label in the history, a fresh query's badness does not read the protocol**: no input
parses as a chain step (`ParseU'` needs the label among the history's inputs). -/
theorem advBadU'_of_noLabel {F St M Pf : Type} [SampleableType F] (U : ChainSpecU F St)
    (C : ℕ → ListCommit M) (R₁ R₂ : Piop U.K M) (view : Pf → St × List (RMsg F))
    (A : OracleComp KeccakCalls Pf) (H : Finset (List UInt8 ⊕ KeccakState))
    (d : List UInt8 ⊕ KeccakState) (T : KTable) (hH : ∀ s, Sum.inl (U.label s) ∉ H)
    (h : advBadU' U C R₁ view A H d T) : advBadU' U C R₂ view A H d T := by
  rcases h with h | h
  · refine Or.inl ?_
    cases d with
    | inl x =>
      rcases h with h | ⟨j, s, ms, m, hp, -⟩
      · exact Or.inl h
      · exact absurd (mem_viewH.mp (hp.2.2.2.2.1 _ (mem_prevIn_self _ _ _ _))) (hH s)
    | inr _ => exact h
  · exact Or.inr h

variable {F St M Pf : Type} [SampleableType F] (U : ChainSpecU F St)
  (view : Pf → St × List (RMsg F))

/-- The run with its whole transcript, its proof: the adversary's. -/
theorem expL_eval_proof (A : OracleComp KeccakCalls Pf) (ops : List (WhirOp Pf F M)) (T : KTable) :
    (evalWithAnswerFn (QueryImpl.ofFn T) (expL view (preU U view A) ops)).1.1.1 =
      evalWithAnswerFn (QueryImpl.ofFn T) A := by
  unfold expL
  rw [(run_logged _ T).2, evalWithAnswerFn_bind, evalWithAnswerFn_map, (preU_run U view A T).2]
  rfl

theorem exists_map_append4 {α β : Type} (f : α → β) (a b c d : List α) :
    ∃ rest, (a ++ b ++ c ++ d).map f = a.map f ++ rest :=
  ⟨(b ++ c ++ d).map f, by simp⟩

/-- The run with its whole transcript asks the setup's queries first. -/
theorem expL_log_setup {σ : Type} (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCalls Pf) (ops : List (WhirOp Pf F M)) (T : KTable) :
    ∃ rest, (tableQueryLog (expL view (preU U view (withSetupG setup fix A₀)) ops) T).map
        Sigma.fst = (tableQueryLog setup T).map Sigma.fst ++ rest := by
  unfold expL
  rw [(run_logged _ T).1, tableQueryLog_bind, (preU_run U view _ T).1,
    (withSetupG_run setup fix A₀ T).1]
  exact exists_map_append4 Sigma.fst _ _ _ _

end Helpers

/-! ## The trace -/

section Trace

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (U : ChainSpecU F St) (R : Piop U.K M) (view : Pf → St × List (RMsg F))

open Classical in
/-- **The trace, the setup's stacks read off the proof** (`trace_whirU'` with `WhirOp.OKP` and
`WhirOp.SetupHoldsP` for `WhirOp.OK` and `WhirOp.SetupHolds`). -/
theorem trace_whirP {σ : Type} (ops : List (WhirOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : WhirOp Pf F M) → Option (Pf → Column o.S.L.logN))
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (hok : ∀ o ∈ ops, WhirOp.OKP tc good setup fix stk o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHoldsP stk o π ch) → goodS π ch)
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
    have hokO : WhirOp.OKP tc good setup fix stk o := hok o hoops
    obtain ⟨r, hmr, hrr⟩ := exists_root_of_fits U.K hfit' i hi hri
    unfold WhirOp.OKP at hokO
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
  have hSH : ∀ o ∈ ops, WhirOp.SetupHoldsP stk o p ch := by
    intro o hoops
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : WhirOp.OKP tc good setup fix stk o := hok o hoops
    unfold WhirOp.SetupHoldsP
    unfold WhirOp.OKP at hokO
    rcases htg : o.tgt with ⟨i, rd⟩ | ⟨root, q₀⟩
    · trivial
    · intro f hf
      rw [htg] at hokO
      have hsub : ∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst →
          x ∈ L.toFinset := by
        intro x hx
        refine List.mem_toFinset.mpr (hLAL x (mem_filterMap_getLeft?.mpr ?_))
        rw [hsl, List.map_append]
        exact List.mem_append_left _ hx
      obtain ⟨word, hhon, hsw⟩ := hokO f hf T L.toFinset
        (evalWithAnswerFn (QueryImpl.ofFn T) (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)))
        hsub hinj
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
        (W' := word) fun v hv => hsw v hv
      rw [hword] at hq
      have hq₀ := candidates_honest o.S.adm hhon hq
      subst hq₀
      rw [← hse] at hqc
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

end Trace

/-! ## Knowledge soundness, the protocol read off the setup -/

section Closed

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (U : ChainSpecU F St) (view : Pf → St × List (RMsg F))

/-- **Knowledge soundness of the chain with WHIR openings, the setup's stacks and the protocol read off the
setup** (`knowledgeSoundness_listChainU_closed128` with `R : σ → Piop`, read at the setup's output `sOf π`,
and `WhirOp.OKP`): the verifier accepts while no candidate of round `0`'s root read off the adversary's
(and the setup's) queries satisfies the first round's state of the protocol at the setup's output with
probability at most

`Pr[DoomF] + Pr[PairTr tag] + N (me + (nRf + 2) N / 2^256)`, `N = QS + Q + nQ + Σ_k QO_k`,

`me` bounding `maxErrK` at every output of the setup, when no query of the setup is a label (`hlabel`). -/
theorem knowledgeSoundness_listChainU_closed128S {σ : Type} [Inhabited σ] (R : σ → Piop U.K M)
    (sOf : Pf → σ) (ops : List (WhirOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : WhirOp Pf F M) → Option (Pf → Column o.S.L.logN))
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (QS Q : ℕ) (hSq : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hsOf : ∀ s p, sOf (fix s p) = s)
    (hok : ∀ o ∈ ops, WhirOp.OKP tc good setup fix stk o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHoldsP stk o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll U.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = U.K.rounds.length →
      (∀ i (h : i < cs.length), (U.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (U.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ (R (sOf π)).post (view π).1 p m c)
    (hlabel : ∀ (T : KTable) (x : List UInt8),
      Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → ∀ s, x ≠ U.label s)
    (tag : List UInt8)
    (hlab : ∀ T : KTable, ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map
        Sigma.fst ∧
      (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length))
    (me : ℝ≥0∞) (hme : ∀ s, maxErrK U.K (fun i => (tc i).commit) (R s) ≤ me) :
    Pr{let z ← (simulateQ randomOracle
        (expU U view (withSetupG setup fix A₀) (opsRun view ops))).run' ∅}[
        BreaksOK U.K (fun i => (tc i).commit) (R (sOf z.1.1)) view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true) z] ≤
      Pr{let z ← (simulateQ randomOracle
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[DoomF view ops z] +
      Pr{let z ← (simulateQ randomOracle
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[PairTr tag z.2] +
      ((QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) *
        (me + (((U.nRf + 2) * (QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum) : ℕ) : ℝ≥0∞) /
            2 ^ 256) := by
  classical
  set A := withSetupG setup fix A₀ with hAdef
  have hA : IsTotalQueryBound A (QS + Q) :=
    isTotalQueryBound_withSetupG setup fix A₀ QS Q hSq hQ
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set accL : List Bool → Prop := fun bs => ∀ k < ops.length, bs.getD k false = true with haccL
  set N := QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum with hN
  -- The event on the run with its whole transcript.
  have h1 : Pr{let z ← (simulateQ randomOracle (expU U view A (opsRun view ops))).run' ∅}[
        BreaksOK U.K CC (R (sOf z.1.1)) view check accL z] =
      Pr{let z ← (simulateQ randomOracle (expL view (preU U view A) ops)).run' ∅}[
        BreaksOK U.K CC (R (sOf z.1.1.1)) view check accL z.1] := by
    rw [expL, prEvent_run'_loggedKC _ [] ∅
      (fun w => BreaksOK U.K CC (R (sOf w.1.1)) view check accL w), expU_eq]
  rw [h1]
  set mx := (simulateQ randomOracle (expL view (preU U view A) ops)).run' ∅ with hmx
  refine (prEvent_mono mx _ (fun z => DoomF view ops z ∨ PairTr tag z.2 ∨
    (BreaksOK U.K CC (R (sOf z.1.1.1)) view check accL z.1 ∧ ¬ DoomF view ops z ∧
      ¬ PairTr tag z.2)) fun z h => ?_).trans ((prEvent_or_le _ _ _).trans ?_)
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
    (Set.finite_range _) _ (fun H d T => advBadU' U CC (R (setupAt setup H T)) view A H d T) _
    (fun S hS' c t ht hcard => ?_) (fun T h => ?_)
  · -- Each fresh query: the setup's output read off the cache does not depend on the completion.
    have hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS' _ ⟨v, rfl⟩
    have hagree : ∀ g g' : (d : ↥S) → KeccakCalls d.1,
        ∀ q ∈ (cacheDom c).map (Function.Embedding.subtype (· ∈ S)),
          extendTable S (completeTable c g) q = extendTable S (completeTable c g') q := by
      intro g g' q hq
      obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hq
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (mem_cacheDom.mp hd)
      show extendTable S (completeTable c g) d.1 = extendTable S (completeTable c g') d.1
      rw [extendTable_subtype, extendTable_subtype]
      simp only [completeTable, hu, Option.getD_some]
    rcases isEmpty_or_nonempty ((d : ↥S) → KeccakCalls d.1) with he | ⟨⟨g₀⟩⟩
    · exact le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _
        fun g _ => (IsEmpty.false g).elim)) bot_le
    set r₀ := setupAt setup ((cacheDom c).map (Function.Embedding.subtype (· ∈ S)))
      (extendTable S (completeTable c g₀)) with hr₀
    refine (prEvent_mono _ _ (fun g => advBadU' U CC (R r₀) view A
      ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
      (extendTable S (completeTable c g))) fun g hg => ?_).trans ?_
    · rw [hr₀, ← setupAt_congr setup _ _ _ (hagree g g₀)]
      exact hg
    refine (prob_advBadU' U CC (R r₀) view A S hS₀ c t ht).trans ?_
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
          ℝ≥0∞) / 2 ^ 256 + maxErrK U.K CC (R r₀)
        ≤ (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 + me :=
          add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hNle) _) (hme r₀)
      _ = me + (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 := by ring
  · -- The trace, at the protocol of the setup's output against `T`.
    obtain ⟨hB, hnd, hnp⟩ := h
    set s₀ := evalWithAnswerFn (QueryImpl.ofFn T) setup with hs₀
    have hsp : sOf (evalWithAnswerFn (QueryImpl.ofFn T) (expL view (preU U view A) ops)).1.1.1 =
        s₀ := by
      rw [expL_eval_proof U view A ops T, hAdef, (withSetupG_run setup fix A₀ T).2, hsOf]
    rw [hsp] at hB
    have hfr := trace_whirP U (R s₀) view ops tc (fun π ch => check π ch ∧ sOf π = s₀) good goodS
      setup fix stk A₀ hok hcov hS (fun π ch h => hfit π ch h.1)
      (fun π ch cs h hl hg hn hgS => by
        obtain ⟨p, m, c, he, hp⟩ := hlink π ch cs h.1 hl hg hn hgS
        refine ⟨p, m, c, he, ?_⟩
        rw [← h.2]
        exact hp)
      tag T (hlab T) ⟨⟨⟨hB.1, hsp⟩, hB.2.1, hB.2.2⟩, hnd, hnp⟩
    -- From the protocol at the setup's output to the one read off each history.
    obtain ⟨rest, hlog⟩ := expL_log_setup U view setup fix A₀ ops T
    refine freshBad_transfer T _ ∅ hfr fun k hk hb => ?_
    rw [Finset.empty_union] at hb ⊢
    by_cases hkS : ((tableQueryLog setup T).map Sigma.fst).length ≤ k
    · -- The history holds the whole setup's log.
      have hsub : ∀ q ∈ (tableQueryLog setup T).map Sigma.fst,
          q ∈ (((tableQueryLog (expL view (preU U view A) ops) T).map Sigma.fst).take
            k).toFinset := by
        intro q hq
        rw [List.mem_toFinset, hlog, List.take_append, List.take_of_length_le hkS]
        exact List.mem_append_left _ hq
      rw [setupAt_of_sub setup _ T hsub]
      exact hb
    · -- The history holds only the setup's queries: no label.
      refine advBadU'_of_noLabel U CC (R s₀) _ view A _ _ T (fun s hs => ?_) hb
      rw [List.mem_toFinset, hlog, List.take_append_of_le_length (by omega)] at hs
      exact hlabel T (U.label s) (List.mem_of_mem_take hs) s rfl

end Closed

end Compose

/-- info: 'Compose.trace_whirP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_whirP

/-- info: 'Compose.knowledgeSoundness_listChainU_closed128S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainU_closed128S
