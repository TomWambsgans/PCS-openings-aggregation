-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `formal/UniSound/UniSound/FsProof.lean` (`setupK3`'s
-- facts, `whirOp_ok_tree`) and `FsSetup.lean` (`uniSetupBridge`) for π2's setup: π1's three trees, then π2's.
import RecCompose.FsDefs
import UniSound.FsSetup

/-!
# π2's setup: its facts, its opening, and the bridge

The composed setup `p2Setup` (`FsDefs.lean`: π1's three trees `UniSound.uSetup`, then π2's tree of the setup's table
`κ`, `κ + σ` at π1's contract IV of those roots, on the plain shape of `2^25` words `sh25`):

* **its facts** for `Compose.rpm_le_kcS` and `Compose.knowledgeSoundness_listChainU_closed128S`: Keccak-256 only
  (`hOnly_p2Setup`), `p2QS` queries (`isTotalQueryBound_p2Setup`, `p2QS_le`: below `3 · 2^24 + 2^21`), each short
  (`cost_p2Setup`), its log and value (`p2Setup_run`), and no query a label (`p2Setup_noLabel`: every query is a
  Merkle node of `64` bytes or a leaf of `512`, a label has `80`);
* **the setup opening's `OKP`** (`okp_setupOp`): with the setup's queries in the history, the word under π2's setup
  root (the proof's, which the setup fixes) is the honest encoding of the setup's table at the proof's roots
  (`extract_wiringSetup`, `honest_stackWord`); the other openings carry no stack (`p2Stk_none`);
* **SETUP** (`pi2SetupBridge`): the composed setup over `π`, logged, is the Statement's `setupTreesWith` over `π`
  (π1's trees by `UniSound.uniSetupBridge`, π2's by `UniSound.simulateQ_loggedKC_stackSetupS` at `25` variables:
  `Pi2Circuit.setupTreeWith` commits at `(layoutsOf 24).2.2.logN = 25`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local instance high] Completeness.instSampleableTypeE_completeness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack RecStatement.layoutWords

/-! ## Queries of a Merkle tree -/

section TreeQueries

/-- **A Merkle tree's query**: a node of `64` bytes or a leaf of `512`. -/
def TreeQ : KeccakCalls.Domain → Prop
  | .inl x => x.length = 64 ∨ x.length = 512
  | .inr _ => True

theorem allQT_mapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) :
    ∀ l : List β, (∀ a ∈ l, AllQueriesSatisfy (f a) TreeQ) → AllQueriesSatisfy (l.mapM f) TreeQ
  | [], _ => by rw [List.mapM_nil]; trivial
  | a :: l, h => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (h a List.mem_cons_self) fun _ ↦
      allQueriesSatisfy_bind (allQT_mapM f l fun a' ha' ↦ h a' (List.mem_cons_of_mem _ ha')) fun _ ↦ trivial

theorem allQT_arrayMapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) (xs : Array β)
    (h : ∀ a ∈ xs.toList, AllQueriesSatisfy (f a) TreeQ) : AllQueriesSatisfy (xs.mapM f) TreeQ := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (allQT_mapM f _ h) fun _ ↦ trivial

theorem allQT_parentsM (level : Array Digest) (n : ℕ) :
    AllQueriesSatisfy (LeanVM.Prover.parentsWithHash callKeccak256 level n) TreeQ :=
  allQT_arrayMapM _ _ fun _ _ ↦ (allQueriesSatisfy_query_iff (spec := KeccakCalls) (.inl _) TreeQ).mpr
    (Or.inl (by rw [List.length_append, digestBytes_length, digestBytes_length]))

theorem allQT_levelsM : ∀ (k : ℕ) (level : Array Digest),
    AllQueriesSatisfy (LeanVM.Prover.levelsWithHash callKeccak256 k level) TreeQ
  | 0, _ => trivial
  | k + 1, level => by
    simp only [LeanVM.Prover.levelsWithHash]
    exact allQueriesSatisfy_bind (allQT_parentsM _ _) fun _ ↦
      allQueriesSatisfy_bind (allQT_levelsM k _) fun _ ↦ trivial

/-- **A stack's setup asks only Merkle trees' queries.** -/
theorem allQT_stackSetupS (S : WhirShape) (q₀ : Column S.L.logN) : AllQueriesSatisfy (stackSetupS S q₀) TreeQ := by
  unfold stackSetupS wiringSetup LeanVM.Prover.buildTreeWithHash
  rw [map_eq_bind_pure_comp]
  refine allQueriesSatisfy_bind (allQueriesSatisfy_bind
    (allQT_arrayMapM _ _ fun i _ ↦ (allQueriesSatisfy_query_iff (spec := KeccakCalls) (.inl _) TreeQ).mpr
      (Or.inr ?_)) fun _ ↦ allQueriesSatisfy_bind (allQT_levelsM _ _) fun _ ↦ trivial) fun _ ↦ trivial
  rw [LeanVM.Rpm.flatMap_kBytes_length, LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q₀ i]
  decide

/-- **A run's log holds only queries every query of the computation satisfies.** -/
theorem tableQueryLog_allQ (P : KeccakCalls.Domain → Prop) {α : Type} (oa : OracleComp KeccakCalls α)
    (h : AllQueriesSatisfy oa P) (T : KTable) : ∀ q ∈ (tableQueryLog oa T).map Sigma.fst, P q := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro q hq
    rw [tableQueryLog_query_bind, List.map_cons] at hq
    obtain ⟨h1, h2⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact ih _ (h2 _) q hq

end TreeQueries

/-! ## The setup's facts -/

section Setup

variable (D : RecDeployment) (hs : UniSound.UniShapes D.pi1)

/-- **The setup's Keccak-256 queries**: π1's three trees', then π2's tree's (`2^21`). -/
def p2QS : ℕ := UniSound.setupQS (D := D.pi1) + 2 ^ (WhirBridge.rootHeight 25 WhirBridge.logInvRate + 1)

theorem hOnly_p2Setup : LeanVM.Rpm.HOnly (p2Setup D hs) := by
  unfold p2Setup
  exact (UniSound.hOnly_setupK3 hs _ _ _).bind fun _ ↦ (UniSound.hOnly_stackSetupS _ _).bind fun _ ↦ trivial

theorem isTotalQueryBound_p2Setup : IsTotalQueryBound (p2Setup D hs) (p2QS D) := by
  unfold p2Setup
  have h := isTotalQueryBound_bind (UniSound.isTotalQueryBound_setupK3 hs (UniSound.colF D.pi1)
    (UniSound.colA D.pi1) (UniSound.colB D.pi1)) fun r ↦ isTotalQueryBound_bind
      (ob := fun r2 ↦ (pure (r, r2) : OracleComp KeccakCalls SOut)) (n₂ := 0)
      (isTotalQueryBound_stackSetupS sh25 (setupCol D ⟨UniSound.rootsOfS r, default⟩)) fun _ ↦ trivial
  refine IsTotalQueryBound.mono h ?_
  dsimp only [p2QS, sh25, UniSound.plainShape, WhirShape.large, UniSound.plainL, WhirBridge.Layout.new]
  omega

include hs in
theorem p2QS_le : p2QS D ≤ 3 * 2 ^ 24 + 2 ^ 21 := by
  have h := UniSound.setupQS_le D.pi1 hs
  have h21 : 2 ^ (WhirBridge.rootHeight 25 WhirBridge.logInvRate + 1) = 2 ^ 21 := by
    unfold WhirBridge.rootHeight WhirBridge.laneFold WhirBridge.logInvRate
    rfl
  unfold p2QS
  omega

theorem allQ_p2Setup : AllQueriesSatisfy (p2Setup D hs) LeanVM.Rpm.Short := by
  unfold p2Setup
  exact allQueriesSatisfy_bind (UniSound.allQ_setupK3 hs _ _ _) fun _ ↦
    allQueriesSatisfy_bind (UniSound.allQ_stackSetupS _ _) fun _ ↦ LeanVM.Rpm.allQ_pure _

theorem cost_p2Setup : Common.QueryCostAtMost (p2Setup D hs) LeanVM.Rpm.hashBlocks (p2QS D * 2 ^ 32) :=
  LeanVM.Rpm.isWeightBound_of_isTotalQueryBound LeanVM.Rpm.hashBlocks (2 ^ 32) (isTotalQueryBound_p2Setup D hs)
    ((allQ_p2Setup D hs).mono fun _ h ↦ LeanVM.Rpm.hashBlocks_le_of_short h)

/-- **The setup's run**: π1's three trees' log, then π2's tree's; its value π1's roots and π2's root. -/
theorem p2Setup_run (T : KTable) :
    tableQueryLog (p2Setup D hs) T = tableQueryLog (UniSound.uSetup D.pi1 hs) T ++
        tableQueryLog (stackSetupS sh25 (setupCol D
          ⟨UniSound.rootsOfS (evalWithAnswerFn (QueryImpl.ofFn T) (UniSound.uSetup D.pi1 hs)), default⟩)) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (p2Setup D hs) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (UniSound.uSetup D.pi1 hs),
          evalWithAnswerFn (QueryImpl.ofFn T) (stackSetupS sh25 (setupCol D
            ⟨UniSound.rootsOfS (evalWithAnswerFn (QueryImpl.ofFn T) (UniSound.uSetup D.pi1 hs)), default⟩))) := by
  constructor
  · simp only [p2Setup, tableQueryLog_bind, tableQueryLog_pure, List.append_nil]
  · simp only [p2Setup, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

theorem allQT_p2Setup : AllQueriesSatisfy (p2Setup D hs) TreeQ := by
  unfold p2Setup UniSound.uSetup UniSound.setupK3
  exact allQueriesSatisfy_bind (allQueriesSatisfy_bind (allQT_stackSetupS _ _) fun _ ↦
    allQueriesSatisfy_bind (allQT_stackSetupS _ _) fun _ ↦ allQueriesSatisfy_bind (allQT_stackSetupS _ _)
      fun _ ↦ trivial) fun _ ↦ allQueriesSatisfy_bind (allQT_stackSetupS _ _) fun _ ↦ trivial

/-- **No query of the setup is a label**: its queries are Merkle nodes (`64` bytes) and leaves (`512`), a label
`name ‖ iv ‖ input` has `80`. -/
theorem p2Setup_noLabel : ∀ (T : KTable) (x : List UInt8),
    Sum.inl x ∈ (tableQueryLog (p2Setup D hs) T).map Sigma.fst → ∀ s, x ≠ pi2Spec.label s := by
  intro T x hx s hxs
  have h := tableQueryLog_allQ TreeQ (p2Setup D hs) (allQT_p2Setup D hs) T _ hx
  have hl : x.length = 80 := by rw [hxs]; exact p2Label_length s
  simp only [TreeQ] at h
  omega

end Setup

/-! ## The setup's opening -/

section Opening

variable (D : RecDeployment) (hs : UniSound.UniShapes D.pi1)

/-- **The setup's opening carries the setup's table at the proof's roots.** -/
theorem p2Stk_setup :
    p2Stk D (⟨shS, clS, fun π => π.proof.setup, .setup (fun π => π.roots.2) (col0 _)⟩ : WhirOp P2Pf E Stk) =
      some fun π => setupCol D (p2Roots π) := by
  rfl

/-- **The other openings carry none** (their stacks are not of `2^25` words). -/
theorem p2Stk_none (o : WhirOp P2Pf E Stk) (h : o.S.L.logN ≠ 25) : p2Stk D o = none := by
  unfold p2Stk
  split
  · next h' => exact absurd h' h
  · rfl

theorem sh1_logN (k : ℕ) : (sh1 k).L.logN = pi1Vars k := rfl

theorem shW_logN : shW.L.logN = 24 := rfl

theorem shS_logN : shS.L.logN = 25 := rfl

theorem shQ_logN : shQ.L.logN = 28 := rfl

/-- **The setup's table at a proof's roots reads only π1's roots.** -/
theorem setupCol_congr (r r' : RecSetupRoots) (h : r.pi1 = r'.pi1) : setupCol D r = setupCol D r' := by
  unfold setupCol setupStackAt
  rw [h]

/-- **The setup's opening's `OKP`**: with the setup's queries in the history and its answers injective there, the word
under π2's setup root (the proof's, the setup's output) is the honest encoding of the setup's table at the proof's
roots. -/
theorem okp_setupOp :
    WhirOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D)
      (⟨shS, clS, fun π => π.proof.setup, .setup (fun π => π.roots.2) (col0 _)⟩ : WhirOp P2Pf E Stk) := by
  intro f hf T H p hsub hinj
  rw [p2Stk_setup] at hf
  cases Option.some.inj hf
  obtain ⟨hl, he⟩ := p2Setup_run D hs T
  set r := evalWithAnswerFn (QueryImpl.ofFn T) (UniSound.uSetup D.pi1 hs) with hr
  set q := setupCol D ⟨UniSound.rootsOfS r, default⟩ with hq
  have hsub' : ∀ x, Sum.inl x ∈ (tableQueryLog (stackSetupS sh25 q) T).map Sigma.fst → x ∈ H := by
    intro x hx
    refine hsub x ?_
    rw [hl, List.map_append]
    exact List.mem_append_right _ hx
  have hc : setupCol D (p2Roots (p2Fix (evalWithAnswerFn (QueryImpl.ofFn T) (p2Setup D hs)) p)) = q := by
    rw [he]
    exact setupCol_congr D _ _ rfl
  refine ⟨LeanVM.Protocol.Whir.Complete.stackWord 25 q, ?_, fun v hv => ?_⟩
  · show HonestWord 25 WhirBridge.logInvRate _
      (setupCol D (p2Roots (p2Fix (evalWithAnswerFn (QueryImpl.ofFn T) (p2Setup D hs)) p)))
    rw [hc]
    exact honest_stackWord 25 WhirBridge.logInvRate q
  · show Rom.extract (ansOf H (viewT T))
      (ofB (p2Fix (evalWithAnswerFn (QueryImpl.ofFn T) (p2Setup D hs)) p).roots.2)
      (rootHeight shS.L.logN shS.R) (2 ^ laneFold) v = _
    rw [he]
    exact extract_wiringSetup _ _ _ (LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q) T H hsub' hinj v hv

end Opening

/-! ## The setup bridge -/

/-- `layouts(24)`'s setup layout has `2^25` words. -/
theorem layoutsOf_setup_logN : (layoutsOf 24).2.2.logN = 25 := by decide

/-- **SETUP**: the composed setup over `π`, logged, is the Statement's `setupTreesWith` over `π` (π2's circuit the
real deployment's at every IV, π1's setup stack of fewer than `256` variables). -/
theorem pi2SetupBridge (D : RecDeployment) (hD : RecDeployment.Real D) (hs : UniSound.UniShapes D.pi1)
    (hv : (UniStatement.setupLayout D.pi1.shape).vars < 256) : Pi2SetupBridge D hs := by
  have e1 := UniSound.uniSetupBridge D.pi1 hs hv
  unfold UniSound.UniSetupBridge at e1
  have e2 : ∀ a : Array K, simulateQ keccakCallsOverQueryPermutation
      (loggedKC (stackSetupS sh25 (UniSound.colOf a 25))) =
        (fun t : LeanVM.Prover.Tree => (toB t.root, Soundness.treeTr t)) <$>
          PcsQuotient.commitWith Common.queryPermutation 25 a :=
    fun a => UniSound.simulateQ_loggedKC_stackSetupS 25 (by norm_num) (by norm_num) a
  have hc : ∀ t1 : UniStatement.SetupTrees, (D.circuitAt t1.roots).setupTreeWith Common.queryPermutation =
      PcsQuotient.commitWith Common.queryPermutation 25 (D.circuitAt t1.roots).setupStack := by
    intro t1
    unfold Pi2Circuit.setupTreeWith
    rw [RecDeployment.circuitAt, hD.1, show (Data.circuit.logN : ℕ) = 24 from rfl, layoutsOf_setup_logN]
  unfold Pi2SetupBridge p2Setup setupCol
  simp only [UniSound.loggedKC_bind, UniSound.loggedKC_pure, simulateQ_bind, simulateQ_map, simulateQ_pure, e1, e2]
  unfold RecDeployment.setupTreesWith
  simp only [map_bind, map_pure, bind_map_left, hc]
  refine bind_congr fun t1 => ?_
  rw [UniSound.rootsOfS_rootsB]
  refine bind_congr fun t2 => ?_
  simp only [setupTr2, RecSetupTrees.evaluations, List.map_append, List.append_nil, UniSound.setupTr,
    Soundness.treeTr]
  rfl

end RecCompose

/-- info: 'RecCompose.okp_setupOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.okp_setupOp

/-- info: 'RecCompose.pi2SetupBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2SetupBridge

/-- info: 'RecCompose.p2Setup_noLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.p2Setup_noLabel
