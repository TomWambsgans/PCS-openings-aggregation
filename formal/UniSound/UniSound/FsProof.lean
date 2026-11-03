-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The framework is
-- `formal/Compose/Compose/ListChainU.lean`, `ListChainUDoom.lean`, `ListChainKRpmS.lean`; the setup's
-- facts follow `formal/Compose/Compose/Rpm.lean`'s (`hOnly_stackSetup`, `allQ_stackSetup`,
-- `cost_stackSetup`) and `ListChainKDoom.lean`'s `whirOp_ok_stack`.
import UniSound.FsOps

/-!
# The Fiat–Shamir layer, from the composed game

**`fsLayer_of_game`**: `FsLayer D Fl nV V C` from one named hypothesis, **`UniGameLe`** (the
univariate experiment is dominated by `ListChainKRpmS.lean`'s random-permutation game of the chain
over the univariate encoding, its five openings and its setup), and the deployment's numbers
(`UniNumbers`: the layout words' variables `24 … 28`, the chain's `< 2^10` queries, the verifier's
`< 2^80` calls of `π`). The proof:

* the setup is the three trees of the setup's stack `F` and Flock's `A0`, `B0` (`setupK3`, each
  `stackSetupS` of its plain shape), the proof records their roots (`uFix`);
* the openings (`uniOps`), the decoders (`uniTc`), the check (`uniCheck`), `good` (`uniGood`,
  `uniGoodS`), the chain (`uniSpec`) and the protocol (`liftPiop`) are `FsOps.lean`'s and
  `FsChain.lean`'s; their facts are proved here: the openings match (`hok_uni`: the round openings
  by `whirOp_ok_tableCode`, the setup's by its trees, `whirOp_ok_tree`), every round with a root is
  opened (`hcov_uni`), the setup's stacks satisfy their claims (`hS_uni`, the plain layout's table
  is its stack, `plainL_table`), the last link (`hlink_uni`, from `FsLayer`'s);
* `knowledgeSoundness_listChainU_closed_rpm`, then the bound (`le_uniBound`): every doom term at
  most `openingBoundAt 10122 N`, the lists at most `largeList ≤ 9952`, two roots, the tag's
  `2^-128` and seven references an input.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The plain layout's table is its stack -/

theorem newBlocks_plain (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) :
    WhirBridge.Layout.newBlocks v v [(0, 2 ^ v)] = List.range 64 := by
  interval_cases v <;> decide +kernel

theorem toBlocks_plainL (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) :
    (plainL v).toBlocks.blocks = List.range 64 := by
  simp only [WhirBridge.Layout.toBlocks, plainL, WhirBridge.Layout.new, newBlocks_plain v h1 h2,
    List.map_map]
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_id _)

theorem plainL_table (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) (q : LeanVM.Protocol.Column v) (t : ℕ)
    (ht : t < 2 ^ v) : (plainL v).table q t = q.values.getD t 0 := by
  have hb := toBlocks_plainL v h1 h2
  have hl : 2 ^ v = 2 ^ (v - laneFold) * 64 := by
    rw [show (64 : ℕ) = 2 ^ laneFold from rfl, ← pow_add, Nat.sub_add_cancel (by
      unfold laneFold
      omega)]
  have hlt : t / 2 ^ (v - laneFold) < 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), mul_comm, ← hl]
    exact ht
  show (plainL v).toBlocks.table q t = _
  unfold WhirBridge.Blocks.table WhirBridge.Blocks.lanes WhirBridge.Blocks.logLane
  rw [hb, List.length_range]
  have hc : ∀ l ∈ Finset.range 64, ((if (List.range 64).getD l 0 = t / 2 ^ (v - laneFold) then
      q.values.getD (t % 2 ^ (v - laneFold) + 2 ^ (v - laneFold) * l) 0 else 0 : K)) =
      if t / 2 ^ (v - laneFold) = l then
        q.values.getD (t % 2 ^ (v - laneFold) + 2 ^ (v - laneFold) * l) 0 else 0 := by
    intro l hl'
    rw [List.getD_eq_getElem _ _ (by simpa using hl'), List.getElem_range]
    simp only [eq_comm]
  show (∑ l ∈ Finset.range 64, if (List.range 64).getD l 0 = t / 2 ^ (v - laneFold) then
      q.values.getD (t % 2 ^ (v - laneFold) + 2 ^ (v - laneFold) * l) 0 else 0) = _
  rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hlt),
    Nat.mod_add_div]

/-- **A plain layout's evaluation of an array's column is the array's multilinear extension.** -/
theorem plain_tableEval (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) (a : Array K) (p : List E)
    (hp : p.length = v) : (plainL v).tableEval (colOf a v) p = mleArr a v p := by
  refine (tabEval_tabOf (plainL v) (colOf a v) p).symm.trans ?_
  rw [tabEval_rdTab _ _ _ hp]
  unfold mleStk mleArr
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 2
  show rdTab (tabOf (plainL v) (colOf a v)) x.val = _
  have hx : x.val < 2 ^ (plainL v).vars := x.isLt
  have hx' : x.val < 2 ^ v := x.isLt
  simp only [rdTab, hx, ↓reduceDIte, tabOf, Vector.getElem_ofFn]
  rw [plainL_table v h1 h2 _ _ hx']
  simp [colOf, Vector.getD, hx']

/-! ## The setup -/

section Setup

theorem hOnly_stackSetupS (S : WhirShape) (q₀ : LeanVM.Protocol.Column S.L.logN) :
    LeanVM.Rpm.HOnly (stackSetupS S q₀) := by
  unfold stackSetupS wiringSetup
  rw [map_eq_bind_pure_comp]
  exact (LeanVM.Rpm.hOnly_buildTreeM _ _).bind fun _ => trivial

theorem allQ_stackSetupS (S : WhirShape) (q₀ : LeanVM.Protocol.Column S.L.logN) :
    AllQueriesSatisfy (stackSetupS S q₀) LeanVM.Rpm.Short := by
  unfold stackSetupS wiringSetup LeanVM.Prover.buildTreeWithHash
  rw [map_eq_bind_pure_comp]
  refine allQueriesSatisfy_bind (allQueriesSatisfy_bind (LeanVM.Rpm.allQ_leafDigestsM _ ?_)
    fun _ => allQueriesSatisfy_bind (LeanVM.Rpm.allQ_levelsM _ _) fun _ =>
      LeanVM.Rpm.allQ_pure _) fun _ => LeanVM.Rpm.allQ_pure _
  intro p
  rw [LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q₀ p]
  decide

variable {D : Deployment} (hs : UniShapes D)

/-- **The setup**: the trees of the setup's stack `F` and of Flock's `A0`, `B0` (each the Merkle
tree of its stack's encoding on its plain shape), their roots. -/
noncomputable def setupK3 (qF : LeanVM.Protocol.Column (wv D 2))
    (qA : LeanVM.Protocol.Column (wv D 3)) (qB : LeanVM.Protocol.Column (wv D 4)) :
    OracleComp KeccakCalls (Bytes32 × Bytes32 × Bytes32) :=
  stackSetupS (shapeK hs 2 (by decide)) qF >>= fun f =>
    stackSetupS (shapeK hs 3 (by decide)) qA >>= fun a =>
      stackSetupS (shapeK hs 4 (by decide)) qB >>= fun b => pure (f, a, b)

/-- **The proof with the setup's roots** (`fix`). -/
def uFix (s : Bytes32 × Bytes32 × Bytes32) (π : UPf) : UPf :=
  { π with roots := ⟨ofB s.1, ofB s.2.1, ofB s.2.2⟩ }

/-- The setup's Keccak-256 queries. -/
def setupQS : ℕ :=
  2 ^ (rootHeight (wv D 2) logInvRate + 1) + 2 ^ (rootHeight (wv D 3) logInvRate + 1) +
    2 ^ (rootHeight (wv D 4) logInvRate + 1)

variable (qF : LeanVM.Protocol.Column (wv D 2)) (qA : LeanVM.Protocol.Column (wv D 3))
  (qB : LeanVM.Protocol.Column (wv D 4))

theorem hOnly_setupK3 : LeanVM.Rpm.HOnly (setupK3 hs qF qA qB) :=
  (hOnly_stackSetupS _ _).bind fun _ => (hOnly_stackSetupS _ _).bind fun _ =>
    (hOnly_stackSetupS _ _).bind fun _ => trivial

theorem isTotalQueryBound_setupK3 : IsTotalQueryBound (setupK3 hs qF qA qB) (setupQS (D := D)) := by
  have h := isTotalQueryBound_bind (isTotalQueryBound_stackSetupS (shapeK hs 2 (by decide)) qF)
    fun f => isTotalQueryBound_bind (isTotalQueryBound_stackSetupS (shapeK hs 3 (by decide)) qA)
      fun a => isTotalQueryBound_bind
        (ob := fun b => (pure (f, a, b) : OracleComp KeccakCalls (Bytes32 × Bytes32 × Bytes32)))
        (n₂ := 0) (isTotalQueryBound_stackSetupS (shapeK hs 4 (by decide)) qB) fun _ => trivial
  refine IsTotalQueryBound.mono h ?_
  dsimp only [shapeK, plainShape, WhirShape.large, plainL, WhirBridge.Layout.new, setupQS]
  omega

theorem allQ_setupK3 : AllQueriesSatisfy (setupK3 hs qF qA qB) LeanVM.Rpm.Short :=
  allQueriesSatisfy_bind (allQ_stackSetupS _ _) fun _ =>
    allQueriesSatisfy_bind (allQ_stackSetupS _ _) fun _ =>
      allQueriesSatisfy_bind (allQ_stackSetupS _ _) fun _ => LeanVM.Rpm.allQ_pure _

theorem cost_setupK3 : Common.QueryCostAtMost (setupK3 hs qF qA qB) LeanVM.Rpm.hashBlocks
    (setupQS (D := D) * 2 ^ 32) :=
  LeanVM.Rpm.isWeightBound_of_isTotalQueryBound LeanVM.Rpm.hashBlocks (2 ^ 32)
    (isTotalQueryBound_setupK3 hs qF qA qB)
    ((allQ_setupK3 hs qF qA qB).mono fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)

theorem setupK3_run (T : KTable) :
    tableQueryLog (setupK3 hs qF qA qB) T =
        tableQueryLog (stackSetupS (shapeK hs 2 (by decide)) qF) T ++
          (tableQueryLog (stackSetupS (shapeK hs 3 (by decide)) qA) T ++
            tableQueryLog (stackSetupS (shapeK hs 4 (by decide)) qB) T) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (setupK3 hs qF qA qB) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (stackSetupS (shapeK hs 2 (by decide)) qF),
          evalWithAnswerFn (QueryImpl.ofFn T) (stackSetupS (shapeK hs 3 (by decide)) qA),
          evalWithAnswerFn (QueryImpl.ofFn T) (stackSetupS (shapeK hs 4 (by decide)) qB)) := by
  constructor
  · simp [setupK3, tableQueryLog_bind, tableQueryLog_map]
  · simp [setupK3, evalWithAnswerFn_bind, evalWithAnswerFn_map]

end Setup

/-- **A setup opening of one of the setup's trees**: `WhirOp.OK` holds when the setup's log holds
the tree's and the proof the setup fixes carries the tree's root. -/
theorem whirOp_ok_tree {σ : Type} (S : WhirShape) (cl : UPf → List (List E) → Stmt S.L.stacking)
    (prf : UPf → Proof) (root : UPf → Bytes32) (q₀ : LeanVM.Protocol.Column S.L.logN)
    (tc : ℕ → TableCode Stk) (good : ℕ → UPf → List (List E) → Option Stk → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → UPf → UPf)
    (hlog : ∀ T x, Sum.inl x ∈ (tableQueryLog (stackSetupS S q₀) T).map Sigma.fst →
      Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst)
    (hroot : ∀ T p, root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p) =
      evalWithAnswerFn (QueryImpl.ofFn T) (stackSetupS S q₀)) :
    WhirOp.OK tc good setup fix (⟨S, cl, prf, .setup root q₀⟩ : WhirOp UPf E Stk) := by
  refine ⟨LeanVM.Protocol.Whir.Complete.stackWord S.L.logN q₀, honest_stackWord _ _ q₀,
    fun T H p hsub hinj v hv => ?_⟩
  show Rom.extract (ansOf H (viewT T))
    (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)))
    (rootHeight S.L.logN S.R) (2 ^ laneFold) v = _
  rw [hroot]
  exact extract_wiringSetup _ _ _ (LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q₀) T H
    (fun x hx => hsub x (hlog T x hx)) hinj v hv

/-! ## The composition's facts -/

section Facts

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)
  (hs : UniShapes D)

/-- The honest columns: the setup's stack, `A0`, `B0`. -/
def colF : LeanVM.Protocol.Column (wv D 2) := colOf (setupStack D.prog D.shape) (wv D 2)
/-- `A0`'s column. -/
def colA : LeanVM.Protocol.Column (wv D 3) := colOf (flockMatrixStack true) (wv D 3)
/-- `B0`'s column. -/
def colB : LeanVM.Protocol.Column (wv D 4) := colOf (flockMatrixStack false) (wv D 4)

/-- The five openings at the honest columns. -/
noncomputable abbrev uOps : List (WhirOp UPf E Stk) :=
  uniOps Fl nV V C hs (colF D) (colA D) (colB D)

/-- The setup at the honest columns. -/
noncomputable abbrev uSetup : OracleComp KeccakCalls (Bytes32 × Bytes32 × Bytes32) :=
  setupK3 hs (colF D) (colA D) (colB D)

/-- The chain of the main line's rounds. -/
noncomputable abbrev uSpec : ChainSpecU E FSt := uniSpec (uRounds Fl nV V)

theorem hcov_uni : ∀ i < (uSpec Fl nV V).K.rounds.length, ((uSpec Fl nV V).K.spec i).root →
    ∃ o ∈ uOps D Fl nV V C hs, ∃ rd, o.tgt = .round i rd := by
  intro i _ hr
  rcases root_uniRounds Fl.prog.rounds Fl.rounds_root nV V i hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, _, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, _, rfl⟩

theorem hok_uni : ∀ o ∈ uOps D Fl nV V C hs,
    WhirOp.OK (uniTc hs) (uniGood D Fl nV V C) (uSetup D hs) uFix o := by
  intro o ho
  simp only [uOps, uniOps, List.mem_cons, List.mem_nil_iff, or_false] at ho
  have hlog : ∀ k (hk : k = 2 ∨ k = 3 ∨ k = 4) (S : WhirShape) (q : LeanVM.Protocol.Column S.L.logN),
      (k = 2 → S = shapeK hs 2 (by decide) ∧ HEq q (colF D)) →
      (k = 3 → S = shapeK hs 3 (by decide) ∧ HEq q (colA D)) →
      (k = 4 → S = shapeK hs 4 (by decide) ∧ HEq q (colB D)) →
      ∀ T x, Sum.inl x ∈ (tableQueryLog (stackSetupS S q) T).map Sigma.fst →
        Sum.inl x ∈ (tableQueryLog (uSetup D hs) T).map Sigma.fst := by
    intro k hk S q h2 h3 h4 T x hx
    rw [(setupK3_run hs _ _ _ T).1]
    simp only [List.map_append, List.mem_append]
    rcases hk with rfl | rfl | rfl
    · obtain ⟨rfl, hq⟩ := h2 rfl
      cases hq
      exact Or.inl hx
    · obtain ⟨rfl, hq⟩ := h3 rfl
      cases hq
      exact Or.inr (Or.inl hx)
    · obtain ⟨rfl, hq⟩ := h4 rfl
      cases hq
      exact Or.inr (Or.inr hx)
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · refine whirOp_ok_tableCode _ _ _ 0 rdTab (uniTc hs) (by unfold uniTc; rw [ite_eq_left rfl]) _
      (fun π ch t h => ?_) _ _
    rw [uniGood, ite_eq_left rfl]
    exact ⟨rdTab t, rfl, fun cl hcl =>
      (tabEval_rdTab _ t _ ((cl1 D Fl nV V C π ch).wide cl hcl)).symm.trans (h cl hcl)⟩
  · refine whirOp_ok_tableCode _ _ _ (Fl.prog.rounds.length + 1) rdTab (uniTc hs)
      (by unfold uniTc; rw [ite_eq_right (Nat.succ_ne_zero _)]) _ (fun π ch t h => ?_) _ _
    rw [uniGood, ite_eq_right (Nat.succ_ne_zero _), ite_eq_left rfl]
    exact ⟨rdTab t, rfl, fun cl hcl =>
      (tabEval_rdTab _ t _ ((cl2 D Fl nV V C π ch).wide cl hcl)).symm.trans (h cl hcl)⟩
  · refine whirOp_ok_tree _ _ _ _ _ _ _ _ _ (hlog 2 (Or.inl rfl) _ _ (fun _ => ⟨rfl, HEq.rfl⟩)
      (by omega) (by omega)) fun T p => ?_
    simp only [uFix, (setupK3_run hs _ _ _ T).2]
    exact LeanVM.Rpm.digestToRpm_ofRpm _
  · refine whirOp_ok_tree _ _ _ _ _ _ _ _ _ (hlog 3 (Or.inr (Or.inl rfl)) _ _ (by omega)
      (fun _ => ⟨rfl, HEq.rfl⟩) (by omega)) fun T p => ?_
    simp only [uFix, (setupK3_run hs _ _ _ T).2]
    exact LeanVM.Rpm.digestToRpm_ofRpm _
  · refine whirOp_ok_tree _ _ _ _ _ _ _ _ _ (hlog 4 (Or.inr (Or.inr rfl)) _ _ (by omega)
      (by omega) (fun _ => ⟨rfl, HEq.rfl⟩)) fun T p => ?_
    simp only [uFix, (setupK3_run hs _ _ _ T).2]
    exact LeanVM.Rpm.digestToRpm_ofRpm _

theorem hS_uni (π : UPf) (ch : List (List E))
    (h : ∀ o ∈ uOps D Fl nV V C hs, WhirOp.SetupHolds o π ch) : uniGoodS D Fl nV V C π ch := by
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have h4 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h5 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  refine ⟨fun cl hcl => ?_, fun cl hcl => ?_, fun cl hcl => ?_⟩
  · have := h3 cl hcl
    rw [← this]
    exact (plain_tableEval _ (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _ _
      ((cl3 D Fl nV V C π ch).wide cl hcl)).symm
  · have := h4 cl hcl
    rw [← this]
    exact (plain_tableEval _ (hs.lo 3 (by decide)) (hs.hi 3 (by decide)) _ _
      ((cl4 D Fl nV V C π ch).wide cl hcl)).symm
  · have := h5 cl hcl
    rw [← this]
    exact (plain_tableEval _ (hs.lo 4 (by decide)) (hs.hi 4 (by decide)) _ _
      ((cl5 D Fl nV V C π ch).wide cl hcl)).symm

end Facts

end UniSound
