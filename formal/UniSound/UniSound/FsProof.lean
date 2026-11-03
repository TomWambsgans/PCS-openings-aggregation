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
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

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

/-! ## The bound -/

theorem openingBoundAt_mono {QV QA QV' QA' : ℕ} (h : QA + QV ≤ QA' + QV') :
    openingBoundAt QV QA ≤ openingBoundAt QV' QA' := by
  unfold openingBoundAt
  exact mul_le_mul' (Nat.cast_le.mpr h) (add_le_add le_rfl
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left 5 h)) _))

theorem doomSum_le {Pf F M : Type} (b : ℕ) (B : ℝ≥0∞) : ∀ (ops : List (WhirOp Pf F M)) (X : ℕ),
    (∀ o ∈ ops, ∀ QA, QA + o.S.QO ≤ b → o.S.bnd QA ≤ B) →
      X + (ops.map fun o => o.S.QO).sum ≤ b → doomSum ops X ≤ ops.length * B
  | [], _, _, _ => by simp [doomSum]
  | o :: os, X, h, hX => by
    simp only [List.map_cons, List.sum_cons] at hX
    have h1 := h o List.mem_cons_self X (by omega)
    have h2 := doomSum_le b B os (X + o.S.QO) (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
      (by omega)
    calc doomSum (o :: os) X = o.S.bnd X + doomSum os (X + o.S.QO) := rfl
      _ ≤ B + os.length * B := add_le_add h1 h2
      _ = ((o :: os).length : ℝ≥0∞) * B := by
        rw [List.length_cons, Nat.cast_succ]
        ring

theorem facL_le_pow {M : Type} (C : ℕ → ListCommit M) (b : ℕ) (hb : ∀ k, (C k).bound ≤ b) :
    ∀ (i : ℕ) (rs : List RoundSpec), facL C i rs ≤ b ^ (rs.countP fun r => r.root)
  | _, [] => by simp [facL]
  | i, s :: rs => by
    have ih := facL_le_pow C b hb (i + 1) rs
    cases hs : s.root
    · simp only [facL, List.countP_cons, hs, Bool.false_eq_true, ↓reduceIte, one_mul,
        Nat.add_zero]
      exact ih
    · simp only [facL, List.countP_cons, hs, ↓reduceIte, pow_succ]
      exact (Nat.mul_le_mul (hb i) ih).trans (le_of_eq (mul_comm _ _))

theorem countP_root_uniRounds (fr : List RoundSpec) (hfr : ∀ r ∈ fr, r.root = false) (nV V : ℕ) :
    (uniRounds fr nV V).countP (fun r => r.root) = 2 := by
  have h0 : fr.countP (fun r => r.root) = 0 :=
    List.countP_eq_zero.mpr fun r hr => by simp [hfr r hr]
  simp [uniRounds, List.countP_append, h0]

theorem uniTc_bound {D : Deployment} (hs : UniShapes D) (i : ℕ) :
    (uniTc hs i).commit.bound ≤ 9952 := by
  unfold uniTc
  split_ifs
  · exact (tableCode_bound_large (wv D 0) (wv D 0) (wv D 0) [(0, 2 ^ wv D 0)]
      (newOK_plain _ (hs.lo 0 (by decide)) (hs.hi 0 (by decide))) (hs.lo 0 (by decide))
      (hs.hi 0 (by decide)) rdTab).le.trans
      (largeList_le _ (hs.lo 0 (by decide)) (hs.hi 0 (by decide)))
  · exact (tableCode_bound_large (wv D 1) (wv D 1) (wv D 1) [(0, 2 ^ wv D 1)]
      (newOK_plain _ (hs.lo 1 (by decide)) (hs.hi 1 (by decide))) (hs.lo 1 (by decide))
      (hs.hi 1 (by decide)) rdTab).le.trans
      (largeList_le _ (hs.lo 1 (by decide)) (hs.hi 1 (by decide)))

/-- **The composed bound is at most `uniBound`**: the doom terms at most `openingBoundAt 10122 N`,
the list term at most `9952² e`, the tag's `2^-128`, at most `8 N` references a query, the
permutation's calls below `2^81 + Q`. -/
theorem le_uniBound (e : ℝ≥0∞) (Q QS nQ SQO nRf : ℕ) (hQS : QS ≤ 3 * 2 ^ 24) (hnQ : nQ ≤ 2 ^ 10)
    (hSQO : SQO ≤ 5 * 10122) (hr : nRf ≤ 6) (d m t : ℝ≥0∞)
    (hd : d ≤ 5 * openingBoundAt 10122 (uniN Q)) (hm : m ≤ ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e)
    (ht : t = ((256 ^ 16 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    d + ((QS + (QS + (Q + 8)) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + t + (((nRf + 2) * (QS + (QS + (Q + 8)) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ uniBound e Q := by
  unfold uniBound
  have hN : QS + (QS + (Q + 8)) + nQ + SQO ≤ uniN Q := by
    unfold uniN
    have : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
    have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
    have : (2 : ℕ) ^ 10 = 1024 := by norm_num
    omega
  refine add_le_add (add_le_add hd (mul_le_mul' (Nat.cast_le.mpr hN) ?_)) ?_
  · rw [add_assoc]
    refine add_le_add hm ?_
    rw [ht, ENNReal.div_add_div_same, ← Nat.cast_add]
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
    have h7 : (nRf + 2) * (QS + (QS + (Q + 8)) + nQ + SQO) ≤ 8 * uniN Q :=
      Nat.mul_le_mul (by omega) hN
    have h256 : (256 : ℕ) ^ 16 = 2 ^ 128 := by norm_num
    rw [h256]
    exact Nat.add_le_add_left h7 _
  · rw [← Nat.cast_pow, ← Nat.cast_pow]
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.pow_le_pow_left ?_ 2)) _
    have h32 : QS * 2 ^ 32 ≤ 3 * 2 ^ 24 * 2 ^ 32 := Nat.mul_le_mul_right _ hQS
    have h81 : (3 : ℕ) * 2 ^ 24 * 2 ^ 32 + 8 + 2 ^ 80 ≤ 2 ^ 81 := by norm_num
    calc QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 = (QS * 2 ^ 32 + 8 + 2 ^ 80) + Q := by ring
      _ ≤ 2 ^ 81 + Q := Nat.add_le_add_right
          ((Nat.add_le_add_right (Nat.add_le_add_right h32 8) (2 ^ 80)).trans h81) Q

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

/-! ### The last link -/

theorem uniRounds_getD_zero (fr : List RoundSpec) (nV V : ℕ) :
    (uniRounds fr nV V).getD 0 ⟨false, 0, 0⟩ = ⟨true, 0, 5⟩ := by
  simp [uniRounds]

theorem uniRounds_getD_c2 (fr : List RoundSpec) (nV V : ℕ) :
    (uniRounds fr nV V).getD (fr.length + 1) ⟨false, 0, 0⟩ = ⟨true, 0, 0⟩ := by
  have e : uniRounds fr nV V = ([⟨true, 0, 5⟩] ++ fr) ++
      (([⟨true, 0, 0⟩, ⟨false, nV, 1⟩] : List RoundSpec) ++
        List.replicate V (⟨false, 2, 0⟩ : RoundSpec)) := by
    simp [uniRounds]
  rw [e, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem claimsOf_length_le (r : Reduced) (h : r.openings.map Prod.fst = commitments)
    (c : Commitment) : (claimsOf r c).length ≤ 1 := by
  unfold claimsOf
  generalize r.openings = l at h ⊢
  rcases l with _ | ⟨⟨c₁, o₁⟩, _ | ⟨⟨c₂, o₂⟩, _ | ⟨⟨c₃, o₃⟩, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp [commitments] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases c <;> cases o₁ <;> cases o₂ <;> cases o₃ <;> simp

theorem mem_claimsOf {r : Reduced} {o : Commitment × UniStatement.Opening} (ho : o ∈ r.openings) {pt : List E}
    {v : E} {bs : Option Combined} (hpt : o.2 = .point pt v bs) :
    (⟨pt, v⟩ : WhirBridge.Claim) ∈ claimsOf r o.1 := by
  unfold claimsOf
  refine List.mem_filterMap.mpr ⟨o, ho, ?_⟩
  show (if o.1 = o.1 then _ else none) = _
  rw [ite_eq_left rfl, hpt]

theorem wv_eq (k : ℕ) : wv D k = layoutWordVars ((layoutWords D.shape).getD k []) := by
  unfold wv
  rfl

theorem claimsHold_of (r : Reduced) (q1 q2 : Stk)
    (h1 : ∀ cl ∈ claimsOf r .c1, mleStk q1 (wv D 0) cl.point = cl.value)
    (h2 : ∀ cl ∈ claimsOf r .c2, mleStk q2 (wv D 1) cl.point = cl.value)
    (h3 : ∀ cl ∈ claimsOf r .setup,
      mleStk (fun i => (setupStack D.prog D.shape).getD i 0) (wv D 2) cl.point = cl.value)
    (h4 : ∀ cl ∈ matClaims r true, mleArr (flockMatrixStack true) (wv D 3) cl.point = cl.value)
    (h5 : ∀ cl ∈ matClaims r false, mleArr (flockMatrixStack false) (wv D 4) cl.point = cl.value) :
    ClaimsHold D r q1 q2 := by
  refine ⟨fun o ho pt v bs hpt => ?_, fun mc hmc => ⟨?_, ?_⟩⟩
  · have hm := mem_claimsOf ho hpt
    rcases hc : o.1 with _ | _ | _
    · rw [hc] at hm
      have := h1 _ hm
      rw [show wordIndex Commitment.c1 = 0 from rfl, ← wv_eq]
      exact this
    · rw [hc] at hm
      have := h2 _ hm
      rw [show wordIndex Commitment.c2 = 1 from rfl, ← wv_eq]
      exact this
    · rw [hc] at hm
      have := h3 _ hm
      rw [show wordIndex Commitment.setup = 2 from rfl, ← wv_eq]
      exact this
  · rw [← wv_eq]
    exact h4 ⟨mc.point, mc.a⟩ (by simp [matClaims, hmc])
  · rw [← wv_eq]
    exact h5 ⟨mc.point, mc.b⟩ (by simp [matClaims, hmc])

theorem matClaims_length_le (r : Reduced) (b : Bool) : (matClaims r b).length ≤ 1 := by
  unfold matClaims
  split <;> simp

theorem matClaims_point (r : Reduced) (b : Bool) (n : ℕ)
    (h : ∀ mc, r.matrices = some mc → mc.point.length = n) :
    ∀ c ∈ matClaims r b, c.point.length = n := by
  intro c hc
  unfold matClaims at hc
  split at hc
  · next mc hmc =>
    rw [List.mem_singleton] at hc
    rw [hc]
    exact h mc hmc
  · simp at hc

/-- **The composition's last link from `FsLayer`'s**: candidates good at `C1`'s and `C2`'s rounds and
`none` at the others, the setup's stacks good, and the check, make the opened transcript the one
`FsLayer`'s link reads (`openedOf`), its claims true (`ClaimsHold`). -/
theorem hlink_uni (R : RbrPiop (uRounds Fl nV V) USt Stk)
    (hFin : ∀ (s : USt) done tl c1 c2, DoneFits (uRounds Fl nV V) done → tl.length = 5 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf Fl.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch)
    (π : UPf) (ch : List (List E)) (cs : List (Option Stk)) (hc : uniCheck D Fl nV V C π ch)
    (hl : cs.length = (uSpec Fl nV V).K.rounds.length)
    (hg : ∀ i (h : i < cs.length), ((uSpec Fl nV V).K.spec i).root →
      uniGood D Fl nV V C i π ch cs[i])
    (hn : ∀ i (h : i < cs.length), ((uSpec Fl nV V).K.spec i).root = false → cs[i] = none)
    (hgS : uniGoodS D Fl nV V C π ch) :
    ∃ p m c, opened cs (uView (uRounds Fl nV V) π).2 ch = p ++ [(m, c)] ∧
      (liftPiop (uSpec Fl nV V).K R rfl).post (uView (uRounds Fl nV V) π).1 p m c := by
  obtain ⟨hdf, hzv, hwf⟩ := hc
  have hlen : cs.length = Fl.prog.rounds.length + 3 + V := by
    rw [hl]
    exact length_uniRounds _ _ _
  have h0 : 0 < cs.length := by omega
  have h1 : Fl.prog.rounds.length + 1 < cs.length := by omega
  have hs0 : ((uSpec Fl nV V).K.spec 0).root := by
    show ((uniRounds Fl.prog.rounds nV V).getD 0 ⟨false, 0, 0⟩).root = true
    rw [uniRounds_getD_zero]
  have hs1 : ((uSpec Fl nV V).K.spec (Fl.prog.rounds.length + 1)).root := by
    show ((uniRounds Fl.prog.rounds nV V).getD (Fl.prog.rounds.length + 1)
      ⟨false, 0, 0⟩).root = true
    rw [uniRounds_getD_c2]
  have g0 := hg 0 h0 hs0
  rw [uniGood, ite_eq_left rfl] at g0
  obtain ⟨q1, hq1, hc1⟩ := g0
  have g1 := hg _ h1 hs1
  rw [uniGood, ite_eq_right (Nat.succ_ne_zero _), ite_eq_left rfl] at g1
  obtain ⟨q2, hq2, hc2⟩ := g1
  have hcand : ∀ i (h : i < cs.length), cs[i] = candAt Fl.prog.rounds.length q1 q2 i := by
    intro i h
    by_cases hi0 : i = 0
    · subst hi0
      rw [hq1]
      simp [candAt]
    by_cases hi1 : i = Fl.prog.rounds.length + 1
    · subst hi1
      rw [hq2]
      simp [candAt]
    · rcases Bool.eq_false_or_eq_true ((uSpec Fl nV V).K.spec i).root with hr | hr
      · rcases root_uniRounds Fl.prog.rounds Fl.rounds_root nV V i hr with h' | h'
        · exact absurd h' hi0
        · exact absurd h' hi1
      · rw [hn i h hr]
        simp [candAt, hi0, hi1]
  have hlu : (msgsAt π.proof.stream 24 (uRounds Fl nV V)).length = (uRounds Fl nV V).length :=
    length_msgsAt _ _ _
  have hch : (msgsAt π.proof.stream 24 (uRounds Fl nV V)).length ≤ ch.length := by
    have := hdf.length_eq
    simp only [uDone, List.length_zip] at this
    omega
  have hop : opened cs (uView (uRounds Fl nV V) π).2 ch =
      openedOf Fl.prog.rounds.length q1 q2 (uDone (uRounds Fl nV V) π ch) :=
    opened_eq_openedOf _ q1 q2 _ ch cs hch (by rw [hlu]; exact hl) hcand
  obtain ⟨hwo, hw1, hw2, hw3, hwm⟩ := hwf
  have e1 : (cl1 D Fl nV V C π ch).claims = claimsOf (uOut D Fl nV V C π ch) .c1 :=
    mkStmt_claims (plainL (wv D 0)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw1
  have e2 : (cl2 D Fl nV V C π ch).claims = claimsOf (uOut D Fl nV V C π ch) .c2 :=
    mkStmt_claims (plainL (wv D 1)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw2
  have e3 : (cl3 D Fl nV V C π ch).claims = claimsOf (uOut D Fl nV V C π ch) .setup :=
    mkStmt_claims (plainL (wv D 2)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw3
  have e4 : (cl4 D Fl nV V C π ch).claims = matClaims (uOut D Fl nV V C π ch) true :=
    mkStmt_claims (plainL (wv D 3)) (extra_plainL _) _ (matClaims_length_le _ _)
      (matClaims_point _ _ _ fun mc hmc => (hwm mc hmc).1)
  have e5 : (cl5 D Fl nV V C π ch).claims = matClaims (uOut D Fl nV V C π ch) false :=
    mkStmt_claims (plainL (wv D 4)) (extra_plainL _) _ (matClaims_length_le _ _)
      (matClaims_point _ _ _ fun mc hmc => (hwm mc hmc).2)
  have hCH : ClaimsHold D (uOut D Fl nV V C π ch) q1 q2 :=
    claimsHold_of D _ q1 q2 (by rw [← e1]; exact hc1) (by rw [← e2]; exact hc2)
      (by rw [← e3]; exact hgS.1) (by rw [← e4]; exact hgS.2.1) (by rw [← e5]; exact hgS.2.2)
  obtain ⟨p, m, ch', he, hpost⟩ :=
    hFin (uSt Fl nV V π) _ _ q1 q2 hdf (length_uTail _ _) hzv hCH
  exact ⟨p, m, ch', hop.trans he, hpost⟩

/-! ### The event, the hypothesis -/

/-- **The univariate break on the composed game's outcome**: the check, the five openings accept,
and no candidate of `C1`'s root read off the transcript satisfies leanVM 42422001's relation. -/
def UniBreaksRel (z : OutK UPf E (List Bool)) : Prop :=
  uniCheck D Fl nV V C z.1.1 z.1.2.1 ∧
    (∀ k < (uOps D Fl nV V C hs).length, z.1.2.2.getD k false = true) ∧
    ∀ c ∈ extractorK (fun i => (uniTc hs i).commit) (uView (uRounds Fl nV V)) z,
      ∀ q, c = some q → ¬ Rel D (uSt Fl nV V z.1.1) q

/-- **The game bridge** (the hypothesis this file reduces `FsLayer` to): for every adversary of `Q`
calls of `π` and `π⁻¹`, one of at most `Q + 8` calls (the adversary, then the contract's IV, which
the proof the chain reads carries) breaks the composed game (`rpmGameS` of the three trees, the
chain over the univariate encoding and the five openings, the event read on the setup's log and
the Keccak-256 evaluations of its permutation transcript) at least as often as the adversary breaks
the univariate experiment. -/
def UniGameLe : Prop :=
  ∀ (A : UniAdversary) (Q : ℕ),
    (∀ roots, Common.QueryCostAtMost (A roots) Common.permutationCallCost Q) →
    ∃ A' : Bytes32 × Bytes32 × Bytes32 → OracleComp Common.RandomPermutationOracles UPf,
      (∀ s, Common.QueryCostAtMost (A' s) Common.permutationCallCost (Q + 8)) ∧
      Pr{let z ← uniSoundnessExperiment D A}[UniBreaksKnowledgeSoundness D (uniExtractor D) z] ≤
        Pr{let z ← Common.runWithRandomPermutation (rpmGameS (uSetup D hs) uFix A'
            (verU (uSpec Fl nV V) (uView (uRounds Fl nV V))
              (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs))))}[
          UniBreaksRel D Fl nV V C hs (z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))]

/-- **The deployment's numbers**: the chain's queries below `2^10`, the verifier's calls of `π`
below `2^80`. -/
structure UniNumbers : Prop where
  chain : (uSpec Fl nV V).K.nQ ≤ 2 ^ 10
  verifier : ∀ π, Common.QueryCostAtMost (verU (uSpec Fl nV V) (uView (uRounds Fl nV V))
    (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)) π) LeanVM.Rpm.hashBlocks (2 ^ 80)

theorem msgK_uView_zero (π : UPf) : ∃ r, (msgK (uView (uRounds Fl nV V)) π 0).1 = some r :=
  ⟨_, rfl⟩

theorem breaksOK_of_rel (R : RbrPiop (uRounds Fl nV V) USt Stk)
    (hpre : ∀ s c m, R.pre s [] (some c, m) → Rel D s c) (z : OutK UPf E (List Bool))
    (hz : UniBreaksRel D Fl nV V C hs z) :
    BreaksOK (uSpec Fl nV V).K (fun i => (uniTc hs i).commit) (liftPiop (uSpec Fl nV V).K R rfl)
      (uView (uRounds Fl nV V)) (uniCheck D Fl nV V C)
      (fun bs => ∀ k < (uOps D Fl nV V C hs).length, bs.getD k false = true) z := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨h1, h2, fun c hc hpre' => ?_⟩
  obtain ⟨r, hr⟩ := msgK_uView_zero Fl nV V z.1.1
  have hc' := hc
  simp only [extractorK, optC, hr, List.mem_map] at hc'
  obtain ⟨q, -, rfl⟩ := hc'
  exact h3 _ hc q rfl (hpre _ _ _ hpre')

/-! ### The numbers -/

include hs in
theorem setupQS_le : setupQS (D := D) ≤ 3 * 2 ^ 24 := by
  unfold setupQS rootHeight laneFold logInvRate
  have h2 := hs.hi 2 (by decide)
  have h3 := hs.hi 3 (by decide)
  have h4 := hs.hi 4 (by decide)
  have e2 : 2 ^ (wv D 2 - 6 + 1 + 1) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e3 : 2 ^ (wv D 3 - 6 + 1 + 1) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e4 : 2 ^ (wv D 4 - 6 + 1 + 1) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  omega

theorem sumQO_le : ((uOps D Fl nV V C hs).map fun o => o.S.QO).sum ≤ 5 * 10122 := by
  have q : ∀ k (hk : k < 5), largeQueries (wv D k) ≤ 10122 := fun k hk =>
    (largeQueries_le (wv D k) (hs.lo k hk) (hs.hi k hk)).trans_eq variantQueries_eq
  have q0 := q 0 (by decide)
  have q1 := q 1 (by decide)
  have q2 := q 2 (by decide)
  have q3 := q 3 (by decide)
  have q4 := q 4 (by decide)
  simp only [uOps, uniOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  try dsimp only [shapeK, plainShape, WhirShape.large]
  omega

theorem doom_le (Q X : ℕ) (hX : X + ((uOps D Fl nV V C hs).map fun o => o.S.QO).sum ≤ uniN Q) :
    doomSum (uOps D Fl nV V C hs) X ≤ 5 * openingBoundAt 10122 (uniN Q) := by
  refine (doomSum_le (uniN Q) (openingBoundAt 10122 (uniN Q)) _ X (fun o ho QA hQA => ?_) hX).trans
    (le_of_eq (by simp [uOps, uniOps]))
  simp only [uOps, uniOps, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [shapeK, plainShape, WhirShape.large] at hQA ⊢
    exact openingBoundAt_mono (by omega)

theorem maxErrK_uni (R : RbrPiop (uRounds Fl nV V) USt Stk) (e : ℝ≥0∞) (herr : ∀ j, R.err j ≤ e) :
    maxErrK (uSpec Fl nV V).K (fun i => (uniTc hs i).commit) (liftPiop (uSpec Fl nV V).K R rfl) ≤
      ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e := by
  unfold maxErrK
  refine Finset.sup_le fun j _ => mul_le_mul' (Nat.cast_le.mpr ?_) (herr j)
  refine (facL_le_pow _ 9952 (fun k => uniTc_bound hs k) 0 _).trans
    (Nat.pow_le_pow_right (by norm_num) ?_)
  exact (List.take_sublist _ _).countP_le.trans
    (le_of_eq (countP_root_uniRounds Fl.prog.rounds Fl.rounds_root nV V))

/-! ## The Fiat–Shamir layer -/

/-- **The Fiat–Shamir layer from the composed game**: `FsLayer` for a deployment whose five layout
words name `24 … 28` variables (`hs`), from its numbers (`UniNumbers`: the chain's `< 2^10`
queries, the verifier's `< 2^80` calls of `π`) and the game bridge (`UniGameLe`). -/
theorem fsLayer_of_game (hN : UniNumbers D Fl nV V C hs) (hG : UniGameLe D Fl nV V C hs) :
    FsLayer D Fl nV V C := by
  intro R e herr hpre hFin A Q hQ
  obtain ⟨A', hA', hle⟩ := hG A Q hQ
  have hmain := knowledgeSoundness_listChainU_closed_rpm (uSpec Fl nV V)
    (liftPiop (uSpec Fl nV V).K R rfl) (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)
    (fun i => uniTc hs i) (uniCheck D Fl nV V C) (uniGood D Fl nV V C) (uniGoodS D Fl nV V C)
    (uSetup D hs) (hOnly_setupK3 hs _ _ _) setupQS (setupQS * 2 ^ 32)
    (isTotalQueryBound_setupK3 hs _ _ _) (cost_setupK3 hs _ _ _) uFix A' (Q + 8) hA' (2 ^ 80)
    hN.verifier (hok_uni D Fl nV V C hs) (hcov_uni D Fl nV V C hs) (hS_uni D Fl nV V C hs)
    (fun π _ _ => fitsAll_uView _ π)
    (fun π ch cs hc hl hg hn hgS => hlink_uni D Fl nV V C R hFin π ch cs hc hl hg hn hgS)
  refine hle.trans ((prEvent_mono _ _ _ fun z hz =>
    breaksOK_of_rel D Fl nV V C hs R hpre _ hz).trans (hmain.trans ?_))
  have hS := setupQS_le D hs
  have hn := hN.chain
  have hq := sumQO_le D Fl nV V C hs
  exact le_uniBound e Q setupQS (uSpec Fl nV V).K.nQ _ (uSpec Fl nV V).nRf hS hn hq
    (show (5 : ℕ) ≤ 6 by decide) _ _ _
    (doom_le D Fl nV V C hs Q _ (by
      unfold uniN
      have : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
      have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
      have : (2 : ℕ) ^ 10 = 1024 := by norm_num
      omega)) (maxErrK_uni D Fl nV V hs R e herr)
    (uniSpec_tagBound _)

end Facts

end UniSound
