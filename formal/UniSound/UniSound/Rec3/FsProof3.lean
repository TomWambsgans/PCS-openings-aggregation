-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsProof.lean` (the composition's
-- facts, the bound) and `FsCost.lean` (`uniNumbers_of`) for π1-rec3's three openings.
import UniSound.Rec3.FsOps3
import UniSound.FsCost

/-!
# π1-rec3: the composition's facts, the numbers, the bound

`FsProof.lean`'s and `FsCost.lean`'s facts for π1-rec3's three openings (`uOps3`), the chain `uSpec3` on
`rec3Rounds` and the setup **unchanged** (`uSetup`: the three trees of the setup's stack, `A0`, `B0`; the verifier
opens only the first, the IV hashes all three roots):

* the openings match (`hok_uni3`: `C1`, `C2` by `whirOp_ok_tableCode`, the setup's by its tree, `whirOp_ok_tree`),
  every round with a root is opened (`hcov_uni3`), the setup's stack satisfies its claim (`hS_uni3`), the last link
  (`hlink_uni3`, from `FsLayer3`'s: `ClaimsHold`'s matrices' half is vacuous, the result has no matrices' claim);
* **the numbers** (`UniNumbers3`, `uniNumbers3_of`): the chain's `< 2^10` queries, the composed verifier's calls of
  `π` below `2^80` (`(2^10 + 3 · 10122) · 2^32`);
* **the bound** (`le_uniBound3`): the three doom terms at most `openingBoundAt 10122 N` each, the lists at most
  `largeList ≤ 9952` (two roots: `countP_root_rec3Rounds`), the tag's `2^-128`, at most `8 N` references a query.
  `uniBound3`'s definition (`Fs3.lean`) is unchanged: its constants other than the doom terms' count are the
  main line's, and the setup's and the chain's counts are the same (three trees; `< 2^10` queries).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open LeanVM.Rpm (Short hashBlocks)
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

theorem countP_root_rec3Rounds (fr : List RoundSpec) (hfr : ∀ r ∈ fr, r.root = false) (nV np : ℕ) :
    (rec3Rounds fr nV np).countP (fun r => r.root) = 2 := by
  have h0 : fr.countP (fun r => r.root) = 0 :=
    List.countP_eq_zero.mpr fun r hr => by simp [hfr r hr]
  simp [rec3Rounds, List.countP_append, h0]

/-- **The composed bound is at most `uniBound3`**: the three doom terms at most `openingBoundAt 10122 N`, the list
term at most `9952² e`, the tag's `2^-128`, at most `8 N` references a query, the permutation's calls below
`2^81 + Q`. -/
theorem le_uniBound3 (e : ℝ≥0∞) (Q QS nQ SQO nRf : ℕ) (hQS : QS ≤ 3 * 2 ^ 24) (hnQ : nQ ≤ 2 ^ 10)
    (hSQO : SQO ≤ 3 * 10122) (hr : nRf ≤ 6) (d m t : ℝ≥0∞)
    (hd : d ≤ 3 * openingBoundAt 10122 (uniN Q)) (hm : m ≤ ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e)
    (ht : t = ((256 ^ 16 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    d + ((QS + (QS + (Q + 8)) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + t + (((nRf + 2) * (QS + (QS + (Q + 8)) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ uniBound3 e Q := by
  unfold uniBound3
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

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
  (hs : UniShapes D)

/-- The three openings at the honest setup column. -/
noncomputable abbrev uOps3 : List (WhirOp UPf E Stk) :=
  uniOps3 F3 nV np C hs (colF D)

/-- The chain of π1-rec3's rounds. -/
noncomputable abbrev uSpec3 : ChainSpecU E FSt := uniSpec (uRounds3 F3 nV np)

theorem hcov_uni3 : ∀ i < (uSpec3 F3 nV np).K.rounds.length, ((uSpec3 F3 nV np).K.spec i).root →
    ∃ o ∈ uOps3 D F3 nV np C hs, ∃ rd, o.tgt = .round i rd := by
  intro i _ hr
  rcases root_rec3Rounds F3.prog.rounds F3.rounds_root nV np i hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, _, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, _, rfl⟩

theorem hok_uni3 : ∀ o ∈ uOps3 D F3 nV np C hs,
    WhirOp.OK (uniTc hs) (uniGood3 D F3 nV np C) (uSetup D hs) uFix o := by
  intro o ho
  simp only [uOps3, uniOps3, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · refine whirOp_ok_tableCode _ _ _ 0 rdTab (uniTc hs) (by unfold uniTc; rw [ite_eq_left rfl]) _
      (fun π ch t h => ?_) _ _
    rw [uniGood3, ite_eq_left rfl]
    exact ⟨rdTab t, rfl, fun cl hcl =>
      (tabEval_rdTab _ t _ ((cl1_3 D F3 nV np C π ch).wide cl hcl)).symm.trans (h cl hcl)⟩
  · refine whirOp_ok_tableCode _ _ _ (F3.prog.rounds.length + 1) rdTab (uniTc hs)
      (by unfold uniTc; rw [ite_eq_right (Nat.succ_ne_zero _)]) _ (fun π ch t h => ?_) _ _
    rw [uniGood3, ite_eq_right (Nat.succ_ne_zero _), ite_eq_left rfl]
    exact ⟨rdTab t, rfl, fun cl hcl =>
      (tabEval_rdTab _ t _ ((cl2_3 D F3 nV np C π ch).wide cl hcl)).symm.trans (h cl hcl)⟩
  · refine whirOp_ok_tree _ _ _ _ _ _ _ _ _ (fun T x hx => ?_) fun T p => ?_
    · rw [(setupK3_run hs _ _ _ T).1]
      simp only [List.map_append, List.mem_append]
      exact Or.inl hx
    · simp only [uFix, (setupK3_run hs _ _ _ T).2]
      exact LeanVM.Rpm.digestToRpm_ofRpm _

theorem hS_uni3 (π : UPf) (ch : List (List E))
    (h : ∀ o ∈ uOps3 D F3 nV np C hs, WhirOp.SetupHolds o π ch) : uniGoodS3 D F3 nV np C π ch := by
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  intro cl hcl
  have := h3 cl hcl
  rw [← this]
  exact (plain_tableEval _ (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _ _
    ((cl3_3 D F3 nV np C π ch).wide cl hcl)).symm

/-! ### The last link -/

/-- **The composition's last link from `FsLayer3`'s**: candidates good at `C1`'s and `C2`'s rounds and `none` at
the others, the setup's stack good, and the check, make the opened transcript the one `FsLayer3`'s link reads
(`openedOf`), its claims true (`ClaimsHold`: the matrices' half vacuous, `WellFormed3` has none). -/
theorem hlink_uni3 (R : RbrPiop (uRounds3 F3 nV np) USt Stk)
    (hFin : ∀ (s : USt) done tl c1 c2, DoneFits (uRounds3 F3 nV np) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf F3.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch)
    (π : UPf) (ch : List (List E)) (cs : List (Option Stk)) (hc : uniCheck3 D F3 nV np C π ch)
    (hl : cs.length = (uSpec3 F3 nV np).K.rounds.length)
    (hg : ∀ i (h : i < cs.length), ((uSpec3 F3 nV np).K.spec i).root →
      uniGood3 D F3 nV np C i π ch cs[i])
    (hn : ∀ i (h : i < cs.length), ((uSpec3 F3 nV np).K.spec i).root = false → cs[i] = none)
    (hgS : uniGoodS3 D F3 nV np C π ch) :
    ∃ p m c, opened cs (uView (uRounds3 F3 nV np) π).2 ch = p ++ [(m, c)] ∧
      (liftPiop (uSpec3 F3 nV np).K R rfl).post (uView (uRounds3 F3 nV np) π).1 p m c := by
  obtain ⟨hdf, hzv, hwf⟩ := hc
  have hlen : cs.length = F3.prog.rounds.length + 4 + np := by
    rw [hl]
    exact length_rec3Rounds _ _ _
  have h0 : 0 < cs.length := by omega
  have h1 : F3.prog.rounds.length + 1 < cs.length := by omega
  have hs0 : ((uSpec3 F3 nV np).K.spec 0).root := by
    show ((rec3Rounds F3.prog.rounds nV np).getD 0 ⟨false, 0, 0⟩).root = true
    rw [rec3Rounds_zero]
  have hs1 : ((uSpec3 F3 nV np).K.spec (F3.prog.rounds.length + 1)).root := by
    show ((rec3Rounds F3.prog.rounds nV np).getD (F3.prog.rounds.length + 1) ⟨false, 0, 0⟩).root = true
    rw [rec3Rounds_c2]
  have g0 := hg 0 h0 hs0
  rw [uniGood3, ite_eq_left rfl] at g0
  obtain ⟨q1, hq1, hc1⟩ := g0
  have g1 := hg _ h1 hs1
  rw [uniGood3, ite_eq_right (Nat.succ_ne_zero _), ite_eq_left rfl] at g1
  obtain ⟨q2, hq2, hc2⟩ := g1
  have hcand : ∀ i (h : i < cs.length), cs[i] = candAt F3.prog.rounds.length q1 q2 i := by
    intro i h
    by_cases hi0 : i = 0
    · subst hi0
      rw [hq1]
      simp [candAt]
    by_cases hi1 : i = F3.prog.rounds.length + 1
    · subst hi1
      rw [hq2]
      simp [candAt]
    · rcases Bool.eq_false_or_eq_true ((uSpec3 F3 nV np).K.spec i).root with hr | hr
      · rcases root_rec3Rounds F3.prog.rounds F3.rounds_root nV np i hr with h' | h'
        · exact absurd h' hi0
        · exact absurd h' hi1
      · rw [hn i h hr]
        simp [candAt, hi0, hi1]
  have hlu : (msgsAt π.proof.stream 24 (uRounds3 F3 nV np)).length = (uRounds3 F3 nV np).length :=
    length_msgsAt _ _ _
  have hch : (msgsAt π.proof.stream 24 (uRounds3 F3 nV np)).length ≤ ch.length := by
    have := hdf.length_eq
    simp only [uDone, List.length_zip] at this
    omega
  have hop : opened cs (uView (uRounds3 F3 nV np) π).2 ch =
      openedOf F3.prog.rounds.length q1 q2 (uDone (uRounds3 F3 nV np) π ch) :=
    opened_eq_openedOf _ q1 q2 _ ch cs hch (by rw [hlu]; exact hl) hcand
  obtain ⟨hwo, hw1, hw2, hw3, hwm⟩ := hwf
  have e1 : (cl1_3 D F3 nV np C π ch).claims = claimsOf (uOut3 D F3 nV np C π ch) .c1 :=
    mkStmt_claims (plainL (wv D 0)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw1
  have e2 : (cl2_3 D F3 nV np C π ch).claims = claimsOf (uOut3 D F3 nV np C π ch) .c2 :=
    mkStmt_claims (plainL (wv D 1)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw2
  have e3 : (cl3_3 D F3 nV np C π ch).claims = claimsOf (uOut3 D F3 nV np C π ch) .setup :=
    mkStmt_claims (plainL (wv D 2)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw3
  have hm0 : ∀ b, matClaims (uOut3 D F3 nV np C π ch) b = [] := fun b => by
    unfold matClaims
    rw [hwm]
  have hCH : ClaimsHold D (uOut3 D F3 nV np C π ch) q1 q2 :=
    claimsHold_of D _ q1 q2 (by rw [← e1]; exact hc1) (by rw [← e2]; exact hc2)
      (by rw [← e3]; exact hgS) (by rw [hm0]; simp) (by rw [hm0]; simp)
  obtain ⟨p, m, ch', he, hpost⟩ :=
    hFin (uSt3 F3 nV np π) _ _ q1 q2 hdf (length_uTail3 _ _) hzv hCH
  exact ⟨p, m, ch', hop.trans he, hpost⟩

/-! ### The event, the numbers -/

/-- **π1-rec3's break on the composed game's outcome**: the check, the three openings accept, and no candidate of
`C1`'s root read off the transcript satisfies leanVM 42422001's relation. -/
def UniBreaksRel3 (z : OutK UPf E (List Bool)) : Prop :=
  uniCheck3 D F3 nV np C z.1.1 z.1.2.1 ∧
    (∀ k < (uOps3 D F3 nV np C hs).length, z.1.2.2.getD k false = true) ∧
    ∀ c ∈ extractorK (fun i => (uniTc hs i).commit) (uView (uRounds3 F3 nV np)) z,
      ∀ q, c = some q → ¬ Rel D (uSt3 F3 nV np z.1.1) q

/-- **The deployment's numbers**: the chain's queries below `2^10`, the composed verifier's calls of `π` below
`2^80`. -/
structure UniNumbers3 : Prop where
  chain : (uSpec3 F3 nV np).K.nQ ≤ 2 ^ 10
  verifier : ∀ π, Common.QueryCostAtMost (verU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np))
    (opsRun (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)) π) LeanVM.Rpm.hashBlocks (2 ^ 80)

theorem msgK_uView3_zero (π : UPf) : ∃ r, (msgK (uView (uRounds3 F3 nV np)) π 0).1 = some r :=
  ⟨_, rfl⟩

theorem breaksOK_of_rel3 (R : RbrPiop (uRounds3 F3 nV np) USt Stk)
    (hpre : ∀ s c m, R.pre s [] (some c, m) → Rel D s c) (z : OutK UPf E (List Bool))
    (hz : UniBreaksRel3 D F3 nV np C hs z) :
    BreaksOK (uSpec3 F3 nV np).K (fun i => (uniTc hs i).commit) (liftPiop (uSpec3 F3 nV np).K R rfl)
      (uView (uRounds3 F3 nV np)) (uniCheck3 D F3 nV np C)
      (fun bs => ∀ k < (uOps3 D F3 nV np C hs).length, bs.getD k false = true) z := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨h1, h2, fun c hc hpre' => ?_⟩
  obtain ⟨r, hr⟩ := msgK_uView3_zero F3 nV np z.1.1
  have hc' := hc
  simp only [extractorK, optC, hr, List.mem_map] at hc'
  obtain ⟨q, -, rfl⟩ := hc'
  exact h3 _ hc q rfl (hpre _ _ _ hpre')

theorem sumQO_le3 : ((uOps3 D F3 nV np C hs).map fun o => o.S.QO).sum ≤ 3 * 10122 := by
  have q : ∀ k (hk : k < 5), largeQueries (wv D k) ≤ 10122 := fun k hk =>
    (largeQueries_le (wv D k) (hs.lo k hk) (hs.hi k hk)).trans_eq variantQueries_eq
  have q0 := q 0 (by decide)
  have q1 := q 1 (by decide)
  have q2 := q 2 (by decide)
  simp only [uOps3, uniOps3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  try dsimp only [shapeK, plainShape, WhirShape.large]
  omega

theorem doom_le3 (Q X : ℕ) (hX : X + ((uOps3 D F3 nV np C hs).map fun o => o.S.QO).sum ≤ uniN Q) :
    doomSum (uOps3 D F3 nV np C hs) X ≤ 3 * openingBoundAt 10122 (uniN Q) := by
  refine (doomSum_le (uniN Q) (openingBoundAt 10122 (uniN Q)) _ X (fun o ho QA hQA => ?_) hX).trans
    (le_of_eq (by simp [uOps3, uniOps3]))
  simp only [uOps3, uniOps3, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  all_goals
    dsimp only [shapeK, plainShape, WhirShape.large] at hQA ⊢
    exact openingBoundAt_mono (by omega)

theorem maxErrK_uni3 (R : RbrPiop (uRounds3 F3 nV np) USt Stk) (e : ℝ≥0∞) (herr : ∀ j, R.err j ≤ e) :
    maxErrK (uSpec3 F3 nV np).K (fun i => (uniTc hs i).commit) (liftPiop (uSpec3 F3 nV np).K R rfl) ≤
      ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e := by
  unfold maxErrK
  refine Finset.sup_le fun j _ => mul_le_mul' (Nat.cast_le.mpr ?_) (herr j)
  refine (facL_le_pow _ 9952 (fun k => uniTc_bound hs k) 0 _).trans
    (Nat.pow_le_pow_right (by norm_num) ?_)
  exact (List.take_sublist _ _).countP_le.trans
    (le_of_eq (countP_root_rec3Rounds F3.prog.rounds F3.rounds_root nV np))

/-- **The composed verifier's calls of `π`**: at most `2^80`, when the chain asks at most `2^10` queries and every
round sends at most `2^30` scalars (`(2^10 + 3 · 10122) · 2^32 ≤ 2^80`). -/
theorem uniNumbers3_of (hnQ : (uSpec3 F3 nV np).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds3 F3 nV np, r.nv ≤ 2 ^ 30) : UniNumbers3 D F3 nV np C hs := by
  refine ⟨hnQ, fun π => ?_⟩
  have htot : IsTotalQueryBound (verU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np))
      (opsRun (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)) π)
      ((uSpec3 F3 nV np).K.nQ + ((uOps3 D F3 nV np C hs).map fun o => o.S.QO).sum) := by
    unfold verU
    exact isTotalQueryBound_bind (isTotalQueryBound_chainU _ _ _) fun ch =>
      isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_opsRun _ _ _ _) fun _ => trivial
  have hmsg : ∀ m ∈ (uView (uRounds3 F3 nV np) π).2, m.2.length ≤ 2 ^ 30 := by
    intro m hm
    have hfit := fitsAll_uView (uRounds3 F3 nV np) π
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    have hl := hfit.length_eq
    have := fitsAll_getD hfit i (by omega)
    have hi' : i < (uRounds3 F3 nV np).length := by omega
    rw [List.getD_eq_getElem _ _ hi] at this
    rw [this.2, List.getD_eq_getElem _ _ hi']
    exact hnv _ (List.getElem_mem hi')
  have hops : ∀ ch, ∀ o ∈ uOps3 D F3 nV np C hs,
      (o.cl π ch).claims.length ≤ 2 ∧ o.S.L.vars ≤ 2 ^ 30 := by
    intro ch o ho
    simp only [uOps3, uniOps3, List.mem_cons, List.mem_nil_iff, or_false] at ho
    have hk : ∀ k < 5, wv D k ≤ 2 ^ 30 := fun k hk => (hs.hi k hk).trans (by norm_num)
    rcases ho with rfl | rfl | rfl
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 0 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 1 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 2 (by decide)⟩
  have hall : AllQueriesSatisfy (verU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np))
      (opsRun (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)) π) Short := by
    unfold verU ChainSpecU.chain
    rw [map_eq_bind_pure_comp, bind_assoc]
    refine allQueriesSatisfy_bind (allQ_runM _ _ ?_ ?_) fun sts => ?_
    · show (uniLabel _).length ≤ _
      simp [uniLabel, name_length]
    · intro e he
      have := length_mem_absorbsI _ (2 ^ 30) 0 _ _ hmsg e he
      omega
    · simp only [Function.comp_apply, pure_bind]
      exact allQueriesSatisfy_bind (allQ_opsRun _ _ _ _ (hops _)) fun _ => LeanVM.Rpm.allQ_pure _
  have hq := sumQO_le3 D F3 nV np C hs
  refine (LeanVM.Rpm.isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) htot
    (hall.mono fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)).mono ?_
  have h80 : (2 ^ 10 + 3 * 10122) * 2 ^ 32 ≤ (2 : ℕ) ^ 80 := by norm_num
  exact (Nat.mul_le_mul_right _ (by omega)).trans h80

end Facts

end UniSound

/-- info: 'UniSound.hok_uni3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.hok_uni3

/-- info: 'UniSound.hlink_uni3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.hlink_uni3

/-- info: 'UniSound.uniNumbers3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniNumbers3_of

/-- info: 'UniSound.le_uniBound3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.le_uniBound3
