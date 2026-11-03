-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `formal/UniSound/UniSound/FsOps.lean` and
-- `FsProof.lean`'s facts (`hok_uni`, `hcov_uni`, `hS_uni`, `maxErrK_uni`, the shapes) to π2's six openings.
import RecCompose.FsDefs
import RecCompose.Tables
import Bridge.Verifier
import WhirBridge.Union

/-!
# π2's openings: what the framework needs of them

* **the layouts** (`layoutsOf_cc`): `W`'s, `Q`'s and the setup's public layouts at `m = 24`, F2's `shW`, `shQ`, `shS`
  (`layoutTr_W`, `layoutTr_Q`, `layoutTr_S`);
* **a claim on a public layout's stack is F2's on its column** (`claimOn_iff`): `ClaimOn` (`readEntry`, `eqBits`) is
  F2's `tableEval` (`Blocks.table`, `eqEval`) for a layout of distinct blocks (`readEntry_public`);
* **the openings' `OKP`** (`okp_W`, `okp_Q`: the decoders list the candidates' stacks, a stack satisfying the
  opening's claims is good; π1's three: no stack); `hcov`, `hfit`, and **`hS`** (the setup's claim on its table, from
  its opening);
* **the shapes at once** (`p2Shapes`: plain `2^24`, the setup's `2^25`, `Q`'s `2^28`, plain `2^27`; their prefixes
  distinct) and the openings' query counts (`sumQO_le`); the decoders' lists (`L_W = 9952`, `L_Q = 3564`) and
  `maxErrK` (`maxErrK_le`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge Finset
open OracleSpec OracleComp
open scoped ENNReal

attribute [local instance high] Completeness.instSampleableTypeE_completeness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack RecStatement.layoutWords

/-! ## The layouts -/

theorem cc_logN : cc.logN = 24 := rfl

theorem cc_logRow : cc.logRow = 4 := rfl

theorem layoutsOf_cc : layoutsOf cc.logN =
    (PcsQuotient.Layout.ofChunks 24 24 24 [(0, 2 ^ 24)],
      PcsQuotient.Layout.ofChunks 29 24 28 (quotientChunks 24),
      PcsQuotient.Layout.ofChunks 25 24 25 [(0, 2 ^ 24), (1, 2 ^ 24)]) := by
  rw [cc_logN]
  simp only [layoutsOf, certifiedFrom, minCertifiedStack, show (20 : ℕ) ≤ 24 by norm_num, ite_true]
  rfl

/-- `W`'s layout at the real circuit. -/
abbrev lW : PcsQuotient.Layout := PcsQuotient.Layout.ofChunks 24 24 24 [(0, 2 ^ 24)]
/-- `Q`'s layout at the real circuit. -/
abbrev lQ : PcsQuotient.Layout := PcsQuotient.Layout.ofChunks 29 24 28 (quotientChunks 24)
/-- The setup's layout at the real circuit. -/
abbrev lS : PcsQuotient.Layout := PcsQuotient.Layout.ofChunks 25 24 25 [(0, 2 ^ 24), (1, 2 ^ 24)]

theorem layoutTr_W : Bridge.layoutTr lW = shW.L := Bridge.layoutTr_ofChunks_zero 24 24 24 (2 ^ 24)

theorem layoutTr_Q : Bridge.layoutTr lQ = shQ.L := by decide +kernel

theorem layoutTr_S : Bridge.layoutTr lS = shS.L := by decide +kernel

theorem lanes_W : (∀ l ∈ lW.lanes, ∃ b, l = .block b) ∧ lW.lanes.Nodup := by
  constructor
  · intro l hl
    simp only [PcsQuotient.Layout.ofChunks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_map] at hl
    obtain ⟨j, -, rfl⟩ := hl
    exact ⟨_, rfl⟩
  · decide +kernel

theorem lanes_Q : (∀ l ∈ lQ.lanes, ∃ b, l = .block b) ∧ lQ.lanes.Nodup := by
  constructor
  · intro l hl
    simp only [PcsQuotient.Layout.ofChunks, List.mem_flatMap, List.mem_map] at hl
    obtain ⟨_, -, j, -, rfl⟩ := hl
    exact ⟨_, rfl⟩
  · decide +kernel

theorem lanes_S : (∀ l ∈ lS.lanes, ∃ b, l = .block b) ∧ lS.lanes.Nodup := by
  constructor
  · intro l hl
    simp only [PcsQuotient.Layout.ofChunks, List.mem_flatMap, List.mem_map] at hl
    obtain ⟨_, -, j, -, rfl⟩ := hl
    exact ⟨_, rfl⟩
  · decide +kernel

/-! ## A claim on a public layout's stack is F2's -/

theorem getD_toArray {μ : ℕ} (q : Column μ) (j : ℕ) : q.values.toArray.getD j 0 = q.values.getD j 0 := by
  by_cases h : j < 2 ^ μ
  · simp [Array.getD, Vector.getD, h]
  · simp [Array.getD, Vector.getD, h]

/-- **A column's words read through a public layout of distinct blocks are F2's table.** -/
theorem readEntry_public (L : PcsQuotient.Layout) (hp : L.logPiece = none)
    (hb : ∀ l ∈ L.lanes, ∃ b, l = .block b) (hnd : L.lanes.Nodup) (q : Column L.logN) (i : ℕ) :
    L.readEntry (stackOf q) i = (Bridge.layoutTr L).table q i := by
  have hlog : (Bridge.layoutTr L).toBlocks.logLane = L.logLane := rfl
  have hlen : (Bridge.layoutTr L).toBlocks.lanes = L.lanes.length := by
    simp [WhirBridge.Layout.toBlocks, WhirBridge.Blocks.lanes, Bridge.layoutTr]
  have hgetD : ∀ l (hl : l < L.lanes.length) b, L.lanes[l] = .block b →
      (Bridge.layoutTr L).toBlocks.blocks.getD l 0 = b := by
    intro l hl b hlb
    simp only [WhirBridge.Layout.toBlocks, Bridge.layoutTr, List.map_map]
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
    simp only [Function.comp_apply, hlb]
    rfl
  have htab : (Bridge.layoutTr L).table q i = (Bridge.layoutTr L).toBlocks.table q i := by
    unfold WhirBridge.Layout.table
    rw [Bridge.layoutTr_logPiece, hp]
  rw [htab]
  unfold WhirBridge.Blocks.table PcsQuotient.Layout.readEntry
  rw [hp, hlog, hlen]
  simp only
  rcases hf : L.lanes.findIdx? (· = PcsQuotient.Lane.block (i / 2 ^ L.logLane)) with _ | l
  · refine (Finset.sum_eq_zero fun l hl => ?_).symm
    have hl' := Finset.mem_range.mp hl
    obtain ⟨b, hb'⟩ := hb _ (List.getElem_mem hl')
    rw [hgetD l hl' b hb']
    rw [List.findIdx?_eq_none_iff] at hf
    have := hf (L.lanes[l]) (List.getElem_mem hl')
    rw [hb'] at this
    simp only [decide_eq_false_iff_not] at this
    rw [ite_eq_right_iff]
    intro h
    exact absurd (by rw [h]) this
  · obtain ⟨hl, hlv, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [decide_eq_true_eq] at hlv
    dsimp only
    rw [Finset.sum_eq_single l]
    · rw [hgetD l hl _ hlv, ite_eq_left rfl]
      show q.values.toArray.getD _ 0 = _
      rw [getD_toArray]
      congr 1
      ring
    · intro l' hl' hne
      have hl'' := Finset.mem_range.mp hl'
      obtain ⟨b, hb'⟩ := hb _ (List.getElem_mem hl'')
      rw [hgetD l' hl'' b hb']
      rw [ite_eq_right_iff]
      intro h
      have heq : L.lanes[l'] = L.lanes[l] := by
        rw [hb', hlv, h]
      exact absurd ((List.Nodup.getElem_inj_iff hnd).mp heq) hne
    · intro h
      exact absurd (Finset.mem_range.mpr hl) h

/-- **A claim on a public layout's stack is F2's on its column**: `ClaimOn` (the statement's `readEntry`, `eqBits`)
is `tableEval` of `layoutTr`, for a point of the layout's variables. -/
theorem claimOn_iff (L : PcsQuotient.Layout) (hp : L.logPiece = none)
    (hb : ∀ l ∈ L.lanes, ∃ b, l = .block b) (hnd : L.lanes.Nodup) (q : Column L.logN) (pt : List E) (v : E)
    (hpt : pt.length = L.vars) :
    ClaimOn L (stackOf q) (pt, v) ↔ (Bridge.layoutTr L).tableEval q pt = v := by
  unfold ClaimOn WhirBridge.Layout.tableEval
  have : ∑ i ∈ range (2 ^ L.vars), PcsQuotient.eqBits pt i * ofK (L.readEntry (stackOf q) i) =
      ∑ t ∈ range (2 ^ (Bridge.layoutTr L).vars),
        ofK ((Bridge.layoutTr L).table q t) * Verifier.eqEval (boolPoint (Bridge.layoutTr L).vars t) pt := by
    rw [Bridge.layoutTr_vars]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [readEntry_public L hp hb hnd q i, Bridge.eqBits_eq, WhirBridge.eqBits_eq_boolPoint, hpt, mul_comm]
  simp only
  rw [this]

/-- `claimOn_iff` at a layout given up to `layoutTr`. -/
theorem claimOn_iff' (L : PcsQuotient.Layout) (L' : WhirBridge.Layout) (hLL : Bridge.layoutTr L = L')
    (hp : L.logPiece = none) (hb : ∀ l ∈ L.lanes, ∃ b, l = .block b) (hnd : L.lanes.Nodup)
    (q : Column L'.logN) (pt : List E) (v : E) (hpt : pt.length = L.vars) :
    ClaimOn L (stackOf q) (pt, v) ↔ L'.tableEval q pt = v := by
  subst hLL
  exact claimOn_iff L hp hb hnd q pt v hpt

/-- **A public layout reads its stack below its lanes' words only.** -/
theorem readEntry_congr (L : PcsQuotient.Layout) (hp : L.logPiece = none) (s s' : Stk)
    (h : ∀ j < L.lanes.length * 2 ^ L.logLane, s j = s' j) (i : ℕ) : L.readEntry s i = L.readEntry s' i := by
  unfold PcsQuotient.Layout.readEntry
  rw [hp]
  simp only
  rcases hf : L.lanes.findIdx? (· = PcsQuotient.Lane.block (i / 2 ^ L.logLane)) with _ | l
  · rfl
  · obtain ⟨hl, -, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    dsimp only
    refine h _ ?_
    have hm : i % 2 ^ L.logLane < 2 ^ L.logLane := Nat.mod_lt _ (Nat.two_pow_pos _)
    calc l * 2 ^ L.logLane + i % 2 ^ L.logLane < l * 2 ^ L.logLane + 2 ^ L.logLane := by omega
      _ = (l + 1) * 2 ^ L.logLane := by ring
      _ ≤ L.lanes.length * 2 ^ L.logLane := Nat.mul_le_mul_right _ hl

/-! ## The run's points -/

theorem p2Out_witnessPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).witnessPoint.length = 24 := by
  unfold p2Out
  rw [run_witnessPoint, spec_core_logN, spec_core_logRow]
  simp [digitsList, cc_logN, cc_logRow]

theorem p2Out_setupPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).setupPoint.length = 25 := by
  unfold p2Out
  rw [run_setupPoint, spec_core_logN]
  simp [digitsList, cc_logN]

theorem p2Out_quotientPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).quotientPoint.length = 29 := by
  unfold p2Out
  rw [run_quotientPoint, List.length_append, run_uList_length, spec_core_logN, cc_logN]
  rfl

theorem p2Out_sumPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).sumPoint.length = 29 := by
  unfold p2Out
  rw [run_sumPoint, spec_core_logN, cc_logN]
  simp

theorem clW_claims (π : P2Pf) (ch : List (List E)) :
    (clW π ch).claims = [⟨(p2Out π ch).witnessPoint, (p2Out π ch).fold⟩] :=
  Bridge.toStmt_claims_of (by simp) fun c hc => by
    rw [List.mem_singleton] at hc
    subst hc
    exact p2Out_witnessPoint_length π ch

theorem clS_claims (π : P2Pf) (ch : List (List E)) :
    (clS π ch).claims = [⟨(p2Out π ch).setupPoint, (p2Inputs π ch).ξ⟩] :=
  Bridge.toStmt_claims_of (by simp) fun c hc => by
    rw [List.mem_singleton] at hc
    subst hc
    exact p2Out_setupPoint_length π ch

theorem clQ_claims (π : P2Pf) (ch : List (List E)) :
    (clQ π ch).claims = [⟨(p2Out π ch).quotientPoint, (p2Out π ch).quotientValue⟩,
      ⟨(p2Out π ch).sumPoint, (p2Out π ch).sumValue⟩] :=
  Bridge.toStmt_claims_of (by simp) fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact p2Out_quotientPoint_length π ch
    · exact p2Out_sumPoint_length π ch

/-! ## The openings' `OKP` -/

section Ops

variable (D : RecDeployment) (hs : UniSound.UniShapes D.pi1)

theorem p2Tc_zero : p2Tc 0 = colCode shW.L shW.R shW.adm := by
  unfold p2Tc
  exact ite_eq_left rfl

theorem p2Tc_one : p2Tc 1 = colCode shQ.L shQ.R shQ.adm := by
  unfold p2Tc
  exact ite_eq_right (by decide)

theorem colCode_dec (L : WhirBridge.Layout) (R : ℕ) (hw : Whir.Admissible L.logN R)
    (w : Fin (2 ^ WhirBridge.rootHeight L.logN R) → Option (List UInt8)) :
    (colCode L R hw).dec w = (decodeColumns L.logN R (wordOfMerkle (WhirBridge.rootHeight L.logN R)
      (2 ^ WhirBridge.laneFold) w)).map stackOf := by
  simp only [colCode]

theorem colCode_mem (L : WhirBridge.Layout) (R : ℕ) (hw : Whir.Admissible L.logN R)
    (w : Fin (2 ^ WhirBridge.rootHeight L.logN R) → Option (List UInt8)) (q : Column L.logN)
    (hq : q ∈ Candidates L.logN R (code₀ L.logN R).thr
      (wordOfMerkle (WhirBridge.rootHeight L.logN R) (2 ^ WhirBridge.laneFold) w)) :
    stackOf q ∈ (colCode L R hw).dec w := by
  rw [colCode_dec]
  exact List.mem_map_of_mem ((mem_decodeColumns hw _ q).mpr hq)

theorem colCode_height (L : WhirBridge.Layout) (R : ℕ) (hw : Whir.Admissible L.logN R) :
    (colCode L R hw).height = WhirBridge.rootHeight L.logN R := by simp only [colCode]

theorem colCode_leafLen (L : WhirBridge.Layout) (R : ℕ) (hw : Whir.Admissible L.logN R) :
    (colCode L R hw).leafLen = 8 * 2 ^ WhirBridge.laneFold := by simp only [colCode]

/-- **`W`'s opening**: its decoder lists the candidates' stacks, and a stack satisfying its claim is good. -/
theorem okp_W : WhirOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D)
    (⟨shW, clW, fun π => π.proof.w, .round 0 stackOf⟩ : WhirOp P2Pf E Stk) := by
  unfold WhirOp.OKP
  dsimp only
  rw [p2Tc_zero]
  refine ⟨colCode_height _ _ _, colCode_leafLen _ _ _, fun w q hq => colCode_mem shW.L shW.R shW.adm w q hq,
    fun π ch q h => ?_⟩
  unfold p2Good
  rw [ite_eq_left rfl]
  refine ⟨stackOf q, rfl, ?_⟩
  have hcl := h _ (by rw [clW_claims]; exact List.mem_singleton_self _)
  rw [layoutsOf_cc]
  exact (claimOn_iff' lW shW.L layoutTr_W rfl lanes_W.1 lanes_W.2 q _ _
    (p2Out_witnessPoint_length π ch)).mpr hcl

/-- **`Q`'s opening**: its decoder lists the candidates' stacks, and a stack satisfying its two claims is good. -/
theorem okp_Q : WhirOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D)
    (⟨shQ, clQ, fun π => π.proof.q, .round 1 stackOf⟩ : WhirOp P2Pf E Stk) := by
  unfold WhirOp.OKP
  dsimp only
  rw [p2Tc_one]
  refine ⟨colCode_height _ _ _, colCode_leafLen _ _ _, fun w q hq => colCode_mem shQ.L shQ.R shQ.adm w q hq,
    fun π ch q h => ?_⟩
  unfold p2Good
  rw [ite_eq_right (by decide), ite_eq_left rfl]
  have h1 := h _ (by rw [clQ_claims]; exact List.mem_cons_self)
  have h2 := h _ (by rw [clQ_claims]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨stackOf q, rfl, ?_, ?_⟩
  · rw [layoutsOf_cc]
    exact (claimOn_iff' lQ shQ.L layoutTr_Q rfl lanes_Q.1 lanes_Q.2 q _ _
      (p2Out_quotientPoint_length π ch)).mpr h1
  · rw [layoutsOf_cc]
    exact (claimOn_iff' lQ shQ.L layoutTr_Q rfl lanes_Q.1 lanes_Q.2 q _ _
      (p2Out_sumPoint_length π ch)).mpr h2

/-- **An opening of no `2^25`-word stack has no stack.** -/
theorem p2Stk_none (o : WhirOp P2Pf E Stk) (h : o.S.L.logN ≠ 25) : p2Stk D o = none := by
  unfold p2Stk
  exact dite_eq_right_iff.mpr fun h' => absurd h' h

/-- **π1's openings**: nothing to show (no stack). -/
theorem okp_pi1 (k : ℕ) (r : P2Pf → Bytes32) (q₀ : Column (sh1 k).L.logN) (prf : P2Pf → Compile.Proof) :
    WhirOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D)
      (⟨sh1 k, cl1 D k, prf, .setup r q₀⟩ : WhirOp P2Pf E Stk) := by
  unfold WhirOp.OKP
  dsimp only
  intro f hf
  rw [p2Stk_none D _ (by
    show pi1Vars k ≠ 25
    unfold pi1Vars
    split_ifs <;> decide)] at hf
  exact absurd hf (by simp)

/-- **The setup's opening's stack** is the setup's table at the proof's roots. -/
theorem p2Stk_setup :
    p2Stk D (⟨shS, clS, fun π => π.proof.setup, .setup (fun π => π.roots.2) (col0 _)⟩ : WhirOp P2Pf E Stk) =
      some fun π => setupCol D (p2Roots π) := by
  unfold p2Stk
  split_ifs with h
  · rfl
  · exact absurd rfl h

/-- **Every round with a root is opened**: `W`'s and `Q`'s. -/
theorem hcov_p2 : ∀ i < pi2Spec.K.rounds.length, (pi2Spec.K.spec i).root →
    ∃ o ∈ p2Ops D, ∃ rd, o.tgt = .round i rd := by
  intro i hi hr
  have hi3 : i < 3 := hi
  interval_cases i
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      stackOf, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))), stackOf, rfl⟩
  · exact absurd hr (by decide)

/-- **The stream's messages fit the rounds.** -/
theorem hfit_p2 (π : P2Pf) : FitsAll pi2Spec.K.rounds (p2View π).2 :=
  UniSound.fitsAll_msgsAt _ _ _

/-- The setup's table read off its column (`2^25` words) is the table (`readEntry` reads below `2^25`). -/
theorem claimOn_setupCol (roots : RecSetupRoots) (c : List E × E) :
    ClaimOn lS (stackOf (setupCol D roots)) c ↔ ClaimOn lS (fun j ↦ (setupStackAt D roots).getD j 0) c := by
  have hlen : lS.lanes.length * 2 ^ lS.logLane = 2 ^ 25 := by decide +kernel
  have hr : ∀ i, lS.readEntry (stackOf (setupCol D roots)) i =
      lS.readEntry (fun j ↦ (setupStackAt D roots).getD j 0) i :=
    readEntry_congr lS rfl _ _ fun j hj => by
      rw [hlen] at hj
      have hj' : j < 33554432 := by norm_num at hj; exact hj
      simp [stackOf, setupCol, UniSound.colOf, Array.getD, hj']
  unfold ClaimOn
  simp only [hr]

/-- **The setup's opening gives the setup's claim on its table** (`hS`). -/
theorem hS_p2 (π : P2Pf) (ch : List (List E))
    (h : ∀ o ∈ p2Ops D, WhirOp.SetupHoldsP (p2Stk D) o π ch) : p2GoodS D π ch := by
  have h5 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self))) :
    (⟨shS, clS, fun π => π.proof.setup, .setup (fun π => π.roots.2) (col0 _)⟩ : WhirOp P2Pf E Stk) ∈ p2Ops D)
  unfold WhirOp.SetupHoldsP at h5
  dsimp only at h5
  have hcl := h5 _ (p2Stk_setup D) _ (by rw [clS_claims]; exact List.mem_singleton_self _)
  unfold p2GoodS
  rw [layoutsOf_cc]
  exact (claimOn_setupCol D _ _).mp ((claimOn_iff' lS shS.L layoutTr_S rfl lanes_S.1 lanes_S.2 _ _ _
    (p2Out_setupPoint_length π ch)).mpr hcl)

end Ops

/-! ## The shapes, at once -/

/-- **π2's contract's shapes**: plain `2^24` (`W`, π1's `F`), the setup's `2^25`, `Q`'s `2^28`, plain `2^27` (π1's
`C1`, `C2`), at `εExact`. -/
noncomputable def p2Shapes : List (ExactShape εExact) :=
  [plainShapeE 24 le_rfl (by norm_num),
    ExactShape.large 25 24 25 [(0, 2 ^ 24), (1, 2 ^ 24)] newOK_setup (by decide) (by decide),
    ExactShape.large 29 24 28 (quotientChunks 24) newOK_quotient (by decide) (by decide),
    plainShapeE 27 (by norm_num) (by norm_num)]

theorem p2Shapes_logN : p2Shapes.map (fun s ↦ s.L.logN) = [24, 25, 28, 27] := rfl

theorem p2Shapes_nodup : (p2Shapes.map fun s ↦ openingPrefix s.L s.R).Nodup := by
  refine nodup_prefix_of_logN (fun s hs ↦ ?_) (by rw [p2Shapes_logN]; decide)
  have h := List.mem_map_of_mem (f := fun s : ExactShape εExact ↦ s.L.logN) hs
  rw [p2Shapes_logN] at h
  simp at h
  omega

theorem p2Shapes_QO : ∀ s ∈ p2Shapes, s.QO ≤ 9018 := by
  intro s hs
  obtain ⟨h24, h25, h26, h27, h28⟩ := largeQueries_eq
  simp only [p2Shapes, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · show largeQueries 24 ≤ 9018
    omega
  · show largeQueries 25 ≤ 9018
    omega
  · show largeQueries 28 ≤ 9018
    omega
  · show largeQueries 27 ≤ 9018
    omega

/-- **The six openings' shapes are among `p2Shapes`.** -/
theorem hops_p2 (D : RecDeployment) : ∀ o ∈ p2Ops D, ∃ s ∈ p2Shapes, s.L = o.S.L ∧ s.R = o.S.R := by
  intro o ho
  simp only [p2Ops, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      rfl, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      rfl, rfl⟩
  · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
  · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl, rfl⟩

/-- **The six openings' queries**: `8318 + 8318 + 7183 + 7183 + 7546 + 9018`. -/
theorem sumQO_p2 (D : RecDeployment) : ((p2Ops D).map fun o => o.S.QO).sum = 47566 := by
  obtain ⟨h24, h25, h26, h27, h28⟩ := largeQueries_eq
  have e0 : pi1Vars 0 = 27 := rfl
  have e1 : pi1Vars 1 = 27 := rfl
  have e2 : pi1Vars 2 = 24 := rfl
  simp only [p2Ops, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e0, e1, e2, h24, h25, h27, h28,
    Nat.reduceAdd]

/-! ## The lists, `maxErrK` -/

theorem p2Tc_bound_zero : (p2Tc 0).commit.bound = 9952 := by
  rw [TableCode.commit_bound, p2Tc_zero]
  exact listHi_large 24 le_rfl (by decide)

theorem p2Tc_bound_one : (p2Tc 1).commit.bound = 3564 := by
  rw [TableCode.commit_bound, p2Tc_one]
  exact listHi_large 28 (by decide) le_rfl

/-- **The lists of the roots before round `j`** (`facL`): `L_W`, then `L_W L_Q`. -/
theorem facL_p2 : ∀ j < 3, facL (fun i => (p2Tc i).commit) 0 (pi2Spec.K.rounds.take (j + 1)) = pi2Fac j := by
  intro j hj
  interval_cases j
  · rw [show pi2Spec.K.rounds.take (0 + 1) = [⟨true, 0, 2⟩] from rfl]
    simp only [facL, ite_true, p2Tc_bound_zero, mul_one]
    rfl
  · rw [show pi2Spec.K.rounds.take (1 + 1) = [⟨true, 0, 2⟩, ⟨true, 0, 0⟩] from rfl]
    simp only [facL, ite_true, Nat.reduceAdd, p2Tc_bound_zero, p2Tc_bound_one, mul_one]
    rfl
  · rw [show pi2Spec.K.rounds.take (2 + 1) = RecPiop.pi2Rounds 4 from rfl]
    simp only [RecPiop.pi2Rounds, facL, ite_true, Nat.reduceAdd, p2Tc_bound_zero, p2Tc_bound_one, mul_one,
      Bool.false_eq_true, ite_false]
    rfl

/-- **The rounds' errors times their lists** are at most `e` when each round's error times `pi2Fac` is. -/
theorem maxErrK_p2 (R : Compose.Piop pi2Spec.K Stk) (e : ℝ≥0∞)
    (herr : ∀ j < 3, (pi2Fac j : ℝ≥0∞) * R.err j ≤ e) :
    maxErrK pi2Spec.K (fun i => (p2Tc i).commit) R ≤ e := by
  unfold maxErrK
  refine Finset.sup_le fun j hj => ?_
  have hj3 : j < 3 := Finset.mem_range.mp hj
  rw [facL_p2 j hj3]
  exact herr j hj3

end RecCompose

/-- info: 'RecCompose.readEntry_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.readEntry_public

/-- info: 'RecCompose.hS_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hS_p2

/-- info: 'RecCompose.maxErrK_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.maxErrK_p2
