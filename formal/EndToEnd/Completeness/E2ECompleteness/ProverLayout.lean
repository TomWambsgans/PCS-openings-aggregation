-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Copied from formal/EndToEnd/Bridge/Opening.lean at worktree-agent-a9857ef0660456f3e (96e3755):
-- the translations, the layouts, the weights (`stackClaims_eq`, `LayoutOK`, `layoutOK_layouts`) and
-- `readEntry_eq`, verbatim but in `namespace E2ECompleteness` (that file cannot be imported here: its
-- branch changes the Statement's opening seed). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0) through `PcsQuotient` and `WhirBridge`.
import PcsQuotient.Opening
import WhirBridge.Layouts

/-!
# The statement's layouts are F2's (a copy of Bridge-Defs' bridge)

The parts of `formal/EndToEnd/Bridge/Opening.lean` (Bridge-Defs, `96e3755`) that do not mention the
opening's seed, copied verbatim with the same declaration names in `E2ECompleteness` (a later
deduplication deletes this file and opens `Bridge`):

* **the layouts** (`layoutTr`: the same five fields): `layoutTr_witnessLayout`,
  `layoutTr_wiringLayout`, `layoutTr_quotientLayout`, for every size (`Layout::hidden` and
  `Layout::new` transcribed twice, `layoutTr_hidden`, `layoutTr_ofChunks_zero`);
* **a claim's weight on the stack and the gadget's** (`stackWeight_eq`, `gadgetWeight_eq`), hence
  **the opening's stack claims** (`stackClaims_eq`: the statement's `stackClaims` is F2's
  `Layout.stacking.claims`), for the layouts meeting `LayoutOK` (`layoutOK_layouts`);
* **the table read back from a stack** (`readEntry_eq`: the statement's `Layout.readEntry` is F2's
  `Layout.table`).
-/

namespace E2ECompleteness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The translations -/

/-- A lane of the statement's layout as F2's. -/
def laneTr : PcsQuotient.Lane → WhirBridge.Lane
  | .block b => .block b
  | .overflow => .overflow
  | .random => .random

/-- **The statement's layout as F2's**: the same five fields. -/
def layoutTr (L : PcsQuotient.Layout) : WhirBridge.Layout :=
  ⟨L.vars, L.logN, L.lanes.map laneTr, L.logPiece, L.pieces⟩

/-- A claim of the statement as F2's. -/
def claimTr (c : PcsQuotient.Claim) : WhirBridge.Claim := ⟨c.point, c.value⟩

@[simp] theorem layoutTr_vars (L : PcsQuotient.Layout) : (layoutTr L).vars = L.vars := rfl
@[simp] theorem layoutTr_logN (L : PcsQuotient.Layout) : (layoutTr L).logN = L.logN := rfl
@[simp] theorem layoutTr_lanes (L : PcsQuotient.Layout) :
    (layoutTr L).lanes = L.lanes.map laneTr := rfl
@[simp] theorem layoutTr_logPiece (L : PcsQuotient.Layout) :
    (layoutTr L).logPiece = L.logPiece := rfl
@[simp] theorem layoutTr_pieces (L : PcsQuotient.Layout) : (layoutTr L).pieces = L.pieces := rfl
@[simp] theorem layoutTr_logLane (L : PcsQuotient.Layout) :
    (layoutTr L).logLane = L.logLane := rfl

@[simp] theorem claimTr_point (c : PcsQuotient.Claim) : (claimTr c).point = c.point := rfl
@[simp] theorem claimTr_value (c : PcsQuotient.Claim) : (claimTr c).value = c.value := rfl

theorem laneTr_injective : Function.Injective laneTr := by
  intro a b h
  cases a <;> cases b <;> simp_all [laneTr]

/-! ## The layouts -/

/-- The lanes of a hidden layout, as the statement lists them. -/
theorem hiddenLanes_eq (blocks : List ℕ) (random : ℕ) :
    WhirBridge.Layout.hiddenLanes blocks random =
      ((blocks.take (min blocks.length 32)).map PcsQuotient.Lane.block ++
        List.replicate (32 - min blocks.length 32) PcsQuotient.Lane.random ++
        [PcsQuotient.Lane.overflow] ++ List.replicate random PcsQuotient.Lane.random ++
        (blocks.drop (min blocks.length 32)).map PcsQuotient.Lane.block).map laneTr := by
  simp [WhirBridge.Layout.hiddenLanes, WhirBridge.overflowLane, List.map_map, Function.comp_def,
    laneTr]

theorem layoutTr_hidden (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) (random s : ℕ) :
    layoutTr (PcsQuotient.Layout.hidden vars logChunk logN chunks random s) =
      WhirBridge.Layout.hidden vars logChunk logN chunks random s := by
  simp only [PcsQuotient.Layout.hidden, WhirBridge.Layout.hidden, WhirBridge.Layout.hiddenBlocks,
    WhirBridge.Layout.hiddenTails, PcsQuotient.overflowLaneIndex, PcsQuotient.laneFold,
    WhirBridge.laneFold, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, hiddenLanes_eq, layoutTr]
  congr 2
  rw [List.filterMap_map]
  congr 1
  funext x
  cases x <;> rfl

/-- **The witness table's layout** (`witness_layout`) is F2's, at every size. -/
theorem layoutTr_witnessLayout (logRows : ℕ) :
    layoutTr (PcsQuotient.witnessLayout logRows) = WhirBridge.witnessLayout logRows := by
  rw [PcsQuotient.witnessLayout, layoutTr_hidden]
  rfl

theorem quotientChunks_eq (m : ℕ) :
    PcsQuotient.quotientChunks m = WhirBridge.quotientChunks m WhirBridge.qSpill 64 := rfl

/-- **The quotient table's layout** (`quotient_layout`) is F2's, at every size. -/
theorem layoutTr_quotientLayout (logRows : ℕ) :
    layoutTr (PcsQuotient.quotientLayout logRows) = WhirBridge.quotientLayout logRows := by
  rw [PcsQuotient.quotientLayout, layoutTr_hidden, quotientChunks_eq]
  rfl

/-- `Layout::new` of one chunk `0` (the wiring table's), transcribed twice. -/
theorem layoutTr_ofChunks_zero (vars logChunk logN len : ℕ) :
    layoutTr (PcsQuotient.Layout.ofChunks vars logChunk logN [(0, len)]) =
      WhirBridge.Layout.new vars logChunk logN [(0, len)] := by
  simp [PcsQuotient.Layout.ofChunks, WhirBridge.Layout.new, WhirBridge.Layout.newBlocks, layoutTr,
    List.map_map, Function.comp_def, laneTr, PcsQuotient.laneFold, WhirBridge.laneFold]

/-- **The wiring table's layout** (`wiring_layout`) is F2's, at every size. -/
theorem layoutTr_wiringLayout (logRows : ℕ) :
    layoutTr (PcsQuotient.wiringLayout logRows) = WhirBridge.wiringLayout logRows := by
  rw [PcsQuotient.wiringLayout, layoutTr_ofChunks_zero]
  rfl

/-! ## The weights -/

theorem testBit_iff_shift (i k : ℕ) : i.testBit k = decide ((i >>> k) % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]

/-- `eq(point, bits of index)`, transcribed twice. -/
theorem eqBits_eq (p : List E) (i : ℕ) : PcsQuotient.eqBits p i = WhirBridge.eqBits p i := by
  unfold PcsQuotient.eqBits WhirBridge.eqBits
  apply List.foldl_ext
  intro w pk _
  obtain ⟨q, k⟩ := pk
  simp only [testBit_iff_shift, decide_eq_true_eq]

theorem laneScales_eq (L : PcsQuotient.Layout) (p : List E) :
    (layoutTr L).laneScales p = (L.scales p).1 := by
  simp only [WhirBridge.Layout.laneScales, PcsQuotient.Layout.scales, layoutTr_lanes,
    layoutTr_logLane, List.map_map]
  congr 1
  funext l
  cases l <;> simp [laneTr, eqBits_eq]

theorem pieceScales_eq (L : PcsQuotient.Layout) (p : List E) :
    (layoutTr L).pieceScales p = (L.scales p).2 := by
  simp only [WhirBridge.Layout.pieceScales, PcsQuotient.Layout.scales, layoutTr_logPiece,
    layoutTr_pieces]
  cases L.logPiece <;> simp [eqBits_eq]

/-- F2's `on_blocks` on the translated lanes, as the statement writes it. -/
theorem onBlocks_eq (ls : List PcsQuotient.Lane) (sc high : List E) :
    WhirBridge.onBlocks (ls.map laneTr) sc (WhirBridge.laneEqs (ls.map laneTr).length high) =
      ls.zipIdx.foldl (fun sum ll => match ll.1 with
        | PcsQuotient.Lane.block _ => sum + sc.getD ll.2 0 * PcsQuotient.eqBits high ll.2
        | _ => sum) 0 := by
  unfold WhirBridge.onBlocks
  rw [List.zipIdx_map, List.foldl_map]
  apply List.foldl_ext
  intro sum ll hll
  obtain ⟨a, i⟩ := ll
  have hi := (List.mem_zipIdx' hll).1
  cases a <;> simp [WhirBridge.onStep, laneTr, WhirBridge.laneEqs, List.getD_eq_getElem?_getD, hi,
    eqBits_eq]

theorem findIdx_laneTr (ls : List PcsQuotient.Lane) :
    (ls.map laneTr).findIdx (· == WhirBridge.Lane.overflow) =
      ls.findIdx (fun l => decide (l = PcsQuotient.Lane.overflow)) := by
  rw [List.findIdx_map]
  congr 1
  funext l
  cases l <;> simp [laneTr]

/-- The overflow lane, found twice: where F2 finds one, the statement finds the same. -/
theorem overflowLane_eq (ls : List PcsQuotient.Lane)
    (h : (ls.map laneTr).findIdx (· == WhirBridge.Lane.overflow) < ls.length) :
    (ls.findIdx? (· = PcsQuotient.Lane.overflow)).getD 0 =
      (ls.map laneTr).findIdx (· == WhirBridge.Lane.overflow) := by
  rw [findIdx_laneTr] at h ⊢
  rw [(List.findIdx?_eq_some_iff_findIdx_eq.mpr ⟨h, rfl⟩)]
  rfl

/-- **A claim's weight on the stack is F2's** (`stackWeight` = `Layout.claimWeight`), for a public
layout, or a hidden one with an overflow lane. -/
theorem stackWeight_eq (L : PcsQuotient.Layout)
    (hov : L.logPiece.isSome → (layoutTr L).overflow < L.lanes.length) (c : PcsQuotient.Claim)
    (x : List E) : PcsQuotient.stackWeight L c x = (layoutTr L).claimWeight (claimTr c) x := by
  simp only [PcsQuotient.stackWeight, WhirBridge.Layout.claimWeight, WhirBridge.Layout.term,
    WhirBridge.Layout.part, laneScales_eq, pieceScales_eq, layoutTr_logPiece, layoutTr_logLane,
    layoutTr_lanes, claimTr_point, onBlocks_eq, WhirBridge.eqZ_eq_eqEval, WhirBridge.onePlusProd]
  rcases h : L.logPiece with _ | s
  · rfl
  · have ho := hov (by simp [h])
    have hov' : L.overflowLane = (layoutTr L).overflow := overflowLane_eq L.lanes ho
    have hget : (WhirBridge.laneEqs (L.lanes.map laneTr).length (List.drop L.logLane x)).getD
        (layoutTr L).overflow 0 = PcsQuotient.eqBits (List.drop L.logLane x) L.overflowLane := by
      rw [hov']
      simp [WhirBridge.laneEqs, List.getD_eq_getElem?_getD, ho, eqBits_eq]
    simp only [hget, ← eqBits_eq]
    rfl

theorem kOfLane_one : K.ofLane 1 = 1 := rfl

theorem kOfLane_zero : K.ofLane 0 = 0 := rfl

theorem gadgetBeta_eq (i : ℕ) : PcsQuotient.gadgetBeta i = WhirBridge.gadgetBeta i := by
  unfold PcsQuotient.gadgetBeta WhirBridge.gadgetBeta
  split_ifs <;> simp_all [kOfLane_one, kOfLane_zero]

/-- **The gadget's weight on the stack is F2's**, for a hidden layout of at least `33` lanes (the
gadget's lanes `0, 1, 30, 31, 32` all lanes of the stack). -/
theorem gadgetWeight_eq (L : PcsQuotient.Layout) {s : ℕ} (hs : L.logPiece = some s)
    (hn : 33 ≤ L.lanes.length) (x : List E) :
    PcsQuotient.gadgetWeight L x = (layoutTr L).gadgetWeight x := by
  have h0 : 0 < L.lanes.length := by omega
  have h1 : 1 < L.lanes.length := by omega
  have h30 : 30 < L.lanes.length := by omega
  have h31 : 31 < L.lanes.length := by omega
  have h32 : 32 < L.lanes.length := by omega
  simp [PcsQuotient.gadgetWeight, WhirBridge.Layout.gadgetWeight, WhirBridge.gadgetSum,
    WhirBridge.Layout.gadgetParts, hs, List.range_succ, WhirBridge.laneEqs,
    List.getD_eq_getElem?_getD, h0, h1, h30, h31, h32, eqBits_eq, PcsQuotient.gadgetLanes,
    WhirBridge.gadgetLanes, WhirBridge.overflowLane, PcsQuotient.overflowLaneIndex,
    PcsQuotient.Layout.gadgetEntry, WhirBridge.gadgetEntry, PcsQuotient.gadgetSize,
    WhirBridge.gadget, gadgetBeta_eq]

/-- **What the weight bridge needs of a layout**: public, or hidden with an overflow lane and the
gadget's lanes among its at least `33` lanes. -/
def LayoutOK (L : PcsQuotient.Layout) : Prop :=
  L.logPiece = none ∨
    ((layoutTr L).overflow < L.lanes.length ∧ 33 ≤ L.lanes.length)

/-- **The opening's stack claims are F2's** (`stackClaims` = `Layout.stacking.claims`): the claims'
weights and values, then a hidden layout's gadget, of value zero. -/
theorem stackClaims_eq (L : PcsQuotient.Layout) (hL : LayoutOK L) (claims : List PcsQuotient.Claim) :
    PcsQuotient.stackClaims L claims = (layoutTr L).stacking.claims (claims.map claimTr) := by
  have hov : L.logPiece.isSome → (layoutTr L).overflow < L.lanes.length := by
    intro h
    rcases hL with hL | hL
    · simp [hL] at h
    · exact hL.1
  simp only [PcsQuotient.stackClaims, WhirBridge.Stacking.claims, WhirBridge.Layout.stacking,
    List.map_map]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, claimTr_value]
    exact Prod.ext (funext fun x => stackWeight_eq L hov c x) rfl
  · rcases h : L.logPiece with _ | s
    · simp [WhirBridge.Layout.extra, h]
    · have hn : 33 ≤ L.lanes.length := by
        rcases hL with hL | hL
        · simp [hL] at h
        · exact hL.2
      simp only [WhirBridge.Layout.extra, layoutTr_logPiece, h, Option.isSome_some, ↓reduceIte]
      exact congrArg (fun f => [(f, (0 : E))]) (funext fun x => gadgetWeight_eq L h hn x)

theorem layoutOK_of (L : PcsQuotient.Layout) {W : WhirBridge.Layout} (hW : layoutTr L = W)
    (h : W.logPiece = none ∨ (W.overflow < W.lanes.length ∧ 33 ≤ W.lanes.length)) : LayoutOK L := by
  subst hW
  simpa [LayoutOK] using h

/-- The three layouts meet `LayoutOK` at every supported size (F2's `layouts_shape`). -/
theorem layoutOK_layouts (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows) :
    LayoutOK (PcsQuotient.witnessLayout r) ∧ LayoutOK (PcsQuotient.wiringLayout r) ∧
      LayoutOK (PcsQuotient.quotientLayout r) := by
  obtain ⟨hw, -, hq, hwo, hqo, -⟩ := WhirBridge.layouts_shape r h1 h2
  refine ⟨layoutOK_of _ (layoutTr_witnessLayout r) (Or.inr ⟨by omega, by omega⟩),
    layoutOK_of _ (layoutTr_wiringLayout r) (Or.inl rfl),
    layoutOK_of _ (layoutTr_quotientLayout r) (Or.inr ⟨by omega, by omega⟩)⟩

/-! ## The table read back from a stack -/

theorem findIdx?_nat_eq (l : List ℕ) (p : ℕ) :
    l.findIdx? (fun x => decide (x = p)) = l.findIdx? (· == p) := by
  congr 1

theorem findIdx?_block_eq (ls : List PcsQuotient.Lane) (b : ℕ) :
    ls.findIdx? (fun x => decide (x = PcsQuotient.Lane.block b)) =
      (ls.map laneTr).findIdx? (· == WhirBridge.Lane.block b) := by
  rw [List.findIdx?_map]
  congr 1
  funext x
  cases x with
  | block b' =>
    by_cases h : b' = b
    · subst h; simp [laneTr]
    · have h' : (WhirBridge.Lane.block b' == WhirBridge.Lane.block b) = false := by
        simpa using h
      simp [laneTr, h, h']
  | overflow => rfl
  | random => rfl

/-- **The statement's read-back of a hidden table is F2's** (`Layout.readEntry` = `Table::read` =
F2's `Layout.table`), the stack given by its words, for a hidden layout with an overflow lane (the
witness and quotient layouts, `layoutOK_layouts`). -/
theorem readEntry_eq (L : PcsQuotient.Layout) {s : ℕ} (hs : L.logPiece = some s)
    (hov : (layoutTr L).overflow < L.lanes.length) (q : Column L.logN) (i : ℕ) :
    L.readEntry (fun j => q.values.getD j 0) i = (layoutTr L).table q i := by
  have hov' : L.overflowLane = (layoutTr L).overflow := overflowLane_eq L.lanes hov
  simp only [PcsQuotient.Layout.readEntry, WhirBridge.Layout.table, WhirBridge.Layout.readHidden,
    layoutTr_logPiece, hs, layoutTr_pieces, layoutTr_lanes, layoutTr_logLane, Nat.shiftRight_eq_div_pow,
    findIdx?_nat_eq, findIdx?_block_eq, WhirBridge.stackAt, Nat.and_two_pow_sub_one_eq_mod, hov']
  rcases hk : L.pieces.findIdx? (· == i / 2 ^ s) with _ | k
  · rcases hl : (L.lanes.map laneTr).findIdx?
        (· == WhirBridge.Lane.block (i / 2 ^ s / 2 ^ (L.logLane - s))) with _ | l
    · rfl
    · simp only
      congr 1
      ring
  · simp only
    congr 1
    ring

end E2ECompleteness

/-- info: 'E2ECompleteness.layoutTr_witnessLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.layoutTr_witnessLayout

/-- info: 'E2ECompleteness.layoutTr_wiringLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.layoutTr_wiringLayout

/-- info: 'E2ECompleteness.layoutTr_quotientLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.layoutTr_quotientLayout

/-- info: 'E2ECompleteness.eqBits_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.eqBits_eq

/-- info: 'E2ECompleteness.stackWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.stackWeight_eq

/-- info: 'E2ECompleteness.gadgetWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.gadgetWeight_eq

/-- info: 'E2ECompleteness.stackClaims_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.stackClaims_eq

/-- info: 'E2ECompleteness.layoutOK_layouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.layoutOK_layouts

/-- info: 'E2ECompleteness.readEntry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.readEntry_eq
