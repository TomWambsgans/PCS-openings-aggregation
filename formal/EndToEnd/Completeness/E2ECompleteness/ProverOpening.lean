-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Adapts leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `corr_openingFast` (`lean_vm/LeanVM/Prover/Whir.lean`) for
-- `corr_openingScript`, `toList_basisTableA` (`WhirBasis.lean`) for `weightTable_eq`,
-- `stackWordFast_eq` (`Ntt.lean`), and uses `runFrom_eq_proveFromM`, `runFrom_corr` (`Refine.lean`,
-- `Corr.lean`), `proveM_id` (`Protocol/Compile/Rom/Prover.lean`), `runI_openingProgram`
-- (`Protocol/Whir/Complete/Opening.lean`), `runProof_prove`, `prove_ne_none`, `findNonce_eq_none_iff`
-- (`Protocol/Compile/Prover.lean`). The layout translation (`laneTr`, `layoutTr`, `stackWeight_eq`,
-- `gadgetWeight_eq`, `runWithHash_bind`) is copied from this repository's
-- `formal/EndToEnd/Bridge/Opening.lean` (Bridge-Defs).
import E2ECompleteness.ProverDefs
import WhirBridge
import Completeness.Opening
import LeanVM.Prover.Whir
import LeanVM.Prover.Refine
import LeanVM.Protocol.Whir.Complete.Opening
import LeanVM.Protocol.Compile.Rom.Prover

/-!
# The Statement's WHIR opening prover is accepted

`proveOpeningWithH` (`WithHash.lean`, the Statement's `proveOpeningWith` with Keccak-256 explicit)
runs `openingScript` (mumbai's `openingFast` with the protocol's weight table `weightTable`) against
the verifier's program. Here:

* **`weightTable_eq`**: the weight table is the batched weight of the opening's stack claims on the
  cube, in WHIR's variable order (mumbai's `basisTable`): at stack position `y + 2^ℓ·l`, a claim's
  weight `stackWeight` is `Layout.weightAt`'s closed form (`stackWeight_cube`) and the gadget's
  `gadgetWeight` is `Layout.gadgetAt` (`gadgetWeight_cube`), for a layout of the shape
  `WeightShape` (true of the three layouts at `log_rows = 22`, `weightShape_layouts`).
* **`corr_openingScript`**: `openingScript` makes the moves of mumbai's specification
  `honestOpening` on the stack as a column (`colOf`).
* **`proveOpeningWithH_eq_prove`**: at a pure hash and permutation, the Statement's opening prover
  is mumbai's compiled honest prover `prove` of `openingProgram` (commit the stack, open, accept)
  with the honest strategy `openingProver`, from the opening's sponge.
* **`openingWithH_proveOpeningWithH`**: the Statement's opening check accepts every proof the
  Statement's opening prover produces, for claims of the table's length that hold of the stack.
* **`exists_failed_pow_opening`**: the prover fails only at a `17`-bit proof of work at a sponge
  where every nonce below `fuel` fails.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient
open LeanVM.Protocol.EndToEnd (boolPoint)

set_option autoImplicit false

namespace E2ECompleteness

/-! ## The Statement's layouts as F2's (copied from Bridge-Defs) -/

namespace OpeningTr

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

/-- The overflow lane of a layout with one: F2's is the statement's, and it is a lane. -/
theorem overflow_tr {L : PcsQuotient.Layout} (hov : L.lanes[L.overflowLane]? = some .overflow) :
    (layoutTr L).overflow = L.overflowLane ∧ L.overflowLane < L.lanes.length := by
  have hlt : L.overflowLane < L.lanes.length := (List.getElem?_eq_some_iff.1 hov).1
  have hmem : PcsQuotient.Lane.overflow ∈ L.lanes := List.mem_of_getElem? hov
  have h : (L.lanes.map laneTr).findIdx (· == WhirBridge.Lane.overflow) < L.lanes.length := by
    rw [findIdx_laneTr]
    exact List.findIdx_lt_length_of_exists ⟨_, hmem, by simp⟩
  exact ⟨(overflowLane_eq L.lanes h).symm, hlt⟩

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

end OpeningTr

open OpeningTr

/-! ## The layouts' shape -/

/-- **What the weight table's proof needs of a layout**: lanes of at least `2^0` words in a stack of
at most `64` variables, at most `64` lanes, the table's variables at least a lane's; in a hidden
layout, pieces `2^s` shorter than a lane and at least the gadget's `9` entries, fewer pieces than a
lane holds, at least `33` lanes (the gadget's lanes `0, 1, 30, 31, 32` among them), and exactly one
overflow lane, `Layout.overflowLane`. -/
def WeightShape (L : PcsQuotient.Layout) : Prop :=
  6 ≤ L.logN ∧ L.logN ≤ 64 ∧ L.lanes.length ≤ 64 ∧ L.logLane ≤ L.vars ∧
    ∀ s ∈ L.logPiece, s < L.logLane ∧ gadgetSize ≤ 2 ^ s ∧
      L.pieces.length < 2 ^ (L.logLane - s) ∧ 33 ≤ L.lanes.length ∧
      L.lanes[L.overflowLane]? = some .overflow ∧
      ∀ l < L.lanes.length, L.lanes[l]? = some .overflow → l = L.overflowLane

instance (L : PcsQuotient.Layout) : Decidable (WeightShape L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- **The three layouts at `log_rows = 22` have the shape.** -/
theorem weightShape_layouts :
    WeightShape (witnessLayout 22) ∧ WeightShape (wiringLayout 22) ∧
      WeightShape (quotientLayout 22) := by
  decide +kernel

/-- **The three layouts at `log_rows = 22` are admissible** at rate `1/2`. -/
theorem admissible_layouts :
    Whir.Admissible (witnessLayout 22).logN PcsQuotient.logInvRate ∧
      Whir.Admissible (wiringLayout 22).logN PcsQuotient.logInvRate ∧
      Whir.Admissible (quotientLayout 22).logN PcsQuotient.logInvRate := by
  decide +kernel

/-! ## The weights at a cube point -/

theorem getD_ofFn' {α : Type} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem toArray_getD' {α : Type} (l : List α) (i : ℕ) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- A stack position `y + 2^ℓ·l` as a cube point: `y`'s, then the lane's. -/
theorem boolPoint_lane {L : PcsQuotient.Layout} (h6 : 6 ≤ L.logN) {y : ℕ}
    (hy : y < 2 ^ L.logLane) (l : ℕ) :
    boolPoint L.logN (y + 2 ^ L.logLane * l) =
      boolPoint L.logLane y ++ boolPoint WhirBridge.laneFold l := by
  have h : L.logN = L.logLane + WhirBridge.laneFold := by
    simp only [PcsQuotient.Layout.logLane, PcsQuotient.laneFold, WhirBridge.laneFold]
    omega
  rw [h]
  exact LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ hy

/-- The statement's `eq_bits` at a cube point is a Kronecker delta. -/
theorem eqBits_cube' {m i j : ℕ} (hi : i < 2 ^ m) (hj : j < 2 ^ m) :
    PcsQuotient.eqBits (boolPoint m j) i = if i = j then 1 else 0 := by
  rw [eqBits_eq]
  exact WhirBridge.eqBits_cube hi hj

/-- Entry `y` of the equality kernel of the point's first `n` coordinates. -/
theorem eqKernelA_getD_take (p : List E) {n y : ℕ} (hn : n ≤ p.length) (hy : y < 2 ^ n) :
    (eqKernelA (p.take n)).getD y 0 = eqEval (boolPoint n y) (p.take n) := by
  have hl : (p.take n).length = n := by simp [hn]
  rw [Enc.eqKernelA_getD, LeanVM.Protocol.Whir.Complete.getD_eqKernel _ _ (by rw [hl]; exact hy),
    hl]

/-- `eq` of a lane entry `y` and a lane point, below and above a piece of `2^s`. -/
theorem eqEval_split (P : List E) {ℓ s y : ℕ} (hP : P.length = ℓ) (hs : s ≤ ℓ)
    (hy : y < 2 ^ ℓ) :
    eqEval (boolPoint ℓ y) P =
      WhirBridge.eqZ (P.take s) (boolPoint s (y % 2 ^ s)) *
        eqEval (P.drop s) (boolPoint (ℓ - s) (y / 2 ^ s)) := by
  have hb : boolPoint ℓ y = boolPoint s (y % 2 ^ s) ++ boolPoint (ℓ - s) (y / 2 ^ s) := by
    have h := LeanVM.Protocol.Whir.Complete.boolPoint_add s (ℓ - s) (y % 2 ^ s) (y / 2 ^ s)
      (Nat.mod_lt _ (by positivity))
    rwa [Nat.mod_add_div, Nat.add_sub_cancel' hs] at h
  have _ := hy
  conv_lhs => rw [hb, ← List.take_append_drop s P]
  rw [LeanVM.Protocol.Whir.Complete.eqEval_append _ _ _ _ (by simp [hP, hs]),
    WhirBridge.eqZ_eq_eqEval, LeanVM.Protocol.Whir.Complete.eqEval_comm (P.take s),
    LeanVM.Protocol.Whir.Complete.eqEval_comm (P.drop s)]

/-- A lane's scale, read from the lanes. -/
theorem scales_fst_getD (L : PcsQuotient.Layout) (p : List E) (l : ℕ) :
    (L.scales p).1.getD l 0 = match L.lanes[l]? with
      | some (.block b) => PcsQuotient.eqBits (p.drop L.logLane) b
      | _ => 0 := by
  simp only [PcsQuotient.Layout.scales, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases L.lanes[l]? with _ | (b | _ | _) <;> rfl

/-- The pieces' scales of a hidden layout. -/
theorem scales_snd (L : PcsQuotient.Layout) {s : ℕ} (hs : L.logPiece = some s) (p : List E) :
    (L.scales p).2 = L.pieces.map (PcsQuotient.eqBits (p.drop s)) := by
  simp only [PcsQuotient.Layout.scales, hs]

/-- **A claim's weight at a stack position** `y + 2^ℓ·l` is `Layout.weightAt`'s closed form. -/
theorem stackWeight_cube {L : PcsQuotient.Layout} (hL : WeightShape L) (c : PcsQuotient.Claim)
    (hc : c.point.length = L.vars) {l y : ℕ} (hl : l < 64) (hy : y < 2 ^ L.logLane) :
    PcsQuotient.stackWeight L c (boolPoint L.logN (y + 2 ^ L.logLane * l)) =
      L.weightAt (L.claimWeights c) l y := by
  obtain ⟨h6, -, hN, hℓV, hhid⟩ := hL
  have hx := boolPoint_lane h6 hy l
  have hlen : (boolPoint L.logLane y).length = L.logLane := WhirBridge.boolPoint_length' _ _
  have hpl : (c.point.take L.logLane).length = L.logLane := by rw [List.length_take, hc]; omega
  have hNw : (L.lanes.map laneTr).length ≤ 2 ^ WhirBridge.laneFold := by
    rw [List.length_map]; exact hN
  have hl' : l < 2 ^ WhirBridge.laneFold := hl
  rcases hs : L.logPiece with _ | s
  · -- a public layout
    rw [stackWeight_eq L (by simp [hs]) c, WhirBridge.claimWeight_public _ _ hs, hx]
    simp only [layoutTr_logLane, claimTr_point, layoutTr_lanes, laneScales_eq]
    rw [List.take_left' hlen, List.drop_left' hlen, WhirBridge.onBlocks_cube _ _ hNw hl',
      WhirBridge.eqZ_eq_eqEval, LeanVM.Protocol.Whir.Complete.eqEval_comm]
    simp only [PcsQuotient.Layout.weightAt, PcsQuotient.Layout.claimWeights, hs, toArray_getD']
    rw [eqKernelA_getD_take c.point (by omega) hy, scales_fst_getD]
    rcases hlane : L.lanes[l]? with _ | (b | _ | _) <;>
      simp [List.getElem?_map, hlane, laneTr, mul_comm]
  · -- a hidden layout
    obtain ⟨hsℓ, h9, hheld, -, hov, hovu⟩ := hhid s hs
    obtain ⟨hovtr, hovlt⟩ := overflow_tr hov
    rw [stackWeight_eq L (fun _ ↦ hovtr ▸ hovlt) c, WhirBridge.claimWeight_hidden _ _ hs, hx]
    simp only [layoutTr_logLane, claimTr_point, layoutTr_lanes, laneScales_eq, pieceScales_eq]
    rw [min_eq_left hsℓ.le, List.take_append_of_le_length (by omega),
      WhirBridge.boolPoint_take' _ hsℓ.le, ← WhirBridge.boolPoint_mod', List.take_left' hlen,
      List.drop_left' hlen, WhirBridge.boolPoint_drop']
    have hal : ((c.point.take L.logLane).drop s).length = L.logLane - s := by
      rw [List.length_drop, hpl]
    have hkm : y / 2 ^ s < 2 ^ (L.logLane - s) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hsℓ.le]
      exact hy
    have hps : (L.scales c.point).2.length = L.pieces.length := by
      rw [scales_snd L hs, List.length_map]
    rw [WhirBridge.blockTerm_cube _ hal hkm, WhirBridge.onBlocks_cube _ _ hNw hl',
      WhirBridge.laneEq_cube hNw (by rw [List.length_map, hovtr]; exact hovlt) hl', hovtr,
      WhirBridge.pieces_cube _ (by rw [hps]; exact hheld) hkm, hps]
    simp only [PcsQuotient.Layout.weightAt, PcsQuotient.Layout.claimWeights, hs, toArray_getD',
      Option.getD_some, Nat.shiftRight_eq_div_pow]
    by_cases hk0 : y / 2 ^ s = 0
    · simp [hk0]
    · rw [if_neg hk0, if_neg hk0]
      rcases hlane : L.lanes[l]? with _ | lane
      · have hne : L.overflowLane ≠ l := fun h ↦ by rw [h, hlane] at hov; cases hov
        simp [List.getElem?_map, hlane, hne, List.getD_eq_getElem?_getD]
      · rcases lane with b | _ | _
        · -- a block lane
          have hne : L.overflowLane ≠ l := fun h ↦ by rw [h, hlane] at hov; cases hov
          simp only [List.getElem?_map, hlane, Option.map_some, laneTr, hne, if_false, mul_zero,
            add_zero, List.getD_eq_getElem?_getD, Option.getD_some]
          rw [← List.getD_eq_getElem?_getD, scales_fst_getD, hlane,
            eqKernelA_getD_take c.point (by omega) hy,
            eqEval_split (c.point.take L.logLane) hpl hsℓ.le hy, List.take_take,
            min_eq_left hsℓ.le]
          simp only
          ring
        · -- the overflow lane
          have hlo : l = L.overflowLane :=
            hovu l (List.getElem?_eq_some_iff.1 hlane).1 hlane
          subst hlo
          simp only [List.getElem?_map, hlane, Option.map_some, laneTr, if_true, mul_one,
            mul_zero, zero_add, List.getD_eq_getElem?_getD, Option.getD_some]
          rw [eqKernelA_getD_take c.point (by omega) (Nat.mod_lt _ (by positivity)), List.take_take,
            min_eq_left hsℓ.le, WhirBridge.eqZ_eq_eqEval,
            LeanVM.Protocol.Whir.Complete.eqEval_comm (c.point.take s)]
          by_cases hkp : 1 ≤ y / 2 ^ s ∧ y / 2 ^ s ≤ L.pieces.length
          · rw [if_pos hkp, ← List.getD_eq_getElem?_getD]
            ring
          · rw [if_neg hkp, ← List.getD_eq_getElem?_getD]
            have hge : (L.scales c.point).2.length ≤ y / 2 ^ s - 1 := by
              rw [hps]
              generalize y / 2 ^ s = k at hk0 hkp ⊢
              omega
            rw [List.getD_eq_default _ _ hge]
            ring
        · -- a random lane
          have hne : L.overflowLane ≠ l := fun h ↦ by rw [h, hlane] at hov; cases hov
          simp [List.getElem?_map, hlane, hne, laneTr, List.getD_eq_getElem?_getD]

/-- **The gadget's weight at a stack position** `y + 2^ℓ·l` is `Layout.gadgetAt`. -/
theorem gadgetWeight_cube {L : PcsQuotient.Layout} (hL : WeightShape L) {s : ℕ}
    (hs : L.logPiece = some s) {l y : ℕ} (hl : l < 64) (hy : y < 2 ^ L.logLane) :
    PcsQuotient.gadgetWeight L (boolPoint L.logN (y + 2 ^ L.logLane * l)) = L.gadgetAt l y := by
  obtain ⟨h6, -, -, -, hhid⟩ := hL
  obtain ⟨hsℓ, h9, -⟩ := hhid s hs
  have h9' : 9 ≤ 2 ^ s := h9
  have hlen : (boolPoint L.logLane y).length = L.logLane := WhirBridge.boolPoint_length' _ _
  have hsl : 2 ^ s ≤ 2 ^ L.logLane := Nat.pow_le_pow_right (by norm_num) hsℓ.le
  have hlane : ∀ l', l' < 64 →
      PcsQuotient.eqBits (boolPoint WhirBridge.laneFold l) l' = if l' = l then 1 else 0 :=
    fun l' hl' ↦ eqBits_cube' (m := WhirBridge.laneFold) hl' hl
  have hent : ∀ e, e < 2 ^ L.logLane →
      PcsQuotient.eqBits (boolPoint L.logLane y) e = if e = y then 1 else 0 :=
    fun e he ↦ eqBits_cube' he hy
  simp only [PcsQuotient.gadgetWeight, boolPoint_lane h6 hy l, List.take_left' hlen,
    List.drop_left' hlen, show List.range 3 = [0, 1, 2] from rfl, List.foldl_cons, List.foldl_nil,
    show PcsQuotient.gadgetLanes 0 = [0, 31] from rfl, show PcsQuotient.gadgetLanes 1 = [1, 30] from rfl,
    show PcsQuotient.gadgetLanes 2 = [32] from rfl, PcsQuotient.Layout.gadgetEntry, hs,
    Option.getD_some, PcsQuotient.gadgetSize]
  rw [hlane 0 (by norm_num), hlane 31 (by norm_num), hlane 1 (by norm_num), hlane 30 (by norm_num),
    hlane 32 (by norm_num)]
  simp only [PcsQuotient.Layout.gadgetAt, hs, PcsQuotient.gadgetSize]
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ s = t + 9 := ⟨2 ^ s - 9, by omega⟩
  rw [hent _ (by omega), hent _ (by omega), hent _ (by omega), hent _ (by omega), hent _ (by omega),
    hent _ (by omega), hent _ (by omega), hent _ (by omega), hent _ (by omega)]
  rw [ht]
  simp only [Nat.add_sub_cancel]
  -- each pattern's entries: `β` of `y`'s offset in the pattern's three entries, if `y` is one
  have hB : ∀ g : ℕ, ((0 + gadgetBeta 0 * (if t + 3 * g + 0 = y then (1 : E) else 0)) +
      gadgetBeta 1 * (if t + 3 * g + 1 = y then 1 else 0)) +
      gadgetBeta 2 * (if t + 3 * g + 2 = y then 1 else 0) =
      if t + 3 * g ≤ y ∧ y < t + 3 * g + 3 then gadgetBeta (y - (t + 3 * g)) else 0 := by
    intro g
    by_cases h : t + 3 * g ≤ y ∧ y < t + 3 * g + 3
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 3 ∧ y = t + 3 * g + i :=
        ⟨y - (t + 3 * g), by omega, by omega⟩
      rw [if_pos h, Nat.add_sub_cancel_left]
      interval_cases i <;> simp
    · rw [if_neg h, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
  -- each pattern's lanes: one if `l` is one of them
  have hA2 : ∀ a b : ℕ, a ≠ b →
      ((0 + if a = l then (1 : E) else 0) + if b = l then 1 else 0) =
        if l = a ∨ l = b then 1 else 0 := by
    intro a b hab
    rcases eq_or_ne l a with rfl | ha
    · simp [Ne.symm hab]
    · rcases eq_or_ne l b with rfl | hb
      · simp [Ne.symm ha]
      · simp [Ne.symm ha, Ne.symm hb, ha, hb]
  have hA1 : (0 + if 32 = l then (1 : E) else 0) = if l = 32 then 1 else 0 := by
    by_cases h : l = 32 <;> simp [h, eq_comm]
  rw [hB 0, hB 1, hB 2, hA2 0 31 (by norm_num), hA2 1 30 (by norm_num), hA1]
  have hc0 : ([0, 31] : List ℕ).contains l = true ↔ (l = 0 ∨ l = 31) := by simp
  have hc1 : ([1, 30] : List ℕ).contains l = true ↔ (l = 1 ∨ l = 30) := by simp
  have hc2 : ([32] : List ℕ).contains l = true ↔ l = 32 := by simp
  by_cases hr : t ≤ y ∧ y < t + 9
  · rw [show y + 9 - (t + 9) = y - t by omega]
    rcases (show y < t + 3 ∨ (t + 3 ≤ y ∧ y < t + 6) ∨ t + 6 ≤ y by omega) with h | h | h
    · rw [if_pos (show t + 3 * 0 ≤ y ∧ y < t + 3 * 0 + 3 by omega),
        if_neg (show ¬ (t + 3 * 1 ≤ y ∧ y < t + 3 * 1 + 3) by omega),
        if_neg (show ¬ (t + 3 * 2 ≤ y ∧ y < t + 3 * 2 + 3) by omega),
        show (y - t) / 3 = 0 by omega, show (y - t) % 3 = y - (t + 3 * 0) by omega,
        show PcsQuotient.gadgetLanes 0 = [0, 31] from rfl]
      by_cases hl0 : l = 0 ∨ l = 31
      · rw [if_pos hl0, if_pos (show t ≤ y ∧ y < t + 9 ∧ ([0, 31] : List ℕ).contains l = true from
          ⟨hr.1, hr.2, hc0.2 hl0⟩)]
        ring
      · rw [if_neg hl0, if_neg (show ¬ (t ≤ y ∧ y < t + 9 ∧ ([0, 31] : List ℕ).contains l = true) from
          fun h' ↦ hl0 (hc0.1 h'.2.2))]
        ring
    · rw [if_neg (show ¬ (t + 3 * 0 ≤ y ∧ y < t + 3 * 0 + 3) by omega),
        if_pos (show t + 3 * 1 ≤ y ∧ y < t + 3 * 1 + 3 by omega),
        if_neg (show ¬ (t + 3 * 2 ≤ y ∧ y < t + 3 * 2 + 3) by omega),
        show (y - t) / 3 = 1 by omega, show (y - t) % 3 = y - (t + 3 * 1) by omega,
        show PcsQuotient.gadgetLanes 1 = [1, 30] from rfl]
      by_cases hl1 : l = 1 ∨ l = 30
      · rw [if_pos hl1, if_pos (show t ≤ y ∧ y < t + 9 ∧ ([1, 30] : List ℕ).contains l = true from
          ⟨hr.1, hr.2, hc1.2 hl1⟩)]
        ring
      · rw [if_neg hl1, if_neg (show ¬ (t ≤ y ∧ y < t + 9 ∧ ([1, 30] : List ℕ).contains l = true) from
          fun h' ↦ hl1 (hc1.1 h'.2.2))]
        ring
    · rw [if_neg (show ¬ (t + 3 * 0 ≤ y ∧ y < t + 3 * 0 + 3) by omega),
        if_neg (show ¬ (t + 3 * 1 ≤ y ∧ y < t + 3 * 1 + 3) by omega),
        if_pos (show t + 3 * 2 ≤ y ∧ y < t + 3 * 2 + 3 by omega),
        show (y - t) / 3 = 2 by omega, show (y - t) % 3 = y - (t + 3 * 2) by omega,
        show PcsQuotient.gadgetLanes 2 = [32] from rfl]
      by_cases hl2 : l = 32
      · rw [if_pos hl2, if_pos (show t ≤ y ∧ y < t + 9 ∧ ([32] : List ℕ).contains l = true from
          ⟨hr.1, hr.2, hc2.2 hl2⟩)]
        ring
      · rw [if_neg hl2, if_neg (show ¬ (t ≤ y ∧ y < t + 9 ∧ ([32] : List ℕ).contains l = true) from
          fun h' ↦ hl2 (hc2.1 h'.2.2))]
        ring
  · rw [if_neg (show ¬ (t + 3 * 0 ≤ y ∧ y < t + 3 * 0 + 3) by omega),
      if_neg (show ¬ (t + 3 * 1 ≤ y ∧ y < t + 3 * 1 + 3) by omega),
      if_neg (show ¬ (t + 3 * 2 ≤ y ∧ y < t + 3 * 2 + 3) by omega),
      if_neg (show ¬ (t ≤ y ∧ y < t + 9 ∧
        (PcsQuotient.gadgetLanes ((y + 9 - (t + 9)) / 3)).contains l = true) from
          fun h' ↦ hr ⟨h'.1, h'.2.1⟩)]
    ring

/-! ## The weight table -/

theorem dot_append_single : ∀ (scales A : List E) (g : E),
    dot scales (A ++ [g]) = dot scales A + scales.getD A.length 0 * g
  | [], A, g => by simp [dot]
  | s :: ss, [], g => by simp [dot]
  | s :: ss, a :: A, g => by
    rw [List.cons_append, Whir.Complete.dot_cons, Whir.Complete.dot_cons, dot_append_single ss A g]
    simp only [List.length_cons, List.getD_cons_succ]
    ring

/-- **The weight table's entry `i`**: the gadget's scale times `gadgetAt`, plus the claims' scales
times `weightAt`, at entry `⌊i / 64⌋` of lane `i mod 64`. -/
theorem weightTable_getD (L : PcsQuotient.Layout) (scales : List E)
    (claims : List PcsQuotient.Claim) {i : ℕ} (hi : i < 2 ^ L.logN) :
    (weightTable L scales claims).getD i 0 =
      scales.getD claims.length 0 * L.gadgetAt (i % 64) (i / 64) +
        dot scales (claims.map fun c ↦ L.weightAt (L.claimWeights c) (i % 64) (i / 64)) := by
  rw [weightTable, getD_ofFn' _ hi]
  dsimp only
  generalize scales.getD claims.length 0 * L.gadgetAt (i % 64) (i / 64) = init
  induction claims generalizing scales init with
  | nil => simp [dot]
  | cons c cs ih =>
    cases scales with
    | nil => simp [dot]
    | cons s ss =>
      simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons]
      rw [ih, Whir.Complete.dot_cons]
      ring

/-- **The weight table is the batched weight of the stack claims on the cube**, in WHIR's
variable order (mumbai's `basisTable`): for claims of the table's length on a layout of the shape
`WeightShape`, and any scales. -/
theorem weightTable_eq (L : PcsQuotient.Layout) (hL : WeightShape L)
    (claims : List PcsQuotient.Claim) (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (scales : List E) :
    (weightTable L scales claims).toList =
      Whir.Complete.basisTable L.logN scales (stackClaims L claims) := by
  have h6 : 6 ≤ L.logN := hL.1
  have hsz : (weightTable L scales claims).size = 2 ^ L.logN := by simp [weightTable]
  refine Enc.list_ext_getD (by simp [hsz, Whir.Complete.basisTable]) fun i hi ↦ ?_
  have hi' : i < 2 ^ L.logN := by simpa [hsz] using hi
  rw [Enc.toList_getD_E, weightTable_getD _ _ _ hi', Whir.Complete.basisTable,
    Whir.Complete.getD_tableOf _ _ _ hi']
  have hℓ : L.logN = 6 + L.logLane := by
    simp only [PcsQuotient.Layout.logLane, PcsQuotient.laneFold]
    omega
  have hrot : (boolPoint L.logN i).drop EndToEnd.laneBits ++
      (boolPoint L.logN i).take EndToEnd.laneBits =
        boolPoint L.logN (i / 64 + 2 ^ L.logLane * (i % 64)) := by
    have h := Whir.Complete.boolPoint_rotIndex 6 L.logLane i (by rw [← hℓ]; exact hi')
    rw [← hℓ, show L.logLane + 6 = L.logN by omega] at h
    exact h.symm
  have hy : i / 64 < 2 ^ L.logLane := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    rw [hℓ, pow_add] at hi'
    omega
  have hl : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hclaims : (claims.map fun c ↦ PcsQuotient.stackWeight L c
      (boolPoint L.logN (i / 64 + 2 ^ L.logLane * (i % 64)))) =
      claims.map fun c ↦ L.weightAt (L.claimWeights c) (i % 64) (i / 64) :=
    List.map_congr_left fun c hc ↦ stackWeight_cube hL c (hlen c hc) hl hy
  rw [hrot]
  simp only [Whir.Complete.batchedBasis, stackClaims, List.map_append, List.map_map,
    Function.comp_def]
  rcases hs : L.logPiece with _ | s
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.map_nil, List.append_nil,
      PcsQuotient.Layout.gadgetAt, hs, mul_zero, zero_add]
    rw [hclaims]
  · simp only [Option.isSome_some, ↓reduceIte, List.map_cons, List.map_nil]
    rw [dot_append_single, List.length_map, gadgetWeight_cube hL hs hl hy, hclaims, add_comm]

/-! ## The script makes the specification's moves -/

theorem getD_colOf (μ : ℕ) (a : Array K) {i : ℕ} (hi : i < 2 ^ μ) :
    (colOf μ a).values.toArray.getD i 0 = a.getD i 0 := by
  simp [colOf, Array.getD_eq_getD_getElem?, hi]

/-- The stack table of an array is its column's. -/
theorem stackTableA_colOf {μ : ℕ} (h6 : 6 ≤ μ) (stack : Array K) :
    stackTableA μ stack = stackTableA μ (colOf μ stack).values.toArray := by
  unfold stackTableA
  congr 1
  funext i
  have hi : i.val < 2 ^ (6 + (μ - 6)) := by rw [show 6 + (μ - 6) = μ by omega]; exact i.isLt
  have h := Whir.Complete.rotIndex_lt hi
  rw [show μ - 6 + 6 = μ by omega] at h
  rw [getD_colOf μ stack (show i.val / 2 ^ 6 + 2 ^ (μ - 6) * (i.val % 2 ^ 6) < 2 ^ μ from h)]

theorem toList_stackTableA_colOf {μ : ℕ} (h6 : 6 ≤ μ) (stack : Array K) :
    (stackTableA μ stack).toList = Whir.Complete.stackTable μ (colOf μ stack) := by
  rw [stackTableA_colOf h6, Enc.toList_stackTableA]

/-- **The Statement's opening script makes the moves of mumbai's honest opening** of the stack
claims on the stack's column: the same scalars sent and words committed, for every challenge and
opening. -/
theorem corr_openingScript (L : PcsQuotient.Layout) (hL : WeightShape L) (stack : Array K)
    (claims : List PcsQuotient.Claim) (hlen : ∀ c ∈ claims, c.point.length = L.vars) :
    Corr (fun _ _ ↦ True) (openingScript L stack claims)
      (Whir.Complete.honestOpening L.logN PcsQuotient.logInvRate (colOf L.logN stack)
        (stackClaims L claims)) := by
  have h6 : 6 ≤ L.logN := hL.1
  have hμ : L.logN ≤ 64 := hL.2.1
  simp only [openingScript, Whir.Complete.honestOpening]
  refine corrW_sampleE fun c ↦ ?_
  cases Whir.ladder L.logN PcsQuotient.logInvRate with
  | none => trivial
  | some config =>
    dsimp only
    simp only [Whir.Complete.hWhirRun]
    refine Corr.bind' (corr_roundA' (weightTable_eq L hL claims hlen _)
      (toList_stackTableA_colOf h6 stack)) fun quad _ hq ↦ ?_
    subst hq
    have := corr_levelsA hμ (Whir.Complete.stackTable L.logN (colOf L.logN stack)) config 0
      ⟨dot (powers c (stackClaims L claims).length) ((stackClaims L claims).map (·.2)),
        Whir.Complete.roundQuad
          (dot (powers c (stackClaims L claims).length) ((stackClaims L claims).map (·.2)))
          (Whir.Complete.basisTable L.logN (powers c (stackClaims L claims).length)
            (stackClaims L claims))
          (Whir.Complete.stackTable L.logN (colOf L.logN stack)), [], []⟩
      (weightTable L (powers c (stackClaims L claims).length) claims) (stackTableA L.logN stack)
      (by rw [toList_stackTableA_colOf h6]; rfl)
    rwa [weightTable_eq L hL claims hlen] at this

/-- The same, then nothing. -/
theorem corr_openingScript_ret (L : PcsQuotient.Layout) (hL : WeightShape L) (stack : Array K)
    (claims : List PcsQuotient.Claim) (hlen : ∀ c ∈ claims, c.point.length = L.vars) :
    Corr (fun _ _ ↦ True) (openingScript L stack claims)
      ((Whir.Complete.honestOpening L.logN PcsQuotient.logInvRate (colOf L.logN stack)
        (stackClaims L claims)).bind fun _ ↦ Script.ret ()) := by
  rw [← Script.bind_ret (openingScript L stack claims)]
  exact Corr.bind (fun _ _ _ ↦ trivial) _ _ (corr_openingScript L hL stack claims hlen)

/-! ## The prover is mumbai's compiled honest prover -/

/-- The opening program at an admissible shape: the stack's commitment, then the opening, then
accept. -/
theorem openingProgram_eq {μ R : ℕ} (hw : Whir.Admissible μ R) (sc : List StackClaim) :
    Whir.Complete.openingProgram μ R sc =
      Prog.commit (μ - 6 + R) (2 ^ 6)
        ((verifyStackedOpening μ R sc).bind fun _ ↦ Prog.ret true) := by
  obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hw
  simp only [Whir.Complete.openingProgram, commitStack, hc, Verifier.liftOption, Prog.bind_eq,
    Prog.pure_eq, Prog.ret_bind, levelShape, Prog.readCommitment]
  rfl

/-- **A trailing `return` changes no proof**: the runner sees only the moves. -/
theorem runFromWithHash_bind_ret {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) (fuel : ℕ) {α β : Type} (b : Bool) :
    ∀ (P : Prog α) (S : Option (Script β)) (sp : Sponge) (cs : List LeanVM.Prover.Tree),
      runFromWithHash H F fuel (P.bind fun _ ↦ Prog.ret b) S sp cs =
        runFromWithHash H F fuel P S sp cs := by
  intro P
  induction P with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]
  | sample k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]
  | grind bits k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]
  | commit ht w k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]
  | query i ps k ih => intro S sp cs; simp only [Prog.bind, runFromWithHash, ih]

/-- The executable stack word reads the array as its column. -/
theorem stackWordFast_colOf {μ : ℕ} (h6 : 6 ≤ μ) (R : ℕ) (a : Array K) :
    stackWordFast μ R a = stackWordFast μ R (colOf μ a).values.toArray := by
  have hb : ∀ {v u : ℕ}, v < 2 ^ (μ - 6) → u < 64 → v + 2 ^ (μ - 6) * u < 2 ^ μ := by
    intro v u hv hu
    have h := WhirBridge.lt_two_pow_add (b := 6) hv (show u < 2 ^ 6 from hu)
    rwa [show μ - 6 + 6 = μ by omega] at h
  have hcodes : stackCodes μ R a = stackCodes μ R (colOf μ a).values.toArray := by
    simp only [stackCodes]
    congr 1
    funext u
    congr 2
    funext v
    rw [getD_colOf μ a (hb v.isLt u.isLt)]
  funext p
  simp only [stackWordFast, stackWordFast.stackWordOf]
  rw [hcodes]
  split_ifs with hp
  · rfl
  · apply congrArg List.reverse
    refine List.map_congr_left fun u hu ↦ ?_
    have hfun : (fun x ↦ a.getD (LeanVM.Protocol.Whir.bitsToNat x + 2 ^ (μ - 6) * u) 0) =
        fun x ↦ (colOf μ a).values.toArray.getD (LeanVM.Protocol.Whir.bitsToNat x + 2 ^ (μ - 6) * u) 0 :=
      funext fun x ↦
        (getD_colOf μ a (hb (LeanVM.Protocol.Whir.bitsToNat_lt x) (List.mem_range.1 hu))).symm
    rw [hfun]

/-- **The Statement's opening prover is mumbai's compiled honest prover**, at a pure hash `H` and
permutation `F`: committing the stack (`commitWithH`) and running `openingScript` against the
verifier's program from the opening's sponge is `prove` of `openingProgram` (commit the stack's
word, open, accept) with the honest strategy `openingProver` of the stack's column, seeded with the
opening's sponge state. -/
theorem proveOpeningWithH_eq_prove (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (fuel : ℕ) (L : PcsQuotient.Layout) (hL : WeightShape L)
    (hw : Whir.Admissible L.logN PcsQuotient.logInvRate) (stack : Array K)
    (claims : List PcsQuotient.Claim) (hlen : ∀ c ∈ claims, c.point.length = L.vars) :
    proveOpeningWithH (m := Id) H F fuel L (commitWithH (m := Id) H L.logN stack) stack claims =
      Compile.prove H F
        (Whir.Complete.openingProgram L.logN PcsQuotient.logInvRate (stackClaims L claims))
        (Whir.Complete.openingProver L.logN PcsQuotient.logInvRate (colOf L.logN stack)
          (stackClaims L claims))
        (openingSpongeWithH (m := Id) H F L claims).state fuel := by
  have h6 : 6 ≤ L.logN := hL.1
  have hμ : L.logN ≤ 64 := hL.2.1
  have hword : (Whir.Complete.openingProver L.logN PcsQuotient.logInvRate (colOf L.logN stack)
      (stackClaims L claims)).word [] = stackWordFast L.logN 1 stack := by
    show Whir.Complete.stackWord _ _ = _
    rw [stackWordFast_colOf h6, Enc.stackWordFast_eq hμ]
  have hrun : ∀ (sp : Sponge) (cs : List LeanVM.Prover.Tree) (ht w : ℕ) (W : Word),
      proveFromM (m := Id) H F (Whir.Complete.openingProver L.logN PcsQuotient.logInvRate
          (colOf L.logN stack) (stackClaims L claims)) fuel
        ((verifyStackedOpening L.logN PcsQuotient.logInvRate (stackClaims L claims)).bind
          fun _ ↦ Prog.ret true) sp [Ev.commit ht w W] cs =
      runFromWithHash (m := Id) H F fuel
        (verifyStackedOpening L.logN PcsQuotient.logInvRate (stackClaims L claims))
        (some (openingScript L stack claims)) sp cs := by
    intro sp cs ht w W
    have hwalk : Script.walk (Whir.Complete.honestCommitOpening L.logN PcsQuotient.logInvRate
        (colOf L.logN stack) (stackClaims L claims) >>= fun _ ↦ Script.ret ()) [Ev.commit ht w W] =
        some ((Whir.Complete.honestOpening L.logN PcsQuotient.logInvRate (colOf L.logN stack)
          (stackClaims L claims)).bind fun _ ↦ Script.ret ()) := rfl
    rw [Whir.Complete.openingProver, ← runFrom_eq_proveFromM (m := Id) H F fuel _ _ _ sp _ cs hwalk,
      runFromWithHash_bind_ret]
    exact (runFrom_corr (m := Id) H F fuel _ (corr_openingScript_ret L hL stack claims hlen) sp cs).symm
  rw [← proveM_id, openingProgram_eq hw]
  simp only [proveM, proveFromM, proveOpeningWithH, commitWithH, hword, List.nil_append, hrun,
    bind_assoc, pure_bind, Option.map_map]
  rfl

/-! ## The opening check accepts -/

/-- Running a sequence is running its first part, then the rest from the state it leaves (copied
from Bridge-Defs). -/
theorem runWithHash_bind {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) {α β : Type} (P : Prog α) (f : α → Prog β) :
    ∀ s : ProgState, runWithHash H F (P.bind f) s = runWithHash H F P s >>= fun o => match o with
      | some (a, s') => runWithHash H F (f a) s'
      | none => pure none := by
  induction P with
  | ret a => intro s; simp [Prog.bind, runWithHash]
  | fail => intro s; simp [Prog.bind, runWithHash]
  | read k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split <;> simp [ih]
  | sample k ih =>
    intro s
    simp [Prog.bind, runWithHash, ih]
  | grind b k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext sp; congr 1; funext cs
      split <;> simp [ih]
  | commit h w k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp only [bind_assoc]
      congr 1; funext sp0; congr 1; funext sp1
      split <;> simp [ih]
    · simp
  | query i ps k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext o
      split <;> simp [ih]

theorem id_bind_eq' {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem id_pure_eq' {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- **The Statement's opening check is the compiled verifier of `openingProgram`** from the
opening's sponge, on a proof whose first two scalars encode the expected root, for claims of the
table's length, at an admissible shape. -/
theorem openingWithH_eq_runProof (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (L : PcsQuotient.Layout) (hw : Whir.Admissible L.logN PcsQuotient.logInvRate)
    (claims : List PcsQuotient.Claim) (hne : claims ≠ [])
    (hlen : ∀ c ∈ claims, c.point.length = L.vars) (root : Digest) (x0 x1 : E) (rest : List E)
    (os : List Opening) (hd : digestOfScalars (x0, x1) = some root) :
    openingWithH (m := Id) H F L root claims ⟨x0 :: x1 :: rest, os⟩ =
      runProofWithHash (m := Id) H F
        (Whir.Complete.openingProgram L.logN PcsQuotient.logInvRate (stackClaims L claims))
        (openingSpongeWithH (m := Id) H F L claims).state ⟨x0 :: x1 :: rest, os⟩ := by
  have hall : (claims.all fun c ↦ decide (c.point.length = L.vars)) = true :=
    List.all_eq_true.2 fun c hc ↦ decide_eq_true (hlen c hc)
  rw [openingProgram_eq hw]
  simp only [openingWithH, runProofWithHash, runWithHash, hd, ne_eq, hne, not_false_eq_true, hall,
    and_self, ↓reduceIte, runWithHash_bind, List.nil_append, id_bind_eq', id_pure_eq',
    show (⟨(openingSpongeWithH (m := Id) H F L claims).state, []⟩ : Sponge) =
      openingSpongeWithH (m := Id) H F L claims from rfl,
    show PcsQuotient.laneFold = 6 from rfl, show (2 : ℕ) ^ 6 = 64 from rfl]
  split <;> rename_i h <;> simp [h]

/-- **The Statement's opening check accepts the Statement's opening prover's proof**, at a pure
hash `H` and permutation `F`: for a layout of the shape `WeightShape` at an admissible size, claims
(at least one) of the table's length whose stack claims hold of the stack's column and have
multilinear weights, every proof `proveOpeningWithH` produces from the stack's commitment is
accepted against the commitment's root. Generic in the opening's sponge. -/
theorem openingWithH_proveOpeningWithH (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (fuel : ℕ) (L : PcsQuotient.Layout) (hL : WeightShape L)
    (hw : Whir.Admissible L.logN PcsQuotient.logInvRate) (stack : Array K)
    (claims : List PcsQuotient.Claim) (hne : claims ≠ [])
    (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (hholds : ∀ sc ∈ stackClaims L claims, EndToEnd.StackClaim.Holds L.logN sc (colOf L.logN stack))
    (hml : ∀ sc ∈ stackClaims L claims, EndToEnd.IsMultilinearFn L.logN sc.1) {π : Compile.Proof}
    (hπ : proveOpeningWithH (m := Id) H F fuel L (commitWithH (m := Id) H L.logN stack) stack
      claims = some π) :
    openingWithH (m := Id) H F L (commitWithH (m := Id) H L.logN stack).root claims π = true := by
  have hacc := runProof_prove H F _ _ _ fuel
    (fun chal ↦ (Whir.Complete.runI_openingProgram hw (colOf L.logN stack) _ hholds hml chal).1)
    (fun chal ↦ (Whir.Complete.runI_openingProgram hw (colOf L.logN stack) _ hholds hml chal).2)
    ((proveOpeningWithH_eq_prove H F fuel L hL hw stack claims hlen).symm.trans hπ)
  obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hπ
  rw [openingWithH_eq_runProof H F L hw claims hne hlen (commitWithH (m := Id) H L.logN stack).root
    _ _ t.1 t.2 (digestOfScalars_digestScalars _)]
  exact hacc

/-! ## The proofs of work -/

/-- The opening program's proofs of work: WHIR's, of `Whir.queryGrindingBits = 17` bits. -/
theorem movesOK_openingProgram (μ R : ℕ) (sc : List StackClaim) :
    EndToEnd.Sound.MovesOK (· = Whir.queryGrindingBits) True
      (Whir.Complete.openingProgram μ R sc) :=
  EndToEnd.Sound.MovesOK.seq
    ((EndToEnd.Sound.movesOK_commitStack _ _).mono (fun _ h ↦ h.elim) id) fun _ ↦
      EndToEnd.Sound.MovesOK.seq (EndToEnd.Sound.movesOK_verifyStackedOpening _ _ _) fun _ ↦
        EndToEnd.Sound.MovesOK.pure _

/-- **The Statement's opening prover fails only at a proof of work**: if it produces no proof, the
opening program reaches a `17`-bit proof of work at a sponge where every nonce below `fuel`
fails. -/
theorem exists_failed_pow_opening (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (fuel : ℕ) (L : PcsQuotient.Layout) (hL : WeightShape L)
    (hw : Whir.Admissible L.logN PcsQuotient.logInvRate) (stack : Array K)
    (claims : List PcsQuotient.Claim) (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (h : proveOpeningWithH (m := Id) H F fuel L (commitWithH (m := Id) H L.logN stack) stack
      claims = none) :
    ∃ hist k sp, (Whir.Complete.openingProgram L.logN PcsQuotient.logInvRate
        (stackClaims L claims)).after hist = some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel,
        powOk Whir.queryGrindingBits (Compile.nonceOf n) (Compile.powStep F sp (Compile.nonceOf n)).1 = false := by
  rw [proveOpeningWithH_eq_prove H F fuel L hL hw stack claims hlen] at h
  by_contra hne
  refine prove_ne_none H F _ _ _ fuel (fun hist bits k sp hg hn ↦ hne ?_) h
  obtain rfl := ((movesOK_openingProgram _ _ _).after hg).1
  exact ⟨hist, k, sp, hg, ((findNonce_eq_none_iff F _ sp fuel).1 hn).2⟩

/-! ## The stack claims' weights are multilinear -/

/-- **Every stack claim of a layout of the shape `WeightShape` has a multilinear weight** (F2's
`isMultiaffine_layoutClaimWeight`, `isMultiaffine_gadgetWeight` through the translation), so the
hypothesis `hml` of `openingWithH_proveOpeningWithH` holds. -/
theorem isMultilinearFn_stackClaims (L : PcsQuotient.Layout) (hL : WeightShape L)
    (claims : List PcsQuotient.Claim) :
    ∀ sc ∈ stackClaims L claims, EndToEnd.IsMultilinearFn L.logN sc.1 := by
  obtain ⟨-, -, -, -, hhid⟩ := hL
  have hov : L.logPiece.isSome → (layoutTr L).overflow < L.lanes.length := by
    intro h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨-, -, -, -, hov, -⟩ := hhid s hs
    obtain ⟨hovtr, hovlt⟩ := overflow_tr hov
    rw [hovtr]
    exact hovlt
  intro sc hsc
  simp only [stackClaims, List.mem_append, List.mem_map] at hsc
  rcases hsc with ⟨c, -, rfl⟩ | hg
  · rw [show PcsQuotient.stackWeight L c = (layoutTr L).claimWeight (claimTr c) from
      funext (stackWeight_eq L hov c)]
    exact Completeness.isMultilinearFn_of_isMultiaffine
      (WhirBridge.isMultiaffine_layoutClaimWeight (layoutTr L) (claimTr c))
  · rcases hs : L.logPiece with _ | s
    · simp [hs] at hg
    · obtain ⟨-, -, -, h33, -⟩ := hhid s hs
      simp only [hs, Option.isSome_some, ↓reduceIte, List.mem_singleton] at hg
      subst hg
      rw [show PcsQuotient.gadgetWeight L = (layoutTr L).gadgetWeight from
        funext (gadgetWeight_eq L hs h33)]
      exact Completeness.isMultilinearFn_of_isMultiaffine
        (WhirBridge.isMultiaffine_gadgetWeight (layoutTr L))

/-- **Acceptance without the multilinearity hypothesis**: `openingWithH_proveOpeningWithH` with
`isMultilinearFn_stackClaims`. -/
theorem openingWithH_proveOpeningWithH' (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (fuel : ℕ) (L : PcsQuotient.Layout) (hL : WeightShape L)
    (hw : Whir.Admissible L.logN PcsQuotient.logInvRate) (stack : Array K)
    (claims : List PcsQuotient.Claim) (hne : claims ≠ [])
    (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (hholds : ∀ sc ∈ stackClaims L claims, EndToEnd.StackClaim.Holds L.logN sc (colOf L.logN stack))
    {π : Compile.Proof}
    (hπ : proveOpeningWithH (m := Id) H F fuel L (commitWithH (m := Id) H L.logN stack) stack
      claims = some π) :
    openingWithH (m := Id) H F L (commitWithH (m := Id) H L.logN stack).root claims π = true :=
  openingWithH_proveOpeningWithH H F fuel L hL hw stack claims hne hlen hholds
    (isMultilinearFn_stackClaims L hL claims) hπ

end E2ECompleteness
