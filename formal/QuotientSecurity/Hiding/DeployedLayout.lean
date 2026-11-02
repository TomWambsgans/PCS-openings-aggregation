-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.GadgetLayout
import QuotientSecurity.Hiding.NovelBasis

/-!
# The deployed hidden layouts as `GadgetLayout`s

`crates/quotient/src/opening.rs` (`Layout::hidden_with`, `Table::hidden_in`, `gadget_lanes`,
`Layout::gadget_entry`) and `crates/quotient/src/protocol.rs` (`witness_layout`, `quotient_layout`),
transcribed:

* `Lane`, `Layout`: the Rust struct's fields (a hidden layout: its piece's `log` is a number);
  `hiddenWith`: `Layout::hidden_with` step by step (the whole blocks, the tails, the first `32` blocks
  on lanes `0 .. 32` and random lanes there if there are fewer, the overflow lane `32`, the random
  lanes, the other blocks, the given-up pieces then the tails); `witnessLayout r`, `quotientLayout r`:
  the protocol's two hidden tables at `2^r` rows.
* `Layout.OK`: what the model needs of a layout (pieces of `2^8`, lanes of more, `34 ≤ L ≤ 64` lanes,
  the overflow lane `32` and no other, lanes `30` and `31` blocks, the held pieces within the overflow
  lane), decided for both layouts at every supported size (`deployed_ok`, `decide +kernel`), with their
  shapes (`deployed_shape`: `40` and `63` lanes, `33` and `167` pieces, the random lanes exactly
  `33 .. 40`).
* `Layout.toGadget`: **the `GadgetLayout`** of such a layout, on its lanes `Fin L` and entries
  `Fin 2^ℓ`: `first = [0, 247)`, the gadget's entries `247 + 3p + i`, the pairs `(0, 31)`, `(1, 30)`,
  the overflow lane `32`, `held` its pieces `1 .. H`, the random lanes those holding `Lane::Random`.
* `hiddenWord_eq`: **the stack `Table::hidden` writes is `stackD d + stackR r`**, `d` the table's
  entries where the layout holds them (`place`), `r` the lanes' random words: the model's randomness
  (with the pairs' copies and the overflow lane's zeros) and its table part are the Rust's.
* The lanes `GadgetLayout.roundsReached` asks for (`pos_pairA0`, …, `pos_low`, `pos_33`, `pos_pat`).
-/

namespace QuotientSecurity.Hiding

open Finset

set_option linter.unusedSectionVars false

namespace Deployed

/-- What a lane of the stack holds (`opening::Lane`). -/
inductive Lane where
  /-- The table's block `b` (all of it but its first piece). -/
  | block (b : ℕ)
  /-- The table's pieces, at its pieces `1, 2, ...`. -/
  | overflow
  /-- Randomness. -/
  | random
  deriving DecidableEq, Repr

/-- `matches!(lane, Lane::Block(_))`. -/
def Lane.isBlock : Lane → Bool
  | .block _ => true
  | _ => false

/-- `opening::Layout` of a hidden layout, field by field. -/
structure Layout where
  vars : ℕ
  logN : ℕ
  lanes : List Lane
  logPiece : ℕ
  pieces : List ℕ
  deriving DecidableEq, Repr

/-- `LANE_FOLD`. -/
def laneFold : ℕ := 6

/-- `LOG_PIECE`. -/
def logPieceD : ℕ := 8

/-- `GADGET`. -/
def gadgetD : ℕ := 9

/-- `OVERFLOW_LANE`. -/
def overflowLane : ℕ := 32

namespace Layout

/-- `log_lane`. -/
def logLane (L : Layout) : ℕ := L.logN - laneFold

/-- `Layout::overflow`: the first overflow lane. -/
def overflow (L : Layout) : ℕ := L.lanes.findIdx (· == Lane.overflow)

end Layout

/-- `hidden_with`'s whole blocks: for each chunk `(chunk, len)`, its `len >> log_lane` blocks. -/
def hiddenBlocks (logChunk logLane : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c => (List.range (c.2 >>> logLane)).map fun j => (c.1 <<< (logChunk - logLane)) + j

/-- `hidden_with`'s tails: the pieces of what each chunk holds past its whole blocks. -/
def hiddenTails (logChunk logLane logPiece : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c =>
    let first := c.1 <<< (logChunk - logLane)
    let whole := c.2 >>> logLane
    let start := (first + whole) <<< (logLane - logPiece)
    let tail := c.2 - (whole <<< logLane)
    (List.range ((tail + 2 ^ logPiece - 1) / 2 ^ logPiece)).map fun j => start + j

/-- **`Layout::hidden_with`**: the first `32` whole blocks on lanes `0 .. 32` (random lanes there if
there are fewer), the overflow lane, `random` random lanes, the other blocks; the overflow lane's
pieces are the piece each block lane gives up, in lane order, then the tails. -/
def hiddenWith (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) (random logPiece : ℕ) : Layout :=
  let logLane := logN - laneFold
  let blocks := hiddenBlocks logChunk logLane chunks
  let lower := min blocks.length overflowLane
  let lanes := (blocks.take lower).map Lane.block ++ List.replicate (overflowLane - lower) Lane.random ++
    [Lane.overflow] ++ List.replicate random Lane.random ++ (blocks.drop lower).map Lane.block
  let givenUp := lanes.filterMap fun
    | .block b => some (b <<< (logLane - logPiece))
    | _ => none
  { vars := vars
    logN := logN
    lanes := lanes
    logPiece := logPiece
    pieces := givenUp ++ hiddenTails logChunk logLane logPiece chunks }

/-- `cell_vars(log_rows) = log_rows + 2`. -/
def cellVars (r : ℕ) : ℕ := r + 2

/-- `WITNESS_RANDOM_LANES = QUOTIENT_RANDOM_LANES = 7`. -/
def randomLanesD : ℕ := 7

/-- **`witness_layout(r)`**: the four row polynomials, then their masks, sixteen entries of the next
chunk. -/
def witnessLayout (r : ℕ) : Layout :=
  hiddenWith (cellVars r + 1) (cellVars r) (cellVars r + 1) [(0, 2 ^ cellVars r), (1, 16)]
    randomLanesD logPieceD

/-- `Q_SPILL = PUBLIC_EXCESS + 64`. -/
def qSpill : ℕ := 9216 + 64

/-- `quotient_chunks(m, spill, tail)`. -/
def quotientChunks (m spill tail : ℕ) : List (ℕ × ℕ) :=
  let n := 2 ^ m
  ((List.range 3).flatMap fun e =>
      (16 * e, n) :: (List.range 3).map (fun digit => (16 * e + 4 + digit, n)) ++
        [(16 * e + 7, spill)]) ++
    [(8, n), (9, 3 * n / 4 + tail)]

/-- **`quotient_layout(r)`**: `m + 6` variables, stacked in lanes of a quarter chunk. -/
def quotientLayout (r : ℕ) : Layout :=
  hiddenWith (cellVars r + 6) (cellVars r) (cellVars r + 4) (quotientChunks (cellVars r) qSpill 64)
    randomLanesD logPieceD

/-! ### What the model needs of a layout -/

/-- A layout the gadget model covers. -/
structure Layout.OK (L : Layout) : Prop where
  piece : L.logPiece = logPieceD
  lane : logPieceD < L.logLane
  lanes_ge : 34 ≤ L.lanes.length
  lanes_le : L.lanes.length ≤ 64
  overflow : L.overflow = overflowLane
  at_ov : L.lanes[overflowLane]? = some .overflow
  ov_unique : ∀ l < L.lanes.length, L.lanes[l]? = some .overflow → l = overflowLane
  block30 : L.lanes[30]?.map Lane.isBlock = some true
  block31 : L.lanes[31]?.map Lane.isBlock = some true
  fits : (L.pieces.length + 1) * 2 ^ logPieceD ≤ 2 ^ L.logLane

/-- `Layout.OK` as one decidable conjunction. -/
def Layout.OKb (L : Layout) : Prop :=
  L.logPiece = logPieceD ∧ logPieceD < L.logLane ∧ 34 ≤ L.lanes.length ∧ L.lanes.length ≤ 64 ∧
    L.overflow = overflowLane ∧ L.lanes[overflowLane]? = some .overflow ∧
    (∀ l < L.lanes.length, L.lanes[l]? = some .overflow → l = overflowLane) ∧
    L.lanes[30]?.map Lane.isBlock = some true ∧ L.lanes[31]?.map Lane.isBlock = some true ∧
    (L.pieces.length + 1) * 2 ^ logPieceD ≤ 2 ^ L.logLane

instance (L : Layout) : Decidable L.OKb := by
  unfold Layout.OKb; infer_instance

theorem Layout.OKb.toOK {L : Layout} (h : L.OKb) : L.OK :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem deployed_okb : ∀ r, 17 ≤ r → r ≤ 22 → (witnessLayout r).OKb ∧ (quotientLayout r).OKb := by
  decide +kernel

/-- **Both deployed layouts are covered by the model**, at every supported size. -/
theorem deployed_ok (r : ℕ) (h1 : 17 ≤ r) (h2 : r ≤ 22) :
    (witnessLayout r).OK ∧ (quotientLayout r).OK :=
  ⟨(deployed_okb r h1 h2).1.toOK, (deployed_okb r h1 h2).2.toOK⟩

/-- **Their shapes**: `40` and `63` lanes, `33` and `167` held pieces, lanes of `2^(r-3)` and `2^r`
words; blocks on lanes `0 .. 32` (and from `40` on), the overflow lane `32`, the random lanes exactly
`33 .. 40` (the cube `32 .. 40` but the overflow lane's corner). -/
theorem deployed_shape : ∀ r, 17 ≤ r → r ≤ 22 →
    (witnessLayout r).lanes.length = 40 ∧ (quotientLayout r).lanes.length = 63 ∧
      (witnessLayout r).pieces.length = 33 ∧ (quotientLayout r).pieces.length = 167 ∧
      (witnessLayout r).logLane = r - 3 ∧ (quotientLayout r).logLane = r ∧
      (witnessLayout r).lanes.map Lane.isBlock =
        List.replicate 32 true ++ [false] ++ List.replicate 7 false ∧
      (witnessLayout r).lanes.map (· == Lane.random) =
        List.replicate 32 false ++ [false] ++ List.replicate 7 true ∧
      (quotientLayout r).lanes.map Lane.isBlock =
        List.replicate 32 true ++ [false] ++ List.replicate 7 false ++ List.replicate 23 true ∧
      (quotientLayout r).lanes.map (· == Lane.random) =
        List.replicate 32 false ++ [false] ++ List.replicate 7 true ++ List.replicate 23 false := by
  decide +kernel

/-! ### The `GadgetLayout` -/

/-- `Layout::gadget_entry(g, i)`: `2^s − GADGET + 3g + i`. -/
def gadgetEntry (s g i : ℕ) : ℕ := 2 ^ s - gadgetD + 3 * g + i

/-- `gadget_lanes(g)`. -/
def gadgetLanes : ℕ → List ℕ
  | 0 => [0, 31]
  | 1 => [1, 30]
  | _ => [overflowLane]

namespace Layout

variable (L : Layout)

/-- Lane `l`'s index: its six bits (`laneBits`). -/
def pos : Fin L.lanes.length → (Fin 6 → Bool) := fun l i => (l : ℕ).testBit i

/-- The overflow lane's entries holding the table: its pieces `1 .. H`. -/
def heldSet : Finset (Fin (2 ^ L.logLane)) :=
  univ.filter fun y => 2 ^ logPieceD ≤ (y : ℕ) ∧ (y : ℕ) < (L.pieces.length + 1) * 2 ^ logPieceD

variable {L}

theorem OK.n32 (h : L.OK) : 32 < L.lanes.length := by have := h.lanes_ge; omega

theorem OK.piece_le (h : L.OK) : 2 ^ logPieceD ≤ 2 ^ L.logLane :=
  Nat.pow_le_pow_right (by norm_num) h.lane.le

theorem OK.gent_lt (h : L.OK) (p i : Fin 3) : gadgetEntry logPieceD p i < 2 ^ L.logLane := by
  have := h.piece_le
  have hp := p.isLt
  have hi := i.isLt
  simp only [gadgetEntry, logPieceD, gadgetD] at this ⊢
  omega

/-- **The deployed layout as a `GadgetLayout`**: lanes `Fin L`, entries `Fin 2^ℓ`. -/
def toGadget (h : L.OK) : GadgetLayout (Fin L.lanes.length) (Fin (2 ^ L.logLane)) where
  isRand l := L.lanes[(l : ℕ)]? = some .random
  ov := ⟨overflowLane, h.n32⟩
  first := firstFree L.logLane
  held := L.heldSet
  gent p i := ⟨gadgetEntry logPieceD p i, h.gent_lt p i⟩
  pairA := ![⟨0, by have := h.n32; omega⟩, ⟨1, by have := h.n32; omega⟩]
  pairB := ![⟨31, by have := h.n32; omega⟩, ⟨30, by have := h.n32; omega⟩]
  gent_inj p i p' i' hpi := by
    simp only [Fin.mk.injEq, gadgetEntry, logPieceD, gadgetD] at hpi
    have := p.isLt; have := i.isLt; have := p'.isLt; have := i'.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  gent_first p i := by
    simp only [firstFree, mem_filter, mem_univ, true_and, gadgetEntry, logPieceD, gadgetD, not_lt]
    omega
  gent_held p i := by
    have := p.isLt; have := i.isLt
    simp only [heldSet, mem_filter, mem_univ, true_and, gadgetEntry, logPieceD, gadgetD, not_and]
    norm_num
    omega
  held_first := by
    rw [Finset.disjoint_left]
    intro y hy hf
    simp only [heldSet, mem_filter, mem_univ, true_and, logPieceD] at hy
    simp only [firstFree, mem_filter, mem_univ, true_and] at hf
    norm_num at hy
    omega
  not_rand_ov := by
    show ¬ L.lanes[overflowLane]? = some .random
    rw [h.at_ov]
    simp
  not_rand_pairB p := by
    fin_cases p
    · show ¬ L.lanes[31]? = some .random
      intro h'
      have := h.block31
      rw [h'] at this
      simp [Lane.isBlock] at this
    · show ¬ L.lanes[30]? = some .random
      intro h'
      have := h.block30
      rw [h'] at this
      simp [Lane.isBlock] at this
  pairB_ne_ov p := by
    fin_cases p <;> simp [overflowLane]
  pairA_ne_pairB p := by
    fin_cases p <;> simp

/-! ### The lanes `GadgetLayout.roundsReached` uses -/

theorem pos_injective (h : L.OK) : Function.Injective L.pos := by
  intro l l' hll
  have h64 := h.lanes_le
  have := laneBits_injective (a₁ := ⟨l, by omega⟩) (a₂ := ⟨l', by omega⟩) hll
  exact Fin.ext (by simpa using congrArg Fin.val this)

theorem pos_eq_lane (h : L.OK) (l : Fin L.lanes.length) :
    L.pos l = lane ⟨l, lt_of_lt_of_le l.isLt h.lanes_le⟩ := rfl

theorem pos_pairA0 (h : L.OK) : L.pos ((L.toGadget h).pairA 0) = lane 0 := rfl
theorem pos_pairB0 (h : L.OK) : L.pos ((L.toGadget h).pairB 0) = lane 31 := rfl
theorem pos_pairA1 (h : L.OK) : L.pos ((L.toGadget h).pairA 1) = lane 1 := rfl
theorem pos_pairB1 (h : L.OK) : L.pos ((L.toGadget h).pairB 1) = lane 30 := rfl
theorem pos_ov (h : L.OK) : L.pos (L.toGadget h).ov = lane 32 := rfl

theorem lower_lanes : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → ∃ l : Fin 32, lane (Fin.castLE (by norm_num) l) = b := by
  decide +kernel

/-- Every lane index of the lower half is a lane of the layout. -/
theorem pos_low (h : L.OK) : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range L.pos := by
  intro b hb
  obtain ⟨l, hl⟩ := lower_lanes b hb
  exact ⟨⟨l, by have := h.n32; have := l.isLt; omega⟩, hl⟩

theorem pos_33 (h : L.OK) : lane 33 ∈ Set.range L.pos :=
  ⟨⟨33, by have := h.lanes_ge; omega⟩, rfl⟩

/-- The gadget's patterns weigh only lanes of the layout. -/
theorem pos_pat {E : Type} [Field E] (h : L.OK) (p : Fin 3) (b : Fin 6 → Bool)
    (hb : patE (E := E) p b ≠ 0) : b ∈ Set.range L.pos := by
  have hl : ∀ (l : ℕ) (hl : l < 33), lane ⟨l, by omega⟩ ∈ Set.range L.pos := fun l hl =>
    ⟨⟨l, by have := h.n32; omega⟩, rfl⟩
  fin_cases p
  · by_cases h0 : b = lane 0
    · exact h0 ▸ hl 0 (by norm_num)
    by_cases h31 : b = lane 31
    · exact h31 ▸ hl 31 (by norm_num)
    exfalso
    apply hb
    simp [patE, pattern0, pairCol, unitCol, flipC_lane0, h0, h31]
  · by_cases h1 : b = lane 1
    · exact h1 ▸ hl 1 (by norm_num)
    by_cases h30 : b = lane 30
    · exact h30 ▸ hl 30 (by norm_num)
    exfalso
    apply hb
    simp [patE, pattern1, pairCol, unitCol, flipC_lane1, h1, h30]
  · by_cases h32 : b = lane 32
    · exact h32 ▸ hl 32 (by norm_num)
    exfalso
    apply hb
    simp [patE, pattern2, unitCol, h32]

end Layout

/-! ### `Table::hidden`'s stack is the model's -/

namespace Layout

variable (L : Layout) {K : Type} [Field K]

/-- `Table::hidden_in`'s fill of lane `l` at entry `y`, before the gadget's values: the first piece
random, then the block's entries, the overflow lane's held pieces (and random past them), or random. -/
def fillWord (t : ℕ → K) (rnd : ℕ → ℕ → K) (l y : ℕ) : K :=
  if y < 2 ^ L.logPiece then rnd l y
  else match L.lanes[l]? with
    | some (.block b) => t ((b <<< L.logLane) + y)
    | some .overflow =>
      if y < (L.pieces.length + 1) * 2 ^ L.logPiece then
        t (L.pieces.getD (y / 2 ^ L.logPiece - 1) 0 * 2 ^ L.logPiece + y % 2 ^ L.logPiece)
      else rnd l y
    | _ => rnd l y

/-- **The stack `Table::hidden` writes**: the fill, then at gadget pattern `g`'s entries the pair's
second lane takes its first lane's value, and the overflow lane `0`. -/
def hiddenWord (t : ℕ → K) (rnd : ℕ → ℕ → K) (l y : ℕ) : K :=
  if 2 ^ L.logPiece - gadgetD ≤ y ∧ y < 2 ^ L.logPiece then
    match gadgetLanes ((y - (2 ^ L.logPiece - gadgetD)) / 3) with
    | [a, b] => if l = b then L.fillWord t rnd a y else L.fillWord t rnd l y
    | [a] => if l = a then 0 else L.fillWord t rnd l y
    | _ => L.fillWord t rnd l y
  else L.fillWord t rnd l y

/-- The table's entries where the layout holds them (what `Table::hidden`'s `entries` writes). -/
def place (t : ℕ → K) (l y : ℕ) : K :=
  match L.lanes[l]? with
  | some (.block b) => t ((b <<< L.logLane) + y)
  | some .overflow =>
    t (L.pieces.getD (y / 2 ^ L.logPiece - 1) 0 * 2 ^ L.logPiece + y % 2 ^ L.logPiece)
  | _ => 0

end Layout

end Deployed

end QuotientSecurity.Hiding
