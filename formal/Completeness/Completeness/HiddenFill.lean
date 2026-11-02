-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import WhirBridge.Layouts

/-!
# The honest prover's hidden stack

The redesigned hidden layout of `crates/quotient/src/opening.rs` (commit `cbb527d`; the design is
`crates/quotient/HIDING.md`), its honest stack and the table read back from it, transcribed:

* `Layout.hiddenNew` is `Layout::hidden_with` (`opening.rs:153-203`): the chunks' whole blocks
  and tails (`opening.rs:166-176`); the first (at most) `32` blocks on lanes `0..32`, random lanes
  there if there are fewer, the overflow lane `OVERFLOW_LANE = 32`, `random` random lanes, then the
  other blocks (`opening.rs:178-184`); the overflow lane's pieces are each block lane's block's
  **first** piece `b << (log_lane − log_piece)`, in lane order, then the tails (`opening.rs:186-190`).
  There is no share lane (`share := none`).
* `Layout.fillNew L s T pad` is `Table::hidden_in` (`opening.rs:479-521`), the table's entries `T`
  (what `entries` writes) and the random words an arbitrary `pad l y` (lane `l`, entry `y`), so that
  everything below holds for every padding: every lane's first piece is random; a block lane `b`
  holds the table's entries `b·2^ℓ + y` from its piece `1` on; the overflow lane holds the table's
  piece `pieces[k]` at its piece `k + 1`, random after; a random lane is random
  (`Layout.laneFill`, `opening.rs:494-508`); then the gadget's values (`gadgetFix`,
  `opening.rs:509-519`): in pattern `g` at its entry `gadget_entry(g, i)` (`opening.rs:247-250`), a
  pair's second lane takes its first lane's word and the overflow lane zero. The stack is the
  `lanes · 2^ℓ` words of the lanes; WHIR's column has `2^log_n` words, zero past them.
* `Layout.readNew L s q t` is `Table::read` (`opening.rs:523-545`), entry by entry: the table's
  piece `p = t >> s` is the overflow lane's piece `k + 1` if `p = pieces[k]`, else the piece
  `p & (2^(ℓ−s) − 1)` of the lane holding `Block(p >> (ℓ − s))`, else zero.

## Results

* `readNew_fillNew`: for a layout of the shape `hidden_with` gives (`NewHiddenOK`), for every table
  `T`, every padding `pad` and every entry `t`, the table read back from the honest stack is
  `if L.CoveredNew s t then T t else 0`, `CoveredNew` the entries the layout holds (in the table, and
  its piece an overflow piece or its block on a lane). `readNew_fillNew_eq`: a table that vanishes
  off them is read back whole.
* `coveredNew_hiddenNew`: in `Layout.hiddenNew`, every entry `c·2^log_chunk + j` of a chunk
  `(c, len)`, `j < len`, is covered; `readNew_fillNew_hiddenNew`: a table that vanishes off its
  chunks is read back whole from the honest stack.
* The gadget: `gadget_pair0`, `gadget_pair1`, `gadget_overflow`: at every gadget entry the honest
  stack's lanes `0` and `31` (`1` and `30`) hold one word and the overflow lane zero, so
  (`gadget_cancel`, `gadget_sum_zero`) in characteristic two
  `Σ_{g<3} Σ_{i<3} β_i · Σ_{l ∈ gadget_lanes(g)} stack(l, gadget_entry(g, i)) = 0` for every
  `β : Fin 3 → E`, and (`gadgetWeight_sum_zero`) the gadget's weight on the cube
  (`gadgetWeight`, what `opening::verify`'s gadget term is at a cube point, `opening.rs:786-806`;
  equal to `gadget_at`, `opening.rs:253-261`, by `gadgetAt_eq`) pairs to zero with the honest stack.
* `deployed_newHiddenOK`, `deployed_shape`, `witness_read`, `quotient_read`: the witness and
  quotient layouts of `protocol.rs:117-130` at `LOG_ROWS = 22` (`hiddenNew 25 24 25 [(0, 2^24),
  (1, 16)] 7 8` and `hiddenNew 30 24 28 (quotient_chunks 24 Q_SPILL 64) 7 8`) have the shape, `40`
  and `63` lanes, `33` and `167` pieces, and read their tables back; decided by kernel evaluation
  (`decide +kernel`, no `native_decide`).

The functions on `Layout` are declared in `WhirBridge.Layout`'s namespace (`L.readNew`, ...); the
rest in `Completeness`.
-/

namespace Completeness

open WhirBridge LeanVM.Parameters LeanVM.Protocol Finset

/-! ## Constants (`opening.rs:48-81`) -/

/-- `GADGET` (`opening.rs:60`): the gadget's entries, three patterns of three, the last of every
lane's first piece. -/
def gadget : ℕ := 9

/-- `OVERFLOW_LANE` (`opening.rs:64`): the hidden layouts' overflow lane. -/
def overflowLane : ℕ := 32

/-- `MIN_RANDOM_LANES` (`opening.rs:67`). -/
def minRandomLanes : ℕ := 7

/-- `gadget_lanes(g)` (`opening.rs:71-74`): `0` and `31`, `1` and `30`, then the overflow lane
alone. (The Rust panics for `g ≥ 3`; here that reads as pattern `2`.) -/
def gadgetLanes : ℕ → List ℕ
  | 0 => [0, 31]
  | 1 => [1, 30]
  | _ => [overflowLane]

/-- `Layout::gadget_entry(g, i)` (`opening.rs:247-250`), for pieces of `2^s` entries:
`2^s − GADGET + 3g + i`. -/
def gadgetEntry (s g i : ℕ) : ℕ := 2 ^ s - gadget + 3 * g + i

/-! ## The layout (`Layout::hidden_with`, `opening.rs:153-203`) -/

/-- The chunks' whole blocks, in chunk order (`opening.rs:166-176`): chunk `(c, len)` gives the
blocks `(c << (log_chunk − log_lane)) + j`, `j < len >> log_lane`. -/
def chunkBlocks (logChunk logLane : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c ↦ (List.range (c.2 >>> logLane)).map fun j ↦ (c.1 <<< (logChunk - logLane)) + j

/-- The chunks' tails, in chunk order (`opening.rs:166-176`): the pieces of what chunk `(c, len)`
holds past its whole blocks, from `start = (first + whole) << (log_lane − log_piece)` on,
`⌈tail / 2^log_piece⌉` of them. -/
def chunkTails (logChunk logLane logPiece : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c ↦
    let first := c.1 <<< (logChunk - logLane)
    let whole := c.2 >>> logLane
    let start := (first + whole) <<< (logLane - logPiece)
    let tail := c.2 - (whole <<< logLane)
    (List.range ((tail + 2 ^ logPiece - 1) / 2 ^ logPiece)).map fun j ↦ start + j

/-- The lanes (`opening.rs:178-184`): the first `lower = min(blocks, 32)` blocks, random lanes up to
`OVERFLOW_LANE`, the overflow lane, `random` random lanes, then the other blocks. -/
def hiddenLanes (blocks : List ℕ) (random : ℕ) : List Lane :=
  let lower := min blocks.length overflowLane
  (blocks.take lower).map .block ++ List.replicate (overflowLane - lower) .random ++ [.overflow] ++
    List.replicate random .random ++ (blocks.drop lower).map .block

/-- The blocks the lanes hold, in lane order. -/
def laneBlocks (lanes : List Lane) : List ℕ :=
  lanes.filterMap fun
    | .block b => some b
    | _ => none

/-- **`Layout::hidden_with`** (`opening.rs:153-203`; `Layout::hidden` is `log_piece = LOG_PIECE`):
the lanes of `hiddenLanes`, the overflow lane's pieces the first piece each block lane gives up
(`given_up`, in lane order), then the chunks' tails. The Rust's assertions are not checked here:
`NewHiddenOK` is decided of the layouts used. -/
def _root_.WhirBridge.Layout.hiddenNew (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (random logPiece : ℕ) : Layout :=
  let logLane := logN - laneFold
  let lanes := hiddenLanes (chunkBlocks logChunk logLane chunks) random
  { vars := vars
    logN := logN
    lanes := lanes
    logPiece := some logPiece
    pieces := (laneBlocks lanes).map (· <<< (logLane - logPiece)) ++
      chunkTails logChunk logLane logPiece chunks
    share := none }

/-! ## The honest stack (`Table::hidden_in`, `opening.rs:479-521`) -/

/-- Entry `y` of lane `l` of a stack (`lane(l)[y]`, `opening.rs:530`): the column's word
`y + 2^ℓ·l`. -/
def laneWord {n : ℕ} (q : Column n) (logLane l y : ℕ) : K := q.values.getD (y + 2 ^ logLane * l) 0

/-- The word `Table::hidden_in` writes at entry `y` of lane `l` before the gadget's values
(`opening.rs:494-508`), for the table's entries `T` and the random words `pad`: the first piece
random; a block lane `b`'s entry `b·2^ℓ + y`; the overflow lane's piece `k + 1`, `k < |pieces|`, the
table's piece `pieces[k]`, random after; a random lane random. -/
def _root_.WhirBridge.Layout.laneFill (L : Layout) (s : ℕ) (T : ℕ → K) (pad : ℕ → ℕ → K)
    (l y : ℕ) : K :=
  if y < 2 ^ s then pad l y
  else match L.lanes[l]? with
    | some (.block b) => T ((b <<< L.logLane) + y)
    | some .overflow =>
      if y / 2 ^ s ≤ L.pieces.length then T (L.pieces.getD (y / 2 ^ s - 1) 0 * 2 ^ s + y % 2 ^ s)
      else pad l y
    | some .random => pad l y
    | none => 0

/-- The gadget's values (`opening.rs:509-519`), at entry `y` of lane `l`: for `g, i < 3` in order, at
`y = gadget_entry(g, i)`, a pair `[a, b]`'s second lane `b` takes lane `a`'s word (`some (some a)`),
a lone lane `[a]` zero (`some none`); `none` where nothing is written. The lanes written (`31`, `30`,
the overflow lane) are never read (`0`, `1`), so the Rust's writes in sequence are these. -/
def gadgetFix (s l y : ℕ) : Option (Option ℕ) :=
  (List.range 3).findSome? fun g ↦ (List.range 3).findSome? fun i ↦
    if y = gadgetEntry s g i then
      match gadgetLanes g with
      | [a, b] => if l = b then some (some a) else none
      | [a] => if l = a then some none else none
      | _ => none
    else none

/-- The honest stack's word at entry `y` of lane `l` (`Table::hidden_in`, `opening.rs:479-521`):
the gadget's value there, else `laneFill`. -/
def _root_.WhirBridge.Layout.wordNew (L : Layout) (s : ℕ) (T : ℕ → K) (pad : ℕ → ℕ → K)
    (l y : ℕ) : K :=
  match gadgetFix s l y with
  | some (some a) => L.laneFill s T pad a y
  | some none => 0
  | none => L.laneFill s T pad l y

/-- **`Table::hidden_in`** (`opening.rs:479-521`) as WHIR's column of `2^log_n` words: word `x` is
lane `x / 2^ℓ`'s entry `x mod 2^ℓ`, zero past the placed lanes. -/
def _root_.WhirBridge.Layout.fillNew (L : Layout) (s : ℕ) (T : ℕ → K) (pad : ℕ → ℕ → K) :
    Column L.logN :=
  ⟨Vector.ofFn fun x ↦
    if x.val / 2 ^ L.logLane < L.lanes.length then
      L.wordNew s T pad (x.val / 2 ^ L.logLane) (x.val % 2 ^ L.logLane)
    else 0⟩

/-! ## `Table::read` (`opening.rs:523-545`) -/

/-- **`Table::read`** (`opening.rs:523-545`), entry by entry, with pieces of `2^s` entries: the
table's entry `t`, in piece `p = t >> s` at `o = t mod 2^s`, is the overflow lane's entry
`(k + 1)·2^s + o` if `p = pieces[k]` (the first such `k`); else the entry
`(p & (2^(ℓ−s) − 1))·2^s + o` of the first lane holding `Block(p >> (ℓ − s))`; else zero. -/
def _root_.WhirBridge.Layout.readNew (L : Layout) (s : ℕ) (q : Column L.logN) (t : ℕ) : K :=
  let ℓ := L.logLane
  let p := t >>> s
  let o := t % 2 ^ s
  match L.pieces.findIdx? (· == p) with
  | some k => laneWord q ℓ L.overflow ((k + 1) * 2 ^ s + o)
  | none => match L.lanes.findIdx? (· == .block (p >>> (ℓ - s))) with
    | some l => laneWord q ℓ l ((p &&& (2 ^ (ℓ - s) - 1)) * 2 ^ s + o)
    | none => 0

/-- **The entries a hidden layout holds**: in the table, and its piece one of the overflow lane's or
its block on a lane. -/
def _root_.WhirBridge.Layout.CoveredNew (L : Layout) (s t : ℕ) : Prop :=
  t < 2 ^ L.vars ∧ (t >>> s ∈ L.pieces ∨ Lane.block (t >>> s >>> (L.logLane - s)) ∈ L.lanes)

instance (L : Layout) (s t : ℕ) : Decidable (L.CoveredNew s t) := by
  unfold Layout.CoveredNew; infer_instance

/-! ## The shape -/

/-- **The shape `Layout::hidden_with` gives**, with pieces of `2^s`, all of it asserted by the Rust
or true by construction: the piece's `log`; lanes of `2^ℓ = 2^(log_n − 6)` words, `s < ℓ ≤ vars`;
at most `64` lanes; the overflow lane is lane `32` (the first overflow lane, `Layout::overflow`); fewer
overflow pieces than a lane's pieces (its piece `0` is random); the gadget inside the first piece;
the pieces distinct and in the table; each block on at most one lane and in the table; every block
lane's first piece among the pieces, and no other piece of its block. (`readNew_fillNew` uses neither
distinctness nor the last condition; the claims' weights need them.) -/
structure NewHiddenOK (L : Layout) (s : ℕ) : Prop where
  piece : L.logPiece = some s
  six_le : laneFold ≤ L.logN
  s_lt : s < L.logLane
  lane_le : L.logLane ≤ L.vars
  lanes_le : L.lanes.length ≤ 2 ^ laneFold
  overflow_eq : L.overflow = overflowLane
  overflow_lane : L.lanes[overflowLane]? = some .overflow
  held_lt : L.pieces.length < 2 ^ (L.logLane - s)
  gadget_lt : gadget < 2 ^ s
  nodup : L.pieces.Nodup
  piece_lt : ∀ p ∈ L.pieces, p < 2 ^ (L.vars - s)
  blocks_nodup : (laneBlocks L.lanes).Nodup
  block_lt : ∀ b ∈ laneBlocks L.lanes, b < 2 ^ (L.vars - L.logLane)
  first_mem : ∀ b ∈ laneBlocks L.lanes, b <<< (L.logLane - s) ∈ L.pieces
  first_only : ∀ b ∈ laneBlocks L.lanes, ∀ p ∈ L.pieces,
    p >>> (L.logLane - s) = b → p = b <<< (L.logLane - s)

/-- `NewHiddenOK` as one conjunction, whose decision the kernel evaluates. -/
def NewHiddenOKc (L : Layout) (s : ℕ) : Prop :=
  L.logPiece = some s ∧ laneFold ≤ L.logN ∧ s < L.logLane ∧ L.logLane ≤ L.vars ∧
    L.lanes.length ≤ 2 ^ laneFold ∧ L.overflow = overflowLane ∧
    L.lanes[overflowLane]? = some .overflow ∧ L.pieces.length < 2 ^ (L.logLane - s) ∧
    gadget < 2 ^ s ∧ L.pieces.Nodup ∧ (∀ p ∈ L.pieces, p < 2 ^ (L.vars - s)) ∧
    (laneBlocks L.lanes).Nodup ∧ (∀ b ∈ laneBlocks L.lanes, b < 2 ^ (L.vars - L.logLane)) ∧
    (∀ b ∈ laneBlocks L.lanes, b <<< (L.logLane - s) ∈ L.pieces) ∧
    ∀ b ∈ laneBlocks L.lanes, ∀ p ∈ L.pieces,
      p >>> (L.logLane - s) = b → p = b <<< (L.logLane - s)

instance (L : Layout) (s : ℕ) : Decidable (NewHiddenOKc L s) := by
  unfold NewHiddenOKc; infer_instance

theorem newHiddenOKc_iff (L : Layout) (s : ℕ) : NewHiddenOKc L s ↔ NewHiddenOK L s :=
  ⟨fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ ↦
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩,
    fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15⟩⟩

instance (L : Layout) (s : ℕ) : Decidable (NewHiddenOK L s) :=
  decidable_of_iff _ (newHiddenOKc_iff L s)

/-- `NewHiddenOK` as a `Bool`. -/
def newHiddenOKb (L : Layout) (s : ℕ) : Bool := decide (NewHiddenOK L s)

theorem newHiddenOKb_iff (L : Layout) (s : ℕ) : newHiddenOKb L s = true ↔ NewHiddenOK L s :=
  decide_eq_true_iff

theorem mem_laneBlocks {lanes : List Lane} {b : ℕ} : b ∈ laneBlocks lanes ↔ Lane.block b ∈ lanes := by
  simp only [laneBlocks, List.mem_filterMap]
  constructor
  · rintro ⟨lane, hl, hf⟩
    rcases lane with b' | _ | _ <;> simp at hf
    subst hf
    exact hl
  · intro h
    exact ⟨_, h, rfl⟩

namespace NewHiddenOK

variable {L : Layout} {s : ℕ}

theorem logN_eq (hL : NewHiddenOK L s) : L.logN = L.logLane + laneFold := by
  have := hL.six_le
  unfold Layout.logLane
  omega

theorem ov_lt (hL : NewHiddenOK L s) : L.overflow < L.lanes.length := by
  have h := hL.overflow_lane
  rw [hL.overflow_eq]
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

theorem ov_lane (hL : NewHiddenOK L s) : L.lanes[L.overflow]? = some .overflow := by
  rw [hL.overflow_eq]
  exact hL.overflow_lane

theorem s_le_vars (hL : NewHiddenOK L s) : s ≤ L.vars := by
  have := hL.s_lt
  have := hL.lane_le
  omega

theorem lt_of_piece (hL : NewHiddenOK L s) {t : ℕ} (h : t >>> s ∈ L.pieces) : t < 2 ^ L.vars := by
  have h1 := hL.piece_lt _ h
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
    Nat.sub_add_cancel hL.s_le_vars] at h1
  exact h1

theorem lt_of_block (hL : NewHiddenOK L s) {t : ℕ}
    (h : Lane.block (t >>> s >>> (L.logLane - s)) ∈ L.lanes) : t < 2 ^ L.vars := by
  have h1 := hL.block_lt _ (mem_laneBlocks.2 h)
  rw [← Nat.shiftRight_add, Nat.add_sub_cancel' hL.s_lt.le, Nat.shiftRight_eq_div_pow,
    Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hL.lane_le] at h1
  exact h1

end NewHiddenOK

/-! ## Reading the honest stack -/

theorem div_piece {s a o : ℕ} (ho : o < 2 ^ s) : (a * 2 ^ s + o) / 2 ^ s = a := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt ho, zero_add]

theorem mod_piece {s a o : ℕ} (ho : o < 2 ^ s) : (a * 2 ^ s + o) % 2 ^ s = o := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]

theorem getD_ofFn {n : ℕ} (f : Fin n → K) {i : ℕ} (h : i < n) :
    (Vector.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Vector.getD, h]

/-- The honest stack's entry `y` of a placed lane `l` is `wordNew`. -/
theorem laneWord_fillNew {L : Layout} (hN : L.logN = L.logLane + laneFold)
    (hlanes : L.lanes.length ≤ 2 ^ laneFold) (s : ℕ) (T : ℕ → K) (pad : ℕ → ℕ → K) {l y : ℕ}
    (hl : l < L.lanes.length) (hy : y < 2 ^ L.logLane) :
    laneWord (L.fillNew s T pad) L.logLane l y = L.wordNew s T pad l y := by
  have hx : y + 2 ^ L.logLane * l < 2 ^ L.logN := by
    rw [hN, pow_add]
    calc y + 2 ^ L.logLane * l < 2 ^ L.logLane * (l + 1) := by rw [mul_add, mul_one]; omega
      _ ≤ 2 ^ L.logLane * 2 ^ laneFold := Nat.mul_le_mul_left _ (by omega)
  have hdiv : (y + 2 ^ L.logLane * l) / 2 ^ L.logLane = l := by
    rw [mul_comm, add_comm]; exact div_piece hy
  have hmod : (y + 2 ^ L.logLane * l) % 2 ^ L.logLane = y := by
    rw [mul_comm, add_comm]; exact mod_piece hy
  unfold laneWord Layout.fillNew
  rw [getD_ofFn _ hx]
  simp only [hdiv, hmod, if_pos hl]

theorem gadgetEntry_lt {s g i : ℕ} (hs : gadget < 2 ^ s) (hg : g < 3) (hi : i < 3) :
    gadgetEntry s g i < 2 ^ s := by
  unfold gadgetEntry gadget at *
  omega

theorem gadgetFix_of_le {s l y : ℕ} (hs : gadget < 2 ^ s) (hy : 2 ^ s ≤ y) :
    gadgetFix s l y = none := by
  unfold gadgetFix
  rw [List.findSome?_eq_none_iff]
  intro g hg
  rw [List.findSome?_eq_none_iff]
  intro i hi
  have := gadgetEntry_lt hs (List.mem_range.1 hg) (List.mem_range.1 hi)
  rw [if_neg (by omega)]

/-- Past the first piece, the gadget writes nothing. -/
theorem wordNew_of_le {L : Layout} {s : ℕ} (hs : gadget < 2 ^ s) (T : ℕ → K) (pad : ℕ → ℕ → K)
    {l y : ℕ} (hy : 2 ^ s ≤ y) : L.wordNew s T pad l y = L.laneFill s T pad l y := by
  unfold Layout.wordNew
  rw [gadgetFix_of_le hs hy]

/-- **The table read back from the honest stack** (`Table::read` of `Table::hidden_in`): for a
layout of the shape `Layout::hidden_with` gives, every table `T`, every padding and every entry `t`,
`T t` where the layout holds the entry and zero elsewhere. -/
theorem readNew_fillNew {L : Layout} {s : ℕ} (hL : NewHiddenOK L s) (T : ℕ → K)
    (pad : ℕ → ℕ → K) (t : ℕ) :
    L.readNew s (L.fillNew s T pad) t = if L.CoveredNew s t then T t else 0 := by
  have hN := hL.logN_eq
  have hsl := hL.s_lt
  have hps : 0 < 2 ^ s := by positivity
  have ho : t % 2 ^ s < 2 ^ s := Nat.mod_lt _ hps
  have hwin : 2 ^ L.logLane = 2 ^ (L.logLane - s) * 2 ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hsl.le]
  have ht : t = (t >>> s) * 2 ^ s + t % 2 ^ s := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_add_mod']
  dsimp only [Layout.readNew]
  rcases hk : L.pieces.findIdx? (· == t >>> s) with _ | k
  · have hnot : t >>> s ∉ L.pieces := by
      intro hm
      have := List.findIdx?_eq_none_iff.1 hk _ hm
      simp at this
    rcases hl : L.lanes.findIdx? (· == Lane.block (t >>> s >>> (L.logLane - s))) with _ | l
    · rw [if_neg]
      rintro ⟨-, hp | hb⟩
      · exact hnot hp
      · have := List.findIdx?_eq_none_iff.1 hl _ hb
        simp at this
    · dsimp only
      obtain ⟨hll, hlp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hl
      have hlb : L.lanes[l] = .block (t >>> s >>> (L.logLane - s)) := by simpa using hlp
      have hbm : Lane.block (t >>> s >>> (L.logLane - s)) ∈ L.lanes := hlb ▸ List.getElem_mem hll
      rw [if_pos ⟨hL.lt_of_block hbm, Or.inr hbm⟩, Nat.and_two_pow_sub_one_eq_mod]
      have hdm := Nat.div_add_mod (t >>> s) (2 ^ (L.logLane - s))
      have hjlt : (t >>> s) % 2 ^ (L.logLane - s) < 2 ^ (L.logLane - s) :=
        Nat.mod_lt _ (by positivity)
      have hj0 : (t >>> s) % 2 ^ (L.logLane - s) ≠ 0 := by
        intro h0
        apply hnot
        have hfirst := hL.first_mem _ (mem_laneBlocks.2 hbm)
        rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow (t >>> s)] at hfirst
        rw [h0, add_zero] at hdm
        rw [mul_comm] at hdm
        rwa [hdm] at hfirst
      have hy : (t >>> s) % 2 ^ (L.logLane - s) * 2 ^ s + t % 2 ^ s < 2 ^ L.logLane := by
        rw [hwin]
        calc (t >>> s) % 2 ^ (L.logLane - s) * 2 ^ s + t % 2 ^ s
            < (t >>> s) % 2 ^ (L.logLane - s) * 2 ^ s + 2 ^ s := by omega
          _ = ((t >>> s) % 2 ^ (L.logLane - s) + 1) * 2 ^ s := by ring
          _ ≤ 2 ^ (L.logLane - s) * 2 ^ s := Nat.mul_le_mul_right _ hjlt
      have hy2 : 2 ^ s ≤ (t >>> s) % 2 ^ (L.logLane - s) * 2 ^ s + t % 2 ^ s := by
        calc 2 ^ s = 1 * 2 ^ s := (one_mul _).symm
          _ ≤ (t >>> s) % 2 ^ (L.logLane - s) * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := Nat.le_add_right _ _
      rw [laneWord_fillNew hN hL.lanes_le s T pad hll hy, wordNew_of_le hL.gadget_lt T pad hy2]
      unfold Layout.laneFill
      rw [if_neg (by omega), List.getElem?_eq_getElem hll, hlb]
      dsimp only
      congr 1
      rw [Nat.shiftLeft_eq, hwin, Nat.shiftRight_eq_div_pow (t >>> s)]
      conv_rhs => rw [ht]
      calc (t >>> s) / 2 ^ (L.logLane - s) * (2 ^ (L.logLane - s) * 2 ^ s) +
            ((t >>> s) % 2 ^ (L.logLane - s) * 2 ^ s + t % 2 ^ s)
          = (2 ^ (L.logLane - s) * ((t >>> s) / 2 ^ (L.logLane - s)) +
              (t >>> s) % 2 ^ (L.logLane - s)) * 2 ^ s + t % 2 ^ s := by ring
        _ = (t >>> s) * 2 ^ s + t % 2 ^ s := by rw [hdm]
  · dsimp only
    obtain ⟨hkl, hkp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hk
    have hpk : L.pieces[k] = t >>> s := by simpa using hkp
    have hm : t >>> s ∈ L.pieces := hpk ▸ List.getElem_mem hkl
    rw [if_pos ⟨hL.lt_of_piece hm, Or.inl hm⟩]
    have hk2 : k + 2 ≤ 2 ^ (L.logLane - s) := by have := hL.held_lt; omega
    have hy : (k + 1) * 2 ^ s + t % 2 ^ s < 2 ^ L.logLane := by
      rw [hwin]
      calc (k + 1) * 2 ^ s + t % 2 ^ s < (k + 1) * 2 ^ s + 2 ^ s := by omega
        _ = (k + 2) * 2 ^ s := by ring
        _ ≤ 2 ^ (L.logLane - s) * 2 ^ s := Nat.mul_le_mul_right _ hk2
    have hy2 : 2 ^ s ≤ (k + 1) * 2 ^ s + t % 2 ^ s := by
      calc 2 ^ s ≤ (k + 1) * 2 ^ s := Nat.le_mul_of_pos_left _ (by omega)
        _ ≤ _ := Nat.le_add_right _ _
    rw [laneWord_fillNew hN hL.lanes_le s T pad hL.ov_lt hy, wordNew_of_le hL.gadget_lt T pad hy2]
    unfold Layout.laneFill
    rw [if_neg (by omega), hL.ov_lane]
    dsimp only
    rw [div_piece ho, mod_piece ho, if_pos (by omega), Nat.add_sub_cancel,
      List.getD_eq_getElem _ _ hkl, hpk]
    exact congrArg T ht.symm

/-- **A table that vanishes off the entries the layout holds is read back whole** from the honest
stack, for every padding. -/
theorem readNew_fillNew_eq {L : Layout} {s : ℕ} (hL : NewHiddenOK L s) (T : ℕ → K)
    (hT : ∀ t, ¬ L.CoveredNew s t → T t = 0) (pad : ℕ → ℕ → K) (t : ℕ) :
    L.readNew s (L.fillNew s T pad) t = T t := by
  rw [readNew_fillNew hL]
  split_ifs with h
  · rfl
  · exact (hT t h).symm

/-! ## Coverage: `Layout.hiddenNew` holds its chunks -/

theorem mem_chunkBlocks {logChunk logLane : ℕ} {chunks : List (ℕ × ℕ)} {c len k : ℕ}
    (hmem : (c, len) ∈ chunks) (hk : k < len >>> logLane) :
    c <<< (logChunk - logLane) + k ∈ chunkBlocks logChunk logLane chunks := by
  simp only [chunkBlocks, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨(c, len), hmem, k, hk, rfl⟩

theorem mem_chunkTails {logChunk logLane logPiece : ℕ} {chunks : List (ℕ × ℕ)} {c len k : ℕ}
    (hmem : (c, len) ∈ chunks)
    (hk : k < (len - ((len >>> logLane) <<< logLane) + 2 ^ logPiece - 1) / 2 ^ logPiece) :
    ((c <<< (logChunk - logLane)) + (len >>> logLane)) <<< (logLane - logPiece) + k ∈
      chunkTails logChunk logLane logPiece chunks := by
  simp only [chunkTails, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨(c, len), hmem, k, hk, rfl⟩

theorem block_mem_hiddenLanes {blocks : List ℕ} {random b : ℕ} (hb : b ∈ blocks) :
    Lane.block b ∈ hiddenLanes blocks random := by
  unfold hiddenLanes
  rw [← List.take_append_drop (min blocks.length overflowLane) blocks] at hb
  rcases List.mem_append.1 hb with h | h
  · apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map_of_mem h
  · apply List.mem_append_right
    exact List.mem_map_of_mem h

/-- **Every entry of a chunk is held** by `Layout.hiddenNew`: entry `j < len` of chunk `(c, len)` is
in a whole block (on a lane) or in a tail piece (an overflow piece), given the Rust's assertions
`log_piece ≤ log_lane ≤ log_chunk ≤ vars`, `c < 2^(vars − log_chunk)`, `len ≤ 2^log_chunk`. -/
theorem coveredNew_hiddenNew {vars logChunk logN random s : ℕ} {chunks : List (ℕ × ℕ)}
    (hs : s ≤ logN - laneFold) (hl : logN - laneFold ≤ logChunk) (hv : logChunk ≤ vars)
    {c len j : ℕ} (hmem : (c, len) ∈ chunks) (hc : c < 2 ^ (vars - logChunk))
    (hlen : len ≤ 2 ^ logChunk) (hj : j < len) :
    (Layout.hiddenNew vars logChunk logN chunks random s).CoveredNew s (c * 2 ^ logChunk + j) := by
  set ℓ := logN - laneFold with hℓ
  refine ⟨?_, ?_⟩
  · show c * 2 ^ logChunk + j < 2 ^ vars
    calc c * 2 ^ logChunk + j < (c + 1) * 2 ^ logChunk := by rw [add_mul, one_mul]; omega
      _ ≤ 2 ^ (vars - logChunk) * 2 ^ logChunk := Nat.mul_le_mul_right _ hc
      _ = 2 ^ vars := by rw [← pow_add, Nat.sub_add_cancel hv]
  · show (c * 2 ^ logChunk + j) >>> s ∈ (laneBlocks (hiddenLanes (chunkBlocks logChunk ℓ chunks) random)).map
        (· <<< (ℓ - s)) ++ chunkTails logChunk ℓ s chunks ∨
      Lane.block ((c * 2 ^ logChunk + j) >>> s >>> (ℓ - s)) ∈
        hiddenLanes (chunkBlocks logChunk ℓ chunks) random
    have e1 : 2 ^ logChunk = 2 ^ (logChunk - ℓ) * 2 ^ ℓ := by rw [← pow_add, Nat.sub_add_cancel hl]
    have e2 : 2 ^ ℓ = 2 ^ (ℓ - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
    have hw : len >>> ℓ = len / 2 ^ ℓ := Nat.shiftRight_eq_div_pow _ _
    by_cases hjw : j < (len >>> ℓ) * 2 ^ ℓ
    · right
      have hblk : (c * 2 ^ logChunk + j) >>> s >>> (ℓ - s) = c <<< (logChunk - ℓ) + j / 2 ^ ℓ := by
        rw [← Nat.shiftRight_add, Nat.add_sub_cancel' hs, Nat.shiftRight_eq_div_pow,
          Nat.shiftLeft_eq, e1,
          show c * (2 ^ (logChunk - ℓ) * 2 ^ ℓ) + j = j + c * 2 ^ (logChunk - ℓ) * 2 ^ ℓ by ring,
          Nat.add_mul_div_right _ _ (by positivity), add_comm]
      rw [hblk]
      apply block_mem_hiddenLanes
      exact mem_chunkBlocks hmem (by rw [Nat.div_lt_iff_lt_mul (by positivity)]; exact hjw)
    · left
      push_neg at hjw
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hjw
      have hrl : r < len - (len >>> ℓ) <<< ℓ := by rw [Nat.shiftLeft_eq]; omega
      have hpiece : (c * 2 ^ logChunk + j) >>> s =
          ((c <<< (logChunk - ℓ)) + (len >>> ℓ)) <<< (ℓ - s) + r / 2 ^ s := by
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.shiftLeft_eq, hr, e1, e2,
          show c * (2 ^ (logChunk - ℓ) * (2 ^ (ℓ - s) * 2 ^ s)) +
              ((len >>> ℓ) * (2 ^ (ℓ - s) * 2 ^ s) + r) =
            r + (c * 2 ^ (logChunk - ℓ) + (len >>> ℓ)) * 2 ^ (ℓ - s) * 2 ^ s by ring,
          Nat.add_mul_div_right _ _ (by positivity), add_comm]
      rw [hpiece]
      apply List.mem_append_right
      apply mem_chunkTails hmem
      have hps : 0 < 2 ^ s := by positivity
      calc r / 2 ^ s < r / 2 ^ s + 1 := Nat.lt_succ_self _
        _ = (r + 2 ^ s) / 2 ^ s := (Nat.add_div_right r hps).symm
        _ ≤ _ := Nat.div_le_div_right (by omega)

/-- The entries of the chunks: `c·2^log_chunk + j`, `(c, len)` a chunk, `j < len`. -/
def InChunks (logChunk : ℕ) (chunks : List (ℕ × ℕ)) (t : ℕ) : Prop :=
  ∃ c ∈ chunks, ∃ j < c.2, t = c.1 * 2 ^ logChunk + j

/-- **A table that vanishes off its chunks is read back whole** from the honest stack of
`Layout.hiddenNew`, for every padding. -/
theorem readNew_fillNew_hiddenNew {vars logChunk logN random s : ℕ} {chunks : List (ℕ × ℕ)}
    (hL : NewHiddenOK (Layout.hiddenNew vars logChunk logN chunks random s) s)
    (hl : logN - laneFold ≤ logChunk) (hv : logChunk ≤ vars)
    (hch : ∀ c ∈ chunks, c.1 < 2 ^ (vars - logChunk) ∧ c.2 ≤ 2 ^ logChunk)
    (T : ℕ → K) (hT : ∀ t, ¬ InChunks logChunk chunks t → T t = 0) (pad : ℕ → ℕ → K) (t : ℕ) :
    (Layout.hiddenNew vars logChunk logN chunks random s).readNew s
      ((Layout.hiddenNew vars logChunk logN chunks random s).fillNew s T pad) t = T t := by
  refine readNew_fillNew_eq hL T (fun t ht ↦ hT t ?_) pad t
  rintro ⟨⟨c, len⟩, hmem, j, hj, rfl⟩
  exact ht (coveredNew_hiddenNew hL.s_lt.le hl hv hmem (hch _ hmem).1 (hch _ hmem).2 hj)

/-! ## The gadget -/

theorem gadgetEntry_inj {s g i g' i' : ℕ} :
    gadgetEntry s g i = gadgetEntry s g' i' ↔ 3 * g + i = 3 * g' + i' := by
  unfold gadgetEntry
  omega

theorem range_three : List.range 3 = [0, 1, 2] := rfl

/-- Lanes `0` and `1`, the pairs' first lanes, are never written by the gadget. -/
theorem gadgetFix_src {s l y : ℕ} (hl : l = 0 ∨ l = 1) : gadgetFix s l y = none := by
  unfold gadgetFix
  rw [List.findSome?_eq_none_iff]
  intro g hg
  rw [List.findSome?_eq_none_iff]
  intro i _
  have hg3 := List.mem_range.1 hg
  split_ifs
  · interval_cases g <;> simp only [gadgetLanes, overflowLane] <;> rcases hl with rfl | rfl <;> simp
  · rfl

theorem gadgetFix_pair0 {s i : ℕ} (hi : i < 3) : gadgetFix s 31 (gadgetEntry s 0 i) = some (some 0) := by
  interval_cases i <;> simp [gadgetFix, range_three, gadgetEntry_inj, gadgetLanes]

theorem gadgetFix_pair1 {s i : ℕ} (hi : i < 3) : gadgetFix s 30 (gadgetEntry s 1 i) = some (some 1) := by
  interval_cases i <;> simp [gadgetFix, range_three, gadgetEntry_inj, gadgetLanes]

theorem gadgetFix_overflow {s i : ℕ} (hi : i < 3) :
    gadgetFix s overflowLane (gadgetEntry s 2 i) = some none := by
  interval_cases i <;> simp [gadgetFix, range_three, gadgetEntry_inj, gadgetLanes, overflowLane]

section gadget

variable {L : Layout} {s : ℕ} (hL : NewHiddenOK L s) (T : ℕ → K) (pad : ℕ → ℕ → K)
include hL

theorem gadgetEntry_lt_lane {g i : ℕ} (hg : g < 3) (hi : i < 3) : gadgetEntry s g i < 2 ^ L.logLane :=
  lt_trans (gadgetEntry_lt hL.gadget_lt hg hi) (Nat.pow_lt_pow_right (by norm_num) hL.s_lt)

theorem lanes_gt : overflowLane < L.lanes.length := by
  have := hL.ov_lt
  rwa [hL.overflow_eq] at this

/-- **The gadget's first pair**: at its pattern's entries, lane `31` holds lane `0`'s word. -/
theorem gadget_pair0 {i : ℕ} (hi : i < 3) :
    laneWord (L.fillNew s T pad) L.logLane 31 (gadgetEntry s 0 i) =
      laneWord (L.fillNew s T pad) L.logLane 0 (gadgetEntry s 0 i) := by
  have hlen := lanes_gt hL
  unfold overflowLane at hlen
  have hy := gadgetEntry_lt_lane hL (by norm_num : 0 < 3) hi
  rw [laneWord_fillNew hL.logN_eq hL.lanes_le s T pad (by omega) hy,
    laneWord_fillNew hL.logN_eq hL.lanes_le s T pad (by omega) hy]
  unfold Layout.wordNew
  rw [gadgetFix_pair0 hi, gadgetFix_src (Or.inl rfl)]

/-- **The gadget's second pair**: at its pattern's entries, lane `30` holds lane `1`'s word. -/
theorem gadget_pair1 {i : ℕ} (hi : i < 3) :
    laneWord (L.fillNew s T pad) L.logLane 30 (gadgetEntry s 1 i) =
      laneWord (L.fillNew s T pad) L.logLane 1 (gadgetEntry s 1 i) := by
  have hlen := lanes_gt hL
  unfold overflowLane at hlen
  have hy := gadgetEntry_lt_lane hL (by norm_num : 1 < 3) hi
  rw [laneWord_fillNew hL.logN_eq hL.lanes_le s T pad (by omega) hy,
    laneWord_fillNew hL.logN_eq hL.lanes_le s T pad (by omega) hy]
  unfold Layout.wordNew
  rw [gadgetFix_pair1 hi, gadgetFix_src (Or.inr rfl)]

/-- **The gadget's lone lane**: at its pattern's entries, the overflow lane holds zero. -/
theorem gadget_overflow {i : ℕ} (hi : i < 3) :
    laneWord (L.fillNew s T pad) L.logLane overflowLane (gadgetEntry s 2 i) = 0 := by
  have hy := gadgetEntry_lt_lane hL (by norm_num : 2 < 3) hi
  rw [laneWord_fillNew hL.logN_eq hL.lanes_le s T pad (lanes_gt hL) hy]
  unfold Layout.wordNew
  rw [gadgetFix_overflow hi]

/-- **Each pattern cancels at each of its entries**: the sum over the pattern's lanes of the honest
stack's words there is zero in `E` (two equal words in characteristic two, or one zero). -/
theorem gadget_cancel {g i : ℕ} (hg : g < 3) (hi : i < 3) :
    ((gadgetLanes g).map fun l ↦
      ofK (laneWord (L.fillNew s T pad) L.logLane l (gadgetEntry s g i))).sum = 0 := by
  interval_cases g
  · simp only [gadgetLanes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [gadget_pair0 hL T pad hi]
    exact CharTwo.add_self_eq_zero _
  · simp only [gadgetLanes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [gadget_pair1 hL T pad hi]
    exact CharTwo.add_self_eq_zero _
  · simp only [gadgetLanes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [gadget_overflow hL T pad hi]
    exact map_zero (algebraMap K E)

/-- **The honest stack cancels the gadget**: for every `β`, `Σ_{g<3} Σ_{i<3} β_i ·
Σ_{l ∈ gadget_lanes(g)} stack(l, gadget_entry(g, i)) = 0`. -/
theorem gadget_sum_zero (β : Fin 3 → E) :
    ∑ g ∈ range 3, ∑ i : Fin 3, β i * ((gadgetLanes g).map fun l ↦
      ofK (laneWord (L.fillNew s T pad) L.logLane l (gadgetEntry s g i))).sum = 0 := by
  refine Finset.sum_eq_zero fun g hg ↦ Finset.sum_eq_zero fun i _ ↦ ?_
  rw [gadget_cancel hL T pad (Finset.mem_range.1 hg) i.2, mul_zero]

end gadget

/-! ## The gadget's weight on the cube -/

/-- **The gadget's weight at entry `y` of lane `l`**, for weights `β`: `Σ_g [l ∈ gadget_lanes(g)] ·
Σ_i β_i [y = gadget_entry(g, i)]`, the gadget term of `opening::verify`'s weight
(`opening.rs:786-806`: `on = Σ_{l ∈ pattern} lane_eq[l]` times `Σ_i β_i eq_index(low, y_i)`) at a
cube point, unscaled. -/
def gadgetWeight (β : Fin 3 → E) (s l y : ℕ) : E :=
  ∑ g ∈ range 3, (if l ∈ gadgetLanes g then 1 else 0) *
    ∑ i : Fin 3, β i * (if y = gadgetEntry s g i then 1 else 0)

/-- `Layout::gadget_at(l, y)` (`opening.rs:253-261`) for weights `β` (the Rust's `gadget_beta`): `β_{k
mod 3}` if `k = y − (2^s − GADGET)` is below `GADGET` and `l` is in pattern `k / 3`, else zero. -/
def gadgetAt (β : Fin 3 → E) (s l y : ℕ) : E :=
  if h : 2 ^ s - gadget ≤ y ∧ y - (2 ^ s - gadget) < gadget ∧
      l ∈ gadgetLanes ((y - (2 ^ s - gadget)) / 3) then
    β ⟨(y - (2 ^ s - gadget)) % 3, Nat.mod_lt _ (by norm_num)⟩
  else 0

/-- `gadget_at` is the verifier's gadget weight on the cube. -/
theorem gadgetAt_eq (β : Fin 3 → E) (s l y : ℕ) : gadgetAt β s l y = gadgetWeight β s l y := by
  unfold gadgetAt gadgetWeight
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := h
    have hg : (y - (2 ^ s - gadget)) / 3 < 3 := by unfold gadget at *; omega
    rw [Finset.sum_eq_single_of_mem ((y - (2 ^ s - gadget)) / 3) (Finset.mem_range.2 hg)]
    · rw [if_pos h3, one_mul,
        Finset.sum_eq_single_of_mem (⟨(y - (2 ^ s - gadget)) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)
          (Finset.mem_univ _)]
      · rw [if_pos (by dsimp only; unfold gadgetEntry; unfold gadget at *; omega), mul_one]
      · intro i _ hi
        rw [if_neg, mul_zero]
        intro he
        apply hi
        ext
        simp only
        unfold gadgetEntry at he
        unfold gadget at *
        omega
    · intro g _ hg'
      rw [Finset.sum_eq_zero, mul_zero]
      intro i _
      rw [if_neg, mul_zero]
      intro he
      apply hg'
      unfold gadgetEntry at he
      unfold gadget at *
      have := i.2
      omega
  · symm
    refine Finset.sum_eq_zero fun g hg ↦ ?_
    have hg3 := Finset.mem_range.1 hg
    split_ifs with hl
    · rw [one_mul]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [if_neg, mul_zero]
      intro he
      apply h
      have hi := i.2
      have hq : (y - (2 ^ s - gadget)) / 3 = g := by
        unfold gadgetEntry at he; unfold gadget at *; omega
      refine ⟨by unfold gadgetEntry at he; unfold gadget at *; omega,
        by unfold gadgetEntry at he; unfold gadget at *; omega, ?_⟩
      rw [hq]
      exact hl
    · rw [zero_mul]

theorem gadgetLanes_nodup (g : ℕ) : (gadgetLanes g).Nodup := by
  unfold gadgetLanes
  split <;> simp [overflowLane]

theorem gadgetLanes_lt {g l : ℕ} (hl : l ∈ gadgetLanes g) : l ≤ overflowLane := by
  unfold gadgetLanes at hl
  split at hl <;> simp [overflowLane] at hl ⊢ <;> omega

/-- **The gadget's weight pairs to zero with the honest stack**: summed over the placed lanes and
their entries, `Σ_l Σ_y gadget(l, y) · stack(l, y) = 0` for every `β`. -/
theorem gadgetWeight_sum_zero {L : Layout} {s : ℕ} (hL : NewHiddenOK L s) (T : ℕ → K)
    (pad : ℕ → ℕ → K) (β : Fin 3 → E) :
    ∑ l ∈ range L.lanes.length, ∑ y ∈ range (2 ^ L.logLane),
      gadgetWeight β s l y * ofK (laneWord (L.fillNew s T pad) L.logLane l y) = 0 := by
  have hexp : ∀ l y, gadgetWeight β s l y * ofK (laneWord (L.fillNew s T pad) L.logLane l y) =
      ∑ g ∈ range 3, ∑ i : Fin 3, if y = gadgetEntry s g i then
        (if l ∈ gadgetLanes g then β i * ofK (laneWord (L.fillNew s T pad) L.logLane l y) else 0)
      else 0 := by
    intro l y
    unfold gadgetWeight
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring
  have step1 : ∀ l ∈ range L.lanes.length, ∑ y ∈ range (2 ^ L.logLane),
      gadgetWeight β s l y * ofK (laneWord (L.fillNew s T pad) L.logLane l y) =
      ∑ g ∈ range 3, ∑ i : Fin 3, if l ∈ gadgetLanes g then
        β i * ofK (laneWord (L.fillNew s T pad) L.logLane l (gadgetEntry s g i)) else 0 := by
    intro l _
    simp_rw [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g hg ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.2
      (gadgetEntry_lt_lane hL (Finset.mem_range.1 hg) i.2))]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_eq_zero fun g hg ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [← Finset.sum_filter]
  have hfilter : (range L.lanes.length).filter (· ∈ gadgetLanes g) = (gadgetLanes g).toFinset := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨lt_of_le_of_lt (gadgetLanes_lt h) (lanes_gt hL), h⟩⟩
  rw [hfilter, List.sum_toFinset _ (gadgetLanes_nodup g), List.sum_map_mul_left,
    gadget_cancel hL T pad (Finset.mem_range.1 hg) i.2, mul_zero]

/-! ## The deployed layouts (`protocol.rs:117-130`) -/

/-- `witness_layout(log_rows)` (`protocol.rs:117-120`) in the redesigned layout:
`Layout::hidden(m + 1, m, m + 1, [(0, 2^m), (1, 16)], WITNESS_RANDOM_LANES = 7)`, `LOG_PIECE = 8`. -/
def witnessLayoutNew (r : ℕ) : Layout :=
  Layout.hiddenNew (cellVars r + 1) (cellVars r) (cellVars r + 1)
    [(0, 2 ^ cellVars r), (1, 16)] 7 8

/-- `quotient_layout(log_rows)` (`protocol.rs:127-130`) in the redesigned layout:
`Layout::hidden(m + 6, m, m + 4, quotient_chunks(m, Q_SPILL, 64), QUOTIENT_RANDOM_LANES = 7)`,
`LOG_PIECE = 8`. -/
def quotientLayoutNew (r : ℕ) : Layout :=
  Layout.hiddenNew (cellVars r + 6) (cellVars r) (cellVars r + 4)
    (quotientChunks (cellVars r) qSpill 64) 7 8

/-- The Rust's own check of `Layout::hidden` (`opening.rs`, `claims_open_against_a_hidden_table`):
five blocks on lanes `0..5`, random lanes to `32`, the overflow lane and seven random lanes; `5 + 12 + 3`
pieces. -/
example : let L := Layout.hiddenNew 20 15 20 [(3, 2 ^ 15), (0, 3000), (9, 2 ^ 14 + 700), (5, 2 ^ 15)] 7 8
    (L.lanes.length, L.pieces.length, L.overflow) = (32 + 1 + 7, 5 + 12 + 3, 32) ∧ NewHiddenOK L 8 := by
  decide +kernel

/-- **The deployed layouts have the shape** at `LOG_ROWS = 22`. -/
theorem deployed_newHiddenOK :
    NewHiddenOK (witnessLayoutNew logRows) 8 ∧ NewHiddenOK (quotientLayoutNew logRows) 8 := by
  decide +kernel

/-- **The deployed layouts' shape** at `LOG_ROWS = 22`: `40` and `63` lanes, the overflow lane `32`,
`33` and `167` pieces, stacks of `25` and `28` variables. -/
theorem deployed_shape :
    (witnessLayoutNew logRows).lanes.length = 40 ∧ (quotientLayoutNew logRows).lanes.length = 63 ∧
      (witnessLayoutNew logRows).overflow = 32 ∧ (quotientLayoutNew logRows).overflow = 32 ∧
      (witnessLayoutNew logRows).pieces.length = 33 ∧
      (quotientLayoutNew logRows).pieces.length = 167 ∧
      (witnessLayoutNew logRows).logN = 25 ∧ (quotientLayoutNew logRows).logN = 28 := by
  decide +kernel

/-- The chunks' conditions of the deployed layouts (`Layout::hidden_with`'s assertions). -/
theorem deployed_chunks :
    (∀ c ∈ [(0, 2 ^ cellVars logRows), (1, 16)],
      c.1 < 2 ^ (cellVars logRows + 1 - cellVars logRows) ∧ c.2 ≤ 2 ^ cellVars logRows) ∧
    (∀ c ∈ quotientChunks (cellVars logRows) qSpill 64,
      c.1 < 2 ^ (cellVars logRows + 6 - cellVars logRows) ∧ c.2 ≤ 2 ^ cellVars logRows) := by
  decide +kernel

/-- **Every entry of the witness table's chunks is held** by its layout. -/
theorem witness_covered {c : ℕ × ℕ} (hc : c ∈ [(0, 2 ^ cellVars logRows), (1, 16)]) {j : ℕ}
    (hj : j < c.2) : (witnessLayoutNew logRows).CoveredNew 8 (c.1 * 2 ^ cellVars logRows + j) :=
  coveredNew_hiddenNew (by decide) (by decide) (by decide) hc (deployed_chunks.1 c hc).1
    (deployed_chunks.1 c hc).2 hj

/-- **Every entry of the quotient table's chunks is held** by its layout. -/
theorem quotient_covered {c : ℕ × ℕ} (hc : c ∈ quotientChunks (cellVars logRows) qSpill 64) {j : ℕ}
    (hj : j < c.2) : (quotientLayoutNew logRows).CoveredNew 8 (c.1 * 2 ^ cellVars logRows + j) :=
  coveredNew_hiddenNew (by decide) (by decide) (by decide) hc (deployed_chunks.2 c hc).1
    (deployed_chunks.2 c hc).2 hj

/-- **The witness table is read back** from its honest stack: a table that vanishes off the witness
chunks, for every padding. -/
theorem witness_read (T : ℕ → K)
    (hT : ∀ t, ¬ InChunks (cellVars logRows) [(0, 2 ^ cellVars logRows), (1, 16)] t → T t = 0)
    (pad : ℕ → ℕ → K) (t : ℕ) :
    (witnessLayoutNew logRows).readNew 8 ((witnessLayoutNew logRows).fillNew 8 T pad) t = T t :=
  readNew_fillNew_hiddenNew deployed_newHiddenOK.1 (by decide) (by decide) deployed_chunks.1 T hT pad t

/-- **The quotient table is read back** from its honest stack: a table that vanishes off the
quotient chunks, for every padding. -/
theorem quotient_read (T : ℕ → K)
    (hT : ∀ t, ¬ InChunks (cellVars logRows) (quotientChunks (cellVars logRows) qSpill 64) t →
      T t = 0)
    (pad : ℕ → ℕ → K) (t : ℕ) :
    (quotientLayoutNew logRows).readNew 8 ((quotientLayoutNew logRows).fillNew 8 T pad) t = T t :=
  readNew_fillNew_hiddenNew deployed_newHiddenOK.2 (by decide) (by decide) deployed_chunks.2 T hT pad t

end Completeness
