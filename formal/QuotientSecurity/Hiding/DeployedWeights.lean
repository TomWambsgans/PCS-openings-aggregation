-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.DeployedLayout

/-!
# The deployed weight: `opening::verify`'s closure, and `WeightsFit`

`opening::verify` (`crates/quotient/src/opening.rs`) hands leanVM's WHIR verifier a closure: at a stack
point `x` (the lane's `ℓ` coordinates, then the lane index's six) it returns the combined weight of the
claims and the gadget, `Σ_c λ^c W_c(x) + λ^m G(x)`, as multilinear polynomials. Transcribed here
(`Layout.weight`, with `Layout::scales`, `ClaimWeight`, `eq`, `eq_index`, `gadget_lanes`,
`Layout::gadget_entry`; each `fold(ONE, w * f)` a product, each `fold(ZERO, s + f)` a sum), over any
field of characteristic 2. Its values on the Boolean cube are the weights the model reads:

* `claimW`: a claim's weight at lane `l`, entry `y`: the closure's term for the claim, with its power of
  `λ` pulled out (`claimTerm_part`), at the Boolean point of `(y, l)`;
* `weightsFit`: **the deployed claims meet `GadgetLayout.WeightsFit`**: they weigh nothing on the first
  piece below the gadget, at the gadget's entries, on the random lanes, nor on the overflow lane off its
  held pieces (the first-piece cancellation `above + first_above·first_piece = 0` there is
  characteristic 2's);
* `weight_bool`: **the closure at the Boolean point of `(y, l)` is `Σ_c λ^c W_c(l, y) + λ^m G(l, y)`**,
  `G = gadgetW pos β`, and `weight_combinedW`: it is the model's `combinedW pos (withGadget W G)
  (λ^·)` at the lane's index;
* `powers_snoc`: the closure's powers `λ^c` (`c ≤ m`) are `Fin.snoc (λ^·) (λ^m)`, the end theorem's
  claims' powers and gadget scale `μ = λ^m`.
-/

namespace QuotientSecurity.Hiding

open Finset

set_option linter.unusedSectionVars false

namespace Deployed

variable {E : Type} [Field E]

/-! ### The closure (`opening::verify`) -/

/-- `eq_bits(point, index)`, and the verifier's `eq_index(x, index)`: `Π_k (bit k of index ? p_k :
1 + p_k)` over the point's coordinates. -/
def eqBits (point : List E) (index : ℕ) : E :=
  ∏ k ∈ range point.length, if index.testBit k then point.getD k 0 else 1 + point.getD k 0

/-- `eq1(c, p) = c·p + (1 + c)(1 + p)`. -/
def eq1 (c p : E) : E := c * p + (1 + c) * (1 + p)

/-- `eq(a, b)`: `eq1` of the zipped coordinates. -/
def eqZ (a b : List E) : E := ∏ k ∈ range (min a.length b.length), eq1 (a.getD k 0) (b.getD k 0)

/-- `Π (1 + p)`. -/
def onePlusProd (l : List E) : E := ∏ k ∈ range l.length, (1 + l.getD k 0)

/-- `ClaimWeight`: a claim's lane coordinates, its block lanes' scales, its overflow pieces'. -/
structure Part (E : Type) where
  low : List E
  lanes : List E
  pieces : List E

namespace Layout

variable (L : Layout)

/-- `Layout::scales`, the lanes': `eq` of the point's coordinates above the lane at each block lane's
block, zero on the other lanes. -/
def laneScales (point : List E) : List E :=
  L.lanes.map fun
    | .block b => eqBits (point.drop L.logLane) b
    | _ => 0

/-- `Layout::scales`, the pieces': `eq` of the coordinates above a piece at each held piece. -/
def pieceScales (point : List E) : List E := L.pieces.map fun p => eqBits (point.drop L.logPiece) p

/-- `parts` (`verify`): a claim's `ClaimWeight`, its scales times its power `lam` of the challenge. -/
def part (lam : E) (point : List E) : Part E :=
  ⟨point.take L.logLane, (L.laneScales point).map (lam * ·), (L.pieceScales point).map (lam * ·)⟩

/-- `on_blocks`: the block lanes, each its scale times its `lane_eq`. -/
def onBlocks (laneEq : List E) (part : Part E) : E :=
  ∑ l ∈ range L.lanes.length,
    if (L.lanes.getD l .random).isBlock then part.lanes.getD l 0 * laneEq.getD l 0 else 0

/-- `pieces`: each held piece's scale times `eq_index(low[s..], k + 1)`. -/
def piecesTerm (s : ℕ) (low : List E) (part : Part E) : E :=
  ∑ k ∈ range part.pieces.length, part.pieces.getD k 0 * eqBits (low.drop s) (k + 1)

/-- One claim's term of the closure (the hidden branch): `below · ((above + first_above ·
first_piece) · on_blocks + pieces · on_overflow)`. -/
def claimTerm (laneEq low : List E) (part : Part E) : E :=
  let s := L.logPiece
  let below := eqZ (part.low.take s) (low.take s)
  let above := eqZ (part.low.drop s) (low.drop s)
  let firstAbove := onePlusProd (part.low.drop s)
  let firstPiece := onePlusProd (low.drop s)
  let onOverflow := laneEq.getD L.overflow 0
  below * ((above + firstAbove * firstPiece) * L.onBlocks laneEq part +
    piecesTerm s low part * onOverflow)

/-- The gadget's term: per pattern, its lanes' `lane_eq` times `Σ_i (scale·β_i)·eq_index(low,
entry_i)`. -/
def gadgetTerm (beta : Fin 3 → E) (scale : E) (laneEq low : List E) : E :=
  ∑ g : Fin 3, ((gadgetLanes g).map fun l => laneEq.getD l 0).sum *
    ∑ i : Fin 3, scale * beta i * eqBits low (gadgetEntry L.logPiece g i)

/-- **The weight closure** of `opening::verify` for claims at `points`, challenge `lam` (the claims'
powers `λ^c`, the gadget's `λ^m`) and the gadget's `β`, at a stack point `x`. -/
def weight {m : ℕ} (points : Fin m → List E) (lam : E) (beta : Fin 3 → E) (x : List E) : E :=
  let low := x.take L.logLane
  let high := x.drop L.logLane
  let laneEq := (List.range L.lanes.length).map (eqBits high)
  (∑ c : Fin m, L.claimTerm laneEq low (L.part (lam ^ (c : ℕ)) (points c))) +
    L.gadgetTerm beta (lam ^ m) laneEq low

end Layout

/-! ### The Boolean cube -/

/-- The Boolean point of `y` on `n` coordinates, low bit first. -/
def bits (n y : ℕ) : List E := (List.range n).map fun k => if y.testBit k then 1 else 0

/-- The stack point of entry `y` of lane `l`. -/
def boolPt (ℓ y l : ℕ) : List E := bits ℓ y ++ bits 6 l

namespace Layout

variable (L : Layout)

/-- `lane_eq` at the Boolean point of lane `l`. -/
def laneEqAt (l : ℕ) : List E := (List.range L.lanes.length).map (eqBits (bits 6 l))

/-- **The deployed claims' weights**: claim `c`'s term of the closure, before its power of `λ`, at
the Boolean point of entry `y` of lane `l`. -/
def claimW {m : ℕ} (points : Fin m → List E) :
    Fin m → Fin L.lanes.length → Fin (2 ^ L.logLane) → E :=
  fun c l y => L.claimTerm (L.laneEqAt l) (bits L.logLane y) (L.part 1 (points c))

end Layout

theorem length_bits (n y : ℕ) : (bits n y : List E).length = n := by simp [bits]

theorem getD_bits (n y k : ℕ) :
    (bits n y : List E).getD k 0 = if k < n then (if y.testBit k then 1 else 0) else 0 := by
  unfold bits
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : k < n <;> simp [hk]

variable (h2 : (2 : E) = 0)
include h2

theorem one_add_one_eq_zero : (1 : E) + 1 = 0 := by rw [one_add_one_eq_two, h2]

theorem eqBits_bits (n y idx : ℕ) :
    eqBits (bits n y : List E) idx = if ∀ k ∈ range n, idx.testBit k = y.testBit k then 1 else 0 := by
  rw [eqBits, length_bits, ← prod_boole]
  refine prod_congr rfl fun k hk => ?_
  rw [getD_bits, ite_eq_left (mem_range.mp hk)]
  have h11 := one_add_one_eq_zero h2
  cases idx.testBit k <;> cases y.testBit k <;> simp [h11]

omit h2 in
theorem testBits_iff {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (∀ k ∈ range n, a.testBit k = b.testBit k) ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < n
    · exact h k (mem_range.mpr hk)
    · have hn : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hn), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hn)]
  · rintro rfl _ _
    rfl

theorem eqBits_bits_eq {n y idx : ℕ} (hy : y < 2 ^ n) (hidx : idx < 2 ^ n) :
    eqBits (bits n y : List E) idx = if idx = y then 1 else 0 := by
  rw [eqBits_bits h2, if_congr (testBits_iff hidx hy) rfl rfl]

omit h2 in
theorem drop_bits (n s y : ℕ) : (bits n y : List E).drop s = bits (n - s) (y >>> s) := by
  apply List.ext_getElem
  · simp [length_bits]
  · intro k h1 h2'
    simp only [bits, List.getElem_drop, List.getElem_map, List.getElem_range, Nat.testBit_shiftRight]

theorem eqZ_bits (a : List E) (n y : ℕ) (ha : a.length ≤ n) : eqZ a (bits n y) = eqBits a y := by
  rw [eqZ, eqBits, length_bits, min_eq_left ha]
  refine prod_congr rfl fun k hk => ?_
  rw [getD_bits, ite_eq_left (lt_of_lt_of_le (mem_range.mp hk) ha)]
  have h11 := one_add_one_eq_zero h2
  cases y.testBit k <;> simp [eq1, h11]

omit h2 in
theorem onePlusProd_eq (a : List E) : onePlusProd a = eqBits a 0 := by
  simp [onePlusProd, eqBits]

namespace Layout

variable {L : Layout}

omit h2 in
theorem getD_laneEqAt (l l' : ℕ) :
    (L.laneEqAt l : List E).getD l' 0 = if l' < L.lanes.length then eqBits (bits 6 l) l' else 0 := by
  unfold laneEqAt
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : l' < L.lanes.length <;> simp [hk]

theorem getD_laneEqAt_eq (h : L.OK) {l l' : ℕ} (hl : l < L.lanes.length) (hl' : l' < L.lanes.length) :
    (L.laneEqAt l : List E).getD l' 0 = if l' = l then 1 else 0 := by
  have h64 := h.lanes_le
  rw [getD_laneEqAt, ite_eq_left hl', eqBits_bits_eq h2 (by norm_num; omega) (by norm_num; omega)]

/-- `on_blocks` at a lane that holds no block is zero. -/
theorem onBlocks_zero (h : L.OK) (part : Part E) {l : ℕ} (hl : l < L.lanes.length)
    (hb : (L.lanes.getD l .random).isBlock = false) :
    L.onBlocks (L.laneEqAt l) part = 0 := by
  refine sum_eq_zero fun l' hl' => ?_
  rw [getD_laneEqAt_eq h2 h hl (mem_range.mp hl')]
  by_cases he : l' = l
  · rw [he, hb]
    simp
  · simp [he]

omit h2 in
theorem part_low_length (lam : E) (point : List E) : (L.part lam point).low.length ≤ L.logLane := by
  simp [part]

/-- On the first piece (`y < 2^8`) a claim's term vanishes: `above = first_above`,
`first_piece = 1` (the cancellation is characteristic 2's), and no held piece is there. -/
theorem claimTerm_first (h : L.OK) (lam : E) (point : List E) (l : ℕ) (y : ℕ)
    (hy : y < 2 ^ logPieceD) :
    L.claimTerm (L.laneEqAt l) (bits L.logLane y) (L.part lam point) = 0 := by
  have hs : L.logPiece = logPieceD := h.piece
  have hy0 : y >>> logPieceD = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hy
  have hA : ((L.part lam point).low.drop logPieceD).length ≤ L.logLane - logPieceD := by
    have := part_low_length (L := L) lam point
    simp only [List.length_drop]
    omega
  have hpl : (L.part lam point).pieces.length = L.pieces.length := by simp [part, pieceScales]
  have hfit : L.pieces.length + 1 ≤ 2 ^ (L.logLane - logPieceD) := by
    have hf := h.fits
    have hl := h.lane
    rw [show L.logLane = (L.logLane - logPieceD) + logPieceD by omega, pow_add] at hf
    exact le_of_mul_le_mul_right hf (by norm_num [logPieceD])
  have hpz : piecesTerm logPieceD (bits L.logLane y) (L.part lam point) = (0 : E) := by
    refine sum_eq_zero fun k hk => ?_
    rw [hpl] at hk
    have hk' := mem_range.mp hk
    rw [drop_bits, hy0, eqBits_bits_eq h2 (Nat.two_pow_pos _) (by omega), ite_eq_right (by omega),
      mul_zero]
  simp only [claimTerm, hs]
  rw [hpz, drop_bits, hy0, eqZ_bits h2 _ _ _ hA, onePlusProd_eq, onePlusProd_eq,
    eqBits_bits_eq h2 (Nat.two_pow_pos _) (Nat.two_pow_pos _), ite_eq_left rfl, mul_one,
    ← two_mul, h2, zero_mul, zero_mul, zero_add, zero_mul, mul_zero]

/-- On a lane holding no block (a random lane, the overflow lane), past the held pieces, a claim's
term vanishes. -/
theorem claimTerm_noBlock (h : L.OK) (lam : E) (point : List E) {l y : ℕ} (hl : l < L.lanes.length)
    (hb : (L.lanes.getD l .random).isBlock = false)
    (hov : l ≠ overflowLane ∨ ¬ (y < (L.pieces.length + 1) * 2 ^ logPieceD)) (hy : y < 2 ^ L.logLane) :
    L.claimTerm (L.laneEqAt l) (bits L.logLane y) (L.part lam point) = 0 := by
  have hs : L.logPiece = logPieceD := h.piece
  simp only [claimTerm]
  rw [onBlocks_zero h2 h _ hl hb, mul_zero, zero_add]
  rcases hov with hov | hov
  · rw [h.overflow, getD_laneEqAt_eq h2 h hl (show overflowLane < L.lanes.length from h.n32),
      ite_eq_right (Ne.symm hov), mul_zero, mul_zero]
  · have hpl : (L.part lam point).pieces.length = L.pieces.length := by simp [part, pieceScales]
    have hfit : L.pieces.length + 1 ≤ 2 ^ (L.logLane - logPieceD) := by
      have hf := h.fits
      have hl := h.lane
      rw [show L.logLane = (L.logLane - logPieceD) + logPieceD by omega, pow_add] at hf
      exact le_of_mul_le_mul_right hf (by norm_num [logPieceD])
    have hyl : y >>> logPieceD < 2 ^ (L.logLane - logPieceD) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      have hl := h.lane
      rw [show L.logLane - logPieceD + logPieceD = L.logLane by omega]
      exact hy
    have hyH : L.pieces.length + 1 ≤ y >>> logPieceD := by
      rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
      omega
    have hpz : piecesTerm L.logPiece (bits L.logLane y) (L.part lam point) = (0 : E) := by
      refine sum_eq_zero fun k hk => ?_
      rw [hpl] at hk
      have hk' := mem_range.mp hk
      rw [hs, drop_bits, eqBits_bits_eq h2 hyl (by omega), ite_eq_right (by omega), mul_zero]
    rw [hpz, zero_mul, mul_zero]

/-! ### `WeightsFit` -/

/-- **The deployed claims fit the gadget layout**: at every supported layout, the closure's claim
terms weigh nothing on the first piece below the gadget, at the gadget's entries, on the random lanes,
nor on the overflow lane off its held pieces. -/
theorem weightsFit (h : L.OK) {m : ℕ} (points : Fin m → List E) :
    (L.toGadget h).WeightsFit (L.claimW points) where
  first c l y hy := by
    have : (y : ℕ) < 247 := by simpa [toGadget, firstFree] using hy
    exact claimTerm_first h2 h 1 (points c) l y (by norm_num [logPieceD]; omega)
  gadget c l y hy := by
    obtain ⟨p, hp⟩ := hy
    have := (atPat_iff h p y).mp hp
    have := p.isLt
    exact claimTerm_first h2 h 1 (points c) l y (by norm_num [logPieceD]; omega)
  rand c l y hr := by
    have hr' : L.lanes[(l : ℕ)]? = some .random := hr
    refine claimTerm_noBlock h2 h 1 (points c) l.isLt ?_ (Or.inl ?_) y.isLt
    · rw [List.getD_eq_getElem?_getD, hr']
      rfl
    · intro he
      have := h.at_ov
      rw [← he, hr'] at this
      simp at this
  off_held c y hy := by
    have hov : ((L.toGadget h).ov : ℕ) = overflowLane := rfl
    have hb : (L.lanes.getD overflowLane .random).isBlock = false := by
      rw [List.getD_eq_getElem?_getD, h.at_ov]
      rfl
    by_cases hy1 : (y : ℕ) < 2 ^ logPieceD
    · exact claimTerm_first h2 h 1 (points c) _ y hy1
    · refine claimTerm_noBlock h2 h 1 (points c) h.n32 hb (Or.inr ?_) y.isLt
      intro hy2
      exact hy (by
        simp only [toGadget, heldSet, mem_filter, mem_univ, true_and]
        exact ⟨by omega, hy2⟩)

/-! ### The closure on the Boolean cube -/

omit h2 in
theorem getD_map_mul (lam : E) (xs : List E) (i : ℕ) :
    (xs.map (lam * ·)).getD i 0 = lam * xs.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> simp

omit h2 in
/-- A claim's term is its power of `λ` times its term at power `1`. -/
theorem claimTerm_part (laneEq low : List E) (lam : E) (point : List E) :
    L.claimTerm laneEq low (L.part lam point) = lam * L.claimTerm laneEq low (L.part 1 point) := by
  have hlow : (L.part lam point).low = (L.part 1 point).low := rfl
  have hon : L.onBlocks laneEq (L.part lam point) = lam * L.onBlocks laneEq (L.part 1 point) := by
    simp only [onBlocks, part, getD_map_mul, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    split_ifs <;> ring
  have hpc : ∀ s, piecesTerm s low (L.part lam point) = lam * piecesTerm s low (L.part 1 point) := by
    intro s
    simp only [piecesTerm, part, getD_map_mul, mul_sum, List.length_map]
    refine sum_congr rfl fun k _ => ?_
    ring
  simp only [claimTerm]
  rw [hlow, hon, hpc]
  ring

omit h2 in
theorem lane_pos_iff (h : L.OK) (l : Fin L.lanes.length) (l' : Fin 64) :
    L.pos l = lane l' ↔ (l : ℕ) = l' := by
  rw [pos_eq_lane h]
  constructor
  · intro he
    have := laneBits_injective he
    simpa using congrArg Fin.val this
  · intro he
    congr 1
    exact Fin.ext he

omit h2 in
theorem patE_pos (h : L.OK) (p : Fin 3) (l : Fin L.lanes.length) :
    patE (E := E) p (L.pos l) = ((gadgetLanes p).map fun l' => if (l : ℕ) = l' then (1 : E) else 0).sum := by
  fin_cases p
  · simp only [patE, pattern0, pairCol, unitCol, flipC_lane0, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, one_mul, gadgetLanes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    simp only [lane_pos_iff h l]
    rfl
  · simp only [patE, pattern1, pairCol, unitCol, flipC_lane1, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, one_mul, gadgetLanes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    simp only [lane_pos_iff h l]
    rfl
  · simp only [patE, pattern2, unitCol, gadgetLanes, overflowLane, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    simp only [lane_pos_iff h l]
    rfl

theorem gadgetTerm_bool (h : L.OK) (beta : Fin 3 → E) (scale : E) (l : Fin L.lanes.length)
    (y : Fin (2 ^ L.logLane)) :
    L.gadgetTerm beta scale (L.laneEqAt l) (bits L.logLane y) =
      scale * (L.toGadget h).gadgetW L.pos beta l y := by
  have hs : L.logPiece = logPieceD := h.piece
  simp only [gadgetTerm, GadgetLayout.gadgetW, mul_sum, hs]
  refine sum_congr rfl fun g _ => ?_
  refine sum_congr rfl fun i _ => ?_
  have hlanes : ((gadgetLanes g).map fun l' => (L.laneEqAt l : List E).getD l' 0).sum =
      patE (E := E) g (L.pos l) := by
    rw [patE_pos h]
    congr 1
    refine List.map_congr_left fun l' hl' => ?_
    have hl'32 : l' < L.lanes.length := by
      have := h.n32
      fin_cases g <;> simp [gadgetLanes, overflowLane] at hl' <;> omega
    rw [getD_laneEqAt_eq h2 h l.isLt hl'32]
    exact if_congr eq_comm rfl rfl
  rw [hlanes, eqBits_bits_eq h2 y.isLt (h.gent_lt g i)]
  have hgent : ((L.toGadget h).gent g i = y) ↔ gadgetEntry logPieceD g i = (y : ℕ) := by
    simp [toGadget, Fin.ext_iff]
  by_cases he : gadgetEntry logPieceD g i = (y : ℕ)
  · rw [ite_eq_left he, ite_eq_left (hgent.mpr he)]
    ring
  · rw [ite_eq_right he, ite_eq_right (fun h' => he (hgent.mp h'))]
    ring

/-- **The closure on the Boolean cube**: at entry `y` of lane `l`, `opening::verify`'s weight is
`Σ_c λ^c W_c(l, y) + λ^m G(l, y)`, `W = claimW`, `G = gadgetW pos β`. -/
theorem weight_bool (h : L.OK) {m : ℕ} (points : Fin m → List E) (lam : E) (beta : Fin 3 → E)
    (l : Fin L.lanes.length) (y : Fin (2 ^ L.logLane)) :
    L.weight points lam beta (boolPt L.logLane y l) =
      (∑ c : Fin m, lam ^ (c : ℕ) * L.claimW points c l y) +
        lam ^ m * (L.toGadget h).gadgetW L.pos beta l y := by
  have hx1 : (boolPt L.logLane y l : List E).take L.logLane = bits L.logLane y :=
    List.take_left' (length_bits _ _)
  have hx2 : (boolPt L.logLane y l : List E).drop L.logLane = bits 6 l :=
    List.drop_left' (length_bits _ _)
  simp only [weight, hx1, hx2]
  rw [← gadgetTerm_bool h2 h beta (lam ^ m) l y]
  congr 1
  refine sum_congr rfl fun c _ => ?_
  rw [claimTerm_part]
  rfl

/-- **The closure is the model's combined weight**: at the index of lane `l`, the combined weight of
the claims `claimW` with the gadget appended, at the powers `λ^c` (`c ≤ m`), is the closure at the
Boolean point of `(y, l)`. -/
theorem weight_combinedW (h : L.OK) {m : ℕ} (points : Fin m → List E) (lam : E) (beta : Fin 3 → E)
    (l : Fin L.lanes.length) (y : Fin (2 ^ L.logLane)) :
    HiddenLayout.combinedW L.pos
        (GadgetLayout.withGadget (L.claimW points) ((L.toGadget h).gadgetW L.pos beta))
        (fun c : Fin (m + 1) => lam ^ (c : ℕ)) (L.pos l) y =
      L.weight points lam beta (boolPt L.logLane y l) := by
  rw [weight_bool h2 h]
  simp only [HiddenLayout.combinedW]
  rw [sum_eq_single l]
  · rw [ite_eq_left rfl, Fin.sum_univ_castSucc]
    simp [GadgetLayout.withGadget, Fin.snoc_castSucc, Fin.snoc_last]
  · intro l' _ hl'
    rw [ite_eq_right (fun he => hl' ((pos_injective h) he))]
  · simp

omit h2 in
/-- The powers `λ^c`, `c ≤ m`, are the claims' powers with the gadget's `λ^m` appended. -/
theorem powers_snoc (lam : E) (m : ℕ) :
    (fun c : Fin (m + 1) => lam ^ (c : ℕ)) = Fin.snoc (fun c : Fin m => lam ^ (c : ℕ)) (lam ^ m) := by
  funext c
  refine Fin.lastCases ?_ (fun c => ?_) c
  · simp
  · simp

end Layout

end Deployed

end QuotientSecurity.Hiding
