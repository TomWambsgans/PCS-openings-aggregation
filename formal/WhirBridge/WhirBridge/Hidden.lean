/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

What a claim of `crates/quotient/src/opening.rs` says of a **hidden** layout's stack: its
multilinear claim on the table `Table::read` reads back from the stack; and what the gadget the
opening adds says of it. Uses lemmas of leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM,
commit 6175f1a0, MIT OR Apache-2.0) on cube points (`boolPoint_add`, `eqEval_append`,
`eqEval_comm`, `eqEval_boolPoint_boolPoint`, `selectorPoint_eq_boolPoint`).
-/
import WhirBridge.Table

/-!
# The claims on a hidden layout are claims on the table

A hidden layout (`Layout::hidden_with`, `opening.rs:153-203`) stacks a table in lanes of `2^ℓ`
entries, `ℓ = log_n − 6`, cut in pieces of `2^s`: block lane `l` holds its block but its first
piece at its pieces `k ≥ 1` (its piece `0` is random), the overflow lane holds, at its piece
`k + 1`, the table's piece `pieces[k]` (the blocks' first pieces, then the chunks' tails).
`Layout.readHidden` is `Table::read` (`opening.rs:525-545`), entry by entry: the table a stack
stands for.

`holds_iff_hidden`: **for every stack `q`, `q` satisfies the stack claim of a claim `c` (with the
weight `opening::verify` evaluates, `Layout.claimWeight`) exactly when the table read back from `q`
has `c.value` as its multilinear extension at `c.point`**, for a layout of the shape
`Layout::hidden` gives (`Layout.HiddenOK`: the pieces distinct and fewer than a lane's, each block
on one lane, every block lane's first piece among the pieces and no other piece of its block, the
overflow lane where `Layout::overflow` says, the gadget's entries in the first piece and its lanes
among the layout's).

The proof reads each stack entry's weight on the cube (`claimWeight_cube`): the `eq` of the table
entry it holds (`Layout.role`), or zero; and each table entry as the sum of the stack entries
holding it (`readHidden_eq_fiber`): one (the overflow lane's) for a piece of `pieces`, one for any
other piece of a block on a lane, none otherwise.

**The gadget** (`gadget_holds_iff`): the stack claim the opening adds, the gadget of value zero
(`Layout.extra`), holds of `q` exactly when `Σ_{g,i} β_i · Σ_{l ∈ pattern g} q[l][2^s − 9 + 3g + i]
= 0` (`Layout.gadgetValue`): at the gadget's entries the pattern lanes' `β`-combination is zero, a
condition on the random first pieces, not on the table. So the opening's doom in table terms
(`Layout.openingDoom_iff`) is: every candidate's table violates one of the claims, or the candidate
violates the gadget; and an opening that is not doomed has one candidate whose table satisfies every
claim and which satisfies the gadget (`Layout.joint_of_not_doom`).
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd Finset

/-! ## Cube points -/

theorem boolPoint_length' (n y : ℕ) : (boolPoint n y).length = n := by simp [boolPoint]

theorem boolPoint_take' {n m : ℕ} (y : ℕ) (h : m ≤ n) : (boolPoint n y).take m = boolPoint m y := by
  apply List.ext_getElem
  · simp [boolPoint, h]
  · intro i h1 h2
    simp [boolPoint]

theorem boolPoint_drop' (n m y : ℕ) : (boolPoint n y).drop m = boolPoint (n - m) (y / 2 ^ m) := by
  apply List.ext_getElem
  · simp [boolPoint]
  · intro i h1 h2
    simp [boolPoint, Nat.testBit_div_two_pow, add_comm]

theorem boolPoint_mod' (m y : ℕ) : boolPoint m (y % 2 ^ m) = boolPoint m y := by
  apply List.ext_getElem
  · simp [boolPoint]
  · intro i h1 h2
    have : i < m := by simpa [boolPoint] using h1
    simp [boolPoint, Nat.testBit_mod_two_pow, this]

theorem boolPoint_zero' (m : ℕ) : boolPoint m 0 = List.replicate m 0 := by
  apply List.ext_getElem
  · simp [boolPoint]
  · intro i h1 h2
    simp [boolPoint]

/-- `eq_index` at a cube point is a Kronecker delta. -/
theorem eqBits_cube {m i j : ℕ} (hi : i < 2 ^ m) (hj : j < 2 ^ m) :
    eqBits (boolPoint m j) i = if i = j then 1 else 0 := by
  rw [eqBits_eq_eqEval, LeanVM.Protocol.EndToEnd.Front.selectorPoint_eq_boolPoint, boolPoint_length',
    LeanVM.Protocol.EndToEnd.Complete.eqEval_boolPoint_boolPoint m i j hi hj]

/-- `eq_bits(p, b)` is `eq` of `b`'s cube point and `p`. -/
theorem eqBits_eq_boolPoint (p : List E) (b : ℕ) :
    eqBits p b = eqEval (boolPoint p.length b) p := by
  rw [eqBits_eq_eqEval, LeanVM.Protocol.EndToEnd.Front.selectorPoint_eq_boolPoint]

/-- **The block term on the cube**: `eq` of the claim's coordinates and the lane's piece, but zero
on the first piece. -/
theorem blockTerm_cube (a : List E) {m k : ℕ} (ham : a.length = m) (hk : k < 2 ^ m) :
    blockTerm a (onePlusProd a) (boolPoint m k) =
      if k = 0 then 0 else eqEval a (boolPoint m k) := by
  subst ham
  have hfa : onePlusProd a = eqEval a (boolPoint a.length 0) := by
    rw [LeanVM.Protocol.Whir.Complete.eqEval_comm, boolPoint_zero', onePlusProd_eq]
  have hfp : onePlusProd (boolPoint a.length k) = if k = 0 then 1 else 0 := by
    rw [onePlusProd_eq, boolPoint_length', ← boolPoint_zero',
      LeanVM.Protocol.EndToEnd.Complete.eqEval_boolPoint_boolPoint _ 0 k (by positivity) hk]
    simp only [eq_comm]
  rw [blockTerm, eqZ_eq_eqEval, hfp]
  split_ifs with h0
  · subst h0
    rw [mul_one, ← hfa]
    exact CharTwo.add_self_eq_zero _
  · rw [mul_zero, add_zero]

/-! ## The lanes on the cube -/

/-- `on_blocks` at a lane's cube point: the lane's scale if it is a block lane. -/
theorem onBlocks_cube (lanes : List Lane) (ps : List E) {l : ℕ}
    (hN : lanes.length ≤ 2 ^ laneFold) (hl : l < 2 ^ laneFold) :
    onBlocks lanes ps (laneEqs lanes.length (boolPoint laneFold l)) =
      match lanes[l]? with
      | some (.block _) => ps.getD l 0
      | _ => 0 := by
  rw [onBlocks_eq_sum, sum_zipIdx .random _ _ 0]
  have hterm : ∀ i ∈ range lanes.length,
      onTerm ps (laneEqs lanes.length (boolPoint laneFold l)) (lanes.getD i .random, 0 + i) =
        if i = l then
          (match lanes[l]? with
            | some (.block _) => ps.getD l 0
            | _ => 0)
        else 0 := by
    intro i hi
    have hi' := mem_range.1 hi
    have hget : lanes.getD i .random = lanes[i] := List.getD_eq_getElem _ _ hi'
    have hle : (laneEqs lanes.length (boolPoint laneFold l)).getD i 0 = if i = l then 1 else 0 := by
      rw [laneEqs_getD, if_pos hi', eqBits_cube (lt_of_lt_of_le hi' hN) hl]
    rw [zero_add, onTerm]
    simp only [hget, hle]
    have hsome : lanes[i]? = some lanes[i] := List.getElem?_eq_getElem hi'
    by_cases hil : i = l
    · subst hil
      rw [hsome]
      rcases lanes[i] with b | _ | _
      · simp
      · simp
      · simp
    · rcases lanes[i] with b | _ | _
      · simp [hil]
      · simp [hil]
      · simp [hil]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  by_cases hlN : l ∈ range lanes.length
  · rw [if_pos hlN]
  · rw [if_neg hlN, List.getElem?_eq_none (by simpa using hlN)]

/-- A lane's `eq` at a lane's cube point. -/
theorem laneEq_cube {N i l : ℕ} (hN : N ≤ 2 ^ laneFold) (hi : i < N) (hl : l < 2 ^ laneFold) :
    (laneEqs N (boolPoint laneFold l)).getD i 0 = if i = l then 1 else 0 := by
  rw [laneEqs_getD, if_pos hi, eqBits_cube (lt_of_lt_of_le hi hN) hl]

/-- The pieces' term at a cube point of the window: the piece's scale on the overflow piece `k`. -/
theorem pieces_cube (ps : List E) {m k : ℕ} (hps : ps.length < 2 ^ m) (hk : k < 2 ^ m) :
    (ps.zipIdx.map fun wk ↦ wk.1 * eqBits (boolPoint m k) (wk.2 + 1)).sum =
      if 1 ≤ k ∧ k ≤ ps.length then ps.getD (k - 1) 0 else 0 := by
  rw [sum_zipIdx 0 (fun wk ↦ wk.1 * eqBits (boolPoint m k) (wk.2 + 1)) ps 0]
  have hterm : ∀ i ∈ range ps.length, ps.getD i 0 * eqBits (boolPoint m k) (0 + i + 1) =
      if i = k - 1 ∧ 1 ≤ k then ps.getD i 0 else 0 := by
    intro i hi
    have hi' := mem_range.1 hi
    rw [zero_add, eqBits_cube (by omega) hk]
    by_cases h : i + 1 = k
    · rw [if_pos h, if_pos ⟨by omega, by omega⟩, mul_one]
    · rw [if_neg h, if_neg (by omega), mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hk1 : 1 ≤ k
  · simp only [hk1, and_true, true_and]
    rw [Finset.sum_ite_eq']
    by_cases hkl : k ≤ ps.length
    · rw [if_pos (mem_range.2 (by omega)), if_pos hkl]
    · rw [if_neg (by simp; omega), if_neg hkl]
  · simp only [hk1, and_false, false_and, ↓reduceIte, Finset.sum_const_zero]

/-! ## The shape of a hidden layout -/

/-- The block lanes: `(block, lane)`. -/
def Layout.blockLanes (L : Layout) : List (ℕ × ℕ) :=
  L.lanes.zipIdx.filterMap fun ll ↦ match ll.1 with
    | .block b => some (b, ll.2)
    | _ => none

theorem mem_blockLanes {L : Layout} {b i : ℕ} :
    (b, i) ∈ L.blockLanes ↔ L.lanes[i]? = some (.block b) := by
  simp only [Layout.blockLanes, List.mem_filterMap]
  constructor
  · rintro ⟨⟨lane, j⟩, hmem, hf⟩
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    rcases lane with b' | _ | _ <;> simp at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact hmem
  · intro h
    exact ⟨(.block b, i), List.mem_zipIdx_iff_getElem?.2 h, rfl⟩

/-- **What the meaning of the claims and of the gadget needs of a hidden layout**, all of which
`Layout::hidden` gives (decided for ours, `Layouts.lean`): pieces of `2^s` inside lanes of `2^ℓ`
inside the table, at most `64` lanes, fewer pieces than a lane's (the overflow lane's piece `0` is
random), the overflow lane where `Layout::overflow` says, the pieces distinct and in the table,
each block on one lane and in the table, a block lane's first piece among the pieces and no other
piece of its block; the gadget's entries inside the first piece (`GADGET < 2^s`, the Rust's
assertion) and its patterns' lanes among the layout's. -/
structure Layout.HiddenOK (L : Layout) (s : ℕ) : Prop where
  piece : L.logPiece = some s
  six_le : laneFold ≤ L.logN
  s_lt : s < L.logLane
  lane_le : L.logLane ≤ L.vars
  lanes_le : L.lanes.length ≤ 2 ^ laneFold
  held_lt : L.pieces.length < 2 ^ (L.logLane - s)
  overflow : L.lanes[L.overflow]? = some .overflow
  nodup : L.pieces.Nodup
  piece_lt : ∀ p ∈ L.pieces, p < 2 ^ (L.vars - s)
  blocks_nodup : (L.blockLanes.map Prod.fst).Nodup
  block_ok : ∀ bi ∈ L.blockLanes, bi.1 < 2 ^ (L.vars - L.logLane) ∧
    2 ^ (L.logLane - s) * bi.1 ∈ L.pieces ∧
    ∀ p ∈ L.pieces, p / 2 ^ (L.logLane - s) = bi.1 → p % 2 ^ (L.logLane - s) = 0
  gadget_lt : gadget < 2 ^ s
  gadget_lanes : ∀ g < 3, ∀ l ∈ gadgetLanes g, l < L.lanes.length

theorem Layout.HiddenOK.block_inj {L : Layout} {s : ℕ} (hL : L.HiddenOK s) {i j b : ℕ}
    (hi : L.lanes[i]? = some (.block b)) (hj : L.lanes[j]? = some (.block b)) : i = j := by
  have hmi := mem_blockLanes.2 hi
  have hmj := mem_blockLanes.2 hj
  obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hmi
  obtain ⟨k', hk', hkj⟩ := List.getElem_of_mem hmj
  have hkk : k = k' := by
    have := (List.Nodup.getElem_inj_iff hL.blocks_nodup (hi := by simpa using hk)
      (hj := by simpa using hk')).1 (by simp [hki, hkj])
    exact this
  subst hkk
  rw [hki] at hkj
  exact (Prod.mk.inj hkj).2

/-! ## `Table::read` -/

/-- The stack's entry `y` of lane `l` (`lane(l)[y]`, `opening.rs:530`). -/
def stackAt {n : ℕ} (q : Column n) (logLane l y : ℕ) : K := q.values.getD (y + 2 ^ logLane * l) 0

/-- **`Table::read`** (`opening.rs:525-545`), entry by entry, for a hidden layout with pieces of
`2^s` entries: the table's entry `t`, in piece `p = t >> s` at `o = t mod 2^s`, is the overflow
lane's at its piece `k + 1` if `p` is the overflow lane's `k`-th piece; else the entry of the block
lane holding `p`'s block at its piece `p mod 2^(ℓ−s)`; else zero. -/
def Layout.readHidden (L : Layout) (s : ℕ) (q : Column L.logN) (t : ℕ) : K :=
  let ℓ := L.logLane
  let p := t >>> s
  let o := t % 2 ^ s
  match L.pieces.findIdx? (· == p) with
  | some k => stackAt q ℓ L.overflow ((k + 1) * 2 ^ s + o)
  | none => match L.lanes.findIdx? (· == .block (p >>> (ℓ - s))) with
    | some l => stackAt q ℓ l ((p &&& (2 ^ (ℓ - s) - 1)) * 2 ^ s + o)
    | none => 0

/-- **The table a stack stands for**: `Table::read` for a hidden layout; for a public one, its
blocks (`Blocks.table`). -/
def Layout.table (L : Layout) (q : Column L.logN) (t : ℕ) : K :=
  match L.logPiece with
  | some s => L.readHidden s q t
  | none => L.toBlocks.table q t

/-- The table's multilinear extension at `p` (`Table::eval`, `opening.rs:547-582`). -/
def Layout.tableEval (L : Layout) (q : Column L.logN) (p : List E) : E :=
  ∑ t ∈ range (2 ^ L.vars), ofK (L.table q t) * eqEval (boolPoint L.vars t) p

/-! ## The table entry each stack entry holds -/

/-- **The table entry stack entry `y` of lane `l` holds** with a weight: a block lane's past its
first piece, the overflow lane's at its pieces `1 ..= |pieces|`. -/
def Layout.role (L : Layout) (s l y : ℕ) : Option ℕ :=
  match L.lanes[l]? with
  | some (.block b) =>
    if y / 2 ^ s = 0 then none
    else some (y % 2 ^ s + 2 ^ s * (y / 2 ^ s + 2 ^ (L.logLane - s) * b))
  | some _ =>
    if l = L.overflow ∧ 1 ≤ y / 2 ^ s ∧ y / 2 ^ s ≤ L.pieces.length then
      some (y % 2 ^ s + 2 ^ s * L.pieces.getD (y / 2 ^ s - 1) 0)
    else none
  | none => none

theorem lt_two_pow_add {a b o z : ℕ} (ho : o < 2 ^ a) (hz : z < 2 ^ b) :
    o + 2 ^ a * z < 2 ^ (a + b) := by
  rw [pow_add]
  calc o + 2 ^ a * z < 2 ^ a + 2 ^ a * z := by omega
    _ = 2 ^ a * (z + 1) := by ring
    _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_left _ hz

theorem split_point {s m : ℕ} (p : List E) :
    p = p.take s ++ ((p.drop s).take m ++ p.drop (s + m)) := by
  rw [show p.drop (s + m) = (p.drop s).drop m from List.drop_drop.symm, List.take_append_drop,
    List.take_append_drop]

/-- `eq` of a table entry `o + 2^s (j + 2^m b)` and a point, factor by factor. -/
theorem eqEval_entry {s m V o j b : ℕ} (p : List E) (hp : p.length = V) (hsm : s + m ≤ V)
    (ho : o < 2 ^ s) (hj : j < 2 ^ m) :
    eqEval (boolPoint V (o + 2 ^ s * (j + 2 ^ m * b))) p =
      eqEval (boolPoint s o) (p.take s) * (eqEval (boolPoint m j) ((p.drop s).take m) *
        eqEval (boolPoint (V - (s + m)) b) (p.drop (s + m))) := by
  have hV : V = s + (m + (V - (s + m))) := by omega
  conv_lhs => rw [split_point (s := s) (m := m) p, hV]
  rw [LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ ho,
    LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ hj,
    LeanVM.Protocol.Whir.Complete.eqEval_append _ _ _ _ (by simp [hp]; omega),
    LeanVM.Protocol.Whir.Complete.eqEval_append _ _ _ _ (by simp [hp]; omega)]

/-- `eq` of a table entry `o + 2^s p` and a point. -/
theorem eqEval_entry' {s V o p : ℕ} (x : List E) (hx : x.length = V) (hs : s ≤ V)
    (ho : o < 2 ^ s) :
    eqEval (boolPoint V (o + 2 ^ s * p)) x =
      eqEval (boolPoint s o) (x.take s) * eqEval (boolPoint (V - s) p) (x.drop s) := by
  have hV : V = s + (V - s) := by omega
  conv_lhs => rw [← List.take_append_drop s x, hV]
  rw [LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ ho,
    LeanVM.Protocol.Whir.Complete.eqEval_append _ _ _ _ (by simp [hx]; omega)]

section Cube

variable {L : Layout} {s : ℕ} (hL : L.HiddenOK s)

include hL in
theorem Layout.HiddenOK.logN_eq : L.logN = L.logLane + laneFold := by
  have := hL.six_le
  simp only [Layout.logLane]
  omega

include hL in
theorem Layout.HiddenOK.ov_lt : L.overflow < L.lanes.length :=
  (List.getElem?_eq_some_iff.1 hL.overflow).1

include hL in
/-- **A stack entry's weight on the cube** is the `eq` of the table entry it holds, or zero. -/
theorem claimWeight_cube (c : Claim) (hc : c.point.length = L.vars) {l y : ℕ}
    (hl : l < 2 ^ laneFold) (hy : y < 2 ^ L.logLane) :
    L.claimWeight c (boolPoint L.logN (y + 2 ^ L.logLane * l)) =
      match L.role s l y with
      | some t => eqEval (boolPoint L.vars t) c.point
      | none => 0 := by
  have hsℓ := hL.s_lt
  have hℓV := hL.lane_le
  have hN := hL.lanes_le
  have hx : boolPoint L.logN (y + 2 ^ L.logLane * l) =
      boolPoint L.logLane y ++ boolPoint laneFold l := by
    rw [hL.logN_eq]
    exact LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ hy
  rw [claimWeight_hidden L c hL.piece, hx]
  have hlen : (boolPoint L.logLane y).length = L.logLane := boolPoint_length' _ _
  rw [min_eq_left hsℓ.le, List.take_append_of_le_length (by omega), boolPoint_take' _ hsℓ.le,
    ← boolPoint_mod', List.take_left' hlen, List.drop_left' hlen, boolPoint_drop']
  unfold Layout.role
  -- the claim's coordinates
  have hpll : (c.point.take L.logLane).length = L.logLane := by
    rw [List.length_take, hc]; omega
  have hal : ((c.point.take L.logLane).drop s).length = L.logLane - s := by
    rw [List.length_drop, hpll]
  have hca : (c.point.take L.logLane).drop s = (c.point.drop s).take (L.logLane - s) := by
    rw [List.drop_take]
  have hbelow : eqZ ((c.point.take L.logLane).take s) (boolPoint s (y % 2 ^ s)) =
      eqEval (boolPoint s (y % 2 ^ s)) (c.point.take s) := by
    rw [eqZ_eq_eqEval, LeanVM.Protocol.Whir.Complete.eqEval_comm, List.take_take,
      min_eq_left hsℓ.le]
  rw [hbelow]
  generalize hpl : c.point.take L.logLane = pl at hpll hal hca
  generalize ha : pl.drop s = a at hal hca
  generalize hm : L.logLane - s = m at hal hca
  have hkm : y / 2 ^ s < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← hm]
    convert hy using 2
    omega
  have hom : y % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
  generalize hk : y / 2 ^ s = k at hkm ⊢
  generalize ho : y % 2 ^ s = o at hom ⊢
  rw [blockTerm_cube a hal hkm, onBlocks_cube _ _ hN hl, laneEq_cube hN hL.ov_lt hl]
  have hps : (L.pieceScales c.point).length = L.pieces.length := by
    simp [Layout.pieceScales, hL.piece]
  rw [pieces_cube _ (by rw [hps, ← hm]; exact hL.held_lt) hkm, hps]
  rcases hlane : L.lanes[l]? with _ | lane
  · -- no lane
    have hov : L.overflow ≠ l := fun h ↦ by
      have := hL.overflow; rw [h, hlane] at this; cases this
    simp [hov]
  · rcases lane with b | _ | _
    · -- a block lane
      have hov : L.overflow ≠ l := fun h ↦ by
        have := hL.overflow; rw [h, hlane] at this; cases this
      simp only [hov, ↓reduceIte, add_zero, mul_zero]
      have hscale : (L.laneScales c.point).getD l 0 =
          eqEval (boolPoint (L.vars - L.logLane) b) (c.point.drop L.logLane) := by
        have hl' : l < L.lanes.length := (List.getElem?_eq_some_iff.1 hlane).1
        rw [List.getD_eq_getElem _ _ (by simpa [Layout.laneScales] using hl')]
        simp only [Layout.laneScales, List.getElem_map]
        rw [(List.getElem?_eq_some_iff.1 hlane).2]
        simp only
        rw [eqBits_eq_boolPoint, List.length_drop, hc]
      rw [hscale]
      by_cases hk0 : k = 0
      · simp [hk0]
      · simp only [hk0, ↓reduceIte]
        rw [eqEval_entry c.point hc (by omega) hom hkm, show s + m = L.logLane by omega, ← hca,
          LeanVM.Protocol.Whir.Complete.eqEval_comm a]
    all_goals
      -- the overflow lane or a random lane
      simp only [mul_zero, zero_add]
      by_cases hos : l = L.overflow
      · rw [if_pos hos.symm, mul_one]
        simp only [hos, true_and]
        by_cases hkp : 1 ≤ k ∧ k ≤ L.pieces.length
        · rw [if_pos hkp, if_pos hkp]
          have hpk : (L.pieceScales c.point).getD (k - 1) 0 =
              eqEval (boolPoint (L.vars - s) (L.pieces.getD (k - 1) 0)) (c.point.drop s) := by
            rw [List.getD_eq_getElem _ _ (by rw [hps]; omega),
              List.getD_eq_getElem _ _ (by omega)]
            simp only [Layout.pieceScales, hL.piece, List.getElem_map]
            rw [eqBits_eq_boolPoint, List.length_drop, hc]
          show _ = eqEval (boolPoint L.vars (o + 2 ^ s * L.pieces.getD (k - 1) 0)) c.point
          rw [hpk, eqEval_entry' c.point hc (by omega) hom]
        · rw [if_neg hkp, if_neg hkp, mul_zero]
      · have h1 : L.overflow ≠ l := fun h ↦ hos h.symm
        simp [h1, hos]

/-! ## Each table entry is the stack entry holding it -/

include hL in
theorem div_lt_window {y : ℕ} (hy : y < 2 ^ L.logLane) : y / 2 ^ s < 2 ^ (L.logLane - s) := by
  have := hL.s_lt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  convert hy using 2
  omega

theorem decomp_mod {a o z : ℕ} (ho : o < 2 ^ a) : (o + 2 ^ a * z) % 2 ^ a = o := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho]

theorem decomp_div {a o z : ℕ} (ho : o < 2 ^ a) : (o + 2 ^ a * z) / 2 ^ a = z := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ho, zero_add]

include hL in
/-- A block lane's stack entry holds `t` exactly when it is past the first piece and lands on `t`'s
piece and offset. -/
theorem role_block {l y b t : ℕ} (hy : y < 2 ^ L.logLane) (hlane : L.lanes[l]? = some (.block b)) :
    L.role s l y = some t ↔ y / 2 ^ s ≠ 0 ∧ y % 2 ^ s = t % 2 ^ s ∧
      y / 2 ^ s = t / 2 ^ s % 2 ^ (L.logLane - s) ∧
        b = t / 2 ^ s / 2 ^ (L.logLane - s) := by
  unfold Layout.role
  rw [hlane]
  simp only
  constructor
  · intro h
    split_ifs at h with hk0
    obtain rfl := (Option.some.inj h).symm
    have hom : y % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
    have hj : y / 2 ^ s < 2 ^ (L.logLane - s) := div_lt_window hL hy
    refine ⟨hk0, (decomp_mod hom).symm, ?_, ?_⟩
    · rw [decomp_div hom, decomp_mod hj]
    · rw [decomp_div hom, decomp_div hj]
  · rintro ⟨hk0, ho, hj, hb⟩
    rw [if_neg hk0, hb, hj, ho, Nat.mod_add_div, Nat.mod_add_div]

include hL in
/-- The overflow and random lanes' stack entry holds `t` exactly when it is the overflow lane's
piece `k + 1` holding `t`'s piece, at `t`'s offset. -/
theorem role_other {l y t : ℕ} {lane : Lane} (hlane : L.lanes[l]? = some lane)
    (hnb : ∀ b, lane ≠ .block b) :
    L.role s l y = some t ↔ l = L.overflow ∧ 1 ≤ y / 2 ^ s ∧
      y / 2 ^ s ≤ L.pieces.length ∧ y % 2 ^ s = t % 2 ^ s ∧
        L.pieces.getD (y / 2 ^ s - 1) 0 = t / 2 ^ s := by
  have hom : y % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
  unfold Layout.role
  rw [hlane]
  rcases lane with b | _ | _
  · exact absurd rfl (hnb b)
  all_goals
    simp only
    constructor
    · intro h
      split_ifs at h with hc
      obtain rfl := (Option.some.inj h).symm
      exact ⟨hc.1, hc.2.1, hc.2.2, (decomp_mod hom).symm, (decomp_div hom).symm⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      rw [if_pos ⟨h1, h2, h3⟩, h4, h5, Nat.mod_add_div]

theorem getD_mem' {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem _

theorem sum_sum_single {A B l0 y0 : ℕ} (hl0 : l0 < A) (hy0 : y0 < B) (P : ℕ → ℕ → Prop)
    [∀ l y, Decidable (P l y)] (f : ℕ → ℕ → E)
    (hP : ∀ l < A, ∀ y < B, P l y ↔ l = l0 ∧ y = y0) :
    ∑ l ∈ range A, ∑ y ∈ range B, (if P l y then f l y else 0) = f l0 y0 := by
  have h : ∀ l ∈ range A, ∑ y ∈ range B, (if P l y then f l y else 0) =
      if l = l0 then f l0 y0 else 0 := by
    intro l hl
    have h' : ∀ y ∈ range B, (if P l y then f l y else 0) =
        if y = y0 then (if l = l0 then f l0 y0 else 0) else 0 := by
      intro y hy
      by_cases hly : l = l0 ∧ y = y0
      · obtain ⟨rfl, rfl⟩ := hly
        rw [if_pos ((hP _ (mem_range.1 hl) _ (mem_range.1 hy)).2 ⟨rfl, rfl⟩), if_pos rfl, if_pos rfl]
      · rw [if_neg (fun h ↦ hly ((hP _ (mem_range.1 hl) _ (mem_range.1 hy)).1 h))]
        by_cases hy' : y = y0
        · rw [if_pos hy', if_neg (fun h ↦ hly ⟨h, hy'⟩)]
        · rw [if_neg hy']
    rw [Finset.sum_congr rfl h', Finset.sum_ite_eq', if_pos (mem_range.2 hy0)]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq', if_pos (mem_range.2 hl0)]

include hL in
/-- **Each table entry is the sum of the stack entries holding it** (`Table::read`): the one
holding it, or none. -/
theorem readHidden_eq_fiber (q : Column L.logN) (t : ℕ) :
    ofK (L.readHidden s q t) = ∑ l ∈ range (2 ^ laneFold), ∑ y ∈ range (2 ^ L.logLane),
      if L.role s l y = some t then ofK (stackAt q L.logLane l y) else 0 := by
  have hsℓ := hL.s_lt
  have hm1 : 1 ≤ L.logLane - s := by omega
  unfold Layout.readHidden
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  generalize hm : L.logLane - s = m at hm1
  have hℓ : L.logLane = s + m := by omega
  have hom : t % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
  have hyl : ∀ {k : ℕ}, k < 2 ^ m → t % 2 ^ s + 2 ^ s * k < 2 ^ L.logLane := fun hk ↦ by
    rw [hℓ]; exact lt_two_pow_add hom hk
  rcases hk : L.pieces.findIdx? (· == t / 2 ^ s) with _ | k
  · have hnp : t / 2 ^ s ∉ L.pieces := by
      intro hmem
      have := (List.findIdx?_eq_none_iff.1 hk) _ hmem
      simp at this
    rcases hl0 : L.lanes.findIdx? (· == Lane.block (t / 2 ^ s / 2 ^ m)) with _ | l0
    · -- no piece, no lane: nothing holds `t`
      simp only
      symm
      refine Finset.sum_eq_zero fun l hl ↦ Finset.sum_eq_zero fun y hy ↦ if_neg fun hr ↦ ?_
      rcases hlane : L.lanes[l]? with _ | lane
      · unfold Layout.role at hr; rw [hlane] at hr; cases hr
      · by_cases hb : ∃ b, lane = .block b
        · obtain ⟨b, rfl⟩ := hb
          obtain ⟨-, -, -, hb⟩ := (role_block hL (mem_range.1 hy) hlane).1 hr
          rw [hm] at hb
          have := (List.findIdx?_eq_none_iff.1 hl0) _ (List.mem_of_getElem? hlane)
          simp [hb] at this
        · push_neg at hb
          obtain ⟨-, h1, h2, -, h5⟩ := (role_other hL hlane hb).1 hr
          exact hnp (h5 ▸ getD_mem' (by omega))
    · -- a block on a lane: the lane holds `t`
      obtain ⟨hl0lt, hl0eq, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hl0
      have hlane0 : L.lanes[l0]? = some (.block (t / 2 ^ s / 2 ^ m)) := by
        rw [List.getElem?_eq_getElem hl0lt]
        simpa using hl0eq
      have hj : t / 2 ^ s % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
      have hk0 : t / 2 ^ s % 2 ^ m ≠ 0 := by
        intro h0
        apply hnp
        have := (hL.block_ok _ (mem_blockLanes.2 hlane0)).2.1
        simp only at this
        rw [hm] at this
        rw [← Nat.mod_add_div (t / 2 ^ s) (2 ^ m), h0, zero_add]
        exact this
      have hl0' : l0 < 2 ^ laneFold := lt_of_lt_of_le hl0lt hL.lanes_le
      simp only
      rw [sum_sum_single hl0' (hyl hj) _ (fun l y ↦ ofK (stackAt q L.logLane l y)) ?_]
      · congr 2
        ring
      · intro l hl y hy
        constructor
        · intro hr
          rcases hlane : L.lanes[l]? with _ | lane
          · unfold Layout.role at hr; rw [hlane] at hr; cases hr
          · by_cases hb : ∃ b', lane = .block b'
            · obtain ⟨b', rfl⟩ := hb
              obtain ⟨-, ho, hjx, hb'⟩ := (role_block hL hy hlane).1 hr
              rw [hm] at hjx hb'
              rw [hb'] at hlane
              have hll : l = l0 := hL.block_inj hlane hlane0
              subst hll
              refine ⟨rfl, ?_⟩
              rw [← Nat.mod_add_div y (2 ^ s), ho, hjx]
            · push_neg at hb
              obtain ⟨-, h1, h2, -, h5⟩ := (role_other hL hlane hb).1 hr
              exact absurd (h5 ▸ getD_mem' (by omega)) hnp
        · rintro ⟨rfl, rfl⟩
          refine (role_block hL (hyl hj) hlane0).2 ⟨?_, ?_, ?_, ?_⟩
          · rw [decomp_div hom]; exact hk0
          · rw [decomp_mod hom]
          · rw [decomp_div hom, hm]
          · rw [hm]
  · -- a piece of the overflow lane: the overflow lane holds `t`
    obtain ⟨hklt, hkeq, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hk
    have hPk : L.pieces[k] = t / 2 ^ s := by simpa using hkeq
    have hheld := hL.held_lt
    rw [hm] at hheld
    have hy0 : t % 2 ^ s + 2 ^ s * (k + 1) < 2 ^ L.logLane := hyl (by omega)
    have hpmem : t / 2 ^ s ∈ L.pieces := hPk ▸ List.getElem_mem _
    have hiff : ∀ l < 2 ^ laneFold, ∀ y < 2 ^ L.logLane, L.role s l y = some t ↔
        l = L.overflow ∧ y = t % 2 ^ s + 2 ^ s * (k + 1) := by
      intro l hl y hy
      constructor
      · intro hr
        rcases hlane : L.lanes[l]? with _ | lane
        · unfold Layout.role at hr; rw [hlane] at hr; cases hr
        · by_cases hb : ∃ b', lane = .block b'
          · obtain ⟨b', rfl⟩ := hb
            obtain ⟨hy0', -, hjx, hb'⟩ := (role_block hL hy hlane).1 hr
            have hpar := (hL.block_ok _ (mem_blockLanes.2 hlane)).2.2 _ hpmem hb'.symm
            exact absurd (hjx.trans hpar) hy0'
          · push_neg at hb
            obtain ⟨hos, h1, h2, ho, h5⟩ := (role_other hL hlane hb).1 hr
            refine ⟨hos, ?_⟩
            have hidx : y / 2 ^ s - 1 = k := by
              rw [List.getD_eq_getElem _ _ (by omega), ← hPk] at h5
              exact (List.Nodup.getElem_inj_iff hL.nodup).1 h5
            rw [← Nat.mod_add_div y (2 ^ s), ho]
            congr 2
            omega
      · rintro ⟨hos, rfl⟩
        have hlane : L.lanes[l]? = some .overflow := by rw [hos]; exact hL.overflow
        refine (role_other hL hlane fun b h ↦ by cases h).2 ⟨hos, ?_, ?_, ?_, ?_⟩
        · rw [decomp_div hom]; omega
        · rw [decomp_div hom]; omega
        · rw [decomp_mod hom]
        · rw [decomp_div hom, Nat.add_sub_cancel, List.getD_eq_getElem _ _ hklt, hPk]
    have hov : L.overflow < 2 ^ laneFold := lt_of_lt_of_le hL.ov_lt hL.lanes_le
    simp only
    rw [sum_sum_single hov hy0 _ (fun l y ↦ ofK (stackAt q L.logLane l y)) hiff]
    congr 2
    ring

include hL in
/-- The table entries the stack holds are in the table. -/
theorem role_lt {l y t : ℕ} (hy : y < 2 ^ L.logLane) (hr : L.role s l y = some t) :
    t < 2 ^ L.vars := by
  have hsℓ := hL.s_lt
  have hℓV := hL.lane_le
  have hom : y % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
  have hkm := div_lt_window hL hy
  unfold Layout.role at hr
  rcases hlane : L.lanes[l]? with _ | lane
  · rw [hlane] at hr; cases hr
  · rw [hlane] at hr
    rcases lane with b | _ | _
    · simp only at hr
      split_ifs at hr
      obtain rfl := (Option.some.inj hr).symm
      have hb := (hL.block_ok _ (mem_blockLanes.2 hlane)).1
      have hV : L.vars = s + ((L.logLane - s) + (L.vars - L.logLane)) := by omega
      rw [hV]
      exact lt_two_pow_add hom (lt_two_pow_add hkm hb)
    all_goals
      simp only at hr
      split_ifs at hr with hc
      obtain rfl := (Option.some.inj hr).symm
      have hp := hL.piece_lt _ (getD_mem' (l := L.pieces) (i := y / 2 ^ s - 1) (by omega))
      have hV : L.vars = s + (L.vars - s) := by omega
      rw [hV]
      exact lt_two_pow_add hom hp

include hL in
/-- **A claim holds of a hidden layout's stack exactly when its table claim holds of the table
read back from the stack** (`Table::read`). -/
theorem holds_iff_hidden (c : Claim) (hc : c.point.length = L.vars) (q : Column L.logN) :
    StackClaim.Holds L.logN (L.claimWeight c, c.value) q ↔
      ∑ t ∈ range (2 ^ L.vars), ofK (L.readHidden s q t) * eqEval (boolPoint L.vars t) c.point =
        c.value := by
  simp only [StackClaim.Holds]
  suffices h : ∑ x : Fin (2 ^ L.logN), L.claimWeight c (boolPoint L.logN x) *
      ofK (q.values.getD x 0) =
      ∑ t ∈ range (2 ^ L.vars), ofK (L.readHidden s q t) * eqEval (boolPoint L.vars t) c.point by
    rw [h]
  have hR : range (2 ^ L.logN) = range (2 ^ L.logLane * 2 ^ laneFold) := by
    rw [← pow_add, ← hL.logN_eq]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ L.claimWeight c (boolPoint L.logN x) *
    ofK (q.values.getD x 0)) (2 ^ L.logN), hR, sum_range_mul_split]
  have hW : ∀ l ∈ range (2 ^ laneFold), ∀ y ∈ range (2 ^ L.logLane),
      L.claimWeight c (boolPoint L.logN (y + 2 ^ L.logLane * l)) *
          ofK (q.values.getD (y + 2 ^ L.logLane * l) 0) =
        ∑ t ∈ range (2 ^ L.vars), eqEval (boolPoint L.vars t) c.point *
          (if L.role s l y = some t then ofK (stackAt q L.logLane l y) else 0) := by
    intro l hl y hy
    rw [claimWeight_cube hL c hc (mem_range.1 hl) (mem_range.1 hy)]
    rcases hr : L.role s l y with _ | t
    · simp
    · simp only
      rw [Finset.sum_eq_single t]
      · rw [if_pos rfl]; rfl
      · intro t' _ ht'
        rw [if_neg (fun h ↦ ht' (Option.some.inj h).symm), mul_zero]
      · intro ht
        exact absurd (mem_range.2 (role_lt hL (mem_range.1 hy) hr)) ht
  rw [Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl fun y hy ↦ hW l hl y hy]
  have hswap : ∀ (F : ℕ → ℕ → ℕ → E) (A B C : ℕ), ∑ l ∈ range A, ∑ y ∈ range B,
      ∑ t ∈ range C, F l y t = ∑ t ∈ range C, ∑ l ∈ range A, ∑ y ∈ range B, F l y t := by
    intro F A B C
    rw [Finset.sum_congr rfl fun l _ ↦ Finset.sum_comm]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [readHidden_eq_fiber hL q t]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun y _ ↦ mul_comm _ _

end Cube

/-! ## The gadget -/

/-- **The gadget's value on a stack** of pieces `2^s`:
`Σ_g Σ_i β_i · Σ_{l ∈ pattern g} q[l][2^s − 9 + 3g + i]`. -/
def Layout.gadgetValue (L : Layout) (s : ℕ) (q : Column L.logN) : E :=
  ((List.range 3).map fun g ↦ ((List.range 3).map fun i ↦ gadgetBeta i *
    ((gadgetLanes g).map fun l ↦ ofK (stackAt q L.logLane l (gadgetEntry s g i))).sum).sum).sum

/-- A sum over a `Finset` of a list's sum is the list's sum of the sums. -/
theorem finset_sum_list_sum {α : Type} (S : Finset ℕ) (xs : List α) (g : α → ℕ → E) :
    ∑ l ∈ S, (xs.map fun x ↦ g x l).sum = (xs.map fun x ↦ ∑ l ∈ S, g x l).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem sum_delta2 {A B l0 y0 : ℕ} (hl0 : l0 < A) (hy0 : y0 < B) (c : E) :
    ∑ l ∈ range A, ∑ y ∈ range B,
      c * ((if y0 = y then 1 else 0) * (if l0 = l then 1 else 0)) = c := by
  have h : ∀ l ∈ range A, ∑ y ∈ range B,
      c * ((if y0 = y then (1 : E) else 0) * (if l0 = l then 1 else 0)) =
        if l0 = l then c else 0 := by
    intro l _
    rw [Finset.sum_eq_single y0]
    · by_cases h : l0 = l <;> simp [h]
    · intro y _ hy
      rw [if_neg (Ne.symm hy)]
      simp
    · intro h
      exact absurd (mem_range.2 hy0) h
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq, if_pos (mem_range.2 hl0)]

/-- **The gadget's term against a stack**, summed over the cube: each pattern's entries' weights
times its lanes' stack entries there. -/
theorem gadgetSum_cube {N ℓ : ℕ} (hN : N ≤ 2 ^ laneFold) (parts : List (List ℕ × List (ℕ × E)))
    (hlanes : ∀ pe ∈ parts, ∀ l ∈ pe.1, l < N) (hent : ∀ pe ∈ parts, ∀ yb ∈ pe.2, yb.1 < 2 ^ ℓ)
    (f : ℕ → ℕ → E) :
    ∑ l ∈ range (2 ^ laneFold), ∑ y ∈ range (2 ^ ℓ),
        gadgetSum parts (laneEqs N (boolPoint laneFold l)) (boolPoint ℓ y) * f l y =
      (parts.map fun pe ↦ (pe.2.map fun yb ↦ yb.2 * (pe.1.map fun l' ↦ f l' yb.1).sum).sum).sum := by
  have hterm : ∀ l ∈ range (2 ^ laneFold), ∀ y ∈ range (2 ^ ℓ),
      gadgetSum parts (laneEqs N (boolPoint laneFold l)) (boolPoint ℓ y) * f l y =
        (parts.map fun pe ↦ (pe.2.map fun yb ↦ (pe.1.map fun l' ↦
          yb.2 * f l' yb.1 * ((if yb.1 = y then 1 else 0) * (if l' = l then 1 else 0))).sum).sum).sum := by
    intro l hl y hy
    rw [gadgetSum_eq_sum, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun pe hpe ↦ ?_)
    rw [← List.sum_map_mul_right, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun yb hyb ↦ ?_)
    rw [eqBits_cube (hent pe hpe yb hyb) (mem_range.1 hy), ← List.sum_map_mul_left,
      ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun l' hl' ↦ ?_)
    rw [laneEq_cube hN (hlanes pe hpe l' hl') (mem_range.1 hl)]
    by_cases h1 : yb.1 = y
    · by_cases h2 : l' = l
      · rw [if_pos h1, if_pos h2, ← h1, ← h2]
        ring
      · rw [if_neg h2]
        ring
    · rw [if_neg h1]
      ring
  rw [Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl fun y hy ↦ hterm l hl y hy]
  simp only [finset_sum_list_sum]
  refine congrArg List.sum (List.map_congr_left fun pe hpe ↦ ?_)
  refine congrArg List.sum (List.map_congr_left fun yb hyb ↦ ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun l' hl' ↦ ?_)
  rw [sum_delta2 (lt_of_lt_of_le (hlanes pe hpe l' hl') hN) (hent pe hpe yb hyb)]

section Gadget

variable {L : Layout} {s : ℕ} (hL : L.HiddenOK s)

include hL in
/-- **What the gadget says of a stack**: the stack claim the opening adds (`Layout.extra`, the
gadget of value zero) holds exactly when the gadget's value is zero: at the gadget's entries, the
`β`-combination of the pattern lanes' entries is zero. -/
theorem gadget_holds_iff (q : Column L.logN) :
    StackClaim.Holds L.logN (L.gadgetWeight, 0) q ↔ L.gadgetValue s q = 0 := by
  simp only [StackClaim.Holds]
  suffices h : ∑ x : Fin (2 ^ L.logN), L.gadgetWeight (boolPoint L.logN x) *
      ofK (q.values.getD x 0) = L.gadgetValue s q by
    rw [h]
  have hR : range (2 ^ L.logN) = range (2 ^ L.logLane * 2 ^ laneFold) := by
    rw [← pow_add, ← hL.logN_eq]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ L.gadgetWeight (boolPoint L.logN x) *
    ofK (q.values.getD x 0)) (2 ^ L.logN), hR, sum_range_mul_split]
  have hW : ∀ l ∈ range (2 ^ laneFold), ∀ y ∈ range (2 ^ L.logLane),
      L.gadgetWeight (boolPoint L.logN (y + 2 ^ L.logLane * l)) *
          ofK (q.values.getD (y + 2 ^ L.logLane * l) 0) =
        gadgetSum (L.gadgetParts 1) (laneEqs L.lanes.length (boolPoint laneFold l))
          (boolPoint L.logLane y) * ofK (stackAt q L.logLane l y) := by
    intro l hl y hy
    have hx : boolPoint L.logN (y + 2 ^ L.logLane * l) =
        boolPoint L.logLane y ++ boolPoint laneFold l := by
      rw [hL.logN_eq]
      exact LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ (mem_range.1 hy)
    have hlen : (boolPoint L.logLane y).length = L.logLane := boolPoint_length' _ _
    rw [Layout.gadgetWeight, hx, List.take_left' hlen, List.drop_left' hlen]
    rfl
  rw [Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl fun y hy ↦ hW l hl y hy]
  have hparts : L.gadgetParts 1 = (List.range 3).map fun g ↦
      (gadgetLanes g, (List.range 3).map fun i ↦ (gadgetEntry s g i, 1 * gadgetBeta i)) := by
    simp only [Layout.gadgetParts, hL.piece]
  have h9 : gadget < 2 ^ s := hL.gadget_lt
  have hsl : 2 ^ s < 2 ^ L.logLane := Nat.pow_lt_pow_right (by norm_num) hL.s_lt
  rw [gadgetSum_cube hL.lanes_le _ ?_ ?_ (fun l y ↦ ofK (stackAt q L.logLane l y)), hparts]
  · simp only [Layout.gadgetValue, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun g _ ↦ ?_)
    simp only [Function.comp, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun i _ ↦ ?_)
    simp only [Function.comp, one_mul]
  · intro pe hpe l hl
    rw [hparts, List.mem_map] at hpe
    obtain ⟨g, hg, rfl⟩ := hpe
    exact hL.gadget_lanes g (List.mem_range.1 hg) l hl
  · intro pe hpe yb hyb
    rw [hparts, List.mem_map] at hpe
    obtain ⟨g, hg, rfl⟩ := hpe
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hyb
    have hg' := List.mem_range.1 hg
    have hi' := List.mem_range.1 hi
    show gadgetEntry s g i < 2 ^ L.logLane
    unfold gadgetEntry
    unfold gadget at h9 ⊢
    omega

end Gadget

/-! ## Every layout -/

/-- **What the meaning of the claims needs of a layout**: a public one whose blocks are a valid
public stacking, or a hidden one of the shape `Layout::hidden` gives. -/
def Layout.Valid (L : Layout) : Prop :=
  (L.IsPublic ∧ L.toBlocks.Valid) ∨ ∃ s, L.HiddenOK s

/-- **A claim holds of a stack exactly when its table claim holds of the table the stack stands
for**, for every valid layout, public or hidden: the stack claim with the weight `opening::verify`
evaluates, and the table `Table::read` (or a public layout's blocks) reads back. -/
theorem Layout.holds_iff (L : Layout) (hL : L.Valid) (c : Claim) (hc : c.point.length = L.vars)
    (q : Column L.logN) :
    StackClaim.Holds L.logN (L.claimWeight c, c.value) q ↔ L.tableEval q c.point = c.value := by
  rcases hL with ⟨hP, hV⟩ | ⟨s, hH⟩
  · rw [L.claimWeight_toBlocks hP c]
    have h := WhirBridge.holds_iff L.toBlocks hV c hc q
    have he : L.tableEval q c.point = L.toBlocks.tableEval q c.point := by
      simp only [Layout.tableEval, Layout.table, Blocks.tableEval, hP.1]
      rfl
    rw [he]
    exact h
  · rw [holds_iff_hidden hH c hc q]
    unfold Layout.tableEval Layout.table
    rw [hH.piece]

/-- **The gadget holds of a stack**: in a hidden layout of pieces `2^s`, its value is zero;
nothing to hold in a public layout. -/
def Layout.GadgetHolds (L : Layout) (q : Column L.logN) : Prop :=
  match L.logPiece with
  | some s => L.gadgetValue s q = 0
  | none => True

/-- The stack claims the opening adds hold exactly when the gadget does. -/
theorem Layout.extra_holds_iff (L : Layout) (hL : L.Valid) (q : Column L.logN) :
    (∀ sc ∈ L.extra, StackClaim.Holds L.logN sc q) ↔ L.GadgetHolds q := by
  rcases hL with ⟨hP, -⟩ | ⟨s, hH⟩
  · rw [Layout.extra_of_none hP.1]
    simp [Layout.GadgetHolds, hP.1]
  · rw [Layout.extra_of_some hH.piece]
    simp only [List.mem_singleton, forall_eq]
    rw [gadget_holds_iff hH q]
    simp [Layout.GadgetHolds, hH.piece]

/-- **The opening's doom in table terms**, for every valid layout: the level-0 commitment has the
stack's shape, and every candidate's table violates one of the claims or the candidate violates
the gadget (a hidden layout's stack claim of value zero). -/
theorem Layout.openingDoom_iff (L : Layout) (hL : L.Valid) (R : ℕ) (claims : List Claim)
    (hc : ∀ c ∈ claims, c.point.length = L.vars) (cs : List (ℕ × ℕ × Word)) :
    OpeningDoom L.stacking R claims cs ↔
      LeanVM.Protocol.Whir.Sound.ShapeOK 0 (code₀ L.logN R) laneBits cs ∧
        ∀ q ∈ Candidates L.logN R (code₀ L.logN R).thr (LeanVM.Protocol.Whir.Sound.wordOf cs 0),
          (∃ c ∈ claims, L.tableEval q c.point ≠ c.value) ∨ ¬ L.GadgetHolds q := by
  unfold OpeningDoom LeanVM.Protocol.Whir.Sound.StackedPre
  refine and_congr Iff.rfl (forall₂_congr fun q _ ↦ ?_)
  rw [← L.extra_holds_iff hL q]
  constructor
  · rintro ⟨sc, hsc, hn⟩
    rcases List.mem_append.1 hsc with hsc | hsc
    · obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 hsc
      exact Or.inl ⟨c, hcm, fun h ↦ hn ((L.holds_iff hL c (hc c hcm) q).2 h)⟩
    · exact Or.inr fun h ↦ hn (h sc hsc)
  · rintro (⟨c, hcm, hn⟩ | hg)
    · exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨c, hcm, rfl⟩),
        fun h ↦ hn ((L.holds_iff hL c (hc c hcm) q).1 h)⟩
    · push_neg at hg
      obtain ⟨sc, hsc, hn⟩ := hg
      exact ⟨sc, List.mem_append_right _ hsc, hn⟩

/-- **Joint extraction**: a root's commitment of the stack's shape that is not doomed for an
opening has one candidate whose table satisfies all of that opening's claims, and which satisfies
the gadget. -/
theorem Layout.joint_of_not_doom (L : Layout) (hL : L.Valid) (R : ℕ) (claims : List Claim)
    (hc : ∀ c ∈ claims, c.point.length = L.vars) (cs : List (ℕ × ℕ × Word))
    (hshape : LeanVM.Protocol.Whir.Sound.ShapeOK 0 (code₀ L.logN R) laneBits cs)
    (hnot : ¬ OpeningDoom L.stacking R claims cs) :
    ∃ q ∈ Candidates L.logN R (code₀ L.logN R).thr (LeanVM.Protocol.Whir.Sound.wordOf cs 0),
      (∀ c ∈ claims, L.tableEval q c.point = c.value) ∧ L.GadgetHolds q := by
  rw [L.openingDoom_iff hL R claims hc cs] at hnot
  by_contra hno
  refine hnot ⟨hshape, fun q hq ↦ ?_⟩
  by_contra hall
  push_neg at hall
  exact hno ⟨q, hq, hall.1, hall.2⟩

end WhirBridge
