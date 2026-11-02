-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.Openings

/-!
# The deployed opening's claim on a stacked table is the table's multilinear claim

The zero-knowledge model opens the witness and quotient tables on the hidden layouts
`Lw = witness_layout(22)` and `Lq = quotient_layout(22)` (`QuotientSecurity.Hiding.DeployedLayout`):
the table `t` (entry `i` is `t i`) lies on the stack `stackD (place t) + stackR r` (`hiddenWord_eq`),
and a claim at a point `p` weighs the stack by `claimW` (`DeployedWeights.lean`: `opening::verify`'s
weight closure at the Boolean point of `(y, l)`). Here: **the claim on the table's part of the stack
is the table's multilinear claim**, `Σ_i eq_bits(p, i) · t(i)` over the `2^vars` entries, for every
table vanishing off the layout's chunks (`claimsMap_place_witness`, `claimsMap_place_quotient`).

The proof (after `WhirBridge.holds_iff_hidden`, with `Completeness.coveredNew_hiddenNew` for the
coverage):

* `claimsMap_stackD`: the claims weigh nothing where `stackD` zeroes the stack (`WeightsFit`);
* `role`: **the table entry stack entry `(l, y)` holds**: on a block lane `b`, past the first piece,
  the entry `b·2^ℓ + y`; on the overflow lane, at its piece `k ∈ 1 ..= |pieces|`, the entry `y mod
  2^8` of the table's piece `pieces[k − 1]`; nothing else; `place_of_role`: `place` puts it there;
* `claimW_eq`: **a claim's weight at `(l, y)` is `eq_bits(p, i)` of the entry `i` it holds**, or zero
  (in characteristic 2: a block lane's first piece weighs `2·(…)`);
* `Facts`: what the summation needs of a layout (pieces distinct, each block on one lane, every block
  lane's first piece among the pieces and no other piece of its block, all within the table), decided
  for the deployed layouts (`deployed_facts`, `decide +kernel`, on lists of `40`/`63` lanes and
  `33`/`167` pieces); with it, `role` is injective (`Facts.role_inj`) and lands in the table
  (`Facts.role_lt`), and every entry of a chunk is held (`covered_hiddenWith`, `Facts.exists_role`);
* `claimsMap_place`: the general statement.
-/

namespace PcsQuotient.EndToEnd

open Finset QuotientSecurity.Hiding QuotientSecurity.Hiding.Deployed

set_option linter.unusedSectionVars false

/-- The table entries a layout's chunks hold (`Completeness.InChunks`): entry `j < len` of chunk
`(c, len)` is the table's entry `c·2^logChunk + j`. -/
def InChunksD (logChunk : ℕ) (chunks : List (ℕ × ℕ)) (i : ℕ) : Prop :=
  ∃ c ∈ chunks, ∃ j < c.2, i = c.1 * 2 ^ logChunk + j

namespace LayoutClaims

/-! ### `eq_bits` -/

section EqBits

variable {E : Type} [Field E]

theorem eqBits_nil (i : ℕ) : eqBits ([] : List E) i = 1 := by simp [eqBits]

/-- `eq_bits` splits at any coordinate: the low coordinates read the index, the high ones its
shift. -/
theorem eqBits_split (p : List E) (k i : ℕ) :
    eqBits p i = eqBits (p.take k) i * eqBits (p.drop k) (i >>> k) := by
  rcases le_or_gt k p.length with hk | hk
  · unfold eqBits
    rw [List.length_take, List.length_drop, min_eq_left hk]
    have hlen : p.length = k + (p.length - k) := by omega
    conv_lhs => rw [hlen]
    rw [prod_range_add]
    congr 1
    · refine prod_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
        ite_eq_left hj']
    · refine prod_congr rfl fun j _ => ?_
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
        Nat.testBit_shiftRight]
  · rw [List.take_of_length_le hk.le, List.drop_of_length_le hk.le, eqBits_nil, mul_one]

/-- `eq_bits` reads only as many bits of the index as the point has coordinates. -/
theorem eqBits_mod (q : List E) {n : ℕ} (hq : q.length ≤ n) (i : ℕ) :
    eqBits q (i % 2 ^ n) = eqBits q i := by
  unfold eqBits
  refine prod_congr rfl fun j hj => ?_
  have hj' : j < n := lt_of_lt_of_le (mem_range.mp hj) hq
  simp [Nat.testBit_mod_two_pow, hj']

theorem div_split {a s o : ℕ} (ho : o < 2 ^ s) : (a * 2 ^ s + o) / 2 ^ s = a := by
  rw [add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt ho, zero_add]

theorem mod_split {a s o : ℕ} (ho : o < 2 ^ s) : (a * 2 ^ s + o) % 2 ^ s = o := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]

theorem lt_two_pow_split {a s V o : ℕ} (hsV : s ≤ V) (ha : a < 2 ^ (V - s)) (ho : o < 2 ^ s) :
    a * 2 ^ s + o < 2 ^ V := by
  calc a * 2 ^ s + o < (a + 1) * 2 ^ s := by rw [add_mul, one_mul]; omega
    _ ≤ 2 ^ (V - s) * 2 ^ s := Nat.mul_le_mul_right _ ha
    _ = 2 ^ V := by rw [← pow_add, Nat.sub_add_cancel hsV]

/-- `eq_bits` of a table entry `a·2^s + o`: its offset against the low `s` coordinates, its piece
against the others. -/
theorem eqBits_entry (p : List E) {s a o : ℕ} (ho : o < 2 ^ s) :
    eqBits p (a * 2 ^ s + o) = eqBits (p.take s) o * eqBits (p.drop s) a := by
  rw [eqBits_split p s, Nat.shiftRight_eq_div_pow, div_split ho,
    ← eqBits_mod (p.take s) (n := s) (by simp) (a * 2 ^ s + o), mod_split ho]

theorem take_bits (n k y : ℕ) : (bits n y : List E).take k = bits (min k n) y := by
  apply List.ext_getElem
  · simp [length_bits]
  · intro j h1 h2
    simp [bits]

end EqBits

/-! ### The table entry a stack entry holds -/

section Role

variable {L : Layout}

/-- The blocks the lanes hold, in lane order. -/
def laneBlocks (L : Layout) : List ℕ :=
  L.lanes.filterMap fun
    | .block b => some b
    | _ => none

theorem mem_laneBlocks {b : ℕ} : b ∈ laneBlocks L ↔ Lane.block b ∈ L.lanes := by
  unfold laneBlocks
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hab⟩
    rcases a with b' | _ | _
    · simp only [Option.some.injEq] at hab
      subst hab
      exact ha
    · simp at hab
    · simp at hab
  · intro hb
    exact ⟨_, hb, rfl⟩

/-- **The table entry stack entry `(l, y)` holds** (with a weight): on a block lane, past its first
piece, its block's entry `y`; on the overflow lane, at its piece `k ∈ 1 ..= |pieces|`, the entry
`y mod 2^s` of the table's piece `pieces[k − 1]`; nothing else. -/
def role (L : Layout) (l y : ℕ) : Option ℕ :=
  match L.lanes[l]? with
  | some (.block b) => if y / 2 ^ L.logPiece = 0 then none else some ((b <<< L.logLane) + y)
  | some .overflow =>
    if 1 ≤ y / 2 ^ L.logPiece ∧ y / 2 ^ L.logPiece ≤ L.pieces.length then
      some (L.pieces.getD (y / 2 ^ L.logPiece - 1) 0 * 2 ^ L.logPiece + y % 2 ^ L.logPiece)
    else none
  | _ => none

/-- `place` puts at a stack entry the table entry it holds. -/
theorem place_of_role {K : Type} [Field K] (t : ℕ → K) {l y i : ℕ} (hr : role L l y = some i) :
    L.place t l y = t i := by
  unfold role at hr
  unfold Layout.place
  rcases hl : L.lanes[l]? with _ | (b | _ | _) <;> rw [hl] at hr
  · simp at hr
  · dsimp only at hr ⊢
    split_ifs at hr
    simp only [Option.some.injEq] at hr
    rw [hr]
  · dsimp only at hr ⊢
    split_ifs at hr
    simp only [Option.some.injEq] at hr
    rw [hr]
  · simp at hr

/-- What a stack entry holding a table entry is. -/
theorem role_some (h : L.OK) {l y i : ℕ} (hr : role L l y = some i) :
    (∃ b, L.lanes[l]? = some (.block b) ∧ y / 2 ^ logPieceD ≠ 0 ∧ i = b * 2 ^ L.logLane + y) ∨
      (L.lanes[l]? = some .overflow ∧ 1 ≤ y / 2 ^ logPieceD ∧ y / 2 ^ logPieceD ≤ L.pieces.length ∧
        i = L.pieces.getD (y / 2 ^ logPieceD - 1) 0 * 2 ^ logPieceD + y % 2 ^ logPieceD) := by
  have hs : L.logPiece = logPieceD := h.piece
  unfold role at hr
  rw [hs] at hr
  rcases hl : L.lanes[l]? with _ | (b | _ | _) <;> rw [hl] at hr
  · simp at hr
  · dsimp only at hr
    split_ifs at hr with h0
    simp only [Option.some.injEq] at hr
    exact Or.inl ⟨b, rfl, h0, by rw [← hr, Nat.shiftLeft_eq]⟩
  · dsimp only at hr
    split_ifs at hr with hc
    simp only [Option.some.injEq] at hr
    exact Or.inr ⟨rfl, hc.1, hc.2, hr.symm⟩
  · simp at hr

theorem role_block_lane {l y b : ℕ} (hl : L.lanes[l]? = some (.block b)) :
    role L l y = if y / 2 ^ L.logPiece = 0 then none else some ((b <<< L.logLane) + y) := by
  simp only [role, hl]

theorem role_ov_lane {l y : ℕ} (hl : L.lanes[l]? = some .overflow) :
    role L l y =
      if 1 ≤ y / 2 ^ L.logPiece ∧ y / 2 ^ L.logPiece ≤ L.pieces.length then
        some (L.pieces.getD (y / 2 ^ L.logPiece - 1) 0 * 2 ^ L.logPiece + y % 2 ^ L.logPiece)
      else none := by
  simp only [role, hl]

theorem role_rand_lane {l y : ℕ} (hl : L.lanes[l]? = some .random) : role L l y = none := by
  simp only [role, hl]

/-! ### The weight on the cube -/

variable {E : Type} [Field E]

theorem fits' (h : L.OK) : L.pieces.length + 1 ≤ 2 ^ (L.logLane - logPieceD) := by
  have hf := h.fits
  have hl := h.lane
  rw [show L.logLane = (L.logLane - logPieceD) + logPieceD by omega, pow_add] at hf
  exact le_of_mul_le_mul_right hf (by norm_num [logPieceD])

theorem div_lt_window (h : L.OK) {y : ℕ} (hy : y < 2 ^ L.logLane) :
    y / 2 ^ logPieceD < 2 ^ (L.logLane - logPieceD) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
  have hl := h.lane
  rwa [show L.logLane - logPieceD + logPieceD = L.logLane by omega]

/-- `on_blocks` at a lane's cube point: the lane's scale if it holds a block. -/
theorem onBlocks_bool (h2 : (2 : E) = 0) (h : L.OK) (part : Deployed.Part E) {l : ℕ}
    (hl : l < L.lanes.length) :
    L.onBlocks (L.laneEqAt l) part =
      if (L.lanes.getD l .random).isBlock then part.lanes.getD l 0 else 0 := by
  unfold Layout.onBlocks
  rw [sum_eq_single l]
  · rw [Layout.getD_laneEqAt_eq h2 h hl hl, ite_eq_left rfl, mul_one]
  · intro l' hl' hne
    rw [Layout.getD_laneEqAt_eq h2 h hl (mem_range.mp hl'), ite_eq_right hne, mul_zero, ite_self]
  · intro hn
    exact absurd (mem_range.mpr hl) hn

/-- The pieces' term at a cube point: the scale of the held piece there. -/
theorem piecesTerm_bool (h2 : (2 : E) = 0) (h : L.OK) (p : List E) {y : ℕ}
    (hy : y < 2 ^ L.logLane) :
    Layout.piecesTerm logPieceD (bits L.logLane y) (L.part 1 p) =
      if 1 ≤ y / 2 ^ logPieceD ∧ y / 2 ^ logPieceD ≤ L.pieces.length then
        eqBits (p.drop logPieceD) (L.pieces.getD (y / 2 ^ logPieceD - 1) 0) else 0 := by
  have hs : L.logPiece = logPieceD := h.piece
  have hpl : (L.part 1 p).pieces.length = L.pieces.length := by
    simp [Layout.part, Layout.pieceScales]
  have hfit := fits' h
  have hyl := div_lt_window h hy
  have hterm : ∀ k ∈ range (L.part 1 p).pieces.length,
      (L.part 1 p).pieces.getD k 0 * eqBits ((bits L.logLane y : List E).drop logPieceD) (k + 1) =
        if k + 1 = y / 2 ^ logPieceD then eqBits (p.drop logPieceD) (L.pieces.getD k 0) else 0 := by
    intro k hk
    rw [hpl] at hk
    have hk' := mem_range.mp hk
    rw [drop_bits, Nat.shiftRight_eq_div_pow, eqBits_bits_eq h2 hyl (by omega)]
    have hpk : (L.part 1 p).pieces.getD k 0 = eqBits (p.drop logPieceD) (L.pieces.getD k 0) := by
      rw [List.getD_eq_getElem _ _ (by rw [hpl]; exact hk'), List.getD_eq_getElem _ _ hk']
      simp [Layout.part, Layout.pieceScales, hs]
    rw [hpk]
    split_ifs <;> ring
  unfold Layout.piecesTerm
  rw [sum_congr rfl hterm]
  by_cases hc : 1 ≤ y / 2 ^ logPieceD ∧ y / 2 ^ logPieceD ≤ L.pieces.length
  · rw [ite_eq_left hc, sum_eq_single (y / 2 ^ logPieceD - 1)]
    · rw [ite_eq_left (by omega)]
    · intro k _ hk
      rw [ite_eq_right (by omega)]
    · intro hn
      exact absurd (mem_range.mpr (by rw [hpl]; omega)) hn
  · rw [ite_eq_right hc]
    refine sum_eq_zero fun k hk => ?_
    rw [hpl] at hk
    have hk' := mem_range.mp hk
    rw [ite_eq_right (by omega)]

/-- **A claim's weight at a stack entry is `eq_bits` of the table entry it holds**, or zero. -/
theorem claimW_eq (h2 : (2 : E) = 0) (h : L.OK) {m : ℕ} (points : Fin m → List E) (c : Fin m)
    (l : Fin L.lanes.length) (y : Fin (2 ^ L.logLane)) :
    L.claimW points c l y = match role L l y with
      | some i => eqBits (points c) i
      | none => 0 := by
  have hs : L.logPiece = logPieceD := h.piece
  have hℓ := h.lane
  have hy := y.isLt
  have hl := l.isLt
  have hyl := div_lt_window h hy
  show L.claimTerm (L.laneEqAt l) (bits L.logLane y) (L.part 1 (points c)) = _
  generalize points c = p
  have hlow : (L.part 1 p).low = p.take L.logLane := rfl
  have hbelow : eqZ ((p.take L.logLane).take logPieceD)
      ((bits L.logLane y : List E).take logPieceD) = eqBits ((p.take L.logLane).take logPieceD) y := by
    rw [take_bits, min_eq_left hℓ.le]
    exact eqZ_bits h2 _ _ _ (by simp)
  have hA : ((p.take L.logLane).drop logPieceD).length ≤ L.logLane - logPieceD := by
    simp only [List.length_drop, List.length_take]
    omega
  have habove : eqZ ((p.take L.logLane).drop logPieceD)
      ((bits L.logLane y : List E).drop logPieceD) =
        eqBits ((p.take L.logLane).drop logPieceD) (y / 2 ^ logPieceD) := by
    rw [drop_bits, eqZ_bits h2 _ _ _ hA, Nat.shiftRight_eq_div_pow]
  have hfirst : onePlusProd ((bits L.logLane y : List E).drop logPieceD) =
      if (y : ℕ) / 2 ^ logPieceD = 0 then 1 else 0 := by
    rw [onePlusProd_eq, drop_bits, Nat.shiftRight_eq_div_pow,
      eqBits_bits_eq h2 hyl (Nat.two_pow_pos _)]
    exact if_congr eq_comm rfl rfl
  have hov : (L.laneEqAt l : List E).getD L.overflow 0 =
      if (l : ℕ) = overflowLane then 1 else 0 := by
    rw [h.overflow, Layout.getD_laneEqAt_eq h2 h hl (show overflowLane < L.lanes.length from h.n32)]
    exact if_congr eq_comm rfl rfl
  rcases hlane : L.lanes[(l : ℕ)]? with _ | (b | _ | _)
  · rw [List.getElem?_eq_none_iff] at hlane
    omega
  · -- A block lane.
    have hgetD : L.lanes.getD l .random = .block b := by
      rw [List.getD_eq_getElem?_getD, hlane]
      rfl
    have hne : (l : ℕ) ≠ overflowLane := by
      intro he
      have := h.at_ov
      rw [← he, hlane] at this
      simp at this
    have hscale : (L.part 1 p).lanes.getD l 0 = eqBits (p.drop L.logLane) b := by
      show ((L.laneScales p).map (1 * ·)).getD l 0 = _
      rw [Layout.getD_map_mul, one_mul, List.getD_eq_getElem?_getD, Layout.laneScales,
        List.getElem?_map, hlane]
      rfl
    by_cases h0 : (y : ℕ) / 2 ^ logPieceD = 0
    · have hrole : role L l y = none := by rw [role_block_lane hlane, hs, ite_eq_left h0]
      rw [hrole]
      have hy8 : (y : ℕ) < 2 ^ logPieceD := by
        by_contra hc
        have := Nat.div_pos (not_lt.mp hc) (Nat.two_pow_pos logPieceD)
        omega
      exact Layout.claimTerm_first h2 h 1 p l y hy8
    · have hrole : role L l y = some ((b <<< L.logLane) + y) := by
        rw [role_block_lane hlane, hs, ite_eq_right h0]
      rw [hrole]
      simp only [Layout.claimTerm, hs, hlow]
      rw [hbelow, habove, hfirst, ite_eq_right h0, hov, ite_eq_right hne, onBlocks_bool h2 h _ hl,
        hgetD, ite_eq_left (show (Lane.block b).isBlock = true from rfl), hscale, Nat.shiftLeft_eq,
        eqBits_entry p hy,
        eqBits_split (p.take L.logLane) logPieceD y, Nat.shiftRight_eq_div_pow]
      ring
  · -- The overflow lane.
    have hl32 : (l : ℕ) = overflowLane := h.ov_unique l hl hlane
    have hgetD : (L.lanes.getD l .random).isBlock = false := by
      rw [List.getD_eq_getElem?_getD, hlane]
      rfl
    simp only [Layout.claimTerm, hs, hlow]
    rw [Layout.onBlocks_zero h2 h _ hl hgetD, hov, ite_eq_left hl32, hbelow,
      piecesTerm_bool h2 h p hy, List.take_take, min_eq_left hℓ.le]
    by_cases hc : 1 ≤ (y : ℕ) / 2 ^ logPieceD ∧ (y : ℕ) / 2 ^ logPieceD ≤ L.pieces.length
    · have hrole : role L l y = some (L.pieces.getD ((y : ℕ) / 2 ^ logPieceD - 1) 0 *
          2 ^ logPieceD + (y : ℕ) % 2 ^ logPieceD) := by
        rw [role_ov_lane hlane, hs, ite_eq_left hc]
      rw [hrole, ite_eq_left hc]
      dsimp only
      rw [eqBits_entry p (Nat.mod_lt _ (Nat.two_pow_pos _)),
        eqBits_mod (p.take logPieceD) (n := logPieceD) (by simp)]
      ring
    · have hrole : role L l y = none := by rw [role_ov_lane hlane, hs, ite_eq_right hc]
      rw [hrole, ite_eq_right hc]
      dsimp only
      ring
  · -- A random lane.
    have hrole : role L l y = none := role_rand_lane hlane
    rw [hrole]
    have hne : (l : ℕ) ≠ overflowLane := by
      intro he
      have := h.at_ov
      rw [← he, hlane] at this
      simp at this
    refine Layout.claimTerm_noBlock h2 h 1 p hl ?_ (Or.inl hne) hy
    rw [List.getD_eq_getElem?_getD, hlane]
    rfl

end Role

/-! ### What the summation needs of a layout -/

/-- **The facts the claims' meaning needs of a hidden layout**, beyond `Layout.OK`, all true by
construction of `Layout::hidden_with` (decided for the deployed layouts, `deployed_facts`): lanes
inside the table, the pieces distinct and in the table, each block on one lane (its first lane:
`idxOf`) and in the table, every block lane's first piece among the pieces, and no other piece of its
block. -/
structure Facts (L : Layout) : Prop where
  lane_le : L.logLane ≤ L.vars
  nodup : L.pieces.Nodup
  piece_lt : ∀ q ∈ L.pieces, q < 2 ^ (L.vars - logPieceD)
  block_idx : ∀ l, l < L.lanes.length → (L.lanes.getD l .random).isBlock = true →
    L.lanes.idxOf (L.lanes.getD l .random) = l
  block_lt : ∀ b ∈ laneBlocks L, b < 2 ^ (L.vars - L.logLane)
  first_mem : ∀ b ∈ laneBlocks L, b <<< (L.logLane - logPieceD) ∈ L.pieces
  first_only : ∀ b ∈ laneBlocks L, ∀ q ∈ L.pieces,
    q >>> (L.logLane - logPieceD) = b → q = b <<< (L.logLane - logPieceD)

/-- `Facts` as one decidable conjunction. -/
def FactsC (L : Layout) : Prop :=
  L.logLane ≤ L.vars ∧ L.pieces.Nodup ∧ (∀ q ∈ L.pieces, q < 2 ^ (L.vars - logPieceD)) ∧
    (∀ l, l < L.lanes.length → (L.lanes.getD l .random).isBlock = true →
      L.lanes.idxOf (L.lanes.getD l .random) = l) ∧
    (∀ b ∈ laneBlocks L, b < 2 ^ (L.vars - L.logLane)) ∧
    (∀ b ∈ laneBlocks L, b <<< (L.logLane - logPieceD) ∈ L.pieces) ∧
    (∀ b ∈ laneBlocks L, ∀ q ∈ L.pieces,
      q >>> (L.logLane - logPieceD) = b → q = b <<< (L.logLane - logPieceD))

instance (L : Layout) : Decidable (FactsC L) := by
  unfold FactsC; infer_instance

theorem FactsC.toFacts {L : Layout} (h : FactsC L) : Facts L :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem deployed_factsC : FactsC (witnessLayout 22) ∧ FactsC (quotientLayout 22) := by
  decide +kernel

/-- **The deployed layouts have the facts.** -/
theorem deployed_facts : Facts (witnessLayout 22) ∧ Facts (quotientLayout 22) :=
  ⟨deployed_factsC.1.toFacts, deployed_factsC.2.toFacts⟩

section Facts

variable {L : Layout}

theorem Facts.block_inj (F : Facts L) {l l' b : ℕ} (hl : L.lanes[l]? = some (.block b))
    (hl' : L.lanes[l']? = some (.block b)) : l = l' := by
  have hlt : l < L.lanes.length := (List.getElem?_eq_some_iff.mp hl).1
  have hlt' : l' < L.lanes.length := (List.getElem?_eq_some_iff.mp hl').1
  have hg : L.lanes.getD l .random = .block b := by
    rw [List.getD_eq_getElem?_getD, hl]
    rfl
  have hg' : L.lanes.getD l' .random = .block b := by
    rw [List.getD_eq_getElem?_getD, hl']
    rfl
  have e1 := F.block_idx l hlt (by rw [hg]; rfl)
  have e2 := F.block_idx l' hlt' (by rw [hg']; rfl)
  rw [hg] at e1
  rw [hg'] at e2
  exact e1.symm.trans e2

/-- The table entries the stack holds are in the table. -/
theorem Facts.role_lt (h : L.OK) (F : Facts L) {l y i : ℕ} (hy : y < 2 ^ L.logLane)
    (hr : role L l y = some i) : i < 2 ^ L.vars := by
  rcases role_some h hr with ⟨b, hl, -, rfl⟩ | ⟨-, h1, h2, rfl⟩
  · exact lt_two_pow_split F.lane_le (F.block_lt b (mem_laneBlocks.mpr (List.mem_of_getElem? hl))) hy
  · have hmem : L.pieces.getD (y / 2 ^ logPieceD - 1) 0 ∈ L.pieces := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    exact lt_two_pow_split (le_trans h.lane.le F.lane_le) (F.piece_lt _ hmem)
      (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- No stack entry of a block lane past its first piece holds what the overflow lane holds. -/
theorem Facts.block_ne_piece (h : L.OK) (F : Facts L) {b y q o : ℕ} (hb : b ∈ laneBlocks L)
    (hy : y < 2 ^ L.logLane) (h0 : y / 2 ^ logPieceD ≠ 0) (hq : q ∈ L.pieces)
    (ho : o < 2 ^ logPieceD) : b * 2 ^ L.logLane + y ≠ q * 2 ^ logPieceD + o := by
  intro he
  have hℓ := h.lane
  have e2 : 2 ^ L.logLane = 2 ^ (L.logLane - logPieceD) * 2 ^ logPieceD := by
    rw [← pow_add, Nat.sub_add_cancel hℓ.le]
  have hsplit : b * 2 ^ L.logLane + y = 2 ^ logPieceD * (b * 2 ^ (L.logLane - logPieceD)) + y := by
    rw [e2]
    ring
  have hq' : q = b * 2 ^ (L.logLane - logPieceD) + y / 2 ^ logPieceD := by
    have h1 : (b * 2 ^ L.logLane + y) / 2 ^ logPieceD = q := by rw [he, div_split ho]
    rw [← h1, hsplit, Nat.mul_add_div (Nat.two_pow_pos _)]
  have hyl := div_lt_window h hy
  have hsh : q >>> (L.logLane - logPieceD) = b := by
    rw [Nat.shiftRight_eq_div_pow, hq', mul_comm, Nat.mul_add_div (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hyl, add_zero]
  have := F.first_only b hb q hq hsh
  rw [Nat.shiftLeft_eq, hq'] at this
  omega

/-- **`role` is injective**: no two stack entries hold the same table entry. -/
theorem Facts.role_inj (h : L.OK) (F : Facts L) {l l' y y' i : ℕ} (hy : y < 2 ^ L.logLane)
    (hy' : y' < 2 ^ L.logLane) (hr : role L l y = some i) (hr' : role L l' y' = some i) :
    l = l' ∧ y = y' := by
  rcases role_some h hr with ⟨b, hl, h0, rfl⟩ | ⟨hl, h1, h2, hi⟩ <;>
    rcases role_some h hr' with ⟨b', hl', h0', he⟩ | ⟨hl', h1', h2', he⟩
  · -- two block lanes
    have hmod : (b * 2 ^ L.logLane + y) % 2 ^ L.logLane =
        (b' * 2 ^ L.logLane + y') % 2 ^ L.logLane := by rw [he]
    have hdiv : (b * 2 ^ L.logLane + y) / 2 ^ L.logLane =
        (b' * 2 ^ L.logLane + y') / 2 ^ L.logLane := by rw [he]
    rw [mod_split hy, mod_split hy'] at hmod
    rw [div_split hy, div_split hy'] at hdiv
    subst hdiv
    exact ⟨F.block_inj hl hl', hmod⟩
  · exact absurd he (F.block_ne_piece h (mem_laneBlocks.mpr (List.mem_of_getElem? hl)) hy h0
      (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
      (Nat.mod_lt _ (Nat.two_pow_pos _)))
  · exact absurd (hi.symm.trans he) (F.block_ne_piece h (mem_laneBlocks.mpr (List.mem_of_getElem? hl'))
      hy' h0' (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
      (Nat.mod_lt _ (Nat.two_pow_pos _))).symm
  · -- the overflow lane, twice
    have hll : l = l' := by
      rw [h.ov_unique l (List.getElem?_eq_some_iff.mp hl).1 hl,
        h.ov_unique l' (List.getElem?_eq_some_iff.mp hl').1 hl']
    have he' := hi.symm.trans he
    have hmod := congrArg (· % 2 ^ logPieceD) he'
    have hdiv := congrArg (· / 2 ^ logPieceD) he'
    have ho := Nat.mod_lt y (Nat.two_pow_pos logPieceD)
    have ho' := Nat.mod_lt y' (Nat.two_pow_pos logPieceD)
    beta_reduce at hmod hdiv
    rw [mod_split ho, mod_split ho'] at hmod
    rw [div_split ho, div_split ho'] at hdiv
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hdiv
    have hk := (List.Nodup.getElem_inj_iff F.nodup).mp hdiv
    have hq : y / 2 ^ logPieceD = y' / 2 ^ logPieceD := by omega
    refine ⟨hll, ?_⟩
    calc y = 2 ^ logPieceD * (y / 2 ^ logPieceD) + y % 2 ^ logPieceD := (Nat.div_add_mod _ _).symm
      _ = 2 ^ logPieceD * (y' / 2 ^ logPieceD) + y' % 2 ^ logPieceD := by rw [hq, hmod]
      _ = y' := Nat.div_add_mod _ _

/-- **A table entry whose piece is held, or whose block is on a lane, is held by a stack entry.** -/
theorem Facts.exists_role (h : L.OK) (F : Facts L) {i : ℕ}
    (hi : i / 2 ^ logPieceD ∈ L.pieces ∨ Lane.block (i / 2 ^ L.logLane) ∈ L.lanes) :
    ∃ l < L.lanes.length, ∃ y < 2 ^ L.logLane, role L l y = some i := by
  have hs : L.logPiece = logPieceD := h.piece
  have hℓ := h.lane
  have hfit := fits' h
  have ho := Nat.mod_lt i (Nat.two_pow_pos logPieceD)
  have hpiece : i / 2 ^ logPieceD ∈ L.pieces →
      ∃ l < L.lanes.length, ∃ y < 2 ^ L.logLane, role L l y = some i := by
    intro hm
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hm
    refine ⟨overflowLane, h.n32, (k + 1) * 2 ^ logPieceD + i % 2 ^ logPieceD,
      lt_two_pow_split hℓ.le (by omega) ho, ?_⟩
    unfold role
    rw [h.at_ov, hs]
    dsimp only
    rw [div_split ho, ite_eq_left ⟨by omega, by omega⟩, mod_split ho, Nat.add_sub_cancel,
      List.getD_eq_getElem _ _ hk, hkeq, Nat.div_add_mod']
  rcases hi with hm | hm
  · exact hpiece hm
  · obtain ⟨l, hl, hleq⟩ := List.getElem_of_mem hm
    by_cases h0 : (i % 2 ^ L.logLane) / 2 ^ logPieceD = 0
    · apply hpiece
      have hb : i / 2 ^ L.logLane ∈ laneBlocks L := mem_laneBlocks.mpr hm
      have hfm := F.first_mem _ hb
      rw [Nat.shiftLeft_eq] at hfm
      have e : i = 2 ^ logPieceD * (i / 2 ^ L.logLane * 2 ^ (L.logLane - logPieceD)) +
          i % 2 ^ L.logLane := by
        conv_lhs => rw [← Nat.div_add_mod i (2 ^ L.logLane)]
        rw [show 2 ^ L.logLane = 2 ^ (L.logLane - logPieceD) * 2 ^ logPieceD by
          rw [← pow_add, Nat.sub_add_cancel hℓ.le]]
        ring
      have hd : i / 2 ^ logPieceD = i / 2 ^ L.logLane * 2 ^ (L.logLane - logPieceD) := by
        conv_lhs => rw [e]
        rw [Nat.mul_add_div (Nat.two_pow_pos _), h0, add_zero]
      rw [hd]
      exact hfm
    · refine ⟨l, hl, i % 2 ^ L.logLane, Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
      unfold role
      rw [List.getElem?_eq_getElem hl, hleq, hs]
      dsimp only
      rw [ite_eq_right h0, Nat.shiftLeft_eq, Nat.div_add_mod']

/-- A stack entry's contribution: `f` of the table entry it holds, or zero. -/
def roleVal {M : Type} [Zero M] (L : Layout) (f : ℕ → M) (l y : ℕ) : M :=
  match role L l y with
  | some i => f i
  | none => 0

/-- **Summing over the stack entries is summing over the table entries they hold**, for a function
vanishing off the held entries. -/
theorem Facts.sum_roles {M : Type} [AddCommMonoid M] (h : L.OK) (F : Facts L) (f : ℕ → M)
    (hf : ∀ i, f i ≠ 0 → ∃ l < L.lanes.length, ∃ y < 2 ^ L.logLane, role L l y = some i) :
    ∑ x : Fin L.lanes.length × Fin (2 ^ L.logLane), roleVal L f x.1 x.2 =
      ∑ i ∈ range (2 ^ L.vars), f i := by
  have hzero : ∀ x : Fin L.lanes.length × Fin (2 ^ L.logLane), role L x.1 x.2 = none →
      roleVal L f x.1 x.2 = 0 := fun x hr => by simp [roleVal, hr]
  refine sum_bij_ne_zero (fun x _ _ => (role L x.1 x.2).getD 0) ?_ ?_ ?_ ?_
  · intro x _ hx
    rcases hr : role L x.1 x.2 with _ | i
    · exact absurd (hzero x hr) hx
    · exact mem_range.mpr (F.role_lt h x.2.isLt hr)
  · intro x _ hx x' _ hx' he
    rcases hr : role L x.1 x.2 with _ | i
    · exact absurd (hzero x hr) hx
    rcases hr' : role L x'.1 x'.2 with _ | i'
    · exact absurd (hzero x' hr') hx'
    rw [hr, hr'] at he
    simp only [Option.getD_some] at he
    subst he
    obtain ⟨e1, e2⟩ := F.role_inj h x.2.isLt x'.2.isLt hr hr'
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · intro i _ hfi
    obtain ⟨l, hl, y, hy, hr⟩ := hf i hfi
    refine ⟨(⟨l, hl⟩, ⟨y, hy⟩), mem_univ _, ?_, ?_⟩
    · simpa [roleVal, hr] using hfi
    · simp [hr]
  · intro x _ hx
    rcases hr : role L x.1 x.2 with _ | i
    · exact absurd (hzero x hr) hx
    · simp [roleVal, hr]

end Facts

/-! ### Coverage: `hidden_with` holds its chunks -/

/-- `hidden_with`'s lanes. -/
def hiddenLanes (blocks : List ℕ) (random : ℕ) : List Lane :=
  (blocks.take (min blocks.length overflowLane)).map Lane.block ++
    List.replicate (overflowLane - min blocks.length overflowLane) Lane.random ++ [Lane.overflow] ++
    List.replicate random Lane.random ++ (blocks.drop (min blocks.length overflowLane)).map Lane.block

theorem hiddenWith_lanes (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) (random logPiece : ℕ) :
    (hiddenWith vars logChunk logN chunks random logPiece).lanes =
      hiddenLanes (hiddenBlocks logChunk (logN - laneFold) chunks) random := rfl

theorem mem_pieces_of_tail {vars logChunk logN random logPiece : ℕ} {chunks : List (ℕ × ℕ)}
    {x : ℕ} (hx : x ∈ hiddenTails logChunk (logN - laneFold) logPiece chunks) :
    x ∈ (hiddenWith vars logChunk logN chunks random logPiece).pieces :=
  List.mem_append_right _ hx

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

/-- **Every entry of a chunk is held** by `hidden_with`: entry `j < len` of chunk `(c, len)` is in a
whole block (on a lane) or in a tail piece (an overflow piece). -/
theorem covered_hiddenWith {vars logChunk logN random logPiece : ℕ} {chunks : List (ℕ × ℕ)}
    (hs : logPiece ≤ logN - laneFold) (hl : logN - laneFold ≤ logChunk) {i : ℕ}
    (hi : InChunksD logChunk chunks i) :
    i / 2 ^ logPiece ∈ (hiddenWith vars logChunk logN chunks random logPiece).pieces ∨
      Lane.block (i / 2 ^ (logN - laneFold)) ∈
        (hiddenWith vars logChunk logN chunks random logPiece).lanes := by
  obtain ⟨⟨c, len⟩, hmem, j, hj, rfl⟩ := hi
  dsimp only at hj ⊢
  set ℓ := logN - laneFold with hℓ
  have e1 : 2 ^ logChunk = 2 ^ (logChunk - ℓ) * 2 ^ ℓ := by rw [← pow_add, Nat.sub_add_cancel hl]
  have e2 : 2 ^ ℓ = 2 ^ (ℓ - logPiece) * 2 ^ logPiece := by rw [← pow_add, Nat.sub_add_cancel hs]
  by_cases hjw : j < (len >>> ℓ) * 2 ^ ℓ
  · right
    have hblk : (c * 2 ^ logChunk + j) / 2 ^ ℓ = c <<< (logChunk - ℓ) + j / 2 ^ ℓ := by
      rw [Nat.shiftLeft_eq, e1,
        show c * (2 ^ (logChunk - ℓ) * 2 ^ ℓ) + j = j + c * 2 ^ (logChunk - ℓ) * 2 ^ ℓ by ring,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), add_comm]
    rw [hblk, hiddenWith_lanes]
    apply block_mem_hiddenLanes
    simp only [hiddenBlocks, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨(c, len), hmem, j / 2 ^ ℓ,
      by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; exact hjw, rfl⟩
  · left
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (not_lt.mp hjw)
    have hrl : r < len - (len >>> ℓ) <<< ℓ := by rw [Nat.shiftLeft_eq]; omega
    have hpiece : (c * 2 ^ logChunk + j) / 2 ^ logPiece =
        ((c <<< (logChunk - ℓ)) + (len >>> ℓ)) <<< (ℓ - logPiece) + r / 2 ^ logPiece := by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, hr, e1, e2,
        show c * (2 ^ (logChunk - ℓ) * (2 ^ (ℓ - logPiece) * 2 ^ logPiece)) +
            ((len >>> ℓ) * (2 ^ (ℓ - logPiece) * 2 ^ logPiece) + r) =
          r + (c * 2 ^ (logChunk - ℓ) + (len >>> ℓ)) * 2 ^ (ℓ - logPiece) * 2 ^ logPiece by ring,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), add_comm]
    rw [hpiece]
    apply mem_pieces_of_tail
    simp only [hiddenTails, List.mem_flatMap, List.mem_map, List.mem_range]
    refine ⟨(c, len), hmem, r / 2 ^ logPiece, ?_, rfl⟩
    have hps : 0 < 2 ^ logPiece := Nat.two_pow_pos _
    show r / 2 ^ logPiece < (len - (len >>> ℓ) <<< ℓ + 2 ^ logPiece - 1) / 2 ^ logPiece
    calc r / 2 ^ logPiece < r / 2 ^ logPiece + 1 := Nat.lt_succ_self _
      _ = (r + 2 ^ logPiece) / 2 ^ logPiece := (Nat.add_div_right r hps).symm
      _ ≤ _ := Nat.div_le_div_right (by omega)

/-! ### The claims on the table's part of the stack -/

/-- The claims weigh nothing where `stackD` zeroes the stack. -/
theorem claimsMap_stackD {K E : Type} [Field K] [Field E] [Algebra K E] {ι Y : Type} [Fintype ι]
    [DecidableEq ι] [Fintype Y] [DecidableEq Y] (G : GadgetLayout ι Y) {m : ℕ}
    {W : Fin m → ι → Y → E} (hW : G.WeightsFit W) (d : ι → Y → K) :
    HiddenLayout.claimsMap W (G.stackD d) = HiddenLayout.claimsMap W d := by
  funext c
  show ∑ l, ∑ y, W c l y * algebraMap K E (if G.randPos l y then 0 else d l y) =
    ∑ l, ∑ y, W c l y * algebraMap K E (d l y)
  refine sum_congr rfl fun l _ => sum_congr rfl fun y _ => ?_
  by_cases hr : G.randPos l y
  · rw [ite_eq_left hr]
    have hz : W c l y = 0 := by
      rcases hr with hy | hy | hy | ⟨rfl, hy⟩
      · exact hW.first c l y hy
      · exact hW.gadget c l y hy
      · exact hW.rand c l y hy
      · exact hW.off_held c y hy
    rw [hz, zero_mul, zero_mul]
  · rw [ite_eq_right hr]

/-- **The claim on the table's part of the stack is the table's multilinear claim**, for a layout
with the facts and a table vanishing off the entries it holds. -/
theorem claimsMap_place {K E : Type} [Field K] [Field E] [Algebra K E] (h2 : (2 : E) = 0)
    {L : Layout} (h : L.OK) (F : Facts L) (t : ℕ → K)
    (ht : ∀ i, t i ≠ 0 → i / 2 ^ logPieceD ∈ L.pieces ∨ Lane.block (i / 2 ^ L.logLane) ∈ L.lanes)
    {m : ℕ} (points : Fin m → List E) (c : Fin m) :
    HiddenLayout.claimsMap (L.claimW points)
        ((L.toGadget h).stackD (K := K) (fun l y => L.place t l y)) c =
      ∑ i ∈ range (2 ^ L.vars), eqBits (points c) i * algebraMap K E (t i) := by
  rw [claimsMap_stackD (L.toGadget h) (Layout.weightsFit h2 h points)]
  show ∑ l, ∑ y, L.claimW points c l y * algebraMap K E (L.place t l y) = _
  have hsum := F.sum_roles h (fun i => eqBits (points c) i * algebraMap K E (t i)) (by
    intro i hi
    have hti : t i ≠ 0 := fun h0 => hi (by simp [h0])
    exact F.exists_role h (ht i hti))
  rw [Fintype.sum_prod_type] at hsum
  rw [← hsum]
  refine sum_congr rfl fun l _ => sum_congr rfl fun y _ => ?_
  show _ = roleVal L _ l y
  rw [claimW_eq h2 h points c l y]
  unfold roleVal
  rcases hr : role L l y with _ | i
  · exact zero_mul _
  · show eqBits (points c) i * _ = eqBits (points c) i * _
    rw [place_of_role t hr]

end LayoutClaims

open LayoutClaims

/-- **The witness opening's claim on the stacked witness table is the table's multilinear claim**
(`witness_layout(22)`, `2^25` entries), for a table vanishing off its chunks. -/
theorem claimsMap_place_witness {K E : Type} [Field K] [Field E] [Algebra K E] [CharP E 2]
    (t : ℕ → K) (ht : ∀ i, ¬ InChunksD 24 [(0, 2 ^ 24), (1, 16)] i → t i = 0)
    {m : ℕ} (points : Fin m → List E) (c : Fin m) :
    HiddenLayout.claimsMap (QuotientZk.Instance.Lw.claimW points)
        ((QuotientZk.Instance.Lw.toGadget QuotientZk.Instance.okW).stackD (K := K)
          (fun l y => QuotientZk.Instance.Lw.place t l y)) c =
      ∑ i ∈ Finset.range (2 ^ 25), eqBits (points c) i * algebraMap K E (t i) :=
  claimsMap_place CharTwo.two_eq_zero QuotientZk.Instance.okW deployed_facts.1 t
    (fun i hi => covered_hiddenWith (vars := 25) (logChunk := 24) (logN := 25)
      (chunks := [(0, 2 ^ 24), (1, 16)]) (random := randomLanesD) (logPiece := logPieceD)
      (by decide) (by decide) (by_contra fun hn => hi (ht i hn))) points c

/-- **The quotient opening's claims on the stacked quotient table are the table's multilinear
claims** (`quotient_layout(22)`, `2^30` entries), for a table vanishing off its chunks. -/
theorem claimsMap_place_quotient {K E : Type} [Field K] [Field E] [Algebra K E] [CharP E 2]
    (t : ℕ → K) (ht : ∀ i, ¬ InChunksD 24 (quotientChunks 24 qSpill 64) i → t i = 0)
    {m : ℕ} (points : Fin m → List E) (c : Fin m) :
    HiddenLayout.claimsMap (QuotientZk.Instance.Lq.claimW points)
        ((QuotientZk.Instance.Lq.toGadget QuotientZk.Instance.okQ).stackD (K := K)
          (fun l y => QuotientZk.Instance.Lq.place t l y)) c =
      ∑ i ∈ Finset.range (2 ^ 30), eqBits (points c) i * algebraMap K E (t i) :=
  claimsMap_place CharTwo.two_eq_zero QuotientZk.Instance.okQ deployed_facts.2 t
    (fun i hi => covered_hiddenWith (vars := 30) (logChunk := 24) (logN := 28)
      (chunks := quotientChunks 24 qSpill 64) (random := randomLanesD) (logPiece := logPieceD)
      (by decide) (by decide) (by_contra fun hn => hi (ht i hn))) points c

/-- info: 'PcsQuotient.EndToEnd.claimsMap_place_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimsMap_place_witness

/-- info: 'PcsQuotient.EndToEnd.claimsMap_place_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms claimsMap_place_quotient

end PcsQuotient.EndToEnd
