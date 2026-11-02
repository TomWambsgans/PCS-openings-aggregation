-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0) through `Completeness` and `WhirBridge` (`Column`, `StackClaim.Holds`,
-- `IsMultilinearFn`).
import E2ECompleteness.ProverDefs
import E2ECompleteness.ProverLayout
import Completeness.HiddenOpenings

/-!
# The Statement's honest stacks make the openings' stack claims true

The Statement's honest prover stacks a table with `Layout.stackOf` (`Prover.lean`): in a hidden layout
every lane's first piece is padding, a block lane holds its block's later pieces, the overflow lane its
held pieces then padding, a random lane padding, and the gadget's entries are cancelled
(`Layout.cancelGadget`). Completeness's proof layer (`formal/Completeness`, `HiddenFill.lean`) stacks
a table with `Layout.fillNew`, and proves the table read back from it (`readNew_fillNew`) and the
gadget cancelled on it (`gadgetValue_fillNew`). Here:

* **`colOf_stackOf`**: for every hidden layout of the shape `Layout::hidden` gives
  (`NewHiddenOK` of its translation `layoutTr`, `ProverLayout.lean`), WHIR's column of the Statement's
  stack (`colOf`, `ProverDefs.lean`) **is** Completeness's `fillNew` of the same entries, the padding
  reindexed (`padTr`: the Statement continues the overflow lane's stream after its held pieces). The
  gadget's nine writes are read entry by entry (`cancelGadget_getD`).
* **`hidden_stackClaims_hold`**: hence, through Bridge-Defs' `stackClaims_eq` (the Statement's stack
  claims are F2's) and F2's meaning of a claim (`Layout.holds_iff`) and of the gadget
  (`Layout.extra_holds_iff`), every stack claim of the opening holds of the honest stack when the
  table's claims are true, for entries agreeing with the table wherever the layout holds it.
* **`coveredNew_hiddenNew_inv`**: what a hidden layout holds is its chunks' entries, or the ends of
  their last pieces (`PastChunks`): the overflow lane holds whole pieces of `2^s`.
* The deployed layouts (`LOG_ROWS = 22`): **`witness_stackClaims_hold`**,
  **`quotient_stackClaims_hold`** (hidden), **`wiring_stackClaims_hold`** (public: the stack is the
  table), and **`stackClaims_multilinear`** (each stack claim's weight is multilinear, as mumbai's
  completeness of the opening asks).

The entries `entry` the stack reads must agree with the table `T` on the table's chunks (`hE`) and vanish
on the ends of their last pieces (`hZ`), where the table vanishes but the overflow lane still holds
entries (the witness table's last piece, entries `2^24 + 16 … 2^24 + 255`; the quotient table's spills'
and the gate quotient's last pieces). The Statement's `witnessEntry` vanishes there (sixteen mask
entries); its `quotientEntry` there is the quotients' coefficients past their degree bounds.
-/

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier

set_option autoImplicit false

namespace E2ECompleteness

/-! ## Arrays -/

theorem getD_setIfInBounds (a : Array K) (j x : ℕ) (v : K) :
    (a.setIfInBounds j v).getD x 0 = if j = x ∧ j < a.size then v else a.getD x 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  rcases Nat.lt_or_ge j a.size with h2 | h2
  · by_cases h1 : j = x
    · subst h1; simp [h2]
    · simp [h1]
  · have h3 : ¬ j < a.size := by omega
    by_cases h1 : j = x
    · subst h1; simp [h3]
    · simp [h1]

theorem getD_ofFn_lt {n : ℕ} (f : Fin n → K) {i : ℕ} (h : i < n) :
    (Array.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_of_size_le (a : Array K) {i : ℕ} (h : a.size ≤ i) : a.getD i 0 = 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- Entry `y` of lane `l` of a stack of lanes of `lane` entries: `a·lane + y = b·lane + z` exactly when
`a = b` and `y = z`. -/
theorem pos_eq_iff {lane a b y z : ℕ} (hy : y < lane) (hz : z < lane) :
    a * lane + y = b * lane + z ↔ a = b ∧ y = z := by
  have hp : 0 < lane := by omega
  constructor
  · intro h
    have h1 : (a * lane + y) / lane = a := by
      rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hy, zero_add]
    have h2 : (b * lane + z) / lane = b := by
      rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hz, zero_add]
    have h3 : (a * lane + y) % lane = y := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
    have h4 : (b * lane + z) % lane = z := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
    exact ⟨by rw [← h1, h, h2], by rw [← h3, h, h4]⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## The gadget's writes (`Layout.cancelGadget`) -/

/-- One write of a gadget pair (`Layout.cancelGadget`): entry `y` of lane `b` takes lane `a`'s. -/
def gW (lane : ℕ) (st : Array K) (a b y : ℕ) : Array K :=
  st.setIfInBounds (b * lane + y) (st.getD (a * lane + y) 0)

/-- One write of the overflow lane's gadget: its entry `y` set to zero. -/
def gZ (lane : ℕ) (st : Array K) (y : ℕ) : Array K := st.setIfInBounds (32 * lane + y) 0

/-- `cancelGadget`'s nine writes, in order: pattern `0` (lane `31` from lane `0`), pattern `1` (lane
`30` from lane `1`), pattern `2` (the overflow lane `32` zeroed). -/
theorem cancelGadget_eq (L : PcsQuotient.Layout) (st : Array K) :
    L.cancelGadget st =
      gZ (2 ^ L.logLane) (gZ (2 ^ L.logLane) (gZ (2 ^ L.logLane)
        (gW (2 ^ L.logLane) (gW (2 ^ L.logLane) (gW (2 ^ L.logLane)
          (gW (2 ^ L.logLane) (gW (2 ^ L.logLane) (gW (2 ^ L.logLane) st
            0 31 (L.gadgetEntry 0 0)) 0 31 (L.gadgetEntry 0 1)) 0 31 (L.gadgetEntry 0 2))
            1 30 (L.gadgetEntry 1 0)) 1 30 (L.gadgetEntry 1 1)) 1 30 (L.gadgetEntry 1 2))
        (L.gadgetEntry 2 0)) (L.gadgetEntry 2 1)) (L.gadgetEntry 2 2) := by
  simp only [PcsQuotient.Layout.cancelGadget, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil, PcsQuotient.gadgetLanes,
    PcsQuotient.overflowLaneIndex]
  rfl

theorem cancelGadget_size (L : PcsQuotient.Layout) (st : Array K) :
    (L.cancelGadget st).size = st.size := by
  rw [cancelGadget_eq]
  simp only [gZ, gW, Array.size_setIfInBounds]

theorem gadgetEntry_eq (L : PcsQuotient.Layout) (g i : ℕ) :
    L.gadgetEntry g i = Completeness.gadgetEntryN (L.logPiece.getD 0) g i := rfl

/-- Where `gadgetFix` writes: a pair's second lane at its pattern's entries, or the overflow lane. -/
theorem gadgetFix_some {s l y : ℕ} {o : Option ℕ} (h : Completeness.gadgetFix s l y = some o) :
    ∃ g < 3, ∃ i < 3, y = Completeness.gadgetEntryN s g i ∧
      ((g = 0 ∧ l = 31 ∧ o = some 0) ∨ (g = 1 ∧ l = 30 ∧ o = some 1) ∨
        (g = 2 ∧ l = 32 ∧ o = none)) := by
  unfold Completeness.gadgetFix at h
  obtain ⟨g, hg, hgf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨i, hi, hif⟩ := List.exists_of_findSome?_eq_some hgf
  have hg3 := List.mem_range.1 hg
  have hi3 := List.mem_range.1 hi
  refine ⟨g, hg3, i, hi3, ?_⟩
  split_ifs at hif with hye
  refine ⟨hye, ?_⟩
  interval_cases g <;>
    simp only [Completeness.gadgetLanesN, Completeness.overflowLaneN] at hif <;>
    split_ifs at hif with hl <;> simp_all

/-- Where `gadgetFix` writes nothing, no pattern's lane is at its entry. -/
theorem gadgetFix_none {s l y : ℕ} (h : Completeness.gadgetFix s l y = none) {g i : ℕ} (hg : g < 3)
    (hi : i < 3) (hy : y = Completeness.gadgetEntryN s g i) :
    (g = 0 → l ≠ 31) ∧ (g = 1 → l ≠ 30) ∧ (g = 2 → l ≠ 32) := by
  unfold Completeness.gadgetFix at h
  have h1 := List.findSome?_eq_none_iff.1 h g (List.mem_range.2 hg)
  have h2 := List.findSome?_eq_none_iff.1 h1 i (List.mem_range.2 hi)
  simp only [hy, ↓reduceIte] at h2
  interval_cases g <;>
    simp only [Completeness.gadgetLanesN, Completeness.overflowLaneN] at h2 <;>
    split_ifs at h2 with hl <;> simp_all

/-- `gadgetFix` copies only lanes `0` and `1`. -/
theorem gadgetFix_src_le {s l y a : ℕ} (h : Completeness.gadgetFix s l y = some (some a)) : a ≤ 1 := by
  obtain ⟨g, -, i, -, -, hcase⟩ := gadgetFix_some h
  rcases hcase with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> simp_all

/-- **The gadget's writes, entry by entry**: in lanes of `2^ℓ` entries, with the gadget's entries
inside a lane and at least `33` lanes, `cancelGadget` leaves entry `y` of lane `l` as it is, but where
`gadgetFix` (`HiddenFill.lean`, `Table::hidden_in`'s gadget) writes: there a pair's second lane takes its
first lane's word, the overflow lane zero. -/
theorem cancelGadget_getD (L : PcsQuotient.Layout) (st : Array K)
    (hsz : 33 * 2 ^ L.logLane ≤ st.size)
    (he : ∀ g < 3, ∀ i < 3, Completeness.gadgetEntryN (L.logPiece.getD 0) g i < 2 ^ L.logLane)
    (l y : ℕ) (hy : y < 2 ^ L.logLane) :
    (L.cancelGadget st).getD (l * 2 ^ L.logLane + y) 0 =
      match Completeness.gadgetFix (L.logPiece.getD 0) l y with
      | some (some a) => st.getD (a * 2 ^ L.logLane + y) 0
      | some none => 0
      | none => st.getD (l * 2 ^ L.logLane + y) 0 := by
  have hpos : ∀ b ≤ 32, ∀ z < 2 ^ L.logLane, b * 2 ^ L.logLane + z < st.size := by
    intro b hb z hz
    calc b * 2 ^ L.logLane + z < b * 2 ^ L.logLane + 2 ^ L.logLane := by omega
      _ = (b + 1) * 2 ^ L.logLane := by ring
      _ ≤ 33 * 2 ^ L.logLane := Nat.mul_le_mul_right _ (by omega)
      _ ≤ st.size := hsz
  have s30 := hpos 30 (by norm_num)
  have s31 := hpos 31 (by norm_num)
  have s32 := hpos 32 (by norm_num)
  have e00 := he 0 (by norm_num) 0 (by norm_num)
  have e01 := he 0 (by norm_num) 1 (by norm_num)
  have e02 := he 0 (by norm_num) 2 (by norm_num)
  have e10 := he 1 (by norm_num) 0 (by norm_num)
  have e11 := he 1 (by norm_num) 1 (by norm_num)
  have e12 := he 1 (by norm_num) 2 (by norm_num)
  have e20 := he 2 (by norm_num) 0 (by norm_num)
  have e21 := he 2 (by norm_num) 1 (by norm_num)
  have e22 := he 2 (by norm_num) 2 (by norm_num)
  rw [cancelGadget_eq]
  rcases hfix : Completeness.gadgetFix (L.logPiece.getD 0) l y with _ | o
  · have hn := fun g hg i hi hyg ↦ gadgetFix_none hfix (g := g) (i := i) hg hi hyg
    have n0 : ∀ i < 3, ¬ (31 = l ∧ Completeness.gadgetEntryN (L.logPiece.getD 0) 0 i = y) :=
      fun i hi h ↦ (hn 0 (by norm_num) i hi h.2.symm).1 rfl h.1.symm
    have n1 : ∀ i < 3, ¬ (30 = l ∧ Completeness.gadgetEntryN (L.logPiece.getD 0) 1 i = y) :=
      fun i hi h ↦ (hn 1 (by norm_num) i hi h.2.symm).2.1 rfl h.1.symm
    have n2 : ∀ i < 3, ¬ (32 = l ∧ Completeness.gadgetEntryN (L.logPiece.getD 0) 2 i = y) :=
      fun i hi h ↦ (hn 2 (by norm_num) i hi h.2.symm).2.2 rfl h.1.symm
    have n00 := n0 0 (by norm_num)
    have n01 := n0 1 (by norm_num)
    have n02 := n0 2 (by norm_num)
    have n10 := n1 0 (by norm_num)
    have n11 := n1 1 (by norm_num)
    have n12 := n1 2 (by norm_num)
    have n20 := n2 0 (by norm_num)
    have n21 := n2 1 (by norm_num)
    have n22 := n2 2 (by norm_num)
    simp only [gZ, gW, getD_setIfInBounds, Array.size_setIfInBounds, gadgetEntry_eq, pos_eq_iff,
      e00, e01, e02, e10, e11, e12, e20, e21, e22, hy, s30, s31, s32, n00, n01, n02, n10, n11, n12,
      n20, n21, n22, false_and, ite_false]
  · obtain ⟨g, hg, i, hi, rfl, hcase⟩ := gadgetFix_some hfix
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      interval_cases i <;>
      simp (config := { decide := true }) only [gZ, gW, getD_setIfInBounds,
        Array.size_setIfInBounds, gadgetEntry_eq, pos_eq_iff, e00, e01, e02, e10, e11, e12, e20,
        e21, e22, s30, s31, s32, Completeness.gadgetEntry_inj, and_false, and_true, ite_true,
        ite_false]

/-! ## The honest stack is `fillNew` -/

/-- **The Statement's honest stack's word at entry `i` of lane `l`, before the gadget**
(`Layout.stackOf`, pieces of `2^s`): the first piece padding; a block lane its block's entry; the
overflow lane its held pieces, then its padding stream continued; a random lane padding. -/
def preWord (L : PcsQuotient.Layout) (s : ℕ) (entry : ℕ → K) (pad : PcsQuotient.Padding)
    (l i : ℕ) : K :=
  if i < 2 ^ s then pad l i
  else
    match L.lanes.toArray.getD l .random with
    | .block b => entry (b * 2 ^ L.logLane + i)
    | .overflow =>
      if i < (L.pieces.toArray.size + 1) * 2 ^ s then
        entry (L.pieces.toArray.getD (i / 2 ^ s - 1) 0 * 2 ^ s + i % 2 ^ s)
      else pad l (i - L.pieces.toArray.size * 2 ^ s)
    | .random => pad l i

/-- The Statement's honest stack of a hidden layout: `preWord` on every lane, then the gadget. -/
theorem stackOf_eq (L : PcsQuotient.Layout) {s : ℕ} (hs : L.logPiece = some s) (entry : ℕ → K)
    (pad : PcsQuotient.Padding) :
    L.stackOf entry pad = L.cancelGadget (Array.ofFn (n := L.lanes.toArray.size * 2 ^ L.logLane)
      fun p ↦ preWord L s entry pad (p.val / 2 ^ L.logLane) (p.val % 2 ^ L.logLane)) := by
  unfold PcsQuotient.Layout.stackOf
  rw [hs]
  rfl

/-- **The padding as `fillNew` reads it**: the overflow lane's past its held pieces is the Statement's
stream continued (`pad l (y − |pieces|·2^s)`), any other word the Statement's. -/
def padTr (L : PcsQuotient.Layout) (s : ℕ) (pad : PcsQuotient.Padding) : ℕ → ℕ → K :=
  fun l y ↦
    match L.lanes.getD l .random with
    | .overflow =>
      if (L.pieces.length + 1) * 2 ^ s ≤ y then pad l (y - L.pieces.length * 2 ^ s) else pad l y
    | _ => pad l y

/-- **Lane by lane, the Statement's words are `laneFill`'s** (`HiddenFill.lean`), with the padding
`padTr`. -/
theorem preWord_eq_laneFill (L : PcsQuotient.Layout) (s : ℕ) (entry : ℕ → K)
    (pad : PcsQuotient.Padding) {l : ℕ} (hl : l < L.lanes.length) (y : ℕ) :
    preWord L s entry pad l y = (layoutTr L).laneFill s entry (padTr L s pad) l y := by
  have hget : L.lanes.toArray.getD l .random = L.lanes[l] := by
    simp [Array.getD_eq_getD_getElem?, hl]
  have hget' : (layoutTr L).lanes[l]? = some (laneTr L.lanes[l]) := by
    simp [layoutTr, hl]
  have hgetD : L.lanes.getD l .random = L.lanes[l] := by
    simp [List.getD_eq_getElem?_getD, hl]
  have hpsize : L.pieces.toArray.size = L.pieces.length := List.size_toArray
  have hpget : ∀ k, L.pieces.toArray.getD k 0 = L.pieces.getD k 0 := fun k ↦ by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  unfold preWord WhirBridge.Layout.laneFill padTr
  rw [hget, hget', hgetD, hpsize]
  simp only [hpget, layoutTr_pieces, layoutTr_logLane]
  rcases hk : L.lanes[l] with b | _ | _
  · by_cases hy : y < 2 ^ s
    · simp [hy]
    · simp [hy, laneTr, Nat.shiftLeft_eq]
  · have hdiv : y / 2 ^ s ≤ L.pieces.length ↔ y < (L.pieces.length + 1) * 2 ^ s := by
      rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by positivity)]
    by_cases hy : y < 2 ^ s
    · have : ¬ (L.pieces.length + 1) * 2 ^ s ≤ y := by
        have : 2 ^ s ≤ (L.pieces.length + 1) * 2 ^ s := Nat.le_mul_of_pos_left _ (by omega)
        omega
      simp [hy, this]
    · by_cases hp : y < (L.pieces.length + 1) * 2 ^ s
      · simp [hy, hp, laneTr, hdiv.2 hp]
      · have h1 : ¬ y / 2 ^ s ≤ L.pieces.length := fun h ↦ hp (hdiv.1 h)
        have h2 : (L.pieces.length + 1) * 2 ^ s ≤ y := by omega
        simp [hy, hp, laneTr, h1, h2]
  · by_cases hy : y < 2 ^ s
    · simp [hy]
    · simp [hy, laneTr]

/-- A hidden layout of the shape has at least `33` lanes (its overflow lane is lane `32`). -/
theorem lanes_ge_33 {L : PcsQuotient.Layout} {s : ℕ} (hL : Completeness.NewHiddenOK (layoutTr L) s) :
    33 ≤ L.lanes.length := by
  have h := hL.overflow_lane
  have h32 : Completeness.overflowLaneN < (layoutTr L).lanes.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  have h32' : 32 < L.lanes.length := by simpa [Completeness.overflowLaneN] using h32
  omega

/-- Two columns given by their words are equal when their words are. -/
theorem column_ext_ofFn {n : ℕ} {f g : Fin (2 ^ n) → K} (h : ∀ x, f x = g x) :
    (⟨Vector.ofFn f⟩ : Column n) = ⟨Vector.ofFn g⟩ := by
  rw [funext h]

/-- **WHIR's column of the Statement's honest stack is Completeness's `fillNew`** of the same entries,
the padding reindexed (`padTr`), for every hidden layout of the shape `Layout::hidden` gives. -/
theorem colOf_stackOf (L : PcsQuotient.Layout) {s : ℕ} (hL : Completeness.NewHiddenOK (layoutTr L) s)
    (entry : ℕ → K) (pad : PcsQuotient.Padding) :
    colOf L.logN (L.stackOf entry pad) = (layoutTr L).fillNew s entry (padTr L s pad) := by
  have hs : L.logPiece = some s := hL.piece
  have h33 : 33 ≤ L.lanes.length := lanes_ge_33 hL
  have he : ∀ g < 3, ∀ i < 3,
      Completeness.gadgetEntryN (L.logPiece.getD 0) g i < 2 ^ L.logLane := by
    intro g hg i hi
    rw [hs]
    exact Completeness.gadgetEntry_lt_lane hL hg hi
  have hlane : 0 < 2 ^ L.logLane := by positivity
  rw [stackOf_eq L hs]
  set arr := Array.ofFn (n := L.lanes.toArray.size * 2 ^ L.logLane)
    fun p ↦ preWord L s entry pad (p.val / 2 ^ L.logLane) (p.val % 2 ^ L.logLane) with harr
  have hsize : arr.size = L.lanes.length * 2 ^ L.logLane := by simp [arr]
  have hget : ∀ l y, l < L.lanes.length → y < 2 ^ L.logLane →
      arr.getD (l * 2 ^ L.logLane + y) 0 = (layoutTr L).laneFill s entry (padTr L s pad) l y := by
    intro l y hl hy
    have hidx : l * 2 ^ L.logLane + y < L.lanes.toArray.size * 2 ^ L.logLane := by
      rw [List.size_toArray]
      calc l * 2 ^ L.logLane + y < l * 2 ^ L.logLane + 2 ^ L.logLane := by omega
        _ = (l + 1) * 2 ^ L.logLane := by ring
        _ ≤ L.lanes.length * 2 ^ L.logLane := Nat.mul_le_mul_right _ hl
    rw [harr, getD_ofFn_lt _ hidx]
    dsimp only
    rw [Completeness.div_piece hy, Completeness.mod_piece hy]
    exact preWord_eq_laneFill L s entry pad hl y
  unfold colOf WhirBridge.Layout.fillNew
  refine column_ext_ofFn fun x ↦ ?_
  simp only [layoutTr_logLane, layoutTr_lanes, List.length_map]
  by_cases hl : x.val / 2 ^ L.logLane < L.lanes.length
  · simp only [hl, ↓reduceIte]
    have hy : x.val % 2 ^ L.logLane < 2 ^ L.logLane := Nat.mod_lt _ hlane
    conv_lhs => rw [show x.val = x.val / 2 ^ L.logLane * 2 ^ L.logLane + x.val % 2 ^ L.logLane from
      (Nat.div_add_mod' _ _).symm]
    rw [cancelGadget_getD L arr (by rw [hsize]; exact Nat.mul_le_mul_right _ h33) he _ _ hy]
    unfold WhirBridge.Layout.wordNew
    simp only [hs, Option.getD_some]
    rcases hfix : Completeness.gadgetFix s (x.val / 2 ^ L.logLane) (x.val % 2 ^ L.logLane) with
      _ | _ | a
    · exact hget _ _ hl hy
    · rfl
    · exact hget _ _ (by have := gadgetFix_src_le hfix; omega) hy
  · simp only [hl, ↓reduceIte]
    apply getD_of_size_le
    rw [cancelGadget_size, hsize]
    have := (Nat.le_div_iff_mul_le hlane).1 (not_lt.1 hl)
    omega

/-! ## The stack claims of a hidden layout -/

/-- **Every stack claim of a hidden layout's opening holds of the Statement's honest stack**: for a
layout of the shape `Layout::hidden` gives (`NewHiddenOK`, F2's `Valid`), entries agreeing with the table
wherever the layout holds it, a table vanishing elsewhere, and true claims, whatever the padding. -/
theorem hidden_stackClaims_hold (L : PcsQuotient.Layout) {s : ℕ}
    (hL : Completeness.NewHiddenOK (layoutTr L) s) (hval : (layoutTr L).Valid) (entry T : ℕ → K)
    (hEc : ∀ t, (layoutTr L).CoveredNew s t → entry t = T t)
    (hTc : ∀ t, ¬ (layoutTr L).CoveredNew s t → T t = 0) (pad : PcsQuotient.Padding)
    (claims : List PcsQuotient.Claim)
    (hcl : ∀ c ∈ claims,
      c.point.length = L.vars ∧ Completeness.tableEvalN L.vars T c.point = c.value) :
    ∀ sc ∈ PcsQuotient.stackClaims L claims,
      StackClaim.Holds L.logN sc (colOf L.logN (L.stackOf entry pad)) := by
  have hOK : LayoutOK L := Or.inr ⟨by simpa using hL.ov_lt, lanes_ge_33 hL⟩
  have hread : ∀ t, (layoutTr L).table ((layoutTr L).fillNew s entry (padTr L s pad)) t = T t := by
    intro t
    unfold WhirBridge.Layout.table
    rw [hL.piece]
    show (layoutTr L).readNew s _ t = T t
    rw [Completeness.readNew_fillNew hL]
    split_ifs with h
    · exact hEc t h
    · exact (hTc t h).symm
  rw [colOf_stackOf L hL entry pad]
  intro sc hsc
  rw [stackClaims_eq L hOK claims] at hsc
  rcases List.mem_append.1 hsc with h | h
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    refine ((layoutTr L).holds_iff hval (claimTr c) (hcl c hc).1 _).2 ?_
    refine Eq.trans ?_ (hcl c hc).2
    unfold WhirBridge.Layout.tableEval Completeness.tableEvalN
    exact Finset.sum_congr rfl fun t _ ↦ by rw [hread t]; rfl
  · refine ((layoutTr L).extra_holds_iff hval _).2 ?_ sc h
    unfold WhirBridge.Layout.GadgetHolds
    rw [hL.piece]
    exact Completeness.gadgetValue_fillNew hL entry (padTr L s pad)

/-! ## What a hidden layout holds -/

/-- **The ends of the chunks' last pieces**: `c·2^lc + j`, `len ≤ j < ⌈len / 2^s⌉ · 2^s`, for a chunk
`(c, len)`. A hidden layout's overflow lane holds whole pieces of `2^s`, so its honest stack holds
these entries too (where the table vanishes). -/
def PastChunks (logChunk s : ℕ) (chunks : List (ℕ × ℕ)) (t : ℕ) : Prop :=
  ∃ c ∈ chunks, ∃ j, c.2 ≤ j ∧ j < (c.2 + 2 ^ s - 1) / 2 ^ s * 2 ^ s ∧ t = c.1 * 2 ^ logChunk + j

theorem block_mem_of_mem_hiddenLanes {blocks : List ℕ} {random b : ℕ}
    (h : WhirBridge.Lane.block b ∈ Completeness.hiddenLanesN blocks random) : b ∈ blocks := by
  unfold Completeness.hiddenLanesN at h
  simp only [List.mem_append, List.mem_map, List.mem_replicate, List.mem_singleton,
    WhirBridge.Lane.block.injEq, reduceCtorEq, and_false, or_false] at h
  rcases h with ⟨b', hb', rfl⟩ | ⟨b', hb', rfl⟩
  · exact List.mem_of_mem_take hb'
  · exact List.mem_of_mem_drop hb'

/-- An entry whose block (of `2^ℓ`) is one of the chunks' whole blocks is a chunk's entry. -/
theorem inChunks_of_block {logChunk ℓ : ℕ} {chunks : List (ℕ × ℕ)} (hl : ℓ ≤ logChunk) {t : ℕ}
    (h : t / 2 ^ ℓ ∈ Completeness.chunkBlocks logChunk ℓ chunks) :
    Completeness.InChunks logChunk chunks t := by
  simp only [Completeness.chunkBlocks, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨c, hc, j, hj, hb⟩ := h
  rw [Nat.shiftLeft_eq] at hb
  rw [Nat.shiftRight_eq_div_pow] at hj
  refine ⟨c, hc, j * 2 ^ ℓ + t % 2 ^ ℓ, ?_, ?_⟩
  · have h1 : t % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ (by positivity)
    have h2 : (j + 1) * 2 ^ ℓ ≤ c.2 / 2 ^ ℓ * 2 ^ ℓ := Nat.mul_le_mul_right _ hj
    have h3 : c.2 / 2 ^ ℓ * 2 ^ ℓ ≤ c.2 := Nat.div_mul_le_self _ _
    rw [add_mul, one_mul] at h2
    omega
  · have e1 : 2 ^ logChunk = 2 ^ (logChunk - ℓ) * 2 ^ ℓ := by
      rw [← pow_add, Nat.sub_add_cancel hl]
    have h4 := Nat.div_add_mod' t (2 ^ ℓ)
    rw [← hb] at h4
    rw [e1]
    calc t = (c.1 * 2 ^ (logChunk - ℓ) + j) * 2 ^ ℓ + t % 2 ^ ℓ := h4.symm
      _ = c.1 * (2 ^ (logChunk - ℓ) * 2 ^ ℓ) + (j * 2 ^ ℓ + t % 2 ^ ℓ) := by ring

/-- An entry whose piece (of `2^s`) is one of the chunks' tail pieces is a chunk's entry, or past a
chunk's end in its last piece. -/
theorem pastOrIn_of_tail {logChunk ℓ s : ℕ} {chunks : List (ℕ × ℕ)} (hs : s ≤ ℓ) (hl : ℓ ≤ logChunk)
    {t : ℕ} (h : t / 2 ^ s ∈ Completeness.chunkTails logChunk ℓ s chunks) :
    Completeness.InChunks logChunk chunks t ∨ PastChunks logChunk s chunks t := by
  simp only [Completeness.chunkTails, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨c, hc, j, hj, hp⟩ := h
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at hj hp
  have hWle : c.2 / 2 ^ ℓ * 2 ^ ℓ ≤ c.2 := Nat.div_mul_le_self _ _
  generalize hW : c.2 / 2 ^ ℓ = W at hj hp hWle
  have hB : 0 < 2 ^ s := by positivity
  have eℓ : 2 ^ ℓ = 2 ^ (ℓ - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have elc : 2 ^ logChunk = 2 ^ (logChunk - ℓ) * (2 ^ (ℓ - s) * 2 ^ s) := by
    rw [← eℓ, ← pow_add, Nat.sub_add_cancel hl]
  have ho : t % 2 ^ s < 2 ^ s := Nat.mod_lt _ hB
  have ht : t = c.1 * 2 ^ logChunk + (W * 2 ^ ℓ + j * 2 ^ s + t % 2 ^ s) := by
    have h4 := Nat.div_add_mod' t (2 ^ s)
    rw [← hp] at h4
    rw [elc, eℓ]
    calc t = ((c.1 * 2 ^ (logChunk - ℓ) + W) * 2 ^ (ℓ - s) + j) * 2 ^ s + t % 2 ^ s := h4.symm
      _ = _ := by ring
  by_cases hJ : W * 2 ^ ℓ + j * 2 ^ s + t % 2 ^ s < c.2
  · exact Or.inl ⟨c, hc, _, hJ, ht⟩
  · refine Or.inr ⟨c, hc, _, not_lt.1 hJ, ?_, ht⟩
    -- `⌈len / 2^s⌉ = W·2^(ℓ−s) + ⌈tail / 2^s⌉`, the whole blocks a multiple of `2^s`.
    have hsplit : c.2 + 2 ^ s - 1 =
        (c.2 - W * 2 ^ ℓ + 2 ^ s - 1) + W * 2 ^ (ℓ - s) * 2 ^ s := by
      have : W * 2 ^ ℓ = W * 2 ^ (ℓ - s) * 2 ^ s := by rw [eℓ, mul_assoc]
      omega
    rw [hsplit, Nat.add_mul_div_right _ _ hB]
    have h5 : (j + 1) * 2 ^ s ≤ (c.2 - W * 2 ^ ℓ + 2 ^ s - 1) / 2 ^ s * 2 ^ s :=
      Nat.mul_le_mul_right _ hj
    rw [add_mul, one_mul] at h5
    have h6 : W * 2 ^ ℓ = W * 2 ^ (ℓ - s) * 2 ^ s := by rw [eℓ, mul_assoc]
    rw [add_mul, ← h6]
    omega

/-- **What `Layout::hidden` holds** (the converse of `coveredNew_hiddenNew`): an entry its layout covers
is a chunk's entry, or past a chunk's end in that chunk's last piece. -/
theorem coveredNew_hiddenNew_inv {vars logChunk logN random s : ℕ} {chunks : List (ℕ × ℕ)}
    (hs : s ≤ logN - WhirBridge.laneFold) (hl : logN - WhirBridge.laneFold ≤ logChunk) {t : ℕ}
    (h : (WhirBridge.Layout.hiddenNew vars logChunk logN chunks random s).CoveredNew s t) :
    Completeness.InChunks logChunk chunks t ∨ PastChunks logChunk s chunks t := by
  obtain ⟨-, hp | hb⟩ := h
  · change t >>> s ∈ (Completeness.laneBlocks (Completeness.hiddenLanesN
        (Completeness.chunkBlocks logChunk (logN - WhirBridge.laneFold) chunks) random)).map
        (· <<< (logN - WhirBridge.laneFold - s)) ++
      Completeness.chunkTails logChunk (logN - WhirBridge.laneFold) s chunks at hp
    rw [Nat.shiftRight_eq_div_pow] at hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨b, hb, hbe⟩ := List.mem_map.1 hp
      left
      apply inChunks_of_block hl
      have hb' := block_mem_of_mem_hiddenLanes (Completeness.mem_laneBlocks.1 hb)
      have e : 2 ^ (logN - WhirBridge.laneFold) = 2 ^ s * 2 ^ (logN - WhirBridge.laneFold - s) := by
        rw [← pow_add, Nat.add_sub_cancel' hs]
      rw [e, ← Nat.div_div_eq_div_mul, ← hbe, Nat.shiftLeft_eq, Nat.mul_div_cancel _ (by positivity)]
      exact hb'
    · exact pastOrIn_of_tail hs hl hp
  · change WhirBridge.Lane.block (t >>> s >>> (logN - WhirBridge.laneFold - s)) ∈
      Completeness.hiddenLanesN
        (Completeness.chunkBlocks logChunk (logN - WhirBridge.laneFold) chunks) random at hb
    left
    apply inChunks_of_block hl
    have hb' := block_mem_of_mem_hiddenLanes hb
    rwa [← Nat.shiftRight_add, Nat.add_sub_cancel' hs, Nat.shiftRight_eq_div_pow] at hb'

/-! ## The deployed layouts -/

theorem layoutTr_witness22 :
    layoutTr (PcsQuotient.witnessLayout 22) = Completeness.witnessLayoutNew WhirBridge.logRows :=
  (layoutTr_witnessLayout 22).trans Completeness.witnessLayout_eq

theorem layoutTr_quotient22 :
    layoutTr (PcsQuotient.quotientLayout 22) = Completeness.quotientLayoutNew WhirBridge.logRows :=
  (layoutTr_quotientLayout 22).trans Completeness.quotientLayout_eq

/-- **The witness opening's stack claims hold of the Statement's honest stack** (`witness_layout(22)`,
hidden): for entries `entry` equal to the table `T` on its chunks (`hE`) and zero past its last piece's
held entries (`hZ`: entries `2^24 + 16 … 2^24 + 255`), a table vanishing off its chunks (`hT`), and true
claims of `25` coordinates, whatever the padding. -/
theorem witness_stackClaims_hold (entry T : ℕ → K)
    (hT : ∀ i, ¬ Completeness.witnessHeld i → T i = 0)
    (hE : ∀ i, Completeness.witnessHeld i → entry i = T i)
    (hZ : ∀ i, PastChunks 24 8 [(0, 2 ^ 24), (1, 16)] i → entry i = 0)
    (pad : PcsQuotient.Padding) (claims : List PcsQuotient.Claim)
    (hcl : ∀ c ∈ claims, c.point.length = 25 ∧ Completeness.tableEvalN 25 T c.point = c.value) :
    ∀ sc ∈ PcsQuotient.stackClaims (PcsQuotient.witnessLayout 22) claims,
      StackClaim.Holds 25 sc (colOf 25 ((PcsQuotient.witnessLayout 22).stackOf entry pad)) := by
  have hL : Completeness.NewHiddenOK (layoutTr (PcsQuotient.witnessLayout 22)) 8 := by
    rw [layoutTr_witness22]
    exact Completeness.deployed_newHiddenOK.1
  have hval : (layoutTr (PcsQuotient.witnessLayout 22)).Valid := by
    rw [layoutTr_witnessLayout]
    exact (WhirBridge.layouts_valid 22 (by decide) (by decide)).1
  refine hidden_stackClaims_hold (PcsQuotient.witnessLayout 22) hL hval entry T (fun t ht ↦ ?_)
    (fun t ht ↦ ?_) pad claims hcl
  · rw [layoutTr_witness22] at ht
    by_cases hh : Completeness.witnessHeld t
    · exact hE t hh
    · rcases coveredNew_hiddenNew_inv (by decide) (by decide) ht with h | h
      · exact absurd h hh
      · rw [hZ t h, hT t hh]
  · refine hT t fun hh ↦ ht ?_
    rw [layoutTr_witness22]
    obtain ⟨c, hc, j, hj, rfl⟩ := hh
    exact Completeness.witness_covered hc hj

/-- **The quotient opening's stack claims hold of the Statement's honest stack**
(`quotient_layout(22)`, hidden): for entries `entry` equal to the table `T` on its chunks (`hE`) and zero
past the chunks' ends in their last pieces (`hZ`: the spills' and the gate quotient's), a table vanishing
off its chunks (`hT`), and true claims of `30` coordinates, whatever the padding. -/
theorem quotient_stackClaims_hold (entry T : ℕ → K)
    (hT : ∀ i, ¬ Completeness.quotientHeld i → T i = 0)
    (hE : ∀ i, Completeness.quotientHeld i → entry i = T i)
    (hZ : ∀ i, PastChunks 24 8 (PcsQuotient.quotientChunks 24) i → entry i = 0)
    (pad : PcsQuotient.Padding) (claims : List PcsQuotient.Claim)
    (hcl : ∀ c ∈ claims, c.point.length = 30 ∧ Completeness.tableEvalN 30 T c.point = c.value) :
    ∀ sc ∈ PcsQuotient.stackClaims (PcsQuotient.quotientLayout 22) claims,
      StackClaim.Holds 28 sc (colOf 28 ((PcsQuotient.quotientLayout 22).stackOf entry pad)) := by
  have hL : Completeness.NewHiddenOK (layoutTr (PcsQuotient.quotientLayout 22)) 8 := by
    rw [layoutTr_quotient22]
    exact Completeness.deployed_newHiddenOK.2
  have hval : (layoutTr (PcsQuotient.quotientLayout 22)).Valid := by
    rw [layoutTr_quotientLayout]
    exact (WhirBridge.layouts_valid 22 (by decide) (by decide)).2.2
  refine hidden_stackClaims_hold (PcsQuotient.quotientLayout 22) hL hval entry T (fun t ht ↦ ?_)
    (fun t ht ↦ ?_) pad claims hcl
  · rw [layoutTr_quotient22] at ht
    by_cases hh : Completeness.quotientHeld t
    · exact hE t hh
    · rcases coveredNew_hiddenNew_inv (by decide) (by decide) ht with h | h
      · exact absurd h hh
      · rw [hZ t h, hT t hh]
  · refine hT t fun hh ↦ ht ?_
    rw [layoutTr_quotient22]
    obtain ⟨c, hc, j, hj, rfl⟩ := hh
    exact Completeness.quotient_covered hc hj

set_option linter.unusedVariables false in
/-- **The wiring opening's stack claims hold of the table itself** (`wiring_layout(22)`, public: lane
`l` holds block `l`, so the stack is the table): for true claims of `24` coordinates on the table
`T` (its entries read with `getD`). The size `hT` is not needed: the column and the claims both read
`T` with `getD` below `2^24`; it is kept for the caller's interface. -/
theorem wiring_stackClaims_hold (T : Array K) (hT : T.size = 2 ^ 24)
    (claims : List PcsQuotient.Claim)
    (hcl : ∀ c ∈ claims, c.point.length = 24 ∧
      Completeness.tableEvalN 24 (fun i ↦ T.getD i 0) c.point = c.value) :
    ∀ sc ∈ PcsQuotient.stackClaims (PcsQuotient.wiringLayout 22) claims,
      StackClaim.Holds 24 sc (colOf 24 T) := by
  obtain ⟨-, -, hl, hlanes, hp⟩ := Completeness.wL_shape
  have hOK := (layoutOK_layouts 22 (by decide) (by decide)).2.1
  have hval : Completeness.wL.Valid := (WhirBridge.layouts_valid 22 (by decide) (by decide)).2.1
  have hq : colOf 24 T = Completeness.fillPublic Completeness.wL (fun i ↦ T.getD i 0) := by
    unfold colOf Completeness.fillPublic
    refine column_ext_ofFn fun x ↦ ?_
    have hx : x.val < 2 ^ 24 := x.isLt
    have hdiv : x.val / 2 ^ 18 < 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc x.val < 2 ^ 24 := hx
        _ = 64 * 2 ^ 18 := by norm_num
    rw [hl, hlanes]
    simp only [List.length_map, List.length_range, hdiv, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range, Option.map_some, Option.getD_some,
      WhirBridge.Lane.blockD]
    rw [Nat.div_add_mod']
  intro sc hsc
  rw [stackClaims_eq _ hOK claims, layoutTr_wiringLayout] at hsc
  rcases List.mem_append.1 hsc with h | h
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    rw [hq]
    refine (Completeness.wL.holds_iff hval (claimTr c) (hcl c hc).1 _).2 ?_
    rw [Completeness.wiring_tableEval]
    exact (hcl c hc).2
  · change sc ∈ Completeness.wL.extra at h
    rw [WhirBridge.Layout.extra_of_none hp] at h
    exact absurd h List.not_mem_nil

set_option linter.unusedVariables false in
/-- **Every stack claim of the three openings is multilinear** (`IsMultilinearFn`, what mumbai's
completeness of the opening asks of each): the weights are multiaffine (F2's
`Stacking.isMultiaffine_claims`, through Bridge-Defs' `stackClaims_eq`), whatever the claims' points:
`hlen` is not needed, and is kept for the caller's interface. -/
theorem stackClaims_multilinear (L : PcsQuotient.Layout)
    (hL : L = PcsQuotient.witnessLayout 22 ∨ L = PcsQuotient.wiringLayout 22 ∨
      L = PcsQuotient.quotientLayout 22)
    (claims : List PcsQuotient.Claim) (hlen : ∀ c ∈ claims, c.point.length = L.vars) :
    ∀ sc ∈ PcsQuotient.stackClaims L claims, IsMultilinearFn L.logN sc.1 := by
  have hOK : LayoutOK L := by
    obtain ⟨h1, h2, h3⟩ := layoutOK_layouts 22 (by decide) (by decide)
    rcases hL with rfl | rfl | rfl
    exacts [h1, h2, h3]
  intro sc hsc
  rw [stackClaims_eq L hOK claims] at hsc
  exact Completeness.isMultilinearFn_of_isMultiaffine
    ((layoutTr L).stacking.isMultiaffine_claims (claims.map claimTr) sc hsc)

end E2ECompleteness

/-- info: 'E2ECompleteness.colOf_stackOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.colOf_stackOf

/--
info: 'E2ECompleteness.hidden_stackClaims_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms E2ECompleteness.hidden_stackClaims_hold

/--
info: 'E2ECompleteness.coveredNew_hiddenNew_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms E2ECompleteness.coveredNew_hiddenNew_inv

/--
info: 'E2ECompleteness.witness_stackClaims_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms E2ECompleteness.witness_stackClaims_hold

/--
info: 'E2ECompleteness.quotient_stackClaims_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms E2ECompleteness.quotient_stackClaims_hold

/--
info: 'E2ECompleteness.wiring_stackClaims_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms E2ECompleteness.wiring_stackClaims_hold

/--
info: 'E2ECompleteness.stackClaims_multilinear' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms E2ECompleteness.stackClaims_multilinear
