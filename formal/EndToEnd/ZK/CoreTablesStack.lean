-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoreSpec
import E2ECompleteness.ProverCircuit
import E2ECompleteness.ProverQuotient
import E2ECompleteness.ProverStaged
import E2ECompleteness.ProverFacts

/-!
# The stacks (`StackW`, `StackQ`)

The joint model's stack of a secret table is `stackD (place t) + stackR r`, which is the word
`Table::hidden` writes (`Hiding.Deployed.Layout.hiddenWord_eq`): the fill `fillWord` (the first
piece random, a block lane's block, the overflow lane's held pieces then random, a random lane
random) and the gadget's nine entries (lanes `31`, `30` copying lanes `0`, `1`, the overflow lane
zero). The statement's prover writes `Layout.stackOf`: `preWord` and `cancelGadget`, which
`E2ECompleteness` reads entry by entry (`stackOf_eq`, `cancelGadget_getD`, `gadgetFix`). Here:

* `gadgetFix_eight`, `hiddenWord_eight`: both gadgets, as the same three cases;
* **`stack_eq`**: for two layouts with the same lanes (`laneTrD`), lane size and pieces of `2^8`,
  the model's word is the statement's array entry wherever the fills agree; **`fill_eq`**: the fills
  agree when the statement's entries are the model's table where a lane holds it (`role`) and its
  padding is the model's randomness (the overflow lane's stream continued past its held pieces);
* the deployed layouts are the statement's (`lanes_W_tr`, `pieces_W_eq`, `lanes_Q_tr`,
  `pieces_Q_eq`, by the kernel on the short lists);
* the witness table: the statement's entries are the honest table everywhere
  (`E2ECompleteness.ProverTables.witness_table`, `entry_W`), its padding the model's randomness
  (`decodeCoins_eD_pad₁`); **`stackW`**, and the array's size `size_wStackD`.

The quotient table (`stackQ`) is `CoreTablesQuot.lean`'s.
-/

open Polynomial QuotientSecurity
open LeanVM.Parameters
open PcsQuotient.Domain
open QuotientZk.Instance
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## The layouts -/

/-- A lane of the model's layout as the statement's. -/
def laneTrD : Hiding.Deployed.Lane → PcsQuotient.Lane
  | .block b => .block b
  | .overflow => .overflow
  | .random => .random

/-- **The model's witness layout is the statement's**: its lanes. -/
theorem lanes_W_tr : Lw.lanes.map laneTrD = (PcsQuotient.witnessLayout logRows).lanes := by
  decide +kernel

/-- Its pieces. -/
theorem pieces_W_eq : Lw.pieces = (PcsQuotient.witnessLayout logRows).pieces := by
  decide +kernel

/-- **The model's quotient layout is the statement's**: its lanes. -/
theorem lanes_Q_tr : Lq.lanes.map laneTrD = (PcsQuotient.quotientLayout logRows).lanes := by
  decide +kernel

/-- Its pieces. -/
theorem pieces_Q_eq : Lq.pieces = (PcsQuotient.quotientLayout logRows).pieces := by
  decide +kernel

theorem piecesLen_W : Lw.pieces.length = 33 :=
  (Hiding.Deployed.deployed_shape 22 (by norm_num) (by norm_num)).2.2.1

theorem piecesLen_Q : Lq.pieces.length = 167 :=
  (Hiding.Deployed.deployed_shape 22 (by norm_num) (by norm_num)).2.2.2.1

/-! ## The gadgets -/

theorem gadgetEntryN_eight (g i : ℕ) : Completeness.gadgetEntryN 8 g i = 247 + 3 * g + i := by
  simp [Completeness.gadgetEntryN, Completeness.gadgetN]

/-- **The statement's gadget** (`gadgetFix`, pieces of `2^8`): lane `31` copies lane `0` at
`247 .. 250`, lane `30` lane `1` at `250 .. 253`, the overflow lane zero at `253 .. 256`. -/
theorem gadgetFix_eight (l y : ℕ) :
    Completeness.gadgetFix 8 l y =
      if 247 ≤ y ∧ y < 250 ∧ l = 31 then some (some 0)
      else if 250 ≤ y ∧ y < 253 ∧ l = 30 then some (some 1)
      else if 253 ≤ y ∧ y < 256 ∧ l = 32 then some none else none := by
  rcases h : Completeness.gadgetFix 8 l y with _ | o
  · have hn := fun g hg i hi hyg => E2ECompleteness.gadgetFix_none h (g := g) (i := i) hg hi hyg
    split_ifs with h1 h2 h3
    · exact absurd h1.2.2 ((hn 0 (by norm_num) (y - 247) (by omega)
        (by rw [gadgetEntryN_eight]; omega)).1 rfl)
    · exact absurd h2.2.2 ((hn 1 (by norm_num) (y - 250) (by omega)
        (by rw [gadgetEntryN_eight]; omega)).2.1 rfl)
    · exact absurd h3.2.2 ((hn 2 (by norm_num) (y - 253) (by omega)
        (by rw [gadgetEntryN_eight]; omega)).2.2 rfl)
    · rfl
  · obtain ⟨g, hg, i, hi, hy, hcase⟩ := E2ECompleteness.gadgetFix_some h
    rw [gadgetEntryN_eight] at hy
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

/-- **The model's gadget** (`hiddenWord`), as the same three cases. -/
theorem hiddenWord_eight {L : Hiding.Deployed.Layout} (h : L.OK) (t : ℕ → K) (rnd : ℕ → ℕ → K)
    (l y : ℕ) :
    L.hiddenWord t rnd l y =
      if 247 ≤ y ∧ y < 250 ∧ l = 31 then L.fillWord t rnd 0 y
      else if 250 ≤ y ∧ y < 253 ∧ l = 30 then L.fillWord t rnd 1 y
      else if 253 ≤ y ∧ y < 256 ∧ l = 32 then 0 else L.fillWord t rnd l y := by
  unfold Hiding.Deployed.Layout.hiddenWord
  rw [h.piece]
  have e1 : (2 : ℕ) ^ Hiding.Deployed.logPieceD - Hiding.Deployed.gadgetD = 247 := rfl
  have e2 : (2 : ℕ) ^ Hiding.Deployed.logPieceD = 256 := rfl
  rw [e1, e2]
  by_cases hy : 247 ≤ y ∧ y < 256
  · rw [ite_eq_left hy]
    have h3 : (y - 247) / 3 = 0 ∨ (y - 247) / 3 = 1 ∨ (y - 247) / 3 = 2 := by omega
    rcases h3 with h3 | h3 | h3 <;> rw [h3] <;>
      simp only [Hiding.Deployed.gadgetLanes, Hiding.Deployed.overflowLane] <;>
      split_ifs <;> first | rfl | omega
  · rw [ite_eq_right hy, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The stacks of two layouts -/

/-- **The model's word is the statement's array entry**, for two layouts with the same lanes,
lane size and pieces of `2^8`, wherever the fills agree (`hfill`). -/
theorem stack_eq {DL : Hiding.Deployed.Layout} (hDL : DL.OK) {SL : PcsQuotient.Layout}
    (hlanes : DL.lanes.map laneTrD = SL.lanes) (hlog : SL.logLane = DL.logLane)
    (hpiece : SL.logPiece = some 8) (t entry : ℕ → K) (rnd : ℕ → ℕ → K)
    (pad : PcsQuotient.Padding)
    (hfill : ∀ a < DL.lanes.length, ∀ y < 2 ^ DL.logLane,
      DL.fillWord t rnd a y = E2ECompleteness.preWord SL 8 entry pad a y)
    {l y : ℕ} (hl : l < DL.lanes.length) (hy : y < 2 ^ DL.logLane) :
    DL.hiddenWord t rnd l y = (SL.stackOf entry pad).getD (l * 2 ^ DL.logLane + y) 0 := by
  have hlen : SL.lanes.length = DL.lanes.length := by rw [← hlanes, List.length_map]
  have h40 := hDL.lanes_ge
  have hlane8 : 2 ^ 8 < 2 ^ DL.logLane := Nat.pow_lt_pow_right (by norm_num) hDL.lane
  have hy' : y < 2 ^ SL.logLane := by rw [hlog]; exact hy
  have harr : ∀ a < DL.lanes.length,
      (Array.ofFn (n := SL.lanes.toArray.size * 2 ^ SL.logLane) fun p =>
        E2ECompleteness.preWord SL 8 entry pad (p.val / 2 ^ SL.logLane)
          (p.val % 2 ^ SL.logLane)).getD (a * 2 ^ SL.logLane + y) 0 =
        E2ECompleteness.preWord SL 8 entry pad a y := by
    intro a ha
    have hidx : a * 2 ^ SL.logLane + y < SL.lanes.toArray.size * 2 ^ SL.logLane := by
      rw [List.size_toArray, hlen]
      exact idx_lt' ha hy'
    rw [E2ECompleteness.getD_ofFn_lt _ hidx]
    simp only [div_idx hy', mod_idx hy']
  have hsz : 33 * 2 ^ SL.logLane ≤ (Array.ofFn (n := SL.lanes.toArray.size * 2 ^ SL.logLane)
      fun p => E2ECompleteness.preWord SL 8 entry pad (p.val / 2 ^ SL.logLane)
        (p.val % 2 ^ SL.logLane)).size := by
    rw [Array.size_ofFn, List.size_toArray, hlen]
    exact Nat.mul_le_mul_right _ (by omega)
  have he : ∀ g < 3, ∀ i < 3,
      Completeness.gadgetEntryN (SL.logPiece.getD 0) g i < 2 ^ SL.logLane := by
    intro g hg i hi
    rw [hpiece, Option.getD_some, gadgetEntryN_eight, hlog]
    have : (2 : ℕ) ^ 8 = 256 := rfl
    omega
  rw [E2ECompleteness.stackOf_eq SL hpiece, ← hlog,
    E2ECompleteness.cancelGadget_getD SL _ hsz he l y hy', hpiece, Option.getD_some,
    gadgetFix_eight, hiddenWord_eight hDL]
  split_ifs with h1 h2 h3
  · dsimp only
    rw [harr 0 (by omega), hfill 0 (by omega) y hy]
  · dsimp only
    rw [harr 1 (by omega), hfill 1 (by omega) y hy]
  · rfl
  · dsimp only
    rw [harr l hl, hfill l hl y hy]

/-- **The fills agree** when the statement's entries are the model's table on the entries a lane
holds (`hE`), and its padding the model's randomness: as is (`hpad`), but on the overflow lane past
its held pieces, where the statement's stream continues (`hov`). -/
theorem fill_eq {DL : Hiding.Deployed.Layout} (hDL : DL.OK) {SL : PcsQuotient.Layout}
    (hlanes : DL.lanes.map laneTrD = SL.lanes) (hpieces : DL.pieces = SL.pieces)
    (hlog : SL.logLane = DL.logLane) (t entry : ℕ → K) (rnd : ℕ → ℕ → K)
    (pad : PcsQuotient.Padding)
    (hE : ∀ a y i, a < DL.lanes.length → y < 2 ^ DL.logLane →
      LayoutClaims.role DL a y = some i → entry i = t i)
    (hpad : ∀ a < DL.lanes.length, ∀ y < 2 ^ DL.logLane, ¬ (a = 32 ∧ 256 ≤ y) →
      pad a y = rnd a y)
    (hov : ∀ y < 2 ^ DL.logLane, (DL.pieces.length + 1) * 256 ≤ y →
      pad 32 (y - DL.pieces.length * 256) = rnd 32 y)
    {a y : ℕ} (ha : a < DL.lanes.length) (hy : y < 2 ^ DL.logLane) :
    DL.fillWord t rnd a y = E2ECompleteness.preWord SL 8 entry pad a y := by
  have hp : DL.logPiece = 8 := hDL.piece
  have e8 : (2 : ℕ) ^ 8 = 256 := rfl
  obtain ⟨k, hk⟩ : ∃ k, DL.lanes[a]? = some k := ⟨DL.lanes[a], List.getElem?_eq_getElem ha⟩
  have hsl : SL.lanes.toArray.getD a .random = laneTrD k := by
    rw [← hlanes]
    simp [Array.getD_eq_getD_getElem?, hk]
  have hps : SL.pieces.toArray.size = DL.pieces.length := by rw [List.size_toArray, hpieces]
  have hpg : ∀ j, SL.pieces.toArray.getD j 0 = DL.pieces.getD j 0 := fun j => by
    rw [hpieces]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  unfold Hiding.Deployed.Layout.fillWord E2ECompleteness.preWord
  rw [hp, hk, hsl, hps, hlog, hpg, e8]
  by_cases h8 : y < 256
  · rw [ite_eq_left h8, ite_eq_left h8]
    exact (hpad a ha y hy (by omega)).symm
  rw [ite_eq_right h8, ite_eq_right h8]
  rcases k with b | _ | _
  · -- a block lane
    have hr : LayoutClaims.role DL a y = some ((b <<< DL.logLane) + y) := by
      rw [LayoutClaims.role_block_lane hk, hp, e8, ite_eq_right (by omega)]
    show t ((b <<< DL.logLane) + y) = entry (b * 2 ^ DL.logLane + y)
    rw [← hE a y _ ha hy hr, Nat.shiftLeft_eq]
  · -- the overflow lane
    have ha32 : a = 32 := hDL.ov_unique a ha hk
    show (if y < (DL.pieces.length + 1) * 256 then
        t (DL.pieces.getD (y / 256 - 1) 0 * 256 + y % 256) else rnd a y) =
      (if y < (DL.pieces.length + 1) * 256 then
        entry (DL.pieces.getD (y / 256 - 1) 0 * 256 + y % 256)
      else pad a (y - DL.pieces.length * 256))
    by_cases hh : y < (DL.pieces.length + 1) * 256
    · rw [ite_eq_left hh, ite_eq_left hh]
      have hr : LayoutClaims.role DL a y =
          some (DL.pieces.getD (y / 256 - 1) 0 * 256 + y % 256) := by
        rw [LayoutClaims.role_ov_lane hk, hp, e8, ite_eq_left ⟨by omega, by omega⟩]
      exact (hE a y _ ha hy hr).symm
    · rw [ite_eq_right hh, ite_eq_right hh, ha32]
      exact (hov y hy (by omega)).symm
  · -- a random lane
    have ha32 : a ≠ 32 := by
      rintro rfl
      have h32 : DL.lanes[32]? = some .overflow := hDL.at_ov
      rw [h32] at hk
      simp at hk
    exact (hpad a ha y hy (by omega)).symm

/-- The model's randomness by numbers (zero off the stack). -/
noncomputable def rndOf {n m : ℕ} (r : Fin n → Fin m → K) : ℕ → ℕ → K :=
  fun l y => if h : l < n ∧ y < m then r ⟨l, h.1⟩ ⟨y, h.2⟩ else 0

theorem fin2_congr {n m : ℕ} (r : Fin n → Fin m → K) {a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (h1 : a < n) (h2 : b < m) (h1' : a' < n) (h2' : b' < m) :
    r ⟨a, h1⟩ ⟨b, h2⟩ = r ⟨a', h1'⟩ ⟨b', h2'⟩ := by
  subst ha hb
  rfl

theorem rndOf_fin {n m : ℕ} (r : Fin n → Fin m → K) :
    (fun (l : Fin n) (y : Fin m) => rndOf r l y) = r := by
  funext l y
  simp [rndOf, l.isLt, y.isLt]

/-! ## The witness table -/

theorem cellsKD_eq (w : Secret) :
    cellsKD w = Completeness.cellBitsK Completeness.deployedMembership (E2ECompleteness.secretOf w) := by
  funext b
  rw [cellsKD, E2ECompleteness.ProverCircuit.secretTr_eq]
  rfl

/-- **The statement's witness entries are the honest table**, everywhere. -/
theorem entry_W (w : Secret) (m : Masks) (i : ℕ) :
    E2ECompleteness.witnessEntry (2 ^ cellVars logRows) (wHatD w) (maskEntries m) i =
      natTableD (witTableD w m) i := by
  have h := E2ECompleteness.ProverTables.witness_table E2ECompleteness.constants
    (Completeness.cellBitsK Completeness.deployedMembership (E2ECompleteness.secretOf w))
    (E2ECompleteness.cellsOf w) (E2ECompleteness.cellsOf_size w)
    (E2ECompleteness.ProverCircuit.cells_getD w) m i
  rw [witTableD, cellsKD_eq]
  exact h

/-- **The witness stacks agree.** -/
theorem stackW : StackW := by
  intro w s l y
  obtain ⟨l, hl⟩ := l
  obtain ⟨y, hy⟩ := y
  have hM : stackWm w s ⟨l, hl⟩ ⟨y, hy⟩ =
      Lw.hiddenWord (natTableD (witTableD w s.1)) (rndOf s.2.1) l y := by
    refine Eq.trans ?_
      (Hiding.Deployed.Layout.hiddenWord_eq okW _ (rndOf s.2.1) ⟨l, hl⟩ ⟨y, hy⟩).symm
    exact congrArg (fun r => ((Lw.toGadget okW).stackD (TWD w s.1) +
      (Lw.toGadget okW).stackR r) ⟨l, hl⟩ ⟨y, hy⟩) (rndOf_fin s.2.1).symm
  rw [hM]
  show _ = (wStackD w (decodeCoins (eD s))).getD (l * 2 ^ 19 + y) 0
  rw [wStackD, E2ECompleteness.witnessStack_eq, decodeCoins_eD_masks]
  have e19 : (2 : ℕ) ^ 19 = 2 ^ Lw.logLane := by rw [logLane_W]
  rw [e19]
  have hlog : (PcsQuotient.witnessLayout logRows).logLane = Lw.logLane := by
    rw [logLane_SW, logLane_W]
  refine stack_eq okW lanes_W_tr hlog logPiece_SW _ _ _ _ (fun a ha y' hy' => ?_) hl hy
  refine fill_eq okW lanes_W_tr pieces_W_eq hlog _ _ _ _ (fun _ _ i _ _ _ => entry_W w s.1 i)
    ?_ ?_ ha hy'
  · intro a ha y hy hn
    have ha' : a < 40 := by rwa [lanes_W] at ha
    have hy'' : y < 2 ^ 19 := by rwa [logLane_W] at hy
    rw [decodeCoins_eD_pad₁ s a y ha' hy'', rndOf, dite_eq_left ⟨ha, hy⟩]
    refine fin2_congr s.2.1 rfl ?_ _ _ _ _
    unfold padSrc
    rw [ite_eq_right hn]
  · intro y hy hge
    have hy'' : y < 2 ^ 19 := by rwa [logLane_W] at hy
    rw [piecesLen_W] at hge ⊢
    rw [decodeCoins_eD_pad₁ s 32 (y - 33 * 256) (by norm_num) (by omega), rndOf,
      dite_eq_left ⟨by rw [lanes_W]; norm_num, hy⟩]
    refine fin2_congr s.2.1 rfl ?_ _ _ _ _
    unfold padSrc
    rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left (by norm_num; omega)]
    omega

/-- **The statement's witness stack has `40` lanes of `2^19`.** -/
theorem size_wStackD (w : Secret) (c : Masks × Padding × Padding) :
    (wStackD w c).size = 40 * 2 ^ 19 := by
  rw [wStackD, E2ECompleteness.witnessStack_eq, E2ECompleteness.stackOf_eq _ logPiece_SW,
    E2ECompleteness.cancelGadget_size, Array.size_ofFn, List.size_toArray, lanes_SW, logLane_SW]

end PcsQuotient.EndToEnd.Core
