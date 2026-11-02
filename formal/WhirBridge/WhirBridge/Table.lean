/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

What a claim of `crates/quotient/src/opening.rs` says of a stack: its multilinear claim on the
*table* the stack stands for. Uses lemmas of leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM,
commit 6175f1a0, MIT OR Apache-2.0) on cube points (`boolPoint_add`, `eqEval_append`,
`eqEval_comm`, `eqEval_boolPoint_boolPoint`, `selectorPoint_eq_boolPoint`).
-/
import WhirBridge.Sound
import LeanVM.Protocol.EndToEnd.Complete.Gkr
import LeanVM.Protocol.EndToEnd.Front.LayoutStack
import LeanVM.Protocol.EndToEnd.Front.LayoutArith

/-!
# The claims are claims on the table

mumbai's doom (`StackedPre`) and its extractor speak of *stacks*: a candidate `q` of the level-0
word satisfies a stack claim `(w, v)` when `Σ_x w(x) q(x) = v` over the stack's cube
(`StackClaim.Holds`). A public layout (`Layout::new`) commits a table of `vars` variables as the
stack of its blocks: lane `l` holds the table's block `blocks[l]` of `2^ℓ` entries, `ℓ = log_n − 6`,
and the table is zero outside them (a hidden layout's table is `Hidden.lean`'s). `Blocks.table L q` is that table read back from a stack, and
`Blocks.tableEval L q p` its multilinear extension at `p`.

`holds_iff`: **for every stack `q`, `q` satisfies the stack claim of a claim `c` exactly when the
table `L.table q` has `c.value` as its multilinear extension at `c.point`** (for a well-formed
layout and a point of `vars` coordinates). So "every candidate violates one of the claims" is
"every candidate's table violates one of the table claims", and an extracted candidate satisfying
all of them is a table satisfying all of them: the claims on one commitment, opened jointly, bind
one table.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd Finset

/-- What the meaning of the claims needs of a public stacking (`Layout::new` gives all of it, its
assertions and `log_n ≥ 6`): `64` lanes of `2^ℓ` entries, at most `64` of them used, each holding a
block of the table. -/
structure Blocks.Valid (L : Blocks) : Prop where
  six_le : laneFold ≤ L.logN
  lane_le : L.logLane ≤ L.vars
  lanes_le : L.lanes ≤ 2 ^ laneFold
  block_lt : ∀ b ∈ L.blocks, b < 2 ^ (L.vars - L.logLane)

/-- **The table a public stack stands for** (`Table::new`, `opening.rs:392-412`): entry `o + 2^ℓ·b`
(`o < 2^ℓ`) is entry `o + 2^ℓ·l` of the stack for the lane `l` holding block `b`, and `0` where no
lane holds it; written as the sum over the lanes holding the block, which is that one entry for
distinct blocks (as `Layout::new` lists them). -/
def Blocks.table (L : Blocks) (q : Column L.logN) (t : ℕ) : K :=
  ∑ l ∈ range L.lanes, if L.blocks.getD l 0 = t / 2 ^ L.logLane then
    q.values.getD (t % 2 ^ L.logLane + 2 ^ L.logLane * l) 0 else 0

/-- The table's multilinear extension at `p` (`Table::eval`, `opening.rs:504-516`). -/
def Blocks.tableEval (L : Blocks) (q : Column L.logN) (p : List E) : E :=
  ∑ t ∈ range (2 ^ L.vars), ofK (L.table q t) * eqEval (boolPoint L.vars t) p

/-! ## Sums -/

theorem if_pos' {P : Prop} [Decidable P] (h : P) {α : Type} (a b : α) :
    (if P then a else b) = a := by simp [h]


theorem sum_range_mul_split (a b : ℕ) (f : ℕ → E) :
    ∑ x ∈ range (a * b), f x = ∑ l ∈ range b, ∑ o ∈ range a, f (o + a * l) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    refine congrArg (HAdd.hAdd _) ?_
    exact Finset.sum_congr rfl fun o _ ↦ by rw [add_comm]

theorem zip_range'_sum (g : ℕ → E) : ∀ (ws : List E) (s : ℕ),
    ((ws.zip (List.range' s ws.length)).map fun p ↦ p.1 * g p.2).sum =
      ∑ i ∈ range ws.length, ws.getD i 0 * g (s + i)
  | [], _ => by simp
  | w :: ws, s => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      zip_range'_sum g ws (s + 1), Finset.sum_range_succ', add_comm]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) (by simp)
    simp only [List.getD_cons_succ]
    rw [show s + 1 + i = s + (i + 1) by omega]

theorem sum_three_swap (s t u : Finset ℕ) (F : ℕ → ℕ → ℕ → E) :
    ∑ b ∈ s, ∑ o ∈ t, ∑ l ∈ u, F b o l = ∑ l ∈ u, ∑ o ∈ t, ∑ b ∈ s, F b o l :=
  calc ∑ b ∈ s, ∑ o ∈ t, ∑ l ∈ u, F b o l = ∑ b ∈ s, ∑ l ∈ u, ∑ o ∈ t, F b o l :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ l ∈ u, ∑ b ∈ s, ∑ o ∈ t, F b o l := Finset.sum_comm
    _ = ∑ l ∈ u, ∑ o ∈ t, ∑ b ∈ s, F b o l := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

theorem ofK_sum (s : Finset ℕ) (f : ℕ → K) : ofK (∑ l ∈ s, f l) = ∑ l ∈ s, ofK (f l) :=
  map_sum (algebraMap K E) f s

theorem ofK_ite (P : Prop) [Decidable P] (a : K) :
    ofK (if P then a else 0) = if P then ofK a else 0 := by
  split_ifs
  · rfl
  · exact map_zero (algebraMap K E)

/-! ## The claim's weight on the cube -/

/-- A claim's weight, as `eq` of the lane coordinates times the lanes' sum. -/
theorem claimWeight_eq (L : Blocks) (c : Claim) (x : List E) :
    claimWeight L c x = eqEval (c.point.take L.logLane) (x.take L.logLane) *
      ∑ i ∈ range L.lanes, (L.laneWeights c.point).getD i 0 * eqBits (x.drop L.logLane) i := by
  have hl : (L.laneWeights c.point).length = L.lanes := by simp [Blocks.laneWeights, Blocks.lanes]
  rw [claimWeight, eqLow_eq_eqEval, lanes_eq_sum, List.range_eq_range', ← hl, zip_range'_sum]
  simp

/-- A lane's weight is `eq` of the point's high coordinates at the lane's block. -/
theorem laneWeight_getD (L : Blocks) (p : List E) {l : ℕ} (hl : l < L.lanes) :
    (L.laneWeights p).getD l 0 =
      eqEval (boolPoint (p.length - L.logLane) (L.blocks.getD l 0)) (p.drop L.logLane) := by
  have hl' : l < (L.laneWeights p).length := by simpa [Blocks.laneWeights, Blocks.lanes] using hl
  rw [List.getD_eq_getElem _ _ hl', List.getD_eq_getElem _ _ (by simpa [Blocks.lanes] using hl)]
  simp only [Blocks.laneWeights, List.getElem_map]
  rw [eqBits_eq_eqEval, LeanVM.Protocol.EndToEnd.Front.selectorPoint_eq_boolPoint, List.length_drop]
  rfl

/-- On the cube, the lane sum picks the lane's weight. -/
theorem lanes_at_boolPoint (L : Blocks) (hL : L.Valid) (p : List E) {l : ℕ}
    (hl : l < 2 ^ laneFold) :
    ∑ i ∈ range L.lanes, (L.laneWeights p).getD i 0 * eqBits (boolPoint laneFold l) i =
      if l ∈ range L.lanes then (L.laneWeights p).getD l 0 else 0 := by
  have h : ∀ i ∈ range L.lanes, (L.laneWeights p).getD i 0 * eqBits (boolPoint laneFold l) i =
      if i = l then (L.laneWeights p).getD i 0 else 0 := by
    intro i hi
    have hi64 : i < 2 ^ laneFold := (mem_range.1 hi).trans_le hL.lanes_le
    rw [eqBits_eq_eqEval, LeanVM.Protocol.EndToEnd.Front.selectorPoint_eq_boolPoint,
      show (boolPoint laneFold l).length = laneFold by simp [boolPoint],
      LeanVM.Protocol.EndToEnd.Complete.eqEval_boolPoint_boolPoint laneFold i l hi64 hl]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']

/-! ## The two sums -/

variable (L : Blocks) (hL : L.Valid) (c : Claim) (hc : c.point.length = L.vars)
  (q : Column L.logN)

include hL hc in
/-- The stack's side: the claim's weight against the stack, lane by lane. -/
theorem stack_sum :
    ∑ x : Fin (2 ^ L.logN), claimWeight L c (boolPoint L.logN x) * ofK (q.values.getD x 0) =
      ∑ l ∈ range L.lanes, ∑ o ∈ range (2 ^ L.logLane),
        ofK (q.values.getD (o + 2 ^ L.logLane * l) 0) *
          (eqEval (boolPoint L.logLane o) (c.point.take L.logLane) *
            eqEval (boolPoint (L.vars - L.logLane) (L.blocks.getD l 0))
              (c.point.drop L.logLane)) := by
  have hN : L.logN = L.logLane + laneFold := by
    have := hL.six_le; simp only [Blocks.logLane]; omega
  have hR : range (2 ^ L.logN) = range (2 ^ L.logLane * 2 ^ laneFold) := by
    rw [← pow_add, ← hN]
  have hpt : ∀ o l, o < 2 ^ L.logLane →
      boolPoint L.logN (o + 2 ^ L.logLane * l) = boolPoint L.logLane o ++ boolPoint laneFold l :=
    fun o l ho ↦ by
      conv_lhs => rw [hN]
      exact LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ ho
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ claimWeight L c (boolPoint L.logN x) *
    ofK (q.values.getD x 0)) (2 ^ L.logN), hR, sum_range_mul_split]
  refine (Finset.sum_subset (fun x hx ↦ mem_range.2 ((mem_range.1 hx).trans_le hL.lanes_le))
    ?_).symm.trans (Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl fun o ho ↦ ?_)
  · -- an unused lane contributes nothing
    intro l hl hnl
    refine Finset.sum_eq_zero fun o ho ↦ ?_
    have ho' : o < 2 ^ L.logLane := mem_range.1 ho
    rw [hpt o l ho', claimWeight_eq,
      List.take_left' (by simp [boolPoint]), List.drop_left' (by simp [boolPoint]),
      lanes_at_boolPoint L hL c.point (mem_range.1 hl)]
    simp [hnl]
  · have ho' : o < 2 ^ L.logLane := mem_range.1 ho
    have hl' : l < 2 ^ laneFold := (mem_range.1 hl).trans_le hL.lanes_le
    rw [hpt o l ho', claimWeight_eq,
      List.take_left' (by simp [boolPoint]), List.drop_left' (by simp [boolPoint]),
      lanes_at_boolPoint L hL c.point hl', if_pos' hl,
      laneWeight_getD L c.point (mem_range.1 hl), hc,
      LeanVM.Protocol.Whir.Complete.eqEval_comm (c.point.take _)]
    ring

include hL hc in
/-- The table's side: its multilinear extension, lane by lane. -/
theorem table_sum :
    L.tableEval q c.point =
      ∑ l ∈ range L.lanes, ∑ o ∈ range (2 ^ L.logLane),
        ofK (q.values.getD (o + 2 ^ L.logLane * l) 0) *
          (eqEval (boolPoint L.logLane o) (c.point.take L.logLane) *
            eqEval (boolPoint (L.vars - L.logLane) (L.blocks.getD l 0))
              (c.point.drop L.logLane)) := by
  have hV : L.vars = L.logLane + (L.vars - L.logLane) := by have := hL.lane_le; omega
  have hR : range (2 ^ L.vars) = range (2 ^ L.logLane * 2 ^ (L.vars - L.logLane)) := by
    rw [← pow_add, ← hV]
  -- each entry of the table, with its point split at the lane's coordinates
  have hentry : ∀ b ∈ range (2 ^ (L.vars - L.logLane)), ∀ o ∈ range (2 ^ L.logLane),
      ofK (L.table q (o + 2 ^ L.logLane * b)) *
          eqEval (boolPoint L.vars (o + 2 ^ L.logLane * b)) c.point =
        ∑ l ∈ range L.lanes, if L.blocks.getD l 0 = b then
          ofK (q.values.getD (o + 2 ^ L.logLane * l) 0) *
            (eqEval (boolPoint L.logLane o) (c.point.take L.logLane) *
              eqEval (boolPoint (L.vars - L.logLane) b) (c.point.drop L.logLane)) else 0 := by
    intro b _ o ho
    have ho' : o < 2 ^ L.logLane := mem_range.1 ho
    have hdiv : (o + 2 ^ L.logLane * b) / 2 ^ L.logLane = b := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ho', zero_add]
    have hmod : (o + 2 ^ L.logLane * b) % 2 ^ L.logLane = o := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho']
    have hpt : boolPoint L.vars (o + 2 ^ L.logLane * b) =
        boolPoint L.logLane o ++ boolPoint (L.vars - L.logLane) b := by
      conv_lhs => rw [hV]
      exact LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ ho'
    have hsplit : eqEval (boolPoint L.vars (o + 2 ^ L.logLane * b)) c.point =
        eqEval (boolPoint L.logLane o) (c.point.take L.logLane) *
          eqEval (boolPoint (L.vars - L.logLane) b) (c.point.drop L.logLane) := by
      rw [hpt]
      conv_lhs => rw [← List.take_append_drop L.logLane c.point]
      exact LeanVM.Protocol.Whir.Complete.eqEval_append _ _ _ _
        (by simp [boolPoint, hc, hL.lane_le])
    rw [Blocks.table, hdiv, hmod, ofK_sum, Finset.sum_mul, hsplit]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [ofK_ite]
    split_ifs <;> simp
  rw [Blocks.tableEval, hR, sum_range_mul_split,
    Finset.sum_congr rfl fun b hb ↦ Finset.sum_congr rfl fun o ho ↦ hentry b hb o ho,
    sum_three_swap]
  refine Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl fun o _ ↦ ?_
  have hmem : L.blocks.getD l 0 ∈ L.blocks := by
    rw [List.getD_eq_getElem _ _ (by simpa [Blocks.lanes] using hl)]
    exact List.getElem_mem _
  rw [Finset.sum_ite_eq, if_pos' (mem_range.2 (hL.block_lt _ hmem))]

include hL hc in
/-- **A claim holds of a stack exactly when its table claim holds of the stack's table.** -/
theorem holds_iff :
    StackClaim.Holds L.logN (claimWeight L c, c.value) q ↔ L.tableEval q c.point = c.value := by
  simp only [StackClaim.Holds]
  rw [stack_sum L hL c hc q, table_sum L hL c hc q]

/-- **The opening's doom in table terms**: the level-0 commitment has the stack's shape, and
every candidate's table violates one of the claims. -/
theorem openingDoom_iff (L : Blocks) (hL : L.Valid) (R : ℕ) (claims : List Claim)
    (hc : ∀ c ∈ claims, c.point.length = L.vars) (cs : List (ℕ × ℕ × Word)) :
    OpeningDoom L.stacking R claims cs ↔
      LeanVM.Protocol.Whir.Sound.ShapeOK 0 (code₀ L.logN R) laneBits cs ∧
        ∀ q ∈ Candidates L.logN R (code₀ L.logN R).thr (LeanVM.Protocol.Whir.Sound.wordOf cs 0),
          ∃ c ∈ claims, L.tableEval q c.point ≠ c.value := by
  unfold OpeningDoom LeanVM.Protocol.Whir.Sound.StackedPre
  refine and_congr Iff.rfl (forall₂_congr fun q _ ↦ ?_)
  constructor
  · rintro ⟨sc, hsc, hn⟩
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 hsc
    exact ⟨c, hcm, fun h ↦ hn ((holds_iff L hL c (hc c hcm) q).2 h)⟩
  · rintro ⟨c, hcm, hn⟩
    exact ⟨_, List.mem_map.2 ⟨c, hcm, rfl⟩, fun h ↦ hn ((holds_iff L hL c (hc c hcm) q).1 h)⟩


/-! ## A public layout is a public stacking -/

/-- A lane's block (`0` for a lane holding none). -/
def Lane.blockD : Lane → ℕ
  | .block b => b
  | _ => 0

/-- **A public layout's blocks** (`Layout::new`'s layouts). -/
def Layout.toBlocks (L : Layout) : Blocks := ⟨L.vars, L.logN, L.lanes.map Lane.blockD⟩

/-- A public layout: no piece, every lane a block. -/
def Layout.IsPublic (L : Layout) : Prop := L.logPiece = none ∧ ∀ l ∈ L.lanes, ∃ b, l = .block b

/-- A sum over `zipIdx` as a sum over the indices. -/
theorem sum_zipIdx {α : Type} (d : α) (g : α × ℕ → E) : ∀ (xs : List α) (k : ℕ),
    ((xs.zipIdx k).map g).sum = ∑ i ∈ range xs.length, g (xs.getD i d, k + i)
  | [], k => by simp
  | a :: xs, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx d g xs (k + 1),
      List.length_cons, Finset.sum_range_succ', add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    refine congrArg (· + _) (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [show k + 1 + i = k + (i + 1) by omega]

theorem and_one_cases (i : ℕ) : i &&& 1 = 0 ∨ i &&& 1 = 1 := by
  rw [Nat.and_one_is_mod]
  exact Nat.mod_two_eq_zero_or_one i

/-- Both parities: every block lane. -/
theorem onTerm_add (ps le : List E) (ll : Lane × ℕ) :
    onTerm ps le 0 ll + onTerm ps le 1 ll =
      match ll.1 with
      | .block _ => ps.getD ll.2 0 * le.getD ll.2 0
      | _ => 0 := by
  rcases ll with ⟨_ | _ | _, i⟩ <;> simp only [onTerm]
  · rcases and_one_cases i with h | h <;> simp [h]
  · simp
  · simp

/-- **A public layout's claim weight is its blocks'**. -/
theorem Layout.claimWeight_toBlocks (L : Layout) (hP : L.IsPublic) (c : Claim) :
    L.claimWeight c = WhirBridge.claimWeight L.toBlocks c := by
  funext x
  have hlog : L.toBlocks.logLane = L.logLane := rfl
  have hlanes : L.toBlocks.lanes = L.lanes.length := by simp [Blocks.lanes, Layout.toBlocks]
  rw [claimWeight_public L c hP.1, claimWeight_eq, hlog, hlanes, eqZ_eq_eqEval,
    onParity_eq_sum, onParity_eq_sum, ← List.sum_map_add, sum_zipIdx .random _ _ 0]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun i hi ↦ ?_)
  have hi' : i < L.lanes.length := mem_range.1 hi
  obtain ⟨b, hb⟩ := hP.2 _ (List.getElem_mem hi')
  have hget : L.lanes.getD i .random = .block b := by
    rw [List.getD_eq_getElem _ _ hi', hb]
  simp only [zero_add]
  rw [onTerm_add, hget]
  simp only
  rw [laneEqs_getD, if_pos hi']
  congr 1
  rw [List.getD_eq_getElem _ _ (by simpa [Layout.laneScales] using hi'),
    List.getD_eq_getElem _ _ (by simpa [Blocks.laneWeights, Layout.toBlocks] using hi')]
  simp [Layout.laneScales, Blocks.laneWeights, Layout.toBlocks, hb, Lane.blockD]
  rfl

/-! ## What the composition imports

**The list bound exported.** The candidates every statement here quantifies over are
`Candidates μ R (code₀ μ R).thr W`: the stacks whose encoding agrees with the root's word `W` on
at least level 0's Johnson threshold of columns, the threshold of leanerVM's **certified** level-0
code (`deployedCodes`, slack `η = e/2^22` from `Params/Deployed.lean`, the one under which the
deployed query counts certify `2^-128` with the fold group's row-union factor `2^(ℓ−1)`; not the
slack `whir_config.rs` searches). For every word there are at most `listMax` of them
(`candidates_count`), and at our shapes at most `9952` (`log_n = 24`, the wiring table), `7908`
(`25`, the witness table) and `3564` (`28`, the quotient table) (`candidates_ours`); mumbai's
global bound is `2^18`. A reduction whose challenges come before any claim pins a list member
union-bounds over these lists.

**One opening per root.** The guarantee is joint only within one opening: an opening that is not
doomed has **one** candidate whose table satisfies **all** its claims (`joint_of_not_doom`).
Claims on one root split over two openings would get one candidate each, possibly different list
members; so the composition must open all the claims on a root in one opening, as
`protocol::verify_openings` does (one opening per commitment, the quotient table's two claims
together). -/

/-- The candidates of a level-0 word at the deployed threshold are finite and at most `listMax`
(mumbai's `candidates_finite`, `candidates_ncard_le`). -/
theorem candidates_count {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) :
    (Candidates μ R (code₀ μ R).thr W).Finite ∧
      (Candidates μ R (code₀ μ R).thr W).ncard ≤ (code₀ μ R).listMax := by
  obtain ⟨q₀, rest, hc, -⟩ := LeanVM.Protocol.Whir.Complete.exists_ladder hw
  obtain ⟨-, hμ, hκ, hR, -⟩ := LeanVM.Protocol.Whir.Params.deployed_spec_hyps hw hc
  exact ⟨LeanVM.Protocol.EndToEnd.Sound.candidates_finite _ hκ hR hμ W,
    LeanVM.Protocol.EndToEnd.Sound.candidates_ncard_le _ hκ hR hμ W⟩

/-- **The list bound exported for the composition**: at our three shapes (rate `1/2`), every
root's word has at most `9952`, `7908`, `3564` candidates. -/
theorem candidates_ours (W : Word) :
    (Candidates 24 1 (code₀ 24 1).thr W).ncard ≤ 9952 ∧
      (Candidates 25 1 (code₀ 25 1).thr W).ncard ≤ 7908 ∧
      (Candidates 28 1 (code₀ 28 1).thr W).ncard ≤ 3564 :=
  ⟨(candidates_count (by decide) W).2.trans listMax_ours.1,
    (candidates_count (by decide) W).2.trans listMax_ours.2.1,
    (candidates_count (by decide) W).2.trans listMax_ours.2.2⟩

/-- **Joint extraction**: a root's commitment of the stack's shape that is not doomed for an
opening has one candidate whose table satisfies all of that opening's claims. -/
theorem joint_of_not_doom (L : Blocks) (hL : L.Valid) (R : ℕ) (claims : List Claim)
    (hc : ∀ c ∈ claims, c.point.length = L.vars) (cs : List (ℕ × ℕ × Word))
    (hshape : LeanVM.Protocol.Whir.Sound.ShapeOK 0 (code₀ L.logN R) laneBits cs)
    (hnot : ¬ OpeningDoom L.stacking R claims cs) :
    ∃ q ∈ Candidates L.logN R (code₀ L.logN R).thr (LeanVM.Protocol.Whir.Sound.wordOf cs 0),
      ∀ c ∈ claims, L.tableEval q c.point = c.value := by
  rw [openingDoom_iff L hL R claims hc cs] at hnot
  by_contra hno
  refine hnot ⟨hshape, fun q hq ↦ ?_⟩
  by_contra hall
  exact hno ⟨q, hq, fun c hcm ↦ by
    by_contra hne
    exact hall ⟨c, hcm, hne⟩⟩

end WhirBridge

