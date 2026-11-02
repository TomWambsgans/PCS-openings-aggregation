-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Heap.Balanced

/-!
# The blocks of an instance

The leaves SPEC §5.2 assigns, read off an `M3Instance` and a stack `q`:

* **`tableBlock I q j`**: table `j`'s `2^τ_j` rows; executed row `x`'s leaf pushes and pulls the
  tuples of its flushes of each side (`rowTuples`), a padding row's leaf has none (its leaf is
  `1`, as at `leanvm-univariate` `56ea040`). Its pushes are a permutation of the table's part of
  `flushTuples` (`pushes_tableBlock_perm`): flush by flush there, row by row here
  (`perm_flatMap_map_comm`).
* **`pairBlock I q b₁ b₂`**: a pair of boundary blocks of one height, row `x`'s leaf pushing
  `b₁`'s row `x` and pulling `b₂`'s (the memory's seed and finalize, the bytecode's).
* **`boundaryRow I q b 0`**: a boundary block of one row, for the root (the state boundary).

These are generic in the instance; `Heap.LeanIsa` assembles leanISA's.
-/

namespace Heap

open LeanVM.Parameters Lv42.Protocol

/-- **Transposition**: a list of lists indexed by `(a, b)`, read `a`-major or `b`-major, is one
multiset. -/
theorem perm_flatMap_map_comm {α β γ : Type*} (as : List α) (bs : List β) (g : α → β → γ) :
    (as.flatMap fun a ↦ bs.map (g a)).Perm (bs.flatMap fun b ↦ as.map fun a ↦ g a b) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_bind, ← Multiset.coe_bind]
  simp only [← Multiset.map_coe, ← Multiset.bind_singleton]
  exact Multiset.bind_bind _ _

variable (I : M3Instance) (q : LeanVM.Protocol.Column I.μ)

/-- The tuple a flush sends from row `x` of table `j`. -/
def flushTuple (j : Fin I.ntab) (f : Side × Vector (CPoly.CMvPolynomial (I.width j) K) 16)
    (x : Fin (2 ^ I.τ j)) : Vector K 16 :=
  f.2.map fun P ↦ P.eval (I.row q j x)

/-- The tuples row `x` of table `j` flushes on side `s`, one per flush of that side, in flush
order; none past the table. -/
def rowTuples (j : Fin I.ntab) (s : Side) (x : ℕ) : List (Vector K 16) :=
  if h : x < 2 ^ I.τ j then
    ((I.flushes j).filter fun f ↦ decide (f.1 = s)).map fun f ↦ flushTuple I q j f ⟨x, h⟩
  else []

/-- **Table `j`'s block of leaves**: its `2^τ_j` rows, the executed ones with their tuples, the
padding ones with none. -/
def tableBlock (j : Fin I.ntab) : LeafBlock (Vector K 16) :=
  LeafBlock.ofRows (I.τ j) (I.rows j) (rowTuples I q j .push) (rowTuples I q j .pull)

/-- Table `j`'s part of `flushTuples` on side `s`. -/
def tableTuples (j : Fin I.ntab) (s : Side) : List (Vector K 16) :=
  ((I.flushes j).filter fun f ↦ decide (f.1 = s)).flatMap fun f ↦
    (I.executed j).map fun x ↦ f.2.map fun P ↦ P.eval (I.row q j x)

theorem flushTuples_eq (s : Side) :
    I.flushTuples q s = (List.finRange I.ntab).flatMap fun j ↦ tableTuples I q j s := rfl

/-- The executed rows' tuples of side `s`, row by row, are table `j`'s part of `flushTuples`. -/
theorem rows_perm_tableTuples (j : Fin I.ntab) (s : Side) :
    ((List.range (I.rows j)).flatMap (rowTuples I q j s)).Perm (tableTuples I q j s) := by
  have hr := I.rows_le j
  have hrange : List.range (I.rows j) = (List.finRange (I.rows j)).map Fin.val := by
    rw [List.map_coe_finRange_eq_range]
  rw [hrange, List.flatMap_map, tableTuples, M3Instance.executed_eq]
  have hrow : ∀ y : Fin (I.rows j), rowTuples I q j s y.val =
      ((I.flushes j).filter fun f ↦ decide (f.1 = s)).map fun f ↦
        flushTuple I q j f (Fin.castLE hr y) := by
    intro y
    rw [rowTuples, dite_eq_left_of_eq_true (eq_true (lt_of_lt_of_le y.isLt hr))]
    rfl
  rw [List.flatMap_congr fun y _ ↦ hrow y]
  refine (perm_flatMap_map_comm _ _ (fun y f ↦ flushTuple I q j f (Fin.castLE hr y))).trans ?_
  refine List.Perm.of_eq (List.flatMap_congr fun f _ ↦ ?_)
  rw [List.map_map]
  rfl

/-- **A table's block holds its executed rows' flushes**, push side. -/
theorem pushes_tableBlock_perm (j : Fin I.ntab) :
    (tableBlock I q j).pushes.Perm (tableTuples I q j .push) := by
  rw [tableBlock, LeafBlock.pushes_ofRows (I.rows_le j)]
  exact rows_perm_tableTuples I q j .push

/-- **A table's block holds its executed rows' flushes**, pull side. -/
theorem pulls_tableBlock_perm (j : Fin I.ntab) :
    (tableBlock I q j).pulls.Perm (tableTuples I q j .pull) := by
  rw [tableBlock, LeafBlock.pulls_ofRows (I.rows_le j)]
  exact rows_perm_tableTuples I q j .pull

/-- **Every table's block**, in table order: their pushes are `flushTuples`'s pushes. -/
theorem allPush_tableBlocks_perm :
    (allPush ((List.finRange I.ntab).map (tableBlock I q))).Perm (I.flushTuples q .push) := by
  rw [allPush, List.flatMap_map, flushTuples_eq]
  exact List.Perm.flatMap_left _ fun j _ ↦ pushes_tableBlock_perm I q j

/-- **Every table's block**, in table order: their pulls are `flushTuples`'s pulls. -/
theorem allPull_tableBlocks_perm :
    (allPull ((List.finRange I.ntab).map (tableBlock I q))).Perm (I.flushTuples q .pull) := by
  rw [allPull, List.flatMap_map, flushTuples_eq]
  exact List.Perm.flatMap_left _ fun j _ ↦ pulls_tableBlock_perm I q j

/-! ## Boundary blocks -/

/-- Row `x` of a boundary block: its tuple; the zero tuple past the block. -/
def boundaryRow (b : BoundaryBlock I.toShape) (x : ℕ) : Vector K 16 :=
  if h : x < 2 ^ b.κ then b.coords.map fun co ↦ I.coordCell q co ⟨x, h⟩ else Vector.replicate 16 0

/-- A boundary block's tuples, as `boundaryTuples` lists them. -/
def boundaryRows (b : BoundaryBlock I.toShape) : List (Vector K 16) :=
  (List.finRange (2 ^ b.κ)).map fun x ↦ b.coords.map fun co ↦ I.coordCell q co x

theorem map_boundaryRow (b : BoundaryBlock I.toShape) :
    (List.range (2 ^ b.κ)).map (boundaryRow I q b) = boundaryRows I q b := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, boundaryRows]
  refine List.map_congr_left fun x _ ↦ ?_
  simp only [Function.comp_apply, boundaryRow, dite_eq_left_of_eq_true (eq_true x.isLt)]

theorem boundaryTuples_eq (s : Side) :
    I.boundaryTuples q s =
      (I.boundary.filter fun b ↦ decide (b.side = s)).flatMap (boundaryRows I q) := rfl

/-- **A pair of boundary blocks** of one height: row `x`'s leaf pushes `b₁`'s row `x` and pulls
`b₂`'s. -/
def pairBlock (b₁ b₂ : BoundaryBlock I.toShape) : LeafBlock (Vector K 16) :=
  LeafBlock.pair b₁.κ (boundaryRow I q b₁) (boundaryRow I q b₂)

theorem pushes_pairBlock (b₁ b₂ : BoundaryBlock I.toShape) :
    (pairBlock I q b₁ b₂).pushes = boundaryRows I q b₁ := by
  rw [pairBlock, LeafBlock.pushes_pair, map_boundaryRow]

theorem pulls_pairBlock (b₁ b₂ : BoundaryBlock I.toShape) (h : b₁.κ = b₂.κ) :
    (pairBlock I q b₁ b₂).pulls = boundaryRows I q b₂ := by
  rw [pairBlock, LeafBlock.pulls_pair, h, map_boundaryRow]

/-- A boundary block of one row is its row `0`. -/
theorem boundaryRows_of_kappa_zero (b : BoundaryBlock I.toShape) (h : b.κ = 0) :
    boundaryRows I q b = [boundaryRow I q b 0] := by
  rw [← map_boundaryRow, h]
  rfl

end Heap
