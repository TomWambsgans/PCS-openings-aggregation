-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/stacks.rs` and `verifier.rs`'s
-- `weight_at`. MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Claims
public import UniStatement.Flock

/-!
# The stacks (`stacks.rs`, SPEC.md §3) and a claim's weight on them

A **stack** is a `K`-table of `2^vars` words, its multilinear extension over `vars` variables (low first). A
column of `2^v` words sits in an aligned block at `offset` (largest first, ties in the order given): its word
`i` is the stack's `offset + i`. An `E`-valued column is three such blocks, its limbs
(`x = c₀ + c₁ y + c₂ y²`). `q_flock`'s slot `j` is the column `Qflock` with its low 8 coordinates fixed to
`j`'s bits. The stack has at least `2^15` words (`MIN_STACKED_LOG`).

**A claim's weight at a stack point** `r` (`weight_at`): each term's `eq` on its column's blocks, `eq` of the
(twisted) point on the block's own coordinates, times the block's selector on the coordinates above,
up to `r`'s length (the batch's point may be longer than the stack: the stack is zero-extended, and so is
its weight). The Rust caches the `eq` products and the twisted points (`EqCache`), and (iteration 2, lever 1c)
shares work: a column's limbs share its row, terms on one row add their parts before the row multiplies them,
and `q_flock`'s slots share their instance coordinates' `eq`; the values are the same (field arithmetic is
exact), computed here directly term by term but for the twisted points, which are built once per point.
**The ring-switch term** (iteration 2, lever 1a: twist `ringTwist`, the main line's one term for the whole
weight `Φ(eq(p, ·))`) is evaluated by the map in tower order, `Flock.towerWeightAt`.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters

/-- **A stack's layout** (`StackLayout`): its variables, and its blocks (column, limb, variables,
offset). -/
structure StackLayout where
  vars : ℕ
  blocks : List (Column × ℕ × ℕ × ℕ)
  deriving Inhabited

/-- **`StackLayout::new(columns)`**: each column (its variables, whether it is `E`-valued) as one or three
pieces, sorted largest first (stable), laid end to end; at least `15` variables. -/
def StackLayout.new (columns : List (Column × ℕ × Bool)) : StackLayout :=
  let pieces : List (Column × ℕ × ℕ) := columns.flatMap fun (column, vars, eValued) ↦
    (List.range (if eValued then 3 else 1)).map fun limb ↦ (column, limb, vars)
  let sorted := pieces.mergeSort fun a b ↦ b.2.2 ≤ a.2.2
  let (blocks, offset) := sorted.foldl (fun (acc : Array (Column × ℕ × ℕ × ℕ) × ℕ) (column, limb, vars) ↦
    (acc.1.push (column, limb, vars, acc.2), acc.2 + 2 ^ vars)) (#[], 0)
  ⟨max (log2Ceil (max offset 2)) 15, blocks.toList⟩

/-- `StackLayout::words`: the words the blocks fill (`placed`, a layout word's last seven bytes). -/
def StackLayout.words (l : StackLayout) : ℕ := l.blocks.foldl (fun acc (_, _, vars, _) ↦ acc + 2 ^ vars) 0

/-- `limbs(column)`: the column's blocks, as (limb, variables, offset). -/
def StackLayout.limbs (l : StackLayout) (column : Column) : List (ℕ × ℕ × ℕ) :=
  l.blocks.filterMap fun (c, limb, vars, offset) ↦ if c == column then some (limb, vars, offset) else none

/-- `limb_basis()`: `(1, y, y²)`. -/
def limbBasis : List E := [eNew 1 0 0, eNew 0 1 0, eNew 0 0 1]

/-- `EqCache::row`: `Π_{k<len} (1 + p_k + r_k)` for the (already twisted) point `p`. -/
def rowEq (point : List E) (len : ℕ) (r : List E) : E :=
  (List.range len).foldl (fun acc k ↦ acc * (1 + point.getD k 0 + r.getD k 0)) 1

/-- `EqCache::selector(from, offset)`: `Π_{k ≥ from} eq(bit_k(offset), r_k)` over `r`'s coordinates. -/
def selector (r : List E) (fromVar offset : ℕ) : E :=
  (List.range' fromVar (r.length - fromVar)).foldl (fun acc k ↦
    acc * if offset.testBit k then r.getD k 0 else 1 + r.getD k 0) 1

/-- A point's coordinates squared `twist` times, for every twist up to `maxTwist`
(`EqCache::twisted_point`, built from the previous twist's). -/
def twistedPoints (point : List E) (maxTwist : ℕ) : Array (List E) :=
  (List.range maxTwist).foldl (fun acc _ ↦ acc.push ((acc.back?.getD point).map fun x ↦ x * x)) #[point]

/-- **`RING_TWIST`** (`verifier.rs`, iteration 2): the twist of the term that stands for the whole ring-switch
weight `Φ(eq(p, ·))` on the main line, which the batch's weight evaluates at its point by the map
(`Flock.towerWeightAt`) rather than as 64 twisted terms. -/
def ringTwist : ℕ := 255

/-- **A combined claim's weight at the stack point `r`** (`weight_at`): every term's `eq` weight on its
column's blocks; the ring-switch term (twist `ringTwist`) by the map `ringMap` (iteration 2:
`S::ring_weight`, `ring_tower::weight_at` of the point's first `vars` coordinates and of `1 + r`; `0` without
a map, where the Rust panics). -/
def weightAt (claim : Combined) (layout : StackLayout) (r : List E) (ringMap : Option (List E) := none) : E :=
  let points := claim.points.toArray
  let onePlusR := r.map (1 + ·)
  -- Every point's twisted forms, up to the largest twist its terms use (but the ring-switch term's).
  let maxTwist : Array ℕ := claim.terms.foldl (fun acc (_, p, twist, _) ↦
    if twist = ringTwist then acc else acc.modify p (max twist)) (Array.replicate points.size 0)
  let twisted : Array (Array (List E)) :=
    Array.ofFn (n := points.size) fun p ↦ twistedPoints (points.getD p.val []) (maxTwist.getD p.val 0)
  claim.terms.foldl (fun total (column, p, twist, coefficient) ↦
    if twist = ringTwist then
      (layout.limbs column).foldl (fun total (limb, vars, offset) ↦
        let row := match ringMap with
          | some map => Flock.towerWeightAt ((points.getD p []).take vars) (onePlusR.take vars) map
          | none => 0
        let scale := if limb = 0 then coefficient else coefficient * limbBasis.getD limb 0
        total + scale * (row * selector r vars offset)) total
    else
    let point := (twisted.getD p #[]).getD twist []
    -- `q_flock`'s word `slot + 256 · instance`: the slot's bits, then the instance's coordinates.
    let (column, row, rowLen) : Column × List E × ℕ := match column with
      | .qflockSlot j =>
        let row := (List.range 8).map (bitE j) ++ point
        (.qflock, row, row.length)
      | _ => (column, point, 0)
    (layout.limbs column).foldl (fun total (limb, vars, offset) ↦
      let len := if rowLen > 0 then rowLen else vars
      let eq := rowEq row len r * selector r vars offset
      let scale := if limb = 0 then coefficient else coefficient * limbBasis.getD limb 0
      total + scale * eq) total) 0

end UniStatement

end
