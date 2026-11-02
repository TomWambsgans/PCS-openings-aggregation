-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/stacks.rs` and `verifier.rs`'s
-- `weight_at`. MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Claims

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
its weight). The Rust caches the `eq` products and the twisted points (`EqCache`); the values are the
same, computed here directly but for the twisted points, which are built once per point.
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

/-- **A combined claim's weight at the stack point `r`** (`weight_at`): every term's `eq` weight on its
column's blocks. -/
def weightAt (claim : Combined) (layout : StackLayout) (r : List E) : E :=
  let points := claim.points.toArray
  -- Every point's twisted forms, up to the largest twist its terms use.
  let maxTwist : Array ℕ := claim.terms.foldl (fun acc (_, p, twist, _) ↦
    acc.modify p (max twist)) (Array.replicate points.size 0)
  let twisted : Array (Array (List E)) :=
    Array.ofFn (n := points.size) fun p ↦ twistedPoints (points.getD p.val []) (maxTwist.getD p.val 0)
  claim.terms.foldl (fun total (column, p, twist, coefficient) ↦
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
