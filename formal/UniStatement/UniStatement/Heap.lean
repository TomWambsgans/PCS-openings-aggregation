-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/heap.rs`. MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Basic

/-!
# The product heap's layout (`heap.rs`, SPEC.md §5.2)

The heap is one polynomial on `V_H`: position `i` holds node `i` (children `2i`, `2i + 1`, root `1`), the
leaves at `[2^(H−1), 2^H)`. The leaves come in aligned blocks: the memory's (each cell's initial over final
fingerprint), the bytecode's (likewise per instruction), one per table (each row's pushes over pulls),
largest first (ties: memory, bytecode, then the tables in opcode order); the rest of the leaves are covered
by aligned **unused** blocks, each pinned to `1`.
-/

@[expose] public section

namespace UniStatement

/-- What a block's leaves are (`Leaves`). -/
inductive Leaves where
  | memory
  | bytecode
  | table (t : ℕ)
  | unused
  deriving DecidableEq, Repr, Inhabited

/-- `leaves_order`: the tie-break of equal sizes. -/
def Leaves.order : Leaves → ℕ
  | .memory => 0
  | .bytecode => 1
  | .table t => 2 + t
  | .unused => 99

/-- **A block** (`Block`): its leaves, its variables (`2^r` leaves), its first leaf's heap position
(`2^(H−1)` plus its offset among the leaves). -/
structure Block where
  leaves : Leaves
  r : ℕ
  position : ℕ
  deriving Inhabited

/-- **The heap's layout** (`HeapLayout`): `2^h` positions, `2^(h−1)` leaves, the blocks. -/
structure HeapLayout where
  h : ℕ
  blocks : List Block
  deriving Inhabited

/-- The unused blocks covering `[offset, base)`, each the largest aligned block that fits
(`HeapLayout::new`'s second loop). -/
def unusedBlocks (base : ℕ) (offset : ℕ) : List Block := Id.run do
  let mut out : Array Block := #[]
  let mut offset := offset
  for _ in [0:2 * (Nat.log2 base + 1) + 2] do
    if offset < base then
      let mut r := trailingZeros offset
      for _ in [0:65] do
        if offset + 2 ^ r > base then r := r - 1
      out := out.push ⟨.unused, r, base + offset⟩
      offset := offset + 2 ^ r
  return out.toList

/-- **`HeapLayout::new`**: the memory's, the bytecode's and the tables' blocks, largest first, at
aligned offsets from `2^d`, `d = ⌈log₂ Σ 2^r⌉`; then the unused blocks; `h = d + 1`. -/
def HeapLayout.new (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) : HeapLayout :=
  let used : List (Leaves × ℕ) :=
    [(.memory, logMemory), (.bytecode, logBytecode)] ++
      (List.range tableLogHeights.length).map fun t ↦ (.table t, tableLogHeights.getD t 0)
  let sorted := used.mergeSort fun a b ↦ b.2 < a.2 || (a.2 == b.2 && a.1.order ≤ b.1.order)
  let total := (sorted.map fun (_, r) ↦ 2 ^ r).sum
  let d := log2Ceil total
  let base := 2 ^ d
  let (blocks, offset) := sorted.foldl (fun (acc : Array Block × ℕ) (leaves, r) ↦
    (acc.1.push ⟨leaves, r, base + acc.2⟩, acc.2 + 2 ^ r)) (#[], 0)
  ⟨d + 1, blocks.toList ++ unusedBlocks base offset⟩

end UniStatement

end
