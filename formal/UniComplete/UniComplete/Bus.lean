-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `crates/leanvm_univariate/src/prover/bus.rs`
-- (branch `leanvm-univariate-prover2`): the leaves and the product heap (SPEC.md §5).
import UniComplete.Trace

/-!
# The bus as a product heap, prover side (`bus.rs`)

Every leaf is a push-over-pull ratio: a table's active row `Π_j D'_j / Π_j D_j` over its flushes (a padding row
`1`), a memory cell's `D_init / D_fin` (count `1` over its final count), an instruction's likewise. The heap
(`heapValues`) holds node `i` at position `i`: the leaves at their blocks of `HeapLayout` (`Shape.heap`), unused
blocks `1`, every inner node the product of its children, position `0` zero.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters

/-- A row's value in `E`: column `c`, row `i` of table `t`. -/
def Trace.cell (tr : Trace) (t c i : ℕ) : E := ofK ((tr.column t c).getD i 0)

/-- **Table `t`'s leaves** (`table_leaves`): `Π push / Π pull` on the active rows, `1` on the padding rows. -/
def tableLeaves (tr : Trace) (weights : Array E) (beta : E) (t : ℕ) : Array E :=
  let table := tables.getD t default
  let r := tr.height t
  let rows := tr.rows.getD t 0
  Array.ofFn (n := 2 ^ r) fun i ↦
    if isActive i.val rows r then
      let col := (tr.cell t · i.val)
      let pull := table.flushes.pull.foldl (fun acc tuple ↦ acc * fpE tuple weights beta col) 1
      let push := table.flushes.push.foldl (fun acc tuple ↦ acc * fpE tuple weights beta col) 1
      push * pull⁻¹
    else 1

/-- **The memory's leaves** (`memory_leaves`): `D_init / D_fin` of every cell. -/
def memoryLeaves (tr : Trace) (weights : Array E) (beta : E) : Array E :=
  let lm := tr.shape.logMemory
  Array.ofFn (n := 2 ^ lm) fun i ↦
    let limbs := (List.range 3).map fun k ↦ ofK ((tr.memory.getD k #[]).getD i.val 0)
    let address := ofK (LeanVM.Parameters.gpow i.val)
    let fin := memoryFp weights beta address (ofK ((tr.memory.getD 3 #[]).getD i.val 0)) limbs
    let init := memoryFp weights beta address 1 limbs
    init * fin⁻¹

/-- An instruction's slot `s` at count `count`. -/
def bytecodeSlot (tr : Trace) (i s : ℕ) (count : E) : E :=
  if s = 2 then count else ofK ((tr.slots.getD s #[]).getD i 0)

/-- **The bytecode's leaves** (`bytecode_leaves`): `D_init / D_fin` of every instruction. -/
def bytecodeLeaves (tr : Trace) (weights : Array E) (beta : E) : Array E :=
  let lb := tr.shape.logBytecode
  Array.ofFn (n := 2 ^ lb) fun i ↦
    let fin := bytecodeFp weights beta (fun s ↦ bytecodeSlot tr i.val s (ofK (tr.bytecodeFinal.getD i.val 0)))
    let init := bytecodeFp weights beta (fun s ↦ bytecodeSlot tr i.val s 1)
    init * fin⁻¹

/-- A block's leaves. -/
def blockLeaves (tr : Trace) (weights : Array E) (beta : E) : Leaves → Array E
  | .memory => memoryLeaves tr weights beta
  | .bytecode => bytecodeLeaves tr weights beta
  | .table t => tableLeaves tr weights beta t
  | .unused => #[]

/-- One level of the heap: positions `[half/2, half)` the products of their children. -/
def heapLevel (heap : Array E) (half : ℕ) : Array E :=
  (List.range (half / 2)).foldl (fun h j ↦
    let p := half / 2 + j
    h.set! p (h.getD (2 * p) 0 * h.getD (2 * p + 1) 0)) heap

/-- **The heap** (`heap`): `2^h` positions, the used blocks' leaves at their positions, unused leaves `1`, every
inner node the product of its children (levels from the leaves up), position `0` zero. -/
def heapValues (tr : Trace) (weights : Array E) (beta : E) : Array E :=
  let layout := tr.shape.heap
  let size := 2 ^ layout.h
  let leaves := layout.blocks.foldl (fun (heap : Array E) block ↦
    match block.leaves with
    | .unused => heap
    | kind =>
      let values := blockLeaves tr weights beta kind
      (List.range (2 ^ block.r)).foldl (fun h i ↦ h.set! (block.position + i) (values.getD i 0)) heap)
    (Array.replicate size 1)
  -- levels: half = 2^(h−1), …, 2
  let filled := (List.range (layout.h - 1)).foldl (fun heap j ↦ heapLevel heap (2 ^ (layout.h - 1 - j))) leaves
  filled.set! 0 0

/-- The root the state boundary requires (`expected_root`): `fp(final) / fp(initial)`. -/
def expectedRoot (weights : Array E) (beta : E) (lb : ℕ) : E :=
  stateFp weights beta (gpow (2 ^ lb - 1)) * (stateFp weights beta 1)⁻¹

end UniComplete
