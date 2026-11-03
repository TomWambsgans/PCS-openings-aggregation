-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniStatement.Opening

/-!
# The reference shape's constants

The reference deployment (`UniStatement.reference`: 1,000 signatures, memory `2^21`, bytecode `2^19`, heights
18 18 18 18 17 18) as numbers the end theorem needs, each by kernel evaluation of the shape's small objects (lists of
a few hundred natural numbers; no stack is evaluated):

* `reference_valid`: the shape is valid (`Shape.Valid`: six heights, `validate` with Flock);
* `reference_vars`: the three stacks have `27`, `27`, `24` variables (`layoutsOf`), so `C1`, `C2` and the setup are
  opened at `2^27`, `2^27`, `2^24` words, and the five `PCS_OPEN` layout words name `27, 27, 24, 28, 28`
  (`reference_wordVars`): every opening is within WHIR's `2^24 … 2^28` (`Whir.lean`'s `pcsOpen_honest`).

**The sorts.** `StackLayout.new` and `HeapLayout.new` sort with `List.mergeSort`, a well-founded recursion the
kernel does not reduce. Neither number depends on the order, so the sorts are removed by permutation
(`List.mergeSort_perm`) before the kernel evaluates:

* `stackLayout_vars`: `(StackLayout.new cols).vars = max (log2Ceil (max (pieceWords cols) 2)) 15`, the words of
  the pieces `Σ (3 if E-valued else 1) · 2^vars` in any order (the offset fold is their sum);
* `heapLayout_h`, `heapLayout_blocks_sum`: the heap's `h` from the unsorted used blocks (`heapUsed`), and a sum
  over its blocks of anything that reads only a block's leaves and size, as the sum over the unsorted used blocks
  plus the unused blocks' (`unusedBlocks`, no sort);
* `c2_pieceWords`: `C2`'s words as the heap's, the tree and constraint quotients' and the leaf quotients'
  (`leafWords`, a block's `leafDegree` chunks; none for an unused block), so that `C2`'s variables come from the
  unsorted blocks.
-/

namespace UniComplete

open UniStatement

theorem reference_heights : reference.heights = [18, 18, 18, 18, 17, 18] := by decide +kernel

theorem reference_valid : reference.Valid := by decide +kernel

/-! ### A stack's variables from its pieces' words -/

/-- The words a column list's pieces fill: `Σ (3 if E-valued else 1) · 2^vars`. -/
def pieceWords (cols : List (Column × ℕ × Bool)) : ℕ :=
  (cols.map fun c ↦ (if c.2.2 then 3 else 1) * 2 ^ c.2.1).sum

theorem pieceWords_append (a b : List (Column × ℕ × Bool)) :
    pieceWords (a ++ b) = pieceWords a + pieceWords b := by
  simp [pieceWords]

/-- A list sum is unchanged by `mergeSort` (a permutation). -/
theorem sum_map_mergeSort {α : Type} (l : List α) (le : α → α → Bool) (f : α → ℕ) :
    ((l.mergeSort le).map f).sum = (l.map f).sum :=
  ((List.mergeSort_perm l le).map f).sum_eq

theorem stackFold_snd (L : List (Column × ℕ × ℕ)) (acc : Array (Column × ℕ × ℕ × ℕ) × ℕ) :
    (L.foldl (fun (acc : Array (Column × ℕ × ℕ × ℕ) × ℕ) (x : Column × ℕ × ℕ) ↦
      (acc.1.push (x.1, x.2.1, x.2.2, acc.2), acc.2 + 2 ^ x.2.2)) acc).2 =
      acc.2 + (L.map fun p ↦ 2 ^ p.2.2).sum := by
  induction L generalizing acc with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    omega

theorem pieces_words (cols : List (Column × ℕ × Bool)) :
    ((cols.flatMap fun (x : Column × ℕ × Bool) ↦
      (List.range (if x.2.2 = true then 3 else 1)).map fun limb ↦ (x.1, limb, x.2.1)).map
        fun p ↦ 2 ^ p.2.2).sum = pieceWords cols := by
  induction cols with
  | nil => rfl
  | cons c cols ih =>
    obtain ⟨col, v, e⟩ := c
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
    simp only [pieceWords, List.map_cons, List.sum_cons]
    cases e <;> simp [List.range_succ]
    omega

/-- **A stack's variables are its pieces' words'**, the sort aside: `max (⌈log₂ max(S, 2)⌉) 15`. -/
theorem stackLayout_vars (cols : List (Column × ℕ × Bool)) :
    (StackLayout.new cols).vars = max (log2Ceil (max (pieceWords cols) 2)) 15 := by
  unfold StackLayout.new
  dsimp only
  rw [stackFold_snd, sum_map_mergeSort, pieces_words, zero_add]

/-! ### The heap's height and blocks from the unsorted used blocks -/

/-- `HeapLayout::new`'s used blocks, before the sort. -/
def heapUsed (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) : List (Leaves × ℕ) :=
  [(.memory, logMemory), (.bytecode, logBytecode)] ++
    (List.range tableLogHeights.length).map fun t ↦ (.table t, tableLogHeights.getD t 0)

/-- The used blocks' leaves. -/
def heapTotal (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) : ℕ :=
  ((heapUsed logMemory logBytecode tableLogHeights).map fun x ↦ 2 ^ x.2).sum

theorem heapFold (q : Block → ℕ) (hq : ∀ l r p p', q ⟨l, r, p⟩ = q ⟨l, r, p'⟩) (base : ℕ)
    (L : List (Leaves × ℕ)) (acc : Array Block × ℕ) :
    ((L.foldl (fun (acc : Array Block × ℕ) (x : Leaves × ℕ) ↦
      (acc.1.push ⟨x.1, x.2, base + acc.2⟩, acc.2 + 2 ^ x.2)) acc).1.toList.map q).sum =
        (acc.1.toList.map q).sum + (L.map fun x ↦ q ⟨x.1, x.2, 0⟩).sum ∧
      (L.foldl (fun (acc : Array Block × ℕ) (x : Leaves × ℕ) ↦
        (acc.1.push ⟨x.1, x.2, base + acc.2⟩, acc.2 + 2 ^ x.2)) acc).2 =
        acc.2 + (L.map fun x ↦ 2 ^ x.2).sum := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (acc.1.push ⟨x.1, x.2, base + acc.2⟩, acc.2 + 2 ^ x.2)
    refine ⟨?_, ?_⟩
    · rw [h1]
      simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, hq x.1 x.2 (base + acc.2) 0]
      omega
    · rw [h2]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **The heap's height** from the unsorted used blocks: `⌈log₂ Σ 2^r⌉ + 1`. -/
theorem heapLayout_h (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) :
    (HeapLayout.new logMemory logBytecode tableLogHeights).h =
      log2Ceil (heapTotal logMemory logBytecode tableLogHeights) + 1 := by
  unfold HeapLayout.new
  dsimp only
  rw [sum_map_mergeSort]
  rfl

/-- **A sum over the heap's blocks** of anything that reads only a block's leaves and size: the unsorted used
blocks', then the unused blocks' (from the used blocks' total). -/
theorem heapLayout_blocks_sum (q : Block → ℕ) (hq : ∀ l r p p', q ⟨l, r, p⟩ = q ⟨l, r, p'⟩)
    (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) :
    ((HeapLayout.new logMemory logBytecode tableLogHeights).blocks.map q).sum =
      ((heapUsed logMemory logBytecode tableLogHeights).map fun x ↦ q ⟨x.1, x.2, 0⟩).sum +
      ((unusedBlocks (2 ^ log2Ceil (heapTotal logMemory logBytecode tableLogHeights))
        (heapTotal logMemory logBytecode tableLogHeights)).map q).sum := by
  unfold HeapLayout.new
  dsimp only
  rw [List.map_append, List.sum_append, (heapFold q hq _ _ _).1, (heapFold q hq _ _ _).2]
  simp only [List.map_nil, List.sum_nil, zero_add, sum_map_mergeSort]
  rfl

/-! ### `C2`'s words -/

/-- **A heap block's leaf quotient's words** in `C2`: its `leafDegree`'s chunks, `E`-valued; none for an unused
block. -/
def leafWords (b : Block) : ℕ :=
  match Shape.leafDegree b with
  | none => 0
  | some d => ((chunks (d + 1)).map fun e ↦ 3 * 2 ^ e).sum

theorem leafWords_position (l : Leaves) (r p p' : ℕ) : leafWords ⟨l, r, p⟩ = leafWords ⟨l, r, p'⟩ := rfl

theorem sum_zip_range_fst {α : Type} (L : List α) (g : α → ℕ) :
    ((L.zip (List.range L.length)).map fun x ↦ g x.1).sum = (L.map g).sum := by
  have h : (L.zip (List.range L.length)).map (fun x ↦ g x.1) =
      ((L.zip (List.range L.length)).map Prod.fst).map g := by
    rw [List.map_map]
    rfl
  rw [h, List.map_fst_zip (by simp)]

theorem sum_map_flatMap {α β : Type} (L : List α) (F : α → List β) (g : β → ℕ) :
    ((L.flatMap F).map g).sum = (L.map fun x ↦ ((F x).map g).sum).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- **`C2`'s words**: the heap's and the tree quotient's (`E`-valued, `h`, `h`, `0` variables), the constraint
quotient's chunks, and the heap blocks' leaf quotients. -/
theorem c2_pieceWords (s : Shape) :
    pieceWords s.c2Columns =
      3 * 2 ^ s.heap.h + 3 * 2 ^ s.heap.h + 3 * 2 ^ 0 +
        ((chunks (s.constraintDegree + 1)).map fun e ↦ 3 * 2 ^ e).sum + (s.heap.blocks.map leafWords).sum := by
  unfold Shape.c2Columns
  dsimp only
  rw [pieceWords_append, pieceWords_append]
  congr 1
  · simp only [pieceWords, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_map,
      Function.comp_def, ite_true]
    rw [sum_zip_range_fst (chunks (s.constraintDegree + 1)) fun e ↦ 3 * 2 ^ e]
    omega
  · rw [pieceWords, sum_map_flatMap, ← sum_zip_range_fst s.heap.blocks leafWords]
    congr 1
    refine List.map_congr_left fun x _ ↦ ?_
    unfold leafWords
    cases h : Shape.leafDegree x.1 with
    | none => rfl
    | some d =>
      simp only [List.map_map, Function.comp_def, ite_true]
      exact sum_zip_range_fst _ fun e ↦ 3 * 2 ^ e

/-! ### The reference shape -/

/-- `C1`'s columns (`layouts`' `c1`). -/
def c1Columns (shape : Shape) : List (Column × ℕ × Bool) :=
  let heights := shape.heights
  [(.qflock, heights.getD opBlake2s 0 + 8, false)] ++
    tables.flatMap (fun t ↦
      let h := heights.getD t.opcode 0
      (List.range t.width).map (fun c ↦ (Column.table t.opcode c, h, false)) ++
        [(.inverse t.opcode, h, false)]) ++
    (List.range 4).map (fun k ↦ (Column.memory k, shape.logMemory, false)) ++
    [(.bytecodeFinal, shape.logBytecode, false)]

/-- The setup's columns (`layouts`' `setup`). -/
def setupColumns (shape : Shape) : List (Column × ℕ × Bool) :=
  [(.bytecodeTuple, shape.logBytecode + 4, false), (.address, shape.logMemory, false)]

theorem layoutsOf_eq (s : Shape) :
    layoutsOf s = [(.c1, StackLayout.new (c1Columns s)), (.c2, StackLayout.new s.c2Columns),
      (.setup, StackLayout.new (setupColumns s))] := rfl

theorem reference_c1Vars : (StackLayout.new (c1Columns reference)).vars = 27 := by
  rw [stackLayout_vars]
  decide +kernel

theorem reference_setupVars : (StackLayout.new (setupColumns reference)).vars = 24 := by
  rw [stackLayout_vars]
  decide +kernel

theorem reference_c2Vars : (StackLayout.new reference.c2Columns).vars = 27 := by
  rw [stackLayout_vars, c2_pieceWords, Shape.heap, heapLayout_h,
    heapLayout_blocks_sum leafWords (fun l r p p' ↦ leafWords_position l r p p')]
  decide +kernel

/-- **The reference shape's three stacks have `27`, `27`, `24` variables.** -/
theorem reference_vars : (layoutsOf reference).map (·.2.vars) = [27, 27, 24] := by
  rw [layoutsOf_eq]
  simp only [List.map_cons, List.map_nil, reference_c1Vars, reference_c2Vars, reference_setupVars]

theorem layoutWordVars_layoutWord (s : Shape) (code vars placed : ℕ) :
    layoutWordVars (layoutWord s code vars placed) = vars % 256 := rfl

/-- **The five `PCS_OPEN` layout words name `27, 27, 24, 28, 28` variables.** -/
theorem reference_wordVars : (layoutWords reference).map layoutWordVars = [27, 27, 24, 28, 28] := by
  unfold layoutWords
  simp only [List.map_cons, List.map_nil, layoutWordVars_layoutWord]
  rw [layoutsOf_eq]
  show [(StackLayout.new (c1Columns reference)).vars % 256, (StackLayout.new reference.c2Columns).vars % 256,
    (StackLayout.new (setupColumns reference)).vars % 256, matrixVars % 256, matrixVars % 256] = _
  rw [reference_c1Vars, reference_c2Vars, reference_setupVars]
  rfl

end UniComplete

/-- info: 'UniComplete.reference_vars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.reference_vars

/-- info: 'UniComplete.reference_wordVars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.reference_wordVars
