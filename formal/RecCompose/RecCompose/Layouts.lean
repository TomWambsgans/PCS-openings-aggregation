-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Reference
import RecCompose.Bridge

/-!
# π1's calls' layout words are π1-rec3's

**`pi1CallsLayouts_of_real`**: `Pi1CallsLayouts D` at the real deployment. π1's calls are `Data.pi1Calls`, and their
layout words (word 1 of each, constants the Rust wrote) are π1-rec3's at the reference shape (`w1`, `UniStatement.
layoutWords`). `layoutWords` sorts (`StackLayout.new`'s `List.mergeSort`, well-founded: the kernel does not reduce it),
so the two numbers a word holds are taken off the sort first, as `UniComplete.stackLayout_vars` does for the variables:

* `stackLayout_words`: the words a stack's blocks fill are its pieces' (`UniComplete.pieceWords`), in any order;
* `C2`'s through `UniComplete.c2_pieceWords` and the heap's unsorted blocks (`heapLayout_h`, `heapLayout_blocks_sum`);

then the kernel compares the three 32-byte words (small terms: the shape's bytes, the hex strings).
-/

namespace RecCompose

open UniStatement UniComplete

/-- A fold that adds `g x` is a sum. -/
theorem foldl_add_eq {β : Type} (g : β → ℕ) (f : ℕ → β → ℕ) (hf : ∀ a x, f a x = a + g x) :
    ∀ (L : List β) (a : ℕ), L.foldl f a = a + (L.map g).sum
  | [], a => by simp
  | x :: L, a => by
    rw [List.foldl_cons, hf, foldl_add_eq g f hf L, List.map_cons, List.sum_cons]
    omega

theorem stackFold_fst (L : List (Column × ℕ × ℕ)) (acc : Array (Column × ℕ × ℕ × ℕ) × ℕ) :
    ((L.foldl (fun (acc : Array (Column × ℕ × ℕ × ℕ) × ℕ) (x : Column × ℕ × ℕ) ↦
      (acc.1.push (x.1, x.2.1, x.2.2, acc.2), acc.2 + 2 ^ x.2.2)) acc).1.toList.map fun b ↦ 2 ^ b.2.2.1) =
      (acc.1.toList.map fun b ↦ 2 ^ b.2.2.1) ++ L.map fun p ↦ 2 ^ p.2.2 := by
  induction L generalizing acc with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons, ih]
    simp

/-- **A stack's words are its pieces' words**, the sort aside. -/
theorem stackLayout_words (cols : List (Column × ℕ × Bool)) : (StackLayout.new cols).words = pieceWords cols := by
  unfold StackLayout.new StackLayout.words
  dsimp only
  rw [foldl_add_eq (fun b : Column × ℕ × ℕ × ℕ ↦ 2 ^ b.2.2.1) _ (fun a x ↦ by obtain ⟨_, _, _, _⟩ := x; rfl),
    stackFold_fst]
  simp only [List.map_nil, List.nil_append, zero_add]
  rw [sum_map_mergeSort, pieces_words]

theorem reference_c1Words : (StackLayout.new (c1Columns reference)).words = pieceWords (c1Columns reference) :=
  stackLayout_words _

theorem reference_setupWords :
    (StackLayout.new (setupColumns reference)).words = pieceWords (setupColumns reference) :=
  stackLayout_words _

/-- `C2`'s words at the reference shape, from the heap's unsorted blocks. -/
theorem reference_c2Words : (StackLayout.new reference.c2Columns).words =
    3 * 2 ^ (log2Ceil (heapTotal reference.logMemory reference.logBytecode reference.heights) + 1) +
      3 * 2 ^ (log2Ceil (heapTotal reference.logMemory reference.logBytecode reference.heights) + 1) + 3 * 2 ^ 0 +
      ((chunks (reference.constraintDegree + 1)).map fun e ↦ 3 * 2 ^ e).sum +
      (((heapUsed reference.logMemory reference.logBytecode reference.heights).map fun x ↦ leafWords ⟨x.1, x.2, 0⟩).sum +
        ((unusedBlocks (2 ^ log2Ceil (heapTotal reference.logMemory reference.logBytecode reference.heights))
          (heapTotal reference.logMemory reference.logBytecode reference.heights)).map leafWords).sum) := by
  rw [stackLayout_words, c2_pieceWords, Shape.heap, heapLayout_h,
    heapLayout_blocks_sum leafWords (fun l r p p' ↦ leafWords_position l r p p')]

/-- **π1-rec3's three layout words at the reference shape**, their numbers off the sort. -/
theorem w1_eq :
    w1 0 = layoutWord reference 0x5501 27 (pieceWords (c1Columns reference)) ∧
    w1 1 = layoutWord reference 0x5502 27
      (3 * 2 ^ (log2Ceil (heapTotal reference.logMemory reference.logBytecode reference.heights) + 1) +
        3 * 2 ^ (log2Ceil (heapTotal reference.logMemory reference.logBytecode reference.heights) + 1) + 3 * 2 ^ 0 +
        ((chunks (reference.constraintDegree + 1)).map fun e ↦ 3 * 2 ^ e).sum +
        (((heapUsed reference.logMemory reference.logBytecode reference.heights).map fun x ↦
            leafWords ⟨x.1, x.2, 0⟩).sum +
          ((unusedBlocks (2 ^ log2Ceil (heapTotal reference.logMemory reference.logBytecode reference.heights))
            (heapTotal reference.logMemory reference.logBytecode reference.heights)).map leafWords).sum)) ∧
    w1 2 = layoutWord reference 0x5503 24 (pieceWords (setupColumns reference)) := by
  refine ⟨?_, ?_, ?_⟩
  · show layoutWord reference 0x5501 (StackLayout.new (c1Columns reference)).vars
      (StackLayout.new (c1Columns reference)).words = _
    rw [reference_c1Vars, reference_c1Words]
  · show layoutWord reference 0x5502 (StackLayout.new reference.c2Columns).vars
      (StackLayout.new reference.c2Columns).words = _
    rw [reference_c2Vars, reference_c2Words]
  · show layoutWord reference 0x5503 (StackLayout.new (setupColumns reference)).vars
      (StackLayout.new (setupColumns reference)).words = _
    rw [reference_setupVars, reference_setupWords]

/-- `Data.pi1Calls`' layout words are π1-rec3's at the reference shape (kernel decisions on 32-byte words). -/
theorem data_pi1Calls_layouts : ∀ ci < 3, (RecStatement.Data.pi1Calls.getD ci []).getD 1 default =
    RecStatement.CallWord.const (w1 ci) := by
  obtain ⟨h0, h1, h2⟩ := w1_eq
  intro ci hci
  interval_cases ci
  · rw [h0]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h2]; decide +kernel

/-- **π1's calls' layout words are π1-rec3's**, at the real deployment. -/
theorem pi1CallsLayouts_of_real {D : RecStatement.RecDeployment} (hD : D.Real) : Pi1CallsLayouts D := by
  intro ci hci
  rw [hD.2.1]
  exact data_pi1Calls_layouts ci hci

end RecCompose

/-- info: 'RecCompose.pi1CallsLayouts_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1CallsLayouts_of_real
