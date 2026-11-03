-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHCols
import UniComplete.AlgCTerm

/-!
# A term's value on `C2` (milestone 4)

`C2`'s stack is `placeStack` of `StackLayout.new (Shape.c2Columns shape)` (`c2Stack_eq`, `c2Layout_eq`). Its column
names are pairwise distinct (`c2Names_nodup`: the heap, the tree quotient's two chunks, the constraint quotient's
chunks, each used block's leaf quotient's chunks, each block by its index), so a term on a `C2` column listed with
`(v, true)` is `k ·` the multilinear extension of its `E` words at the point (**`termEval_c2col`**, from the column
agent's `AlgC.termEval_new_E`). `chunksB_length`, `chunksB_size`: a quotient's chunks, one per size, chunk `c` of
`2^(e_c)` words. `quotientTerms_value`: the terms of a quotient's chunks add up to `scale ·` the chunks' value
(`AlgC.chunksValue`) for the sizes `chunks` returns.
-/

namespace UniComplete.AlgH

open UniStatement LeanVM.Parameters
open UniComplete.Domain (ite_pos_of ite_neg_of)

/-! ### `C2`'s layout and stack -/

/-- `C2`'s words (`c2DataOf`'s `c2Words`), from its data. -/
def c2Words' (c2 : C2Data) : Column → ℕ → Array K := fun column limb ↦
  match column with
  | .heap => limbWords c2.heapB limb
  | .treeQuotient c => limbWords (c2.treeChunks.getD c #[]) limb
  | .constraintQuotient c => limbWords (c2.constraintChunks.getD c #[]) limb
  | .leafQuotient b c => match c2.leafChunks.find? (·.1 == b) with
    | some (_, _, parts) => limbWords (parts.getD c #[]) limb
    | none => #[]
  | _ => #[]

theorem c2Layout_eq (shape : Shape) :
    ((layoutsOf shape).lookup .c2).getD default = StackLayout.new (Shape.c2Columns shape) := rfl

theorem c2Stack_eq (tr : Trace) (weights : Array E) (beta gamma : E) :
    (c2DataOf tr weights beta gamma).stack =
      placeStack (StackLayout.new (Shape.c2Columns tr.shape)) (c2Words' (c2DataOf tr weights beta gamma)) := rfl

theorem layoutIn_c2 (shape : Shape) (cols : List (Column × ℕ × Bool)) :
    layoutIn (layouts shape cols) .c2 = StackLayout.new cols := rfl

/-! ### `C2`'s names are distinct -/

theorem map_snd_zip_range {α : Type} (l : List α) : (l.zip (List.range l.length)).map Prod.snd = List.range l.length :=
  List.map_snd_zip (by simp)

theorem map_zip_range_snd {α β : Type} (l : List α) (f : ℕ → β) :
    (l.zip (List.range l.length)).map (fun y ↦ f y.2) = (List.range l.length).map f := by
  have := congrArg (List.map f) (map_snd_zip_range l)
  rwa [List.map_map] at this

theorem zip_range_pairwise {α : Type} (l : List α) : (l.zip (List.range l.length)).Pairwise (fun a b ↦ a.2 < b.2) := by
  have h := List.pairwise_lt_range (n := l.length)
  rw [← map_snd_zip_range l, List.pairwise_map] at h
  exact h

theorem shapeBlockCols_fst (x : Block × ℕ) : (shapeBlockCols x).map Prod.fst =
    match Shape.leafDegree x.1 with
    | none => []
    | some d => (List.range (chunks (d + 1)).length).map (Column.leafQuotient x.2) := by
  unfold shapeBlockCols
  cases Shape.leafDegree x.1 with
  | none => rfl
  | some d =>
    dsimp only
    rw [List.map_map]
    exact map_zip_range_snd _ _

theorem mem_shapeBlockCols_fst {x : Block × ℕ} {col : Column} (h : col ∈ (shapeBlockCols x).map Prod.fst) :
    ∃ c, col = Column.leafQuotient x.2 c := by
  rw [shapeBlockCols_fst] at h
  cases hd : Shape.leafDegree x.1 with
  | none => rw [hd] at h; exact absurd h List.not_mem_nil
  | some d =>
    rw [hd] at h
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp h
    exact ⟨c, rfl⟩

theorem c2Names_nodup (shape : Shape) : ((Shape.c2Columns shape).map Prod.fst).Nodup := by
  rw [c2Columns_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_flatMap, List.map_map]
  have hB : ((chunks (shape.constraintDegree + 1)).zip (List.range (chunks (shape.constraintDegree + 1)).length)).map
      (Prod.fst ∘ fun x ↦ (Column.constraintQuotient x.2, x.1, true)) =
      (List.range (chunks (shape.constraintDegree + 1)).length).map Column.constraintQuotient := by
    exact map_zip_range_snd _ _
  rw [hB]
  have hA : [Column.heap, Column.treeQuotient 0, Column.treeQuotient 1].Nodup := by decide
  have hBn : ((List.range (chunks (shape.constraintDegree + 1)).length).map Column.constraintQuotient).Nodup :=
    (List.nodup_range).map fun a b h ↦ Column.constraintQuotient.inj h
  have hCn : ((shape.heap.blocks.zip (List.range shape.heap.blocks.length)).flatMap
      fun x ↦ (shapeBlockCols x).map Prod.fst).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun x _ ↦ ?_, (zip_range_pairwise _).imp fun {a b} hab ↦ ?_⟩
    · rw [shapeBlockCols_fst]
      cases Shape.leafDegree x.1 with
      | none => exact List.nodup_nil
      | some d => exact (List.nodup_range).map fun a b h ↦ (Column.leafQuotient.inj h).2
    · intro col ha hb
      obtain ⟨c, rfl⟩ := mem_shapeBlockCols_fst ha
      obtain ⟨c', hc'⟩ := mem_shapeBlockCols_fst hb
      have := (Column.leafQuotient.inj hc').1
      omega
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨hA, hBn, ?_⟩, hCn, ?_⟩
  · intro a ha b hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact Column.noConfusion
  · intro a ha b hb
    obtain ⟨x, -, hbx⟩ := List.mem_flatMap.mp hb
    obtain ⟨c, rfl⟩ := mem_shapeBlockCols_fst hbx
    rcases List.mem_append.mp ha with ha | ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> exact Column.noConfusion
    · obtain ⟨c', -, rfl⟩ := List.mem_map.mp ha
      exact Column.noConfusion

/-- **A term on a `C2` column** listed once with `(v, true)`: `k ·` the extension of its `E` words. -/
theorem termEval_c2col {shape : Shape} (data : Column → ℕ → Array K) {column : Column} {v : ℕ}
    (hmem : (column, v, true) ∈ Shape.c2Columns shape) (hq : ∀ j, column ≠ .qflockSlot j) {D : Array E}
    (hD : ∀ l < 3, data column l = limbWords D l) (hsize : D.size = 2 ^ v) {pt : List E} (hpt : pt.length = v)
    (rm : Option (List E)) (k : E) :
    termEval (StackLayout.new (Shape.c2Columns shape)) (placeStack (StackLayout.new (Shape.c2Columns shape)) data) rm
      (term column pt k) = k * multilinearEval D.toList pt := by
  have hnd := c2Names_nodup shape
  refine AlgC.termEval_new_E (List.count_eq_one_of_mem hnd (List.mem_map_of_mem hmem)) (fun p hp hp1 ↦ ?_) hq data
    hD hsize hpt rm k
  have := List.inj_on_of_nodup_map hnd hp hmem hp1
  rw [this]

/-! ### Chunks -/

theorem chunksB_length {q : Poly} {sizes : List ℕ} (hs : AlgC.ChunkShape sizes) :
    (chunksB q sizes).length = sizes.length := by
  rcases hs with ⟨a, rfl⟩ | ⟨a, b, rfl, -⟩ | ⟨a, b, c, rfl, -, -⟩
  · rw [AlgC.chunksB_one]; rfl
  · rw [AlgC.chunksB_two]; rfl
  · rw [AlgC.chunksB_three]; rfl

theorem chunksB_size {q : Poly} {sizes : List ℕ} (hs : AlgC.ChunkShape sizes) {c : ℕ} (hc : c < sizes.length) :
    ((chunksB q sizes).getD c #[]).size = 2 ^ sizes.getD c 0 := by
  rcases hs with ⟨a, rfl⟩ | ⟨a, b, rfl, -⟩ | ⟨a, b, d, rfl, -, -⟩
  · rw [AlgC.chunksB_one]
    simp at hc
    subst hc
    simp [AlgC.subsetSumsE_size, AlgC.chunkAt_size]
  · rw [AlgC.chunksB_two]
    simp at hc
    interval_cases c <;> simp [AlgC.subsetSumsE_size, AlgC.chunkAt_size]
  · rw [AlgC.chunksB_three]
    simp at hc
    interval_cases c <;> simp [AlgC.subsetSumsE_size, AlgC.chunkAt_size]

/-- **A quotient's chunks' terms add up to `scale ·` the chunks' value.** -/
theorem quotientTerms_value (column : ℕ → Column) {sizes : List ℕ} (hs : AlgC.ChunkShape sizes) (w : List E)
    (scale : E) (f : Term → E) {cs : List (Array E)} (hcs : cs.length = sizes.length)
    (hf : ∀ c < sizes.length, ∀ k, f (term (column c) (w.take (sizes.getD c 0)) k) =
      k * evalB (cs.getD c #[]) (sizes.getD c 0) w) :
    ((quotientTerms column sizes w scale).map f).sum = scale * AlgC.chunksValue cs sizes w := by
  rcases hs with ⟨a, rfl⟩ | ⟨a, b, rfl, -⟩ | ⟨a, b, d, rfl, -, -⟩
  · obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp (hcs.trans rfl)
    have h0 : ∀ k, f (term (column 0) (w.take a) k) = k * evalB c0 a w := fun k ↦ hf 0 (by simp) k
    have hr : List.range [a].length = [0] := rfl
    unfold quotientTerms AlgC.chunksValue
    rw [hr]
    simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
      Array.toList_push, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, h0]
    ring
  · obtain ⟨c0, c1, rfl⟩ := List.length_eq_two.mp (hcs.trans rfl)
    have h0 : ∀ k, f (term (column 0) (w.take a) k) = k * evalB c0 a w := fun k ↦ hf 0 (by simp) k
    have h1 : ∀ k, f (term (column 1) (w.take b) k) = k * evalB c1 b w := fun k ↦ hf 1 (by simp) k
    have hr : List.range [a, b].length = [0, 1] := rfl
    unfold quotientTerms AlgC.chunksValue
    rw [hr]
    simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
      Array.toList_push, List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, h0, h1]
    ring
  · obtain ⟨c0, c1, c2, rfl⟩ := List.length_eq_three.mp (hcs.trans rfl)
    have h0 : ∀ k, f (term (column 0) (w.take a) k) = k * evalB c0 a w := fun k ↦ hf 0 (by simp) k
    have h1 : ∀ k, f (term (column 1) (w.take b) k) = k * evalB c1 b w := fun k ↦ hf 1 (by simp) k
    have h2 : ∀ k, f (term (column 2) (w.take d) k) = k * evalB c2 d w := fun k ↦ hf 2 (by simp) k
    have hr : List.range [a, b, d].length = [0, 1, 2] := rfl
    unfold quotientTerms AlgC.chunksValue
    rw [hr]
    simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
      Array.toList_push, List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, h0, h1, h2]
    ring

end UniComplete.AlgH
