-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The programs are `formal/UniStatement`'s
-- (`Verifier.lean`: `constraintRelation`, `heapRelations`, `Shape.c2Columns`; `Heap.lean`).
import UniSound.CodeTables

/-!
# `C2`'s columns are the shape's

The verifier computes `C2`'s columns during the run (`constraintRelation`'s quotient degree,
`heapRelations`' leaf quotients' chunks); they are the shape's (`Shape.c2Columns`, which the layout
words and the batch's variables are built from), whatever the values read:

* `constraintRelation_snd`: the constraint quotient's degree is `Shape.constraintDegree`;
* `heapRelations_snd`: the leaf quotients' columns are the shape's, given each table's part has
  its table's degrees (`tableDegrees`) and the heap's blocks are the shape's tables
  (`heap_blocks_tables`).
-/

namespace UniSound

open UniStatement LeanVM.Parameters

/-! ## Loops in `Id` -/

/-- **A loop in `Id` that always continues, projected**: a component that evolves on its own. -/
theorem forIn_id_proj {α β γ : Type} (proj : β → γ) (g : γ → α → γ) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, ∃ b', f a b = pure (ForInStep.yield b') ∧ proj b' = g (proj b) a) :
    ∀ (l : List α) (init : β), proj (forIn l init f).run = l.foldl g (proj init)
  | [], init => rfl
  | a :: l, init => by
    obtain ⟨b', hb, hp⟩ := hf a init
    rw [List.forIn_cons, hb, List.foldl_cons, ← hp]
    exact forIn_id_proj proj g f hf l b'

/-- **A loop in `Id` that always continues, an invariant.** -/
theorem forIn_id_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, P b → ∃ b', f a b = pure (ForInStep.yield b') ∧ P b') :
    ∀ (l : List α) (init : β), P init → P (forIn l init f).run
  | [], init, h => h
  | a :: l, init, h => by
    obtain ⟨b', hb, hp⟩ := hf a init h
    rw [List.forIn_cons, hb]
    exact forIn_id_inv P f hf l b' hp

theorem foldl_zip_fst {α β γ : Type} (g : γ → α → γ) :
    ∀ (l : List α) (m : List β) (c : γ), l.length ≤ m.length →
      (l.zip m).foldl (fun c x => g c x.1) c = l.foldl g c
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | a :: l, b :: m, c, h => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    exact foldl_zip_fst g l m _ (by simp at h; omega)

/-! ## The constraint quotient's degree -/

/-- `Shape.constraintDegree`'s step over a table. -/
def cdStep (shape : Shape) (d : ℕ) (table : Table) : ℕ :=
  let r := shape.heights.getD table.opcode 0
  let n := 2 ^ r
  let d := if table.opcode = opJump then max d (degree n 2) else d
  let d := max d (degree ((n - 1) * (1 + table.countColumns.length)) n)
  if table.opcode = opBlake2s then max d (degree (r * (n / 2)) n) else d

theorem constraintDegree_eq (shape : Shape) :
    shape.constraintDegree = max (tables.foldl (cdStep shape) 0) (degree (2 ^ shape.logMemory) 3) :=
  rfl

/-- **The constraint quotient's degree is the shape's**, for parts of every table. -/
theorem constraintRelation_snd (shape : Shape) (parts : List TablePart) (pw : List E) (g t cv : E)
    (w : List E) (h : tables.length ≤ parts.length) :
    (constraintRelation shape parts pw g t cv w).2 = shape.constraintDegree := by
  unfold constraintRelation
  simp only [Id.run_bind, Id.run_pure]
  rw [constraintDegree_eq]
  refine (congrArg (fun d => max d (degree (2 ^ shape.logMemory) 3))
    (forIn_id_proj (fun s : E × Array Term × E × ℕ => s.2.2.2) (fun d x => cdStep shape d x.1) _ ?_
      _ _)).trans ?_
  · intro x s
    have hjb : opJump ≠ opBlake2s := by decide
    have hbj : opBlake2s ≠ opJump := by decide
    by_cases h1 : x.1.opcode = opJump <;> by_cases h2 : x.1.opcode = opBlake2s <;>
      simp only [h1, h2, ite_true, ite_false] <;>
      exact ⟨_, rfl, by simp [cdStep, h1, h2, hjb, hbj]⟩
  · simp only [foldl_zip_fst _ _ _ _ h]

/-! ## The leaf quotients' columns -/

/-- A heap block's leaf quotient's degree in the run (`heapRelations`), from the tables' parts. -/
def leafDegreeRun (parts : List TablePart) (block : Block) : Option ℕ :=
  match block.leaves with
  | .unused => none
  | .memory => some (degree (2 * (2 ^ block.r - 1)) (2 ^ block.r))
  | .bytecode => some (degree (2 * (2 ^ block.r - 1)) (2 ^ block.r))
  | .table t => some (degree (max (parts.getD t default).pullDegree (parts.getD t default).pushDegree *
      (2 ^ block.r - 1) + (2 ^ block.r - Shape.leastRows block.r)) (2 ^ block.r))

/-- A heap block's leaf quotient's columns, its chunks. -/
def leafColsOf (d : Option ℕ) (index : ℕ) : List (Column × ℕ × Bool) :=
  match d with
  | none => []
  | some d => ((chunks (d + 1)).zip (List.range (chunks (d + 1)).length)).map fun y =>
      (Column.leafQuotient index y.2, y.1, true)

theorem foldl_append_flatMap {α β : Type} (f : α → List β) :
    ∀ (l : List α) (c : List β), l.foldl (fun c x => c ++ f x) c = c ++ l.flatMap f
  | [], c => by simp
  | x :: l, c => by
    rw [List.foldl_cons, foldl_append_flatMap f l, List.flatMap_cons, List.append_assoc]

/-- **The leaf quotients' columns in the run.** -/
theorem heapRelations_snd (shape : Shape) (active : List E) (parts : List TablePart) (weights : Array E)
    (beta hv cv mp mpu bp bpu : E) (w : List E) (cc : List ℕ) :
    (heapRelations shape active parts weights beta hv cv mp mpu bp bpu w cc).2 =
      (shape.heap.blocks.zip (List.range shape.heap.blocks.length)).flatMap fun x =>
        leafColsOf (leafDegreeRun parts x.1) x.2 := by
  unfold heapRelations
  simp only [Id.run_bind, Id.run_pure]
  refine (forIn_id_proj (fun s : Array Relation × Array (Column × ℕ × Bool) => s.2.toList)
    (fun c x => c ++ leafColsOf (leafDegreeRun parts x.1) x.2) _ ?_ _ _).trans ?_
  · intro x s
    rcases x with ⟨block, index⟩
    cases hl : block.leaves <;> simp only [] <;>
      exact ⟨_, rfl, by simp [leafColsOf, leafDegreeRun, hl]⟩
  · rw [foldl_append_flatMap]
    rfl

/-! ## The parts' degrees -/

/-- **A consumed fold, projected**: a component that evolves on its own, whatever the values. -/
theorem consumeFold_proj {α β γ : Type} (k : α → ℕ) (g : α → β → List E → β) (proj : β → γ)
    (g' : γ → α → γ) (h : ∀ x s vs, proj (g x s vs) = g' (proj s) x) :
    ∀ (l : List α) (init : β) (vs : List E), proj (consumeFold k g l init vs) = l.foldl g' (proj init)
  | [], _, _ => rfl
  | x :: l, init, vs => by
    simp only [consumeFold, List.foldl_cons]
    rw [consumeFold_proj k g proj g' h l, h]

theorem consume_flush_degrees (t : Table) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) (l : List (List Form × List Form)) (init : Array Relation × E × E × ℕ × ℕ)
    (vs : List E) :
    ((consumeFold (flushReads weights sent) (flushStep t pt weights beta sent) l init vs).2.2.2.1,
      (consumeFold (flushReads weights sent) (flushStep t pt weights beta sent) l init vs).2.2.2.2) =
      l.foldl (fun acc x => (acc.1 + tupleDegree x.1, acc.2 + tupleDegree x.2)) (init.2.2.2.1, init.2.2.2.2) :=
  consumeFold_proj (flushReads weights sent) (flushStep t pt weights beta sent)
    (fun s : Array Relation × E × E × ℕ × ℕ => (s.2.2.2.1, s.2.2.2.2))
    (fun acc x => (acc.1 + tupleDegree x.1, acc.2 + tupleDegree x.2)) (fun _ _ _ => rfl) l init vs

/-- **A table's part has its table's degrees** (`tableDegrees`), whatever the values. -/
theorem tablePartPure_degrees (t : Table) (lh : ℕ) (weights : Array E) (beta : E) (w vs : List E) :
    ((tablePartPure t lh weights beta w vs).1.pullDegree, (tablePartPure t lh weights beta w vs).1.pushDegree) =
      tableDegrees t := by
  unfold tablePartPure
  simp only []
  rw [consume_flush_degrees]
  rfl

/-! ## The heap's blocks are the shape's tables -/

theorem foldl_blocks_mem (base : ℕ) : ∀ (l : List (Leaves × ℕ)) (acc : Array Block × ℕ) (b : Block),
    b ∈ (l.foldl (fun (acc : Array Block × ℕ) (x : Leaves × ℕ) =>
      (acc.1.push ⟨x.1, x.2, base + acc.2⟩, acc.2 + 2 ^ x.2)) acc).1.toList →
      b ∈ acc.1.toList ∨ ∃ x ∈ l, b.leaves = x.1
  | [], acc, b, h => Or.inl h
  | x :: l, acc, b, h => by
    rw [List.foldl_cons] at h
    rcases foldl_blocks_mem base l _ b h with h1 | ⟨y, hy, hb⟩
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h1
      rcases h1 with h1 | rfl
      · exact Or.inl h1
      · exact Or.inr ⟨x, List.mem_cons_self .., rfl⟩
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hb⟩

theorem unusedBlocks_unused (base offset : ℕ) : ∀ b ∈ unusedBlocks base offset, b.leaves = .unused := by
  unfold unusedBlocks
  simp only [Id.run_bind, Id.run_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_id_inv (fun s : Array Block × ℕ => ∀ b ∈ s.1.toList, b.leaves = .unused) _ ?_ _ _
    (by simp)
  intro i s hs
  by_cases h : s.2 < base
  · simp only [h, ite_true]
    refine ⟨_, rfl, ?_⟩
    intro b hb
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hs b hb
    · rfl
  · simp only [h, ite_false]
    exact ⟨_, rfl, hs⟩

/-- **The heap's blocks of tables are the shape's tables.** -/
theorem heap_blocks_tables (logMemory logBytecode : ℕ) (hs : List ℕ) :
    ∀ b ∈ (HeapLayout.new logMemory logBytecode hs).blocks, ∀ t, b.leaves = .table t → t < hs.length := by
  intro b hb t ht
  unfold HeapLayout.new at hb
  simp only [] at hb
  rw [List.mem_append] at hb
  rcases hb with hb | hb
  · rcases foldl_blocks_mem _ _ _ b hb with h | ⟨x, hx, hbx⟩
    · simp at h
    · rw [List.mem_mergeSort] at hx
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
        or_false] at hx
      rcases hx with (rfl | rfl) | ⟨t', ht', rfl⟩
      · rw [ht] at hbx
        cases hbx
      · rw [ht] at hbx
        cases hbx
      · rw [ht] at hbx
        cases hbx
        exact ht'
  · have h := unusedBlocks_unused _ _ b hb
    rw [h] at ht
    cases ht

/-! ## The tables' parts and `C2`'s columns -/

/-- `reduceWith`'s tables loop (step 4): each table's relations appended, its part pushed. -/
def tablesStep (heights : List ℕ) (weights : Array E) (beta : E) (w : List E) (table : Table)
    (s : Array Relation × Array TablePart) (vs : List E) : Array Relation × Array TablePart :=
  (s.1 ++ (tablePartPure table (heights.getD table.opcode 0) weights beta w vs).2.toArray,
    s.2.push (tablePartPure table (heights.getD table.opcode 0) weights beta w vs).1)

theorem foldl_append_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (c : List β), l.foldl (fun c x => c ++ [f x]) c = c ++ l.map f
  | [], c => by simp
  | x :: l, c => by rw [List.foldl_cons, foldl_append_map f l, List.map_cons, List.append_assoc]; rfl

/-- **The tables' parts have the tables' degrees**, whatever the values. -/
theorem tables_parts_degrees (heights : List ℕ) (weights : Array E) (beta : E) (w vs : List E) :
    (consumeFold tableReads (tablesStep heights weights beta w) tables (#[], #[]) vs).2.toList.map
        (fun p => (p.pullDegree, p.pushDegree)) = tables.map tableDegrees := by
  rw [consumeFold_proj tableReads (tablesStep heights weights beta w)
    (fun s : Array Relation × Array TablePart => s.2.toList.map fun p => (p.pullDegree, p.pushDegree))
    (fun c table => c ++ [tableDegrees table]) ?_ tables (#[], #[]) vs]
  · rw [foldl_append_map]
    rfl
  · intro x s vs
    simp only [tablesStep, Array.toList_push, List.map_append, List.map_cons, List.map_nil,
      tablePartPure_degrees]

theorem leafDegreeRun_eq (parts : List TablePart)
    (hparts : parts.map (fun p => (p.pullDegree, p.pushDegree)) = tables.map tableDegrees) (b : Block)
    (hb : ∀ t, b.leaves = .table t → t < tables.length) : leafDegreeRun parts b = Shape.leafDegree b := by
  unfold leafDegreeRun Shape.leafDegree
  cases hl : b.leaves with
  | unused => rfl
  | memory => rfl
  | bytecode => rfl
  | table t =>
    have ht := hb t hl
    have hlen : parts.length = tables.length := by
      simpa using congrArg List.length hparts
    have h1 := congrArg (fun l => l.getD t (0, 0)) hparts
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at h1
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem ht] at h1
    simp only [Option.map_some, Option.getD_some] at h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < parts.length),
      List.getElem?_eq_getElem ht, Option.getD_some]
    rw [← h1]

theorem flatMap_congr_mem {α β : Type} (f g : α → List β) :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem f g l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- **`C2`'s columns in the run are the shape's.** -/
theorem c2Columns_run (shape : Shape) (hlen : shape.heights.length = tables.length)
    (parts : List TablePart)
    (hparts : parts.map (fun p => (p.pullDegree, p.pushDegree)) = tables.map tableDegrees)
    (active pw : List E) (g t cv : E) (weights : Array E) (beta hv mp mpu bp bpu : E) (w : List E) :
    [(Column.heap, shape.heap.h, true), (Column.treeQuotient 0, shape.heap.h, true),
        (Column.treeQuotient 1, 0, true)] ++
      List.map (fun x => (Column.constraintQuotient x.2, x.1, true))
        ((chunks ((constraintRelation shape parts pw g t cv w).2 + 1)).zip
          (List.range (chunks ((constraintRelation shape parts pw g t cv w).2 + 1)).length)) ++
      (heapRelations shape active parts weights beta hv cv mp mpu bp bpu w
        (chunks ((constraintRelation shape parts pw g t cv w).2 + 1))).2 = shape.c2Columns := by
  have hpl : tables.length ≤ parts.length := by
    have := congrArg List.length hparts
    simp at this
    omega
  rw [constraintRelation_snd _ _ _ _ _ _ _ hpl, heapRelations_snd]
  unfold Shape.c2Columns
  congr 1
  refine flatMap_congr_mem _ _ _ fun x hx => ?_
  have hb := List.of_mem_zip hx
  rw [leafDegreeRun_eq parts hparts x.1 (fun t ht => by
    have := heap_blocks_tables shape.logMemory shape.logBytecode shape.heights x.1 hb.1 t ht
    omega)]
  rfl

/-! ## Every commitment has a relation -/

theorem combine_isSome (rels : List Relation) (c : Commitment) (rho : E)
    (h : ∃ r ∈ rels, r.commitment = c) : (combine rels c rho).isSome = true := by
  obtain ⟨r, hr, hc⟩ := h
  unfold combine
  have hne : (rels.filter fun x => x.commitment == c).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff_exists_mem]
    exact ⟨r, List.mem_filter.mpr ⟨hr, by simp [hc]⟩⟩
  simp only [hne, Bool.false_eq_true, ite_false, Option.isSome_some]

/-- **One claim per commitment**, when each has a relation. -/
theorem combined_length (rels : List Relation) (rho : E) (h1 : ∃ r ∈ rels, r.commitment = .c1)
    (h2 : ∃ r ∈ rels, r.commitment = .c2) (h3 : ∃ r ∈ rels, r.commitment = .setup) :
    (commitments.filterMap fun c => (combine rels c rho).map fun x => (c, x)).length = 3 := by
  obtain ⟨x1, hx1⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c1 rho h1)
  obtain ⟨x2, hx2⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c2 rho h2)
  obtain ⟨x3, hx3⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .setup rho h3)
  simp [commitments, hx1, hx2, hx3]

/-- The heap's relations start with `T(t)`'s, on `C2`. -/
theorem heapRelations_mem (shape : Shape) (active : List E) (parts : List TablePart) (weights : Array E)
    (beta hv cv mp mpu bp bpu : E) (w : List E) (cc : List ℕ) :
    Relation.equal .heap (w.take shape.heap.h) hv ∈
      (heapRelations shape active parts weights beta hv cv mp mpu bp bpu w cc).1 := by
  unfold heapRelations
  simp only [Id.run_bind, Id.run_pure]
  rw [Array.toList_push, List.mem_append]
  left
  refine forIn_id_inv (fun s : Array Relation × Array (Column × ℕ × Bool) =>
    Relation.equal .heap (w.take shape.heap.h) hv ∈ s.1.toList) _ ?_ _ _ (by simp)
  intro x s hs
  rcases x with ⟨block, index⟩
  cases hl : block.leaves <;> simp only [] <;>
    exact ⟨_, rfl, by simp only [Array.toList_push, List.mem_append]; exact Or.inl hs⟩

end UniSound
