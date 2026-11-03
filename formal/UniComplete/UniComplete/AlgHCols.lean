-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHRestrict
import UniComplete.AlgCRun

/-!
# The heap's relations, written out, and `C2`'s columns (milestone 4)

* **`heapRelations_eq`**: the verifier's `heapRelations` (a loop over the heap's blocks) is `T(t)`'s relation, the
  tree's, the root's, one relation per block (`blockRel`: the unused block's `R_u(mixed) = 1`, a used block's leaf
  identity with its quotient's chunks), the constraint quotient's chunks; its columns are each used block's leaf
  quotient's chunks (`blockCols`). (`forIn_heap`: the loop's body always yields, `blockLeaf` being its `leaf`.)
* **`constraintRelation_degree`**: the degree `constraintRelation` returns is `Shape.constraintDegree` (the loop's
  degree component depends on the tables only, `forIn_proj`).
* **`atTOf_c2Columns_eq`**: `C2`'s columns as the verifier lists them at `t` are `Shape.c2Columns` (so the layouts
  the verifier states, `layouts shape c2Columns`, are `layoutsOf shape`, the prover's): the parts' degrees are
  `tableDegrees` (`AlgC.tablePartOf_degrees`).
-/

namespace UniComplete.AlgH

open UniStatement LeanVM.Parameters
open UniComplete.Domain (ite_pos_of ite_neg_of)

/-! ### `heapRelations`, written out -/

/-- A block's leaf data (`heapRelations`' `leaf`): its pull and push values, its quotient's degree, its scale. -/
def blockLeaf (active : List E) (parts : List TablePart) (memoryPull memoryPush bytecodePull bytecodePush : E)
    (w : List E) (b : Block) : Option (E × E × ℕ × E) :=
  match b.leaves with
  | Leaves.unused => none
  | Leaves.memory => some (memoryPull, memoryPush, degree (2 * (2 ^ b.r - 1)) (2 ^ b.r), w.getD b.r 0)
  | Leaves.bytecode => some (bytecodePull, bytecodePush, degree (2 * (2 ^ b.r - 1)) (2 ^ b.r), w.getD b.r 0)
  | Leaves.table t =>
    some ((parts.getD t default).pull * w.getD b.r 0 + active.getD t 0 * active.getD t 0,
      (parts.getD t default).push * w.getD b.r 0 + active.getD t 0 * active.getD t 0,
      degree (max (parts.getD t default).pullDegree (parts.getD t default).pushDegree * (2 ^ b.r - 1) +
        (2 ^ b.r - Shape.leastRows b.r)) (2 ^ b.r),
      w.getD b.r 0 * active.getD t 0)

/-- A block's relation (`heapRelations`' loop body). -/
def blockRel (h : ℕ) (active : List E) (parts : List TablePart) (memoryPull memoryPush bytecodePull bytecodePush : E)
    (w : List E) (x : Block × ℕ) : Relation :=
  match blockLeaf active parts memoryPull memoryPush bytecodePull bytecodePush w x.1 with
  | none => ⟨[term .heap (mixedPoint w h x.1.position x.1.r) 1], 1⟩
  | some (pull, push, d, scale) =>
    ⟨[term .heap (mixedPoint w h x.1.position x.1.r) pull] ++ quotientTerms (Column.leafQuotient x.2) (chunks (d + 1)) w scale,
      push⟩

/-- A block's leaf quotient's columns. -/
def blockCols (active : List E) (parts : List TablePart) (memoryPull memoryPush bytecodePull bytecodePush : E)
    (w : List E) (x : Block × ℕ) : List (Column × ℕ × Bool) :=
  match blockLeaf active parts memoryPull memoryPush bytecodePull bytecodePush w x.1 with
  | none => []
  | some (_, _, d, _) => ((chunks (d + 1)).zip (List.range (chunks (d + 1)).length)).map
      fun y ↦ (Column.leafQuotient x.2 y.2, y.1, true)

theorem forIn_heap (g : Block × ℕ → Relation) (c : Block × ℕ → List (Column × ℕ × Bool))
    (F : Block × ℕ → Array Relation × Array (Column × ℕ × Bool) → Id (ForInStep (Array Relation × Array (Column × ℕ × Bool))))
    (hF : ∀ x s, F x s = pure (ForInStep.yield (s.1.push (g x), s.2 ++ (c x).toArray))) :
    ∀ (L : List (Block × ℕ)) (s : Array Relation × Array (Column × ℕ × Bool)),
      forIn L s F = pure (s.1 ++ (L.map g).toArray, s.2 ++ (L.flatMap c).toArray)
  | [], s => by simp
  | x :: L, s => by
    rw [List.forIn_cons, hF]
    show forIn L _ F = _
    rw [forIn_heap g c F hF L]
    simp [Array.append_assoc]

/-- **The heap's relations, written out.** -/
theorem heapRelations_eq (shape : Shape) (active : List E) (parts : List TablePart) (weights : Array E)
    (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : E) (w : List E)
    (constraintChunks : List ℕ) :
    heapRelations shape active parts weights beta heapValue constraintValue memoryPull memoryPush bytecodePull
      bytecodePush w constraintChunks =
      ([Relation.equal .heap (w.take shape.heap.h) heapValue,
          ⟨[term .heap ((w.drop 1).take shape.heap.h) (w.getD 1 0),
            term .heap ((w.take shape.heap.h).modify 0 (· + 1)) (w.getD 1 0 * heapValue),
            term (.treeQuotient 0) (w.take shape.heap.h) (w.getD shape.heap.h 0),
            term (.treeQuotient 1) [] (w.getD shape.heap.h 0 * w.getD shape.heap.h 0)], 0⟩,
          ⟨[term .heap ((List.range shape.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0)
            (beta + weights.getD 0 0 * sepState + weights.getD 1 0 + weights.getD 2 0)],
            beta + weights.getD 0 0 * sepState + weights.getD 1 0 * UniStatement.gpow (2 ^ shape.logBytecode - 1) +
              weights.getD 2 0⟩] ++
        (shape.heap.blocks.zip (List.range shape.heap.blocks.length)).map
          (blockRel shape.heap.h active parts memoryPull memoryPush bytecodePull bytecodePush w) ++
        [⟨quotientTerms .constraintQuotient constraintChunks w 1, constraintValue⟩],
      (shape.heap.blocks.zip (List.range shape.heap.blocks.length)).flatMap
          (blockCols active parts memoryPull memoryPush bytecodePull bytecodePush w)) := by
  unfold heapRelations
  simp only [Id.run]
  rw [forIn_heap (blockRel shape.heap.h active parts memoryPull memoryPush bytecodePull bytecodePush w)
    (blockCols active parts memoryPull memoryPush bytecodePull bytecodePush w) _ (fun x s ↦ by
      unfold blockRel blockCols
      show (match blockLeaf active parts memoryPull memoryPush bytecodePull bytecodePush w x.1 with
        | none => _ | some (pull, push, d, scale) => _) = _
      cases blockLeaf active parts memoryPull memoryPush bytecodePull bytecodePush w x.1 with
      | none => simp [mixedPoint]
      | some v => obtain ⟨pull, push, d, scale⟩ := v; simp [mixedPoint])]
  simp
  rfl


/-! ### The constraint quotient's degree -/

theorem forIn_deg {α : Type} (F : α → E × Array Term × E × ℕ → Id (ForInStep (E × Array Term × E × ℕ)))
    (g : α → ℕ → ℕ) (hF : ∀ x s, ∃ s', F x s = pure (ForInStep.yield s') ∧ s'.2.2.2 = g x s.2.2.2) :
    ∀ (L : List α) (s : E × Array Term × E × ℕ),
      (Id.run (forIn L s F)).2.2.2 = L.foldl (fun acc x ↦ g x acc) s.2.2.2
  | [], _ => rfl
  | x :: L, s => by
    obtain ⟨s', h1, h2⟩ := hF x s
    unfold Id.run
    rw [List.forIn_cons, h1]
    show (Id.run (forIn L s' F)).2.2.2 = _
    rw [forIn_deg F g hF L s', h2]
    rfl

/-- One table's step of `Shape.constraintDegree`'s fold. -/
def cDegStep (shape : Shape) (d : ℕ) (table : Table) : ℕ :=
  let r := shape.heights.getD table.opcode 0
  let n := 2 ^ r
  let d := if table.opcode = opJump then max d (degree n 2) else d
  let d := max d (degree ((n - 1) * (1 + table.countColumns.length)) n)
  if table.opcode = opBlake2s then max d (degree (r * (n / 2)) n) else d

theorem constraintDegree_eq (shape : Shape) :
    shape.constraintDegree = max (tables.foldl (cDegStep shape) 0) (degree (2 ^ shape.logMemory) 3) := rfl

theorem id_bind_snd {α β γ δ : Type} (A : Id α) (B : α → Id β) (f : α → β → γ) (g : α → δ) :
    ((do let s ← A; let s1 ← B s; pure (f s s1, g s)) : Id (γ × δ)).2 = g (Id.run A) := rfl

/-- **`constraintRelation`'s degree is `Shape.constraintDegree`** (for six parts or more). -/
theorem constraintRelation_degree (shape : Shape) (parts : List TablePart) (publicWords : List E)
    (gamma t constraintValue : E) (w : List E) (hp : tables.length ≤ parts.length) :
    (constraintRelation shape parts publicWords gamma t constraintValue w).2 = shape.constraintDegree := by
  unfold constraintRelation
  simp only [Id.run]
  rw [id_bind_snd]
  rw [forIn_deg _ (fun x d ↦ cDegStep shape d x.1) ?_]
  · rw [constraintDegree_eq, ← List.foldl_map (f := Prod.fst) (g := fun acc t ↦ cDegStep shape acc t),
      List.map_fst_zip hp]
  · intro x s
    by_cases h1 : x.1.opcode = opJump
    · by_cases h2 : x.1.opcode = opBlake2s
      · exact absurd (h1.symm.trans h2) (by simp [opJump, opBlake2s])
      · rw [ite_pos_of h1, ite_neg_of h2]
        refine ⟨_, rfl, ?_⟩
        show _ = cDegStep shape s.2.2.2 x.1
        unfold cDegStep
        simp only [ite_pos_of h1, ite_neg_of h2]
    · by_cases h2 : x.1.opcode = opBlake2s
      · rw [ite_neg_of h1, ite_pos_of h2]
        refine ⟨_, rfl, ?_⟩
        show _ = cDegStep shape s.2.2.2 x.1
        unfold cDegStep
        simp only [ite_neg_of h1, ite_pos_of h2]
      · rw [ite_neg_of h1, ite_neg_of h2]
        refine ⟨_, rfl, ?_⟩
        show _ = cDegStep shape s.2.2.2 x.1
        unfold cDegStep
        simp only [ite_neg_of h1, ite_neg_of h2]


/-! ### `C2`'s columns -/

theorem tables_length : tables.length = 6 := rfl

theorem atParts_length (tr : Trace) (weights : Array E) (beta : E) (w : List E) :
    (AlgC.atParts tr weights beta w).length = 6 := by
  rw [AlgC.atParts, List.length_map]; rfl

theorem atParts_getD (tr : Trace) (weights : Array E) (beta : E) (w : List E) {t : ℕ} (ht : t < 6) :
    (AlgC.atParts tr weights beta w).getD t default = (AlgC.atPart tr weights beta w (tables.getD t default)).1 := by
  rw [AlgC.atParts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [tables_length]; exact ht)]
  rfl

theorem atPart_degrees (tr : Trace) (weights : Array E) (beta : E) (w : List E) (table : Table) :
    (AlgC.atPart tr weights beta w table).1.pullDegree = (tableDegrees table).1 ∧
      (AlgC.atPart tr weights beta w table).1.pushDegree = (tableDegrees table).2 :=
  ⟨rfl, rfl⟩

/-- A block's columns, as `Shape.c2Columns` lists them. -/
def shapeBlockCols (x : Block × ℕ) : List (Column × ℕ × Bool) :=
  match Shape.leafDegree x.1 with
  | none => []
  | some d => ((chunks (d + 1)).zip (List.range (chunks (d + 1)).length)).map
      fun y ↦ (Column.leafQuotient x.2 y.2, y.1, true)

theorem blockCols_eq {tr : Trace} (hon : TraceHonest tr) (active : List E) (weights : Array E) (beta : E)
    (w : List E) (memoryPull memoryPush bytecodePull bytecodePush : E) (wp : List E) {b : Block}
    (hb : b ∈ tr.shape.heap.blocks) (index : ℕ) :
    blockCols active (AlgC.atParts tr weights beta wp) memoryPull memoryPush bytecodePull bytecodePush w (b, index) =
      shapeBlockCols (b, index) := by
  unfold blockCols shapeBlockCols blockLeaf
  rcases hl : b.leaves with _ | _ | t | _
  all_goals dsimp only
  · rw [leafDegree_memory hl]
  · rw [leafDegree_bytecode hl]
  · obtain ⟨ht, -⟩ := block_r_table tr.shape hb hl
    have ht6 : t < 6 := by rw [hon.valid.1] at ht; exact ht
    rw [leafDegree_table hl, atParts_getD _ _ _ _ ht6, (atPart_degrees _ _ _ _ _).1, (atPart_degrees _ _ _ _ _).2]
  · rw [leafDegree_unused hl]

theorem c2Columns_eq (shape : Shape) : Shape.c2Columns shape =
    [(.heap, shape.heap.h, true), (.treeQuotient 0, shape.heap.h, true), (.treeQuotient 1, 0, true)] ++
      ((chunks (shape.constraintDegree + 1)).zip (List.range (chunks (shape.constraintDegree + 1)).length)).map
        (fun x ↦ (Column.constraintQuotient x.2, x.1, true)) ++
      (shape.heap.blocks.zip (List.range shape.heap.blocks.length)).flatMap shapeBlockCols := rfl

/-- **The verifier's `C2` columns at `t` are `Shape.c2Columns`** (so its layouts are `layoutsOf`). -/
theorem atTOf_c2Columns_eq {tr : Trace} (hon : TraceHonest tr) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    (atTOf tr c2 alphas beta gamma t none).c2Columns = Shape.c2Columns tr.shape := by
  rw [AlgC.atTOf_c2Columns, c2Columns_eq]
  have hdeg : (AlgC.atConstraint tr c2 alphas beta gamma t).2 = tr.shape.constraintDegree :=
    constraintRelation_degree _ _ _ _ _ _ _ (by rw [atParts_length]; rfl)
  rw [hdeg]
  unfold AlgC.atHeap
  rw [heapRelations_eq, hdeg]
  dsimp only
  rw [List.flatMap_congr fun x hx ↦ by
    obtain ⟨b, index⟩ := x
    exact blockCols_eq hon _ _ _ _ _ _ _ _ _ (List.of_mem_zip hx).1 index]

end UniComplete.AlgH
