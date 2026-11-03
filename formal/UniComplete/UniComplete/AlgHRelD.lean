-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHRelC

/-!
# The heap's relations hold: the headline (milestone 4, item 2)

* `rel_block`: every block's relation (`rel_block_memory`, `_bytecode`, `_table`, `_unused`);
* `constraintDegree_lt`: `Shape.constraintDegree + 1 ≤ 2^(r_W + 4)` (heights `≤ 31`, at most `15` counters a
  table), so every chunk of the constraint quotient is read inside the digits;
* `rel_constraint`: the constraint quotient's chunks add up to `Q_W(t)`, the value sent;
* **`heapRelations_hold`**: every relation `heapRelations` states at `t` holds (`Relation.Holds`) of the three stacks at
  the layouts the verifier states.
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

section Honest

variable {tr : Trace} (hon : TraceHonest tr) {alphas : List E} {beta gamma : E}

include hon in
/-- **Every block's relation holds.** -/
theorem rel_block (hbad : ¬ BadFp tr alphas beta) (hH : tr.shape.heap.h ≤ 28) (t : E) (rm : Option (List E))
    {x : Block × ℕ} (hx : x ∈ tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length)) :
    Relation.Holds (LOf tr alphas beta gamma t) (stacksOf tr (c2Of tr alphas beta gamma)) rm
      (blockRelAt tr alphas beta t x) := by
  obtain ⟨b, index⟩ := x
  rcases hl : b.leaves with _ | _ | tt | _
  · exact rel_block_memory hon hbad hH t rm hx hl
  · exact rel_block_bytecode hon hbad hH t rm hx hl
  · exact rel_block_table hon hbad hH t rm hx hl
  · exact rel_block_unused hon hH t rm hx hl

/-! ### The constraint quotient's chunks -/

theorem tables_ops : ∀ table ∈ tables, table.opcode < 6 ∧ table.countColumns.length ≤ 15 := by decide +kernel

include hon in
theorem heights_le_31 {t : ℕ} (ht : t < 6) : tr.height t ≤ 31 := by
  have hv := hon.valid.2
  unfold Shape.validate at hv
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false,
    decide_eq_true_eq, not_lt] at hv
  have := hv.1.2 (tr.height t) (by
    rw [Trace.height, List.getD_eq_getElem _ _ (by rw [hon.valid.1]; exact ht)]
    exact List.getElem_mem _)
  omega

theorem cDegStep_le (shape : Shape) (B : ℕ) (table : Table) (d : ℕ) (hc : table.countColumns.length ≤ 15)
    (hr : shape.heights.getD table.opcode 0 ≤ 31) (hB : 2 ^ (shape.heights.getD table.opcode 0) * 16 ≤ B + 1) :
    cDegStep shape d table ≤ max d B := by
  unfold cDegStep
  generalize shape.heights.getD table.opcode 0 = r at hr hB ⊢
  have h1 : (2 ^ r - 1) * (1 + table.countColumns.length) ≤ (2 ^ r - 1) * 16 := Nat.mul_le_mul_left _ (by omega)
  have h2 : r * (2 ^ r / 2) ≤ 31 * (2 ^ r / 2) := Nat.mul_le_mul_right _ hr
  have hn : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hJ : degree (2 ^ r) 2 ≤ B := by unfold UniStatement.degree; omega
  have hC : degree ((2 ^ r - 1) * (1 + table.countColumns.length)) (2 ^ r) ≤ B := by
    unfold UniStatement.degree; omega
  have hBl : degree (r * (2 ^ r / 2)) (2 ^ r) ≤ B := by unfold UniStatement.degree; omega
  simp only [max_def]
  split_ifs <;> omega

include hon in
/-- **The constraint quotient's degree** is below `2^(r_W + 4)`. -/
theorem constraintDegree_lt : tr.shape.constraintDegree + 1 ≤ 2 ^ (tr.shape.constraintVars + 4) := by
  have hB : ∀ table ∈ tables, 2 ^ (tr.shape.heights.getD table.opcode 0) * 16 ≤
      2 ^ (tr.shape.constraintVars + 4) - 1 + 1 := by
    intro table ht
    have h6 := (tables_ops table ht).1
    have := height_le_constraintVars hon h6
    have h1 : 2 ^ (tr.shape.heights.getD table.opcode 0) * 16 ≤ 2 ^ (tr.shape.constraintVars + 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by unfold Trace.height at this; omega)
    have := Nat.one_le_two_pow (n := tr.shape.constraintVars + 4)
    omega
  have hfold : ∀ (l : List Table), (∀ table ∈ l, table ∈ tables) → ∀ d, d ≤ 2 ^ (tr.shape.constraintVars + 4) - 1 →
      l.foldl (cDegStep tr.shape) d ≤ 2 ^ (tr.shape.constraintVars + 4) - 1 := by
    intro l
    induction l with
    | nil => intro _ d hd; exact hd
    | cons table l ih =>
      intro hl d hd
      rw [List.foldl_cons]
      have ht := hl table (List.mem_cons_self ..)
      refine ih (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) _ ?_
      have := cDegStep_le tr.shape _ table d (tables_ops table ht).2
        (heights_le_31 hon (tables_ops table ht).1) (hB table ht)
      omega
  have h1 := hfold tables (fun _ h ↦ h) 0 (Nat.zero_le _)
  have hlm : tr.shape.logMemory ≤ tr.shape.constraintVars :=
    (le_foldl_max _ 0).2 _ (List.mem_append_right _ (List.mem_singleton_self _))
  have h2 : 2 ^ tr.shape.logMemory ≤ 2 ^ (tr.shape.constraintVars + 4) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [constraintDegree_eq]
  unfold UniStatement.degree
  have := Nat.one_le_two_pow (n := tr.shape.constraintVars + 4)
  omega

include hon in
/-- **The constraint quotient's chunks add up to `Q_W(t)`**, the value sent. -/
theorem rel_constraint (t : E) (rm : Option (List E)) :
    Relation.Holds (LOf tr alphas beta gamma t) (stacksOf tr (c2Of tr alphas beta gamma)) rm
      ⟨quotientTerms .constraintQuotient
          (chunks ((AlgC.atConstraint tr (c2Of tr alphas beta gamma) alphas beta gamma t).2 + 1)) (AlgC.atW tr t) 1,
        AlgC.atConstraintValue (c2Of tr alphas beta gamma) (AlgC.atW tr t)⟩ := by
  have hdeg : (AlgC.atConstraint tr (c2Of tr alphas beta gamma) alphas beta gamma t).2 = tr.shape.constraintDegree :=
    constraintRelation_degree _ _ _ _ _ _ _ (by rw [atParts_length]; rfl)
  rw [hdeg]
  have hshape := (AlgC.chunks_spec (n := tr.shape.constraintDegree + 1) (by omega)).1
  refine holds_of_c2 _ _ _ _ (fun τ hτ ↦ ?_) ?_
  · have := List.mem_map_of_mem (f := (·.column)) hτ
    rw [AlgC.quotientTerms_columns] at this
    obtain ⟨c, -, hc⟩ := List.mem_map.mp this
    show τ.column.commitment = _
    rw [← hc]; rfl
  · rw [LOf_c2 hon]
    show ((quotientTerms .constraintQuotient (chunks (tr.shape.constraintDegree + 1)) (AlgC.atW tr t) 1).map
      fun τ ↦ termEval (StackLayout.new (Shape.c2Columns tr.shape)) (c2Of tr alphas beta gamma).stack rm τ).sum = _
    rw [quotientTerms_value .constraintQuotient hshape (AlgC.atW tr t) 1 _
      (cs := (c2Of tr alphas beta gamma).constraintChunks) (chunksB_length hshape) (fun c hc k ↦ ?_), one_mul]
    · rfl
    · have he : (chunks (tr.shape.constraintDegree + 1)).getD c 0 ≤ nW tr + 1 + 1 := by
        have h1 := (AlgC.chunks_spec (n := tr.shape.constraintDegree + 1) (by omega)).2.2
          ((chunks (tr.shape.constraintDegree + 1)).getD c 0)
          (by rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem _)
        have h2 := (Nat.log2_lt (n := tr.shape.constraintDegree + 1) (k := tr.shape.constraintVars + 5) (by omega)).mpr
          (by have := constraintDegree_lt hon; rw [pow_succ]; omega)
        have : tr.shape.constraintVars + 4 ≤ nW tr := le_max_right _ _
        omega
      have hmem : (Column.constraintQuotient c, (chunks (tr.shape.constraintDegree + 1)).getD c 0, true) ∈
          Shape.c2Columns tr.shape := by
        rw [c2Columns_eq]
        refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
          ⟨((chunks (tr.shape.constraintDegree + 1))[c], c), ?_, ?_⟩))
        · have : ((chunks (tr.shape.constraintDegree + 1)).zip
              (List.range (chunks (tr.shape.constraintDegree + 1)).length))[c]'(by simpa using hc) =
              ((chunks (tr.shape.constraintDegree + 1))[c], c) := by
            rw [List.getElem_zip, List.getElem_range]
          rw [← this]
          exact List.getElem_mem _
        · rw [List.getD_eq_getElem _ _ hc]
      rw [c2Stack_eq]
      exact termEval_c2col _ hmem (fun j ↦ Column.noConfusion) (fun l _ ↦ rfl)
        (chunksB_size (q := constraintQuotient tr gamma (publicWordsOf tr.publicInput)) hshape hc)
        (length_take_lt (by rw [atW_eq, Domain.length_digits]; exact he)) rm k


/-! ### The headline -/

include hon in
/-- **Every relation the heap states at `t` holds** (`T(t)`, the tree, the root, each block's leaf identity at its
mixed point, the unused blocks, the constraint quotient's chunks), of the three stacks at the layouts the verifier
states, for any ring map. -/
theorem heapRelations_hold (hbad : ¬ BadFp tr alphas beta) (hH : tr.shape.heap.h ≤ 28) (t : E)
    (rm : Option (List E)) :
    ∀ rel ∈ (AlgC.atHeap tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t).1,
      Relation.Holds
        (layoutIn (layouts tr.shape (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).c2Columns))
        (stacksOf tr (c2DataOf tr (eqKernel alphas) beta gamma)) rm rel := by
  intro rel hrel
  unfold AlgC.atHeap at hrel
  rw [heapRelations_eq] at hrel
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append, List.mem_map,
    List.not_mem_nil, or_false] at hrel
  rcases hrel with rfl | rfl | rfl | ⟨x, hx, rfl⟩ | rfl
  · exact rel_T hon t rm
  · exact rel_tree hon hH t rm
  · exact rel_root hon hbad hH t rm
  · exact rel_block hon hbad hH t rm hx
  · exact rel_constraint hon t rm

include hon in
/-- **Every relation of `atTOf`'s that `heapRelations` states holds** (its relations end with the heap's,
`AlgC.atTOf_relations`), at `atTOf`'s ring map. -/
theorem atTOf_heap_holds (hbad : ¬ BadFp tr alphas beta) (hH : tr.shape.heap.h ≤ 28) (t : E) :
    let a := atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none
    (∀ rel ∈ (AlgC.atHeap tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t).1, rel ∈ a.relations) ∧
    ∀ rel ∈ (AlgC.atHeap tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t).1,
      Relation.Holds (layoutIn (layouts tr.shape a.c2Columns)) (stacksOf tr (c2DataOf tr (eqKernel alphas) beta gamma))
        a.ringMap rel := by
  intro a
  refine ⟨fun rel hrel ↦ ?_, heapRelations_hold hon hbad hH t _⟩
  show rel ∈ (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).relations
  rw [AlgC.atTOf_relations]
  exact List.mem_append_right _ hrel

end Honest

end UniComplete.AlgH
