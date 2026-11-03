-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHBlocks

/-!
# The heap's root (milestone 4): `T(1) · fp(SEP_STATE, 1, 1) = fp(SEP_STATE, g^(2^lb − 1), 1)`

* **The root is the leaves' product** (`heap_root_eq_prod`): the tree identity on positions (`Heap.TreeHolds`, from
  `TreeValues`) gives `T_1 = Π_{2^(h−1) ≤ q < 2^h} T_q` (`Heap.root_eq_prod_leaves`);
* **the leaves' product is the blocks'** (`prod_leaves_eq_blocks`): the used blocks are disjoint, every other leaf is
  `1`; by `used_perm`, the product over the memory's, the bytecode's and the six tables' blocks;
* **the blocks' product times the divided fingerprints is the pushed fingerprints** (`blocks_mul_divided`): a
  memory cell's or an instruction's leaf is `D_init / D_fin`, an active row's `Π push / Π pull`, a padding row's
  `1` (no fingerprint divided by vanishes, `¬ BadFp`);
* **the bus's permutation** (`TraceHonest.bus`) makes the pushed and pulled fingerprints' products equal, the
  state's `(SEP_STATE, 1, 1)` pushed and `(SEP_STATE, g^(2^lb − 1), 1)` pulled; hence **`heap_root`**.
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

/-! ### The root is the leaves' product -/

theorem treeHolds_of_treeValues {h : ℕ} {v : Array E} (ht : TreeValues h v) :
    Heap.TreeHolds h fun i ↦ v.getD i 0 := by
  intro i hi2 hi
  have hp1 : 1 ≤ i >>> 1 := by rw [Nat.shiftRight_one]; omega
  have hpar : i >>> 1 < 2 ^ (h - 1) := by
    rw [Nat.shiftRight_one]
    rcases h with _ | h
    · simp at hi; omega
    · rw [pow_succ] at hi; simp only [Nat.add_sub_cancel]; omega
  show v.getD (i >>> 1) 0 = v.getD i 0 * v.getD (i ^^^ 1) 0
  rw [ht (i >>> 1) hp1 hpar]
  rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
  · obtain ⟨p, hp⟩ : ∃ p, i = 2 * p := ⟨i / 2, by omega⟩
    have hs : i >>> 1 = p := by rw [Nat.shiftRight_one]; omega
    have e2 : i ^^^ 1 = 2 * p + 1 := by rw [hp, Heap.two_mul_xor_one]
    rw [hs, e2, ← hp]
  · obtain ⟨p, hp⟩ : ∃ p, i = 2 * p + 1 := ⟨i / 2, by omega⟩
    have hs : i >>> 1 = p := by rw [Nat.shiftRight_one]; omega
    have e2 : i ^^^ 1 = 2 * p := by
      rw [hp, ← Heap.two_mul_xor_one, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hs, e2, ← hp, mul_comm]

/-! ### Products over the blocks -/

/-- A block's leaves' product. -/
def blockProd (tr : Trace) (weights : Array E) (beta : E) (p : Leaves × ℕ) : E :=
  ∏ i ∈ range (2 ^ p.2), (blockLeaves tr weights beta p.1).getD i 0

theorem prod_find_blocks (tr : Trace) (weights : Array E) (beta : E) (lo hi : ℕ) :
    ∀ (bs : List Block), bs.Pairwise blockDisjoint → (∀ b ∈ bs, lo ≤ b.position ∧ b.position + 2 ^ b.r ≤ hi) →
      ∏ q ∈ Ico lo hi, (match bs.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) with
        | some b => (blockLeaves tr weights beta b.leaves).getD (q - b.position) 0
        | none => 1) =
      ((bs.filter fun b ↦ decide (blockUsed b)).map fun b ↦ blockProd tr weights beta (b.leaves, b.r)).prod
  | [], _, _ => by simp
  | b :: bs, hdis, hfit => by
    rw [List.pairwise_cons] at hdis
    have ih := prod_find_blocks tr weights beta lo hi bs hdis.2 fun b' hb' ↦ hfit b' (List.mem_cons_of_mem _ hb')
    by_cases hu : blockUsed b
    · rw [List.filter_cons_of_pos (p := fun b ↦ decide (blockUsed b)) (decide_eq_true hu), List.map_cons,
        List.prod_cons, ← ih]
      have hfree : ∀ q, blockHolds b q → (bs.find? fun b ↦ decide (blockUsed b ∧ blockHolds b q)) = none := by
        intro q hq
        rw [List.find?_eq_none]
        intro b' hb' hc
        simp only [decide_eq_true_eq] at hc
        have hd := hdis.1 b' hb'
        unfold blockDisjoint at hd
        unfold blockHolds at hq hc
        omega
      have e : ∀ q ∈ Ico lo hi, (match (b :: bs).find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) with
          | some b => (blockLeaves tr weights beta b.leaves).getD (q - b.position) 0
          | none => 1) =
          (if blockHolds b q then (blockLeaves tr weights beta b.leaves).getD (q - b.position) 0 else 1) *
          (match bs.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) with
          | some b => (blockLeaves tr weights beta b.leaves).getD (q - b.position) 0
          | none => 1) := by
        intro q _
        by_cases hq : blockHolds b q
        · rw [List.find?_cons_of_pos (p := fun b ↦ decide (blockUsed b ∧ blockHolds b q)) (by simp [hu, hq]), hfree q hq, ite_pos_of hq]
          dsimp only
          rw [mul_one]
        · rw [List.find?_cons_of_neg (p := fun b ↦ decide (blockUsed b ∧ blockHolds b q)) (by simp [hq]), ite_neg_of hq, one_mul]
      rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib]
      congr 1
      rw [← Finset.prod_filter]
      have hset : (Ico lo hi).filter (blockHolds b) = Ico b.position (b.position + 2 ^ b.r) := by
        ext q
        have := hfit b (List.mem_cons_self ..)
        simp only [Finset.mem_filter, Finset.mem_Ico, blockHolds]
        omega
      rw [hset, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left, blockProd]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [Nat.add_sub_cancel_left]
    · rw [List.filter_cons_of_neg (p := fun b ↦ decide (blockUsed b)) (by simpa using hu), ← ih]
      refine Finset.prod_congr rfl fun q _ ↦ ?_
      rw [List.find?_cons_of_neg (p := fun b ↦ decide (blockUsed b ∧ blockHolds b q)) (by simp [hu])]


/-- **The leaves' product is the used blocks' product**, in the used list's order. -/
theorem prod_leaves_eq_usedList (tr : Trace) (weights : Array E) (beta : E) :
    ∏ q ∈ Ico (2 ^ (tr.shape.heap.h - 1)) (2 ^ tr.shape.heap.h), (heapValues tr weights beta).getD q 0 =
      ((usedList tr.shape.logMemory tr.shape.logBytecode tr.shape.heights).map (blockProd tr weights beta)).prod := by
  have hL : LayoutOK tr.shape.heap := layoutOK_new _ _ _
  have e : ∀ q ∈ Ico (2 ^ (tr.shape.heap.h - 1)) (2 ^ tr.shape.heap.h), (heapValues tr weights beta).getD q 0 =
      (match tr.shape.heap.blocks.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) with
        | some b => (blockLeaves tr weights beta b.leaves).getD (q - b.position) 0
        | none => 1) := by
    intro q hq
    rw [Finset.mem_Ico] at hq
    rw [heapValues_getD_leaf tr weights beta hL hq.1, heapLeaves_getD tr weights beta hL]
    cases tr.shape.heap.blocks.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) with
    | some b => rfl
    | none => simp [Array.getD_eq_getD_getElem?, hq.2]
  rw [Finset.prod_congr rfl e, prod_find_blocks tr weights beta _ _ _ hL.disjoint
    (fun b hb ↦ ⟨hL.lo b hb, hL.hi b hb⟩)]
  have := ((used_perm tr.shape.logMemory tr.shape.logBytecode tr.shape.heights).map
    (blockProd tr weights beta)).prod_eq
  rw [List.map_map] at this
  exact this

/-- **The root is the leaves' product.** -/
theorem heap_root_eq_prod (tr : Trace) (weights : Array E) (beta : E) :
    (heapValues tr weights beta).getD 1 0 =
      ∏ q ∈ Ico (2 ^ (tr.shape.heap.h - 1)) (2 ^ tr.shape.heap.h), (heapValues tr weights beta).getD q 0 := by
  have hL : LayoutOK tr.shape.heap := layoutOK_new _ _ _
  exact Heap.root_eq_prod_leaves hL.one_le (treeHolds_of_treeValues (heapValues_tree tr weights beta hL))

/-! ### List products -/

theorem prod_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → E) :
    ((l.flatMap f).map g).prod = (l.map fun a ↦ ((f a).map g).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem prod_comm_lists {α β : Type*} (l1 : List α) (l2 : List β) (g : α → β → E) :
    (l1.map fun a ↦ (l2.map (g a)).prod).prod = (l2.map fun b ↦ (l1.map fun a ↦ g a b).prod).prod := by
  induction l1 with
  | nil => simp
  | cons a l1 ih =>
    rw [List.map_cons, List.prod_cons, ih, ← List.prod_map_mul]
    simp only [List.map_cons, List.prod_cons]

theorem prod_map_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → E) :
    ((l.filter p).map f).prod = (l.map fun i ↦ if p i then f i else 1).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : p a
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, ite_pos_of ha]
    · rw [List.filter_cons_of_neg ha, ih, List.map_cons, List.prod_cons, ite_neg_of ha, one_mul]


/-! ### The bus -/

theorem stateFp_eq_fpOf (weights : Array E) (beta pc : E) :
    stateFp weights beta pc = fpOf weights beta (stateTuple pc) := by
  unfold stateFp fpOf stateTuple
  simp only [range16, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, List.replicate_succ,
    List.replicate_zero, List.getD_cons_zero, List.getD_cons_succ]
  ring

/-- A table's tuples over its active rows. -/
def rowTuples (tr : Trace) (t : ℕ) (tuples : List (List Form)) : List (List E) :=
  tuples.flatMap fun tuple ↦ (activeRows tr t).map fun i ↦ tupleAt tuple (tr.cell t · i)

/-- The pushed tuples but the state's. -/
def pushedBlocks (tr : Trace) : List (List E) :=
  ((List.range 6).flatMap fun t ↦ rowTuples tr t (tables.getD t default).flushes.push) ++
    (List.range (2 ^ tr.shape.logMemory)).map (fun i ↦ memoryTuple tr i 1) ++
    (List.range (2 ^ tr.shape.logBytecode)).map (fun i ↦ bytecodeTuple tr i 1)

theorem dividedTuples_eq (tr : Trace) : dividedTuples tr =
    ((List.range 6).flatMap fun t ↦ rowTuples tr t (tables.getD t default).flushes.pull) ++
      (List.range (2 ^ tr.shape.logMemory)).map (fun i ↦ memoryTuple tr i (ofK ((tr.memory.getD 3 #[]).getD i 0))) ++
      (List.range (2 ^ tr.shape.logBytecode)).map (fun i ↦ bytecodeTuple tr i (ofK (tr.bytecodeFinal.getD i 0))) :=
  rfl

theorem pushTuples_eq (tr : Trace) : pushTuples tr = pushedBlocks tr ++ [stateTuple 1] := rfl

theorem pullTuples_eq (tr : Trace) :
    pullTuples tr = dividedTuples tr ++ [stateTuple (gpow (2 ^ tr.shape.logBytecode - 1))] := rfl

section Honest

variable {tr : Trace} (hon : TraceHonest tr) {alphas : List E} {beta : E} (hbad : ¬ BadFp tr alphas beta)

include hon in
/-- **The bus's permutation, multiplied out.** -/
theorem bus_prod (weights : Array E) (beta : E) :
    ((pushedBlocks tr).map (fpOf weights beta)).prod * stateFp weights beta 1 =
      ((dividedTuples tr).map (fpOf weights beta)).prod * stateFp weights beta (gpow (2 ^ tr.shape.logBytecode - 1)) := by
  have h := (hon.bus.map (fpOf weights beta)).prod_eq
  rw [pushTuples_eq, pullTuples_eq, List.map_append, List.map_append, List.prod_append, List.prod_append] at h
  simpa [stateFp_eq_fpOf] using h

include hbad in
theorem dividedProd_ne_zero : ((dividedTuples tr).map (fpOf (eqKernel alphas) beta)).prod ≠ 0 :=
  List.prod_ne_zero fun h0 ↦ by
    obtain ⟨tau, htau, h⟩ := List.mem_map.mp h0
    exact hbad ⟨tau, htau, h⟩

theorem rowPull_eq (weights : Array E) (beta : E) (t i : ℕ) :
    rowPull tr weights beta t i =
      ((tables.getD t default).flushes.pull.map fun tuple ↦ fpE tuple weights beta (tr.cell t · i)).prod := by
  rw [rowPull, foldl_mul_eq, one_mul]

theorem rowPush_eq (weights : Array E) (beta : E) (t i : ℕ) :
    rowPush tr weights beta t i =
      ((tables.getD t default).flushes.push.map fun tuple ↦ fpE tuple weights beta (tr.cell t · i)).prod := by
  rw [rowPush, foldl_mul_eq, one_mul]

theorem rowTuples_prod (weights : Array E) (beta : E) {t : ℕ} {tuples : List (List Form)}
    (hl : ∀ tu ∈ tuples, tu.length ≤ 16) :
    ((rowTuples tr t tuples).map (fpOf weights beta)).prod =
      ((activeRows tr t).map fun i ↦ (tuples.map fun tuple ↦ fpE tuple weights beta (tr.cell t · i)).prod).prod := by
  unfold rowTuples
  rw [prod_map_flatMap]
  have hc := prod_comm_lists tuples (activeRows tr t) (fun tuple i ↦ fpE tuple weights beta (tr.cell t · i))
  rw [← hc]
  refine congrArg List.prod (List.map_congr_left fun tuple htu ↦ ?_)
  rewrite [List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ ↦ ?_)
  have key := fpE_eq_fpOf (hl tuple htu) weights beta (tr.cell t · i)
  rewrite [Function.comp_apply]
  exact key.symm

include hbad in
/-- **A table's block times its pulls is its pushes.** -/
theorem table_block_mul {t : ℕ} (ht : t < 6) :
    blockProd tr (eqKernel alphas) beta (.table t, tr.height t) *
        ((activeRows tr t).map (rowPull tr (eqKernel alphas) beta t)).prod =
      ((activeRows tr t).map (rowPush tr (eqKernel alphas) beta t)).prod := by
  unfold activeRows
  rw [prod_map_filter, prod_map_filter, Domain.prod_map_range, Domain.prod_map_range, blockProd,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  show (tableLeaves tr _ beta t).getD i 0 * _ = _
  rw [tableLeaves_getD _ _ hi']
  by_cases ha : isActive i (tr.rows.getD t 0) (tr.height t) = true
  · rw [ite_pos_of ha, ite_pos_of ha, ite_pos_of ha, mul_assoc, inv_mul_cancel₀ (rowPull_ne_zero hbad ht hi' ha),
      mul_one]
  · rw [ite_neg_of ha, ite_neg_of ha, ite_neg_of ha, one_mul]

include hbad in
theorem memory_block_mul :
    blockProd tr (eqKernel alphas) beta (.memory, tr.shape.logMemory) *
        ((List.range (2 ^ tr.shape.logMemory)).map fun i ↦
          fpOf (eqKernel alphas) beta (memoryTuple tr i (ofK ((tr.memory.getD 3 #[]).getD i 0)))).prod =
      ((List.range (2 ^ tr.shape.logMemory)).map fun i ↦ fpOf (eqKernel alphas) beta (memoryTuple tr i 1)).prod := by
  rw [Domain.prod_map_range, Domain.prod_map_range, blockProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  show (memoryLeaves tr _ beta).getD i 0 * _ = _
  rw [memoryLeaves_getD _ _ hi', ← memoryFp_eq_fpOf, ← memoryFp_eq_fpOf, mul_assoc]
  have hne := memFin_ne_zero hbad hi'
  unfold memFin at hne
  unfold memFin memInit
  rw [inv_mul_cancel₀ hne, mul_one]

include hbad in
theorem bytecode_block_mul :
    blockProd tr (eqKernel alphas) beta (.bytecode, tr.shape.logBytecode) *
        ((List.range (2 ^ tr.shape.logBytecode)).map fun i ↦
          fpOf (eqKernel alphas) beta (bytecodeTuple tr i (ofK (tr.bytecodeFinal.getD i 0)))).prod =
      ((List.range (2 ^ tr.shape.logBytecode)).map fun i ↦ fpOf (eqKernel alphas) beta (bytecodeTuple tr i 1)).prod := by
  rw [Domain.prod_map_range, Domain.prod_map_range, blockProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  show (bytecodeLeaves tr _ beta).getD i 0 * _ = _
  rw [bytecodeLeaves_getD _ _ hi', ← bytecodeFp_eq_fpOf, ← bytecodeFp_eq_fpOf, mul_assoc]
  have hne := bcFin_ne_zero hbad hi'
  unfold bcFin at hne
  unfold bcFin bcInit
  rw [inv_mul_cancel₀ hne, mul_one]

theorem usedList_six {lm lb : ℕ} {hs : List ℕ} (h6 : hs.length = 6) :
    usedList lm lb hs = [(.memory, lm), (.bytecode, lb)] ++ (List.range 6).map fun t ↦ (.table t, hs.getD t 0) := by
  rw [usedList, h6]

include hon hbad in
/-- **The blocks' product times the divided fingerprints is the pushed fingerprints.** -/
theorem leaves_mul_divided :
    ((usedList tr.shape.logMemory tr.shape.logBytecode tr.shape.heights).map
        (blockProd tr (eqKernel alphas) beta)).prod * ((dividedTuples tr).map (fpOf (eqKernel alphas) beta)).prod =
      ((pushedBlocks tr).map (fpOf (eqKernel alphas) beta)).prod := by
  -- the tables' parts
  have hA' : (((List.range 6).flatMap fun t ↦ rowTuples tr t (tables.getD t default).flushes.pull).map
      (fpOf (eqKernel alphas) beta)).prod = ((List.range 6).map fun t ↦ ((activeRows tr t).map (rowPull tr (eqKernel alphas) beta t)).prod).prod := by
    rw [prod_map_flatMap]
    refine congrArg List.prod (List.map_congr_left fun t ht ↦ ?_)
    rw [rowTuples_prod (eqKernel alphas) beta ((tables_facts t (List.mem_range.mp ht)).1)]
    refine congrArg List.prod (List.map_congr_left fun i _ ↦ ?_)
    rw [rowPull_eq]
  have hA : (((List.range 6).flatMap fun t ↦ rowTuples tr t (tables.getD t default).flushes.push).map
      (fpOf (eqKernel alphas) beta)).prod = ((List.range 6).map fun t ↦ ((activeRows tr t).map (rowPush tr (eqKernel alphas) beta t)).prod).prod := by
    rw [prod_map_flatMap]
    refine congrArg List.prod (List.map_congr_left fun t ht ↦ ?_)
    rw [rowTuples_prod (eqKernel alphas) beta ((tables_facts t (List.mem_range.mp ht)).2.1)]
    refine congrArg List.prod (List.map_congr_left fun i _ ↦ ?_)
    rw [rowPush_eq]
  have hT : ((List.range 6).map fun t ↦ blockProd tr (eqKernel alphas) beta (.table t, tr.shape.heights.getD t 0)).prod *
      ((List.range 6).map fun t ↦ ((activeRows tr t).map (rowPull tr (eqKernel alphas) beta t)).prod).prod =
      ((List.range 6).map fun t ↦ ((activeRows tr t).map (rowPush tr (eqKernel alphas) beta t)).prod).prod := by
    rw [← List.prod_map_mul]
    refine congrArg List.prod (List.map_congr_left fun t ht ↦ ?_)
    exact table_block_mul hbad (List.mem_range.mp ht)
  have hM := memory_block_mul (tr := tr) (alphas := alphas) (beta := beta) hbad
  have hB := bytecode_block_mul (tr := tr) (alphas := alphas) (beta := beta) hbad
  rewrite [usedList_six hon.valid.1, dividedTuples_eq, pushedBlocks]
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rewrite [hA', hA]
  simp only [List.map_map, Function.comp_def] at hM hB hT ⊢
  rewrite [← hM, ← hB, ← hT]
  ring

include hon hbad in
/-- **The root identity**: `T_1 · fp(SEP_STATE, 1, 1) = fp(SEP_STATE, g^(2^lb − 1), 1)`. -/
theorem heap_root :
    (heapValues tr (eqKernel alphas) beta).getD 1 0 * stateFp (eqKernel alphas) beta 1 =
      stateFp (eqKernel alphas) beta (gpow (2 ^ tr.shape.logBytecode - 1)) := by
  have hD := dividedProd_ne_zero (beta := beta) hbad
  have hbus := bus_prod hon (eqKernel alphas) beta
  have hLD := leaves_mul_divided hon hbad
  rw [heap_root_eq_prod, prod_leaves_eq_usedList]
  refine mul_right_cancel₀ hD ?_
  rw [mul_right_comm, hLD, hbus, mul_comm]

end Honest

end UniComplete.AlgH
