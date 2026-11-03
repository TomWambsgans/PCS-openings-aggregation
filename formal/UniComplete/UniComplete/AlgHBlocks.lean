-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHTable

/-!
# Every used heap block's leaf quotient is exact and fits (milestone 4, the headline)

For `TraceHonest tr`, `¬ BadFp tr α β` and a heap of height `h ≤ 28`, at every used block `b` of the layout
(`Shape.leafDegree b = some d`, `leafNumerator … b R_b = some N`, `R_b` the polynomial of the block's leaves on
`V_r`):

* **`leafQuotient_exact`**: `N = w_r · Q_b`, `Q_b = divM N w_r` the prover's quotient (`N` vanishes on `V_r`);
* **`leafQuotient_fits`**: `deg Q_b < Σ_{e ∈ chunks (d + 1)} 2^e`.

The block's height is its kind's (`block_r_memory`, `block_r_bytecode`, `block_r_table`: the used blocks are the
used list, `AlgHLayout.used_perm`), at most `h − 1` (`block_r_le`). **Every honest run whose row counts satisfy
`RowsFit` fits** (no counterexample: the table case is `table_degree_arith`, at every height).
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

theorem mem_usedList {lm lb : ℕ} {hs : List ℕ} {l : Leaves} {r : ℕ} (h : (l, r) ∈ usedList lm lb hs) :
    (l = .memory → r = lm) ∧ (l = .bytecode → r = lb) ∧ (∀ t, l = .table t → t < hs.length ∧ r = hs.getD t 0) := by
  unfold usedList at h
  simp only [List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq, List.mem_map, List.mem_range] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨t, ht, h⟩
  · exact ⟨fun _ ↦ rfl, (fun h ↦ Leaves.noConfusion h), (fun _ h ↦ Leaves.noConfusion h)⟩
  · exact ⟨(fun h ↦ Leaves.noConfusion h), fun _ ↦ rfl, (fun _ h ↦ Leaves.noConfusion h)⟩
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨(fun h ↦ Leaves.noConfusion h), (fun h ↦ Leaves.noConfusion h), fun t' h ↦ ?_⟩
    cases h
    exact ⟨ht, rfl⟩

theorem used_mem (s : Shape) {b : Block} (hb : b ∈ s.heap.blocks) (hu : blockUsed b) :
    (b.leaves, b.r) ∈ usedList s.logMemory s.logBytecode s.heights :=
  (used_perm s.logMemory s.logBytecode s.heights).mem_iff.mp
    (List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, decide_eq_true hu⟩, rfl⟩)

theorem block_r_memory (s : Shape) {b : Block} (hb : b ∈ s.heap.blocks) (hl : b.leaves = .memory) :
    b.r = s.logMemory :=
  (mem_usedList (used_mem s hb (by unfold blockUsed; rw [hl]; simp))).1 hl

theorem block_r_bytecode (s : Shape) {b : Block} (hb : b ∈ s.heap.blocks) (hl : b.leaves = .bytecode) :
    b.r = s.logBytecode :=
  (mem_usedList (used_mem s hb (by unfold blockUsed; rw [hl]; simp))).2.1 hl

theorem block_r_table (s : Shape) {b : Block} (hb : b ∈ s.heap.blocks) {t : ℕ} (hl : b.leaves = .table t) :
    t < s.heights.length ∧ b.r = s.heights.getD t 0 :=
  (mem_usedList (used_mem s hb (by unfold blockUsed; rw [hl]; simp))).2.2 t hl

theorem block_r_le (s : Shape) {b : Block} (hb : b ∈ s.heap.blocks) : b.r ≤ s.heap.h - 1 := by
  have hL : LayoutOK s.heap := layoutOK_new _ _ _
  have h1 := hL.lo b hb
  have h2 := hL.hi b hb
  have hh := hL.one_le
  have e : 2 ^ s.heap.h = 2 * 2 ^ (s.heap.h - 1) := by rw [← pow_succ', Nat.sub_add_cancel hh]
  have : 2 ^ b.r ≤ 2 ^ (s.heap.h - 1) := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

theorem leafDegree_memory {b : Block} (hl : b.leaves = .memory) :
    Shape.leafDegree b = some (degree (2 * (2 ^ b.r - 1)) (2 ^ b.r)) := by
  unfold Shape.leafDegree; rw [hl]

theorem leafDegree_bytecode {b : Block} (hl : b.leaves = .bytecode) :
    Shape.leafDegree b = some (degree (2 * (2 ^ b.r - 1)) (2 ^ b.r)) := by
  unfold Shape.leafDegree; rw [hl]

theorem leafDegree_table {b : Block} {t : ℕ} (hl : b.leaves = .table t) :
    Shape.leafDegree b = some (degree (max (tableDegrees (tables.getD t default)).1
      (tableDegrees (tables.getD t default)).2 * (2 ^ b.r - 1) + (2 ^ b.r - Shape.leastRows b.r)) (2 ^ b.r)) := by
  unfold Shape.leafDegree
  rw [hl]

theorem leafDegree_unused {b : Block} (hl : b.leaves = .unused) : Shape.leafDegree b = none := by
  unfold Shape.leafDegree; rw [hl]

theorem leafNumerator_memory (tr : Trace) (weights : Array E) (beta : E) {b : Block} (hl : b.leaves = .memory)
    (R : Poly) : leafNumerator tr weights beta b R = some (memoryLeafNumerator tr weights beta R) := by
  unfold leafNumerator; rw [hl]

theorem leafNumerator_bytecode (tr : Trace) (weights : Array E) (beta : E) {b : Block} (hl : b.leaves = .bytecode)
    (R : Poly) : leafNumerator tr weights beta b R = some (bytecodeLeafNumerator tr weights beta R) := by
  unfold leafNumerator; rw [hl]

theorem leafNumerator_table (tr : Trace) (weights : Array E) (beta : E) {b : Block} {t : ℕ}
    (hl : b.leaves = .table t) (R : Poly) :
    leafNumerator tr weights beta b R = some (tableLeafNumerator tr weights beta t R) := by
  unfold leafNumerator; rw [hl]

theorem leafNumerator_unused (tr : Trace) (weights : Array E) (beta : E) {b : Block} (hl : b.leaves = .unused)
    (R : Poly) : leafNumerator tr weights beta b R = none := by
  unfold leafNumerator; rw [hl]

theorem getD_map_leastRows (l : List ℕ) (t : ℕ) :
    (l.map Shape.leastRows).getD t 0 = Shape.leastRows (l.getD t 0) := by
  by_cases ht : t < l.length
  · simp [List.getD_eq_getElem?_getD, ht]
  · simp [List.getD_eq_getElem?_getD, show l.length ≤ t by omega, Shape.leastRows]

section Honest

variable {tr : Trace} (hon : TraceHonest tr) {alphas : List E} {beta : E} (hbad : ¬ BadFp tr alphas beta)
include hon hbad

/-- **Every used block's leaf numerator vanishes on `V_r`.** -/
theorem leafNumerator_eval (hH : tr.shape.heap.h ≤ 28) {b : Block} (hb : b ∈ tr.shape.heap.blocks) {N : Poly}
    (hN : leafNumerator tr (eqKernel alphas) beta b
      (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves))) = some N)
    {i : ℕ} (hi : i < 2 ^ b.r) : (tp N).eval (pointE i) = 0 := by
  have hr := block_r_le tr.shape hb
  rcases hl : b.leaves with _ | _ | t | _
  · rw [leafNumerator_memory _ _ _ hl] at hN
    obtain rfl := Option.some.inj hN.symm
    have e := block_r_memory tr.shape hb hl
    rw [hl]
    rewrite [e] at hi ⊢
    exact memoryLeafNumerator_eval hon hbad (by omega) hi
  · rw [leafNumerator_bytecode _ _ _ hl] at hN
    obtain rfl := Option.some.inj hN.symm
    have e := block_r_bytecode tr.shape hb hl
    rw [hl]
    rewrite [e] at hi ⊢
    exact bytecodeLeafNumerator_eval hon hbad (by omega) hi
  · rw [leafNumerator_table _ _ _ hl] at hN
    obtain rfl := Option.some.inj hN.symm
    obtain ⟨ht, e⟩ := block_r_table tr.shape hb hl
    have ht6 : t < 6 := by rw [hon.valid.1] at ht; exact ht
    have e' : b.r = tr.height t := e
    rw [hl]
    rewrite [e'] at hi ⊢
    have hrows := ((hon.rowsFit.2 t ht6).2)
    exact tableLeafNumerator_eval hon hbad ht6 (by rw [← e']; omega) hrows hi
  · rw [leafNumerator_unused _ _ _ hl] at hN
    cases hN

/-- **Every used block's leaf quotient is exact**: `N = w_r · Q_b`. -/
theorem leafQuotient_exact (hH : tr.shape.heap.h ≤ 28) {b : Block} (hb : b ∈ tr.shape.heap.blocks) {N : Poly}
    (hN : leafNumerator tr (eqKernel alphas) beta b
      (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves))) = some N) :
    tp N = wP b.r * tp (divM N (wPoly b.r)) :=
  eq_mul_divM (by have := block_r_le tr.shape hb; omega) fun _ hi ↦ leafNumerator_eval hon hbad hH hb hN hi

omit hbad in
/-- **Every used block's leaf quotient fits its chunks** `chunks (d + 1)`, `d` its `Shape.leafDegree`. -/
theorem leafQuotient_fits (hH : tr.shape.heap.h ≤ 28) {b : Block} (hb : b ∈ tr.shape.heap.blocks) {d : ℕ}
    (hd : Shape.leafDegree b = some d) {N : Poly}
    (hN : leafNumerator tr (eqKernel alphas) beta b
      (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves))) = some N) :
    (tp (divM N (wPoly b.r))).natDegree < ((chunks (d + 1)).map (2 ^ ·)).sum := by
  have hr := block_r_le tr.shape hb
  refine fits_of_le ?_
  have hR : (tp (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))).natDegree ≤
      2 ^ b.r - 1 := Nat.le_sub_one_of_lt (natDegree_tp_ofNovel_lt _ _)
  rcases hl : b.leaves with _ | _ | t | _
  · rw [leafNumerator_memory _ _ _ hl] at hN
    rw [leafDegree_memory hl] at hd
    obtain rfl := Option.some.inj hN.symm
    obtain rfl := Option.some.inj hd.symm
    have e := block_r_memory tr.shape hb hl
    rewrite [e] at hR ⊢
    have h1 := natDegree_divM_le (r := tr.shape.logMemory)
      (natDegree_memoryLeafNumerator_le (eqKernel alphas) beta _ hR)
    refine h1.trans ?_
    unfold UniStatement.degree; omega
  · rw [leafNumerator_bytecode _ _ _ hl] at hN
    rw [leafDegree_bytecode hl] at hd
    obtain rfl := Option.some.inj hN.symm
    obtain rfl := Option.some.inj hd.symm
    have e := block_r_bytecode tr.shape hb hl
    rewrite [e] at hR ⊢
    have h1 := natDegree_divM_le (r := tr.shape.logBytecode)
      (natDegree_bytecodeLeafNumerator_le (eqKernel alphas) beta _ hR)
    refine h1.trans ?_
    unfold UniStatement.degree; omega
  · rw [leafNumerator_table _ _ _ hl] at hN
    rw [leafDegree_table hl] at hd
    obtain rfl := Option.some.inj hN.symm
    obtain rfl := Option.some.inj hd.symm
    obtain ⟨ht, e⟩ := block_r_table tr.shape hb hl
    have ht6 : t < 6 := by rw [hon.valid.1] at ht; exact ht
    have e' : b.r = tr.height t := e
    rewrite [e'] at hR ⊢
    have hfit := hon.rowsFit.2 t ht6
    have hlo : Shape.leastRows (tr.height t) ≤ tr.rows.getD t 0 := by
      have := hfit.1
      unfold Shape.capacityRows at this
      rwa [getD_map_leastRows] at this
    have hdeg := natDegree_tableLeafNumerator_le ht6 (by omega) hfit.2 (eqKernel alphas) beta _ hR
    have h1 := natDegree_divM_le (r := tr.height t) hdeg
    refine h1.trans ?_
    unfold UniStatement.degree
    exact Nat.sub_le_sub_right (table_degree_arith (le_trans (three_le_pullDegree ht6) (le_max_left _ _))
      hlo hfit.2) _
  · rw [leafNumerator_unused _ _ _ hl] at hN
    cases hN

end Honest

end UniComplete.AlgH
