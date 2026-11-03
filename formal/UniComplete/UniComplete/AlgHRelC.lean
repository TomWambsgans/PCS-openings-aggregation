-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHRelB

/-!
# Each block's relation holds (milestone 4)

`holds_leaf`: a used block's relation `R_b(mixed) · pull + scale · Q_b(t) = push` holds on `C2` when its value
identity does (the heap's term is the heap at the mixed point, the chunks' terms add up to `scale · Q_b(t)`, read
through `AlgC.chunksValue_chunksB` with the fit `leafQuotient_fits`). `rel_block`: every block's relation holds,
an unused block's `R_u = 1` (its leaves are `1`, `heapValues_free`), a used block's by its leaf quotient's
exactness at `t` (`leafQuotient_exact`), a table's times `Z_act(t)` (`Z_act Z_pad = w_r`).
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

section Honest

variable {tr : Trace} (hon : TraceHonest tr) {alphas : List E} {beta gamma : E}

/-- The layouts the verifier states at `t` (notation). -/
abbrev LOf (tr : Trace) (alphas : List E) (beta gamma t : E) : Commitment → StackLayout :=
  layoutIn (layouts tr.shape (atTOf tr (c2Of tr alphas beta gamma) alphas beta gamma t none).c2Columns)

include hon in
theorem LOf_c2 (t : E) : LOf tr alphas beta gamma t .c2 = StackLayout.new (Shape.c2Columns tr.shape) :=
  LO_c2 hon _ t

theorem length_take_lt {w : List E} {e : ℕ} (h : e ≤ w.length) : (w.take e).length = e := by
  rw [List.length_take]; omega

include hon in
/-- **A used block's relation holds** when its value identity does. -/
theorem holds_leaf (hH : tr.shape.heap.h ≤ 28) (t : E) (rm : Option (List E)) {b : Block} {index : ℕ}
    (hx : (b, index) ∈ tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length)) {d : ℕ}
    (hd : Shape.leafDegree b = some d) {N : Poly}
    (hN : leafNumerator tr (eqKernel alphas) beta b
      (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves))) = some N)
    (hsz : ∀ e ∈ chunks (d + 1), e < nW tr + 1 + 1) (pull push scale : E)
    (hval : pull * multilinearEval (c2Of tr alphas beta gamma).heapB.toList
        (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r) + scale * pEval t (divM N (wPoly b.r)) = push) :
    Relation.Holds (LOf tr alphas beta gamma t) (stacksOf tr (c2Of tr alphas beta gamma)) rm
      ⟨[term .heap (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r) pull] ++
        quotientTerms (.leafQuotient index) (chunks (d + 1)) (AlgC.atW tr t) scale, push⟩ := by
  have hb : b ∈ tr.shape.heap.blocks := (List.of_mem_zip hx).1
  have hshape := (AlgC.chunks_spec (n := d + 1) (by omega)).1
  refine holds_of_c2 _ _ _ _ (fun τ hτ ↦ ?_) ?_
  · rcases List.mem_append.mp hτ with h1 | h1
    · rw [List.mem_singleton] at h1; subst h1; rfl
    · have := List.mem_map_of_mem (f := (·.column)) h1
      rw [AlgC.quotientTerms_columns] at this
      obtain ⟨c, -, hc⟩ := List.mem_map.mp this
      show τ.column.commitment = _
      rw [← hc]; rfl
  · rw [LOf_c2 hon]
    show (([term .heap (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r) pull] ++
      quotientTerms (.leafQuotient index) (chunks (d + 1)) (AlgC.atW tr t) scale).map
        fun τ ↦ termEval (StackLayout.new (Shape.c2Columns tr.shape)) (c2Of tr alphas beta gamma).stack rm τ).sum = push
    rw [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      termEval_heap (mixedPoint_length _ _ _ _)]
    rw [quotientTerms_value (.leafQuotient index) hshape (AlgC.atW tr t) scale _
      (cs := chunksB (divM N (wPoly b.r)) (chunks (d + 1))) (chunksB_length hshape) (fun c hc k ↦ ?_)]
    · have hQ := AlgC.chunksValue_chunksB _ _ hshape (leafQuotient_fits hon hH hb hd hN) t (nW tr + 1 + 1) hsz
      rw [atW_eq] at hval ⊢
      rw [hQ]
      exact hval
    · have he := hsz ((chunks (d + 1)).getD c 0) (by rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem _)
      exact termEval_leaf hx hd hN hc (length_take_lt (by rw [atW_eq, Domain.length_digits]; omega)) rm k


/-- The block relation's arguments at `t` (notation). -/
abbrev blockRelAt (tr : Trace) (alphas : List E) (beta t : E) : Block × ℕ → Relation :=
  blockRel tr.shape.heap.h (AlgC.atActive tr (AlgC.atW tr t)) (AlgC.atParts tr (eqKernel alphas) beta (AlgC.atW tr t))
    (AlgC.atMemoryPull tr (eqKernel alphas) beta (AlgC.atW tr t)) (AlgC.atMemoryPush tr (eqKernel alphas) beta (AlgC.atW tr t))
    (AlgC.atBytecodePull tr (eqKernel alphas) beta (AlgC.atW tr t))
    (AlgC.atBytecodePush tr (eqKernel alphas) beta (AlgC.atW tr t)) (AlgC.atW tr t)

include hon in
/-- **The memory's block relation holds.** -/
theorem rel_block_memory (hbad : ¬ BadFp tr alphas beta) (hH : tr.shape.heap.h ≤ 28) (t : E) (rm : Option (List E))
    {b : Block} {index : ℕ} (hx : (b, index) ∈ tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length))
    (hl : b.leaves = .memory) :
    Relation.Holds (LOf tr alphas beta gamma t) (stacksOf tr (c2Of tr alphas beta gamma)) rm
      (blockRelAt tr alphas beta t (b, index)) := by
  have hb : b ∈ tr.shape.heap.blocks := (List.of_mem_zip hx).1
  have hL := layoutOK_new tr.shape.logMemory tr.shape.logBytecode tr.shape.heights
  have hr := block_r_le tr.shape hb
  have hv := heapValues_size' tr (eqKernel alphas) beta
  have hMh : tr.shape.heap.h ≤ nW tr := le_max_left _ _
  have e := block_r_memory tr.shape hb hl
  have hRel : blockRelAt tr alphas beta t (b, index) =
      ⟨[term .heap (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r)
          (AlgC.atMemoryPull tr (eqKernel alphas) beta (AlgC.atW tr t))] ++
        quotientTerms (.leafQuotient index) (chunks (degree (2 * (2 ^ b.r - 1)) (2 ^ b.r) + 1)) (AlgC.atW tr t)
          ((AlgC.atW tr t).getD b.r 0), AlgC.atMemoryPush tr (eqKernel alphas) beta (AlgC.atW tr t)⟩ := by
    unfold blockRelAt blockRel blockLeaf
    rw [hl]
  rw [hRel]
  have hN := leafNumerator_memory tr (eqKernel alphas) beta hl
    (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))
  refine holds_leaf hon hH t rm hx (leafDegree_memory hl) hN (fun e' he' ↦ ?_) _ _ _ ?_
  · have h2 := Nat.one_le_two_pow (n := b.r)
    have := chunks_lt (k := b.r + 1) (by unfold UniStatement.degree; rw [pow_succ]; omega) e' he'
    omega
  · have hLs : (blockLeaves tr (eqKernel alphas) beta b.leaves).size = 2 ^ b.r := by
      rw [hl, e]; exact memoryLeaves_size _ _
    have hmix := mle_mixed (n := nW tr + 1 + 1) hH (by omega) (hL.aligned b hb) (hL.hi b hb) hv hLs
      (fun i hi ↦ heapValues_block tr _ beta hL hb (by unfold blockUsed; rw [hl]; simp) hi) t (by omega)
    have hlm : tr.shape.logMemory ≤ nW tr + 1 + 1 := by omega
    have hNt : (tp (memoryLeafNumerator tr (eqKernel alphas) beta
        (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves))))).eval t =
        (tp (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))).eval t *
          AlgC.atMemoryPull tr (eqKernel alphas) beta (AlgC.atW tr t) +
        AlgC.atMemoryPush tr (eqKernel alphas) beta (AlgC.atW tr t) := by
      rw [← ev_apply]
      simp only [memoryLeafNumerator, map_add, map_mul]
      rw [atW_eq, atMemoryPull_eq hon (eqKernel alphas) beta t hlm, atMemoryPush_eq hon (eqKernel alphas) beta t hlm,
        ev_apply]
    have hex := congrArg (Polynomial.eval t) (leafQuotient_exact hon hbad hH hb hN)
    rw [Polynomial.eval_mul, hNt] at hex
    have hwr : (AlgC.atW tr t).getD b.r 0 = (wP b.r).eval t := by rw [atW_eq, digits_getD' t (by omega)]
    rw [show multilinearEval (c2Of tr alphas beta gamma).heapB.toList
        (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r) = _ from hmix, hwr, tp_eval]
    linear_combination (-1 : E) * hex +
      (AlgC.atMemoryPull tr (eqKernel alphas) beta (AlgC.atW tr t) *
        (tp (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))).eval t) *
        Domain.two_eq_zero_E


include hon in
/-- **The bytecode's block relation holds.** -/
theorem rel_block_bytecode (hbad : ¬ BadFp tr alphas beta) (hH : tr.shape.heap.h ≤ 28) (t : E) (rm : Option (List E))
    {b : Block} {index : ℕ} (hx : (b, index) ∈ tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length))
    (hl : b.leaves = .bytecode) :
    Relation.Holds (LOf tr alphas beta gamma t) (stacksOf tr (c2Of tr alphas beta gamma)) rm
      (blockRelAt tr alphas beta t (b, index)) := by
  have hb : b ∈ tr.shape.heap.blocks := (List.of_mem_zip hx).1
  have hL := layoutOK_new tr.shape.logMemory tr.shape.logBytecode tr.shape.heights
  have hr := block_r_le tr.shape hb
  have hv := heapValues_size' tr (eqKernel alphas) beta
  have hMh : tr.shape.heap.h ≤ nW tr := le_max_left _ _
  have e := block_r_bytecode tr.shape hb hl
  have hRel : blockRelAt tr alphas beta t (b, index) =
      ⟨[term .heap (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r)
          (AlgC.atBytecodePull tr (eqKernel alphas) beta (AlgC.atW tr t))] ++
        quotientTerms (.leafQuotient index) (chunks (degree (2 * (2 ^ b.r - 1)) (2 ^ b.r) + 1)) (AlgC.atW tr t)
          ((AlgC.atW tr t).getD b.r 0), AlgC.atBytecodePush tr (eqKernel alphas) beta (AlgC.atW tr t)⟩ := by
    unfold blockRelAt blockRel blockLeaf
    rw [hl]
  rw [hRel]
  have hN := leafNumerator_bytecode tr (eqKernel alphas) beta hl
    (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))
  refine holds_leaf hon hH t rm hx (leafDegree_bytecode hl) hN (fun e' he' ↦ ?_) _ _ _ ?_
  · have h2 := Nat.one_le_two_pow (n := b.r)
    have := chunks_lt (k := b.r + 1) (by unfold UniStatement.degree; rw [pow_succ]; omega) e' he'
    omega
  · have hLs : (blockLeaves tr (eqKernel alphas) beta b.leaves).size = 2 ^ b.r := by
      rw [hl, e]; exact bytecodeLeaves_size _ _
    have hmix := mle_mixed (n := nW tr + 1 + 1) hH (by omega) (hL.aligned b hb) (hL.hi b hb) hv hLs
      (fun i hi ↦ heapValues_block tr _ beta hL hb (by unfold blockUsed; rw [hl]; simp) hi) t (by omega)
    have hlb : tr.shape.logBytecode ≤ nW tr + 1 + 1 := by omega
    have hNt : (tp (bytecodeLeafNumerator tr (eqKernel alphas) beta
        (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves))))).eval t =
        (tp (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))).eval t *
          AlgC.atBytecodePull tr (eqKernel alphas) beta (AlgC.atW tr t) +
        AlgC.atBytecodePush tr (eqKernel alphas) beta (AlgC.atW tr t) := by
      rw [← ev_apply]
      simp only [bytecodeLeafNumerator, map_add, map_mul]
      rw [atW_eq, atBytecodePull_eq hon (eqKernel alphas) beta t hlb,
        atBytecodePush_eq hon (eqKernel alphas) beta t hlb, ev_apply]
      rfl
    have hex := congrArg (Polynomial.eval t) (leafQuotient_exact hon hbad hH hb hN)
    rw [Polynomial.eval_mul, hNt] at hex
    have hwr : (AlgC.atW tr t).getD b.r 0 = (wP b.r).eval t := by rw [atW_eq, digits_getD' t (by omega)]
    rw [show multilinearEval (c2Of tr alphas beta gamma).heapB.toList
        (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r) = _ from hmix, hwr, tp_eval]
    linear_combination (-1 : E) * hex +
      (AlgC.atBytecodePull tr (eqKernel alphas) beta (AlgC.atW tr t) *
        (tp (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))).eval t) *
        Domain.two_eq_zero_E

include hon in
/-- **An unused block's relation holds**: its leaves are `1`, so `R_u = 1`. -/
theorem rel_block_unused (hH : tr.shape.heap.h ≤ 28) (t : E) (rm : Option (List E))
    {b : Block} {index : ℕ} (hx : (b, index) ∈ tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length))
    (hl : b.leaves = .unused) :
    Relation.Holds (LOf tr alphas beta gamma t) (stacksOf tr (c2Of tr alphas beta gamma)) rm
      (blockRelAt tr alphas beta t (b, index)) := by
  have hb : b ∈ tr.shape.heap.blocks := (List.of_mem_zip hx).1
  have hL : LayoutOK tr.shape.heap := layoutOK_new _ _ _
  have hr := block_r_le tr.shape hb
  have hv := heapValues_size' tr (eqKernel alphas) beta
  have hMh : tr.shape.heap.h ≤ nW tr := le_max_left _ _
  have hRel : blockRelAt tr alphas beta t (b, index) =
      ⟨[term .heap (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r) 1], 1⟩ := by
    unfold blockRelAt blockRel blockLeaf
    rw [hl]
  rw [hRel]
  refine holds_of_c2 _ _ _ _ (by simp [term_column, Column.commitment]) ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [LOf_c2 hon]
  show termEval _ (c2Of tr alphas beta gamma).stack rm _ = _
  rw [termEval_heap (mixedPoint_length _ _ _ _), one_mul]
  have hfree : ∀ i < 2 ^ b.r, (heapValues tr (eqKernel alphas) beta).getD (b.position + i) 0 =
      (Array.replicate (2 ^ b.r) (1 : E)).getD i 0 := by
    intro i hi
    have hlo := hL.lo b hb
    have hhi := hL.hi b hb
    rw [heapValues_free tr _ beta hL (by omega) (by omega) fun b' hb' hu ↦ ?_]
    · simp [Array.getD_eq_getD_getElem?, hi]
    · have hne : b' ≠ b := fun h ↦ hu (by rw [h]; exact hl)
      have hsymm : Std.Symm blockDisjoint := ⟨fun a c h ↦ by unfold blockDisjoint at h ⊢; omega⟩
      have hd := hL.disjoint.forall hb' hb hne
      unfold blockDisjoint at hd
      unfold blockHolds
      omega
  have hmix := mle_mixed (n := nW tr + 1 + 1) hH (by omega) (hL.aligned b hb) (hL.hi b hb) hv
    (L := Array.replicate (2 ^ b.r) (1 : E)) Array.size_replicate hfree t (by omega)
  rw [show multilinearEval (c2Of tr alphas beta gamma).heapB.toList
      (mixedPoint (AlgC.atW tr t) tr.shape.heap.h b.position b.r) = _ from hmix]
  have hone : tp (ofNovel b.r (novelOfValuesE b.r (Array.replicate (2 ^ b.r) (1 : E)))) = 1 := by
    refine eq_of_eval_pointE (by omega) (natDegree_tp_ofNovel_lt _ _)
      (by rw [natDegree_one]; exact Nat.two_pow_pos _) fun i hi ↦ ?_
    rw [eval_ofNovel_novelOfValuesE (by omega) Array.size_replicate hi, Polynomial.eval_one]
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [hone, Polynomial.eval_one]


include hon in
/-- **A table's block relation holds** (the leaf identity times `Z_act(t)`). -/
theorem rel_block_table (hbad : ¬ BadFp tr alphas beta) (hH : tr.shape.heap.h ≤ 28) (t : E) (rm : Option (List E))
    {b : Block} {index : ℕ} (hx : (b, index) ∈ tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length))
    {tt : ℕ} (hl : b.leaves = .table tt) :
    Relation.Holds (LOf tr alphas beta gamma t) (stacksOf tr (c2Of tr alphas beta gamma)) rm
      (blockRelAt tr alphas beta t (b, index)) := by
  have hb : b ∈ tr.shape.heap.blocks := (List.of_mem_zip hx).1
  have hL : LayoutOK tr.shape.heap := layoutOK_new _ _ _
  have hr := block_r_le tr.shape hb
  have hv := heapValues_size' tr (eqKernel alphas) beta
  have hMh : tr.shape.heap.h ≤ nW tr := le_max_left _ _
  obtain ⟨ht, e⟩ := block_r_table tr.shape hb hl
  have ht6 : tt < 6 := by rw [hon.valid.1] at ht; exact ht
  have e' : b.r = tr.height tt := e
  have hrW := height_le_constraintVars hon ht6
  have hnW : tr.shape.constraintVars + 4 ≤ nW tr := le_max_right _ _
  set w := AlgC.atW tr t with hw
  set part := (AlgC.atParts tr (eqKernel alphas) beta w).getD tt default
  set z := (AlgC.atActive tr w).getD tt 0
  set wr := w.getD b.r 0
  have hdeg1 : part.pullDegree = (tableDegrees (tables.getD tt default)).1 := by
    show ((AlgC.atParts tr (eqKernel alphas) beta w).getD tt default).pullDegree = _
    rw [atParts_getD _ _ _ _ ht6]; exact (atPart_degrees _ _ _ _ _).1
  have hdeg2 : part.pushDegree = (tableDegrees (tables.getD tt default)).2 := by
    show ((AlgC.atParts tr (eqKernel alphas) beta w).getD tt default).pushDegree = _
    rw [atParts_getD _ _ _ _ ht6]; exact (atPart_degrees _ _ _ _ _).2
  have hRel : blockRelAt tr alphas beta t (b, index) =
      ⟨[term .heap (mixedPoint w tr.shape.heap.h b.position b.r) (part.pull * wr + z * z)] ++
        quotientTerms (.leafQuotient index) (chunks (degree (max (tableDegrees (tables.getD tt default)).1
          (tableDegrees (tables.getD tt default)).2 * (2 ^ b.r - 1) + (2 ^ b.r - Shape.leastRows b.r)) (2 ^ b.r) + 1))
          w (wr * z), part.push * wr + z * z⟩ := by
    unfold blockRelAt blockRel blockLeaf
    rw [hl]
    dsimp only
    rw [← hdeg1, ← hdeg2]
  rw [hRel]
  have hN := leafNumerator_table tr (eqKernel alphas) beta hl
    (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))
  refine holds_leaf hon hH t rm hx (leafDegree_table hl) hN (fun e2 he2 ↦ ?_) _ _ _ ?_
  · have hM := tableDegrees_le ht6
    have h2 := Nat.one_le_two_pow (n := b.r)
    have hMr : max (tableDegrees (tables.getD tt default)).1 (tableDegrees (tables.getD tt default)).2 *
        (2 ^ b.r - 1) ≤ 31 * (2 ^ b.r - 1) := Nat.mul_le_mul_right _ hM
    have := chunks_lt (k := b.r + 5) (by unfold UniStatement.degree; rw [pow_add]; omega) e2 he2
    omega
  · have hLs : (blockLeaves tr (eqKernel alphas) beta b.leaves).size = 2 ^ b.r := by
      rw [hl, e']; exact tableLeaves_size _ _ _
    have hmix := mle_mixed (n := nW tr + 1 + 1) hH (by omega) (hL.aligned b hb) (hL.hi b hb) hv hLs
      (fun i hi ↦ heapValues_block tr _ beta hL hb (by unfold blockUsed; rw [hl]; simp) hi) t (by omega)
    have hrn : tr.height tt ≤ nW tr + 1 + 1 := by omega
    have hP : part.pull = ev t ((tables.getD tt default).flushes.pull.foldl
        (fun acc tuple ↦ acc * fpP tuple (eqKernel alphas) beta fun c ↦ (tablePolys tr tt).getD c 0) 1) := by
      show ((AlgC.atParts tr (eqKernel alphas) beta (AlgC.atW tr t)).getD tt default).pull = _
      rw [atW_eq]; exact part_pull_eq hon ht6 t hrn _ _
    have hP' : part.push = ev t ((tables.getD tt default).flushes.push.foldl
        (fun acc tuple ↦ acc * fpP tuple (eqKernel alphas) beta fun c ↦ (tablePolys tr tt).getD c 0) 1) := by
      show ((AlgC.atParts tr (eqKernel alphas) beta (AlgC.atW tr t)).getD tt default).push = _
      rw [atW_eq]; exact part_push_eq hon ht6 t hrn _ _
    have hz : z = (Domain.zActP (tr.rows.getD tt 0) (tr.height tt)).eval t := by
      show (AlgC.atActive tr (AlgC.atW tr t)).getD tt 0 = _
      rw [atW_eq]; exact atActive_getD hon ht6 t (by omega)
    have hr31 : tr.height tt ≤ 31 := by omega
    have hc := (hon.rowsFit.2 tt ht6).2
    have hZ := congrArg (Polynomial.eval t) (Domain.zActP_mul_zPadP hr31 hc)
    rw [Polynomial.eval_mul] at hZ
    have hNt : (tp (tableLeafNumerator tr (eqKernel alphas) beta tt
        (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves))))).eval t =
        ((tp (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))).eval t * part.pull +
          part.push) * (Domain.zPadP (tr.rows.getD tt 0) (tr.height tt)).eval t +
        ((tp (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))).eval t + 1) *
          (Domain.zActP (tr.rows.getD tt 0) (tr.height tt)).eval t := by
      rw [← ev_apply]
      simp only [tableLeafNumerator, map_add, map_mul, map_one]
      rw [hP, hP', ev_apply _ (zPadP _ _), ev_apply _ (zActP _ _), tp_zPadP hr31, tp_zActP, ev_apply]
    have hex := congrArg (Polynomial.eval t) (leafQuotient_exact hon hbad hH hb hN)
    rw [Polynomial.eval_mul, hNt] at hex
    have hwr : wr = (wP b.r).eval t := by
      show (AlgC.atW tr t).getD b.r 0 = _
      rw [atW_eq, digits_getD' t (by omega)]
    rw [show multilinearEval (c2Of tr alphas beta gamma).heapB.toList
        (mixedPoint w tr.shape.heap.h b.position b.r) = _ from hmix, tp_eval]
    have hwr' : wr = (wP (tr.height tt)).eval t := by rw [hwr, e']
    rw [← hz] at hex hZ
    rw [← hwr] at hex
    rw [← hwr'] at hZ
    set R := (tp (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))).eval t
    set Zp := (Domain.zPadP (tr.rows.getD tt 0) (tr.height tt)).eval t
    set Q := (tp (divM (tableLeafNumerator tr (eqKernel alphas) beta tt
      (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves)))) (wPoly b.r))).eval t
    linear_combination (-z) * hex + (R * part.pull + part.push) * hZ +
      (part.pull * wr * R + z * z * R) * Domain.two_eq_zero_E

end Honest

end UniComplete.AlgH
