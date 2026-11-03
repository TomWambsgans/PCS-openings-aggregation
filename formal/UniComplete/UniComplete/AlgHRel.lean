-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHAtT

/-!
# The heap's relations hold (milestone 4, the heap's layer: item 2)

For `TraceHonest tr`, `¬ BadFp tr α β`, a heap of height `h ≤ 28`, and the prover's values at any `t`
(`a := atTOf tr (c2DataOf tr (eqKernel α) β γ) α β γ t none`), every relation `heapRelations` states holds
(`Relation.Holds`) of the three stacks (`c1Stack tr`, `C2`'s, `setupStackOf tr`) at the layouts the verifier states
(`layoutIn (layouts tr.shape a.c2Columns)`, which are `layoutsOf tr.shape`'s, `atTOf_c2Columns_eq`):

* `T(t)`: the heap's term at `w[..h]` is the value sent (`rel_T`);
* **the tree** (`rel_tree`): `w_1 T(s(t)) + w_1 T(t) T(t + 1) + w_h (Q_0(t) + w_h Q_1) = 0`, by the tree quotient's
  exactness (`treeNumerator_eq_mul`) at `t`;
* **the root** (`rel_root`): `T(1) · fp(SEP_STATE, 1, 1) = fp(SEP_STATE, g^(2^lb − 1), 1)` (`heap_root`);
* **each block** (`rel_block`): the heap at its mixed point is `R_b(t)` (`mle_mixed`); an unused block's `R_u = 1`;
  a used block's leaf identity is its leaf quotient's exactness (`leafQuotient_exact`) at `t`, read through its chunks
  (`AlgC.chunksValue_chunksB`, the fit `leafQuotient_fits`), times `Z_act(t)` for a table;
* **the constraint quotient's chunks** (`rel_constraint`): their terms add up to `Q_W(t)`, the value sent (it is
  defined as their value).
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

/-- **The three stacks**: `C1`, `C2`, the setup. -/
def stacksOf (tr : Trace) (c2 : C2Data) : Commitment → Array K
  | .c1 => c1Stack tr
  | .c2 => c2.stack
  | .setup => setupStackOf tr

section Honest

variable {tr : Trace} (hon : TraceHonest tr) {alphas : List E} {beta gamma : E}

/-- The prover's `C2` (notation). -/
abbrev c2Of (tr : Trace) (alphas : List E) (beta gamma : E) : C2Data := c2DataOf tr (eqKernel alphas) beta gamma

theorem c2Of_heapB_size : (c2Of tr alphas beta gamma).heapB.size = 2 ^ tr.shape.heap.h := by
  show (bOfNovelE _ (novelOfValuesE _ (heapValues tr _ beta))).size = _
  rw [bOfNovelE, AlgC.subsetSumsE_size, novelOfValuesE, Bridge.Ntt.coefficients_size,
    heapValues_size _ _ _ (layoutOK_new _ _ _)]

theorem mem_c2_heap (shape : Shape) : (Column.heap, shape.heap.h, true) ∈ Shape.c2Columns shape := by
  rw [c2Columns_eq]; simp

theorem mem_c2_tree0 (shape : Shape) : (Column.treeQuotient 0, shape.heap.h, true) ∈ Shape.c2Columns shape := by
  rw [c2Columns_eq]; simp

theorem mem_c2_tree1 (shape : Shape) : (Column.treeQuotient 1, 0, true) ∈ Shape.c2Columns shape := by
  rw [c2Columns_eq]; simp

/-- A term on the heap, on `C2`. -/
theorem termEval_heap {pt : List E} (hpt : pt.length = tr.shape.heap.h) (rm : Option (List E)) (k : E) :
    termEval (StackLayout.new (Shape.c2Columns tr.shape)) (c2Of tr alphas beta gamma).stack rm (term .heap pt k) =
      k * multilinearEval (c2Of tr alphas beta gamma).heapB.toList pt := by
  rw [c2Stack_eq]
  exact termEval_c2col _ (mem_c2_heap tr.shape) (fun j ↦ Column.noConfusion) (fun _ _ ↦ rfl) c2Of_heapB_size hpt rm k


theorem treeShape (shape : Shape) : AlgC.ChunkShape [shape.heap.h, 0] :=
  Or.inr (Or.inl ⟨_, _, rfl, (layoutOK_new _ _ _).one_le⟩)

/-- A term on the tree quotient's chunk `c`, on `C2`. -/
theorem termEval_tree {c : ℕ} (hc : c < 2) {pt : List E} (hpt : pt.length = [tr.shape.heap.h, 0].getD c 0)
    (rm : Option (List E)) (k : E) :
    termEval (StackLayout.new (Shape.c2Columns tr.shape)) (c2Of tr alphas beta gamma).stack rm
        (term (.treeQuotient c) pt k) =
      k * multilinearEval ((c2Of tr alphas beta gamma).treeChunks.getD c #[]).toList pt := by
  rw [c2Stack_eq]
  have hsize := chunksB_size (q := treeQuotient tr.shape.heap.h (c2Of tr alphas beta gamma).heapNovel)
    (treeShape tr.shape) (c := c) (by simpa using hc)
  interval_cases c
  · exact termEval_c2col _ (mem_c2_tree0 tr.shape) (fun j ↦ Column.noConfusion) (fun _ _ ↦ rfl) hsize hpt rm k
  · exact termEval_c2col _ (mem_c2_tree1 tr.shape) (fun j ↦ Column.noConfusion) (fun _ _ ↦ rfl) hsize hpt rm k

include hon in
theorem LO_c2 (c2 : C2Data) (t : E) :
    layoutIn (layouts tr.shape (atTOf tr c2 alphas beta gamma t none).c2Columns) .c2 =
      StackLayout.new (Shape.c2Columns tr.shape) := by
  rw [layoutIn_c2, atTOf_c2Columns_eq hon]

/-- A relation all of whose terms are on `C2` holds when its `C2` sum is its value. -/
theorem holds_of_c2 (LO : Commitment → StackLayout) (SO : Commitment → Array K) (rm : Option (List E))
    (rel : Relation) (hall : ∀ t ∈ rel.terms, t.column.commitment = .c2)
    (h : (rel.terms.map fun t ↦ termEval (LO .c2) (SO .c2) rm t).sum = rel.value) : Relation.Holds LO SO rm rel := by
  unfold Relation.Holds
  rw [← h, List.map_congr_left fun t ht ↦ by rw [hall t ht]]

theorem term_column (c : Column) (p : List E) (k : E) : (term c p k).column = c := rfl


/-- The digits' count `atW` reads: `max h (r_W + 4) + 2`. -/
abbrev nW (tr : Trace) : ℕ := max tr.shape.heap.h (tr.shape.constraintVars + 4)

theorem atW_eq (tr : Trace) (t : E) : AlgC.atW tr t = digits t (nW tr + 1 + 1) := rfl

theorem length_take_atW (tr : Trace) (t : E) : ((AlgC.atW tr t).take tr.shape.heap.h).length = tr.shape.heap.h := by
  have : tr.shape.heap.h ≤ nW tr := le_max_left _ _
  rw [atW_eq, List.length_take, Domain.length_digits]; omega

theorem heapValues_size' (tr : Trace) (weights : Array E) (beta : E) :
    (heapValues tr weights beta).size = 2 ^ tr.shape.heap.h := heapValues_size _ _ _ (layoutOK_new _ _ _)

include hon in
/-- **`T(t)`**: the heap's term at `w[..h]` is the value sent. -/
theorem rel_T (t : E) (rm : Option (List E)) :
    Relation.Holds (layoutIn (layouts tr.shape (atTOf tr (c2Of tr alphas beta gamma) alphas beta gamma t none).c2Columns))
      (stacksOf tr (c2Of tr alphas beta gamma)) rm
      (Relation.equal .heap ((AlgC.atW tr t).take tr.shape.heap.h)
        (evalB (c2Of tr alphas beta gamma).heapB tr.shape.heap.h (AlgC.atW tr t))) := by
  refine holds_of_c2 _ _ _ _ (by simp [Relation.equal, term_column, Column.commitment]) ?_
  simp only [Relation.equal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [LO_c2 hon]
  show termEval _ (c2Of tr alphas beta gamma).stack rm _ = _
  rw [termEval_heap (length_take_atW tr t), one_mul]
  rfl

include hon in
/-- **The tree's relation** `w_1 T(s(t)) + w_1 T(t) T(t + 1) + w_h Q_0(t) + w_h² Q_1 = 0`. -/
theorem rel_tree (hH : tr.shape.heap.h ≤ 28) (t : E) (rm : Option (List E)) :
    Relation.Holds (layoutIn (layouts tr.shape (atTOf tr (c2Of tr alphas beta gamma) alphas beta gamma t none).c2Columns))
      (stacksOf tr (c2Of tr alphas beta gamma)) rm
      ⟨[term .heap (((AlgC.atW tr t).drop 1).take tr.shape.heap.h) ((AlgC.atW tr t).getD 1 0),
        term .heap (((AlgC.atW tr t).take tr.shape.heap.h).modify 0 (· + 1))
          ((AlgC.atW tr t).getD 1 0 * evalB (c2Of tr alphas beta gamma).heapB tr.shape.heap.h (AlgC.atW tr t)),
        term (.treeQuotient 0) ((AlgC.atW tr t).take tr.shape.heap.h) ((AlgC.atW tr t).getD tr.shape.heap.h 0),
        term (.treeQuotient 1) [] ((AlgC.atW tr t).getD tr.shape.heap.h 0 * (AlgC.atW tr t).getD tr.shape.heap.h 0)],
        0⟩ := by
  have hL := layoutOK_new tr.shape.logMemory tr.shape.logBytecode tr.shape.heights
  have hh : 1 ≤ tr.shape.heap.h := hL.one_le
  set h := tr.shape.heap.h with hhdef
  set M := nW tr
  have hMh : h ≤ M := le_max_left _ _
  have hv := heapValues_size' tr (eqKernel alphas) beta
  set c2 := c2Of tr alphas beta gamma with hc2
  set T := tp (ofNovel h c2.heapNovel)
  set Q := tp (treeQuotient h c2.heapNovel)
  refine holds_of_c2 _ _ _ _ (by simp [term_column, Column.commitment]) ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [LO_c2 hon]
  show termEval _ c2.stack rm _ + (termEval _ c2.stack rm _ + (termEval _ c2.stack rm _ + termEval _ c2.stack rm _)) = 0
  have hlen1 : (((AlgC.atW tr t).drop 1).take h).length = h := by
    rw [atW_eq, List.length_take, List.length_drop, Domain.length_digits]; omega
  have hlen2 : (((AlgC.atW tr t).take h).modify 0 (· + 1)).length = h := by
    rw [List.length_modify, length_take_atW]
  rw [termEval_heap hlen1, termEval_heap hlen2, termEval_tree (c := 0) (by norm_num) (length_take_atW tr t),
    termEval_tree (c := 1) (by norm_num) rfl]
  -- the heap's values
  have hS : multilinearEval c2.heapB.toList (((AlgC.atW tr t).drop 1).take h) = T.eval (t * t + t) := by
    show evalB c2.heapB h ((digits t (M + 1 + 1)).drop 1) = _
    rw [digits_drop_one]
    exact evalB_heap (by omega) hv _
  have hX : multilinearEval c2.heapB.toList (((AlgC.atW tr t).take h).modify 0 (· + 1)) = T.eval (t + 1) := by
    rw [atW_eq, take_modify_digits t (by omega)]
    exact evalB_heap (by omega) hv _
  have hT0 : evalB c2.heapB h (AlgC.atW tr t) = T.eval t := evalB_heap (by omega) hv _
  -- the tree quotient's chunks
  obtain ⟨c0, c1, hcs⟩ := List.length_eq_two.mp (chunksB_length (q := treeQuotient h c2.heapNovel) (treeShape tr.shape))
  have hcs' : c2.treeChunks = [c0, c1] := hcs
  have hQ := AlgC.chunksValue_chunksB (treeQuotient h c2.heapNovel) [h, 0] (treeShape tr.shape)
    (natDegree_treeQuotient_lt hh _) t (M + 1 + 1) (by simp; omega)
  rw [show chunksB (treeQuotient h c2.heapNovel) [h, 0] = [c0, c1] from hcs] at hQ
  simp only [AlgC.chunksValue, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, zero_add,
    one_mul] at hQ
  rw [AlgC.pEval_eq] at hQ
  rw [hcs']
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  -- the numerator at t
  have hNum := congrArg (Polynomial.eval t) (treeNumerator_eq_mul hh hH hv (heapValues_tree tr _ beta hL))
  rw [treeNumerator_eq hh] at hNum
  simp only [Polynomial.eval_mul, Polynomial.eval_add, eval_comp, Polynomial.eval_pow, eval_X,
    Polynomial.eval_one] at hNum
  rw [pow_two] at hNum
  have hNum' : (t * t + t) * (T.eval (t * t + t) + T.eval t * T.eval (t + 1)) = (wP h).eval t * Q.eval t := hNum
  have hw1 : (AlgC.atW tr t).getD 1 0 = t * t + t := by
    rw [atW_eq, digits_getD' t (by omega), wP_succ, wP_zero]; simp [pow_two]
  have hwh : (AlgC.atW tr t).getD h 0 = (wP h).eval t := by rw [atW_eq, digits_getD' t (by omega)]
  rw [hS, hX, hT0, hw1, hwh]
  change _ + (_ + ((wP h).eval t * evalB c0 h (AlgC.atW tr t) +
    (wP h).eval t * (wP h).eval t * evalB c1 0 (AlgC.atW tr t))) = 0
  rw [digits_getD' t (by omega : h < M + 1 + 1)] at hQ
  have hQ' : evalB c0 h (AlgC.atW tr t) + (wP h).eval t * evalB c1 0 (AlgC.atW tr t) = Q.eval t := hQ
  linear_combination hNum' + (wP h).eval t * hQ' + ((wP h).eval t * Q.eval t) * Domain.two_eq_zero_E


include hon in
/-- **The root's relation**: `T(1) · fp(SEP_STATE, 1, 1) = fp(SEP_STATE, g^(2^lb − 1), 1)`. -/
theorem rel_root (hbad : ¬ BadFp tr alphas beta) (hH : tr.shape.heap.h ≤ 28) (t : E) (rm : Option (List E)) :
    Relation.Holds (layoutIn (layouts tr.shape (atTOf tr (c2Of tr alphas beta gamma) alphas beta gamma t none).c2Columns))
      (stacksOf tr (c2Of tr alphas beta gamma)) rm
      ⟨[term .heap ((List.range tr.shape.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0)
        (beta + (eqKernel alphas).getD 0 0 * sepState + (eqKernel alphas).getD 1 0 + (eqKernel alphas).getD 2 0)],
        beta + (eqKernel alphas).getD 0 0 * sepState +
          (eqKernel alphas).getD 1 0 * UniStatement.gpow (2 ^ tr.shape.logBytecode - 1) + (eqKernel alphas).getD 2 0⟩ := by
  have hL := layoutOK_new tr.shape.logMemory tr.shape.logBytecode tr.shape.heights
  have hh : 1 ≤ tr.shape.heap.h := hL.one_le
  have hv := heapValues_size' tr (eqKernel alphas) beta
  refine holds_of_c2 _ _ _ _ (by simp [term_column, Column.commitment]) ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [LO_c2 hon]
  show termEval _ (c2Of tr alphas beta gamma).stack rm _ = _
  have e : evalB (c2Of tr alphas beta gamma).heapB tr.shape.heap.h (digits 1 tr.shape.heap.h) =
      (tp (ofNovel tr.shape.heap.h (novelOfValuesE tr.shape.heap.h (heapValues tr (eqKernel alphas) beta)))).eval 1 :=
    evalB_heap le_rfl hv 1
  rw [termEval_heap (by simp), atOne_eq (n := tr.shape.heap.h) le_rfl, mle_take, e, ← pointE_one,
    eval_ofNovel_novelOfValuesE hH hv (Nat.one_lt_two_pow (by omega))]
  have hroot := heap_root hon hbad (beta := beta)
  unfold stateFp at hroot
  rw [mul_one] at hroot
  linear_combination hroot

/-! ### A block's leaf quotient on `C2` -/

/-- `C2`'s leaf quotients (`c2DataOf`'s `leafChunks`' step). -/
def leafChunkF (tr : Trace) (weights : Array E) (beta : E) (x : Block × ℕ) : Option (ℕ × List ℕ × List (Array E)) :=
  match Shape.leafDegree x.1, leafNumerator tr weights beta x.1
      (ofNovel x.1.r (novelOfValuesE x.1.r (blockLeaves tr weights beta x.1.leaves))) with
  | some d, some numerator =>
    let sizes := chunks (d + 1)
    some (x.2, sizes, chunksB (divM numerator (wPoly x.1.r)) sizes)
  | _, _ => none

theorem leafChunks_eq (tr : Trace) (weights : Array E) (beta gamma : E) :
    (c2DataOf tr weights beta gamma).leafChunks =
      (tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length)).filterMap (leafChunkF tr weights beta) := rfl

theorem leafChunkF_fst (tr : Trace) (weights : Array E) (beta : E) {x : Block × ℕ} {e : ℕ × List ℕ × List (Array E)}
    (h : leafChunkF tr weights beta x = some e) : e.1 = x.2 := by
  unfold leafChunkF at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · cases h

theorem find_filterMap {α γ : Type} (F : α × ℕ → Option (ℕ × γ)) (hF : ∀ y e, F y = some e → e.1 = y.2) :
    ∀ (L : List (α × ℕ)), L.Pairwise (fun a b ↦ a.2 < b.2) → ∀ x ∈ L, ∀ e, F x = some e →
      (L.filterMap F).find? (fun e ↦ e.1 == x.2) = some e
  | [], _, _, hx, _, _ => absurd hx List.not_mem_nil
  | y :: L, hp, x, hx, e, he => by
    rw [List.pairwise_cons] at hp
    rw [List.filterMap_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [he, List.find?_cons_of_pos (by rw [hF _ _ he]; simp)]
    · have hlt := hp.1 x hx
      cases hy : F y with
      | none => exact find_filterMap F hF L hp.2 x hx e he
      | some e' =>
        rw [List.find?_cons_of_neg (by rw [hF _ _ hy]; simp; omega)]
        exact find_filterMap F hF L hp.2 x hx e he

theorem mem_zip_range {α : Type} {l : List α} {x : α × ℕ} (hx : x ∈ l.zip (List.range l.length)) :
    ∃ hi : x.2 < l.length, l[x.2] = x.1 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < l.length := by simpa using hi
  rw [List.getElem_zip, List.getElem_range]
  exact ⟨hi', rfl⟩

/-- **A term on a used block's leaf quotient's chunk `c`, on `C2`.** -/
theorem termEval_leaf {b : Block} {index : ℕ}
    (hx : (b, index) ∈ tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length)) {d : ℕ}
    (hd : Shape.leafDegree b = some d) {N : Poly}
    (hN : leafNumerator tr (eqKernel alphas) beta b
      (ofNovel b.r (novelOfValuesE b.r (blockLeaves tr (eqKernel alphas) beta b.leaves))) = some N)
    {c : ℕ} (hc : c < (chunks (d + 1)).length) {pt : List E} (hpt : pt.length = (chunks (d + 1)).getD c 0)
    (rm : Option (List E)) (k : E) :
    termEval (StackLayout.new (Shape.c2Columns tr.shape)) (c2Of tr alphas beta gamma).stack rm
        (term (.leafQuotient index c) pt k) =
      k * multilinearEval ((chunksB (divM N (wPoly b.r)) (chunks (d + 1))).getD c #[]).toList pt := by
  have hF : leafChunkF tr (eqKernel alphas) beta (b, index) =
      some (index, chunks (d + 1), chunksB (divM N (wPoly b.r)) (chunks (d + 1))) := by
    unfold leafChunkF
    dsimp only
    rw [hd, hN]
  have hfind := find_filterMap (leafChunkF tr (eqKernel alphas) beta) (fun y e h ↦ leafChunkF_fst tr _ beta h) _
    (zip_range_pairwise _) _ hx _ hF
  have hshape := (AlgC.chunks_spec (n := d + 1) (by omega)).1
  have hmem : (Column.leafQuotient index c, (chunks (d + 1)).getD c 0, true) ∈ Shape.c2Columns tr.shape := by
    rw [c2Columns_eq]
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨(b, index), hx, ?_⟩)
    unfold shapeBlockCols
    rw [hd]
    refine List.mem_map.mpr ⟨((chunks (d + 1))[c], c), ?_, ?_⟩
    · have : ((chunks (d + 1)).zip (List.range (chunks (d + 1)).length))[c]'(by simpa using hc) =
          ((chunks (d + 1))[c], c) := by
        rw [List.getElem_zip, List.getElem_range]
      rw [← this]
      exact List.getElem_mem _
    · rw [List.getD_eq_getElem _ _ hc]
  rw [c2Stack_eq]
  refine termEval_c2col _ hmem (fun j ↦ Column.noConfusion) (fun l _ ↦ ?_) (chunksB_size hshape hc) hpt rm k
  show (match (c2Of tr alphas beta gamma).leafChunks.find? (·.1 == index) with
    | some (_, _, parts) => limbWords (parts.getD c #[]) l | none => #[]) = _
  rw [leafChunks_eq, hfind]

end Honest

end UniComplete.AlgH
