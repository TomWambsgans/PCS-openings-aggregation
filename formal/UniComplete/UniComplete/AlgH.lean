-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHRelD

/-!
# The honest prover's heap on `C2` (milestone 4, layer AlgH)

The headline facts of the heap's layer, for a placed trace `tr`, bus challenges `α` (`eqKernel α` the weights),
`β` and a heap of height `h ≤ 28` (the statement's transform, `PcsQuotient.Domain.coefficients`, has `28` basis
vectors; at a deployable shape `C2`'s `2^28` words bound `h` lower):

1. **The polynomial identities** (`Polynomial E`, through CompPoly's `toPoly`, `AlgHPoly`):
   * `treeQuotient_exact_fits` (any trace): the heap's values are a product tree (`heapValues_tree`), so
     `w_h ∣ w_1 (T(s(X)) + T(X) T(X + 1))` and the tree quotient has degree `≤ 2^h`, its chunks `[h, 0]`;
     `X_k(s(x)) = X_{2k}(x)`, `X_k(x + 1) = X_k(x) + X_{k−1}(x)` for odd `k` (`tp_ofNovel_compSNovel`,
     `tp_ofNovel_shiftOneNovel`);
   * **the root** `heap_root` (`TraceHonest`, `¬ BadFp`): `T_1 · fp(SEP_STATE, 1, 1) = fp(SEP_STATE, g^(2^lb − 1), 1)`
     from the bus's permutation;
   * **every used block's leaf quotient** (`TraceHonest`, `¬ BadFp`): exact (`leafQuotient_exact`) and fitting
     `chunks (d + 1)`, `d` its `Shape.leafDegree` (`leafQuotient_fits`, under `RowsFit`, every height: **every honest
     run fits**).
2. **The heap's relations hold** (`heapRelations_hold`, `atTOf_heap_holds`): at any `t`, every relation
   `heapRelations` states, at the layouts the verifier states, which are `layoutsOf` (`atTOf_c2Columns_eq`: the
   verifier's `C2` columns are `Shape.c2Columns`).

The layout facts (`layoutOK_new`, `used_perm`) and the restriction to a coset (`mle_mixed`) hold at every shape.
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters
open UniComplete.Domain (wP)

/-- **The tree quotient is exact and fits its chunks `[h, 0]`** (any trace, any weights; `h ≤ 28`). -/
theorem treeQuotient_exact_fits (tr : Trace) (weights : Array E) (beta : E) (hH : tr.shape.heap.h ≤ 28) :
    tp (treeNumerator tr.shape.heap.h (novelOfValuesE tr.shape.heap.h (heapValues tr weights beta))) =
        wP tr.shape.heap.h *
          tp (treeQuotient tr.shape.heap.h (novelOfValuesE tr.shape.heap.h (heapValues tr weights beta))) ∧
      (tp (treeQuotient tr.shape.heap.h (novelOfValuesE tr.shape.heap.h (heapValues tr weights beta)))).natDegree <
        ([tr.shape.heap.h, 0].map (2 ^ ·)).sum := by
  have hL := layoutOK_new tr.shape.logMemory tr.shape.logBytecode tr.shape.heights
  exact ⟨treeNumerator_eq_mul hL.one_le hH (heapValues_size' tr weights beta) (heapValues_tree tr weights beta hL),
    natDegree_treeQuotient_lt hL.one_le _⟩

end UniComplete.AlgH

/-! ### Axioms -/

/-- info: 'UniComplete.AlgH.treeQuotient_exact_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.treeQuotient_exact_fits

/-- info: 'UniComplete.AlgH.heapValues_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.heapValues_tree

/-- info: 'UniComplete.AlgH.tp_ofNovel_compSNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.tp_ofNovel_compSNovel

/-- info: 'UniComplete.AlgH.tp_ofNovel_shiftOneNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.tp_ofNovel_shiftOneNovel

/-- info: 'UniComplete.AlgH.heap_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.heap_root

/-- info: 'UniComplete.AlgH.leafNumerator_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.leafNumerator_eval

/-- info: 'UniComplete.AlgH.leafQuotient_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.leafQuotient_exact

/-- info: 'UniComplete.AlgH.leafQuotient_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.leafQuotient_fits

/-- info: 'UniComplete.AlgH.table_degree_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.table_degree_arith

/-- info: 'UniComplete.AlgH.layoutOK_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.layoutOK_new

/-- info: 'UniComplete.AlgH.used_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.used_perm

/-- info: 'UniComplete.AlgH.mle_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.mle_mixed

/-- info: 'UniComplete.AlgH.atTOf_c2Columns_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.atTOf_c2Columns_eq

/-- info: 'UniComplete.AlgH.heapRelations_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.heapRelations_hold

/-- info: 'UniComplete.AlgH.atTOf_heap_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgH.atTOf_heap_holds
