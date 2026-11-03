-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Eval
import UniSound.Ids.Facts

/-!
# The setup's bytecode tuple at `(α, ω_x)` (`BcTupleEval`)

The setup's column `bytecodeTuple` is one limb of `lb + 4` variables, aligned in its stack: word
`s + 16 k` is slot `s` of instruction `k`. Its claim at the point `(α, w_0, …, w_{lb−1})` is
`Σ_{y < 2^(lb+4)} eq((α, w), y) C(off + y)`; splitting the cube as `y = s + 16 k` (`sum_range_mul_split`)
and the `eq` factor as `eq(α, s) eq(w, k)` (`cubeEq_split`), at `ω_x` the inner sum over `k` is slot `s`'s
basis-`B` value at `x` (`ofK_basisValue`), and `eq(α, s)` is `eqKernel α`'s entry `s`
(`bcTuple_core`, for any stack).

**`bcTupleEval_of_heapGood`**: `BcTupleEval D` for a deployment whose heap is `HeapGood` (so
`lb ≤ h ≤ 24`), from the setup's limbs (`setupLimbs`), their alignment (`layoutAligned_new`) and the basis
(`betaCantor`); the setup stack itself is never unfolded. **`bcTupleEval_reference`** at the reference
shape.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial UniSound.Ids.Eval

/-- A sum over `a N` points as `N` blocks of `a`: `y = s + a k`. -/
theorem sum_range_mul_split (f : ℕ → E) (a : ℕ) : ∀ N : ℕ,
    ∑ y ∈ range (a * N), f y = ∑ k ∈ range N, ∑ s ∈ range a, f (s + a * k)
  | 0 => by simp
  | N + 1 => by
    rw [show a * (N + 1) = a * N + a by ring, Finset.sum_range_add, sum_range_mul_split f a N,
      Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [add_comm]

/-- **`eq` on `(α, q)` at `s + 16 k`** is `eq(α, s) eq(q, k)`, `α` of four coordinates, `s < 16`. -/
theorem cubeEq_split (α q : List E) (hα : α.length = 4) (lb s k : ℕ) (hs : s < 16) :
    cubeEq (α ++ q) (lb + 4) (s + 16 * k) = cubeEq α 4 s * cubeEq q lb k := by
  have hbit : ∀ j, (s + 16 * k).testBit j = if j < 4 then s.testBit j else k.testBit (j - 4) := by
    intro j
    rw [add_comm, show 16 * k = 2 ^ 4 * k by norm_num]
    exact Nat.testBit_two_pow_mul_add (i := 4) k (lt_of_lt_of_eq hs (by norm_num : (16 : ℕ) = 2 ^ 4)) j
  unfold cubeEq
  rw [show lb + 4 = 4 + lb by ring, Finset.prod_range_add]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun j hj ↦ ?_) (Finset.prod_congr rfl fun j _ ↦ ?_)
  · have hj4 := Finset.mem_range.mp hj
    rw [hbit j, ite_eq_left hj4, List.getD_append _ _ _ _ (by omega)]
  · rw [hbit (4 + j), ite_eq_right (show ¬ 4 + j < 4 by omega), show 4 + j - 4 = j by omega,
      List.getD_append_right _ _ _ _ (by omega), hα, show 4 + j - 4 = j by omega]

/-- **A basis-`B` value as a claim**: `basisValue g v x = Σ_i eq(ω_{x ≫ ·}, i) g(i)`. -/
theorem ofK_basisValue (g : ℕ → K) (v x : ℕ) :
    ofK (basisValue (Array.ofFn (n := 2 ^ v) fun i ↦ g i.val) v x) =
      ∑ i ∈ range (2 ^ v), cubeEq (((List.range v).map fun l ↦ point (x >>> l)).map ofK) v i *
        ofK (g i) := by
  unfold basisValue
  rw [mleK_eq_sum _ _ (by simp), ofK_sum]
  simp only [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [ofK_mul, ofK_cubeEqK]
  congr 1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [hi]

/-- `eqKernel α`'s entry `s` is `eq(α, s)`. -/
theorem eqKernel_getD_cubeEq (α : List E) (hα : α.length = 4) (s : ℕ) (hs : s < 16) :
    (eqKernel α).getD s 0 = cubeEq α 4 s := by
  rw [Facts.eqKernel_getD _ _ (by rw [hα]; exact lt_of_lt_of_eq hs (by norm_num : (16 : ℕ) = 2 ^ 4)), hα]
  unfold cubeEq
  exact Finset.prod_congr rfl fun j _ ↦ (one_add_ite _ _).symm

/-- **The bytecode tuple's claim at `(α, ω_x)`**, for any stack: `Σ_s eq(α, s)` times slot `s`'s
basis-`B` value at instruction `x`. -/
theorem bcTuple_core (h : BetaCantor) (L : StackLayout) (V : ℕ) (C : Stk) (lb off x : ℕ)
    (alphas : List E) (ha : alphas.length = 4) (hl : L.limbs .bytecodeTuple = [(0, lb + 4, off)])
    (hal : 2 ^ (lb + 4) ∣ off) (hin : off + 2 ^ (lb + 4) ≤ 2 ^ L.vars) (hLV : L.vars ≤ V)
    (hlb : lb ≤ 24) (hx : x < 2 ^ lb) :
    (colPoly L V C .bytecodeTuple
        (fun l ↦ if l < 4 then Polynomial.C (alphas.getD l 0) else digitP (l - 4))).eval (pointE x) =
      ∑ s : Fin 16, (eqKernel alphas).getD s.val 0 *
        ofK (basisValue (Array.ofFn (n := 2 ^ lb) fun k ↦ C (off + s.val + 16 * k.val)) lb x) := by
  have hx24 : x < 2 ^ 24 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hlb)
  have h16 : 2 ^ (lb + 4) = 16 * 2 ^ lb := by rw [pow_add]; ring
  have hoff : off < 2 ^ V := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hLV
    have := Nat.two_pow_pos (lb + 4)
    omega
  set q : List E := ((List.range lb).map fun l ↦ point (x >>> l)).map ofK with hq
  have hqget : ∀ l < lb, q.getD l 0 = pointE (x >>> l) := fun l hl ↦ by
    rw [hq, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
    rfl
  unfold colPoly
  rw [hl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    blockBase_of_aligned hal hoff]
  simp only [limbScale, ite_true, map_one, one_mul]
  rw [eval_mlP _ (lb + 4) _ (pointE x) (alphas ++ q) (fun l hl ↦ by
    by_cases h4 : l < 4
    · rw [ite_eq_left h4, eval_C, List.getD_append _ _ _ _ (by omega)]
    · rw [ite_eq_right h4, eval_digitP_pointE h _ hx24, List.getD_append_right _ _ _ _ (by omega), ha,
        hqget _ (by omega)])]
  rw [h16, sum_range_mul_split, Finset.sum_comm]
  rw [Fin.sum_univ_eq_sum_range (fun s ↦ (eqKernel alphas).getD s 0 *
    ofK (basisValue (Array.ofFn (n := 2 ^ lb) fun k ↦ C (off + s + 16 * k.val)) lb x)) 16]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hs
  rw [eqKernel_getD_cubeEq alphas ha s hs, ofK_basisValue (fun k ↦ C (off + s + 16 * k)) lb x,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [cubeEq_split alphas q ha lb s k hs]
  unfold stE
  rw [ite_eq_left (by omega), ← add_assoc]
  ring

/-- **`BcTupleEval`** for a deployment whose heap is `HeapGood`: the setup's bytecode tuple at
`(α, ω_x)` is `Σ_s eq(α, s)` times slot `s`'s value at `x`. -/
theorem bcTupleEval_of_heapGood (D : Deployment) (hH : HeapGood D.shape) : BcTupleEval D := by
  intro ch x hx
  obtain ⟨off, hl⟩ := (setupLimbs D.shape).2
  have hal : LayoutAligned (layoutOf D.shape .setup) := by
    rw [layoutOf_setup]; exact layoutAligned_new _
  have hb := hal _ (limbs_mem_blocks (b := (0, D.shape.logBytecode + 4, off))
    (by rw [hl]; exact List.mem_singleton_self _))
  have hlb : D.shape.logBytecode ≤ 24 := (lbFits D.shape).trans hH.2.1
  have htup : tupleOff D = off := by
    unfold tupleOff
    rw [UniSound.Ids.setupLayout_eq, hl]
    rfl
  unfold slotVal suP
  rw [htup]
  generalize setupStk D = C
  exact bcTuple_core betaCantor _ _ C _ off x _ (Facts.alphasOf_length ch) hl hb.1 hb.2
    (vars_le_batch _ _) hlb hx

/-- **`BcTupleEval` at the reference shape.** -/
theorem bcTupleEval_reference (D : Deployment) (hS : D.shape = reference) : BcTupleEval D :=
  bcTupleEval_of_heapGood D (hS ▸ heapGood_reference)

end UniSound.Ids

/-- info: 'UniSound.Ids.bcTupleEval_of_heapGood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.bcTupleEval_of_heapGood

/-- info: 'UniSound.Ids.bcTupleEval_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.bcTupleEval_reference
