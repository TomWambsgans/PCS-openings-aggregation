-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Leaf
import UniSound.Ids.CvecOk

/-!
# The identities as polynomials give the heap and the constraint vectors (`MainOfPolysP`)

Where every identity of `polysOf` is the zero polynomial:

* **the constraint vectors** (`cvec_of_wP`): `Z_bad ≠ 0` (`zBad_ne_zero`, by the coordinate functionals),
  so `Σ_i γ^i M_i W_i + Q_W w_{r_W} = 0`, and on `V_{r_W}` `w_{r_W} = 0`: `Σ_i γ^i M_i(ω_x) W_i(ω_x) = 0`;
* **the tree** (`tree_of_treeP`): on `V_h`, `T(s(x)) = T(x) T(x + 1)` off `V_1` (`Heap.tree_of_quotient`);
* **the root** (`root_of_rootP`): `T(1) fp(init) = fp(fin)`;
* **every block's leaves** (`leaves_of_blockP`): the restriction at `ω_k` is `T` at the block's position
  `pos + k` (`mixP_eval_pointE`); a table's active rows have `T P = P'` and its padding rows `T = 1` (the
  padded leaf, `Z_act`'s zeros the active rows, `ZActZero`); the memory's and the bytecode's `T P = P'`;
  an unused block's `T = 1`; `P`, `P'` the rows' fingerprints (`pullP_eval`, the forms at the rows' values).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

/-! ## The constraint vectors -/

theorem sum_zip_range {α : Type} (F : α × ℕ → E) : ∀ (l : List α) (n : ℕ) (d : α),
    ((l.zip (List.range' n l.length)).map F).sum = ∑ i ∈ range l.length, F (l.getD i d, n + i)
  | [], _, _ => by simp
  | a :: l, n, d => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      sum_zip_range F l (n + 1) d, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show n + 1 + i = n + (i + 1) by ring]

/-- The batched constraints at a point are the constraint vector's combination by `γ`. -/
theorem eval_batched (cs : List (Polynomial E × Polynomial E)) (γ θ : E) :
    (((cs.zip (List.range cs.length)).map fun mw ↦ C (γ ^ mw.2) * mw.1.1 * mw.1.2).sum).eval θ =
      powComb (cs.map fun mw ↦ (mw.1 * mw.2).eval θ) γ := by
  rw [eval_listSum, List.map_map, List.range_eq_range', sum_zip_range _ cs 0 (0, 0), powComb_eq_range,
    List.length_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  simp only [Function.comp_apply, zero_add, Polynomial.eval_mul, eval_C]
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  ring

/-- **`Z_bad ≠ 0`** (the coordinate functionals: `y_0(β_1) = 0 ≠ β_1`, `y_0(0) = 0`, `y_0(β_0) = 1`). -/
theorem zBad_ne_zero (S : Shape) (h : BetaCantor) (hf : FunctionalsCorrect (S.heights.getD opBlake2s 0))
    (h2 : 2 ≤ S.heights.getD opBlake2s 0) (p0 : E) : zBad S p0 ≠ 0 := by
  have hb1 : ofK (beta.getD 1 0) ≠ 0 := by
    intro h0
    have := (cantorE h).succ 0 (by norm_num)
    change QuotientSecurity.sq (ofK (beta.getD 1 0)) = ofK (beta.getD 0 0) at this
    rw [h0, QuotientSecurity.sq_zero, h.1, ofK_one] at this
    exact zero_ne_one this
  unfold zBad
  refine mul_ne_zero ?_ ?_
  · intro h0
    have := congrArg (Polynomial.eval (ofK (beta.getD 1 0))) h0
    rw [Polynomial.eval_add, eval_yP_beta hf (by omega) (by omega), eval_X, eval_zero] at this
    simp only [show ¬ (0 : ℕ) = 1 by norm_num, ite_false, zero_add] at this
    exact hb1 this
  · intro h0
    by_cases hp : p0 = 0
    · have := congrArg (Polynomial.eval (ofK (beta.getD 0 0))) h0
      rw [Polynomial.eval_add, eval_yP_beta hf (by omega) (by omega), eval_C, hp, eval_zero] at this
      simp at this
    · have := congrArg (Polynomial.eval 0) h0
      rw [Polynomial.eval_add, eval_yP_zero, eval_C, eval_zero, zero_add] at this
      exact hp this

/-- **The constraint vectors from the constraint identity.** -/
theorem cvec_of_wP (D : Deployment) (hr : C1Reading D) (h2 : 2 ≤ D.shape.heights.getD opBlake2s 0)
    (c1 c2 : Stk) (s : USt) (γ p0 : E) (hfit : CountsFit D.shape s.2)
    (hW : wP D.shape c1 c2 (publicWordsOf s.1.toList) γ p0 = 0) :
    ∀ x < 2 ^ D.shape.constraintVars, powComb (cvecOf D c1 s x) γ = 0 := by
  intro x hx
  unfold wP at hW
  have hin := (mul_eq_zero.mp hW).resolve_left (zBad_ne_zero D.shape hr.beta hr.functionals h2 p0)
  have hx24 : x < 2 ^ 24 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hr.rW)
  have he := congrArg (Polynomial.eval (pointE x)) hin
  rw [Polynomial.eval_add, Polynomial.eval_mul, eval_digitP_pointE hr.beta _ hx24,
    show x >>> D.shape.constraintVars = 0 by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hx,
    pointE_zero, mul_zero, add_zero, eval_zero, eval_batched] at he
  unfold cvecOf
  rw [ite_eq_left hfit]
  exact he

/-! ## The tree and the root -/

/-- The verifier's Cantor basis cut to `n ≤ 24` vectors. -/
def cantorN (h : BetaCantor) (n : ℕ) (hn : n ≤ 24) : QuotientSecurity.CantorBasis E n :=
  Heap.Deployed.restrict (cantorE h) n hn

theorem omega_cantorN (h : BetaCantor) (n : ℕ) (hn : n ≤ 24) {i : ℕ} (hi : i < 2 ^ n) :
    Heap.omega (cantorN h n hn) i = pointE i := by
  have hi24 : i < 2 ^ 24 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hn)
  rw [pointE_eq_omega h hi24]
  unfold Heap.omega
  rw [← Finset.sum_range_add_sum_Ico _ hn]
  have hz : ∑ k ∈ Ico n 24, (if i.testBit k then (cantorE h).β k else 0) = 0 :=
    Finset.sum_eq_zero fun k hk ↦ by
      rw [Finset.mem_Ico] at hk
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk.1))]
      simp
  rw [hz, add_zero]
  exact Finset.sum_congr rfl fun k _ ↦ rfl

theorem c2P_eval_congr (S : Shape) (c2 : Stk) (col : Column) (P P' : ℕ → Polynomial E) (x y : E)
    (h : ∀ l, (P l).eval x = (P' l).eval y) : (c2P S c2 col P).eval x = (c2P S c2 col P').eval y := by
  unfold c2P
  exact colPoly_eval_congr (layoutOf S .c2) (batchVars S) c2 col P P' x y h

/-- The heap's values at the points. -/
noncomputable def heapT (S : Shape) (c2 : Stk) (i : ℕ) : E := (c2P S c2 .heap digitP).eval (pointE i)

/-- **The tree from its identity.** -/
theorem tree_of_treeP (S : Shape) (c2 : Stk) (h : BetaCantor) (hh1 : 1 ≤ S.heap.h) (hh : S.heap.h ≤ 24)
    (ht : treeP S c2 = 0) : Heap.TreeHolds S.heap.h (heapT S c2) := by
  have hq : ∀ x : E, QuotientSecurity.sq x * ((c2P S c2 .heap digitP).eval (QuotientSecurity.sq x) +
      (c2P S c2 .heap digitP).eval x * (c2P S c2 .heap digitP).eval (x + 1)) +
      QuotientSecurity.sq^[S.heap.h] x * (c2P S c2 (.treeQuotient 0) digitP +
        digitP S.heap.h * c2P S c2 (.treeQuotient 1) digitP).eval x = 0 := by
    intro x
    have := congrArg (Polynomial.eval x) ht
    unfold treeP at this
    simp only [Polynomial.eval_add, Polynomial.eval_mul, eval_zero] at this
    rw [eval_digitP 1, eval_digitP S.heap.h,
      c2P_eval_congr _ _ _ (fun l ↦ digitP (l + 1)) digitP x (QuotientSecurity.sq x)
        (fun l ↦ (digitP_eval_sq l x).symm),
      c2P_eval_congr _ _ _ (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l) digitP x (x + 1)
        (fun l ↦ (digitP_eval_add_one l x).symm)] at this
    rw [Function.iterate_one] at this
    rw [Polynomial.eval_add, Polynomial.eval_mul, eval_digitP]
    exact this
  have h1 := Heap.treeHolds_omega (cantorN h S.heap.h hh) hh1
    (T := fun x ↦ (c2P S c2 .heap digitP).eval x)
    (Heap.tree_of_quotient (cantorN h S.heap.h hh) (T := fun x ↦ (c2P S c2 .heap digitP).eval x)
      (Q := fun x ↦ (c2P S c2 (.treeQuotient 0) digitP +
        digitP S.heap.h * c2P S c2 (.treeQuotient 1) digitP).eval x)
      (fun x _ ↦ hq x))
  intro i hi2 hi
  have hj1 : i >>> 1 < 2 ^ S.heap.h :=
    lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hi
  have hj2 : i ^^^ 1 < 2 ^ S.heap.h := Nat.xor_lt_two_pow hi (Nat.one_lt_two_pow (by omega))
  have := h1 i hi2 hi
  simp only at this
  unfold heapT
  rwa [omega_cantorN h _ hh hj1, omega_cantorN h _ hh hi, omega_cantorN h _ hh hj2] at this

/-- **The root from its identity**: `T(1) fp(init) = fp(fin)`. -/
theorem root_of_rootP (S : Shape) (c2 : Stk) (h : BetaCantor) (weights : Array E) (β : E)
    (hr : rootP S c2 weights β = 0) : heapT S c2 1 * rootInit weights β = rootFin S weights β := by
  have he := congrArg (Polynomial.eval 0) hr
  unfold rootP at he
  rw [Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_C, eval_zero,
    c2P_eval_congr _ _ _ (fun l ↦ if l = 0 then (1 : Polynomial E) else 0) digitP 0 1
      (fun l ↦ (digitP_eval_one l).symm)] at he
  have hp1 : pointE 1 = 1 := by
    rw [pointE_eq_omega h (by norm_num), Heap.omega_one (cantorE h) (by norm_num)]
  unfold heapT
  rw [hp1, mul_comm]
  exact CharTwo.add_eq_zero.mp he

/-! ## Fingerprints -/

/-- **A bus fingerprint by the verifier's weights** (`eqKernel`, `EqKernelLagrange`). -/
theorem fp_eq (hE : EqKernelLagrange) (ch : List E) (t : Vector K 16) :
    Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) t =
      ch.getD 4 0 + ∑ s : Fin 16, (eqKernel (alphasOf ch)).getD s.val 0 * ofK (t.get s) := by
  unfold Heap.fp LeanVM.Protocol.fingerprint
  refine congrArg (ch.getD 4 0 + ·) (Finset.sum_congr rfl fun s _ ↦ ?_)
  rw [hE ch s, Vector.get_eq_getElem, Vector.get_eq_getElem, Fin.getElem_fin]

theorem sum_fin16 (f : ℕ → E) : ∑ s : Fin 16, f s.val = ∑ s ∈ range 16, f s :=
  Fin.sum_univ_eq_sum_range f 16

theorem fp_initK (hE : EqKernelLagrange) (ch : List E) :
    Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) initK = rootInit (eqKernel (alphasOf ch)) (betaOf ch) := by
  rw [fp_eq hE]
  unfold initK rootInit betaOf sepState
  simp only [Vector.get_ofFn]
  rw [sum_fin16 (fun s ↦ (eqKernel (alphasOf ch)).getD s 0 * ofK (if s < 3 then 1 else 0))]
  simp (config := {decide := true}) only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ite_true, ite_false, ofK_one, ofK_zero, mul_one, mul_zero, add_zero]
  ring

theorem fp_finK (hE : EqKernelLagrange) (hg : GpowInK) (D : Deployment) (ch : List E) :
    Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) (finK D) =
      rootFin D.shape (eqKernel (alphasOf ch)) (betaOf ch) := by
  rw [fp_eq hE]
  unfold finK rootFin betaOf sepState
  simp only [Vector.get_ofFn]
  rw [sum_fin16 (fun s ↦ (eqKernel (alphasOf ch)).getD s 0 *
    ofK (if s = 1 then toK (UniStatement.gpow (2 ^ D.shape.logBytecode - 1)) else if s < 3 then 1 else 0))]
  simp (config := {decide := true}) only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ite_true, ite_false, ofK_one, ofK_zero, mul_one, mul_zero, add_zero]
  rw [hg]
  ring

end UniSound.Ids
