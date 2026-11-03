-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHStack

/-!
# The prover's values at `t` (milestone 4)

The verifier reads the heap at `w[..h]`, at `(w.drop 1)[..h]`, at `w[..h]` with `1` added to its first digit, at
`(1, 0, …, 0)`: these are the digits of `t`, of `s(t) = t² + t`, of `t + 1`, of `1` (`digits_drop_one`,
`take_modify_digits`, `atOne_eq`), so the heap's basis-`B` coefficients there are `T(t)`, `T(s(t))`, `T(t + 1)`, `T(1)`
(`evalB_heap`). A table's, the memory's, the bytecode's columns at `w` are their polynomials at `t`
(`atColumn_eq`, `atMem_eq`, …, the column agent's `AlgC.evalB_bCoefficients`), so the fingerprints the verifier
computes from them are the prover's polynomials at `t`.
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

/-! ### Digits -/

theorem digits_drop_one (t : E) (n : ℕ) : (digits t (n + 1)).drop 1 = digits (t * t + t) n := by
  rw [Domain.digits_eq, Domain.digits_eq, List.range_succ_eq_map, List.map_cons, List.drop_one, List.tail_cons,
    List.map_map]
  refine List.map_congr_left fun l _ ↦ ?_
  show (fun x : E ↦ x * x + x)^[l + 1] t = _
  rw [Function.iterate_succ_apply]

theorem digits_getD' (t : E) {l n : ℕ} (hl : l < n) : (digits t n).getD l 0 = (wP l).eval t :=
  (Domain.wP_eval_digits t hl).symm

theorem wP_eval_add_one (l : ℕ) (t : E) : (wP l).eval (t + 1) = (wP l).eval t + if l = 0 then 1 else 0 := by
  have := congrArg (Polynomial.eval t) (wP_comp_add_one l)
  rw [eval_comp] at this
  simp only [Polynomial.eval_add, eval_X, Polynomial.eval_one] at this
  rw [this]
  split_ifs <;> simp

theorem take_modify_digits (t : E) {h n : ℕ} (hn : h ≤ n) :
    ((digits t n).take h).modify 0 (· + 1) = (digits (t + 1) n).take h := by
  refine List.ext_getElem (by simp [Domain.length_digits]) fun l h1 h2 ↦ ?_
  have hl : l < h := (by simpa [Domain.length_digits] using h2 : l < h ∧ l < n).1
  rw [List.getElem_modify, List.getElem_take, List.getElem_take]
  have e1 : (digits t n)[l]'(by rw [Domain.length_digits]; omega) = (wP l).eval t := by
    rw [← digits_getD' t (by omega : l < n), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
  have e2 : (digits (t + 1) n)[l]'(by rw [Domain.length_digits]; omega) = (wP l).eval (t + 1) := by
    rw [← digits_getD' (t + 1) (by omega : l < n), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
  rw [e1, e2, wP_eval_add_one]
  by_cases h0 : l = 0
  · subst h0; simp
  · rw [ite_neg_of (Ne.symm h0), ite_neg_of h0, add_zero]

theorem atOne_eq {h n : ℕ} (hn : h ≤ n) :
    (List.range h).map (fun l ↦ if l = 0 then (1 : E) else 0) = (digits 1 n).take h := by
  refine List.ext_getElem (by simp [Domain.length_digits]; omega) fun l h1 h2 ↦ ?_
  have hl : l < h := by simpa using h1
  rw [List.getElem_map, List.getElem_range, List.getElem_take]
  have e : (digits (1 : E) n)[l]'(by rw [Domain.length_digits]; omega) = (wP l).eval 1 := by
    rw [← digits_getD' 1 (by omega : l < n), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
  rw [e]
  have h1' := wP_eval_add_one l 0
  rw [zero_add, show (wP l).eval 0 = 0 from by
    rw [← Domain.pointE_zero, Domain.wP_eval_pointE l (by norm_num)]; simp [Domain.pointE_zero]] at h1'
  rw [h1', zero_add]

/-- **The heap's basis-`B` coefficients at the digits of `x`** are `T(x)`. -/
theorem evalB_heap {h n : ℕ} (hn : h ≤ n) {v : Array E} (hv : v.size = 2 ^ h) (x : E) :
    evalB (bOfNovelE h (novelOfValuesE h v)) h (digits x n) = (tp (ofNovel h (novelOfValuesE h v))).eval x := by
  rw [bOfNovelE, AlgC.evalB_subsetSumsE h n _ (by rw [novelOfValuesE, Bridge.Ntt.coefficients_size, hv]) hn, tp_eval]

theorem mle_take {b : Array E} {r : ℕ} (w : List E) : multilinearEval b.toList (w.take r) = evalB b r w := rfl

/-! ### Columns at `t` -/

theorem ev_eq_pEval (x : E) (p : Poly) : ev x p = pEval x p := by rw [ev_apply, tp_eval]

theorem evalB_empty : ∀ (pt : List E), multilinearEval ([] : List E) pt = 0
  | [] => rfl
  | r :: pt => by
    unfold multilinearEval at *
    have : foldOnce (#[] : Array E) r = #[] := by simp [foldOnce]
    rw [List.foldl_cons]
    rw [show ([] : List E).toArray = #[] from rfl, this]
    exact evalB_empty pt

/-- **A table's column at `w` is its polynomial at `t`** (`0` past the table's columns). -/
theorem atColumn_eq {tr : Trace} (hon : TraceHonest tr) {t : ℕ} (ht : t < 6) (x : E) {n : ℕ}
    (hn : tr.height t ≤ n) (c : ℕ) :
    AlgC.atColumn tr (digits x n) (tables.getD t default) c = ev x ((tablePolys tr t).getD c 0) := by
  have hop : (tables.getD t default).opcode = t := by
    have : ∀ t < 6, (tables.getD t default).opcode = t := by decide
    exact this t ht
  unfold AlgC.atColumn tablePolys
  rw [hop]
  by_cases hc : c < (tables.getD t default).width
  · rw [getD_ofFn_lt _ _ hc, ev_eq_pEval]
    exact AlgC.evalB_bCoefficients _ n _ ((hon.tablesSize.2 t ht).2 c hc) hn x
  · rw [getD_ofFn_ge _ _ (by omega), map_zero, Trace.column, List.getD_eq_default (tr.tables.getD t []) #[] (by
      rw [(hon.tablesSize.2 t ht).1]; omega)]
    have : ∀ r : ℕ, (bCoefficients r #[]).map ofK = #[] := fun r ↦ by
      rw [← Array.size_eq_zero_iff, Array.size_map, AlgC.bCoefficients_size]; rfl
    rw [this]
    exact evalB_empty _

end UniComplete.AlgH
