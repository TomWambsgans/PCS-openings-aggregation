-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHRoot
import UniComplete.AlgCChunks

/-!
# The heap read at a block's mixed point is the block's leaves' polynomial (SPEC.md §2, restriction to a coset)

The verifier reads a block's leaves `R_b(t)` as the heap's multilinear extension at the **mixed point**
`m_l = w_l(t) + ω_{pos >> l}` (`l < r`), `ω_{pos >> l}` (`r ≤ l < h`), `pos` the block's first position. Here:

* `mle_subsetSumsE`: the heap's basis-`B` coefficients at any point `z` are `Σ_j d_j Π_{l ∈ j} z_l` (the novel sum
  at `z`; the column agent's `AlgC.mle_subsetSums`);
* **`mle_mixed`** (`restriction`): for a block aligned at `pos` (`2^r ∣ pos`, `pos + 2^r ≤ 2^h`) whose leaves `L` are
  the heap's values at `pos + i`, the heap at the mixed point of `t` is `R(t)`, `R` the polynomial of `L` on
  `V_r`: both sides are polynomials in `t` of degree `< 2^r` (the mixed coordinates `l < r` are `w_l + c`, the rest
  constants) agreeing on `V_r` (at `ω_i` the mixed point is the digits of `ω_{pos + i}`, an aligned offset adding,
  `Heap.add_eq_xor_of_dvd`);
* the heap at the digits of `s(t)`, of `t + 1`, of `1` (`digits_s`, `digits_add_one`, `digits_one`).
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

/-- **The basis-`B` coefficients' extension at a point is the novel sum there.** -/
theorem mle_subsetSumsE (d : Array E) (z : List E) (hd : d.size = 2 ^ z.length) :
    multilinearEval (subsetSumsE z.length d).toList z =
      ∑ j ∈ range (2 ^ z.length), d.getD j 0 * AlgC.novX z.length j (fun l ↦ z.getD l 0) := by
  rw [AlgC.mle_eq_sum _ _ (by rw [AlgC.subsetSumsE_size, hd])]
  rw [Finset.sum_congr rfl (fun x hx ↦ by
    rw [AlgC.subsetSumsE_eq, AlgC.ss_getD d _ hd (Finset.mem_range.mp hx)])]
  exact AlgC.mle_subsetSums (fun l ↦ z.getD l 0) (fun j ↦ d.getD j 0) z.length

/-- Two polynomials of degree `< 2^r` agreeing on `V_r` (`r ≤ 32`) are equal. -/
theorem eq_of_eval_pointE {r : ℕ} (hr : r ≤ 32) {f g : E[X]} (hf : f.natDegree < 2 ^ r) (hg : g.natDegree < 2 ^ r)
    (h : ∀ i < 2 ^ r, f.eval (pointE i) = g.eval (pointE i)) : f = g := by
  have hinj : Set.InjOn pointE (range (2 ^ r) : Set ℕ) := fun i hi j hj hij ↦ by
    have h32 : 2 ^ r ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hr
    exact Domain.pointE_injOn (by simp at hi; omega) (by simp at hj; omega) hij
  have hcard : ((range (2 ^ r)).image pointE).card = 2 ^ r := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hlt : ∀ p : E[X], p.natDegree < 2 ^ r → p.degree < ((range (2 ^ r)).image pointE).card := by
    intro p hp
    rw [hcard]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hp)
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq _ (hlt f hf) (hlt g hg) fun x hx ↦ ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact h i (Finset.mem_range.mp hi)

/-- The mixed point's coordinate polynomials. -/
noncomputable def mixedP (pos r l : ℕ) : E[X] := if l < r then wP l + C (pointE (pos >>> l)) else C (pointE (pos >>> l))

theorem natDegree_mixedP_le (pos r l : ℕ) : (mixedP pos r l).natDegree ≤ if l < r then 2 ^ l else 0 := by
  unfold mixedP
  split_ifs
  · rw [natDegree_add_C, wP_natDegree]
  · rw [natDegree_C]

theorem sum_two_pow_range (r : ℕ) : ∑ l ∈ range r, 2 ^ l + 1 = 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- The mixed point's polynomial `Σ_j d_j Π_{l ∈ j} m_l`. -/
noncomputable def mixedSum (h pos r : ℕ) (d : ℕ → E) : E[X] :=
  ∑ j ∈ range (2 ^ h), C (d j) * ∏ l ∈ range h, (if j.testBit l = true then mixedP pos r l else 1)

theorem natDegree_mixedSum_lt {h pos r : ℕ} (hrh : r ≤ h) (d : ℕ → E) : (mixedSum h pos r d).natDegree < 2 ^ r := by
  have hbound : ∀ j : ℕ, (∏ l ∈ range h, (if j.testBit l = true then mixedP pos r l else 1)).natDegree ≤ 2 ^ r - 1 := by
    intro j
    refine (natDegree_prod_le _ _).trans ?_
    have e1 : ∀ l ∈ range h, (if j.testBit l = true then mixedP pos r l else 1).natDegree ≤
        if l < r then 2 ^ l else 0 := by
      intro l _
      split_ifs with h1 h2
      · exact (natDegree_mixedP_le pos r l).trans (by rw [ite_pos_of h2])
      · exact (natDegree_mixedP_le pos r l).trans (by rw [ite_neg_of h2])
      · rw [natDegree_one]; exact Nat.zero_le _
      · rw [natDegree_one]
    refine (Finset.sum_le_sum e1).trans ?_
    rw [← Finset.sum_filter, show (range h).filter (· < r) = range r by
      ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega]
    have := sum_two_pow_range r
    omega
  have : (mixedSum h pos r d).natDegree ≤ 2 ^ r - 1 := by
    unfold mixedSum
    refine natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
    exact (natDegree_C_mul_le _ _).trans (hbound j)
  have := Nat.one_le_two_pow (n := r)
  omega

theorem mixedP_eval_pointE {pos r l i : ℕ} (hal : 2 ^ r ∣ pos) (hi : i < 2 ^ r) (hpos : pos + 2 ^ r ≤ 2 ^ 32) :
    (mixedP pos r l).eval (pointE i) = (wP l).eval (pointE (pos + i)) := by
  have hi32 : i < 2 ^ 32 := by omega
  rw [Domain.wP_eval_pointE l (by omega), Heap.add_eq_xor_of_dvd hal hi]
  unfold mixedP
  split_ifs with hl
  · rw [Polynomial.eval_add, Polynomial.eval_C, Domain.wP_eval_pointE l hi32, ← Domain.pointE_xor,
      Nat.shiftRight_xor_distrib, Nat.xor_comm]
  · rw [Polynomial.eval_C, Nat.shiftRight_xor_distrib, Nat.shiftRight_eq_div_pow i, Nat.div_eq_of_lt (lt_of_lt_of_le hi
      (Nat.pow_le_pow_right (by norm_num) (by omega))), Nat.xor_zero]

/-- **Restriction to a coset**: the heap at the mixed point of `t` is the block's leaves' polynomial at `t`. -/
theorem mixedSum_eq {h pos r : ℕ} (h28 : h ≤ 28) (hrh : r ≤ h) (hal : 2 ^ r ∣ pos) (hpos : pos + 2 ^ r ≤ 2 ^ h)
    {v : Array E} (hv : v.size = 2 ^ h) {L : Array E} (hL : L.size = 2 ^ r)
    (hval : ∀ i < 2 ^ r, v.getD (pos + i) 0 = L.getD i 0) :
    mixedSum h pos r (fun j ↦ (novelOfValuesE h v).getD j 0) = tp (ofNovel r (novelOfValuesE r L)) := by
  have hh32 : 2 ^ h ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine eq_of_eval_pointE (by omega) (natDegree_mixedSum_lt hrh _) (natDegree_tp_ofNovel_lt r _) fun i hi ↦ ?_
  rw [eval_ofNovel_novelOfValuesE (by omega) hL hi, ← hval i hi,
    ← eval_ofNovel_novelOfValuesE h28 hv (by omega), tp_ofNovel, eval_novelSum]
  unfold mixedSum
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, nX_eq_prod_ite, Polynomial.eval_prod, Polynomial.eval_prod]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun l _ ↦ ?_)
  split_ifs
  · exact mixedP_eval_pointE hal hi (by omega)
  · simp only [Polynomial.eval_one]

/-- The mixed point the verifier builds (`heapRelations`), from the digits `w`. -/
def mixedPoint (w : List E) (h pos r : ℕ) : List E :=
  (List.range h).map fun l ↦ if l < r then w.getD l 0 + pointE (pos >>> l) else pointE (pos >>> l)

theorem mixedPoint_length (w : List E) (h pos r : ℕ) : (mixedPoint w h pos r).length = h := by
  simp [mixedPoint]

theorem mixedPoint_getD (t : E) {n h pos r l : ℕ} (hn : h ≤ n) (hl : l < h) :
    (mixedPoint (digits t n) h pos r).getD l 0 = (mixedP pos r l).eval t := by
  rw [mixedPoint, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
  simp only [Option.map_some, Option.getD_some]
  unfold mixedP
  split_ifs
  · rw [Polynomial.eval_add, Polynomial.eval_C, Domain.wP_eval_digits t (n := n) (by omega)]
  · rw [Polynomial.eval_C]

/-- **The heap at a block's mixed point** (`multilinearEval` of its basis-`B` coefficients) **is `R_b(t)`.** -/
theorem mle_mixed {h pos r : ℕ} (h28 : h ≤ 28) (hrh : r ≤ h) (hal : 2 ^ r ∣ pos) (hpos : pos + 2 ^ r ≤ 2 ^ h)
    {v : Array E} (hv : v.size = 2 ^ h) {L : Array E} (hL : L.size = 2 ^ r)
    (hval : ∀ i < 2 ^ r, v.getD (pos + i) 0 = L.getD i 0) (t : E) {n : ℕ} (hn : h ≤ n) :
    multilinearEval (bOfNovelE h (novelOfValuesE h v)).toList (mixedPoint (digits t n) h pos r) =
      (tp (ofNovel r (novelOfValuesE r L))).eval t := by
  have hd : (novelOfValuesE h v).size = 2 ^ (mixedPoint (digits t n) h pos r).length := by
    rw [mixedPoint_length, novelOfValuesE, Bridge.Ntt.coefficients_size, hv]
  have e := mle_subsetSumsE (novelOfValuesE h v) (mixedPoint (digits t n) h pos r) hd
  rw [mixedPoint_length] at e
  rw [bOfNovelE, e, ← mixedSum_eq h28 hrh hal hpos hv hL hval, mixedSum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, AlgC.novX]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun l hl ↦ ?_)
  split_ifs
  · exact mixedPoint_getD t hn (Finset.mem_range.mp hl)
  · rw [Polynomial.eval_one]

end UniComplete.AlgH
