-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Domain
import UniComplete.Quotients
import Bridge.Ntt
import CompPoly.Univariate.DivisionCorrectness
import CompPoly.Univariate.ToPoly.RingHom

/-!
# The prover's polynomials in Mathlib's `Polynomial E` (milestone 4, the heap's layer)

The honest prover computes with CompPoly's `CPolynomial E` (`Poly`); the proofs read them through `toPoly` (`tp`),
a ring isomorphism onto Mathlib's `E[X]`, under which CompPoly's `divByMonic` is Mathlib's `/ₘ`
(`DivisionCorrectness`). Here:

* **the digits' polynomials**: `tp (wPoly l) = Domain.wP l` (`tp_wPoly`);
* **the novel basis**: `nX k m = Π_{l < m, bit l of k} w_l` (monic, of degree `k` for `k < 2^m`,
  `nX_monic`, `natDegree_nX`), and `tp (ofNovel m d) = Σ_{k < 2^m} d_k X_k` (`tp_ofNovel`), of degree `< 2^m`
  (`natDegree_tp_ofNovel_lt`);
* **interpolation** (`eval_colPolyE`, `eval_colPolyK`): for `m ≤ 28` (the statement's transform
  `PcsQuotient.Domain.coefficients` has `28` basis vectors, so the prover's columns of more than `2^28` rows are
  not its polynomials) the polynomial of a column of `2^m` values takes value `v_i` at `ω_i`, `i < 2^m`
  (`Bridge.Ntt`'s inverse transforms, the points being UniStatement's `pointE`);
* **the tree's compositions**: `X_k(s(x)) = X_{2k}(x)` and `X_k(x + 1) = X_k(x) + X_{k−1}(x)` for odd `k`
  (`wP_comp_s`, `wP_comp_add_one`), so `compSNovel`, `shiftOneNovel` are `T ∘ s` and `T(X + 1)`
  (`tp_ofNovel_compSNovel`, `tp_ofNovel_shiftOneNovel`, `h ≥ 1`);
* `tp_divM`: `divM p q` is `p /ₘ q` for a monic `q`.
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

/-- **A prover polynomial in Mathlib's `E[X]`** (CompPoly's `toPoly`). -/
noncomputable abbrev tp (p : Poly) : E[X] := CompPoly.CPolynomial.toPoly p

theorem tp_add (p q : Poly) : tp (p + q) = tp p + tp q := CompPoly.CPolynomial.toPoly_add p q

theorem tp_mul (p q : Poly) : tp (p * q) = tp p * tp q := CompPoly.CPolynomial.toPoly_mul p q

theorem tp_C (x : E) : tp (pC x) = C x := CompPoly.CPolynomial.C_toPoly x

theorem tp_X : tp pX = X := CompPoly.CPolynomial.X_toPoly

theorem tp_one : tp 1 = 1 := CompPoly.CPolynomial.toPoly_one

theorem tp_zero : tp 0 = 0 := CompPoly.CPolynomial.toPoly_zero

theorem tp_eval (x : E) (p : Poly) : pEval x p = (tp p).eval x := CompPoly.CPolynomial.eval_toPoly x p

theorem tp_coeff (p : Poly) (i : ℕ) : p.coeff i = (tp p).coeff i := CompPoly.CPolynomial.coeff_toPoly p i

/-- **`divM` is Mathlib's division by a monic polynomial.** -/
theorem tp_divM (p q : Poly) (hq : (tp q).Monic) : tp (divM p q) = tp p /ₘ tp q := toPoly_divM p q hq

/-- `modM` is Mathlib's remainder. -/
theorem tp_modM (p q : Poly) (hq : (tp q).Monic) : tp (modM p q) = tp p %ₘ tp q := toPoly_modM p q hq

/-! ### The digits' polynomials -/

theorem wPolys_succ (n : ℕ) : wPolys (n + 1) =
    match (wPolys n).back? with
    | some w => (wPolys n).push (w * w + w)
    | none => (wPolys n).push pX := by
  unfold wPolys
  rw [List.range_succ, List.foldl_append]
  rfl

theorem wPolys_spec : ∀ n : ℕ, (wPolys n).size = n ∧ ∀ l < n, tp ((wPolys n).getD l 0) = wP l
  | 0 => ⟨rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hs, hw⟩ := wPolys_spec n
    rw [wPolys_succ]
    rcases n with _ | m
    · have hb : (wPolys 0).back? = none := rfl
      rw [hb]
      refine ⟨rfl, fun l hl ↦ ?_⟩
      have : l = 0 := by omega
      subst this
      exact tp_X
    · have hb : (wPolys (m + 1)).back? = some ((wPolys (m + 1)).getD m 0) := by
        rw [Array.back?_eq_getElem?, hs, Array.getD_eq_getD_getElem?]
        simp [hs]
      rw [hb]
      refine ⟨by rw [Array.size_push, hs], fun l hl ↦ ?_⟩
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
      by_cases hlm : l = m + 1
      · subst hlm
        simp only [hs, ↓reduceIte, Option.getD_some]
        rw [tp_add, tp_mul, hw m (by omega), wP_succ, pow_two]
      · have hlt : l < m + 1 := by omega
        simp only [hs, hlm, ↓reduceIte]
        rw [← Array.getD_eq_getD_getElem?]
        exact hw l hlt

/-- **`w_l` is `Domain.wP l`.** -/
theorem tp_wPoly (l : ℕ) : tp (wPoly l) = wP l := (wPolys_spec (l + 1)).2 l (by omega)

theorem tp_wPolys_getD {n l : ℕ} (hl : l < n) : tp ((wPolys n).getD l 0) = wP l := (wPolys_spec n).2 l hl


/-! ### The novel basis -/

/-- **The novel basis polynomial** `X_k = Π_{l < m, bit l of k} w_l`. -/
noncomputable def nX (m k : ℕ) : E[X] := ∏ l ∈ (range m).filter (fun l ↦ k.testBit l = true), wP l

theorem nX_eq_prod_ite (m k : ℕ) : nX m k = ∏ l ∈ range m, if k.testBit l = true then wP l else 1 := by
  rw [nX, Finset.prod_filter]

theorem nX_monic (m k : ℕ) : (nX m k).Monic := monic_prod_of_monic _ _ fun l _ ↦ wP_monic l

theorem natDegree_nX (m k : ℕ) : (nX m k).natDegree = k % 2 ^ m := by
  rw [nX, natDegree_prod_of_monic _ _ fun l _ ↦ wP_monic l]
  simp only [wP_natDegree]
  exact Domain.sum_filter_bits k m

theorem natDegree_nX_lt (m k : ℕ) : (nX m k).natDegree < 2 ^ m := by
  rw [natDegree_nX]; exact Nat.mod_lt _ (Nat.two_pow_pos m)

theorem nX_zero_left (k : ℕ) : nX 0 k = 1 := by simp [nX]

theorem nX_succ_low {m k : ℕ} (hk : k < 2 ^ m) : nX (m + 1) k = nX m k := by
  rw [nX_eq_prod_ite, nX_eq_prod_ite, Finset.prod_range_succ, Nat.testBit_eq_false_of_lt hk]
  simp

theorem nX_succ_high {m k : ℕ} (hk : k < 2 ^ m) : nX (m + 1) (2 ^ m + k) = wP m * nX m k := by
  rw [nX_eq_prod_ite, nX_eq_prod_ite, Finset.prod_range_succ, Nat.testBit_two_pow_add_eq,
    Nat.testBit_eq_false_of_lt hk, mul_comm]
  simp only [Bool.not_false, ↓reduceIte]
  congr 1
  refine Finset.prod_congr rfl fun l hl ↦ ?_
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hl)]

/-- The novel coefficients' polynomial `Σ_{k < 2^m} d_k X_k`. -/
noncomputable def novelSum (m : ℕ) (d : ℕ → E) : E[X] := ∑ k ∈ range (2 ^ m), C (d k) * nX m k

theorem getD_extract (d : Array E) (a b k : ℕ) :
    (d.extract a b).getD k 0 = if k < b - a then d.getD (a + k) 0 else 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases h1 : k < b - a
  · rw [ite_pos_of h1]
    by_cases h2 : k < min b d.size - a
    · rw [ite_pos_of h2]
    · rw [ite_neg_of h2]
      have : d.size ≤ a + k := by omega
      rw [Array.getElem?_eq_none this]
  · rw [ite_neg_of h1, ite_neg_of (by omega)]
    rfl

theorem tp_ofNovelWith (ws : Array Poly) :
    ∀ (m : ℕ) (d : Array E), (∀ l < m, tp (ws.getD l 0) = wP l) →
      tp (ofNovelWith ws m d) = novelSum m (d.getD · 0)
  | 0, d, _ => by
    simp [ofNovelWith, novelSum, nX_zero_left]
  | m + 1, d, hws => by
    rw [ofNovelWith, tp_add, tp_mul, hws m (by omega),
      tp_ofNovelWith ws m _ fun l hl ↦ hws l (by omega),
      tp_ofNovelWith ws m _ fun l hl ↦ hws l (by omega), novelSum, novelSum, novelSum,
      show 2 ^ (m + 1) = 2 ^ m + 2 ^ m by rw [pow_succ]; ring, Finset.sum_range_add, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' := Finset.mem_range.mp hk
      rw [getD_extract, ite_pos_of (by omega), zero_add, nX_succ_low hk']
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' := Finset.mem_range.mp hk
      rw [getD_extract, ite_pos_of (by omega), nX_succ_high hk']
      ring

/-- **`ofNovel m d` is `Σ_{k < 2^m} d_k X_k`.** -/
theorem tp_ofNovel (m : ℕ) (d : Array E) : tp (ofNovel m d) = novelSum m (d.getD · 0) :=
  tp_ofNovelWith (wPolys m) m d fun _ hl ↦ tp_wPolys_getD hl

theorem natDegree_novelSum_lt (m : ℕ) (d : ℕ → E) : (novelSum m d).natDegree < 2 ^ m := by
  have : (novelSum m d).natDegree ≤ 2 ^ m - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun k _ ↦ ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    have := natDegree_nX_lt m k
    omega
  have := Nat.two_pow_pos m
  omega

/-- **A polynomial of `2^m` novel coefficients has degree `< 2^m`.** -/
theorem natDegree_tp_ofNovel_lt (m : ℕ) (d : Array E) : (tp (ofNovel m d)).natDegree < 2 ^ m := by
  rw [tp_ofNovel]; exact natDegree_novelSum_lt m _

theorem eval_novelSum (m : ℕ) (d : ℕ → E) (x : E) :
    (novelSum m d).eval x = ∑ k ∈ range (2 ^ m), d k * (nX m k).eval x := by
  simp [novelSum, eval_finsetSum]

/-! ### Interpolation on `V_m`, `m ≤ 28` -/

/-- The statement's `28` basis vectors are a Cantor basis (`Bridge.Ntt.CantorUpTo`), from the verifier's
words (`Domain.beta_zero`, `Domain.beta_succ`). -/
theorem cantorUpTo28 : Bridge.Ntt.CantorUpTo 28 := by
  refine ⟨?_, fun k hk ↦ ?_⟩
  · rw [← Domain.beta_getD_eq_betaAt (by norm_num)]
    exact Domain.beta_zero
  · rw [← Domain.beta_getD_eq_betaAt hk, ← Domain.beta_getD_eq_betaAt (by omega)]
    exact Domain.beta_succ (by omega)

theorem cantorUpTo_of_le {m : ℕ} (hm : m ≤ 28) : Bridge.Ntt.CantorUpTo m :=
  ⟨cantorUpTo28.1, fun k hk ↦ cantorUpTo28.2 k (by omega)⟩

/-- **The statement's point is the verifier's** below `2^28`. -/
theorem statementPoint_eq {i : ℕ} (hi : i < 2 ^ 28) : PcsQuotient.Domain.point i = point i := by
  rw [Bridge.Ntt.point_eq_sum_of_lt (N := 28) le_rfl hi, ← Domain.omega_basisK, Heap.omega]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by norm_num : 28 ≤ 32)) fun x _ hx ↦ by
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num)
      (by simpa using hx)))]
    rfl]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [Domain.basisK_β, Domain.beta_getD_eq_betaAt (Finset.mem_range.mp ht)]

theorem ofK_eq_algebraMap (a : K) : ofK a = algebraMap K E a := rfl

theorem ofK_iterate_S (x : K) (t : ℕ) :
    ofK (PcsQuotient.Domain.S^[t] x) = (fun y : E ↦ y * y + y)^[t] (ofK x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    show ofK (_ * _ + _) = _
    rw [Domain.embed_add, Domain.embed_mul]

theorem eval_nX_pointE {m : ℕ} (j : ℕ) {i : ℕ} (hi : i < 2 ^ 28) :
    (nX m j).eval (pointE i) = ofK (Bridge.Ntt.X m j (PcsQuotient.Domain.point i)) := by
  rw [nX_eq_prod_ite, eval_prod, Bridge.Ntt.X, ofK_eq_algebraMap, map_prod]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  split_ifs
  · rw [Domain.wP_eval, ← ofK_eq_algebraMap, ofK_iterate_S, statementPoint_eq hi]
    rfl
  · rw [eval_one, map_one]

theorem lt28 {m i : ℕ} (hm : m ≤ 28) (hi : i < 2 ^ m) : i < 2 ^ 28 :=
  lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hm)

/-- **An `E`-column's polynomial takes its values on `V_m`** (`m ≤ 28`, `2^m` values): at `ω_i`, `v_i`. -/
theorem eval_ofNovel_novelOfValuesE {m : ℕ} (hm : m ≤ 28) {v : Array E} (hv : v.size = 2 ^ m) {i : ℕ}
    (hi : i < 2 ^ m) : (tp (ofNovel m (novelOfValuesE m v))).eval (pointE i) = v.getD i 0 := by
  have h := Bridge.Ntt.values_getD_E (cantorUpTo_of_le hm) hm 0 (novelOfValuesE m v)
    (by rw [novelOfValuesE, Bridge.Ntt.coefficients_size, hv]) hi
  rw [novelOfValuesE, Bridge.Ntt.values_coefficients_E m 0 v hv] at h
  rw [h, tp_ofNovel, eval_novelSum, novelOfValuesE, zero_add]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [eval_nX_pointE j (lt28 hm hi), mul_comm]

theorem eval_colPolyE {m : ℕ} (hm : m ≤ 28) {v : Array E} (hv : v.size = 2 ^ m) {i : ℕ} (hi : i < 2 ^ m) :
    (tp (colPolyE m v)).eval (pointE i) = v.getD i 0 := eval_ofNovel_novelOfValuesE hm hv hi

theorem getD_map_ofK (c : Array K) (j : ℕ) : (c.map ofK).getD j 0 = ofK (c.getD j 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rcases Nat.lt_or_ge j c.size with hj | hj
  · simp only [Array.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
  · simp only [Array.getElem?_eq_none hj, Option.map_none, Option.getD_none]
    exact Domain.embed_zero.symm

/-- **A `K`-column's polynomial takes its values on `V_m`** (`m ≤ 28`). -/
theorem eval_colPolyK {m : ℕ} (hm : m ≤ 28) {v : Array K} (hv : v.size = 2 ^ m) {i : ℕ} (hi : i < 2 ^ m) :
    (tp (colPolyK m v)).eval (pointE i) = ofK (v.getD i 0) := by
  have h := Bridge.Ntt.values_getD_K (cantorUpTo_of_le hm) hm 0 (PcsQuotient.Domain.coefficients m 0 v)
    (by rw [Bridge.Ntt.coefficients_size, hv]) hi
  rw [Bridge.Ntt.values_coefficients_K m 0 v hv] at h
  rw [h, colPolyK, tp_ofNovel, eval_novelSum, ofK_eq_algebraMap, map_sum, zero_add]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [novelOfValuesK, getD_map_ofK, eval_nX_pointE j (lt28 hm hi), map_mul, mul_comm, ofK_eq_algebraMap,
    ofK_eq_algebraMap]

theorem natDegree_colPolyK_lt (m : ℕ) (v : Array K) : (tp (colPolyK m v)).natDegree < 2 ^ m :=
  natDegree_tp_ofNovel_lt m _

theorem natDegree_colPolyE_lt (m : ℕ) (v : Array E) : (tp (colPolyE m v)).natDegree < 2 ^ m :=
  natDegree_tp_ofNovel_lt m _

/-! ### The tree's compositions: `s(x) = x² + x` and `x + 1` -/

theorem two_eq_zero_EX : (2 : E[X]) = 0 := CharTwo.two_eq_zero

/-- `w_l(s(x)) = w_{l+1}(x)`. -/
theorem wP_comp_s (l : ℕ) : (wP l).comp (X ^ 2 + X) = wP (l + 1) := by
  induction l with
  | zero => rw [wP_zero, X_comp, wP_succ, wP_zero]
  | succ l ih => rw [wP_succ, add_comp, pow_comp, ih, ← wP_succ]

/-- `w_0(x + 1) = w_0(x) + 1`, `w_l(x + 1) = w_l(x)` for `l ≥ 1`. -/
theorem wP_comp_add_one (l : ℕ) : (wP l).comp (X + 1) = wP l + if l = 0 then 1 else 0 := by
  induction l with
  | zero => rw [wP_zero, X_comp, ite_pos_of rfl]
  | succ l ih =>
    rw [wP_succ, add_comp, pow_comp, ih, ite_neg_of (Nat.succ_ne_zero l)]
    split_ifs
    · linear_combination (wP l + 1) * two_eq_zero_EX
    · ring

theorem nX_comp_s (m k : ℕ) : (nX m k).comp (X ^ 2 + X) = nX (m + 1) (2 * k) := by
  rw [nX_eq_prod_ite, nX_eq_prod_ite, Polynomial.prod_comp, Finset.prod_range_succ']
  have h0 : (2 * k).testBit 0 = false := by
    rw [Nat.testBit_zero]; simp
  rw [h0]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  rw [Nat.testBit_add_one, show 2 * k / 2 = k by omega]
  split_ifs
  · exact wP_comp_s t
  · exact one_comp

theorem nX_comp_add_one {m k : ℕ} (hk : k < 2 ^ m) :
    (nX m k).comp (X + 1) = nX m k + if k % 2 = 1 then nX m (k - 1) else 0 := by
  rcases m with _ | m
  · have : k = 0 := by simpa using hk
    subst this
    simp [nX_zero_left]
  · rw [nX_eq_prod_ite, Polynomial.prod_comp, Finset.prod_range_succ']
    have hhigh : ∀ t ∈ range m, (if k.testBit (t + 1) = true then wP (t + 1) else 1).comp (X + 1) =
        if k.testBit (t + 1) = true then wP (t + 1) else 1 := by
      intro t _
      split_ifs
      · rw [wP_comp_add_one, ite_neg_of (Nat.succ_ne_zero t), add_zero]
      · exact one_comp
    rw [Finset.prod_congr rfl hhigh, Nat.testBit_zero]
    by_cases hodd : k % 2 = 1
    · rw [ite_pos_of hodd, Finset.prod_range_succ', nX_eq_prod_ite, Finset.prod_range_succ']
      have hsame : ∀ t ∈ range m, (if (k - 1).testBit (t + 1) = true then wP (t + 1) else 1) =
          if k.testBit (t + 1) = true then wP (t + 1) else 1 := by
        intro t _
        rw [Nat.testBit_add_one, Nat.testBit_add_one, show (k - 1) / 2 = k / 2 by omega]
      rw [Finset.prod_congr rfl hsame, Nat.testBit_zero, Nat.testBit_zero]
      simp only [hodd, decide_true, ↓reduceIte, wP_zero, X_comp, show (k - 1) % 2 = 0 by omega,
        decide_eq_true_eq, zero_ne_one]
      ring
    · rw [ite_neg_of hodd, add_zero, Finset.prod_range_succ', Nat.testBit_zero]
      simp only [hodd, decide_false, Bool.false_eq_true, ↓reduceIte, one_comp]

theorem novelSum_comp (m : ℕ) (d : ℕ → E) (q : E[X]) :
    (novelSum m d).comp q = ∑ k ∈ range (2 ^ m), C (d k) * (nX m k).comp q := by
  rw [novelSum, Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_comp, C_comp]

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n : ℕ, ∑ j ∈ range (2 * n), f j = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1))
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul f n, Finset.sum_range_succ, add_assoc]

/-- **`compSNovel` is `T ∘ s`**: `ofNovel (h + 1) (compSNovel h d) = T(X² + X)`, `T = ofNovel h d`. -/
theorem tp_ofNovel_compSNovel (h : ℕ) (d : Array E) :
    tp (ofNovel (h + 1) (compSNovel h d)) = (tp (ofNovel h d)).comp (X ^ 2 + X) := by
  rw [tp_ofNovel, tp_ofNovel, novelSum_comp, novelSum, pow_succ, mul_comm, sum_range_two_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  have e1 : (compSNovel h d).getD (2 * k) 0 = d.getD k 0 := by
    rw [compSNovel, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [show 2 * k < 2 ^ (h + 1) by rw [pow_succ]; omega]
  have e2 : (compSNovel h d).getD (2 * k + 1) 0 = 0 := by
    rw [compSNovel, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [show 2 * k + 1 < 2 ^ (h + 1) by rw [pow_succ]; omega, ↓reduceDIte, Option.getD_some]
    rw [ite_neg_of (by omega)]
  rw [e1, e2, C_0, zero_mul, add_zero, nX_comp_s]

/-- **`shiftOneNovel` is `T(X + 1)`** (`h ≥ 1`). -/
theorem tp_ofNovel_shiftOneNovel {h : ℕ} (hh : 1 ≤ h) (d : Array E) :
    tp (ofNovel h (shiftOneNovel h d)) = (tp (ofNovel h d)).comp (X + 1) := by
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  rw [tp_ofNovel, tp_ofNovel, novelSum_comp, novelSum, pow_succ, mul_comm, sum_range_two_mul,
    sum_range_two_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  have hlt0 : 2 * k < 2 ^ (g + 1) := by rw [pow_succ]; omega
  have hlt1 : 2 * k + 1 < 2 ^ (g + 1) := by rw [pow_succ]; omega
  have e1 : (shiftOneNovel (g + 1) d).getD (2 * k) 0 = d.getD (2 * k) 0 + d.getD (2 * k + 1) 0 := by
    rw [shiftOneNovel, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hlt0, ↓reduceDIte, Option.getD_some]
    rw [ite_pos_of (by omega)]
  have e2 : (shiftOneNovel (g + 1) d).getD (2 * k + 1) 0 = d.getD (2 * k + 1) 0 := by
    rw [shiftOneNovel, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hlt1, ↓reduceDIte, Option.getD_some]
    rw [ite_neg_of (by omega)]
  rw [e1, e2, nX_comp_add_one hlt0, nX_comp_add_one hlt1, ite_neg_of (by omega), ite_pos_of (by omega),
    show 2 * k + 1 - 1 = 2 * k by omega, C_add]
  ring

end UniComplete.AlgH
