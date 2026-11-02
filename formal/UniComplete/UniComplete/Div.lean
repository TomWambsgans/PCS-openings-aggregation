-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Basic
import CompPoly.Univariate.DivisionCorrectness
import CompPoly.Univariate.ToPoly.Impl

/-!
# Exact division by a monic polynomial, quadratic

CompPoly's `divByMonic` rebuilds `q · X^k` by a general product at every step of its long division (cubic, too slow
for the interpreter at the heap's `2^8` coefficients). `longDiv` is the schoolbook long division on coefficient
arrays: for `i` from the top down to `deg q`, the remainder's coefficient `c` at `i` becomes the quotient's at
`i − deg q`, and `c · X^(i − deg q) · q` is subtracted. **`divM`, `modM`** are its quotient and remainder as
canonical polynomials; **`toPoly_divM`**, **`toPoly_modM`**: for a monic `q` they are Mathlib's `/ₘ`, `%ₘ`
(`Polynomial.div_modByMonic_unique`), so **`divM_eq`**, **`modM_eq`**: CompPoly's `divByMonic`, `modByMonic`.
-/

namespace UniComplete

open Polynomial LeanVM.Parameters

/-! ### The algorithm -/

/-- One step at index `i`: the remainder's coefficient `c` there is the quotient's at `s = i − d`, and
`c X^s q` is subtracted. -/
def divStepAt (q : Array E) (d : ℕ) (acc : Array E × Array E) (i : ℕ) : Array E × Array E :=
  let c := acc.2.getD i 0
  let s := i - d
  (acc.1.set! s c, Array.ofFn (n := acc.2.size) fun j ↦
    acc.2.getD j.val 0 - (if s ≤ j.val then c * q.getD (j.val - s) 0 else 0))

/-- **Long division** of `p` by `q` (monic, `q.size = d + 1`): quotient and remainder arrays. -/
def longDiv (p q : Array E) : Array E × Array E :=
  let d := q.size - 1
  let n := p.size
  (List.range (n - d)).foldl (fun acc k ↦ divStepAt q d acc (n - 1 - k)) (Array.replicate (n - d) 0, p)

/-- The quotient by a monic polynomial. -/
def divM (p q : Poly) : Poly := CompPoly.CPolynomial.ofArray (longDiv p.val q.val).1

/-- The remainder by a monic polynomial. -/
def modM (p q : Poly) : Poly := CompPoly.CPolynomial.ofArray (longDiv p.val q.val).2

/-- **The novel coefficients** of a polynomial of degree `< 2^m`: the remainder and the quotient by `w_{m−1}`, each
recursively (`X_{2^(m−1) + k} = w_{m−1} X_k`). -/
def toNovelWith (ws : Array Poly) : ℕ → Poly → Array E
  | 0, p => #[p.coeff 0]
  | m + 1, p =>
    let w := ws.getD m 0
    toNovelWith ws m (modM p w) ++ toNovelWith ws m (divM p w)

/-- The `2^m` novel coefficients of `p`. -/
def toNovel (m : ℕ) (p : Poly) : Array E := toNovelWith (wPolys m) m p

/-! ### Arrays as polynomials -/

/-- The polynomial of a coefficient array. -/
noncomputable def polyOf (a : Array E) : Polynomial E :=
  ∑ j ∈ Finset.range a.size, monomial j (a.getD j 0)

theorem getD_eq_zero_of_le {a : Array E} {j : ℕ} (h : a.size ≤ j) : a.getD j 0 = 0 := by
  simp [Array.getD, Nat.not_lt.mpr h]

theorem coeff_polyOf (a : Array E) (i : ℕ) : (polyOf a).coeff i = a.getD i 0 := by
  unfold polyOf
  rw [finset_sum_coeff]
  simp only [coeff_monomial]
  by_cases hi : i < a.size
  · rw [Finset.sum_eq_single i (fun b _ hb ↦ if_neg hb) (fun h ↦ absurd (Finset.mem_range.2 hi) h), if_pos rfl]
  · rw [Finset.sum_eq_zero fun b hb ↦ if_neg (fun h ↦ hi (h ▸ Finset.mem_range.1 hb)),
      getD_eq_zero_of_le (Nat.not_lt.mp hi)]

theorem polyOf_ext {a b : Array E} (h : ∀ i, a.getD i 0 = b.getD i 0) : polyOf a = polyOf b :=
  Polynomial.ext fun i ↦ by rw [coeff_polyOf, coeff_polyOf, h]

/-- A canonical polynomial is the polynomial of its coefficient array. -/
theorem toPoly_eq_polyOf (p : Poly) : p.toPoly = polyOf p.val := by
  ext i
  rw [← CompPoly.CPolynomial.coeff_toPoly, coeff_polyOf]
  rfl

theorem toPoly_ofArray (a : Array E) : (CompPoly.CPolynomial.ofArray a).toPoly = polyOf a := by
  ext i
  rw [← CompPoly.CPolynomial.coeff_toPoly, CompPoly.CPolynomial.coeff_ofArray, coeff_polyOf]

/-! ### One step -/

theorem divStepAt_size (q : Array E) (d : ℕ) (acc : Array E × Array E) (i : ℕ) :
    (divStepAt q d acc i).1.size = acc.1.size ∧ (divStepAt q d acc i).2.size = acc.2.size := by
  simp [divStepAt]

theorem divStepAt_rem_getD (q : Array E) (d : ℕ) (acc : Array E × Array E) (i j : ℕ) :
    (divStepAt q d acc i).2.getD j 0 = if j < acc.2.size then
      acc.2.getD j 0 - (if i - d ≤ j then acc.2.getD i 0 * q.getD (j - (i - d)) 0 else 0) else 0 := by
  unfold divStepAt
  by_cases hj : j < acc.2.size
  · simp [Array.getD, hj]
  · rw [if_neg hj, getD_eq_zero_of_le (by simpa using Nat.not_lt.mp hj)]

theorem divStepAt_quo_getD (q : Array E) (d : ℕ) (acc : Array E × Array E) (i j : ℕ) (hs : i - d < acc.1.size) :
    (divStepAt q d acc i).1.getD j 0 = if j = i - d then acc.2.getD i 0 else acc.1.getD j 0 := by
  unfold divStepAt
  simp only [Array.getD, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  by_cases hj : j < acc.1.size
  · rw [dif_pos hj, dif_pos hj, Array.getElem_setIfInBounds hs]
    by_cases h : i - d = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  · rw [dif_neg hj, dif_neg hj]
    have : j ≠ i - d := fun h ↦ hj (h ▸ hs)
    rw [if_neg this]

/-! ### The invariant -/

/-- After the steps at `n − 1, …, n − k`: `p = q · quo + rem`, the remainder zero at and above `n − k`, the
quotient zero below `n − k − d`; the sizes kept. -/
structure DivInv (p q : Array E) (d k : ℕ) (acc : Array E × Array E) : Prop where
  size1 : acc.1.size = p.size - d
  size2 : acc.2.size = p.size
  eq : polyOf p = polyOf q * polyOf acc.1 + polyOf acc.2
  remZero : ∀ j, p.size - k ≤ j → acc.2.getD j 0 = 0
  quoLow : ∀ j, j + d + k < p.size → acc.1.getD j 0 = 0

theorem polyOf_set_of_zero {a : Array E} {s : ℕ} (hs : s < a.size) (h0 : a.getD s 0 = 0) (c : E) :
    polyOf (a.set! s c) = polyOf a + monomial s c := by
  ext j
  rw [coeff_add, coeff_polyOf, coeff_polyOf, coeff_monomial]
  simp only [Array.getD, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  by_cases hj : j < a.size
  · rw [dif_pos hj, dif_pos hj, Array.getElem_setIfInBounds hs]
    by_cases h : s = j
    · subst h
      have : a[s] = 0 := by simpa [Array.getD, hs] using h0
      simp [this]
    · rw [if_neg h, if_neg h, add_zero]
  · rw [dif_neg hj, dif_neg hj, if_neg (fun h ↦ hj (h ▸ hs)), add_zero]

theorem polyOf_step_rem (q : Array E) (d : ℕ) (acc : Array E × Array E) (i : ℕ) (hq : q.size = d + 1)
    (hi : i < acc.2.size) (hid : d ≤ i) :
    polyOf (divStepAt q d acc i).2 = polyOf acc.2 - monomial (i - d) (acc.2.getD i 0) * polyOf q := by
  ext j
  rw [coeff_sub, coeff_polyOf, coeff_polyOf, divStepAt_rem_getD, coeff_monomial_mul]
  by_cases hj : j < acc.2.size
  · rw [if_pos hj, coeff_polyOf]
    by_cases hs : i - d ≤ j
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs, sub_zero, sub_zero]
  · rw [if_neg hj, getD_eq_zero_of_le (Nat.not_lt.mp hj)]
    by_cases hs : i - d ≤ j
    · rw [if_pos hs, coeff_polyOf, getD_eq_zero_of_le (by omega), mul_zero, sub_zero]
    · rw [if_neg hs, sub_zero]

theorem divInv_step (p q : Array E) (d k : ℕ) (hq : q.size = d + 1) (hq1 : q.getD d 0 = 1)
    (hk : k < p.size - d) (acc : Array E × Array E)
    (h : DivInv p q d k acc) : DivInv p q d (k + 1) (divStepAt q d acc (p.size - 1 - k)) := by
  have hi : p.size - 1 - k < acc.2.size := by rw [h.size2]; omega
  have hid : d ≤ p.size - 1 - k := by omega
  have hs : p.size - 1 - k - d < acc.1.size := by rw [h.size1]; omega
  refine ⟨by rw [(divStepAt_size _ _ _ _).1, h.size1], by rw [(divStepAt_size _ _ _ _).2, h.size2], ?_, ?_, ?_⟩
  · rw [polyOf_step_rem q d acc _ hq hi hid]
    have hq0 : acc.1.getD (p.size - 1 - k - d) 0 = 0 := h.quoLow _ (by omega)
    have hset : (divStepAt q d acc (p.size - 1 - k)).1 =
        acc.1.set! (p.size - 1 - k - d) (acc.2.getD (p.size - 1 - k) 0) := rfl
    rw [hset, polyOf_set_of_zero hs hq0, h.eq]
    ring
  · intro j hj
    rw [divStepAt_rem_getD]
    by_cases hjs : j < acc.2.size
    · rw [if_pos hjs]
      by_cases hjt : j = p.size - 1 - k
      · subst hjt
        rw [if_pos (by omega), show p.size - 1 - k - (p.size - 1 - k - d) = d by omega, hq1, mul_one, sub_self]
      · have hj' : p.size - k ≤ j := by omega
        rw [h.remZero j hj', if_pos (by omega), getD_eq_zero_of_le (a := q) (by rw [hq]; omega), mul_zero,
          sub_zero]
    · rw [if_neg hjs]
  · intro j hj
    rw [divStepAt_quo_getD q d acc _ j hs, if_neg (by omega)]
    exact h.quoLow j (by omega)

theorem divInv_foldl (p q : Array E) (d : ℕ) (hq : q.size = d + 1) (hq1 : q.getD d 0 = 1) :
    ∀ k, k ≤ p.size - d → DivInv p q d k ((List.range k).foldl (fun acc k ↦ divStepAt q d acc (p.size - 1 - k))
      (Array.replicate (p.size - d) 0, p))
  | 0, _ => by
    refine ⟨by simp, rfl, ?_, fun j hj ↦ getD_eq_zero_of_le (by omega), fun j _ ↦ ?_⟩
    · have : polyOf (Array.replicate (p.size - d) (0 : E)) = 0 := by
        ext i
        rw [coeff_polyOf, coeff_zero]
        simp [Array.getD]
      simp [this]
    · simp [Array.getD]
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact divInv_step p q d k hq hq1 (by omega) _ (divInv_foldl p q d hq hq1 k (by omega))

/-- **Long division is division with remainder**: `p = q · quo + rem` with the remainder below `deg q`. -/
theorem longDiv_spec (p q : Array E) (d : ℕ) (hq : q.size = d + 1) (hq1 : q.getD d 0 = 1) :
    polyOf p = polyOf q * polyOf (longDiv p q).1 + polyOf (longDiv p q).2 ∧
      ∀ j, d ≤ j → (longDiv p q).2.getD j 0 = 0 := by
  have hd : q.size - 1 = d := by omega
  have h := divInv_foldl p q d hq hq1 (p.size - d) le_rfl
  unfold longDiv
  rw [hd]
  refine ⟨h.eq, fun j hj ↦ ?_⟩
  by_cases hjp : j < p.size
  · exact h.remZero j (by omega)
  · exact getD_eq_zero_of_le (by rw [h.size2]; omega)

/-! ### Against Mathlib's and CompPoly's division -/

theorem natDegree_polyOf_lt {a : Array E} {d : ℕ} (h : ∀ j, d ≤ j → a.getD j 0 = 0) (hd : 0 < d) :
    (polyOf a).natDegree < d := by
  by_cases h0 : polyOf a = 0
  · rw [h0, natDegree_zero]; exact hd
  · refine lt_of_not_ge fun hge ↦ ?_
    have := h _ hge
    rw [← coeff_polyOf] at this
    exact h0 (leadingCoeff_eq_zero.1 this)

theorem degree_polyOf_lt {a : Array E} {d : ℕ} (h : ∀ j, d ≤ j → a.getD j 0 = 0) :
    (polyOf a).degree < d := by
  by_cases h0 : polyOf a = 0
  · rw [h0, degree_zero]; exact WithBot.bot_lt_coe d
  · rw [degree_eq_natDegree h0]
    refine WithBot.coe_lt_coe.2 (lt_of_not_ge fun hge ↦ h0 (leadingCoeff_eq_zero.1 ?_))
    rw [leadingCoeff, coeff_polyOf]
    exact h _ hge

/-- A monic canonical polynomial's array ends in `1`, at its degree. -/
theorem monic_array {q : Poly} (hq : q.toPoly.Monic) :
    q.val.size = q.toPoly.natDegree + 1 ∧ q.val.getD q.toPoly.natDegree 0 = 1 := by
  have hc : q.val.getD q.toPoly.natDegree 0 = 1 := by
    have := hq.leadingCoeff
    rw [leadingCoeff, toPoly_eq_polyOf, coeff_polyOf] at this
    rwa [toPoly_eq_polyOf]
  refine ⟨?_, hc⟩
  have hlt : q.toPoly.natDegree < q.val.size := by
    by_contra hge
    rw [getD_eq_zero_of_le (Nat.not_lt.mp hge)] at hc
    exact zero_ne_one hc
  have hle : q.val.size ≤ q.toPoly.natDegree + 1 := by
    by_contra hgt
    have hlast : q.val.getD (q.val.size - 1) 0 ≠ 0 := by
      have hc' := q.property
      have hne : q.val.size ≠ 0 := by omega
      have := (CompPoly.CPolynomial.Raw.Trim.isCanonical_iff_size_eq_zero_or_getLastD_ne_zero.mp hc').resolve_left hne
      simpa [Array.getLastD, Array.getD, Array.back?, Array.back, show q.val.size - 1 < q.val.size by omega] using this
    have hcoeff : q.toPoly.coeff (q.val.size - 1) ≠ 0 := by rwa [toPoly_eq_polyOf, coeff_polyOf]
    have := le_natDegree_of_ne_zero hcoeff
    omega
  omega

theorem toPoly_divM_modM (p q : Poly) (hq : q.toPoly.Monic) :
    (divM p q).toPoly = p.toPoly /ₘ q.toPoly ∧ (modM p q).toPoly = p.toPoly %ₘ q.toPoly := by
  obtain ⟨hsize, hone⟩ := monic_array hq
  obtain ⟨heq, hzero⟩ := longDiv_spec p.val q.val q.toPoly.natDegree hsize hone
  have hu := Polynomial.div_modByMonic_unique (polyOf (longDiv p.val q.val).1) (polyOf (longDiv p.val q.val).2) hq
    ⟨by rw [← toPoly_eq_polyOf, ← toPoly_eq_polyOf] at heq; rw [heq]; ring,
      by rw [degree_eq_natDegree hq.ne_zero]; exact degree_polyOf_lt hzero⟩
  unfold divM modM
  rw [toPoly_ofArray, toPoly_ofArray]
  exact ⟨hu.1.symm, hu.2.symm⟩

/-- **`divM` is Mathlib's `/ₘ`** for a monic divisor. -/
theorem toPoly_divM (p q : Poly) (hq : q.toPoly.Monic) : (divM p q).toPoly = p.toPoly /ₘ q.toPoly :=
  (toPoly_divM_modM p q hq).1

/-- **`modM` is Mathlib's `%ₘ`** for a monic divisor. -/
theorem toPoly_modM (p q : Poly) (hq : q.toPoly.Monic) : (modM p q).toPoly = p.toPoly %ₘ q.toPoly :=
  (toPoly_divM_modM p q hq).2

/-- **`divM` is CompPoly's `divByMonic`** for a monic divisor. -/
theorem divM_eq (p q : Poly) (hq : q.monic) : divM p q = CompPoly.CPolynomial.divByMonic p q := by
  have hq' := (CompPoly.CPolynomial.monic_toPoly_iff q).mp hq
  refine CompPoly.CPolynomial.toPoly_inj.mp ?_
  rw [toPoly_divM p q hq', CompPoly.CPolynomial.divByMonic_toPoly_eq_divByMonic p q hq]

/-- **`modM` is CompPoly's `modByMonic`** for a monic divisor. -/
theorem modM_eq (p q : Poly) (hq : q.monic) : modM p q = CompPoly.CPolynomial.modByMonic p q := by
  have hq' := (CompPoly.CPolynomial.monic_toPoly_iff q).mp hq
  refine CompPoly.CPolynomial.toPoly_inj.mp ?_
  rw [toPoly_modM p q hq', CompPoly.CPolynomial.modByMonic_toPoly_eq_modByMonic p q hq]

end UniComplete

/-- info: 'UniComplete.toPoly_divM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.toPoly_divM

/-- info: 'UniComplete.divM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.divM_eq

/-- info: 'UniComplete.modM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.modM_eq
