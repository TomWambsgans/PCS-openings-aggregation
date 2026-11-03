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
`toNovel` (a polynomial's novel coefficients, by `w_{m−1}`'s remainder and quotient recursively) uses them.
-/

namespace UniComplete

open Polynomial LeanVM.Parameters

/-! ### The algorithm -/

/-- One step at index `i`: the remainder's coefficient `c` there is the quotient's at `s = i − d`, and
`c X^s q` is subtracted. -/
def divStepAt (q : Array E) (d : ℕ) (acc : Array E × Array E) (i : ℕ) : Array E × Array E :=
  let c := acc.2.getD i 0
  let s := i - d
  (Array.ofFn (n := acc.1.size) fun j ↦ if j.val = s then c else acc.1.getD j.val 0,
    Array.ofFn (n := acc.2.size) fun j ↦
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
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h, Option.getD_none]

theorem getD_ofFnE {n : ℕ} (f : Fin n → E) (j : ℕ) :
    (Array.ofFn f).getD j 0 = if h : j < n then f ⟨j, h⟩ else 0 := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases h : j < n <;> simp [h]

theorem coeff_polyOf (a : Array E) (i : ℕ) : (polyOf a).coeff i = a.getD i 0 := by
  unfold polyOf
  rw [Polynomial.finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range a.size) i]
  by_cases hi : i < a.size
  · simp [hi]
  · simp only [Finset.mem_range, hi, ↓reduceIte]
    exact (getD_eq_zero_of_le (Nat.not_lt.mp hi)).symm

/-- A canonical polynomial is the polynomial of its coefficient array. -/
theorem toPoly_eq_polyOf (p : Poly) : p.toPoly = polyOf p.val := by
  refine Polynomial.ext fun i ↦ ?_
  rw [← CompPoly.CPolynomial.coeff_toPoly, coeff_polyOf]

theorem toPoly_ofArray (a : Array E) : (CompPoly.CPolynomial.ofArray a).toPoly = polyOf a := by
  refine Polynomial.ext fun i ↦ ?_
  rw [← CompPoly.CPolynomial.coeff_toPoly, CompPoly.CPolynomial.coeff_ofArray, coeff_polyOf]

/-! ### One step -/

theorem divStepAt_size (q : Array E) (d : ℕ) (acc : Array E × Array E) (i : ℕ) :
    (divStepAt q d acc i).1.size = acc.1.size ∧ (divStepAt q d acc i).2.size = acc.2.size := by
  simp [divStepAt]

theorem divStepAt_rem_getD (q : Array E) (d : ℕ) (acc : Array E × Array E) (i j : ℕ) :
    (divStepAt q d acc i).2.getD j 0 = if j < acc.2.size then
      acc.2.getD j 0 - (if i - d ≤ j then acc.2.getD i 0 * q.getD (j - (i - d)) 0 else 0) else 0 := by
  unfold divStepAt
  rw [getD_ofFnE]
  by_cases hj : j < acc.2.size <;> simp [hj]

theorem divStepAt_quo_getD (q : Array E) (d : ℕ) (acc : Array E × Array E) (i j : ℕ) (hs : i - d < acc.1.size) :
    (divStepAt q d acc i).1.getD j 0 = if j = i - d then acc.2.getD i 0 else acc.1.getD j 0 := by
  unfold divStepAt
  rw [getD_ofFnE]
  by_cases hj : j < acc.1.size
  · simp [hj]
  · have : j ≠ i - d := fun h ↦ hj (h ▸ hs)
    simp [hj, this, getD_eq_zero_of_le (Nat.not_lt.mp hj)]

/-! ### The invariant -/

/-- After the steps at `n − 1, …, n − k`: `p = q · quo + rem`, the remainder zero at and above `n − k`, the
quotient zero below `n − k − d`; the sizes kept. -/
structure DivInv (p q : Array E) (d k : ℕ) (acc : Array E × Array E) : Prop where
  size1 : acc.1.size = p.size - d
  size2 : acc.2.size = p.size
  eq : polyOf p = polyOf q * polyOf acc.1 + polyOf acc.2
  remZero : ∀ j, p.size - k ≤ j → acc.2.getD j 0 = 0
  quoLow : ∀ j, j + d + k < p.size → acc.1.getD j 0 = 0

theorem polyOf_step_quo (q : Array E) (d : ℕ) (acc : Array E × Array E) (i : ℕ) (hs : i - d < acc.1.size)
    (h0 : acc.1.getD (i - d) 0 = 0) :
    polyOf (divStepAt q d acc i).1 = polyOf acc.1 + monomial (i - d) (acc.2.getD i 0) := by
  refine Polynomial.ext fun j ↦ ?_
  rw [coeff_add, coeff_polyOf, coeff_polyOf, coeff_monomial, divStepAt_quo_getD q d acc i j hs]
  by_cases h : j = i - d
  · subst h
    simp [h0]
  · simp [h, Ne.symm h]

theorem polyOf_step_rem (q : Array E) (d : ℕ) (acc : Array E × Array E) (i : ℕ) (hq : q.size = d + 1)
    (hi : i < acc.2.size) (hid : d ≤ i) :
    polyOf (divStepAt q d acc i).2 = polyOf acc.2 - monomial (i - d) (acc.2.getD i 0) * polyOf q := by
  refine Polynomial.ext fun j ↦ ?_
  rw [coeff_sub, coeff_polyOf, coeff_polyOf, divStepAt_rem_getD, ← C_mul_X_pow_eq_monomial, mul_assoc,
    coeff_C_mul, coeff_X_pow_mul']
  by_cases hj : j < acc.2.size
  · by_cases hs : i - d ≤ j
    · simp [hj, hs, coeff_polyOf]
    · simp [hj, hs]
  · have hj' : acc.2.size ≤ j := Nat.not_lt.mp hj
    by_cases hs : i - d ≤ j
    · have hq0 : q.getD (j - (i - d)) 0 = 0 := getD_eq_zero_of_le (by omega)
      simp [hj, hs, coeff_polyOf, getD_eq_zero_of_le hj', hq0]
    · simp [hj, hs, getD_eq_zero_of_le hj']

theorem divInv_step (p q : Array E) (d k : ℕ) (hq : q.size = d + 1) (hq1 : q.getD d 0 = 1)
    (hk : k < p.size - d) (acc : Array E × Array E)
    (h : DivInv p q d k acc) : DivInv p q d (k + 1) (divStepAt q d acc (p.size - 1 - k)) := by
  have hi : p.size - 1 - k < acc.2.size := by rw [h.size2]; omega
  have hs : p.size - 1 - k - d < acc.1.size := by rw [h.size1]; omega
  have hq0 : acc.1.getD (p.size - 1 - k - d) 0 = 0 := h.quoLow _ (by omega)
  refine ⟨by rw [(divStepAt_size _ _ _ _).1, h.size1], by rw [(divStepAt_size _ _ _ _).2, h.size2], ?_, ?_, ?_⟩
  · rw [polyOf_step_rem q d acc _ hq hi (by omega), polyOf_step_quo q d acc _ hs hq0, h.eq]
    ring
  · intro j hj
    rw [divStepAt_rem_getD]
    by_cases hjs : j < acc.2.size
    · by_cases hjt : j = p.size - 1 - k
      · subst hjt
        have hsd : p.size - 1 - k - (p.size - 1 - k - d) = d := by omega
        simp [hjs, show p.size - 1 - k - d ≤ p.size - 1 - k from Nat.sub_le _ _, hsd, hq1]
      · have hj' : p.size - k ≤ j := by omega
        have hqz : q.getD (j - (p.size - 1 - k - d)) 0 = 0 := getD_eq_zero_of_le (by rw [hq]; omega)
        simp [hjs, h.remZero j hj', hqz]
    · simp [hjs]
  · intro j hj
    rw [divStepAt_quo_getD q d acc _ j hs]
    have : j ≠ p.size - 1 - k - d := by omega
    simp only [this, ↓reduceIte]
    exact h.quoLow j (by omega)

theorem divInv_foldl (p q : Array E) (d : ℕ) (hq : q.size = d + 1) (hq1 : q.getD d 0 = 1) :
    ∀ k, k ≤ p.size - d → DivInv p q d k ((List.range k).foldl (fun acc k ↦ divStepAt q d acc (p.size - 1 - k))
      (Array.replicate (p.size - d) 0, p))
  | 0, _ => by
    have hz : polyOf (Array.replicate (p.size - d) (0 : E)) = 0 := by
      refine Polynomial.ext fun i ↦ ?_
      rw [coeff_polyOf, coeff_zero, Array.getD_eq_getD_getElem?]
      by_cases hi : i < p.size - d <;> simp [hi]
    refine ⟨by simp, rfl, by simp [hz], fun j hj ↦ getD_eq_zero_of_le (by simp; omega), fun j _ ↦ ?_⟩
    rw [Array.getD_eq_getD_getElem?]
    by_cases hi : j < p.size - d <;> simp [hi]
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
    rwa [leadingCoeff, toPoly_eq_polyOf, coeff_polyOf, ← toPoly_eq_polyOf] at this
  refine ⟨?_, hc⟩
  have hne : q.val.size ≠ 0 := by
    intro h0
    rw [getD_eq_zero_of_le (by omega)] at hc
    exact zero_ne_one hc
  rw [CompPoly.CPolynomial.toPoly_natDegree]
  unfold CompPoly.CPolynomial.natDegree
  split <;> omega

theorem toPoly_divM_modM (p q : Poly) (hq : q.toPoly.Monic) :
    (divM p q).toPoly = p.toPoly /ₘ q.toPoly ∧ (modM p q).toPoly = p.toPoly %ₘ q.toPoly := by
  obtain ⟨hsize, hone⟩ := monic_array hq
  obtain ⟨heq, hzero⟩ := longDiv_spec p.val q.val q.toPoly.natDegree hsize hone
  rw [← toPoly_eq_polyOf, ← toPoly_eq_polyOf] at heq
  have hu := Polynomial.div_modByMonic_unique (f := p.toPoly) (g := q.toPoly) (polyOf (longDiv p.val q.val).1)
    (polyOf (longDiv p.val q.val).2) hq
    ⟨by rw [heq]; ring, by rw [degree_eq_natDegree hq.ne_zero]; exact degree_polyOf_lt hzero⟩
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
