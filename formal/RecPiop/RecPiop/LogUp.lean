-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The counting form follows leanerVM
-- 6175f1a0's `LeanVM.Protocol.card_sideProduct_collision_le` (one Schwartz–Zippel bound on a cleared
-- polynomial, Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`).
import Mathlib
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Set-based logUp in characteristic two

A family of (value, tag) pairs `e x`, `x ∈ s`, and its **log-derivative sum** at `(α, β)`:
`Σ_{x ∈ s} 1/(α + v_x + β τ_x)` (`logSum`). In characteristic two a pair occurring twice cancels,
so the sum sees each pair's multiplicity **mod 2** only:

* `logSum_eq_zero_of_even`: if every pair occurs an even number of times (`EvenAll`), the sum
  vanishes, at every `(α, β)`;
* `sum_eq_sum_oddPairs`: in general it is the sum over the pairs of odd multiplicity (`oddPairs`),
  each once;
* **the cleared polynomial** `cleared (oddPairs s e) = Σ_q Π_{q' ≠ q} (X₀ + v_{q'} + X₁ τ_{q'})`,
  of total degree below `|s|` (`totalDegree_cleared_le`), is the sum's numerator
  (`eval_cleared`): the sum, as a rational function of `(α, β)`, is zero exactly when it is
  (`cleared_eq_zero_iff`: exactly when every pair is even);
* **`card_logSum_eq_zero_le`** (Schwartz–Zippel on the cleared polynomial): if some pair is odd, at
  most `(|s| − 1)·|F|` of the `|F|²` points `(α, β)` have every denominator nonzero and the sum
  zero; `prob_logSum_eq_zero_le`: at most `(|s| − 1)/|F|` at a uniform `(α, β)`.

**Every tag twice** (`eq_of_even_of_pair`): if every pair is even and exactly two members `x ≠ y`
of `s` carry the tag of `x`, then `e x = e y`, the two values equal. This is the step from "mod 2"
to "equal" for π2's copy argument, where each tag is one pull and one push, or one push and one
public term.
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset

variable {F : Type} [Field F] [CharP F 2]
variable {ι : Type} [DecidableEq ι]

/-- **The denominator of a (value, tag) pair** at `(α, β)`: `α + v + β τ`. -/
def den (α β : F) (e : F × F) : F := α + e.1 + β * e.2

/-- **The log-derivative sum** of a family of pairs. -/
def logSum (s : Finset ι) (e : ι → F × F) (α β : F) : F := ∑ x ∈ s, (den α β (e x))⁻¹

/-- The multiplicity of a pair in the family. -/
def mult [DecidableEq F] (s : Finset ι) (e : ι → F × F) (q : F × F) : ℕ :=
  (s.filter fun x => e x = q).card

/-- **Every pair occurs an even number of times**: the family is zero mod 2. -/
def EvenAll [DecidableEq F] (s : Finset ι) (e : ι → F × F) : Prop := ∀ q, Even (mult s e q)

/-- The pairs of odd multiplicity. -/
def oddPairs [DecidableEq F] (s : Finset ι) (e : ι → F × F) : Finset (F × F) :=
  (s.image e).filter fun q => Odd (mult s e q)

section Sum

variable [DecidableEq F]

/-- In characteristic two, a natural number times an element is that element or zero, by the
number's parity. -/
theorem nsmul_char_two (n : ℕ) (a : F) : n • a = if Odd n then a else 0 := by
  rw [nsmul_eq_mul]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two, CharTwo.two_eq_zero, zero_mul, zero_add,
      Nat.cast_one, one_mul]
  · obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp h
    rw [← two_mul, Nat.cast_mul, Nat.cast_two, CharTwo.two_eq_zero, zero_mul, zero_mul]

/-- **The sum over a family is the sum over its odd pairs**, in characteristic two. -/
theorem sum_eq_sum_oddPairs (s : Finset ι) (e : ι → F × F) (g : F × F → F) :
    ∑ x ∈ s, g (e x) = ∑ q ∈ oddPairs s e, g q := by
  rw [Finset.sum_comp, oddPairs, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [nsmul_char_two]
  rfl

/-- **A family zero mod 2 has a vanishing sum**, at every `(α, β)`. -/
theorem logSum_eq_zero_of_even (s : Finset ι) (e : ι → F × F) (h : EvenAll s e) (α β : F) :
    logSum s e α β = 0 := by
  unfold logSum
  rw [sum_eq_sum_oddPairs s e fun q => (den α β q)⁻¹]
  have : oddPairs s e = ∅ := by
    unfold oddPairs
    exact Finset.filter_false_of_mem fun q _ hq => (Nat.not_odd_iff_even.mpr (h q)) hq
  rw [this, Finset.sum_empty]

theorem oddPairs_nonempty (s : Finset ι) (e : ι → F × F) (h : ¬ EvenAll s e) :
    (oddPairs s e).Nonempty := by
  unfold EvenAll at h
  push Not at h
  obtain ⟨q, hq⟩ := h
  have hq' : Odd (mult s e q) := Nat.not_even_iff_odd.mp hq
  refine ⟨q, Finset.mem_filter.mpr ⟨?_, hq'⟩⟩
  obtain ⟨x, hx⟩ : (s.filter fun x => e x = q).Nonempty := by
    rw [← Finset.card_pos]
    exact hq'.pos
  rw [Finset.mem_filter] at hx
  exact Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩

theorem card_oddPairs_le (s : Finset ι) (e : ι → F × F) : (oddPairs s e).card ≤ s.card :=
  (Finset.card_filter_le _ _).trans Finset.card_image_le

end Sum

/-! ## The cleared polynomial -/

section Cleared

open MvPolynomial

/-- A pair's denominator as a polynomial in `(X₀, X₁) = (α, β)`. -/
noncomputable def linD (q : F × F) : MvPolynomial (Fin 2) F := X 0 + C q.1 + X 1 * C q.2

/-- **The cleared polynomial** of a set of pairs: `Σ_q Π_{q' ≠ q} (X₀ + v_{q'} + X₁ τ_{q'})`, the
numerator of `Σ_q 1/(X₀ + v_q + X₁ τ_q)`. -/
noncomputable def cleared [DecidableEq F] (O : Finset (F × F)) : MvPolynomial (Fin 2) F :=
  ∑ q ∈ O, ∏ q' ∈ O.erase q, linD q'

theorem eval_linD (α β : F) (q : F × F) : eval ![α, β] (linD q) = den α β q := by
  simp [linD, den]

theorem totalDegree_linD_le (q : F × F) : (linD q).totalDegree ≤ 1 := by
  unfold linD
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
  · rw [totalDegree_X]
  · rw [totalDegree_C]; exact zero_le_one
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_C]

variable [DecidableEq F]

theorem totalDegree_cleared_le (O : Finset (F × F)) : (cleared O).totalDegree ≤ O.card - 1 := by
  unfold cleared
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun q hq => ?_)
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ q' ∈ O.erase q, (linD q').totalDegree ≤ ∑ _q' ∈ O.erase q, 1 :=
        Finset.sum_le_sum fun q' _ => totalDegree_linD_le q'
    _ = O.card - 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hq]

/-- **The cleared polynomial is the sum's numerator**: where no denominator vanishes, its value is
the product of the denominators times the sum. -/
theorem eval_cleared (O : Finset (F × F)) (α β : F) (h : ∀ q ∈ O, den α β q ≠ 0) :
    eval ![α, β] (cleared O) = (∏ q ∈ O, den α β q) * ∑ q ∈ O, (den α β q)⁻¹ := by
  unfold cleared
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [map_prod]
  simp only [eval_linD]
  rw [← Finset.mul_prod_erase O (fun q => den α β q) hq]
  field_simp [h q hq]

/-- **The cleared polynomial of a nonempty set of pairs is not zero.** Substituting
`X₀ = v₀ + τ₀ Y`, `X₁ = Y` for a member `(v₀, τ₀)` kills every term but the one omitting it, which
becomes a product of nonzero polynomials in `Y` (the other pairs differ from `(v₀, τ₀)`). -/
theorem cleared_ne_zero (O : Finset (F × F)) (hO : O.Nonempty) : cleared O ≠ 0 := by
  obtain ⟨q₀, hq₀⟩ := hO
  let φ : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
    aeval ![Polynomial.C q₀.1 + Polynomial.C q₀.2 * Polynomial.X, Polynomial.X]
  have hφ : ∀ q : F × F, φ (linD q) =
      Polynomial.C (q₀.1 + q.1) + Polynomial.C (q₀.2 + q.2) * Polynomial.X := by
    intro q
    simp only [φ, linD, map_add, map_mul, aeval_X, aeval_C, Matrix.cons_val_zero,
      Matrix.cons_val_one, Polynomial.algebraMap_eq]
    ring
  have hzero : φ (linD q₀) = 0 := by
    rw [hφ, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, Polynomial.C_0, zero_mul,
      add_zero]
  have hne : ∀ q, q ≠ q₀ → φ (linD q) ≠ 0 := by
    intro q hq h0
    rw [hφ] at h0
    have h1 := congrArg (fun p => Polynomial.coeff p 0) h0
    have h2 := congrArg (fun p => Polynomial.coeff p 1) h0
    simp only [Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_X_one] at h1 h2
    simp at h1 h2
    apply hq
    exact Prod.ext (CharTwo.add_eq_zero.mp h1).symm (CharTwo.add_eq_zero.mp h2).symm
  intro h
  have himg : φ (cleared O) = ∏ q' ∈ O.erase q₀, φ (linD q') := by
    unfold cleared
    rw [map_sum, Finset.sum_eq_single q₀]
    · rw [map_prod]
    · intro q hq hqq
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h' => hqq h'.symm, hq₀⟩) hzero
    · intro h'; exact absurd hq₀ h'
  have : ∏ q' ∈ O.erase q₀, φ (linD q') ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q' hq' => hne q' (Finset.ne_of_mem_erase hq')
  rw [← himg, h, map_zero] at this
  exact this rfl

/-- **The sum is zero as a rational function exactly when every pair is even**: the cleared
polynomial of the odd pairs vanishes exactly then. -/
theorem cleared_eq_zero_iff (s : Finset ι) (e : ι → F × F) :
    cleared (oddPairs s e) = 0 ↔ EvenAll s e := by
  constructor
  · intro h
    by_contra hne
    exact cleared_ne_zero _ (oddPairs_nonempty s e hne) h
  · intro h
    have : oddPairs s e = ∅ := by
      unfold oddPairs
      exact Finset.filter_false_of_mem fun q _ hq => (Nat.not_odd_iff_even.mpr (h q)) hq
    rw [this]
    rfl

/-- Where no denominator of the family vanishes and the sum is zero, the cleared polynomial of the
odd pairs vanishes. -/
theorem eval_cleared_eq_zero (s : Finset ι) (e : ι → F × F) (α β : F)
    (hd : ∀ x ∈ s, den α β (e x) ≠ 0) (hs : logSum s e α β = 0) :
    eval ![α, β] (cleared (oddPairs s e)) = 0 := by
  have hO : ∀ q ∈ oddPairs s e, den α β q ≠ 0 := by
    intro q hq
    unfold oddPairs at hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    exact hd x hx
  rw [eval_cleared _ α β hO]
  unfold logSum at hs
  rw [sum_eq_sum_oddPairs s e fun q => (den α β q)⁻¹] at hs
  rw [hs, mul_zero]

end Cleared

/-! ## Schwartz–Zippel -/

section Count

variable [DecidableEq F] [Fintype F]

/-- Counting pairs `(α, β)` as points of `Fin 2 → F`. -/
theorem card_pairs_eq (P : F × F → Prop) [DecidablePred P] :
    (univ.filter P).card = (univ.filter fun v : Fin 2 → F => P (v 0, v 1)).card := by
  refine Finset.card_bij (fun ab _ => ![ab.1, ab.2]) (fun ab h => ?_) (fun a _ b _ h => ?_)
    (fun v hv => ⟨(v 0, v 1), ?_, ?_⟩)
  · simpa using h
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    exact Prod.ext h0 h1
  · simpa using hv
  · funext i
    fin_cases i <;> rfl

/-- **Schwartz–Zippel in two variables, counting form**: a nonzero polynomial of total degree at
most `d` vanishes at at most `d·|F|` points of `F²` (Mathlib's `schwartz_zippel_totalDegree`). -/
theorem card_zeros_le (p : MvPolynomial (Fin 2) F) (hp : p ≠ 0) {d : ℕ} (hd : p.totalDegree ≤ d) :
    (univ.filter fun v : Fin 2 → F => MvPolynomial.eval v p = 0).card ≤ d * Fintype.card F := by
  have h := MvPolynomial.schwartz_zippel_totalDegree hp (univ : Finset F)
  simp only [Fintype.piFinset_univ, Finset.card_univ] at h
  have hq : (0 : NNRat) < (Fintype.card F : NNRat) := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (pow_pos hq 2) hq] at h
  have h' : (univ.filter fun v : Fin 2 → F => MvPolynomial.eval v p = 0).card * Fintype.card F ≤
      p.totalDegree * Fintype.card F ^ 2 := by exact_mod_cast h
  have h'' : (univ.filter fun v : Fin 2 → F => MvPolynomial.eval v p = 0).card * Fintype.card F ≤
      (d * Fintype.card F) * Fintype.card F := by
    calc _ ≤ p.totalDegree * Fintype.card F ^ 2 := h'
      _ ≤ d * Fintype.card F ^ 2 := Nat.mul_le_mul_right _ hd
      _ = (d * Fintype.card F) * Fintype.card F := by ring
  exact Nat.le_of_mul_le_mul_right h'' Fintype.card_pos

/-- **logUp in characteristic two, counting form.** If some pair of the family occurs an odd number
of times, at most `(|s| − 1)·|F|` points `(α, β)` have every denominator nonzero and the
log-derivative sum zero. -/
theorem card_logSum_eq_zero_le (s : Finset ι) (e : ι → F × F) (h : ¬ EvenAll s e) :
    (univ.filter fun ab : F × F =>
        (∀ x ∈ s, den ab.1 ab.2 (e x) ≠ 0) ∧ logSum s e ab.1 ab.2 = 0).card ≤
      (s.card - 1) * Fintype.card F := by
  classical
  set O := oddPairs s e
  have hO := cleared_ne_zero O (oddPairs_nonempty s e h)
  have hdeg : (cleared O).totalDegree ≤ s.card - 1 :=
    (totalDegree_cleared_le O).trans (Nat.sub_le_sub_right (card_oddPairs_le s e) 1)
  have hsz := card_zeros_le (cleared O) hO hdeg
  rw [card_pairs_eq]
  refine (Finset.card_le_card fun v hv => ?_).trans hsz
  rw [Finset.mem_filter] at hv ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have := eval_cleared_eq_zero s e (v 0) (v 1) hv.2.1 hv.2.2
  have hv' : (![v 0, v 1] : Fin 2 → F) = v := by
    funext i
    fin_cases i <;> rfl
  rwa [hv'] at this

open OracleComp in
/-- **logUp in characteristic two**: if some pair of the family occurs an odd number of times, the
denominators are nonzero and the sum zero at a uniform `(α, β)` with probability at most
`(|s| − 1)/|F|`. -/
theorem prob_logSum_eq_zero_le [SampleableType F] (s : Finset ι) (e : ι → F × F)
    (h : ¬ EvenAll s e) :
    Pr{let ab ← $ᵗ (F × F)}[(∀ x ∈ s, den ab.1 ab.2 (e x) ≠ 0) ∧ logSum s e ab.1 ab.2 = 0] ≤
      ((s.card - 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  rw [SampleableType.prEvent_uniformSample, Fintype.card_prod]
  have hF : (Fintype.card F : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hFt : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((univ.filter fun ab : F × F =>
          (∀ x ∈ s, den ab.1 ab.2 (e x) ≠ 0) ∧ logSum s e ab.1 ab.2 = 0).card : ENNReal) /
        ((Fintype.card F * Fintype.card F : ℕ) : ENNReal)
      ≤ (((s.card - 1) * Fintype.card F : ℕ) : ENNReal) /
          ((Fintype.card F * Fintype.card F : ℕ) : ENNReal) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr (card_logSum_eq_zero_le s e h)) _
    _ = ((s.card - 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
        rw [Nat.cast_mul, Nat.cast_mul, ENNReal.mul_div_mul_right _ _ hF hFt]

end Count

/-! ## Every tag twice -/

/-- **Mod 2 is equality when every tag occurs twice.** If every pair of the family is even, `x` is a
member, and every member carrying `x`'s tag is `x` or `y`, then `x` and `y` carry the same value
(the pair `e x` has an even multiplicity, at least one, among at most the two members `x` and
`y`). -/
theorem eq_of_even_of_pair [DecidableEq F] (s : Finset ι) (e : ι → F × F) (hev : EvenAll s e)
    {x y : ι} (hx : x ∈ s) (hpair : ∀ z ∈ s, (e z).2 = (e x).2 → z = x ∨ z = y) : e x = e y := by
  by_contra hne
  have hsub : s.filter (fun z => e z = e x) ⊆ {x} := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rcases hpair z hz.1 (by rw [hz.2]) with rfl | rfl
    · exact Finset.mem_singleton_self _
    · exact absurd hz.2.symm hne
  have hmem : x ∈ s.filter (fun z => e z = e x) := Finset.mem_filter.mpr ⟨hx, rfl⟩
  have hone : (s.filter fun z => e z = e x).card = 1 :=
    le_antisymm ((Finset.card_le_card hsub).trans (Finset.card_singleton x).le)
      (Finset.card_pos.mpr ⟨x, hmem⟩)
  have := hev (e x)
  unfold mult at this
  rw [hone] at this
  exact Nat.not_even_one this

end RecPiop
