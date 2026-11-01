-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Model

/-!
# Condition (Q): the first piece interpolates the opened positions

A lane's codeword at a point `x` of the domain is `Σ_y T(y)·B_y(x)`, `B_y` the code's basis polynomial
of index `y`; for WHIR's additive NTT it is the novel basis polynomial `X_y`, of degree `y`. The first
piece holds the coefficients of the `B_y` with `y < m` (`m = 2^s`). If `deg B_y = y`, these span the
polynomials of degree below `m` (`mem_span_of_degree_lt`), so by Lagrange interpolation the first
piece takes any values at `|Q| ≤ m` distinct points: condition (Q) of `Model.level0_hides`
(`firstEval_surjective_of_degrees`). With `|Q| < m`, it also takes the value `0` on `Q` and `1` at any
other point: the vector `u` of `Merkle.HiddenLayout.unopened_row_le` (`exists_unopened_vector`).
-/

namespace QuotientSecurity.Hiding

open Finset Polynomial

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- Polynomials with one of each degree below `m` span the polynomials of degree below `m`. -/
theorem mem_span_of_degree_lt {N m : ℕ} (hm : m ≤ N) (B : Fin N → K[X])
    (hB : ∀ y, (B y).natDegree = y) (hB0 : ∀ y, B y ≠ 0) :
    ∀ P : K[X], P.degree < m →
      P ∈ Submodule.span K (B '' {y : Fin N | (y : ℕ) < m}) := by
  intro P
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ d ih =>
    intro hP
    by_cases hP0 : P = 0
    · rw [hP0]
      exact Submodule.zero_mem _
    have hd : d < m := by
      rw [← h]
      exact (natDegree_lt_iff_degree_lt hP0).mpr hP
    set y : Fin N := ⟨d, lt_of_lt_of_le hd hm⟩
    have hBy : (B y).natDegree = d := hB y
    set c := P.leadingCoeff / (B y).leadingCoeff
    have hlc : (B y).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hB0 y)
    have hPlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
    have hc : c ≠ 0 := div_ne_zero hPlc hlc
    have hmem : C c * B y ∈ Submodule.span K (B '' {y : Fin N | (y : ℕ) < m}) := by
      rw [← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hd, rfl⟩)
    have hdeg_eq : (C c * B y).degree = P.degree := by
      rw [degree_C_mul hc, degree_eq_natDegree (hB0 y), degree_eq_natDegree hP0, hBy, h]
    have hlc_eq : (C c * B y).leadingCoeff = P.leadingCoeff := by
      rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hc)]
      simp [c, hlc]
    have hsub := Submodule.sub_mem _ (Submodule.zero_mem _) hmem
    by_cases hR : P - C c * B y = 0
    · rw [sub_eq_zero.mp hR]
      exact hmem
    have hlt : (P - C c * B y).degree < P.degree :=
      degree_sub_lt hdeg_eq.symm hP0 hlc_eq.symm
    have hnd : (P - C c * B y).natDegree < d := by
      rw [← h]
      exact natDegree_lt_natDegree hR hlt
    have hR' := ih _ hnd (P - C c * B y) rfl (lt_trans hlt hP)
    have := Submodule.add_mem _ hR' hmem
    simpa using this

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- **Condition (Q).** With `deg B_y = y`, the first `m` coefficients take any values at `|Q| ≤ m`
distinct points. -/
theorem firstEval_surjective_of_degrees {N m : ℕ} (hm : m ≤ N) (B : Fin N → K[X])
    (hB : ∀ y, (B y).natDegree = y) (hB0 : ∀ y, B y ≠ 0) (pt : Q → K)
    (hpt : Function.Injective pt) (hQ : Fintype.card Q ≤ m) :
    Function.Surjective (firstEval (fun x y => (B y).eval (pt x))
      (univ.filter fun y : Fin N => (y : ℕ) < m)) := by
  classical
  intro v
  set P := Lagrange.interpolate (univ : Finset Q) pt v
  have hdeg : P.degree < m :=
    lt_of_lt_of_le (Lagrange.degree_interpolate_lt _ (hpt.injOn))
      (by rw [card_univ]; exact_mod_cast hQ)
  have hmem := mem_span_of_degree_lt hm B hB hB0 P hdeg
  obtain ⟨l, hl, hlP⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hmem
  refine ⟨fun y => l y, ?_⟩
  funext x
  show ∑ y ∈ univ.filter fun y : Fin N => (y : ℕ) < m, (B y).eval (pt x) * l y = v x
  have hsupp : ∀ y, y ∉ (univ.filter fun y : Fin N => (y : ℕ) < m) → l y = 0 := by
    intro y hy
    by_contra hne
    exact hy (mem_filter.mpr ⟨mem_univ _, hl (Finsupp.mem_support_iff.mpr hne)⟩)
  have hP : P.eval (pt x) = v x := Lagrange.eval_interpolate_at_node _ hpt.injOn (mem_univ x)
  rw [← hP, ← hlP, Finsupp.linearCombination_apply, Finsupp.sum, eval_finsetSum]
  symm
  refine sum_subset (fun y hy => ?_) (fun y _ hy => ?_) |>.trans (sum_congr rfl fun y _ => ?_)
  · by_contra hno
    exact (Finsupp.mem_support_iff.mp hy) (hsupp y hno)
  · rw [Finsupp.notMem_support_iff.mp hy, zero_smul, eval_zero]
  · rw [eval_smul, smul_eq_mul, mul_comm]

/-- **The vector behind an unopened row.** With `|Q| < m`, some first-piece vector is `0` at the
opened positions and `1` at a further point `x₀`. -/
theorem exists_unopened_vector {N m : ℕ} (hm : m ≤ N) (B : Fin N → K[X])
    (hB : ∀ y, (B y).natDegree = y) (hB0 : ∀ y, B y ≠ 0) (pt : Q → K)
    (hpt : Function.Injective pt) (hQ : Fintype.card Q < m) (x₀ : K) (hx₀ : ∀ x, pt x ≠ x₀) :
    ∃ u : Fin N → K, (∀ y : Fin N, ¬ (y : ℕ) < m → u y = 0) ∧
      (∀ x, ∑ y, (B y).eval (pt x) * u y = 0) ∧ ∑ y, (B y).eval x₀ * u y = 1 := by
  classical
  set pt' : Option Q → K := fun o => o.elim x₀ pt
  have hpt' : Function.Injective pt' := by
    intro o o' h
    cases o <;> cases o'
    · rfl
    · exact absurd h.symm (hx₀ _)
    · exact absurd h (hx₀ _)
    · exact congrArg some (hpt h)
  have hQ' : Fintype.card (Option Q) ≤ m := by
    rw [Fintype.card_option]
    omega
  obtain ⟨z, hz⟩ := firstEval_surjective_of_degrees hm B hB hB0 pt' hpt' hQ'
    (fun o => o.elim 1 fun _ => 0)
  set u : Fin N → K := fun y => if (y : ℕ) < m then z y else 0
  have hsum : ∀ o : Option Q, ∑ y, (B y).eval (pt' o) * u y = o.elim 1 fun _ => 0 := by
    intro o
    rw [← congrFun hz o]
    show _ = ∑ y ∈ univ.filter fun y : Fin N => (y : ℕ) < m, (B y).eval (pt' o) * z y
    rw [sum_filter]
    refine sum_congr rfl fun y _ => ?_
    simp only [u]
    split_ifs <;> simp
  refine ⟨u, fun y hy => by simp [u, hy], fun x => ?_, ?_⟩
  · simpa [pt'] using hsum (some x)
  · simpa [pt'] using hsum none

end QuotientSecurity.Hiding
