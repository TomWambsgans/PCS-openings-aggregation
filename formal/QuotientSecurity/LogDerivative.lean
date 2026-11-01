-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/LogDerivative.lean. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib

/-!
# The copy argument: a sum of logarithmic derivatives in characteristic 2

Cells `ι` carry values `w` and distinct labels `id`, and `σ` permutes the cells. With
`D x = α + w x + β * id x` and `D' x = α + w x + β * id (σ x)`, the sum of `1 / D x + 1 / D' x`
over the cells is zero when `w` is constant on the cycles of `σ`, and otherwise equals a given
value for few `(α, β)`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]
variable {ι : Type*} [Fintype ι]

/-- The sum of logarithmic derivatives. -/
def logSum (id : ι → F) (σ : Equiv.Perm ι) (w : ι → F) (α β : F) : F :=
  ∑ x, ((α + w x + β * id x)⁻¹ + (α + w x + β * id (σ x))⁻¹)

/-- If the values are constant on the cycles, the sum vanishes. -/
theorem logSum_eq_zero_of_copy (id : ι → F) (σ : Equiv.Perm ι) (w : ι → F)
    (h : ∀ x, w (σ x) = w x) (α β : F) : logSum id σ w α β = 0 := by
  unfold logSum
  rw [Finset.sum_add_distrib]
  have : ∑ x, (α + w x + β * id (σ x))⁻¹ = ∑ x, (α + w x + β * id x)⁻¹ := by
    rw [← Equiv.sum_comp σ (fun x => (α + w x + β * id x)⁻¹)]
    exact Finset.sum_congr rfl fun x _ => by rw [h x]
  rw [this]
  exact CharTwo.add_self_eq_zero _

variable [DecidableEq ι]

/-- The polynomial in `α` that the sum minus `c`, cleared of its denominators, is. -/
noncomputable def clearedPoly (a b : ι → F) (c : F) : F[X] :=
  (∑ x, (∏ y ∈ univ.erase x, (X + C (a y))) * ∏ y, (X + C (b y)))
    + (∑ x, (∏ y, (X + C (a y))) * ∏ y ∈ univ.erase x, (X + C (b y)))
    + C c * ((∏ y, (X + C (a y))) * ∏ y, (X + C (b y)))

theorem natDegree_prod_X_add_C_le (s : Finset ι) (a : ι → F) :
    (∏ y ∈ s, (X + C (a y))).natDegree ≤ s.card := by
  refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
  simp

theorem natDegree_clearedPoly_le (a b : ι → F) (c : F) :
    (clearedPoly a b c).natDegree ≤ 2 * Fintype.card ι := by
  have hu : (univ : Finset ι).card = Fintype.card ι := Finset.card_univ
  have he : ∀ x : ι, (univ.erase x).card ≤ Fintype.card ι := fun x =>
    (Finset.card_erase_le).trans hu.le
  have ha := natDegree_prod_X_add_C_le (univ : Finset ι) a
  have hb := natDegree_prod_X_add_C_le (univ : Finset ι) b
  unfold clearedPoly
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    refine natDegree_mul_le.trans ?_
    have := natDegree_prod_X_add_C_le (univ.erase x) a
    have := he x
    omega
  · refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    refine natDegree_mul_le.trans ?_
    have := natDegree_prod_X_add_C_le (univ.erase x) b
    have := he x
    omega
  · refine natDegree_mul_le.trans ?_
    have h1 : (C c : F[X]).natDegree = 0 := natDegree_C c
    have h2 := (natDegree_mul_le (p := ∏ y, (X + C (a y))) (q := ∏ y, (X + C (b y))))
    omega

/-- Where no denominator vanishes, the cleared polynomial is the product of the denominators
times the sum minus `c`. -/
theorem eval_clearedPoly (a b : ι → F) (c α : F)
    (ha : ∀ x, α + a x ≠ 0) (hb : ∀ x, α + b x ≠ 0) :
    (clearedPoly a b c).eval α =
      ((∏ y, (α + a y)) * ∏ y, (α + b y)) * (∑ x, ((α + a x)⁻¹ + (α + b x)⁻¹) + c) := by
  have hA : ∀ x : ι, ∏ y ∈ univ.erase x, (α + a y) = (∏ y, (α + a y)) * (α + a x)⁻¹ := by
    intro x
    rw [← Finset.mul_prod_erase univ (fun y => α + a y) (Finset.mem_univ x)]
    field_simp [ha x]
  have hB : ∀ x : ι, ∏ y ∈ univ.erase x, (α + b y) = (∏ y, (α + b y)) * (α + b x)⁻¹ := by
    intro x
    rw [← Finset.mul_prod_erase univ (fun y => α + b y) (Finset.mem_univ x)]
    field_simp [hb x]
  simp only [clearedPoly, eval_add, eval_finsetSum, eval_mul, eval_prod, eval_X, eval_C]
  simp only [hA, hB]
  rw [Finset.sum_add_distrib, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun x _ => by ring
    · exact Finset.sum_congr rfl fun x _ => by ring
  · ring

/-- If `a` is injective and one of its values is not a value of `b`, the cleared polynomial is
not zero. -/
theorem clearedPoly_ne_zero (a b : ι → F) (c : F) (ha : Function.Injective a)
    (x₀ : ι) (hx₀ : ∀ y, a x₀ ≠ b y) : clearedPoly a b c ≠ 0 := by
  intro h
  have hev : (clearedPoly a b c).eval (a x₀) = 0 := by rw [h]; simp
  have hzero : ∏ y, (a x₀ + a y) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ x₀) (CharTwo.add_self_eq_zero _)
  simp only [clearedPoly, eval_add, eval_finsetSum, eval_mul, eval_prod, eval_X, eval_C,
    hzero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero] at hev
  rw [Finset.sum_eq_single x₀] at hev
  · rcases mul_eq_zero.mp hev with h1 | h1
    · obtain ⟨y, hy, hy0⟩ := Finset.prod_eq_zero_iff.mp h1
      have hne : y ≠ x₀ := (Finset.mem_erase.mp hy).1
      have : a x₀ = a y := by
        have := CharTwo.add_eq_zero.mp hy0
        exact this
      exact hne (ha this).symm
    · obtain ⟨y, _, hy0⟩ := Finset.prod_eq_zero_iff.mp h1
      exact hx₀ y (CharTwo.add_eq_zero.mp hy0)
  · intro x _ hx
    have : ∏ y ∈ univ.erase x, (a x₀ + a y) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hx h.symm, Finset.mem_univ _⟩)
        (CharTwo.add_self_eq_zero _)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

variable [DecidableEq F]

/-- The `β` at which two cells share a pole, or a pole of the first kind meets one of the second
kind of another label. -/
noncomputable def badBetas (id : ι → F) (σ : Equiv.Perm ι) (w : ι → F) : Finset F :=
  (univ.image fun p : ι × ι => (w p.1 + w p.2) / (id p.1 + id p.2))
    ∪ (univ.image fun p : ι × ι => (w p.1 + w p.2) / (id p.1 + id (σ p.2)))

theorem card_badBetas_le (id : ι → F) (σ : Equiv.Perm ι) (w : ι → F) :
    (badBetas id σ w).card ≤ 2 * Fintype.card ι ^ 2 := by
  unfold badBetas
  refine (Finset.card_union_le _ _).trans ?_
  have h : ∀ f : ι × ι → F, (univ.image f).card ≤ Fintype.card ι ^ 2 := fun f =>
    Finset.card_image_le.trans (by simp [sq])
  have h1 := h fun p : ι × ι => (w p.1 + w p.2) / (id p.1 + id p.2)
  have h2 := h fun p : ι × ι => (w p.1 + w p.2) / (id p.1 + id (σ p.2))
  omega

/-- In characteristic 2, `u + β * i = v + β * j` with `i ≠ j` determines `β`. -/
theorem beta_eq_of_pole_eq {u v i j β : F} (h : u + β * i = v + β * j) (hij : i ≠ j) :
    β = (u + v) / (i + j) := by
  have hne : i + j ≠ 0 := fun h0 => hij (CharTwo.add_eq_zero.mp h0)
  rw [eq_div_iff hne]
  have h2 : u + β * i + (v + β * j) = 0 := by rw [h]; exact CharTwo.add_self_eq_zero _
  have h3 : β * (i + j) + (u + v) = 0 := by rw [← h2]; ring
  exact CharTwo.add_eq_zero.mp h3

/-- Away from the bad `β`, the poles of the first kind are distinct, and if the values are not
constant on the cycles, one of them is no pole of the second kind. -/
theorem good_beta (id : ι → F) (hid : Function.Injective id) (σ : Equiv.Perm ι) (w : ι → F)
    (hcopy : ¬ ∀ x, w (σ x) = w x) {β : F} (hβ : β ∉ badBetas id σ w) :
    Function.Injective (fun x => w x + β * id x) ∧
      ∃ x₀, ∀ y, w x₀ + β * id x₀ ≠ w y + β * id (σ y) := by
  simp only [badBetas, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    not_or, not_exists] at hβ
  refine ⟨fun x y hxy => ?_, ?_⟩
  · by_contra hne
    exact hβ.1 (x, y) (beta_eq_of_pole_eq hxy fun h => hne (hid h)).symm
  · push_neg at hcopy
    obtain ⟨x₁, hx₁⟩ := hcopy
    refine ⟨σ x₁, fun y hy => ?_⟩
    by_cases hyx : σ x₁ = σ y
    · have : x₁ = y := σ.injective hyx
      subst this
      exact hx₁ (add_right_cancel hy)
    · exact hβ.2 (σ x₁, y) (beta_eq_of_pole_eq hy fun h => hyx (hid h)).symm

variable [Fintype F]

/-- **The copy argument.** If the values are not constant on the cycles of `σ`, then for any
target `c`, which may depend on `β`, few `(α, β)` have no vanishing denominator and a sum of
logarithmic derivatives equal to the target. -/
theorem card_logSum_eq_le (id : ι → F) (hid : Function.Injective id) (σ : Equiv.Perm ι)
    (w : ι → F) (hcopy : ¬ ∀ x, w (σ x) = w x) (c : F → F) :
    (univ.filter fun p : F × F =>
        (∀ x, p.1 + w x + p.2 * id x ≠ 0) ∧ (∀ x, p.1 + w x + p.2 * id (σ x) ≠ 0) ∧
          logSum id σ w p.1 p.2 = c p.2).card
      ≤ (2 * Fintype.card ι ^ 2 + 2 * Fintype.card ι) * Fintype.card F := by
  classical
  set S := univ.filter fun p : F × F =>
    (∀ x, p.1 + w x + p.2 * id x ≠ 0) ∧ (∀ x, p.1 + w x + p.2 * id (σ x) ≠ 0) ∧
      logSum id σ w p.1 p.2 = c p.2 with hS
  -- Split by `β`.
  have hsplit : S.card = ∑ β : F, (S.filter fun p => p.2 = β).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun p : F × F => p.2) (t := univ)
      fun _ _ => Finset.mem_univ _
  have hfiber_all : ∀ β : F, (S.filter fun p => p.2 = β).card ≤ Fintype.card F := by
    intro β
    have : (S.filter fun p => p.2 = β).card ≤ (univ.image fun α : F => (α, β)).card := by
      refine Finset.card_le_card fun p hp => ?_
      rw [Finset.mem_filter] at hp
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, by rw [← hp.2]⟩
    exact this.trans (Finset.card_image_le.trans (by simp))
  have hfiber_good : ∀ β : F, β ∉ badBetas id σ w →
      (S.filter fun p => p.2 = β).card ≤ 2 * Fintype.card ι := by
    intro β hβ
    obtain ⟨hinj, x₀, hx₀⟩ := good_beta id hid σ w hcopy hβ
    set Q := clearedPoly (fun x => w x + β * id x) (fun x => w x + β * id (σ x)) (c β) with hQ
    have hQ0 : Q ≠ 0 := clearedPoly_ne_zero _ _ _ hinj x₀ hx₀
    have hsub : (S.filter fun p => p.2 = β) ⊆ Q.roots.toFinset.image fun α : F => (α, β) := by
      intro p hp
      rw [Finset.mem_filter, hS, Finset.mem_filter] at hp
      obtain ⟨⟨-, h1, h2, h3⟩, rfl⟩ := hp
      refine Finset.mem_image.mpr ⟨p.1, ?_, rfl⟩
      rw [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def, hQ,
        eval_clearedPoly _ _ _ _ (fun x => by rw [← add_assoc]; exact h1 x)
          (fun x => by rw [← add_assoc]; exact h2 x)]
      have : ∑ x, ((p.1 + (w x + p.2 * id x))⁻¹ + (p.1 + (w x + p.2 * id (σ x)))⁻¹) + c p.2
          = 0 := by
        have : ∑ x, ((p.1 + (w x + p.2 * id x))⁻¹ + (p.1 + (w x + p.2 * id (σ x)))⁻¹)
            = logSum id σ w p.1 p.2 := by
          unfold logSum
          exact Finset.sum_congr rfl fun x _ => by rw [add_assoc, add_assoc]
        rw [this, h3]
        exact CharTwo.add_self_eq_zero _
      rw [this, mul_zero]
    calc (S.filter fun p => p.2 = β).card
        ≤ (Q.roots.toFinset.image fun α : F => (α, β)).card := Finset.card_le_card hsub
      _ ≤ Q.roots.toFinset.card := Finset.card_image_le
      _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
      _ ≤ Q.natDegree := card_roots' Q
      _ ≤ 2 * Fintype.card ι := natDegree_clearedPoly_le _ _ _
  rw [hsplit]
  calc ∑ β : F, (S.filter fun p => p.2 = β).card
      ≤ ∑ β : F, (if β ∈ badBetas id σ w then Fintype.card F else 2 * Fintype.card ι) :=
        Finset.sum_le_sum fun β _ => by
          split_ifs with h
          · exact hfiber_all β
          · exact hfiber_good β h
    _ = (badBetas id σ w).card * Fintype.card F
          + (univ.filter fun β => β ∉ badBetas id σ w).card * (2 * Fintype.card ι) := by
        have hmem : (univ.filter fun β => β ∈ badBetas id σ w) = badBetas id σ w := by
          ext β; simp
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hmem]
    _ ≤ (2 * Fintype.card ι ^ 2) * Fintype.card F + Fintype.card F * (2 * Fintype.card ι) := by
        gcongr
        · exact card_badBetas_le id σ w
        · exact (Finset.card_le_univ _)
    _ = (2 * Fintype.card ι ^ 2 + 2 * Fintype.card ι) * Fintype.card F := by ring

end QuotientSecurity
