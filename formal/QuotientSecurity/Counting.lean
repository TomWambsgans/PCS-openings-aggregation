-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Counting.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.LogDerivative

/-!
# Counting the first challenge

Three sets of triples `(α, β, γ)`: those at which a denominator vanishes on a cell, those at which
the denominators of each cell vanish together and the sum of logarithmic derivatives meets a
target that depends on `γ` where none vanishes, and those at which a nonzero polynomial in `γ`
vanishes.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Few triples make a denominator vanish on a cell. -/
theorem card_zero_le (id : ι → F) (σ : Equiv.Perm ι) (w : ι → F) :
    (univ.filter fun p : F × F × F =>
        ∃ i, p.1 + w i + p.2.1 * id i = 0 ∨ p.1 + w i + p.2.1 * id (σ i) = 0).card
      ≤ 2 * Fintype.card ι * Fintype.card F ^ 2 := by
  classical
  let f : ι × Bool × F × F → F × F × F := fun r =>
    (w r.1 + r.2.2.1 * (if r.2.1 then id r.1 else id (σ r.1)), r.2.2.1, r.2.2.2)
  have hsub : (univ.filter fun p : F × F × F =>
      ∃ i, p.1 + w i + p.2.1 * id i = 0 ∨ p.1 + w i + p.2.1 * id (σ i) = 0)
        ⊆ univ.image f := by
    rintro ⟨α, β, γ⟩ hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, i, h | h⟩ := hp
    · refine Finset.mem_image.mpr ⟨(i, true, β, γ), Finset.mem_univ _, ?_⟩
      have : α = w i + β * id i := CharTwo.add_eq_zero.mp (by rw [← h]; ring)
      simp [f, this]
    · refine Finset.mem_image.mpr ⟨(i, false, β, γ), Finset.mem_univ _, ?_⟩
      have : α = w i + β * id (σ i) := CharTwo.add_eq_zero.mp (by rw [← h]; ring)
      simp [f, this]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
  exact le_of_eq (by ring)

/-- **The copy argument, over the triples.** If the values are not constant on the cycles, at most
`(4 N - 2) q^2` triples have, at every cell, both denominators zero or neither, and, where no
denominator vanishes, a sum of logarithmic derivatives equal to a target depending on `γ`
(`card_copy_le` for each `γ`). -/
theorem card_copy_triple_le (id : ι → F) (hid : Function.Injective id) (σ : Equiv.Perm ι)
    (w : ι → F) (hcopy : ¬ ∀ x, w (σ x) = w x) (c : F → F) :
    (univ.filter fun p : F × F × F =>
        (∀ x, p.1 + w x + p.2.1 * id x = 0 ↔ p.1 + w x + p.2.1 * id (σ x) = 0) ∧
          ((∀ x, p.1 + w x + p.2.1 * id x ≠ 0) → logSum id σ w p.1 p.2.1 = c p.2.2)).card
      ≤ (4 * Fintype.card ι - 2) * Fintype.card F ^ 2 := by
  classical
  set S := univ.filter fun p : F × F × F =>
    (∀ x, p.1 + w x + p.2.1 * id x = 0 ↔ p.1 + w x + p.2.1 * id (σ x) = 0) ∧
      ((∀ x, p.1 + w x + p.2.1 * id x ≠ 0) → logSum id σ w p.1 p.2.1 = c p.2.2) with hS
  have hsplit : S.card = ∑ γ : F, (S.filter fun p => p.2.2 = γ).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun p : F × F × F => p.2.2) (t := univ)
      fun _ _ => Finset.mem_univ _
  have hfiber : ∀ γ : F, (S.filter fun p => p.2.2 = γ).card
      ≤ (4 * Fintype.card ι - 2) * Fintype.card F := by
    intro γ
    refine le_trans ?_ (card_copy_le id hid σ w hcopy fun _ => c γ)
    refine le_trans (Finset.card_le_card (t := (univ.filter fun p : F × F =>
        (∀ x, p.1 + w x + p.2 * id x = 0 ↔ p.1 + w x + p.2 * id (σ x) = 0) ∧
          ((∀ x, p.1 + w x + p.2 * id x ≠ 0) → logSum id σ w p.1 p.2 = c γ)).image
        fun r : F × F => (r.1, r.2, γ)) ?_)
      Finset.card_image_le
    rintro ⟨α, β, γ'⟩ hp
    rw [Finset.mem_filter, hS, Finset.mem_filter] at hp
    obtain ⟨⟨-, h1, h2⟩, rfl⟩ := hp
    exact Finset.mem_image.mpr ⟨(α, β), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩, rfl⟩
  rw [hsplit]
  calc ∑ γ : F, (S.filter fun p => p.2.2 = γ).card
      ≤ ∑ _γ : F, (4 * Fintype.card ι - 2) * Fintype.card F :=
        Finset.sum_le_sum fun γ _ => hfiber γ
    _ = (4 * Fintype.card ι - 2) * Fintype.card F ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

/-- Few `γ` annihilate a combination of powers whose coefficients are not all zero. -/
theorem card_powers_le {k : ℕ} (e : Fin k → F) (he : e ≠ 0) :
    (univ.filter fun γ : F => ∑ J : Fin k, γ ^ (J : ℕ) * e J = 0).card ≤ k := by
  classical
  set Q : F[X] := ∑ J : Fin k, monomial (J : ℕ) (e J) with hQ
  have hcoeff : ∀ J₀ : Fin k, Q.coeff J₀ = e J₀ := by
    intro J₀
    rw [hQ, finset_sum_coeff, Finset.sum_eq_single J₀]
    · simp
    · intro J _ hJ
      rw [coeff_monomial, if_neg fun h => hJ (Fin.ext h)]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQ0 : Q ≠ 0 := by
    intro h
    apply he
    funext J
    rw [← hcoeff J, h]
    simp
  have hdeg : Q.natDegree ≤ k :=
    natDegree_sum_le_of_forall_le _ _ fun J _ =>
      (natDegree_monomial_le _).trans J.2.le
  have hsub : (univ.filter fun γ : F => ∑ J : Fin k, γ ^ (J : ℕ) * e J = 0) ⊆ Q.roots.toFinset := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    rw [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def, hQ, eval_finsetSum, ← hγ.2]
    exact Finset.sum_congr rfl fun J _ => by rw [eval_monomial]; ring
  calc _ ≤ Q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' Q
    _ ≤ k := hdeg

end QuotientSecurity
