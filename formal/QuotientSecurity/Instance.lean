-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Instance.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Completeness

/-!
# The parameters exist

`Params` asks for polynomials with properties. This file builds them from the data a circuit
gives (rows whose cells are distinct points, a permutation of the cells, public words as linear
functionals) by products and interpolation, so the hypotheses of the security theorems are not
vacuous: every such circuit is an instance, with exact vanishing polynomials.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F]

/-- The parameters of a circuit: its rows, its wiring and its public words. -/
noncomputable def Params.ofData (θ : F) (hθ : θ * θ + θ + 1 = 0) (T : Finset F)
    (hT : ∀ x ∈ T, ∀ y ∈ T, ∀ c d : Fin 4, x + shift θ c = y + shift θ d → x = y ∧ c = d)
    (σ : Equiv.Perm (T × Fin 4)) (words : ℕ) (wordSum : Fin words → (T × Fin 4 → F) →ₗ[F] F) :
    Params F :=
  have hinj : Function.Injective fun i : T × Fin 4 => (i.1 : F) + shift θ i.2 := by
    rintro ⟨⟨x, hx⟩, c⟩ ⟨⟨y, hy⟩, d⟩ h
    obtain ⟨rfl, rfl⟩ := hT x hx y hy c d h
    rfl
  { θ := θ
    hθ := hθ
    T := T
    hT := hT
    vCells := ∏ i : T × Fin 4, (X - C ((i.1 : F) + shift θ i.2))
    vRows := ∏ x : T, (X - C (x : F))
    hCells := fun x hx c => by
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨x, hx⟩, c)) (by simp)
    hRows := fun x hx => by
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨x, hx⟩ : T)) (by simp)
    σ := σ
    sigmaPoly := Lagrange.interpolate univ (fun i : T × Fin 4 => (i.1 : F) + shift θ i.2)
      fun i => ((σ i).1 : F) + shift θ (σ i).2
    hσ := fun i => Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)
    words := words
    wordSum := wordSum
    pub := fun γ => Lagrange.interpolate univ (fun i : T × Fin 4 => (i.1 : F) + shift θ i.2)
      fun i => ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J (fun j => if i = j then 1 else 0)
    hPub := fun γ w => by
      have hnode : ∀ i : T × Fin 4,
          (Lagrange.interpolate univ (fun i : T × Fin 4 => (i.1 : F) + shift θ i.2)
            fun i => ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J (fun j => if i = j then 1 else 0)).eval
              ((i.1 : F) + shift θ i.2)
            = ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J (fun j => if i = j then 1 else 0) := fun i =>
        Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)
      simp only [hnode, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [(wordSum J).pi_apply_eq_sum_univ w, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul]
      ring }

/-- Its vanishing polynomials are the exact ones. -/
theorem Params.ofData_exact (θ : F) (hθ : θ * θ + θ + 1 = 0) (T : Finset F)
    (hT : ∀ x ∈ T, ∀ y ∈ T, ∀ c d : Fin 4, x + shift θ c = y + shift θ d → x = y ∧ c = d)
    (σ : Equiv.Perm (T × Fin 4)) (words : ℕ) (wordSum : Fin words → (T × Fin 4 → F) →ₗ[F] F) :
    (Params.ofData θ hθ T hT σ words wordSum).Exact :=
  ⟨rfl, rfl⟩

end QuotientSecurity
