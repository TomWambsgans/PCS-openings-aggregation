import QuotientSecurity

/-! Review experiment 4: what the zero-knowledge model hides behind its ideal commitments.

* The honest sum polynomial `h₀` (the quotient table's first slot, which `prove` commits
  unmasked) does not depend on the masks at all: it is a function of the witness and `(α, β, γ)`.
* Three mask coefficients in `K` cover exactly one value in `E` (`maskedValue_bijective`), so no
  map from the masks can make two values of `E` uniform: a second opened evaluation of a masked
  row polynomial is not simulatable from the masks alone. -/

open QuotientSecurity Polynomial Module

namespace Review

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2]

/-- The honest `h₀` is the same for every choice of masks. -/
theorem honest_h_mask_free [Fintype E] (P : Params E) (gK : Fin 4 → K[X]) (van : K[X])
    (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0) (m m' : Fin 4 → Fin 3 → K)
    (α β γ : E) :
    (Params.honest P (committed gK van m) α β γ).h₀
      = (Params.honest P (committed gK van m') α β γ).h₀ := by
  have hs : Params.sumValue P (committed gK van m) α β γ
      = Params.sumValue P (committed gK van m') α β γ := by
    funext i
    simp only [Params.sumValue, cells_committed P gK van hvan m m']
  simp only [Params.honest, hs]

/-- No function of the three mask coefficients reaches every pair of values in `E`. -/
theorem masks_cover_one_value [Fintype K] [Fintype E] [FiniteDimensional K E]
    (h3 : finrank K E = 3) (f : (Fin 3 → K) → E × E) : ¬ Function.Surjective f := by
  intro hs
  have h1 := Fintype.card_le_of_surjective f hs
  have hc : Fintype.card (Fin 3 → K) = Fintype.card E := by
    rw [Module.card_eq_pow_finrank (K := K) (V := E), h3]
    simp
  rw [hc, Fintype.card_prod] at h1
  have : 1 < Fintype.card E := Fintype.one_lt_card
  nlinarith

end Review
