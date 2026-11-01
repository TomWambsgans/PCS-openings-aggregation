-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/ZeroKnowledge.lean. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Zero knowledge of the reduction

The verifier sees four values `a_j = G_j(r)`, the wiring's value at its own challenge, which is
public, and four claims it computes from them. Each committed `G_j` is the witness's row
polynomial `g_j`, over the small field `K`, plus the rows' vanishing polynomial times a mask of
three uniform coefficients in `K`. The point `r` is in the cubic extension `E`. This file proves
that for every `r` outside `K` at which the vanishing polynomial is not zero, the four values are
exactly uniform in `E^4`, whatever the witness: a simulator samples them.
-/

open Module Polynomial IntermediateField

namespace QuotientSecurity

variable {K E : Type} [Field K] [Field E] [Algebra K E]

/-- In an extension of degree 3, an element outside the base field has a minimal polynomial of
degree 3. -/
theorem natDegree_minpoly_eq_three [FiniteDimensional K E] (h3 : finrank K E = 3) {r : E}
    (hr : r ∉ Set.range (algebraMap K E)) : (minpoly K r).natDegree = 3 := by
  have hint : IsIntegral K r := Algebra.IsIntegral.isIntegral r
  rw [← IntermediateField.adjoin.finrank hint]
  have hmul := Module.finrank_mul_finrank K K⟮r⟯ E
  rw [h3] at hmul
  have hdvd : finrank K K⟮r⟯ ∣ 3 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h
  · exact absurd (IntermediateField.mem_bot.mp
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h1)) hr
  · exact h

/-- A value of a masked polynomial: the unmasked value `e`, plus the vanishing polynomial's value
`u` times the mask at `r`. -/
def maskedValue (e u r : E) (m : Fin 3 → K) : E := e + u * ∑ i, m i • r ^ (i : ℕ)

/-- **A mask of three coefficients covers one value.** The map from the mask to the value is a
bijection from `K^3` to `E`. -/
theorem maskedValue_bijective [Fintype K] [Fintype E] [FiniteDimensional K E]
    (h3 : finrank K E = 3) (e : E) {u r : E} (hu : u ≠ 0)
    (hr : r ∉ Set.range (algebraMap K E)) : Function.Bijective (maskedValue (K := K) e u r) := by
  classical
  have hdeg := natDegree_minpoly_eq_three h3 hr
  have hli : LinearIndependent K fun i : Fin 3 => r ^ (i : ℕ) := hdeg ▸ linearIndependent_pow r
  have hinj : Function.Injective fun m : Fin 3 → K => ∑ i, m i • r ^ (i : ℕ) := by
    intro m m' h
    have h0 : ∑ i, (m i - m' i) • r ^ (i : ℕ) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr h
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  have hcard : Fintype.card (Fin 3 → K) = Fintype.card E := by
    rw [Module.card_eq_pow_finrank (K := K) (V := E), h3]
    simp
  have hbij : Function.Bijective fun m : Fin 3 → K => ∑ i, m i • r ^ (i : ℕ) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩
  exact (AddGroup.addLeft_bijective e).comp ((mulLeft_bijective₀ u hu).comp hbij)

/-- The masked polynomial takes that value: `g + v * (m_0 + m_1 X + m_2 X^2)` at `r`. -/
theorem aeval_masked (g v : K[X]) (m : Fin 3 → K) (r : E) :
    aeval r (g + v * (C (m 0) + C (m 1) * X + C (m 2) * X ^ 2))
      = maskedValue (aeval r g) (aeval r v) r m := by
  simp only [maskedValue, map_add, map_mul, aeval_C, aeval_X, map_pow, Fin.sum_univ_three,
    Algebra.smul_def]
  simp

/-- The mask changes nothing where the vanishing polynomial vanishes: the witness is the same. -/
theorem eval_masked_of_vanishing (g v : K[X]) (m : Fin 3 → K) {x : K} (hx : v.eval x = 0) :
    (g + v * (C (m 0) + C (m 1) * X + C (m 2) * X ^ 2)).eval x = g.eval x := by
  simp [hx]

section Simulation

variable [Fintype K] [Fintype E] [FiniteDimensional K E] [SampleableType K] [SampleableType E]

/-- What the honest prover sends: the four masked values, under uniform masks. -/
noncomputable def realValues (e : Fin 4 → E) (u r : E) : ProbComp (Fin 4 → E) :=
  (fun (m : Fin 4 → Fin 3 → K) (j : Fin 4) => maskedValue (e j) u r (m j)) <$>
    ($ᵗ (Fin 4 → Fin 3 → K))

/-- **Honest-verifier zero knowledge.** For a challenge whose row `r` is outside `K` and not a
root of the rows' vanishing polynomial, the four values have exactly the distribution of four
uniform elements of `E`, whatever the witness's values `e`. -/
theorem realValues_uniform (h3 : finrank K E = 3) (e : Fin 4 → E) {u r : E} (hu : u ≠ 0)
    (hr : r ∉ Set.range (algebraMap K E)) (a : Fin 4 → E) :
    Pr{let x ← realValues (K := K) e u r}[x = a] = Pr{let x ← $ᵗ (Fin 4 → E)}[x = a] := by
  refine (SampleableType.map_uniformSample_evalDistEq_of_bijective ?_).prEvent_eq (· = a)
  have hb := fun j => maskedValue_bijective (K := K) h3 (e j) hu hr
  constructor
  · intro m m' h
    funext j
    exact (hb j).injective (congrFun h j)
  · intro a
    choose m hm using fun j => (hb j).surjective (a j)
    exact ⟨m, funext hm⟩

/-- So two witnesses are indistinguishable. -/
theorem realValues_witness_independent (h3 : finrank K E = 3) (e e' : Fin 4 → E) {u r : E}
    (hu : u ≠ 0) (hr : r ∉ Set.range (algebraMap K E)) (a : Fin 4 → E) :
    Pr{let x ← realValues (K := K) e u r}[x = a]
      = Pr{let x ← realValues (K := K) e' u r}[x = a] := by
  rw [realValues_uniform h3 e hu hr, realValues_uniform h3 e' hu hr]

end Simulation

/-! ## A row in the small field

When `r` is in `K`, everything the prover sends is in `K`, and the four values are uniform there:
a simulator that looks at `r` samples them in `K`. So the only challenges that leak are the roots
of the rows' vanishing polynomial. -/

section Fibers

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] [SampleableType α]
  [SampleableType β]

/-- A uniform sample pushed through a map whose fibers all have the same size is uniform. -/
theorem probOutput_map_uniform_of_fibers (f : α → β) (c : ℕ)
    (hc : ∀ b, (Finset.univ.filter fun x => f x = b).card = c) (b : β) :
    Pr{let x ← f <$> ($ᵗ α)}[x = b] = Pr{let x ← $ᵗ β}[x = b] := by
  have hsum : Fintype.card α = c * Fintype.card β := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp [hc, mul_comm]
  have hα : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨OracleComp.defaultResult ($ᵗ α)⟩
  have hc0 : (c : ENNReal) ≠ 0 := by
    intro h
    have : c = 0 := by exact_mod_cast h
    rw [this, zero_mul] at hsum
    omega
  rw [prEvent_map, SampleableType.prEvent_uniformSample,
    SampleableType.prEvent_uniformSample_eq_singleton, hc, hsum]
  push_cast
  rw [← mul_one (c : ENNReal), mul_assoc, one_mul,
    ENNReal.mul_div_mul_left _ _ hc0 (ENNReal.natCast_ne_top c), one_div]

/-- The fibers of an affine map over a surjective homomorphism all have the size of its kernel. -/
theorem card_fiber_affine {G H : Type} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    [DecidableEq G] [DecidableEq H] (φ : G →+ H) (hs : Function.Surjective φ) (e b : H) :
    (Finset.univ.filter fun x => e + φ x = b).card = (Finset.univ.filter fun x => φ x = 0).card := by
  obtain ⟨x₀, hx₀⟩ := hs (b - e)
  refine Finset.card_bij (fun x _ => x - x₀) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [map_sub, hx₀, ← hx.2]
    abel
  · intro x _ y _ h
    exact sub_left_injective h
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine ⟨y + x₀, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [map_add, hy.2, hx₀]
    abel

end Fibers

section Base

variable [Fintype K] [DecidableEq K] [SampleableType K]

/-- In the small field, the masked value is the small field's. -/
theorem maskedValue_algebraMap (e u ρ : K) (m : Fin 3 → K) :
    maskedValue (algebraMap K E e) (algebraMap K E u) (algebraMap K E ρ) m
      = algebraMap K E (e + u * ∑ i, m i * ρ ^ (i : ℕ)) := by
  simp [maskedValue, Algebra.smul_def]

/-- **Zero knowledge at a row of the small field.** The four values are exactly uniform in
`K^4`, whatever the witness's values. -/
theorem baseValues_uniform (e : Fin 4 → K) {u : K} (hu : u ≠ 0) (ρ : K) (a : Fin 4 → K) :
    Pr{let x ← (fun (m : Fin 4 → Fin 3 → K) (j : Fin 4) => e j + u * ∑ i, m j i * ρ ^ (i : ℕ)) <$>
        ($ᵗ (Fin 4 → Fin 3 → K))}[x = a] = Pr{let x ← $ᵗ (Fin 4 → K)}[x = a] := by
  let φ : (Fin 4 → Fin 3 → K) →+ (Fin 4 → K) :=
    AddMonoidHom.mk' (fun m j => u * ∑ i, m j i * ρ ^ (i : ℕ)) (by
      intro m m'
      funext j
      simp [add_mul, Finset.sum_add_distrib, mul_add])
  have hs : Function.Surjective φ := by
    intro b
    refine ⟨fun j i => if i = 0 then b j / u else 0, ?_⟩
    funext j
    simp [φ, Fin.sum_univ_three, mul_div_cancel₀ _ hu]
  exact probOutput_map_uniform_of_fibers (fun m => e + φ m) _ (card_fiber_affine φ hs e) a

end Base

/-! ## The simulator of the four values -/

section Simulator

variable [Fintype K] [DecidableEq K] [SampleableType K] [Fintype E] [SampleableType E]
  [FiniteDimensional K E]

open Classical in
/-- The simulator of the four values: uniform in `E`, or in `K` when the row is in `K`. It reads
the row, which the challenge determines, and nothing of the witness. -/
noncomputable def simValues (r : E) : ProbComp (Fin 4 → E) :=
  if r ∈ Set.range (algebraMap K E) then
    (fun (a : Fin 4 → K) (j : Fin 4) => algebraMap K E (a j)) <$> ($ᵗ (Fin 4 → K))
  else $ᵗ (Fin 4 → E)

/-- **The four values are simulated**, at every row where the vanishing polynomial is not zero:
committed polynomials `g_j + van * mask_j` over `K` with uniform masks, opened at `r`. -/
theorem realValues_eq_simValues (h3 : finrank K E = 3) (gK : Fin 4 → K[X]) (van : K[X]) (r : E)
    (hu : aeval r van ≠ 0) (a : Fin 4 → E) :
    Pr{let x ← realValues (K := K) (fun j => aeval r (gK j)) (aeval r van) r}[x = a]
      = Pr{let x ← simValues (K := K) r}[x = a] := by
  classical
  unfold simValues
  split_ifs with hr
  · obtain ⟨ρ, rfl⟩ := hr
    have hu0 : van.eval ρ ≠ 0 := by
      intro h0
      apply hu
      rw [aeval_algebraMap_apply_eq_algebraMap_eval, h0, map_zero]
    have hreal : realValues (K := K) (fun j => aeval (algebraMap K E ρ) (gK j))
          (aeval (algebraMap K E ρ) van) (algebraMap K E ρ)
        = (fun (b : Fin 4 → K) (j : Fin 4) => algebraMap K E (b j)) <$>
          ((fun (m : Fin 4 → Fin 3 → K) (j : Fin 4) =>
            (gK j).eval ρ + van.eval ρ * ∑ i, m j i * ρ ^ (i : ℕ)) <$>
              ($ᵗ (Fin 4 → Fin 3 → K))) := by
      unfold realValues
      rw [Functor.map_map]
      congr 1
      funext m j
      simp only [aeval_algebraMap_apply_eq_algebraMap_eval, maskedValue_algebraMap,
        Function.comp_apply]
    rw [hreal]
    exact ((evalDistEq_iff_forall_prEvent_eq_output.mpr
      (baseValues_uniform (fun j => (gK j).eval ρ) hu0 ρ)).map _).prEvent_eq (· = a)
  · exact realValues_uniform h3 _ hu hr a

end Simulator

end QuotientSecurity
