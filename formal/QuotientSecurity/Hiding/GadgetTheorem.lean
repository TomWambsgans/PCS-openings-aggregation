-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.GadgetLayout
import QuotientSecurity.Hiding.Solve

/-!
# `HIDING.md`'s theorem for the hidden layouts with the gadget

For a `GadgetLayout` whose lanes are where the design puts them (the gadget's pairs at lane indices
`0, 31` and `1, 30`, the overflow lane at `32`, the random lanes at `33 .. 40`, the lower half and
lanes `32 .. 40` in the stack), the claims of the design (`WeightsFit`) and the gadget as one more
claim of value zero, batched by `μ`:

* `view_evalDistEq`: at every challenge `(μ, φ)` with `μ ≠ 0`, no coordinate of `φ` in `{0, 1}` and
  at most one of `φ₀, φ₁, φ₂` in `K`, given (Q), the opening's view up to the first fold of two tables
  with the same claims, and anything computed from it, are identically distributed. Conditions (S)
  and (R) are proven here (`Solve.span_cube_erase`, `GadgetLayout.roundsReached`), not assumed.
* `prEvent_le_bound`: averaged over uniform challenges, the two tables' experiments differ on any
  event by at most `Pr[μ = 0] + (12·|E| + 3·|K|²)/|E|²` (`12·2^-192 + 3·2^-256` for the deployed
  fields, plus `Pr[λ = 0]` for `μ = λ^m`).
-/

namespace QuotientSecurity.Hiding

open Finset OracleComp

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q]
  [DecidableEq Q]

namespace GadgetLayout

variable (L : GadgetLayout ι Y)

/-- **Condition (S) from the cube lemma**: the random lanes `33 .. 40` (the upper cube but the
overflow lane's corner) span `E` at every `φ` with no coordinate in `{0, 1}` and at most one of
`φ₀, φ₁, φ₂` in `K`. -/
theorem foldSpans_of_cube [FiniteDimensional K E] (h3 : Module.finrank K E = 3)
    (pos : ι → (Fin 6 → Bool))
    (hrand : ∀ b ∈ cube true, b ≠ lane 32 → ∃ r, pos r = b ∧ L.isRand r) (φ : Fin 6 → E)
    (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (hK : ¬ TwoInK (K := K) φ) : L.FoldSpans (K := K) pos φ := by
  classical
  set s := univ.filter fun b : Fin 6 → Bool => b ∈ cube true ∧ b ≠ lane 32
  have hs : ∀ j : Fin s.card, ∃ r, pos r = (s.equivFin.symm j : Fin 6 → Bool) ∧ L.isRand r := by
    intro j
    have hj := (mem_filter.mp (s.equivFin.symm j).2).2
    exact hrand _ hj.1 hj.2
  choose r hr using hs
  refine ⟨s.card, r, fun j => (hr j).2, ?_⟩
  refine eq_top_iff.mpr ((span_cube_erase h3 φ hφ hK).symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨b, hb, rfl⟩
  have hbs : b ∈ s := mem_filter.mpr ⟨mem_univ _, hb⟩
  refine ⟨s.equivFin ⟨b, hbs⟩, ?_⟩
  show eqW φ (pos (r _)) = eqW φ b
  rw [(hr _).1]
  simp

theorem gadgetW_first (pos : ι → (Fin 6 → Bool)) (β : Fin 3 → E) (l : ι) {y : Y}
    (hy : y ∈ L.first) : L.gadgetW pos β l y = 0 := by
  refine sum_eq_zero fun p _ => sum_eq_zero fun i _ => ?_
  have : L.gent p i ≠ y := fun h => L.gent_first p i (h ▸ hy)
  simp [this]

/-- **`HIDING.md`'s theorem for the gadget layouts**, at a good challenge: (Q) the only hypothesis on
the challenges' side; (S) and (R) hold. -/
theorem view_evalDistEq [FiniteDimensional K E] [SampleableType (ι → Y → K)]
    (h3 : Module.finrank K E = 3) {m : ℕ} (h2K : (2 : K) = 0) (pos : ι → (Fin 6 → Bool))
    (hpos : Function.Injective pos) (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc)
    (β : Module.Basis (Fin 3) K E) (enc : Q → Y → K) (hQ : Function.Surjective (firstEval enc L.first))
    (hA : ∀ p, ¬ L.isRand (L.pairA p))
    (hA0 : pos (L.pairA 0) = lane 0) (hB0 : pos (L.pairB 0) = lane 31)
    (hA1 : pos (L.pairA 1) = lane 1) (hB1 : pos (L.pairB 1) = lane 30) (hov : pos L.ov = lane 32)
    (hlow : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range pos)
    (hcube : ∀ l : Fin 64, 32 ≤ (l : ℕ) → (l : ℕ) < 40 → lane l ∈ Set.range pos)
    (hrand : ∀ b ∈ cube true, b ≠ lane 32 → ∃ r, pos r = b ∧ L.isRand r)
    (lam : Fin m → E) (μ : E) (hμ : μ ≠ 0) (φ : Fin 6 → E) (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1)
    (hK : ¬ TwoInK (K := K) φ) {O : Type}
    (g : (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → O) {d d' : ι → Y → K}
    (hd : HiddenLayout.claimsMap (K := K) (withGadget Wc (L.gadgetW pos β)) (L.stackD d)
      = HiddenLayout.claimsMap (withGadget Wc (L.gadgetW pos β)) (L.stackD d')) :
    (fun r => g (viewMap (roundsMap pos φ
        (HiddenLayout.combinedW pos (withGadget Wc (L.gadgetW pos β)) (Fin.snoc lam μ : Fin (m + 1) → E)))
        (HiddenLayout.foldW pos φ) enc (L.stackD d + L.stackR r))) <$> ($ᵗ (ι → Y → K))
      =ᵈ (fun r => g (viewMap (roundsMap pos φ
        (HiddenLayout.combinedW pos (withGadget Wc (L.gadgetW pos β)) (Fin.snoc lam μ : Fin (m + 1) → E)))
        (HiddenLayout.foldW pos φ) enc (L.stackD d' + L.stackR r))) <$> ($ᵗ (ι → Y → K)) := by
  set W := HiddenLayout.combinedW pos (withGadget Wc (L.gadgetW pos β)) (Fin.snoc lam μ : Fin (m + 1) → E)
  have hWfirst : ∀ b, ∀ y ∈ L.first, W b y = 0 := by
    intro b y hy
    simp only [W, HiddenLayout.combinedW]
    refine sum_eq_zero fun l _ => ?_
    split_ifs
    · rw [Fin.sum_univ_castSucc]
      simp [withGadget, hW.first _ _ _ hy, L.gadgetW_first pos β l hy]
    · rfl
  have h2E : (2 : E) = 0 := by rw [← map_ofNat (algebraMap K E) 2, h2K, map_zero]
  refine level0_view_evalDistEq (HiddenLayout.foldW pos φ) enc L.first (roundsMap pos φ W)
    (HiddenLayout.claimsMap (withGadget Wc (L.gadgetW pos β))) L.stackD L.stackR
    (LinearMap.ker (lastMap (K := K) φ)) (fun T hT => L.onFirst_mem_range T hT)
    (fun T hT => roundsMap_eq_zero pos φ W L.first hWfirst T hT)
    (L.claims_stackR h2K pos hpos hA0 hB0 hA1 hB1 hov Wc hW β) hQ
    (L.foldSpans_moves hA pos φ (L.foldSpans_of_cube h3 pos hrand φ hφ hK)) ?_ ?_ hd g
  · intro T hT hfold
    refine roundsMap_mem_ker pos φ W L.first hWfirst T ?_ hfold
    rw [HiddenLayout.ip_combinedW pos hpos, hT]
    simp
  · exact L.roundsReached h2K pos hpos (withGadget Wc (L.gadgetW pos β)) (Fin.snoc lam μ) φ μ hμ β
      (L.combinedW_gent pos hpos Wc hW β lam μ hA0 hB0 hA1 hB1 hov) hA0 hB0 hA1 hB1 hov hlow
      (hcube 33 (by decide) (by decide)) hφ (by simp [h2E])
      (hsolve_of_cube h3 φ hφ hK _ (cube_true_subset hcube) hlow)


/-- **Averaged over the challenges, with the bound.** With `μ` from any uniform `γ` (`μ = λ^m` in the
opening) and `φ` uniform in `E^6`, the two tables' experiments (challenges, then anything computed
from the view) give every event probabilities that differ by at most `Pr[μ = 0]` plus
`(12·|E| + 3·|K|²)/|E|²`: below `13·2^-192 + 3·2^-256` for the deployed fields and `μ = λ^m`. -/
theorem prEvent_le_bound [FiniteDimensional K E] [SampleableType (ι → Y → K)] [Fintype K] [Fintype E]
    [DecidableEq E] [SampleableType E] {Γ : Type} [SampleableType Γ] [Fintype Γ]
    (h3 : Module.finrank K E = 3) {m : ℕ} (h2K : (2 : K) = 0) (pos : ι → (Fin 6 → Bool))
    (hpos : Function.Injective pos) (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc)
    (β : Module.Basis (Fin 3) K E) (enc : Q → Y → K) (hQ : Function.Surjective (firstEval enc L.first))
    (hA : ∀ p, ¬ L.isRand (L.pairA p))
    (hA0 : pos (L.pairA 0) = lane 0) (hB0 : pos (L.pairB 0) = lane 31)
    (hA1 : pos (L.pairA 1) = lane 1) (hB1 : pos (L.pairB 1) = lane 30) (hov : pos L.ov = lane 32)
    (hlow : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range pos)
    (hcube : ∀ l : Fin 64, 32 ≤ (l : ℕ) → (l : ℕ) < 40 → lane l ∈ Set.range pos)
    (hrand : ∀ b ∈ cube true, b ≠ lane 32 → ∃ r, pos r = b ∧ L.isRand r)
    (lam : Γ → Fin m → E) (μ : Γ → E) {O : Type}
    (g : Γ × (Fin 6 → E) → (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → O) {d d' : ι → Y → K}
    (hd : HiddenLayout.claimsMap (K := K) (withGadget Wc (L.gadgetW pos β)) (L.stackD d)
      = HiddenLayout.claimsMap (withGadget Wc (L.gadgetW pos β)) (L.stackD d'))
    (S : (Γ × (Fin 6 → E)) × O → Prop) :
    let run := fun (x : ι → Y → K) (c : Γ × (Fin 6 → E)) =>
      (fun r => g c (viewMap (roundsMap pos c.2 (HiddenLayout.combinedW pos (withGadget Wc (L.gadgetW pos β))
          (Fin.snoc (lam c.1) (μ c.1) : Fin (m + 1) → E))) (HiddenLayout.foldW pos c.2) enc
          (L.stackD x + L.stackR r))) <$> ($ᵗ (ι → Y → K))
    Pr{let o ← withChallenges (run d)}[S o]
      ≤ Pr{let o ← withChallenges (run d')}[S o]
        + (Pr{let c ← $ᵗ (Γ × (Fin 6 → E))}[μ c.1 = 0]
          + ((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
              ((Fintype.card E ^ 2 : ℕ) : ENNReal)) := by
  intro run
  refine (prEvent_le_add_prEvent_bad (run d) (run d')
    (fun c => μ c.1 ≠ 0 ∧ ((∀ i, c.2 i ≠ 0 ∧ c.2 i ≠ 1) ∧ ¬ TwoInK (K := K) c.2))
    (fun c hc => L.view_evalDistEq h3 h2K pos hpos Wc hW β enc hQ hA hA0 hB0 hA1 hB1 hov hlow hcube
      hrand (lam c.1) (μ c.1) hc.1 c.2 hc.2.1 hc.2.2 (g c) hd) S).trans (add_le_add le_rfl ?_)
  calc Pr{let c ← $ᵗ (Γ × (Fin 6 → E))}[¬ (μ c.1 ≠ 0 ∧ ((∀ i, c.2 i ≠ 0 ∧ c.2 i ≠ 1) ∧
          ¬ TwoInK (K := K) c.2))]
      ≤ Pr{let c ← $ᵗ (Γ × (Fin 6 → E))}[μ c.1 = 0]
        + Pr{let c ← $ᵗ (Γ × (Fin 6 → E))}[¬ ((∀ i, c.2 i ≠ 0 ∧ c.2 i ≠ 1) ∧ ¬ TwoInK (K := K) c.2)] := by
        refine (prEvent_mono _ _ _ fun c h => ?_).trans (prEvent_or_le _ _ _)
        by_cases hμ : μ c.1 = 0
        · exact Or.inl hμ
        · exact Or.inr fun h' => h ⟨hμ, h'⟩
    _ ≤ _ := add_le_add le_rfl (prob_not_solvable_le (K := K) (Γ := Γ))

end GadgetLayout

end QuotientSecurity.Hiding
