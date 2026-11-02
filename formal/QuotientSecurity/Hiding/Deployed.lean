-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.GadgetTheorem
import QuotientSecurity.Hiding.DeployedWeights

/-!
# Hiding of the deployed openings

`GadgetLayout.prEvent_le_bound` (`GadgetTheorem.lean`) instantiated with the deployed layouts
(`DeployedLayout.lean`: the witness and quotient tables' `Layout::hidden_with` at `2^17 .. 2^22` rows),
the deployed claims' weights (`DeployedWeights.lean`: `opening::verify`'s weight closure on the
Boolean cube, which fits the layout) and the deployed code (`NovelBasis.lean`: WHIR's novel basis at
the positions a level-0 opening reads, at most `225 < D = 247`).

**`Layout.prEvent_le`**: for a layout the model covers, any opened positions `S` (`|S| ≤ 225`, in the
level-0 domain `[0, 2^(ℓ+1))`), any claims (points, `m` of them) and any basis `β` of `E` over `K`
(the gadget's), with `λ` uniform in `E` (the claims' powers `λ^c` and the gadget's `λ^m`, the powers
`opening::verify` builds: `powers_snoc`) and `φ` uniform in `E^6`, two tables whose stacks give the
claims (the gadget's included) the same values have experiments (challenges, then anything computed
from the opening's view up to the first fold) that differ on any event by at most

  `1/|E| + (12·|E| + 3·|K|²)/|E|²`

(`< 2^-188` at `|K| = 2^64`, `|E| = 2^192`). **`deployed_prEvent_le`**: the same for the witness and the
quotient table at every supported size; `queries_card_le`: the positions WHIR's level 0 samples
(`whirQueries0 log_n` of them) qualify.
-/

namespace QuotientSecurity.Hiding

open Finset OracleComp

set_option linter.unusedSectionVars false

namespace Deployed

variable {K E : Type} [Field K] [Field E] [Algebra K E]

/-- `Pr[λ^m = 0] ≤ 1/|E|` for `λ` uniform. -/
theorem prob_pow_eq_zero_le [Fintype E] [DecidableEq E] [SampleableType E] (m : ℕ) :
    Pr{let c ← $ᵗ (E × (Fin 6 → E))}[c.1 ^ m = 0] ≤ 1 / (Fintype.card E : ENNReal) := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hsub : (univ.filter fun c : E × (Fin 6 → E) => c.1 ^ m = 0) ⊆
      ({0} : Finset E) ×ˢ (univ : Finset (Fin 6 → E)) := by
    intro c hc
    have := (mem_filter.mp hc).2
    refine mem_product.mpr ⟨mem_singleton.mpr (eq_zero_of_pow_eq_zero this), mem_univ _⟩
  have hle := card_le_card hsub
  rw [card_product, card_singleton, one_mul, card_univ] at hle
  have hE : 0 < Fintype.card E := Fintype.card_pos
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  have hcast : (1 : ENNReal) / (Fintype.card E : ENNReal) = ((1 : ℕ) : ENNReal) / (Fintype.card E : ℕ) := by
    simp
  rw [hcast]
  refine HiddenLayout.natCast_div_le_natCast_div (Nat.mul_pos hE (Nat.pow_pos hE)) hE ?_
  calc (univ.filter fun c : E × (Fin 6 → E) => c.1 ^ m = 0).card * Fintype.card E
      ≤ Fintype.card E ^ 6 * Fintype.card E := Nat.mul_le_mul_right _ (by
        simpa [Fintype.card_fun] using hle)
    _ = 1 * (Fintype.card E * Fintype.card E ^ 6) := by ring

/-- WHIR's level-0 positions (`sample_queries`, `whirQueries0 log_n` of them) are at most `225`
distinct positions of the level-0 domain. -/
theorem queries_card_le {logN : ℕ} (qs : Fin (whirQueries0 logN) → Fin (2 ^ (logN - 6 + 1))) :
    (univ.image fun i => (qs i : ℕ)).card ≤ 225 ∧
      ∀ q ∈ univ.image (fun i => (qs i : ℕ)), q < 2 ^ (logN - 6 + 1) := by
  refine ⟨card_image_le.trans ((card_univ.trans (Fintype.card_fin _)).le.trans
    (whirQueries0_le logN)), fun q hq => ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.mp hq
  exact (qs i).isLt

namespace Layout

variable {L : Layout}

/-- **Hiding of a deployed opening.** A layout the model covers (`L.OK`), opened at positions `S`
(`|S| ≤ 225`) of its level-0 domain, with claims at `points` and the gadget's basis `β`; challenges
`λ` (the claims' powers `λ^c`, the gadget's `λ^m`) and `φ` uniform. Two tables `d`, `d'` whose stacks
give every claim and the gadget the same values: the experiments differ on any event by at most
`1/|E| + (12|E| + 3|K|²)/|E|²`. -/
theorem prEvent_le [CharP K 2] [FiniteDimensional K E] [Fintype K] [Fintype E] [DecidableEq E]
    [SampleableType E] (h3 : Module.finrank K E = 3) (w : Words K) (h : L.OK)
    [SampleableType (Fin L.lanes.length → Fin (2 ^ L.logLane) → K)]
    (S : Finset ℕ) (hS : ∀ q ∈ S, q < 2 ^ (L.logLane + 1)) (hcard : S.card ≤ 225)
    {m : ℕ} (points : Fin m → List E) (β : Module.Basis (Fin 3) K E) {O : Type}
    (g : E × (Fin 6 → E) → (Fin 6 → E × E) × (Fin (2 ^ L.logLane) → E) ×
      (S → Fin L.lanes.length → K) → O)
    {d d' : Fin L.lanes.length → Fin (2 ^ L.logLane) → K}
    (hd : HiddenLayout.claimsMap (K := K)
        (GadgetLayout.withGadget (L.claimW points) ((L.toGadget h).gadgetW L.pos β))
        ((L.toGadget h).stackD d) =
      HiddenLayout.claimsMap (GadgetLayout.withGadget (L.claimW points)
        ((L.toGadget h).gadgetW L.pos β)) ((L.toGadget h).stackD d'))
    (Ev : (E × (Fin 6 → E)) × O → Prop) :
    let run := fun (x : Fin L.lanes.length → Fin (2 ^ L.logLane) → K) (c : E × (Fin 6 → E)) =>
      (fun r => g c (viewMap (roundsMap L.pos c.2 (HiddenLayout.combinedW L.pos
          (GadgetLayout.withGadget (L.claimW points) ((L.toGadget h).gadgetW L.pos β))
          (Fin.snoc (fun k : Fin m => c.1 ^ (k : ℕ)) (c.1 ^ m) : Fin (m + 1) → E)))
        (HiddenLayout.foldW L.pos c.2) (novelEnc w L.logLane (Subtype.val : S → ℕ))
        ((L.toGadget h).stackD x + (L.toGadget h).stackR r))) <$>
        ($ᵗ (Fin L.lanes.length → Fin (2 ^ L.logLane) → K))
    Pr{let o ← withChallenges (run d)}[Ev o]
      ≤ Pr{let o ← withChallenges (run d')}[Ev o]
        + (1 / (Fintype.card E : ENNReal) +
          ((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
            ((Fintype.card E ^ 2 : ℕ) : ENNReal)) := by
  intro run
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2E : (2 : E) = 0 := by
    have := congrArg (algebraMap K E) h2K
    rwa [map_ofNat, map_zero] at this
  have hl8 : 8 ≤ L.logLane := by have := h.lane; simp only [logPieceD] at this; omega
  have hl64 : L.logLane + 1 ≤ 64 := by
    have := h.logN_le
    simp only [Layout.logLane, laneFold]
    omega
  have hQ := novel_firstEval_surjective w hl8 hl64 (Subtype.val : S → ℕ) (fun x => hS x.1 x.2)
    Subtype.val_injective (by rw [Fintype.card_coe]; exact hcard.trans (by decide))
  refine ((L.toGadget h).prEvent_le_bound h3 h2K L.pos (pos_injective h) (L.claimW points)
    (weightsFit h2E h points) β (novelEnc w L.logLane (Subtype.val : S → ℕ)) hQ (pairA_not_rand h)
    (pos_pairA0 h) (pos_pairB0 h) (pos_pairA1 h) (pos_pairB1 h) (pos_ov h) (pos_low h)
    (pos_cube h) (pos_rand h) (fun c k => c ^ (k : ℕ)) (fun c => c ^ m) g hd Ev).trans ?_
  exact add_le_add le_rfl (add_le_add (prob_pow_eq_zero_le m) le_rfl)

end Layout

/-- **Hiding of the deployed witness and quotient openings**, at every supported size
`17 ≤ r ≤ 22`: `Layout.prEvent_le` at `witnessLayout r` and `quotientLayout r`. -/
theorem deployed_prEvent_le [CharP K 2] [FiniteDimensional K E] [Fintype K] [Fintype E]
    [DecidableEq E] [SampleableType E] (h3 : Module.finrank K E = 3) (w : Words K) (r : ℕ)
    (hr1 : 17 ≤ r) (hr2 : r ≤ 22) (L : Layout) (hL : L = witnessLayout r ∨ L = quotientLayout r)
    [SampleableType (Fin L.lanes.length → Fin (2 ^ L.logLane) → K)]
    (S : Finset ℕ) (hS : ∀ q ∈ S, q < 2 ^ (L.logLane + 1)) (hcard : S.card ≤ 225)
    {m : ℕ} (points : Fin m → List E) (β : Module.Basis (Fin 3) K E) {O : Type}
    (g : E × (Fin 6 → E) → (Fin 6 → E × E) × (Fin (2 ^ L.logLane) → E) ×
      (S → Fin L.lanes.length → K) → O)
    {d d' : Fin L.lanes.length → Fin (2 ^ L.logLane) → K}
    (hd : let h : L.OK := by
            rcases hL with rfl | rfl
            exacts [(deployed_ok r hr1 hr2).1, (deployed_ok r hr1 hr2).2]
          HiddenLayout.claimsMap (K := K)
            (GadgetLayout.withGadget (L.claimW points) ((L.toGadget h).gadgetW L.pos β))
            ((L.toGadget h).stackD d) =
          HiddenLayout.claimsMap (GadgetLayout.withGadget (L.claimW points)
            ((L.toGadget h).gadgetW L.pos β)) ((L.toGadget h).stackD d'))
    (Ev : (E × (Fin 6 → E)) × O → Prop) :
    let h : L.OK := by
      rcases hL with rfl | rfl
      exacts [(deployed_ok r hr1 hr2).1, (deployed_ok r hr1 hr2).2]
    let run := fun (x : Fin L.lanes.length → Fin (2 ^ L.logLane) → K) (c : E × (Fin 6 → E)) =>
      (fun r => g c (viewMap (roundsMap L.pos c.2 (HiddenLayout.combinedW L.pos
          (GadgetLayout.withGadget (L.claimW points) ((L.toGadget h).gadgetW L.pos β))
          (Fin.snoc (fun k : Fin m => c.1 ^ (k : ℕ)) (c.1 ^ m) : Fin (m + 1) → E)))
        (HiddenLayout.foldW L.pos c.2) (novelEnc w L.logLane (Subtype.val : S → ℕ))
        ((L.toGadget h).stackD x + (L.toGadget h).stackR r))) <$>
        ($ᵗ (Fin L.lanes.length → Fin (2 ^ L.logLane) → K))
    Pr{let o ← withChallenges (run d)}[Ev o]
      ≤ Pr{let o ← withChallenges (run d')}[Ev o]
        + (1 / (Fintype.card E : ENNReal) +
          ((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
            ((Fintype.card E ^ 2 : ℕ) : ENNReal)) :=
  Layout.prEvent_le h3 w _ S hS hcard points β g hd Ev

end Deployed

end QuotientSecurity.Hiding
