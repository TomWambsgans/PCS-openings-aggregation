-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Basic

/-!
# Part 1 ⇒ Part 2, completeness: `RecCompleteness D P1 P2 δ1 δh δ2` from `RecCompleteness2 D P1 P2 δ2`

The recursive prover is π1-rec3's then π2's (`composeProver`). Its proof is rejected only if

* π1-rec3's proof is not accepted by π1-rec3's graph with its openings (`pi1GraphVerifierWith`, `v.1` of π2's
  completeness experiment): off the merge hazard the graph is π1-rec3's verifier (`Pi1GraphIsVerifier`), so this is at
  most π1-rec3's rejection at Keccak-f[1600] (`Pi1CompletenessKeccak`, `δ1`) plus the hazard on its honest proofs
  (`Pi1HazardKeccakHonest`, `δh`): `CompletenessPi1Coupling`;
* or it is, and π2's proof of it is rejected (`RecCompleteness2`, `δ2`).

The end-to-end experiment's verdict is π2's experiment's second (`CompletenessAgree`: π2's experiment runs the graph's
check in between, which in the random-permutation model changes nothing of the rest).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-- **The end-to-end completeness experiment's verdict is π2's experiment's second**: inserting π1-rec3's graph's check
(`pi1GraphVerifierWith`, its answer unused by the rest) between π1-rec3's prover and π2's changes nothing of the rest. -/
def CompletenessAgree (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows),
    Pr{let v ← recCompletenessExperiment D (composeProver D P1 P2) input rows q}[v = false] =
      Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.2 = false]

/-- **π1-rec3's completeness coupling**, the graph being π1-rec3's verifier off the hazard: π1-rec3's proof is rejected
by its graph with its openings at most as often as by π1-rec3's verifier at Keccak-f[1600], plus the hazard. -/
def CompletenessPi1Coupling (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) : Prop :=
  RecGraph.Pi1.Pi1GraphIsVerifier →
    ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows),
      Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = false] ≤
        Pr{let v ← pi1KeccakCompletenessExperiment D P1 input rows q}[v = false] +
          Pr{let z ← pi1HonestHazardExperiment D P1 input rows q}[
            ∃ iv s, z = some (iv, s) ∧ RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 iv input.toList s]

/-- **Part 1 ⇒ Part 2 (completeness)**: from π2's completeness `RecCompleteness2 D P1 P2 δ2` and the couplings, the
end-to-end statement `RecCompleteness D P1 P2 δ1 δh δ2`, for every `δ1`, `δh`. -/
theorem recCompleteness_of_part1 {D : RecDeployment} {P1 : Pi1Prover D} {P2 : Pi2Prover} {δ2 : ℝ≥0∞}
    (h2 : RecCompleteness2 D P1 P2 δ2) (hA : CompletenessAgree D P1 P2) (hC : CompletenessPi1Coupling D P1 P2)
    (δ1 δh : ℝ≥0∞) : RecCompleteness D P1 P2 δ1 δh δ2 := by
  intro hgv h1 hh input rows q hfit hhon
  rw [hA input rows q]
  calc Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.2 = false]
      ≤ Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = false ∨ (v.1 = true ∧ v.2 = false)] :=
        prEvent_mono _ _ _ fun v hv ↦ by
          cases h : v.1
          · exact Or.inl rfl
          · exact Or.inr ⟨rfl, hv⟩
    _ ≤ Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = false] +
          Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = true ∧ v.2 = false] :=
        prEvent_or_le _ _ _
    _ ≤ (δ1 + δh) + δ2 :=
        add_le_add ((hC hgv input rows q).trans (add_le_add (h1 input rows q hfit hhon) (hh input rows q hfit hhon)))
          (h2 input rows q hfit hhon)

end RecCompose

/-- info: 'RecCompose.recCompleteness_of_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recCompleteness_of_part1
