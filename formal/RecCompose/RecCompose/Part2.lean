-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Basic

/-!
# Part 1 ⇒ Part 2, knowledge soundness: `RecKnowledgeSoundness D ε2 ε1 εh` from `RecKnowledgeSoundness2 D ε2`

The end-to-end experiment (`recSoundnessExperiment`) is π2's (`recSoundnessExperiment2`) without the calls
(`recSoundnessExperiment_eq`). When the contract accepts and the end-to-end extractor (π2's, then π1-rec3's
`uniExtractor`) finds no stack satisfying `M3Holds`, one of three events holds of π2's outcome:

1. **π2's**: π2's extractor outputs no π1 stream accepted with the contract's π1 openings (`RecBreaksKnowledgeSoundness2`,
   at most `ε2 Q` by Part 1);
2. **the hazard**: it outputs a stream on which π1-rec3's run at Keccak-f[1600] hits the merge hazard (at most the
   hazard experiment's probability for the derived adversary `hazardAdversary A`, `HazardCoupling`; at most `εh Q` by
   `Pi1HazardKeccak`);
3. **π1-rec3's at Keccak-f[1600]**: it outputs an accepted stream off the hazard, and π1-rec3's own extractor finds no
   stack (at most the π1 experiment's probability for the derived adversary `pi1Adversary A` that π1-rec3 is broken,
   `Pi1Coupling`, which reads the graph as π1-rec3's verifier off the hazard, `Pi1GraphIsVerifier`; at most `ε1 Q` by
   `Pi1FsKeccak`).

The derived adversaries run π2's adversary, its queries logged, then π2's extractor on its transcript and the setup's
evaluations (which the statement's fix gives them): their queries are π2's adversary's, `Q` of them.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## The derived adversaries -/

/-- **The hazard's adversary built from π2's**: it runs `A` (its queries logged), then outputs the public input and the
stream π2's extractor outputs (none: the empty stream). -/
def hazardAdversary (D : RecDeployment) (A : RecAdversary) : Pi1StreamAdversary :=
  fun roots evals ↦ do
    let (z, T) ← (simulateQ loggedOracles (A roots)).run []
    return (z.1, (recExtractor2 D roots z.1 evals T z.2).getD #[])

/-- **π1-rec3's adversary built from π2's**: it runs `A` (its queries logged), then outputs the public input and π1's
proof of the stream π2's extractor outputs, with the recursive proof's three π1 opening proofs. -/
def pi1Adversary (D : RecDeployment) (A : RecAdversary) : Pi1Adversary :=
  fun roots evals ↦ do
    let (z, T) ← (simulateQ loggedOracles (A roots)).run []
    return (z.1, z.2.pi1Proof ((recExtractor2 D roots z.1 evals T z.2).getD #[]))

/-! ## The three events -/

/-- The end-to-end outcome of π2's. -/
abbrev toOutcome (z : RecOutcome2) : RecOutcome := (z.1, z.2.1, z.2.2.1, z.2.2.2.1)

/-- **The hazard event**: π2's extractor outputs a stream on which π1-rec3's run at Keccak-f[1600] hits the merge
hazard. -/
def HazardEvent (D : RecDeployment) (z : RecOutcome2) : Prop :=
  ∃ s, recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z) = some s ∧
    RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 (D.pi1IvAt (rts z).pi1) (inp z).toList s

/-- **π1-rec3's event**: the contract accepts, π2's extractor outputs a stream accepted with the contract's π1 openings,
off the hazard, and π1-rec3's own extractor (on that stream, the proof's π1 openings, the setup's evaluations and the
transcript) finds no stack satisfying `M3Holds`. -/
def Pi1Event (D : RecDeployment) (z : RecOutcome2) : Prop :=
  (acc z) = true ∧ ∃ s ops, recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z) = some s ∧
    contractPi1Openings (registryAt D (rts z)) (cls z) = some ops ∧
    Pi1GraphAccepts (D.pi1IvAt (rts z).pi1) (inp z) s ops ∧
    ¬ RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 (D.pi1IvAt (rts z).pi1) (inp z).toList s ∧
    ¬ ∃ q, UniStatement.uniExtractor D.pi1 (inp z) (evs z) (lg z) ((prf z).pi1Proof s) = some q ∧
      D.pi1.Relation ((prf z).pi1Proof s).rows (inp z) q

/-! ## The couplings (named; proved in `Couplings.lean`) -/

/-- **The end-to-end experiment is π2's, the calls dropped.** -/
def ExperimentsAgree (D : RecDeployment) : Prop :=
  ∀ A : RecAdversary, recSoundnessExperiment D A = toOutcome <$> recSoundnessExperiment2 D A

/-- **The hazard coupling**: the derived adversary makes `A`'s queries, and π2's hazard event is at most the hazard
experiment's for it. -/
def HazardCoupling (D : RecDeployment) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    (∀ roots evals, QueryCostAtMost (hazardAdversary D A roots evals) permutationCallCost Q) ∧
    Pr{let z ← recSoundnessExperiment2 D A}[HazardEvent D z] ≤
      Pr{let z ← pi1HazardExperiment D (hazardAdversary D A)}[
        RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 z.1 z.2.1.toList z.2.2]

/-- **π1-rec3's coupling**, the graph being π1-rec3's verifier off the hazard: the derived adversary makes `A`'s
queries, and π2's π1 event is at most the probability that it breaks π1-rec3 at Keccak-f[1600]. -/
def Pi1Coupling (D : RecDeployment) : Prop :=
  RecGraph.Pi1.Pi1GraphIsVerifier →
    ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
      (∀ roots evals, QueryCostAtMost (pi1Adversary D A roots evals) permutationCallCost Q) ∧
      Pr{let z ← recSoundnessExperiment2 D A}[Pi1Event D z] ≤
        Pr{let z ← pi1KeccakSoundnessExperiment D (pi1Adversary D A)}[
          UniStatement.UniBreaksKnowledgeSoundness D.pi1 (UniStatement.uniExtractor D.pi1) z]

/-! ## The implication -/

/-- **On π2's outcome, an end-to-end break is π2's, the hazard's or π1-rec3's.** -/
theorem breaks_cases (D : RecDeployment) (z : RecOutcome2)
    (h : RecBreaksKnowledgeSoundness D (recExtractor D) (toOutcome z)) :
    RecBreaksKnowledgeSoundness2 D (recExtractor2 D) z ∨ HazardEvent D z ∨ Pi1Event D z := by
  obtain ⟨hacc, hno⟩ := h
  change (acc z) = true at hacc
  change ¬ ∃ w, recExtractor D (rts z) (inp z) (evs z) (lg z) (prf z) = some w ∧
    D.pi1.Relation w.1 (inp z) w.2 at hno
  rcases Classical.em (RecBreaksKnowledgeSoundness2 D (recExtractor2 D) z) with h2 | h2
  · exact Or.inl h2
  refine Or.inr ?_
  have hex : ∃ s ops, recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z) = some s ∧
      contractPi1Openings (registryAt D (rts z)) (cls z) = some ops ∧
      Pi1GraphAccepts (D.pi1IvAt (rts z).pi1) (inp z) s ops :=
    Classical.byContradiction fun hc ↦ h2 ⟨hacc, hc⟩
  obtain ⟨s, ops, hs, hops, hga⟩ := hex
  rcases Classical.em (RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 (D.pi1IvAt (rts z).pi1) (inp z).toList s)
    with hz | hz
  · exact Or.inl ⟨s, hs, hz⟩
  refine Or.inr ⟨hacc, s, ops, hs, hops, hga, hz, ?_⟩
  rintro ⟨q, hq, hrel⟩
  refine hno ⟨⟨((prf z).pi1Proof s).rows, q⟩, ?_, hrel⟩
  have e : recExtractor D (rts z) (inp z) (evs z) (lg z) (prf z) =
      (recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z)).bind (fun s ↦
        (UniStatement.uniExtractor D.pi1 (inp z) (evs z) (lg z) ((prf z).pi1Proof s)).map fun q ↦ ⟨_, q⟩) := rfl
  rw [e, hs, Option.bind_some, hq, Option.map_some]

/-- **Part 1 ⇒ Part 2 (knowledge soundness)**: from π2's part `RecKnowledgeSoundness2 D ε2` and the couplings, the
end-to-end statement `RecKnowledgeSoundness D ε2 ε1 εh`, for every `ε1`, `εh`. -/
theorem recKnowledgeSoundness_of_part1 {D : RecDeployment} {ε2 : ℕ → ℝ≥0∞} (h2 : RecKnowledgeSoundness2 D ε2)
    (hE : ExperimentsAgree D) (hH : HazardCoupling D) (hP : Pi1Coupling D) (ε1 εh : ℕ → ℝ≥0∞) :
    RecKnowledgeSoundness D ε2 ε1 εh := by
  intro hgv h1 hh A Q hQ
  rw [hE A, prEvent_map]
  obtain ⟨hHq, hHle⟩ := hH A Q hQ
  obtain ⟨hPq, hPle⟩ := hP hgv A Q hQ
  calc Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness D (recExtractor D) (toOutcome z)]
      ≤ Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness2 D (recExtractor2 D) z ∨
          (HazardEvent D z ∨ Pi1Event D z)] :=
        prEvent_mono _ _ _ fun z hz ↦ breaks_cases D z hz
    _ ≤ Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness2 D (recExtractor2 D) z] +
          (Pr{let z ← recSoundnessExperiment2 D A}[HazardEvent D z] +
            Pr{let z ← recSoundnessExperiment2 D A}[Pi1Event D z]) :=
        (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_or_le _ _ _))
    _ ≤ ε2 Q + (εh Q + ε1 Q) :=
        add_le_add (h2 A Q hQ) (add_le_add (hHle.trans (hh _ Q hHq)) (hPle.trans (h1 _ Q hPq)))
    _ = ε2 Q + ε1 Q + εh Q := by ring

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness_of_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_of_part1
