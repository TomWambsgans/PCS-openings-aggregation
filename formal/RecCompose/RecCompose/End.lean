-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Part1
import RecCompose.Part2
import RecCompose.Complete
import RecCompose.Numbers
import RecCompose.Layers
import RecCompose.Circuit
import RecCompose.CallsPure

/-!
# The end theorems

* **`recKnowledgeSoundness2_real`** (π2's part, in the random-permutation model): at a real deployment, with π2's layers
  and the calldata's π1 openings, `RecKnowledgeSoundness2 D pi2Bound`, and `pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64`
  (`2^-64.93` at `2^64`: 128.93 bits as `Q / ε2`).
* **`recKnowledgeSoundness_end`** (end to end, against Lv42's `M3Holds`): `RecKnowledgeSoundness D pi2Bound ε1 εh` for
  every `ε1`, `εh` (the Props' own hypotheses: `Pi1GraphIsVerifier`, `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh`), from Part 1
  and the couplings.
* **`recCompleteness_end`**: `RecCompleteness D P1 P2 δ1 δh δ2` for every `δ1`, `δh` (the Props' own hypotheses:
  `Pi1GraphIsVerifier`, `Pi1CompletenessKeccak δ1`, `Pi1HazardKeccakHonest δh`), from π2's completeness
  `RecCompleteness2 D P1 P2 δ2` (π2's honest prover is not transcribed: a named hypothesis) and the couplings.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol
open scoped ENNReal

variable {D : RecDeployment}

/-- **The circuit's corollary from RecCircuit's end theorem**: the compiled circuits' roots at the emitted graph's,
the Lean recording the emitted graph (`GraphsAgree`, a run), and the bridge (`CircuitBridge`, open). -/
theorem pi2CircuitAccepts_of_bridge (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hb : CircuitBridge D C.compiled fun roots input stream ↦ Fa.pubOf roots (pi2Scalars D roots input stream)) :
    Pi2CircuitAccepts C Fa := by
  have hc : ∀ iv, RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) =
      .ok (C.compiled iv) := by
    intro iv
    have h := C.compile_ok iv
    unfold GraphsAgree at hg
    rw [hroots, hg] at h
    exact h
  exact circuit_of_bridge hc hb

/-- **π2's part at the real deployment, `ε2 = pi2Bound`**: if the contract accepts, π2's extractor outputs π1's stream
on which π1-rec3's recorded graph run with Keccak-f[1600] accepts, its three calls the contract's, but with
probability `pi2Bound Q`, at most `2^-64` for `Q ≤ 2^64`. From π2's layers (`Pi2Layers`, built by `pi2Layers_of`). -/
theorem recKnowledgeSoundness2_of_real (D : RecDeployment) (_hD : D.Real) (L : Pi2Layers D pi2Bound) :
    RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  ⟨recKnowledgeSoundness2_of_layers L (callsPure D), pi2Bound_le_bits⟩

/-- **π2's part at the real deployment, from its named inputs**: the compiled circuit (`C`: the Lean compiler's run on
π1-rec3's graph at every π1 IV, at the emitted graph's roots; `hg`, the graphs agree, a run), its facts (`Fa`: `SpecOf`,
validity, the shape, the ports), the tables' layer (`T`, open), π2's Fiat–Shamir layer (`hfs`, open), the bridge from
RecCircuit's end theorem (`hb`, open); the calldata's π1 openings are the contract's (`callsPure`, proved):
`RecKnowledgeSoundness2 D pi2Bound`,
`pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64`. -/
theorem recKnowledgeSoundness2_real (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (T : Pi2Tables D C) (hfs : Pi2FsLayer D) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hb : CircuitBridge D C.compiled fun roots input stream ↦ Fa.pubOf roots (pi2Scalars D roots input stream)) :
    RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  recKnowledgeSoundness2_of_real D hD (pi2Layers_of C Fa T hfs (pi2CircuitAccepts_of_bridge C Fa hroots hg hb))

/-- **The recursive verifier is knowledge sound end to end**, against leanVM 42422001's relation, at the real
deployment: `RecKnowledgeSoundness D pi2Bound ε1 εh` for every `ε1`, `εh`, i.e. under `Pi1GraphIsVerifier`,
`Pi1FsKeccak ε1` and `Pi1HazardKeccak εh`, error `pi2Bound Q + ε1 Q + εh Q`. -/
theorem recKnowledgeSoundness_end (D : RecDeployment) (hD : D.Real) (L : Pi2Layers D pi2Bound)
    (hE : ExperimentsAgree D) (hH : HazardCoupling D) (hP : Pi1Coupling D)
    (ε1 εh : ℕ → ℝ≥0∞) : RecKnowledgeSoundness D pi2Bound ε1 εh :=
  recKnowledgeSoundness_of_part1 (recKnowledgeSoundness2_of_real D hD L).1 hE hH hP ε1 εh

/-- **The recursive verifier is complete end to end**, for π1-rec3's prover then π2's: `RecCompleteness D P1 P2 δ1 δh
δ2` for every `δ1`, `δh`, i.e. under `Pi1GraphIsVerifier`, `Pi1CompletenessKeccak δ1` and `Pi1HazardKeccakHonest δh`,
error `δ1 + δh + δ2`. -/
theorem recCompleteness_end (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ2 : ℝ≥0∞)
    (h2 : RecCompleteness2 D P1 P2 δ2) (hA : CompletenessAgree D P1 P2) (hC : CompletenessPi1Coupling D P1 P2)
    (δ1 δh : ℝ≥0∞) : RecCompleteness D P1 P2 δ1 δh δ2 :=
  recCompleteness_of_part1 h2 hA hC δ1 δh

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness2_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_of_real

/-- info: 'RecCompose.recKnowledgeSoundness2_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_real

/-- info: 'RecCompose.recKnowledgeSoundness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_end

/-- info: 'RecCompose.recCompleteness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recCompleteness_end
