-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at π1-rec3's honest prover, every provable named input closed.
import RecCompose.Pi2SimEnd
import RecCompose.Pi2Witness

/-!
# π2's completeness, closed

`Pi2SimEnd`'s end theorems with the compiled circuit's completeness proved (`Pi2W.pi2WitnessComplete`, from the
compiler's completeness checks): **`recCompleteness2_pi2_rec3_final`**, **`recCompleteness_pi2_rec3_final_fs`**. The
inputs left: the run-checked `Pi2Circuits D`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C`; `Pi2AlphaFresh εα` (`α`'s
input not hashed before its query but with probability `εα`, the named form of the false `Pi2HashBeforeAlpha`); and
for the end-to-end form the Fiat–Shamir-heuristic premises `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open Pi2S Pi2K Pi2P Pi2E Pi2G
open scoped ENNReal

/-- **π2's completeness at π1-rec3's honest prover**: from the run-checked inputs and `α`'s freshness only. -/
theorem recCompleteness2_pi2_rec3_final {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) (p1k D) εα) :
    RecCompleteness2 D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_pi2_rec3_closed hD C hchk hroots hg hal (Pi2W.pi2WitnessComplete hD C hchk)

/-- **The recursive verifier's completeness end to end** at π1-rec3's honest prover. -/
theorem recCompleteness_pi2_rec3_final_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) (p1k D) εα)
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D (pi1Rec3Prover D) δ1)
    (hh : Pi1HazardKeccakHonest D (pi1Rec3Prover D) δh) :
    RecCompletenessWith D (composeProver D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_pi2_rec3_closed_fs hD C hchk hroots hg hal (Pi2W.pi2WitnessComplete hD C hchk) δ1 δh h1 hh

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_final

/-- info: 'RecCompose.Pi2Sim.recCompleteness_pi2_rec3_final_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness_pi2_rec3_final_fs
