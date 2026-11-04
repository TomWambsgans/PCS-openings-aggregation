-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at π1-rec3's honest prover (`formal/UniComplete`'s `uniProverRec3RP`),
-- assembled from `Pi2SimExp` (`Pi2ExperimentLe`), `Pi2SimCore` (the grinding without `Pi2RunAt`), `Pi2Chain` and
-- `Pi2TFreshPi2` (`Holds2`, `Pi2TFresh` from `Pi2AlphaFresh`), `Pi2CallsOpen` (`Pi2Pi1Openings`).
import RecCompose.Pi2SimCore
import RecCompose.Pi2TFreshPi2
import RecCompose.Pi2CallsOpen
import RecCompose.Pi2RunCost
import RecCompose.Pi2RunDuplex

/-!
# π2's completeness at π1-rec3's honest prover, the staged run's experiment and analysis proved

`P1` is π1-rec3's honest prover over the random permutation (`pi1Rec3Prover D`), its two-call program `p1k D` (no more
a parameter); `Pi2ExperimentLe` is proved (`pi2ExperimentLe_p1k`), `Pi2RunAt` is not needed (`rejectGood_pi2_good`),
`Pi2Pi1Openings` is proved (`pi2Pi1Openings`), `Pi2TFresh` is proved from `Pi2RunCost` and `Pi2AlphaFresh`
(`pi2TFresh_of`), `Pi2HashBeforeAlpha` (false at `p1k`) is replaced by `Pi2AlphaFresh`.

* **`holds2_pi2_p1k`**: `Pi2Staged.Holds2` of `pi2Staged … (p1k D input rows q)` from `Pi2RunDuplex`, `Pi2RunCost N`,
  `Pi2AlphaFresh εα` and `Pi2WitnessComplete`;
* **`recCompleteness2_pi2_rec3`**: `RecCompleteness2 D (pi1Rec3Prover D) (pi2Prover …) (delta2' N εα (tFreshBound2 N εα)
  (N · missProb 17 ^ nonceFuel))`, below `2^-164` at `N ≤ 2^50`, `εα ≤ 2^-201` (`delta2_pi2_le2`);
* **`recCompleteness_pi2_rec3_fs`**: the recursive verifier's completeness end to end.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2O
open scoped ENNReal

/-- **The staged run's `Holds2`** at π1-rec3's honest prover. -/
theorem holds2_pi2_p1k {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) {N : ℕ} {εα : ℝ≥0∞}
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) (p1k D)) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) (p1k D) N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) (p1k D) εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows)
    (hrel : D.pi1.HonestRelation rows input q) :
    (pi2Staged D C (pi2Facts hD C hchk) (p1k D input rows q) input).Holds2 D (pi1Rec3Prover D)
      (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel) input rows q 536 (badSet2 C.G) (badT2 C.G)
      (2 ^ 25 + 36) (2 ^ 27) N εα (tFreshBound2 N εα)
      ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := pi2ExperimentLe_p1k hD C (pi2Facts hD C hchk) hwc input rows q hfit hrel
  duplex := hdup input rows q hfit hrel
  cost := hcost input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 536 _
  alphaFresh := hal input rows q hfit hrel
  badCard p := card_badCopy_pi2 (pi2Facts hD C hchk) p.1 p.2.1 p.2.2
  badTCard fp := card_badT_pi2 (pi2Facts hD C hchk) fp.1.1 fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    (nonHole_pi2 C hchk (pi2Facts hD C hchk) fp.1.1)
  tFresh := pi2TFresh_of C (pi2Facts hD C hchk) (p1k D) hcost hal input rows q hfit hrel
  rejectGood := rejectGood_pi2_good hD C (pi2Facts hD C hchk) hroots hwc (pi2Pi1Openings hD C hchk hroots hg)
    (p1k D input rows q) input (hcost input rows q hfit hrel)

/-- **π2's completeness at π1-rec3's honest prover**, from the duplex shape, the cost, `α`'s freshness and the witness's
completeness. -/
theorem recCompleteness2_pi2_rec3 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) {N : ℕ} {εα : ℝ≥0∞}
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) (p1k D)) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) (p1k D) N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) (p1k D) εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' N εα (tFreshBound2 N εα) ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_of_staged2 fun input rows q hfit hrel ↦
    ⟨_, _, _, holds2_pi2_p1k hD C hchk hroots hg hdup hcost hal hwc input rows q hfit hrel⟩

/-- **The recursive verifier's completeness end to end** at π1-rec3's honest prover. -/
theorem recCompleteness_pi2_rec3_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) {N : ℕ} {εα : ℝ≥0∞}
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) (p1k D)) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) (p1k D) N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) (p1k D) εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D (pi1Rec3Prover D) δ1)
    (hh : Pi1HazardKeccakHonest D (pi1Rec3Prover D) δh) :
    RecCompletenessWith D (composeProver D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' N εα (tFreshBound2 N εα)
        ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD (pi1Rec3Prover D) _ _
    (recCompleteness2_pi2_rec3 hD C hchk hroots hg hdup hcost hal hwc) δ1 δh h1 hh

/-! ## The duplex shape and the cost proved -/

/-- **π2's completeness at π1-rec3's honest prover**, the staged run's duplex shape (`pi2RunDuplex_p1k`) and block count
(`pi2RunCost_p1k`, `N = pi2RunN ≤ 2^50`) proved: from `α`'s freshness and the witness's completeness. -/
theorem recCompleteness2_pi2_rec3_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) (p1k D) εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_pi2_rec3 hD C hchk hroots hg (pi2RunDuplex_p1k D C _) (pi2RunCost_p1k hD hg C _) hal hwc

/-- **δ2 in bits**: below `2^-164` at `εα ≤ 2^-201`. -/
theorem delta2_rec3_le {εα : ℝ≥0∞} (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 201) :
    delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  delta2_pi2_le2 Cost2.pi2RunN_le ha

/-- **The recursive verifier's completeness end to end** at π1-rec3's honest prover, the duplex shape and the cost
proved. -/
theorem recCompleteness_pi2_rec3_closed_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) (p1k D) εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D (pi1Rec3Prover D) δ1)
    (hh : Pi1HazardKeccakHonest D (pi1Rec3Prover D) δh) :
    RecCompletenessWith D (composeProver D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_pi2_rec3_fs hD C hchk hroots hg (pi2RunDuplex_p1k D C _) (pi2RunCost_p1k hD hg C _) hal hwc δ1 δh
    h1 hh

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.recCompleteness2_pi2_rec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness2_pi2_rec3

/-- info: 'RecCompose.Pi2Sim.recCompleteness_pi2_rec3_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness_pi2_rec3_fs

/-- info: 'RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_closed

/-- info: 'RecCompose.Pi2Sim.delta2_rec3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.delta2_rec3_le

/-- info: 'RecCompose.Pi2Sim.recCompleteness_pi2_rec3_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness_pi2_rec3_closed_fs
