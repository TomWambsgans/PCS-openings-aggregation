-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at π1-rec3's honest prover with `α`'s freshness proved: `Pi2AlphaG`
-- (`Holds3`, the staged bounds conditioned on the graph's acceptance), `Pi2AlphaFresh` (`alphaFresh_p1k`),
-- `Pi2AlphaSupport` (`accA_pi2`, `accB_pi2`), and `Pi2SimEnd`'s, `Pi2Closed`'s ingredients.
import RecCompose.Pi2AlphaFresh
import RecCompose.Pi2AlphaG
import RecCompose.Pi2Closed

/-!
# π2's completeness, closed but for the run-checked inputs

`Pi2AlphaFresh εα` (`Pi2TFreshPi2`) asks `α`'s input to be fresh on every outcome of stage A. Off π1-rec3's graph
accepting (π1's prover returning none, or a proof whose public values do not match the reads), `pi2Staged`'s `α` input is
`fixLen`'s `536` zeros, which nothing in this repository shows π1-rec3's prover does not hash. Those outcomes are
rejected (the verdict's first component is the graph's), so `α`'s and `t`'s freshness are asked only where the graph
accepted (`Pi2AlphaG.Holds3`, `GAcc`), and there they are proved:

* **`holds3_pi2_p1k`**: `Holds3` of `pi2Staged … (p1k D input rows q)` at `G = GAcc`, `εα = alphaBound`
  (`alphaFresh_p1k`), `εt = tFreshBound2 pi2RunN alphaBound` (`pi2TFresh_ofG`);
* **`recCompleteness2_pi2_rec3_closed`**: `RecCompleteness2 D (pi1Rec3Prover D) (pi2Prover …) δ2` from `Pi2Circuits D`,
  `hroots`, `GraphsAgree`, `Pi2ViewChecked C` only, `δ2 = delta2' pi2RunN alphaBound (tFreshBound2 pi2RunN alphaBound)
  (pi2RunN · missProb 17 ^ nonceFuel) ≤ 2^-164` (**`delta2_alpha_le`**);
* **`recCompleteness_pi2_rec3_closed_fs`**: the recursive verifier's completeness end to end, with the Fiat–Shamir
  premises `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest`.

The names are `Pi2Sim`'s (kept, with `hal`), in this namespace.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Alpha

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2O
open scoped ENNReal

/-- **The staged run's `Holds3`** at π1-rec3's honest prover, `α`'s and `t`'s freshness where the graph accepted. -/
theorem holds3_pi2_p1k {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows) (hrel : D.pi1.HonestRelation rows input q) :
    (pi2Staged D C (pi2Facts hD C hchk) (p1k D input rows q) input).Holds3 D (pi1Rec3Prover D)
      (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel) input rows q 536 (badSet2 C.G) (badT2 C.G)
      Pi2Sim.GAcc (fun b : StB ↦ Pi2Sim.GAcc b.a) (2 ^ 25 + 36) (2 ^ 27) Cost2.pi2RunN Pi2Sim.alphaBound
      (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := Pi2Sim.pi2ExperimentLe_p1k hD C (pi2Facts hD C hchk) (Pi2W.pi2WitnessComplete hD C hchk) input rows q
    hfit hrel
  duplex := pi2RunDuplex_p1k D C _ input rows q hfit hrel
  cost := pi2RunCost_p1k hD hg C _ input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 536 _
  alphaFresh := Pi2Sim.alphaFresh_p1k hD hg C hchk input rows q hfit hrel
  accA := fun a ha s₁ s₂ s₃ c z hz ↦ Pi2Sim.accA_pi2 C (pi2Facts hD C hchk) input (p1k D input rows q) a ha s₁ s₂ s₃ c z hz
  accB := fun b hb st c z hz ↦ Pi2Sim.accB_pi2 C input b hb st c z hz
  badCard p := card_badCopy_pi2 (pi2Facts hD C hchk) p.1 p.2.1 p.2.2
  badTCard fp := card_badT_pi2 (pi2Facts hD C hchk) fp.1.1 fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    (nonHole_pi2 C hchk (pi2Facts hD C hchk) fp.1.1)
  tFresh := pi2TFresh_ofG C (pi2Facts hD C hchk) (p1k D input rows q) input
    (pi2RunCost_p1k hD hg C _ input rows q hfit hrel) Pi2Sim.GAcc
    (Pi2Sim.alphaFresh_p1k hD hg C hchk input rows q hfit hrel)
  rejectGood := Pi2Sim.rejectGood_pi2_good hD C (pi2Facts hD C hchk) hroots (Pi2W.pi2WitnessComplete hD C hchk)
    (pi2Pi1Openings hD C hchk hroots hg) (p1k D input rows q) input (pi2RunCost_p1k hD hg C _ input rows q hfit hrel)

/-- **π2's completeness at π1-rec3's honest prover**, from the run-checked inputs only (`Pi2Circuits D`, `hroots`,
`GraphsAgree`, `Pi2ViewChecked C`). -/
theorem recCompleteness2_pi2_rec3_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) :
    RecCompleteness2 D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_of_staged3 fun input rows q hfit hrel ↦
    ⟨_, _, _, _, _, holds3_pi2_p1k hD C hchk hroots hg input rows q hfit hrel⟩

/-- **δ2 in bits**: below `2^-164` (`alphaBound ≤ 2^-204`). -/
theorem delta2_alpha_le :
    delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  Pi2Sim.delta2_rec3_le Pi2Sim.alphaBound_le201

/-- **The recursive verifier's completeness end to end** at π1-rec3's honest prover, from the run-checked inputs and
the Fiat–Shamir premises. -/
theorem recCompleteness_pi2_rec3_closed_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D (pi1Rec3Prover D) δ1)
    (hh : Pi1HazardKeccakHonest D (pi1Rec3Prover D) δh) :
    RecCompletenessWith D (composeProver D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD (pi1Rec3Prover D) _ _
    (recCompleteness2_pi2_rec3_closed hD C hchk hroots hg) δ1 δh h1 hh

end RecCompose.Pi2Alpha

/-- info: 'RecCompose.Pi2Alpha.recCompleteness2_pi2_rec3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.recCompleteness2_pi2_rec3_closed

/-- info: 'RecCompose.Pi2Alpha.delta2_alpha_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.delta2_alpha_le

/-- info: 'RecCompose.Pi2Alpha.recCompleteness_pi2_rec3_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.recCompleteness_pi2_rec3_closed_fs
