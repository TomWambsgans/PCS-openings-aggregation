-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the block cost `hashBlocks`.
import E2ECompleteness.Grinding

/-!
# `PcsQuotient.Completeness deltaDeployed`, end to end

`completeness_deployed_cost_rej` (`Duplex.lean`) left two facts about the deployed staged run
(`stagedRun`): its block count and the grinding at non-degenerate challenges (`RejectGood`).
`Grinding.lean` proves the second from the first and the Prover bridge (`rejectGood_deployed`), so:

* **`completeness_deployed_of_tail`**: `PcsQuotient.Completeness deltaDeployed` from the block count
  `2^48` and the Prover bridge's two facts at every hash function and permutation, (Acc)
  (`TailAccepts`) and (Red) (`TailReduces`);
* **`completeness_deployed_final`**: the same from the block count and the Prover bridge's remaining
  hypotheses (`Constants`, `Bridge.ClaimsMatch stmtConsts`, `CircuitMatch`, `TablesMatch`), which
  give (Acc) and (Red) (`tailAccepts`, `tailReduces`, from `acc_staged`, `red_staged`);

with `deltaDeployed < 2^-162` (`deltaDeployed_lt`).
-/

open LeanVM.Rpm
open PcsQuotient
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

/-- **`PcsQuotient.Completeness deltaDeployed`** from the block count `2^48` of the deployed staged
run, (Acc) and (Red). -/
theorem completeness_deployed_of_tail
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48))
    (hacc : TailAccepts) (hred : TailReduces) :
    PcsQuotient.Completeness deltaDeployed :=
  completeness_deployed_cost_rej hcost (rejectGood_of_tail hcost hacc hred)

/-- **`PcsQuotient.Completeness deltaDeployed`, `deltaDeployed < 2^-162`**, from the block count
`2^48` of the deployed staged run and the Prover bridge's remaining hypotheses. -/
theorem completeness_deployed_final
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48))
    (hK : Constants) (hcl : Bridge.ClaimsMatch stmtConsts) (hcirc : CircuitMatch)
    (hT : TablesMatch) :
    PcsQuotient.Completeness deltaDeployed ∧ deltaDeployed < (2 : ℝ≥0∞)⁻¹ ^ 162 :=
  ⟨completeness_deployed_of_tail hcost (tailAccepts hK hcl hcirc hT)
    (tailReduces hK hcl hcirc hT), deltaDeployed_lt⟩

end E2ECompleteness

/-- info: 'E2ECompleteness.rejectGood_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.rejectGood_of_tail

/-- info: 'E2ECompleteness.rejectGood_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.rejectGood_deployed

/-- info: 'E2ECompleteness.completeness_deployed_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_deployed_of_tail

/-- info: 'E2ECompleteness.completeness_deployed_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_deployed_final
