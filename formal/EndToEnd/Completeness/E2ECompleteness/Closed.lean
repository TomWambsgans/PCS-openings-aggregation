-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.Final
import E2ECompleteness.ProverFacts
import E2ECompleteness.ProverTablesMatch
import E2ECompleteness.ProverCircuit

/-!
# `PcsQuotient.Completeness`, the prover bridge closed

`completeness_deployed_final` (`Final.lean`) with the prover bridge's facts discharged: the
Statement's constants (`constants`), its claims (`claimsMatch`), the prover's tables (`tablesMatch`)
and the membership circuit's cells and wiring (`circuitMatch`). **`completeness_deployed_closed`**:
`PcsQuotient.Completeness deltaDeployed`, `deltaDeployed < 2^-162`, from the block count of the
deployed staged run alone.
-/

open LeanVM.Rpm
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

/-- **`PcsQuotient.Completeness deltaDeployed`** (`deltaDeployed < 2^-162`), from the block count of
the staged run and the membership circuit's cells and wiring being F0b's. -/
theorem completeness_deployed_of_circuit
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48))
    (hcirc : CircuitMatch) :
    PcsQuotient.Completeness deltaDeployed ∧ deltaDeployed < (2 : ℝ≥0∞)⁻¹ ^ 162 :=
  completeness_deployed_final hcost constants claimsMatch hcirc tablesMatch

/-- **`PcsQuotient.Completeness deltaDeployed`** (`deltaDeployed < 2^-162`), from the block count of
the deployed staged run (at most `2^48` block calls) alone: every fact of the prover bridge is
proved. -/
theorem completeness_deployed_closed
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48)) :
    PcsQuotient.Completeness deltaDeployed ∧ deltaDeployed < (2 : ℝ≥0∞)⁻¹ ^ 162 :=
  completeness_deployed_of_circuit hcost circuitMatch

end E2ECompleteness

/-- info: 'E2ECompleteness.completeness_deployed_of_circuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_deployed_of_circuit

/-- info: 'E2ECompleteness.completeness_deployed_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_deployed_closed
