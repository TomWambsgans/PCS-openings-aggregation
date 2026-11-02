-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.Cost
import E2ECompleteness.Closed

/-!
# `PcsQuotient.Completeness`, end to end, with no hypothesis

`completeness_deployed_closed` (`Closed.lean`: the prover bridge closed) leaves one hypothesis, the
block count of the deployed staged run; `hcost_deployed` (`Cost.lean`) proves it (fewer than `2^47`
block calls). **`completeness_end`**: the Statement's `PcsQuotient.Completeness deltaDeployed`,
`deltaDeployed < 2^-162` (`deltaDeployed_lt`).
-/

namespace E2ECompleteness

/-- **End-to-end completeness**: `PcsQuotient.Completeness deltaDeployed`, with no hypothesis
(`deltaDeployed < 2^-162`, `deltaDeployed_lt`). -/
theorem completeness_end : PcsQuotient.Completeness deltaDeployed :=
  (completeness_deployed_closed hcost_deployed).1

end E2ECompleteness

/-- info: 'E2ECompleteness.completeness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_end
