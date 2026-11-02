-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Main

/-! # The axioms of the zero-knowledge bridge's theorems -/

/-- info: 'PcsQuotient.EndToEnd.run_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.run_tape

/-- info: 'PcsQuotient.EndToEnd.close_of_coinFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.close_of_coinFree

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_of_coinFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_of_coinFree

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_of_bridges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_of_bridges

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed

/-- info: 'PcsQuotient.EndToEnd.zkBoundDeployed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zkBoundDeployed_le

/-- info: 'PcsQuotient.EndToEnd.rpmIdeal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.rpmIdeal_eq

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_deployed_rpmSimulator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed_rpmSimulator

/-- info: 'PcsQuotient.EndToEnd.realExperiment_coins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.realExperiment_coins

/-- info: 'PcsQuotient.EndToEnd.realBridge_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.realBridge_of

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_end
