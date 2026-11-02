-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Completeness.Reduction
import Completeness.Circuit
import Completeness.Tables
import Completeness.Honest
import Completeness.HiddenFill
import Completeness.Read
import Completeness.Opening
import Completeness.Wiring
import Completeness.Deployed
import Completeness.Final
import Completeness.HiddenOpenings

/-!
# End-to-end completeness of the membership proof

See the completeness section of `formal/README.md`. The end theorems are `completeness_end` and
`completeness_end_bad_set` (`HiddenOpenings.lean`, every opening proven), from the general
`completeness_deployed` (`Deployed.lean`, any openings that are complete); every
declaration below depends on `propext`, `Classical.choice` and `Quot.sound` only (the kernel's
decision of the layouts' shape on `propext` and `Quot.sound`).
-/

/-- info: 'Completeness.completeness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_end

/-- info: 'Completeness.completeness_end_bad_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_end_bad_set

/-- info: 'Completeness.witnessOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.witnessOpening

/-- info: 'Completeness.quotientOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.quotientOpening

/-- info: 'Completeness.hidden_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.hidden_complete

/-- info: 'Completeness.gadgetValue_fillNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.gadgetValue_fillNew

/-- info: 'Completeness.completeness_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_deployed

/-- info: 'Completeness.completeness_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_hidden

/-- info: 'Completeness.completeness_bad_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_bad_set

/-- info: 'Completeness.honest_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.honest_claims

/-- info: 'Completeness.Reduction.honest_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.Reduction.honest_accepts

/-- info: 'Completeness.Reduction.bad_fraction_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.Reduction.bad_fraction_le

/-- info: 'Completeness.Reduction.bad_bound_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.Reduction.bad_bound_lt

/-- info: 'Completeness.honest_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.honest_relation

/-- info: 'Completeness.exists_table_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.exists_table_support

/-- info: 'Completeness.qGate_mem_lifts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.qGate_mem_lifts

/-- info: 'Completeness.accepts_table_of_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.accepts_table_of_honest

/-- info: 'Completeness.mle_eq_tableEvalN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.mle_eq_tableEvalN

/-- info: 'Completeness.quotient_inChunks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.quotient_inChunks

/-- info: 'Completeness.readNew_fillNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.readNew_fillNew

/-- info: 'Completeness.witness_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.witness_read

/-- info: 'Completeness.quotient_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.quotient_read

/-- info: 'Completeness.gadgetWeight_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.gadgetWeight_sum_zero

/-- info: 'Completeness.deployed_newHiddenOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.deployed_newHiddenOK

/-- info: 'Completeness.wiringOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.wiringOpening

/-- info: 'Completeness.openingVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.openingVerify_honest

/-- info: 'Completeness.ours_romComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.ours_romComplete
