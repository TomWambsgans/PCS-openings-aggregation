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
import Completeness.Chain
import Completeness.Membership

/-!
# End-to-end completeness of the membership proof

See the completeness section of `formal/README.md`. The end theorems are
`completeness_deployed_concrete` and `completeness_deployed_keccak` (`Membership.lean`: the deployed
circuit, σ, weights and basis, no hypothesis left), from `completeness_end` and
`completeness_end_bad_set` (`HiddenOpenings.lean`, every opening proven, for any circuit meeting
`MembershipCircuit`) and the general `completeness_deployed` (`Deployed.lean`, any openings that
are complete); every
declaration below depends on `propext`, `Classical.choice` and `Quot.sound` only (the kernel's
decision of the layouts' shape on `propext` and `Quot.sound`).
-/

/-- info: 'Completeness.completeness_deployed_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_deployed_concrete

/-- info: 'Completeness.completeness_deployed_keccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_deployed_keccak

/-- info: 'Completeness.completeness_deployed_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_deployed_basis

/-- info: 'Completeness.completeness_deployed_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_deployed_sigma

/-- info: 'Completeness.deployedMembership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.deployedMembership

/-- info: 'Completeness.deployedSigma_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.deployedSigma_keeps

/-- info: 'Completeness.honest_relation_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.honest_relation_deployed

/-- info: 'Completeness.deployedAssign_publicBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.deployedAssign_publicBits

/-- info: 'Completeness.Secret.toPcs_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.Secret.toPcs_root

/-- info: 'Completeness.Secret.toPcs_y' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.Secret.toPcs_y

/-- info: 'QuotientSecurity.deployedAssign_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.deployedAssign_satisfies

/-- info: 'QuotientSecurity.deployedAssign_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.deployedAssign_public

/-- info: 'QuotientSecurity.deployedAssign_provesMembership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.deployedAssign_provesMembership

/-- info: 'QuotientSecurity.deployedSigma_cellSrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.deployedSigma_cellSrc

/-- info: 'QuotientSecurity.ChiCircuit.eval_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.ChiCircuit.eval_satisfies

/-- info: 'QuotientSecurity.ChiCircuit.eq_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.ChiCircuit.eq_eval

/-- info: 'QuotientSecurity.deployedBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.deployedBasis

/-- info: 'QuotientSecurity.deployedBasis_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.deployedBasis_unique

/-- info: 'QuotientSecurity.deployedAssign_eq_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.deployedAssign_eq_outputs

/-- info: 'QuotientSecurity.outputs_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.outputs_satisfies

/-- info: 'QuotientSecurity.toChi_eval_eq_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientSecurity.toChi_eval_eq_outputs

/-- info: 'Completeness.completeness_keccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.completeness_keccak

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
