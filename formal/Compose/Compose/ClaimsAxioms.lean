-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Claims

/-!
# Axioms of the claims' discharge

`Reduce.lean`'s bridge (`reduce`'s claims are F1's) and `Claims.lean`'s discharge of
`WitnessClaims`, `QuotientClaims`, `WiringClaims`, with the concrete statement
`knowledgeSoundness_deployed_concrete`: `propext`, `Classical.choice`, `Quot.sound` only.
-/

/-- info: 'Compose.Reduce.witness_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.Reduce.witness_iff

/-- info: 'Compose.Reduce.wiring_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.Reduce.wiring_iff

/--
info: 'Compose.Reduce.quotientClaims_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.Reduce.quotientClaims_of

/--
info: 'Compose.Reduce.matches_params' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.Reduce.matches_params

/-- info: 'Compose.tabEval_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.tabEval_eq_mle

/-- info: 'Compose.deployD_clW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.deployD_clW

/-- info: 'Compose.deployD_clσ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.deployD_clσ

/-- info: 'Compose.deployD_clQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.deployD_clQ

/--
info: 'Compose.witnessClaims_deployD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.witnessClaims_deployD

/--
info: 'Compose.quotientClaims_deployD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.quotientClaims_deployD

/--
info: 'Compose.wiringClaims_deployD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.wiringClaims_deployD

/--
info: 'Compose.knowledgeSoundness_deployed_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_deployed_concrete

/-- info: 'Compose.wiring_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.wiring_table

/--
info: 'Compose.wiringStack_carries' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.wiringStack_carries

/--
info: 'Compose.knowledgeSoundness_deployed_rust' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_deployed_rust
