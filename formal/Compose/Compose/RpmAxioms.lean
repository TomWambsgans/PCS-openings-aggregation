-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Rpm

/-! The axioms of the composition's theorems in the random-permutation model (`Rpm.lean`):
`propext`, `Classical.choice`, `Quot.sound` only. -/

/-- info: 'Compose.knowledgeSoundness_wired_setup_rpm_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_wired_setup_rpm_bits

/-- info: 'Compose.knowledgeSoundness_wired_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_wired_rpm

/-- info: 'Compose.rpm_le_wired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.rpm_le_wired

/-- info: 'Compose.rpmThreaded_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.rpmThreaded_evalDistEq

/-- info: 'Compose.consistent_romPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.consistent_romPrefix

/-- info: 'Compose.exists_det_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.exists_det_setup

/-- info: 'Compose.le_wiredExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.le_wiredExp
