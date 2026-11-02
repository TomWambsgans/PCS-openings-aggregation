-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.RpmMain
import QuotientZk.RpmJoint

/-!
# Axioms of the random-permutation-model results

`zk_rpm`, `zk_rpm_deployed`, `zk_rpm_deployed_bits`, `zk_rpm_deployed_joint` and the steps they
rest on use only `propext`, `Classical.choice` and `Quot.sound` (the
commutation `simulateQ_proverWith` not even `Classical.choice`); the build fails if that changes.
-/

/-- info: 'QuotientZk.simulator_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.simulator_tape

/-- info: 'QuotientZk.romImpl_proverWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.romImpl_proverWith

/-- info: 'QuotientZk.simulateQ_proverWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.simulateQ_proverWith

/-- info: 'QuotientZk.zk_rom_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.zk_rom_perm

/-- info: 'QuotientZk.realGameRpm_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.realGameRpm_close

/-- info: 'QuotientZk.zk_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.zk_rpm

/-- info: 'QuotientZk.simulator2_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.simulator2_tape

/-- info: 'QuotientZk.transfer2_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.transfer2_game

/-- info: 'QuotientZk.DRpm.recImpl_implHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.recImpl_implHF

/-- info: 'QuotientZk.DRpm.romImpl_proverHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.romImpl_proverHF

/-- info: 'QuotientZk.DRpm.ro_enc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.ro_enc

/-- info: 'QuotientZk.DRpm.realGameRpmD_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.realGameRpmD_close

/-- info: 'QuotientZk.DRpm.zk_rpm_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.zk_rpm_skel

/-- info: 'QuotientZk.DRpm.zk_rpm_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.zk_rpm_deployed

/-- info: 'QuotientZk.DRpm.zk_rpm_deployed_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.zk_rpm_deployed_bits

/-- info: 'QuotientZk.DRpm.zk_rpm_deployed_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.zk_rpm_deployed_joint
