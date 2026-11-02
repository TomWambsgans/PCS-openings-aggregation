-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.RpmMain

/-!
# Axioms of the random-permutation-model results

`zk_rpm` and the steps it rests on use only `propext`, `Classical.choice` and `Quot.sound` (the
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
