-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Cube
import FlockSound.Split
import FlockSound.Sumcheck
import FlockSound.Point
import FlockSound.Skip
import FlockSound.Frobenius
import FlockSound.Zerocheck
import FlockSound.R1CS
import FlockSound.Lincheck
import FlockSound.Matrices
import FlockSound.RingSwitch
import FlockSound.Flock
import FlockSound.Fields
import FlockSound.Leanvm
import FlockSound.Main

/-!
# FlockSound: Flock's soundness

Flock (`crates/leanvm_flock_gas/src/flock_min.rs`, `crates/leanvm_univariate/SPEC-FLOCK.md`, SPEC.md §7
and §13): its checks and claims give Lv42's `FlockRegion.Holds` of `q_flock`, but for bad challenges
whose sizes are explicit. Generic first (`Cube` to `Flock`), at leanVM's constants second (`Fields`,
`Leanvm`, `Main`). The guards below fail the build if a theorem's axioms grow beyond Lean's three.
-/

/-- info: 'FlockSound.sumcheck_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.sumcheck_escape

/-- info: 'FlockSound.sumcheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.sumcheck_sound

/-- info: 'FlockSound.card_sumBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_sumBad_le

/-- info: 'FlockSound.sumBad_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.sumBad_congr

/-- info: 'FlockSound.point_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.point_escape

/-- info: 'FlockSound.card_pointBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_pointBad_le

/-- info: 'FlockSound.skip_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.skip_escape

/-- info: 'FlockSound.card_skipBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_skipBad_le

/-- info: 'FlockSound.ring_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.ring_escape

/-- info: 'FlockSound.card_ringBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_ringBad_le

/-- info: 'FlockSound.ringBad_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.ringBad_congr

/-- info: 'FlockSound.range_subset_rel_leanvm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.range_subset_rel_leanvm

/-- info: 'FlockSound.range_subset_rel_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.range_subset_rel_tower

/-- info: 'FlockSound.zerocheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.zerocheck_sound

/-- info: 'FlockSound.card_zcBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_zcBad_le

/-- info: 'FlockSound.lincheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.lincheck_sound

/-- info: 'FlockSound.lin_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.lin_identity

/-- info: 'FlockSound.card_alphaBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_alphaBad_le

/-- info: 'FlockSound.cubeSum_matFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.cubeSum_matFun

/-- info: 'FlockSound.matFun_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.matFun_append

/-- info: 'FlockSound.matrices_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.matrices_sound

/-- info: 'FlockSound.batched_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.batched_sound

/-- info: 'FlockSound.card_lambdaBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_lambdaBad_le

/-- info: 'FlockSound.ring_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.ring_sound

/-- info: 'FlockSound.ringClaim_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.ringClaim_eq

/-- info: 'FlockSound.flock_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.flock_front

/-- info: 'FlockSound.flock_sound_v1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.flock_sound_v1

/-- info: 'FlockSound.flock_sound_merged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.flock_sound_merged

/-- info: 'FlockSound.ringSwitch_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.ringSwitch_injective

/-- info: 'FlockSound.fixedWeights_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.fixedWeights_independent

/-- info: 'FlockSound.phi8_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.phi8_injOn

/-- info: 'FlockSound.ofK_eq_sum_cellBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.ofK_eq_sum_cellBit

/-- info: 'FlockSound.leanvmSetup_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.leanvmSetup_valid

/-- info: 'FlockSound.r1csHolds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.r1csHolds_iff

/-- info: 'FlockSound.colPack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.colPack

/-- info: 'FlockSound.flockHolds_v1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.flockHolds_v1

/-- info: 'FlockSound.flockHolds_merged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.flockHolds_merged

/-- info: 'FlockSound.card_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_bad

/-- info: 'FlockSound.card_matBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_matBad
