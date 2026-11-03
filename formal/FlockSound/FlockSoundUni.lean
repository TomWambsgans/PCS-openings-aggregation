-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.RoundByRound
import FlockSoundUni.Loops
import FlockSoundUni.Decode
import FlockSoundUni.Shape
import FlockSoundUni.Link
import FlockSoundUni.Parse
import FlockSoundUni.Prefix
import FlockSoundUni.Catch
import FlockSoundUni.Transcription
import FlockSoundUni.Instance

/-- info: 'FlockSound.Uni.card_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.card_hit_le

/-- info: 'FlockSound.Uni.prob_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.prob_hit_le

/-- info: 'FlockSound.Uni.step_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.step_le

/-- info: 'FlockSound.Uni.stateOf_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.stateOf_nil

/-- info: 'FlockSound.Uni.ofFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.ofFamily

/-- info: 'FlockSound.Uni.nextScalars_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.nextScalars_eq

/-- info: 'FlockSound.Uni.samples_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.samples_eq

/-- info: 'FlockSound.Uni.sumcheck_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.sumcheck_eq

/-- info: 'FlockSound.Uni.runRounds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.runRounds_eq

/-- info: 'FlockSound.Uni.readRounds_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.readRounds_append

/-- info: 'FlockSound.Uni.roundPoly_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.roundPoly_eq

/-- info: 'FlockSound.Uni.sumcheckR_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.sumcheckR_eq

/-- info: 'FlockSound.Uni.decode_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.decode_consistent

/-- info: 'FlockSound.Uni.decodeSC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.decodeSC_eq

/-- info: 'FlockSound.Uni.readRounds_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.readRounds_fit

/-- info: 'FlockSound.Uni.flock_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flock_link

/-- info: 'FlockSound.Uni.flockProg_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockProg_root

/-- info: 'FlockSound.Uni.card_flockBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.card_flockBad

/-- info: 'FlockSound.Uni.zcBad_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.zcBad_congr

/-- info: 'FlockSound.Uni.sumBad_congr'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.sumBad_congr'

/-- info: 'FlockSound.Uni.trueAt_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.trueAt_congr

/-- info: 'FlockSound.Uni.badAt_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.badAt_congr

/-- info: 'FlockSound.Uni.agree_pfx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.agree_pfx

/-- info: 'FlockSound.Uni.hitIn_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.hitIn_of_mem

/-- info: 'FlockSound.Uni.fits_of_doneFits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.fits_of_doneFits

/-- info: 'FlockSound.Uni.sc_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.sc_consistent

/-- info: 'FlockSound.Uni.zc_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.zc_consistent

/-- info: 'FlockSound.Uni.lin_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.lin_consistent

/-- info: 'FlockSound.Uni.outOf_parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.outOf_parse

/-- info: 'FlockSound.Uni.hit_of_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.hit_of_bad

/-- info: 'FlockSound.Uni.catches_of_tx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.catches_of_tx

/-- info: 'FlockSound.Uni.flockSound_of_tx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockSound_of_tx

/-- info: 'FlockSound.Uni.flockSound_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockSound_err

/-- info: 'FlockSound.Uni.flockSound_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockSound_error

/-- info: 'FlockSound.Uni.tx_of_flockTx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.tx_of_flockTx

/-- info: 'FlockSound.Uni.flockSoundInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockSoundInstance

/-- info: 'FlockSound.Uni.flockSoundInstance_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockSoundInstance_err

/-- info: 'FlockSound.Uni.flockSoundInstance_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockSoundInstance_error
