-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Final
import Compose.ComposedKC
import Compose.Extract
import Compose.AdversaryLog
import Compose.Deployed
import Compose.WiredDecoded
import Compose.WiringSetup

/-! The axioms of the composition's theorems (printed when the module is built). -/

#print axioms Compose.knowledgeSoundness_list
#print axioms Compose.trace_listBad
#print axioms Compose.prob_listBad
#print axioms Compose.breaks_imp
#print axioms Compose.breaksOne_iff
#print axioms Compose.knowledgeSoundness_composed
#print axioms Compose.listError_le_generic
#print axioms Compose.listError_le_certified
#print axioms Compose.knowledgeSoundness_composed_bits
#print axioms Compose.merkleWord_stable
#print axioms Compose.merkleCommit
#print axioms Compose.knowledgeSoundness_merkle
#print axioms Compose.knowledgeSoundness_merkle_certified
#print axioms Compose.prEvent_randomOracle_le_of_freshBad_dep
#print axioms Compose.prEvent_view
#print axioms Compose.prob_kcBad
#print axioms Compose.trace_kc
#print axioms Compose.knowledgeSoundness_list_kc
#print axioms Compose.knowledgeSoundness_composed_kc
#print axioms Compose.knowledgeSoundness_merkle_kc
#print axioms Compose.leafAt_of_climb
#print axioms Compose.leafAt_some
#print axioms Compose.merkleWord_eq_extract
#print axioms Compose.wordOfMerkle_eq_extract
#print axioms Compose.run_congr
#print axioms Compose.prob_rootBad
#print axioms Compose.trace_adv
#print axioms Compose.knowledgeSoundness_list_adv
#print axioms Compose.knowledgeSoundness_composed_adv
#print axioms Compose.knowledgeSoundness_merkle_adv
#print axioms Compose.map_run_loggedKC
#print axioms Compose.consistent_run_loggedKC
#print axioms Compose.prEvent_loggedPrefix
#print axioms Compose.prEvent_EW_le
#print axioms Compose.prEvent_EQ_le
#print axioms Compose.trace_deployed
#print axioms Compose.knowledgeSoundness_deployed
#print axioms Compose.knowledgeSoundness_deployed_setup

/-! The wired composition (guarded: no `sorryAx`, no new axiom). -/

/-- info: 'Compose.ourVerifier_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.ourVerifier_queryBound

/-- info: 'Compose.candidates_of_codeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.candidates_of_codeword

/-- info: 'Compose.candidates_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.candidates_honest

/-- info: 'Compose.prEvent_EWw_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_EWw_le

/-- info: 'Compose.prEvent_Eσw_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_Eσw_le

/-- info: 'Compose.prEvent_EQw_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_EQw_le

/-- info: 'Compose.wired_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.wired_deployed

/-- info: 'Compose.withSetup_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.withSetup_run

/-- info: 'Compose.trace_wired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_wired

/-- info: 'Compose.knowledgeSoundness_wired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_wired

/-- info: 'Compose.knowledgeSoundness_wired_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_wired_decoded

/-- info: 'Compose.knowledgeSoundness_wired_decoded_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_wired_decoded_bits

/-- info: 'Compose.simulateQ_option_of_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.simulateQ_option_of_log

/-- info: 'Compose.climb_of_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.climb_of_levels

/-- info: 'Compose.extract_wiringSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.extract_wiringSetup

/-- info: 'Compose.honest_stackWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.honest_stackWord

/-- info: 'Compose.isTotalQueryBound_stackSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.isTotalQueryBound_stackSetup

/-- info: 'Compose.knowledgeSoundness_wired_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_wired_setup

/-- info: 'Compose.knowledgeSoundness_wired_setup_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_wired_setup_bits
