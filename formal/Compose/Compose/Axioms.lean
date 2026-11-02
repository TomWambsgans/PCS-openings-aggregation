-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Final
import Compose.ComposedKC
import Compose.Extract
import Compose.AdversaryLog
import Compose.Deployed

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
