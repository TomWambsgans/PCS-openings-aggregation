-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.ListChainKInstance
import Compose.ListChainKBits

/-! The axioms of the `k`-round list chain's theorems: `propext`, `Classical.choice`, `Quot.sound`
only (no `sorryAx`, no `native_decide`'s `Lean.ofReduceBool`), checked when the module is built. -/

/-- info: 'Compose.chain_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.chain_unique

/-- info: 'Compose.parseK_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.parseK_unique

/-- info: 'Compose.prEvent_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_path

/-- info: 'Compose.prEvent_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_round

/-- info: 'Compose.draws_chalL_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.draws_chalL_evalDistEq

/-- info: 'Compose.Piop.exists_bad_of_lostWon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.Piop.exists_bad_of_lostWon

/-- info: 'Compose.prEvent_forall₂_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_forall₂_le

/-- info: 'Compose.prob_roundBadK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prob_roundBadK

/-- info: 'Compose.prob_listBadK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prob_listBadK

/-- info: 'Compose.trace_coreK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_coreK

/-- info: 'Compose.prob_kcBadK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prob_kcBadK

/-- info: 'Compose.prob_rootBadK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prob_rootBadK

/-- info: 'Compose.prob_advBadK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prob_advBadK

/-- info: 'Compose.trace_advK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_advK

/-- info: 'Compose.knowledgeSoundness_listK_adv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listK_adv

/-- info: 'Compose.breaksK_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.breaksK_imp

/-- info: 'Compose.knowledgeSoundness_listChainK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainK

/-- info: 'Compose.knowledgeSoundness_listChainK_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainK_setup

/-- info: 'Compose.rpm_le_kcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.rpm_le_kcG

/-- info: 'Compose.knowledgeSoundness_listChainK_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainK_rpm

/-- info: 'Compose.chain_quot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.chain_quot

/-- info: 'Compose.expK_quot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.expK_quot

/-- info: 'Compose.quotPiop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.quotPiop

/-- info: 'Compose.maxErrK_quot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.maxErrK_quot_le

/-- info: 'Compose.knowledgeSoundness_list_adv_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_list_adv_K

/-- info: 'Compose.knowledgeSoundness_composed_adv_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_composed_adv_K

/-- info: 'Compose.knowledgeSoundness_merkle_adv_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_merkle_adv_K

/-- info: 'Compose.factor_mul_err_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.factor_mul_err_le

/-- info: 'Compose.facL_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.facL_le_pow

/-- info: 'Compose.bits_generic₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.bits_generic₂

/-- info: 'Compose.bits_certified₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.bits_certified₂

/-- info: 'Compose.bits_quot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.bits_quot

/-- info: 'Compose.maxErrK_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.maxErrK_le_bits

/-- info: 'Compose.knowledgeSoundness_listChainK_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainK_bits
