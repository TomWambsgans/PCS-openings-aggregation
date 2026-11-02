-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.ListChainKDoomInstance
import Compose.ListChainKDoomExample

/-! The axioms of the closed `k`-round chain's theorems (`ListChainKDoom.lean`, its
`quotient::protocol` instance and its two-root example): `propext`, `Classical.choice`,
`Quot.sound` only (no `sorryAx`, no `native_decide`'s `Lean.ofReduceBool`), checked when the
module is built. -/

/-- info: 'Compose.map_expW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.map_expW

/-- info: 'Compose.prEvent_stageK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_stageK_le

/-- info: 'Compose.prEvent_doomAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_doomAt_le

/-- info: 'Compose.trace_whir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_whir

/-- info: 'Compose.knowledgeSoundness_listChainK_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainK_closed

/-- info: 'Compose.knowledgeSoundness_listChainK_closed_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainK_closed_rpm

/-- info: 'Compose.whirOp_ok_tableCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.whirOp_ok_tableCode

/-- info: 'Compose.whirOp_ok_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.whirOp_ok_stack

/-- info: 'Compose.knowledgeSoundness_merkle_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_merkle_closed

/-- info: 'Compose.chunks27_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Compose.chunks27_ok

/-- info: 'Compose.knowledgeSoundness_twoRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_twoRoots

/-- info: 'Compose.knowledgeSoundness_twoRoots_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_twoRoots_bits
