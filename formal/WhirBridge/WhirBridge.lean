-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import WhirBridge.Opening
import WhirBridge.Sound
import WhirBridge.Table
import WhirBridge.Hidden
import WhirBridge.Layouts
import WhirBridge.Variant
import WhirBridge.Family
import WhirBridge.Verifier
import WhirBridge.Gaps

/-!
# The WHIR bridge

`opening::verify` of `crates/quotient/src/opening.rs` under leanerVM `mumbai`'s theorems: its
Fiat-Shamir soundness in the random-oracle model for every valid layout (`opening_sound`) and for
the protocol's witness, wiring and quotient layouts at every supported size (`ours_sound`), in
table terms (`Layout.holds_iff`, `Table::read` for the hidden layouts; the hidden layouts' gadget,
one more stack claim of value zero, `gadget_holds_iff`). The headline theorems use only `propext`,
`Classical.choice` and `Quot.sound`.
-/

/-- info: 'WhirBridge.isMultiaffine_layoutClaimWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.isMultiaffine_layoutClaimWeight

/-- info: 'WhirBridge.isMultiaffine_gadgetWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.isMultiaffine_gadgetWeight

/-- info: 'WhirBridge.gadget_holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.gadget_holds_iff

/-- info: 'WhirBridge.Layout.joint_of_not_doom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Layout.joint_of_not_doom

/-- info: 'WhirBridge.layouts_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.layouts_shape

/-- info: 'WhirBridge.Layout.check_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Layout.check_eq

/-- info: 'WhirBridge.holds_iff_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.holds_iff_hidden

/-- info: 'WhirBridge.Layout.holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Layout.holds_iff

/-- info: 'WhirBridge.layouts_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.layouts_valid

/-- info: 'WhirBridge.layouts_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.layouts_ok

/-- info: 'WhirBridge.family_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.family_sound

/-- info: 'WhirBridge.openingVerify_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.openingVerify_imp

/-- info: 'WhirBridge.opening_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.opening_sound

/-- info: 'WhirBridge.opening_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.opening_bound_le

/-- info: 'WhirBridge.ours_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ours_sound
