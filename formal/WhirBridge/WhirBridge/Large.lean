/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-/
import WhirBridge.LargeParams
import WhirBridge.LargeLayout
import WhirBridge.LargeSound
import WhirBridge.LargeMargins

/-!
# The bridge at `2^24 ..= 2^28`: public layouts for a leanVM PIOP

* `LargeParams.lean`: the WHIR parameters at `log_n = 24 ..= 28`, rate `1/2` (ladders, grinding,
  certificates, level-0 lists `L₀`, the verifier's queries `QO`), decided.
* `LargeLayout.lean`: every public layout of `(table, height)` chunks `Layout::new` accepts is
  valid (`Layout.new_valid`), by one generic proof, and what its table is.
* `LargeSound.lean`: `ours_sound_public` (with `openingBound`), `ours_sound_public_at` (with the
  shape's `QO`), `joint_public_large`.
* `LargeMargins.lean`: the batching lead and the union over one, two, three roots' lists.

The theorems use only `propext`, `Classical.choice` and `Quot.sound` (below).
-/

/-- info: 'WhirBridge.ladder_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ladder_large

/-- info: 'WhirBridge.shapeOK_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.shapeOK_large

/-- info: 'WhirBridge.listMax_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.listMax_large

/-- info: 'WhirBridge.candidates_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.candidates_large

/-- info: 'WhirBridge.largeQueries_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WhirBridge.largeQueries_eq

/-- info: 'WhirBridge.isTotalQueryBound_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.isTotalQueryBound_large

/-- info: 'WhirBridge.Layout.new_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Layout.new_valid

/-- info: 'WhirBridge.newBlocks_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.newBlocks_nodup

/-- info: 'WhirBridge.Layout.new_table_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Layout.new_table_eq_zero

/-- info: 'WhirBridge.Blocks.table_eq_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Blocks.table_eq_lane

/-- info: 'WhirBridge.ours_sound_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ours_sound_public

/-- info: 'WhirBridge.ours_sound_public_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ours_sound_public_le

/-- info: 'WhirBridge.ours_sound_public_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ours_sound_public_at

/-- info: 'WhirBridge.ours_sound_public_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ours_sound_public_layout

/-- info: 'WhirBridge.joint_public_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.joint_public_large

/-- info: 'WhirBridge.eBatch_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.eBatch_large

/-- info: 'WhirBridge.ncard_bad_candidates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ncard_bad_candidates_le

/-- info: 'WhirBridge.union_two_roots_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.union_two_roots_le

/-- info: 'WhirBridge.union_three_roots_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.union_three_roots_le

/-- info: 'WhirBridge.largeList_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.largeList_pairs
