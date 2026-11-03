-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.FlockProverTerminal
import UniComplete.FlockProverSync
import UniComplete.FlockProverRing
import UniComplete.FlockProverSum

/-!
# Flock's honest prover: the headline theorems and their axioms

`UniComplete.FlockP.flockProve H : FlockProver m` (`FlockProver.lean`), at a pure Keccak-256 `H` (`Id`), every writer
(any challenges), on `q_flock`'s words `q`:

* `pendingTerminalHolds` (`k ≤ 6`, `log_n ≥ 14`, the slices sent): `PendingTerminalHolds`;
* `flockSyncs` (the slices sent): `FlockSyncs H (flockProve (pure ∘ H)) log_n variant q` (`SyncBasic`'s statement);
* `flockRingHolds` (tower order): `FlockRingHolds`;
* `pendingSumHolds` (`k ≤ 6`, `log_n = 14 + κ`, the slices sent, `FlockHolds κ q`, and for `k > 0` the univariate
  skip's completeness `SkipComplete k`): `PendingSumHolds`;
* `tables_shape`: the tables' shape the batch reads (`BatchWF`).

`flockHolds_of_traceHonest`: an honest trace's `TraceHonest.flock` is `FlockHolds (tr.height 5) tr.qflock`.

The guards below fail the build if a theorem's axioms grow beyond Lean's three.
-/

/-- **An honest trace's Flock relation** is `FlockHolds` of its `q_flock` (`qflockColumn tr = colOf …`, by
definition). -/
theorem UniComplete.FlockP.flockHolds_of_traceHonest (tr : UniComplete.Trace) (h : UniComplete.TraceHonest tr) :
    UniComplete.FlockP.FlockHolds (tr.height 5) tr.qflock := h.flock

/-- info: 'UniComplete.FlockP.pendingTerminalHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.pendingTerminalHolds

/-- info: 'UniComplete.FlockP.flockSyncs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.flockSyncs

/-- info: 'UniComplete.FlockP.flockRingHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.flockRingHolds

/-- info: 'UniComplete.FlockP.Tower.towerTarget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.Tower.towerTarget_eq

/-- info: 'UniComplete.FlockP.mle_sliced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.mle_sliced

/-- info: 'UniComplete.FlockP.pendingSumHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.pendingSumHolds

/-- info: 'UniComplete.FlockP.tables_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.tables_shape

/-- info: 'UniComplete.FlockP.zcRounds_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.zcRounds_complete

/-- info: 'UniComplete.FlockP.lcRounds_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.lcRounds_complete

/-- info: 'UniComplete.FlockP.pendingSum_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.pendingSum_pure
