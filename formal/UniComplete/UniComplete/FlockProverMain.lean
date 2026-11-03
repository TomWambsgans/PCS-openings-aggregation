-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.FlockProverTerminal
import UniComplete.FlockProverSync
import UniComplete.FlockProverRing
import UniComplete.FlockProverSum
import UniComplete.FlockProverSkip

/-!
# Flock's honest prover: the headline theorems and their axioms

`UniComplete.FlockP.flockProve H : FlockProver m` (`FlockProver.lean`), at a pure Keccak-256 `H` (`Id`), every writer
(any challenges), on `q_flock`'s words `q`:

* `pendingTerminalHolds` (`k ≤ 6`, `log_n ≥ 14`, the slices sent): `PendingTerminalHolds`;
* `flockSyncs` (the slices sent): `FlockSyncs H (flockProve (pure ∘ H)) log_n variant q` (`SyncBasic`'s statement);
* `flockRingHolds` (tower order): `FlockRingHolds`;
* `pendingSumHolds_honest` (`k ≤ 6`, `log_n = 14 + κ`, the slices sent, `FlockHolds κ q`): `PendingSumHolds`
  (`pendingSumHolds` with the univariate skip's completeness discharged, `Skip.skipComplete`);
* `tables_shape`: the tables' shape the batch reads (`BatchWF`).

`flockHolds_of_traceHonest`: an honest trace's `TraceHonest.flock` is `FlockHolds (tr.height 5) tr.qflock`.

The guards below fail the build if a theorem's axioms grow beyond Lean's three.
-/

/-- **An honest trace's Flock relation** is `FlockHolds` of its `q_flock` (`qflockColumn tr = colOf …`, by
definition). -/
theorem UniComplete.FlockP.flockHolds_of_traceHonest (tr : UniComplete.Trace) (h : UniComplete.TraceHonest tr) :
    UniComplete.FlockP.FlockHolds (tr.height 5) tr.qflock := h.flock

/-- **`PendingSumHolds` of the honest prover**, unconditionally but for Flock's relation on `q_flock`: the
univariate skip's completeness holds at every `k ≤ 6` (`Skip.skipComplete`). -/
theorem UniComplete.FlockP.pendingSumHolds_honest (H : List UInt8 → Id LeanVM.Protocol.Digest) (κ : ℕ)
    (variant : UniStatement.Flock.Variant) (q : Array LeanVM.Parameters.K) (w : UniComplete.Wr)
    (hk : variant.skip ≤ 6) (hc : variant.slices ≠ .claim) (hF : UniComplete.FlockP.FlockHolds κ q) :
    UniComplete.FlockP.PendingSumHolds ((UniComplete.FlockP.flockProve H (14 + κ) variant q).run w).1 :=
  UniComplete.FlockP.pendingSumHolds H κ variant q w hk hc hF fun _ ↦ UniComplete.FlockP.Skip.skipComplete _ hk

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

/-- info: 'UniComplete.FlockP.Skip.skipComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.Skip.skipComplete

/-- info: 'UniComplete.FlockP.pendingSumHolds_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.FlockP.pendingSumHolds_honest
