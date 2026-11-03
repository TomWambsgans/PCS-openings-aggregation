-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.FlockProverTerminal
import UniComplete.FlockProverSync
import UniComplete.FlockProverRing

/-!
# Flock's honest prover: the headline theorems and their axioms

`UniComplete.FlockP.flockProve H : FlockProver m` (`FlockProver.lean`), at a pure Keccak-256 `H` (`Id`), every writer
(any challenges), on `q_flock`'s words `q`:

* `pendingTerminalHolds` (`k ≤ 6`, `log_n ≥ 14`, the slices sent): `PendingTerminalHolds`;
* `flockSyncs` (the slices sent): `FlockSyncs H (flockProve (pure ∘ H)) log_n variant q` (`SyncBasic`'s statement);
* `flockRingHolds` (tower order): `FlockRingHolds`.

The guards below fail the build if a theorem's axioms grow beyond Lean's three.
-/

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
