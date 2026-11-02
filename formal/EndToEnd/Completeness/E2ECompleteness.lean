-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.Chain
import E2ECompleteness.Transfer
import E2ECompleteness.Regular
import E2ECompleteness.End
import E2ECompleteness.WithHash
import E2ECompleteness.Experiment
import E2ECompleteness.Staging
import E2ECompleteness.HashLen
import E2ECompleteness.Assemble
import E2ECompleteness.Duplex
import E2ECompleteness.Grinding
import E2ECompleteness.Final
import E2ECompleteness.Closed

/-!
# `PcsQuotient.Completeness`, end to end

The completeness statement of `formal/Statement` (`PcsQuotient.Completeness δ`: the setup, uniform
coins, the honest `prover` and the `verifier`, in one random permutation) proved from the proof
layers, with an explicit `δ`:

* `Chain.lean`: the reduction's challenges `(α, β, t)` in the two-call random-oracle model, fresh
  by their lengths (`prEvent_staged_le`: in a set `Bad` with probability at most
  `|Bad| / 2^576 + 2 / 2^256`);
* `Transfer.lean`: the random permutation is two random oracles to an honest computation following
  the duplex discipline, up to `N² / 2^508` (`rpm_le_rom`, from mumbai's indifferentiability);
* `End.lean`: `completeness_of_staged`, `PcsQuotient.Completeness` at
  `(17 · 2^24 + 8) / 2^192 + 2 / 2^256 + εpow + N² / 2^508`, the degenerate challenges those of
  `formal/Completeness` (`completeness_deployed_concrete`), given the staged form of the
  experiment (`Staged.Holds`); `completeness_deployed`, at `N = 2^48`, `εpow = 3 · 2^-277`,
  `δ < 2^-162` (`deltaDeployed_lt`).

* `Regular.lean`: the transcript's challenge (`challengeOf`, the digest's bytes `8 … 31` read
  big-endian) has at most `2^64` digests per value (`challengeOf_regular`).
* `Grinding.lean`: the grinding at non-degenerate challenges, `RejectGood (3 · 2^-277)`
  (`rejectGood_deployed`), from the block count and the Prover bridge, by mumbai's proof-of-work
  potential over the whole run's log;
* `Final.lean`: **`completeness_deployed_final`**, `PcsQuotient.Completeness deltaDeployed` with
  `deltaDeployed < 2^-162`.

* The Prover bridge (`Prover*.lean`): the Statement's honest prover is accepted at non-degenerate
  challenges. `ProverDefs`, `ProverRun`: the prover's computations named, the prover at functions
  `H`, `F`; `ProverOpening`: its WHIR opening makes mumbai's honest opening's moves and is accepted
  (`corr_openingScript`, `openingAccepts_layouts`); `ProverStack`: its hidden stacks make the stack
  claims true; `ProverTables`, `ProverQuotient*`: its NTT and coset tables are `formal/Completeness`'s;
  `ProverValues`, `ProverClaims`, `ProverStatement`: its values, claims and target are Completeness's;
  `ProverAccept`: `accept_core`, `reduce_honest`; `ProverStaged`, `ProverBridge`: on the staged run,
  `acc_staged`, `red_staged`; `ProverConstants`, `ProverFacts`, `ProverTablesMatch`: the constants,
  the claims and the tables discharged.
* `Closed.lean`: **`completeness_deployed_of_circuit`**, `PcsQuotient.Completeness deltaDeployed`
  from the block count and `CircuitMatch`.

What stays a hypothesis: the block count of the deployed staged run (`2^48`, `Common.QueryCostAtMost
… hashBlocks`), and the Prover bridge's `CircuitMatch` (the membership circuit's cells and wiring are
F0b's). See the completeness section of `formal/README.md`.
-/

/-- info: 'E2ECompleteness.challengeOf_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.challengeOf_regular

/-- info: 'E2ECompleteness.prEvent_staged_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.prEvent_staged_le

/-- info: 'E2ECompleteness.rpm_le_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.rpm_le_rom

/-- info: 'E2ECompleteness.badSet_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.badSet_density

/-- info: 'E2ECompleteness.completeness_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_of_staged

/-- info: 'E2ECompleteness.deltaDeployed_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.deltaDeployed_lt

/-- info: 'E2ECompleteness.completeness_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_deployed

/-- info: 'E2ECompleteness.completenessExperiment_eq_expH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completenessExperiment_eq_expH

/-- info: 'E2ECompleteness.expH_eq_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.expH_eq_staged

/-- info: 'E2ECompleteness.completeness_deployed_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_deployed_staged

/-- info: 'E2ECompleteness.duplexVm_stagedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.duplexVm_stagedRun

/-- info: 'E2ECompleteness.completeness_deployed_cost_rej' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_deployed_cost_rej

/-- info: 'E2ECompleteness.acc_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.acc_staged

/-- info: 'E2ECompleteness.red_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.red_staged

/-- info: 'E2ECompleteness.constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.constants

/-- info: 'E2ECompleteness.claimsMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.claimsMatch

/-- info: 'E2ECompleteness.tablesMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.tablesMatch

/-- info: 'E2ECompleteness.openingAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.openingAccepts

/-- info: 'E2ECompleteness.completeness_deployed_of_circuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_deployed_of_circuit
