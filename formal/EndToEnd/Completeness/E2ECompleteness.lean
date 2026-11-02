-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.Chain
import E2ECompleteness.Transfer
import E2ECompleteness.End

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

What stays a hypothesis: `Regular challengeOf` (the transcript's challenge, the low 192 bits of a
digest, has at most `2^64` digests per value) and `Staged.Holds` for the Statement's experiment
(its two-call staged form, the duplex discipline, the block count, the chain's lengths, and the
grinding at non-degenerate challenges). See the completeness section of `formal/README.md`.
-/

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
