-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Core
import UniComplete.ProbBadT
import UniComplete.FlockCost
import UniComplete.ProbTFresh

/-!
# End-to-end completeness of the univariate verifier

**`uniCompleteness_end`**: at the reference deployment (`D.shape = reference`, a program IV of at most `2^16`
bytes), the honest prover `uniProverRP flockProveH D` (`uniProverWith` over the random permutation's two calls,
Flock's honest prover `FlockP.flockProve`) is accepted by `Deployment.verifierWith` except with probability at most
`deltaUni < 2^-167` (`deltaUni_lt`; about `2^-167.97`), for every input, row counts that fit (`RowsFit`) and witness
of the relation (`HonestRelation`): `UniCompleteness D (uniProverRP flockProveH D) deltaUni`.

The bad events, each bounded:
* `(2^24 − 1)/2^192`: the bus challenges `β` that make a divided fingerprint vanish (`badFpCard_reference`, at
  most `capBound reference = 10,878,976` per `α`);
* `6/2^256`: two of the five bus challenges' answers collide with earlier queries (the chain's freshness);
* `3·2^17/2^192 + 2^-200`: `t` makes `y(t)` a proper prefix of another point on `C1` (`badTCard_reference`, at
  most `2·2^17` such `t` per Flock point), or the `t` query is not fresh (`tQueryFresh_reference`, below `73 · 2^28 / 2^256`);
* `2^-304`: an opening's proof of work fails for every nonce below `nonceFuel` (`coreFailsOnlyAtPow`);
* `rpmError (2^48)`: the random permutation as two random oracles at `2^48` blocks.

Off the bad events the proof is accepted (`coreAccepts_of`): the verifier's run synchronises with the prover's
stream, every relation holds at `t` (`batchSyncsAt_front`), the batch's terminal is zero, and WHIR's five honest
openings are accepted (`accepts_of_trace`).
-/

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

namespace UniComplete

open Prob

/-- **End-to-end completeness at the reference deployment**, given the batch's hypothesis at the prover's state
(`Core.BatchFront`) and the stacks' sizes (`Core.StackSizes`). -/
theorem uniCompleteness_end_of (D : Deployment) (hD : D.shape = reference) (hiv : D.programIv.length ≤ 2 ^ 16)
    (hbatch : Core.BatchFront) (hsizes : Core.StackSizes) :
    UniCompleteness D (uniProverRP flockProveH D) deltaUni :=
  Prob.uniCompleteness_reference_flockProve D hD hiv (Core.coreAccepts_of D hD hbatch hsizes)
    (Core.coreFailsOnlyAtPow D) (Core.badFpCard_reference D hD) Prob.badTCard_reference (Prob.tQueryFresh_reference D hD)

end UniComplete

/-- info: 'UniComplete.uniCompleteness_end_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.uniCompleteness_end_of
