-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Security

/-!
# End-to-end knowledge soundness as an explicit reduction

`Security.lean`'s Prop-premise form `RecKnowledgeSoundness` takes `Pi1FsKeccak` and `Pi1HazardKeccak`, which quantify
over every `OracleComp` adversary and count only its calls of `π`, `π⁻¹`. π1's challenges are Keccak-f[1600], a fixed
public function such an adversary computes for free, so both are false as stated (`RecCompose/Review/STATEMENT_REVIEW.md`,
finding 3). The statement here takes neither: it is a **reduction**.

For every adversary `A` of `Q` queries against the recursive verifier,

`Pr[the contract accepts ∧ recExtractor fails] ≤ ε2 Q + Pr[pi1Adversary A breaks π1-rec3 at Keccak-f[1600]]
                                                    + Pr[hazardAdversary A hits the merge hazard on an accepted stream]`

with two **explicit derived adversaries** (`def`s, below). Each runs `A` (its queries logged), then π2's explicit
extractor `recExtractor2` on `A`'s output, its transcript and the setup's Keccak-256 evaluations, and outputs:

* `hazardAdversary A`: the public input and the stream π2's extractor outputs (the empty stream if none, which is not
  on the hazard: `RecGraph.MergeHazard` asks that the run draw `t`);
* `pi1Adversary A`: the public input and π1's proof of that stream, with the recursive proof's three π1 opening proofs.

**Their resources** (the conjuncts of `RecKnowledgeSoundnessReduction`): each makes exactly `A`'s calls of `π` and
`π⁻¹`, so at most `Q` (π2's extractor reads the log and the evaluations and makes no query). Their running time is `A`'s
plus π2's extractor's: preimage replay of the log, inversion under `W`'s root, the fast path, the unique decoder and
Guruswami–Sudan list decoding at `W`'s `2^24` words, rate `1/2`, and π1-rec3's graph's checks at Keccak-f[1600] on each
candidate, a polynomial in the log's and the setup's sizes. Lean states the query count; it does not model time.

**The resource the heuristic bounds is their Keccak-f[1600] work**, not `Q`: `A`'s own offline evaluations of
Keccak-f[1600] (free in the model, uncounted by `Q`), plus the extractor's, chiefly π1-rec3's graph's checks at
Keccak-f[1600] on each candidate stream (its Fiat–Shamir: IV, seed, the stream's challenges, Flock's draws). The reader's
Fiat–Shamir premise about these adversaries is a bound in that work; the reduction's `Q` counts only the calls of `π`
and `π⁻¹` (STATEMENT_REVIEW_2.md, finding 6).

The Fiat–Shamir heuristic for Keccak-f[1600] is applied by the reader, to these two adversaries: π1-rec3's
random-permutation theorem (`UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`) for the first, `RecGraph.hazard_prob`
(`2^19/|E|` a uniform `t`) for the second.
-/

namespace RecStatement

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## The derived adversaries -/

/-- **The hazard's adversary built from `A`**: it runs `A` (its queries logged), then outputs the public input and the
stream π2's extractor outputs on `A`'s output, transcript and the setup's evaluations (none: the empty stream, which
is not on the hazard). -/
def hazardAdversary (D : RecDeployment) (A : RecAdversary) : Pi1StreamAdversary :=
  fun roots evals ↦ do
    let (z, T) ← (simulateQ loggedOracles (A roots)).run []
    return (z.1, (recExtractor2 D roots z.1 evals T z.2).getD #[])

/-- **π1-rec3's adversary built from `A`**: it runs `A` (its queries logged), then outputs the public input and π1's
proof of the stream π2's extractor outputs, with the recursive proof's three π1 opening proofs. -/
def pi1Adversary (D : RecDeployment) (A : RecAdversary) : Pi1Adversary :=
  fun roots evals ↦ do
    let (z, T) ← (simulateQ loggedOracles (A roots)).run []
    return (z.1, z.2.pi1Proof ((recExtractor2 D roots z.1 evals T z.2).getD #[]))

/-! ## The reduction -/

/-- **Knowledge soundness of the recursive verifier against leanVM 42422001's relation, end to end, as a reduction**
(π2's verifier and the six openings; the explicit extractor `recExtractor`: π2's, then π1-rec3's). For every adversary
`A` of `Q` calls of `π` and `π⁻¹`:

* the derived adversaries `pi1Adversary D A` and `hazardAdversary D A` make at most `Q` calls of `π` and `π⁻¹` (they
  are `A` followed by π2's extractor, which makes none);
* the contract accepts while `recExtractor` finds no row counts and stack satisfying `M3Holds` with probability at most
  `ε2 Q` (π2's part, in the random-permutation model) plus the probability that `pi1Adversary D A` breaks π1-rec3 with
  its Fiat–Shamir over Keccak-f[1600] (`pi1KeccakSoundnessExperiment`, for π1-rec3's extractor `uniExtractor`) plus the
  probability that `hazardAdversary D A` outputs a stream π1-rec3's graph accepts whose run hits the merge hazard
  (`pi1HazardExperiment`, `Pi1HazardAccepted`).

No Fiat–Shamir hypothesis: bounding the last two terms for these two explicit adversaries is the Fiat–Shamir heuristic
for Keccak-f[1600], which the reader applies. -/
def RecKnowledgeSoundnessReduction (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    (∀ roots evals, QueryCostAtMost (pi1Adversary D A roots evals) permutationCallCost Q) ∧
    (∀ roots evals, QueryCostAtMost (hazardAdversary D A roots evals) permutationCallCost Q) ∧
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D (recExtractor D) z] ≤
      ε2 Q +
        Pr{let z ← pi1KeccakSoundnessExperiment D (pi1Adversary D A)}[
          UniStatement.UniBreaksKnowledgeSoundness D.pi1 (UniStatement.uniExtractor D.pi1) z] +
        Pr{let z ← pi1HazardExperiment D (hazardAdversary D A)}[Pi1HazardAccepted z.1 z.2.1 z.2.2]

end RecStatement
