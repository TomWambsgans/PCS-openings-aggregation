-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's completeness end to end, against
-- `formal/UniStatement/UniStatement/RecSecurity.lean`'s `UniCompletenessRec3` (π1-rec3's verifier
-- `Deployment.verifierRec3With`, `crates/leanvm_univariate`'s `FLOCK_REC3`, `leanvm-rec` 4247e37).
import UniComplete.Rec3Core
import UniComplete.Rec3ProbTFresh
import UniComplete.Rec3ProverSim
import UniComplete.Rec3ProverDuplex
import UniComplete.Rec3ProverCost
import UniComplete.Rec3VerifierHSim
import UniComplete.Rec3VerifierHDuplex
import UniComplete.Rec3VerifierHCost
import UniComplete.Rec3FlockRing
import UniComplete.Rec3FlockSync
import UniComplete.Rec3FlockHonest

/-!
# End-to-end completeness of π1-rec3

**`uniCompletenessRec3_end`**: at the reference deployment (`D.shape = reference`, a program IV of at most `2^16`
bytes), π1-rec3's honest prover `uniProverRec3RP flockProve3H D` (`Rec3Prover.lean`: `α = squares c 4`, Flock's
zerocheck coordinates as squares, the walked lincheck, the batch two variables a round with narrow challenges, three
WHIR openings) is accepted by π1-rec3's deployed verifier (`Deployment.verifierRec3With`) except with probability at
most `deltaRec3 < 2^-167` (`deltaRec3_lt`; about `2^-167.97`), for every input, row counts that fit and witness of
the relation: `UniCompletenessRec3 D (uniProverRec3RP flockProve3H D) deltaRec3`.

**One named hypothesis**, the converse of the walk's lemma (`WalkLemmaConverse`, `Rec3FlockDefs.lean`: the pending
reduction's claim being its sum makes the walk's zero vanish; the `←` of the walk's identity `walk_zero_iff`, proved
on the soundness side, not merged yet).

The bound (`Rec3Prob.lean`'s `deltaRec3`):

| term | event |
|---|---|
| `(2^24 − 1)/2^192` | a bus challenge `β` makes a divided fingerprint vanish (`Core.badFpCard_reference`, any `α`) |
| `3·2^17/2^192` | `y(t)` a proper prefix of another point on `C1` (`Prob.badTCard_reference`) |
| `2^-200` | `t`'s query not fresh (`Rec3ProbTFresh.tQueryFresh3_reference`, 48 chain steps) |
| `2^-304` | an opening's proof of work fails for every nonce (`Rec3ProbGrind.rejectGood3`) |
| `rpmError (2^48)` | the permutation as two random oracles: setup, prover (`2^47`), verifier (`2^42`) |

The main line's `6/2^256` (the five bus answers' repetitions) is gone: π1-rec3 draws two bus answers, the second's
32-byte input always fresh (`Rec3ProbChain.prEvent_staged2_le`).

The layers: the probability layer (`Rec3Prob*.lean`: `uniCompletenessRec3_reference_flockProve3`) from the prover's
facts (`Rec3ProverSim`, `Rec3ProverDuplex`, `Rec3FlockCost`, `Rec3ProverCost`), the verifier's (`Rec3VerifierHSim`,
`Rec3VerifierHDuplex`, `Rec3VerifierHCost`) and the deterministic core (`Rec3Core.coreAccepts3_of`,
`Rec3CoreRun.coreFailsOnlyAtPow3`): the verifier's run synchronises with the prover's stream (`Rec3SyncVerifier`),
Flock's walked step with π1-rec3's Flock prover (`Rec3FlockSync`; its walk's zero vanishes, `Rec3FlockHonest`, from the
named hypothesis), the paired batch's (`Rec3BatchSync`, `Rec3BatchZero`: the honest pair message rebuilt exactly,
`Rec3Pairs.pair_round_complete`, its polynomial computed honestly, `Rec3BatchAlg.pairMsg_honest`), every relation at
`t` holds (the main line's, `Rec3CoreBatch`), and the three openings are WHIR's honest ones.
-/

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

namespace UniComplete.Rec3

/-- Flock's `log_n` on a trace, two spellings. -/
theorem logN_eq3 (tr : Trace) : blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0 = 14 + tr.height 5 := rfl

/-- **Flock's ring switch for π1-rec3's honest Flock prover** (`flockRingSum3`, as `FlockRing3`). -/
theorem flockRing3_flockProve3 (H : List UInt8 → Digest) (logN : ℕ) (q : Array K) :
    FlockRing3 (flockProve3 (m := Id) (Pure.pure ∘ H)) logN q :=
  fun w ↦ flockRingSum3 (Pure.pure ∘ H) logN flockMain q w rfl

/-- **The point of π1-rec3's honest Flock prover has `h_B + 8` coordinates** (`flock3_point_length'`). -/
theorem flockPointLen3_flockProve3 (H : List UInt8 → Digest) (tr : Trace) :
    FlockPointLen3 (flockProve3 (m := Id) (Pure.pure ∘ H)) tr := by
  intro w
  rw [logN_eq3]
  exact flock3_point_length' H tr w

/-- **π1-rec3's honest Flock step at a zero walk** (`flockSyncs3_zero`, from the walk lemma's converse). -/
theorem flockSyncs3_trace (hW : WalkLemmaConverse) (H : List UInt8 → Digest) (tr : Trace) (hon : TraceHonest tr) :
    FlockSyncs3 H (flockProve3 (m := Id) (Pure.pure ∘ H)) (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0)
      flockMain tr.qflock (fun _ ↦ 0) := by
  rw [logN_eq3]
  exact flockSyncs3_zero H hW (tr.height 5) tr.qflock (FlockP.flockHolds_of_traceHonest tr hon)

/-- **π1-rec3's deterministic core** at the reference shape, from the walk lemma's converse: Flock's three facts
for π1-rec3's honest Flock prover (`flockSyncs3_zero`, `flockRingSum3`, `flock3_point_length'`). -/
theorem coreAccepts3_reference (D : Deployment) (hD : D.shape = reference) (hW : WalkLemmaConverse) :
    CoreAccepts3 D flockProve3H :=
  coreAccepts3_of D hD flockProve3H (fun H tr hon _ ↦ flockSyncs3_trace hW H tr hon)
    (fun H tr _ _ ↦ flockRing3_flockProve3 H _ tr.qflock) (fun H tr _ _ ↦ flockPointLen3_flockProve3 H tr)

/-- **End-to-end completeness of π1-rec3 at the reference deployment**, from the walk lemma's converse. -/
theorem uniCompletenessRec3_end (D : Deployment) (hD : D.shape = reference) (hiv : D.programIv.length ≤ 2 ^ 16)
    (hW : WalkLemmaConverse) : UniCompletenessRec3 D (uniProverRec3RP flockProve3H D) deltaRec3 :=
  uniCompletenessRec3_reference_flockProve3 D hD flockCommutes_flockProve3H (proverCommutes3_flockProve3H D)
    (proverDuplex3_flockProve3H D) (proverCost3_flockProve3H D hD hiv) (proverStreamSize3_flockProve3H D hD)
    verifierCommutes3 verifierDisc3 (Cost3.cost_verifierRec3WithH D (2 ^ 40))
    ((Cost3.verifierCost3_le D (hiv.trans (by norm_num))).trans (by norm_num))
    (coreAccepts3_reference D hD hW) (coreFailsOnlyAtPow3 D flockProve3H)

/-- **π1-rec3's bound**: `deltaRec3 < 2^-167` (`deltaRec3_lt_fine`: below `2^-168 + 2^-173`, about `2^-167.96`). -/
theorem deltaRec3_lt' : deltaRec3 < (2 : ℝ≥0∞)⁻¹ ^ 167 := deltaRec3_lt

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.uniCompletenessRec3_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.uniCompletenessRec3_end

/-- info: 'UniComplete.Rec3.coreAccepts3_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.coreAccepts3_reference

/-- info: 'UniComplete.Rec3.deltaRec3_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.deltaRec3_lt
