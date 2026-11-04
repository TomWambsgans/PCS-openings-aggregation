-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Basic
import RecCompose.IvLength
import RecCircuit

/-!
# π2's part: `RecKnowledgeSoundness2`, from π2's layers

`recKnowledgeSoundness2_of_layers`: `RecStatement.RecKnowledgeSoundness2 D ε2` (if the contract accepts, π2's
extractor outputs π1's stream, on which π1-rec3's recorded graph run with Keccak-f[1600] accepts, its three calls the
contract's), from two named inputs:

* **`Pi2Layers D ε2`**: π2's circuit as the Lean compiler builds it from π1-rec3's recorded graph at each π1 IV
  (`RecCircuit.compile`, `RecCircuit.Circuit.toPiop`), public limbs of its ports read off the statement, and two
  layers on them:
  - `extraction` (**π2's Fiat–Shamir, openings and PIOP**, `Pi2Extraction`): if the contract accepts, some candidate
    of `W`'s committed word (as π2's extractor lists them) has witness values satisfying the circuit's relation
    (`RecPiop.Circuit.Satisfies`), but with probability `ε2 Q`. Its route: `Compose.ListChainU128` for π2's three
    rounds, `Compose.prEvent_doomF_le` for π2's three openings, `RecPiop.piop` for the rounds' errors,
    `RecStatement.checks_claims_iff_post2` for the verifier's arithmetic (`RecCompose.Pi2Layers`, `Numbers.lean`);
  - `circuit` (**the circuit computes π1-rec3's graph**): a witness satisfying the circuit, for the public limbs of
    `(roots, input, stream)`, holds a π1 stream (`D.pi1Stream`, RecCircuit's `decodeStream`) on which π1-rec3's graph
    over Keccak-f[1600] accepts with the openings the contract makes on that calldata (`pi1OpsOf`). This is
    `RecCircuit`'s end corollary: `compile_sound`, `SoundRG`'s `compile_sound_statement`, `_root`, `_element`,
    `_zero_rg` and `agree` (proved), with **`ExpandSound`** and the **`call_inputs`** correspondence (branch
    `lean-rec-circuit`, open).
* **`CallsPure D`**: on every outcome of π2's experiment the contract accepts, its first three calls decode under the
  registry to `pi1OpsOf` (π2's run over Keccak-f[1600] on the calldata: π1's calls read the stream's public data, not
  the transcript's hashes).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-- **The contract's π1 openings are the calldata's**: on every outcome of π2's knowledge-soundness experiment whose
contract accepts, the first three calls decode under the registry, to the openings `pi1OpsOf` reads off the calldata
(π2's run over Keccak-f[1600]). π1's three calls read only the stream's public data (π1's roots, its claims' elements
and their pair points) and the setup's root, not the transcript's hashes; the contract's `PCS_OPEN` rejects a call
that does not decode. -/
def CallsPure (D : RecDeployment) : Prop :=
  ∀ (A : RecAdversary), ∀ z ∈ support (recSoundnessExperiment2 D A), (acc z) = true →
    ∃ ops, pi1OpsOf D (rts z) (inp z) (prf z).stream = some ops ∧
      contractPi1Openings (registryAt D (rts z)) (cls z) = some ops

/-- **π2's extraction for a relation `Rel` of `W`'s candidates**: in π2's experiment, the contract accepts while no
candidate of `W`'s committed word (read off the setup's evaluations and the transcript, decoded as π2's extractor
decodes it) has witness values in `Rel`, with probability at most `ε2 Q`. -/
def Pi2Extraction (D : RecDeployment) (Rel : RecSetupRoots → Vector UInt8 32 → Array UInt8 → (ℕ → K) → Prop)
    (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment2 D A}[(acc z) = true ∧
      ¬ ∃ w ∈ outcomeCandidates D z, Rel (rts z) (inp z) (prf z).stream (witnessOf D (rts z) w)] ≤ ε2 Q

/-- **π2's layers**: π2's circuit as the Lean compiler builds it from π1-rec3's recorded graph at every 32-byte π1 IV
(π1's contract IV is a Keccak-256 digest, `RecDeployment.pi1IvAt_length`), the public limbs of its ports for a
statement, π2's extraction for that circuit's relation, and the circuit's corollary.

* `rootsAt`, `compiled`, `compile_ok`: the compiler's input (π1's roots' stream offsets, the IV) and output, at every
  32-byte IV; checked by evaluation at three IVs (`rec-real-check`, `RecComposeTest/RealCheck.lean`), not in the
  kernel (no kernel evaluation of the `2^24`-position circuit), and assumed at the others;
* `stream_eq`: the deployment's π1 stream is the compiler's decoding of the witness's free bits, `streamW`
  (`decodeStream` of the witness's values `ctx.val w`; `RecDeployment`'s docstring: `pi1Stream` is meant to be
  RecCircuit's `decodeStream`), at every 32-byte IV;
* `pub`: port `J`'s public limbs, for the setup's roots, the public input and π2's stream (the statement's four
  words, π1's roots' limbs, π1's claims' elements, zeros);
* `extraction` (**open, `lean-rec-compose`**): π2's Fiat–Shamir layer, openings, PIOP and tables' layer;
* `circuit` (**open, `lean-rec-circuit`**: `ExpandSound` and `call_inputs`): a satisfying witness holds a π1 stream
  π1-rec3's graph accepts with the contract's openings. -/
structure Pi2Layers (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) where
  rootsAt : List ℕ
  compiled : List UInt8 → RecCircuit.Compiled
  compile_ok : ∀ iv, iv.length = 32 →
    RecCircuit.compile (RecCircuit.ofRG RecGraph.Pi1.pi1Graph rootsAt iv) = .ok (compiled iv)
  stream_eq : ∀ iv, iv.length = 32 → ∀ (w : ℕ → K),
    D.pi1Stream w = ((compiled iv).streamW (RecCircuit.ofRG RecGraph.Pi1.pi1Graph rootsAt iv) w).toArray
  pub : RecSetupRoots → Vector UInt8 32 → Array UInt8 → ℕ → List Primitives.F192
  extraction : Pi2Extraction D (fun roots input stream w ↦
    ((compiled (D.pi1IvAt roots.pi1)).circuit.toPiop).Satisfies (pub roots input stream) (RecCircuit.emb w)) ε2
  circuit : ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) (w : ℕ → K)
    (ops : List Pi1Opening),
    ((compiled (D.pi1IvAt roots.pi1)).circuit.toPiop).Satisfies (pub roots input stream) (RecCircuit.emb w) →
      pi1OpsOf D roots input stream = some ops →
        Pi1GraphAccepts (D.pi1IvAt roots.pi1) input (D.pi1Stream w) ops

/-- **π2's part, from π2's layers**: `RecKnowledgeSoundness2 D ε2`. -/
theorem recKnowledgeSoundness2_of_layers {D : RecDeployment} {ε2 : ℕ → ℝ≥0∞} (L : Pi2Layers D ε2)
    (hpure : CallsPure D) : RecKnowledgeSoundness2 D ε2 := by
  intro A Q hQ
  refine (prEvent_mono_of_support _ _ _ ?_).trans (L.extraction A Q hQ)
  rintro z hz ⟨hacc, hno⟩
  refine ⟨hacc, fun ⟨w, hw, hrel⟩ ↦ hno ?_⟩
  obtain ⟨ops, hops, hcon⟩ := hpure A z hz hacc
  obtain ⟨s, hs, hsacc⟩ := recExtractFrom2_of_mem D (rts z) (inp z) _ (prf z) ops hops w hw
    (L.circuit _ _ _ _ ops hrel hops)
  exact ⟨s, ops, hs, hcon, hsacc⟩

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness2_of_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_of_layers
