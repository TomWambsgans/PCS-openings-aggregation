<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The structure follows leanerVM's `Statement/README.md` (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0). -->

# Statement

What `crates/quotient` is to be proved to be, in the files a reviewer reads: **definitions and end
statements only**, no proof, one Lake package (`pcs-quotient-statement`, library `PcsQuotient`) of eleven
files, `PcsQuotient/<Name>.lean` (Lean modules `PcsQuotient.<Name>`). It depends on leanerVM's
`Statement/` package (`statement`, branch `mumbai`, commit `6175f1a0`), whose definitions it reuses
rather than restates: `K = GF(2^64)` and `E = GF(2^192)`, Keccak-f[1600] and Keccak-256 over any
permutation, the random-permutation model, leanVM's WHIR verifier and the pieces of its prover, and its
extractor's Merkle inversion and list decoder. Mathlib, VCVio and CompPoly come through it, at mumbai's
revisions (the toolchain is `leanprover/lean4:v4.34.1`).

The extractor and the simulator are **explicit, computable definitions** referenced by the statements, so
that a reviewer can check what they read and that they are efficient (Lean has no running-time theorem;
the convention is mumbai's: a fixed straight-line extractor reading only the adversary's transcript, its
cost read off its loops). The proofs are to come (`formal/README.md`, layers F1–F5); `PcsQuotientTest/`
is the differential test, not part of the statement.

**The model.** Every end statement with an adversary is in mumbai's random-permutation model: one
uniformly random permutation `π` of the 1600-bit Keccak state, which every party queries forward (`π x`)
and inverse (`π⁻¹ y`), Keccak-256 the sponge over `π`. Every hash of the protocol is Keccak-256 over `π`:
the reduction's chain, the WHIR commitments' Merkle trees and the openings' duplex, and the circuit's
commitment, which a **setup** computes over `π` before the adversary runs (deployed, the verifier holds
it as a constant computed over Keccak-f[1600]). The **relation** is about the deployed Keccak-256: the
circuit computes Keccak-f[1600] on bits, independent of `π` in the model (mumbai's convention for
leanVM's `KECCAK` instruction). That the deployed Keccak-f[1600] behaves as a random permutation is the
assumption. The adversary is classical, its code fixed before `π` is sampled.

**The sources.** Each definition cites the Rust it transcribes (`protocol.rs:N`, `circuit.rs:N`, …) of
`crates/quotient`, and each file names what it takes from leanerVM in its first lines.

## Reading order

1. [`Relation.lean`](PcsQuotient/Relation.lean): the statement (`Statement`: `y`, `root`), the secret
   (`Secret`: `x`, the `32` siblings, the `32` directions), and **`Relation`**: `y = H(x ‖ 0x11^32)` and
   the path from `H(x ‖ 0x22^32)` folds to `root`, `H` the deployed Keccak-256 of a 64-byte block
   (`statement.rs`).
2. [`Domain.lean`](PcsQuotient/Domain.lean): the Cantor basis `β₀ … β₂₇` of `K` (computed as the Rust
   computes it), the cells' points `B(i)`, the subspace polynomials `w_k = S^k`, the constants the
   verifier reads (`coordinates`, `rowVanishing`), and the additive transform between a polynomial's
   novel-basis coefficients and its values on a coset (`values`, `coefficients`) that the prover and the
   extractor use (`domain.rs`).
3. [`Transcript.lean`](PcsQuotient/Transcript.lean): the reduction's Fiat–Shamir transcript, a
   Keccak-256 chain over a permutation `F` (`transcript.rs`).
4. [`Reduction.lean`](PcsQuotient/Reduction.lean): **the reduction's proof** (`ReductionProof`: two
   roots, each as its two halves, and five elements of `E`), the four **claims** (`Claims`), and the
   reduction's verifier (`reduceWith`, `claimsAt`: `reduce` of `protocol.rs` line by line, with its
   constants: the label, the public weight's coordinate weights, the extension's coordinates, the sum's
   point).
5. [`Opening.lean`](PcsQuotient/Opening.lean): the tables' layouts (`witnessLayout`, `wiringLayout`,
   `quotientLayout`), a claim's weight on a stack (`stackWeight`), and **the opening check**
   (`openingWith`): mumbai's WHIR verifier `verifyStackedOpening`, which is generic in the weight, run
   with the root given as commitment `0` and the sponge seeded as `opening.rs` seeds it.
6. [`Verifier.lean`](PcsQuotient/Verifier.lean): **the proof** (`Proof`: the reduction's proof and three
   WHIR opening proofs in mumbai's format) and **the verifier** (`verifyWith`): the reduction, then the
   three openings, as `protocol::verify` then `verify_openings`.
7. [`Circuit.lean`](PcsQuotient/Circuit.lean): the circuit (the gate `V = X + C + Y·C`, the builder,
   Keccak-f[1600] on wires, the membership statement `membership`, the wiring `σ`), its cells from the
   inputs, and **its commitment** (`Circuit.indexRootWith`: the wiring table committed by WHIR over `F`).
8. [`Prover.lean`](PcsQuotient/Prover.lean): **the honest prover** (`proveWith`, `proverWith`):
   `protocol::prove` then `open`, its WHIR openings by mumbai's WHIR prover pieces on this protocol's
   weight table (`openingScript`), run against the verifier's program (mumbai's `runFrom`).
9. [`Extractor.lean`](PcsQuotient/Extractor.lean): **the extractor** (`transcriptExtractorFor`), with its
   cost table.
10. [`Simulator.lean`](PcsQuotient/Simulator.lean): **the simulator** (`Simulator.simulateFor`,
    `Simulator.simOracle`).
11. [`Security.lean`](PcsQuotient/Security.lean): the deployed system (`setupWith`, `verifier`,
    `deployedIndexRoot`, `deployedVerifier`), the experiments, and **`KnowledgeSoundness`,
    `Completeness`, `ZeroKnowledge`**, collected in `Theorems`.

## The end statements

As written in [`Security.lean`](PcsQuotient/Security.lean) (`PcsQuotient` namespace; `logRows = 22`):

```lean
noncomputable def soundnessExperiment (A : Adversary) : ProbComp Outcome :=
  runWithRandomPermutation do
    let indexRoot ← setupWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles A).run []
    let accepted ← verifier queryPermutation indexRoot z.1 z.2
    return ((z, accepted), transcript)

def BreaksKnowledgeSoundness (z : Outcome) : Prop :=
  z.accepted ∧ ¬ ∃ w, extractor z.statement z.transcript z.proof = some w ∧ Relation z.statement w

def KnowledgeSoundness (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), QueryCostAtMost A permutationCallCost Q →
    Pr{let z ← soundnessExperiment A}[BreaksKnowledgeSoundness z] ≤ ε Q

noncomputable def completenessExperiment (stmt : Statement) (w : Secret) : ProbComp Bool :=
  runWithRandomPermutation do
    let indexRoot ← setupWith queryPermutation
    let masks ← sampleMasks
    match ← prover queryPermutation stmt w masks with
    | none => return false
    | some proof => verifier queryPermutation indexRoot stmt proof

def Completeness (δ : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
    Pr{let v ← completenessExperiment stmt w}[v = false] ≤ δ

noncomputable def realExperiment (stmt : Statement) (w : Secret) (D : Distinguisher) :
    ProbComp Bool :=
  runWithRandomPermutation do
    let masks ← sampleMasks
    D (← prover queryPermutation stmt w masks)

def idealExperiment (stmt : Statement) (D : Distinguisher) : ProbComp Bool :=
  (do
    let proof ← simulator stmt
    simulateQ Simulator.simOracle (D proof)).run' {}

def ZeroKnowledge (ζ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
  ∀ (D : Distinguisher) (Q : ℕ), (∀ proof, QueryCostAtMost (D proof) permutationCallCost Q) →
    Pr{let b ← realExperiment stmt w D}[b = true] ≤
        Pr{let b ← idealExperiment stmt D}[b = true] + ζ Q ∧
      Pr{let b ← idealExperiment stmt D}[b = true] ≤
        Pr{let b ← realExperiment stmt w D}[b = true] + ζ Q
```

`Adversary` is `OracleComp RandomPermutationOracles (Statement × Proof)` (coins, `π`, `π⁻¹`);
`Distinguisher` is `Option Proof → OracleComp RandomPermutationOracles Bool`, quantified after the
statement and the witness (non-adaptive zero knowledge). `QueryCostAtMost`, `permutationCallCost`,
`runWithRandomPermutation`, `loggedOracles`, `queryPermutation` are mumbai's (`RandomPermutation.lean`).

**The bounds are parameters**, `ε`, `δ`, `ζ`: they are not yet known, and the end theorem will fix them
(a statement at `ε = 1` says nothing). The targets, by analogy with mumbai's `LeanVM.KnowledgeSoundness`:
`ε Q` of the form `(Q + c)·2^-k + 5(Q + c)²·2^-256` with `k` near `128` and `c` covering the setup's and
the verifier's own calls of `π` (the setup alone makes `2^21 + 2^19 − 1`: `2^19` leaves of four blocks and
`2^19 − 1` nodes); `δ` below `2^-128` (a vanishing denominator, about `2^26·2^-192`, or a proof of work
with no nonce among `2^25`, about `e^-256` each); `ζ Q` of the form `(Q + c)·2^-k`.

## The extractor

`extractor stmt T proof` (`Security.lean`) is `transcriptExtractorFor (membership logRows)`
(`Extractor.lean`). **It reads** the statement, the proof's first two scalars (the witness table's root)
and the adversary's transcript `T`, and nothing else: it neither queries `π`, nor sees the setup's or the
verifier's queries, nor runs the adversary again. From `T`'s forward queries it replays the Keccak-256
evaluations whose whole sponge path the adversary queried (mumbai's `keccakEvaluationsOfTranscript`),
inverts the witness table's Merkle tree under the root through them (mumbai's `committedLeaves`: `2^20`
leaves of `64` words), lists the candidate stacks within the Johnson radius of the word (mumbai's
`fastStacks`, by interpolation for a word without errors, then `decodeStacks`, CompPoly's Guruswami–Sudan
list decoder over `K` with prefix pruning, at most `2^18` candidates), takes each candidate's cells'
polynomial to the cells' values (`Domain.values`) and reads the input rows' `V` cells as bits, and
returns the first candidate's secret that satisfies the relation. **Its cost** (its loops; not proved):
`N` evaluations in the transcript, then `2^21` scans of `N` pairs to invert the tree; `64` additive
transforms of `2^20` on the fast path; the list decoder as mumbai's cost table (infeasible at deployed
sizes, as mumbai's own); per candidate one transform of `2^24` and `33` Keccak-256.

## The simulator

`simulator stmt` (`Security.lean`) is `Simulator.simulateFor (membership logRows) (2^25)`; together with
`Simulator.simOracle`, which answers every query of the distinguisher from the simulator's tables of
`π` (fresh queries by uniform states: a random function, which differs from a permutation on a collision
only). **It reads** the statement and its own coins, never the witness. It is the **honest prover on
fake tables, with oracle programming**:

1. the circuit's commitment honestly (public);
2. the two roots as uniform digests, fixed first; the Keccak-256 chain run honestly over its `π`
   (`α, β, γ`, `t`, `ρ`);
3. the four values **uniform** (in `K` when the row of `t` is in `K`, else in `E`: `simValues` of
   `formal/`'s reduction simulator), `next` honestly; the verifier's four claims;
4. each committed table **uniform on its layout conditioned on its claims** (`fakeStack`: the last
   `3·#claims` entries solved for, the claims being linear over `K` limb by limb);
5. each fake table's tree built honestly up to the root's children, and `π` **programmed** at the
   root node's input so that the tree's root is the one drawn in step 2 (`programmedTree`);
6. the honest WHIR prover on the fake tables, and on the public wiring table.

Its cost is the honest prover's openings and commitments on tables of the same sizes, plus one
uniform word per table entry and a Gauss–Jordan elimination of six unknowns. Its proof of any statement
(true or not) is accepted by the verifier querying the simulator's `π` (the self-test checks it on a small
circuit, for a false statement).

## What is assumed, and what remains

**Trusted**, as in mumbai: the Lean kernel; mumbai's definitions this package reuses (Keccak-256, the
model, `verifyStackedOpening` as leanVM's WHIR verifier, its prover's pieces, its extractor's decoder;
mumbai tests its verifier against leanVM's on mutated proofs); that the deployed Keccak-f[1600] behaves
as a random permutation. **Tested, not proved**, that these definitions are the Rust: the differential
test (below).

**Deviations from the Rust**, each documented where it is:

* The WHIR proofs are in mumbai's format, one full Merkle path per query (the raw form of
  `verifier::MerkleOpenings`); the Rust prover ships pruned paths, which the Rust verifier expands. The
  expansion is not formalized (as in mumbai).
* The reduction's proof is a structure of nine scalars rather than a stream; a stream of another length
  (rejected by the Rust) is no proof.
* The verifier inverts its denominators one by one after checking that none is zero; the Rust inverts
  their product by the norm to `K` (same values).
* The EVM contract (`crates/evm`) is the reduction only; tying it to `reduceWith` is layer F5.

**To be proved** (`formal/README.md`):

* `KnowledgeSoundness ε`: the reduction's round-by-round soundness (F1, ported from leanVM's
  `formal/quotient` with ideal commitments), WHIR's soundness for this weight (F2, mumbai's `Whir/Sound`
  for any multiaffine weight), the composition in the model with extraction from the transcript (F4,
  mumbai's `common` and `lean_vm` extraction), and the circuit argument (inputs are bits, every other cell
  computed; `formal/QuotientSecurity/Circuit.lean` for the BLAKE2s circuit).
* `Completeness δ`: the honest prover's claims hold (F1's completeness) and its WHIR openings are
  accepted (mumbai's completeness of its WHIR prover), with the proofs of work.
* `ZeroKnowledge ζ` **is not true of the current prover**: its tables are not padded, and its openings
  reveal codeword symbols of the witness table (F3, not built in Rust). It is stated for the honest
  prover as defined so that it becomes provable when the prover pads its tables, the verifier, the
  simulator and the statement unchanged; the simulator's step 4 is the distribution the padding must give
  the opened information.

## Building and testing

On a machine with the dependencies (Mathlib and the rest at mumbai's revisions):

```sh
lake build                                   # the statement: PcsQuotient
lake build differential                      # the test

# vectors from the Rust (from the repository root): reductions, whole proofs (honest and tampered),
# circuit commitments, the honest prover's streams; --index adds the membership circuit's commitment
cargo run --release -p quotient --example statement_vectors -- vectors.txt --index
.lake/build/bin/differential vectors.txt     # Lean's verdicts, claims, commitments and streams vs Rust's
.lake/build/bin/differential --self-test     # the extractor on an honest commitment, the simulator
```

The test (`PcsQuotientTest/Differential.lean`) checks, line by line: on random nine-scalar streams at
`2^13`, `2^17` and `2^22` rows (some malformed) and on honest streams, that `reduceWith` gives the Rust's
two roots and four claims or rejects as it does (`R`); on whole proofs of a small circuit, honest and
tampered fourteen ways (values, roots, statement, circuit commitment, WHIR scalars, leaves, siblings,
missing, extra and short paths), that `verifyWith` gives the Rust's verdict (`P`); that the Lean builder
and commitment give the Rust circuits' sizes and commitments, the membership circuit's at `2^22` rows
included (`I`, about five minutes); and that the Lean prover, given the Rust prover's masks, sends the
Rust prover's stream and its proof is accepted (`Q`).
