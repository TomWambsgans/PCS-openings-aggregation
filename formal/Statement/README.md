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
cost read off its loops). They are not F1's (`formal/QuotientSecurity`), whose extractor reads the proof's
polynomials in the ideal model and whose extractor and simulator are `noncomputable`. The proofs are to
come (`formal/README.md`, layers F0–F5); `PcsQuotientTest/` is the differential test, not the statement.

**The model.** Every end statement with an adversary is in mumbai's random-permutation model: one
uniformly random permutation `π` of the 1600-bit Keccak state, which every party queries forward (`π x`)
and inverse (`π⁻¹ y`), Keccak-256 the sponge over `π`. Deployed, **one Keccak-256** serves the reduction's
chain, the WHIR Merkle trees (`hash_pair` is byte for byte the relation's `pair`), the openings' duplex,
the circuit's commitment and the relation. In the model every hash of the protocol is Keccak-256 over the
one `π` (there is no private oracle), the circuit's commitment computed over `π` by a **setup** before the
adversary runs (deployed, the verifier holds it as a constant computed over Keccak-f[1600]); the
**relation** is over the deployed Keccak-256, which the circuit computes on bits, independent of `π` in the
model (mumbai's convention for leanVM's `KECCAK` instruction), with a **collision clause** where a statement
reads more than the relation (`StatementBinds`, as mumbai's `DigestBinds`). That the deployed Keccak-f[1600]
behaves as a random permutation is the assumption. The adversary is classical, its code fixed before `π`
is sampled.

**The sources.** Each definition cites the Rust it transcribes (`protocol.rs`, `opening.rs`,
`circuit.rs:N`, …) of `crates/quotient` at `main` `f4319d6` (the hidden layouts of
`crates/quotient/HIDING.md`, the sizes `2^17` to `2^22` rows, the opening transcript of version `2`), and each
file names what it takes from leanerVM in its first lines.

## Reading order

1. [`Relation.lean`](PcsQuotient/Relation.lean): the statement (`Statement`: `y`, `root`), the secret
   (`Secret`: `x`, the `32` siblings, the `32` directions), and **`Relation`**: `y = H(x ‖ 0x11^32)` and
   the path from `H(x ‖ 0x22^32)` folds to `root`, `H` the deployed Keccak-256 of a 64-byte block
   (`statement.rs`). This is Keccak-256 membership itself, not a circuit's satisfiability.
2. [`Domain.lean`](PcsQuotient/Domain.lean): the Cantor basis `β₀ … β₂₇` of `K` (computed as the Rust
   computes it), the cells' points `B(i)`, the subspace polynomials `w_k = S^k`, the constants the
   verifier reads (`coordinates`, `rowVanishing`) **with their defining properties** (`IsCantorBasis`,
   `CoordinatesRead`, `RowVanishingProperty`, decidable, checked in `PcsQuotientTest/Constants.lean`), and
   the additive transform between a polynomial's novel-basis coefficients and its values on a coset
   (`values`, `coefficients`) that the prover and the extractor use (`domain.rs`).
3. [`Transcript.lean`](PcsQuotient/Transcript.lean): the reduction's Fiat–Shamir transcript, a
   Keccak-256 chain over a permutation `F` (`transcript.rs`).
4. [`Reduction.lean`](PcsQuotient/Reduction.lean): **the reduction's proof** (`ReductionProof`: two
   roots, each as its two halves, and five elements of `E`), the four **claims** (`Claims`), **the
   statement embedding** (`statementWords`: `y` and `root` as their halves, big-endian in the low two
   limbs, then `1, 0, 0, 0`), the sizes (`Supported`: `2^17` to `2^22` rows), and the reduction's verifier
   (`reduceWith`, `claimsAt`: `reduce` of `protocol.rs` line by line, with its constants: the label, the
   bit weights `bitWeight`, the coordinate weights, the extension's coordinates, the sum's point).
5. [`Opening.lean`](PcsQuotient/Opening.lean): the tables' layouts (the public `wiringLayout`; the
   **hidden** `witnessLayout`, `quotientLayout`: padded first pieces, an overflow lane, random lanes, and the
   gadget weight `gadgetWeight`, a claim of value zero,
   `Layout.hidden`), a claim's weight on a stack (`stackWeight`), the read-back of a table from its stack
   (`Layout.readEntry`), and **the opening check** (`openingWith`): mumbai's WHIR verifier
   `verifyStackedOpening`, which is generic in the weight, run with the root given as commitment `0` and
   the sponge seeded as `opening.rs` seeds it.
6. [`Verifier.lean`](PcsQuotient/Verifier.lean): **the proof** (`Proof`: the reduction's proof and three
   WHIR opening proofs in mumbai's format) and **the verifier** (`verifyWith`): the reduction, then the
   three openings, as `protocol::verify` then `verify_openings`.
7. [`Circuit.lean`](PcsQuotient/Circuit.lean): **the circuit** (the gate `V = X + C + Y·C`, the builder,
   Keccak-f[1600] on wires, the membership statement `membership`, the public rows, the wiring `σ`), its
   cells from the inputs, and **its commitment** (`Circuit.indexRootWith`: the wiring table committed by
   WHIR over `F`).
8. [`Prover.lean`](PcsQuotient/Prover.lean): **the honest prover** (`proveWith`, `proverWith`):
   `protocol::prove` then `open`, its tables stacked in their hidden layouts with the padding it is given
   (`Layout.stackOf`), its WHIR openings by mumbai's WHIR prover pieces on this protocol's weight table
   (`openingScript`), run against the verifier's program (mumbai's `runFrom`).
9. [`Extractor.lean`](PcsQuotient/Extractor.lean): **the extractor** (`transcriptExtractorFor`), with its
   cost table.
10. [`Simulator.lean`](PcsQuotient/Simulator.lean): **the simulator** (`Simulator.simulateFor`,
    `Simulator.simOracle`).
11. [`Security.lean`](PcsQuotient/Security.lean): the deployed system (`setupWith`, `verifier`,
    `deployedIndexRoot`, `deployedVerifier`), the prover's coins, the experiments, and
    **`KnowledgeSoundness`, `Completeness`, `ZeroKnowledge`**, `StatementBinds`, collected in `Theorems`.

## The circuit and its commitment are named data

The deployed circuit is `PcsQuotient.membership logRows` (`Circuit.lean`, `logRows = 22`), a definition
transcribed from `quotient::circuit::membership`; its commitment is **a definition**, not a hypothesis:
`setupWith F = (membership logRows).indexRootWith F` (the WHIR root of its wiring table, over `F`), and the
deployed verifier's constant is `deployedIndexRoot () = setupWith keccakF1600`, which the differential test
finds equal to the Rust's (`8fd9a050…3ca9`, `--index`). Layer F0 (a χ-circuit end theorem with the zero
and one pinned and the statement embedding `statementWords`; `formal/Circuit`'s `membership` proved to
compute Keccak-256 membership) plugs in here: its circuit must be this `membership` (or be proved equal to
it), its embedding this `statementWords`. Nothing in the statements quantifies over the circuit, the
wiring or the constants: they are the computed ones.

## How the proofs plug in

The package stays proof-free and imports only mumbai's `statement` (Mathlib, VCVio, CompPoly through it); the
proofs in `formal/` are to import it and prove its statements about its definitions:

* **The circuit**: F0b's `formal/Circuit` `membership` is a second transcription of the same builder (its
  wiring checked against the Rust's by hash); this package's `PcsQuotient.membership` is checked against the
  Rust's by the circuit's commitment. One must be proved equal to the other (or one package import the other)
  for F0b's theorem to speak about `setupWith`'s circuit.
* **The extractor**: `transcriptExtractorFor` is mumbai's `committedLeaves` and list decoder on the witness
  table, then the hidden layout's read-back and the cells; `formal/Compose`'s Merkle-climbing extractor is
  proved equal to mumbai's `extract` on injective histories (`wordOfMerkle_eq_extract`), the link to this one.
* **The simulator**: zero knowledge is stated for any simulator, `ZeroKnowledgeWith s₀ sim simOracle ζ`
  (a simulator `Statement → StateT S ProbComp (Option Proof)`, its oracle
  `QueryImpl RandomPermutationOracles (StateT S ProbComp)`, its initial state `s₀`). The end theorem
  (`formal/EndToEnd/ZK`, `zeroKnowledge_end`) proves it for `formal/QuotientZk`'s simulator put in this
  shape (`zkSimulator`, `rpmSimOracle`; described in `formal/README.md`, "Zero knowledge end to end"), so
  the simulator the theorem covers is named in the theorem's statement. This package's own `simulator`
  (`ZeroKnowledge ζ` is `ZeroKnowledgeWith` at it) is a tested heuristic (the self-test runs it): it is
  **not** covered by the theorem (it programs the roots where `QuotientZk`'s simulator programs the
  challenges; the two are not equal in distribution).

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
    let coins ← sampleCoins
    match ← prover queryPermutation stmt w coins with
    | none => return false
    | some proof => verifier queryPermutation indexRoot stmt proof

def Completeness (δ : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
    Pr{let v ← completenessExperiment stmt w}[v = false] ≤ δ

noncomputable def realExperiment (stmt : Statement) (w : Secret) (D : Distinguisher) :
    ProbComp Bool :=
  runWithRandomPermutation do
    let coins ← sampleCoins
    D (← prover queryPermutation stmt w coins)

def idealExperimentWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (stmt : Statement)
    (D : Distinguisher) : ProbComp Bool :=
  (do
    let proof ← sim stmt
    simulateQ simOracle (D proof)).run' s₀

def ZeroKnowledgeWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (ζ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
  ∀ (D : Distinguisher) (Q : ℕ), (∀ proof, QueryCostAtMost (D proof) permutationCallCost Q) →
    Pr{let b ← realExperiment stmt w D}[b = true] ≤
        Pr{let b ← idealExperimentWith s₀ sim simOracle stmt D}[b = true] + ζ Q ∧
      Pr{let b ← idealExperimentWith s₀ sim simOracle stmt D}[b = true] ≤
        Pr{let b ← realExperiment stmt w D}[b = true] + ζ Q

-- this package's own simulator (a tested heuristic, not covered by the end theorem)
def ZeroKnowledge (ζ : ℕ → ℝ≥0∞) : Prop :=
  ZeroKnowledgeWith (S := Simulator.SimState) {} simulator Simulator.simOracle ζ

def StatementBinds : Prop :=
  ∀ w w' : Secret, w.statement = w'.statement →
    w.x = w'.x ∨ PairCollision (w.x, Vector.replicate 32 yPad) (w'.x, Vector.replicate 32 yPad)
```

`Adversary` is `OracleComp RandomPermutationOracles (Statement × Proof)` (coins, `π`, `π⁻¹`);
`Distinguisher` is `Option Proof → OracleComp RandomPermutationOracles Bool`, quantified after the
statement and the witness (non-adaptive zero knowledge). `sampleCoins` is the prover's coins: twelve
uniform mask words and a uniform word at every padding position of the two hidden tables.
`QueryCostAtMost`, `permutationCallCost`, `runWithRandomPermutation`, `loggedOracles`, `queryPermutation`
are mumbai's (`RandomPermutation.lean`). `PairCollision a b` is `a ≠ b ∧ pair a.1 a.2 = pair b.1 b.2`.

**Knowledge soundness needs no collision clause**: an extracted secret satisfies the relation exactly (the
circuit computes the deployed Keccak-256). `StatementBinds` is the clause a consumer needs who reads from a
statement that `y` names one `x`; it holds outright (it is a pigeonhole on `y`'s preimages).

**The bounds are parameters**, `ε`, `δ`, `ζ`: they are not yet known, and the end theorem will fix them
(a statement at `ε = 1` says nothing). The targets, by analogy with mumbai's `LeanVM.KnowledgeSoundness`:
`ε Q` of the form `(Q + c)·2^-k + 5(Q + c)²·2^-256` with `k` near `128` and `c` covering the setup's and
the verifier's own calls of `π` (the setup alone makes `2^21 + 2^19 − 1`: `2^19` leaves of four blocks and
`2^19 − 1` nodes); `δ` below `2^-128` (a vanishing denominator, about `2^26·2^-192`, or a proof of work
with no nonce among `2^25`, about `e^-256` each); `ζ Q` of the form `(Q + c)·2^-k` plus `HIDING.md`'s
terms (`2·H·2^(ℓ+1)·2^(-64(L−3))` for the siblings, and whatever bounds the failure of its conditions (S)
and (R) on the challenges).

## The extractor

`extractor stmt T proof` (`Security.lean`) is `transcriptExtractorFor (membership logRows)`
(`Extractor.lean`). **It reads** the statement, the proof's first two scalars (the witness table's root)
and the adversary's transcript `T`, and nothing else: it neither queries `π`, nor sees the setup's or the
verifier's queries, nor runs the adversary again. From `T`'s forward queries it replays the Keccak-256
evaluations whose whole sponge path the adversary queried (mumbai's `keccakEvaluationsOfTranscript`),
inverts the witness table's Merkle tree under the root through them (mumbai's `committedLeaves`: `2^20`
leaves of `64` words), lists the candidate stacks within the Johnson radius of the word (mumbai's
`fastStacks`, by interpolation for a word without errors, then, only if no fast candidate works,
`decodeStacks`, CompPoly's Guruswami–Sudan list decoder over `K` with prefix pruning, at most `2^18`
candidates), reads each candidate's table back through the hidden layout (`Layout.readEntry`), takes the
cells' polynomial to the cells' values (`Domain.values`), reads the input rows' `V` cells as bits, and
returns the first candidate's secret that satisfies the relation. **Its cost** (its loops; not proved):
mumbai's transcript replay and Merkle inversion, quadratic in the transcript (`N` evaluations, then
`2^21` scans of `N` pairs); `64` additive transforms of `2^20` on the fast path; the list decoder as
mumbai's cost table (infeasible at deployed sizes, as mumbai's own); per candidate the read-back of `2^24`
entries (a scan of the layout's `≤ 64` lanes and `≤ 167` held pieces each), one transform of `2^24`, and
`33` Keccak-256.

## The simulator

**Which simulator the end theorem covers.** `ZeroKnowledgeWith` takes the simulator as a parameter; the end
theorem (`formal/EndToEnd/ZK/Main.lean`, `zeroKnowledge_end`) proves it for `formal/QuotientZk`'s simulator in
this shape (`zkSimulator`, `rpmSimOracle`, `formal/EndToEnd/ZK/With.lean` and `Simulator.lean`), whose
definition and cost `formal/README.md` describes ("Zero knowledge end to end"). It draws every Fiat–Shamir
challenge first and programs the oracle with them, takes the messages and opened rows from the joint
honest-verifier simulator, and answers the unopened leaves with fresh private digests. The rest of this
section describes **this package's own `simulator`**, a tested heuristic that `ZeroKnowledge ζ` (that is,
`ZeroKnowledgeWith` at it) is about and that **no theorem covers**: it programs the trees' roots instead of
the challenges.

`simulator stmt` (`Security.lean`) is `Simulator.simulateFor (membership logRows) (2^25)`; together with
`Simulator.simOracle`, which answers every query of the distinguisher from the simulator's tables of
`π` (hash maps; fresh queries by uniform states: a random function, which differs from a permutation on a
collision only). **It reads** the statement and its own coins, never the witness. It is the **honest
prover on fake tables, with oracle programming**:

1. the circuit's commitment honestly (public);
2. the two roots as uniform digests, fixed first; the Keccak-256 chain run honestly over its `π`
   (`α, β, γ`, `t`, `ρ`);
3. the four values **uniform** (in `K` when the row of `t` is in `K`, else in `E`: `simValues` of
   `formal/`'s reduction simulator), `next` honestly; the verifier's four claims;
4. each hidden stack **uniform on its layout conditioned on its claims** (`fakeStack`: `3·#claims`
   entries solved for, the claims being linear over `K` limb by limb), that is a uniform table with those
   claims, uniformly padded;
5. each fake table's tree built honestly up to the root's children, and `π` **programmed** at the root
   node's input so that the tree's root is the one drawn in step 2 (`programmedTree`);
6. the honest WHIR prover on the fake tables, and on the public wiring table.

Step 4 is the right distribution by `HIDING.md`'s theorem: for fixed challenges, a translation of the padding
maps the opening's view of a table onto that of any other table with the same claims. Its cost is the
honest prover's openings and commitments on tables of the same sizes, plus one uniform word per stack word
and a Gauss–Jordan elimination of six unknowns. Its proof of any statement, true or not, is accepted by the
verifier querying the simulator's `π` (the self-test checks it on a small circuit, for a false statement).

## What is assumed, and what remains

**Trusted**, as in mumbai: the Lean kernel; mumbai's definitions this package reuses (Keccak-256, the
model, `verifyStackedOpening` as leanVM's WHIR verifier, its prover's pieces, its extractor's decoder;
mumbai tests its verifier against leanVM's on mutated proofs); that the deployed Keccak-f[1600] behaves
as a random permutation. **Tested, not proved**, that these definitions are the Rust: the differential
test (below). The constants' properties are checked by compiled evaluation (`native_decide`), not by the
kernel, which did not finish evaluating them in twenty minutes.

**Deviations from the Rust**, each documented where it is:

* The WHIR proofs are in mumbai's format, one full Merkle path per query (the raw form of
  `verifier::MerkleOpenings`); the Rust prover ships pruned paths, which the Rust verifier expands. The
  expansion is not formalized (as in mumbai).
* The reduction's proof is a structure of nine scalars rather than a stream; a stream of another length
  (rejected by the Rust) is no proof.
* The verifier inverts its denominators one by one after checking that none is zero; the Rust inverts
  their product by the norm to `K` (same values). The target `Σ_J γ^J word_J` is a fold over
  `statementWords`; the Rust writes it out (same value).
* The statement's prover takes its padding uniform; the deployed prover expands a 32-byte seed by
  ChaCha12 keyed by Keccak-256 (`Table::hidden`), which the test reproduces (`PcsQuotientTest/ChaCha.lean`).
* The EVM contract (`crates/evm`) is the reduction only; tying it to `reduceWith` is layer F5.

**To be proved** (`formal/README.md`):

* `KnowledgeSoundness ε`: the circuit (F0: `membership`'s satisfying assignments are its computation of
  Keccak-256 membership, the embedding `statementWords`), the reduction's round-by-round soundness (F1,
  with ideal commitments), WHIR's soundness for this weight on hidden layouts (F2, mumbai's `Whir/Sound` for
  any multiaffine weight; `formal/WhirBridge`, merged at `25d06ea`, states this opening check in mumbai's
  verifier language and proves it sound for leanVM's transcript shape, the opening's seed form the gap), and
  the composition in the model with extraction from the transcript (F4, mumbai's
  `common` and `lean_vm` extraction, through the hidden layout's read-back).
* `Completeness δ`: the honest prover's claims hold (F1's completeness) and its WHIR openings are accepted
  (mumbai's completeness of its WHIR prover), with the proofs of work.
* `ZeroKnowledgeWith` for `QuotientZk`'s simulator (`formal/EndToEnd/ZK`, `zeroKnowledge_end`, under named
  hypotheses: the joint model's instance, the skeleton's Fiat–Shamir freshness, the statement's prover against
  the skeleton's at fixed coins). `ZeroKnowledge ζ`, for this package's heuristic `simulator`, is not proved.
* `StatementBinds`: a pigeonhole, immediate.

## Building and testing

On a machine with the dependencies (Mathlib and the rest at mumbai's revisions):

```sh
lake build                                   # the statement: PcsQuotient
lake build PcsQuotientTest differential      # the constants' properties, the test

# vectors from the Rust (from the repository root): reductions, whole proofs (honest and tampered),
# circuit commitments, the honest prover's streams; --index adds the membership circuit's commitment
cargo run --release -p quotient --example statement_vectors -- vectors.txt --index
.lake/build/bin/differential vectors.txt     # Lean's verdicts, claims, commitments and streams vs Rust's
.lake/build/bin/differential --self-test     # the extractor's inversion and decoding, the simulator
.lake/build/bin/differential --weights       # the prover's weight vs the verifier's; fakeStack's claims
```

The test (`PcsQuotientTest/Differential.lean`) checks, line by line: on random nine-scalar streams at
`2^16` to `2^23` rows (some malformed, some at sizes the layouts do not take) and on honest streams, that
`reduceWith` gives the Rust's two roots and four claims or rejects as it does (`R`); on whole proofs of a
small circuit (`2^17` rows, hidden layouts), honest and tampered fourteen ways (values, roots, statement,
circuit commitment, WHIR scalars, leaves, siblings, missing, extra and short paths), that `verifyWith` gives
the Rust's verdict (`P`); that the Lean builder and commitment give the Rust circuits' sizes and
commitments, the membership circuit's at `2^22` rows included (`I`, about five minutes); and that the Lean
prover, given the Rust prover's masks and seed (its padding expanded by ChaCha12 as the Rust's), sends the
Rust prover's stream and its proof is accepted (`Q`). `--self-test` runs the extractor's Merkle inversion
through a transcript (a small tree: mumbai's replay is quadratic), its decoding of an honest hidden witness
table back to the input bits, and the simulator's proof of a false statement (about two hours at `2^17`
rows); `--weights` that the prover's and the simulator's weight on a hidden stack (`Layout.weightAt`) is the
verifier's (`stackWeight`) and that `fakeStack` meets the quotient table's two claim shapes.
