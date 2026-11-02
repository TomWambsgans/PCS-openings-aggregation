<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The structure follows leanerVM's `Statement/README.md` (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0). -->

# Statement

What `crates/quotient` is proved to be, in the files a reviewer reads: **definitions and end
statements only**, no proof, one Lake package (`pcs-quotient-statement`, library `PcsQuotient`) of thirteen
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
polynomials in the ideal model and whose extractor and simulator are `noncomputable`. The proofs are in
`formal/EndToEnd` (`formal/README.md`, "End-to-end theorems"): knowledge soundness and completeness are proved,
zero knowledge is in progress ("What is proved", below). `PcsQuotientTest/` is the differential test, not the
statement.

**The model.** Every end statement with an adversary is in mumbai's random-permutation model: one
uniformly random permutation `π` of the 1600-bit Keccak state, which every party queries forward (`π x`)
and inverse (`π⁻¹ y`), Keccak-256 the sponge over `π`. Deployed, **one Keccak-256** serves the reduction's
chain, the WHIR Merkle trees (`hash_pair` is byte for byte the relation's `pair`), the openings' duplex,
the circuit's commitment and the relation. In the model every hash of the protocol is Keccak-256 over the
one `π` (there is no private oracle), the circuit's commitment computed over `π` by a **setup** before the
adversary runs (deployed, the verifier holds it as a constant computed over Keccak-f[1600]); the
**relation** is over the deployed Keccak-256, which the circuit computes on bits, independent of `π` in the
model (mumbai's convention for leanVM's `KECCAK` instruction), with a **collision clause** where a statement
reads more than the relation (`StatementBinds`, as mumbai's `DigestBinds`). The three layouts' identifiers
(`Layout.id`, the Keccak-256 of each layout's encoding in the openings' prefix) are **constants of the
verifier**, fixed 32-byte values computed with the deployed Keccak-256, the same for every proof (the Rust
recomputes the same bytes; `formal/WhirBridge` proves the openings sound for any fixed prefix). That the deployed Keccak-f[1600]
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
   WHIR over `F`; its tree `Circuit.indexTreeWith`, and the tree's Keccak-256 evaluations
   `Tree.evaluations`, which the extractor reads).
8. [`Prover.lean`](PcsQuotient/Prover.lean): **the honest prover** (`proveWith`, `proverWith`):
   `protocol::prove` then `open`, its tables stacked in their hidden layouts with the padding it is given
   (`Layout.stackOf`), its WHIR openings by mumbai's WHIR prover pieces on this protocol's weight table
   (`openingScript`), run against the verifier's program (mumbai's `runFrom`).
9. [`Replay.lean`](PcsQuotient/Replay.lean): the transcript's Keccak-256 evaluations and the Merkle
   inversion, as mumbai's `keccakEvaluationsOfTranscript`, `answerPairs`, `preimage` and `subtreeLeaves`
   compute them, with hash maps (`transcriptEvaluations`, `preimageIndex`, `leavesUnder`).
10. [`Decoder.lean`](PcsQuotient/Decoder.lean): **the unique decoder** (`UniqueDecoding.uniqueStacks`):
    Gao's decoder on each lane, between mumbai's fast path and its list decoder.
11. [`Extractor.lean`](PcsQuotient/Extractor.lean): **the extractor** (`transcriptExtractorFor`), with its
    cost table.
12. [`Simulator.lean`](PcsQuotient/Simulator.lean): **the simulator** (`Simulator.simulateFor`,
    `Simulator.simOracle`).
13. [`Security.lean`](PcsQuotient/Security.lean): the deployed system (`setupWith`, `verifier`,
    `deployedIndexRoot`, `deployedVerifier`), the prover's coins, the experiments, and
    **`KnowledgeSoundness`, `Completeness`, `ZeroKnowledge`**, `StatementBinds`, collected in `Theorems`.

## The circuit and its commitment are named data

The deployed circuit is `PcsQuotient.membership logRows` (`Circuit.lean`, `logRows = 22`), a definition
transcribed from `quotient::circuit::membership`; its commitment is **a definition**, not a hypothesis:
`setupWith F = (membership logRows).indexRootWith F` (the WHIR root of its wiring table, over `F`), and the
deployed verifier's constant is `deployedIndexRoot () = setupWith keccakF1600`, which the differential test
finds equal to the Rust's (`8fd9a050…3ca9`, `--index`). Layer F0 (a χ-circuit end theorem with the zero
and one pinned and the statement embedding `statementWords`; `formal/Circuit`'s `membership` proved to
compute Keccak-256 membership) plugs in here: `formal/EndToEnd/Bridge/Circuit.lean` proves this `membership`
equal to F0b's (`membership_eq`). Nothing in the statements quantifies over the circuit, the wiring or the
constants: they are the computed ones.

## How the proofs plug in

The package stays proof-free and imports only mumbai's `statement` (Mathlib, VCVio, CompPoly through it); the
proofs in `formal/EndToEnd` import it and prove its statements about its definitions (`formal/EndToEnd/Bridge`
proves each definition here equal to the proof layers' own):

* **The circuit**: F0b's `formal/Circuit` `membership` is a second transcription of the same builder (its
  wiring checked against the Rust's by hash); this package's `PcsQuotient.membership` is checked against the
  Rust's by the circuit's commitment. `formal/EndToEnd/Bridge/Circuit.lean` proves the two equal
  (`membership_eq`, builder step by builder step), so F0b's theorem speaks about `setupWith`'s circuit.
* **The extractor**: `transcriptExtractorFor` is mumbai's replay, `committedLeaves` and decoders on the
  witness table (with hash maps, and the unique decoder between the fast path and the list decoder), then
  the hidden layout's read-back and the cells. `formal/EndToEnd/Soundness` proves `KnowledgeSoundness` for
  it (`Soundness.knowledgeSoundness`): its hash maps compute mumbai's lists where it reads them (`Soundness/Replay.lean`), and its last
  stage, the list decoder, lists every Johnson candidate, so a witness in `formal/Compose`'s extractor's
  list is one it returns (`Soundness/Extract.lean`); nothing is needed of the first two stages.
* **The simulator**: zero knowledge is stated for any simulator, `ZeroKnowledgeWith s₀ sim simOracle ζ`
  (a simulator `Statement → StateT S ProbComp (Option Proof)`, its oracle
  `QueryImpl RandomPermutationOracles (StateT S ProbComp)`, its initial state `s₀`). The end theorem, in
  progress (`formal/EndToEnd/ZK`: `zeroKnowledge_end`, `zeroKnowledge_deployed_final`,
  `zeroKnowledge_deployed_whir`, the last with one hypothesis left, `CoreWhir`), proves it for
  `formal/QuotientZk`'s simulator put in this shape (`zkSimulator`, `rpmSimOracle`; described in
  `formal/README.md`, "Zero knowledge end to end"), so the simulator the theorem covers is named in the
  theorem's statement. This package's own `simulator`
  (`ZeroKnowledge ζ` is `ZeroKnowledgeWith` at it) is a tested heuristic (the self-test runs it): it is
  **not** covered by the theorem (it programs the roots where `QuotientZk`'s simulator programs the
  challenges; the two are not equal in distribution).

## The end statements

As written in [`Security.lean`](PcsQuotient/Security.lean) (`PcsQuotient` namespace; `logRows = 22`):

```lean
noncomputable def soundnessExperiment (A : Adversary) : ProbComp Outcome :=
  runWithRandomPermutation do
    let tree ← setupTreeWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A tree.root)).run []
    let accepted ← verifier queryPermutation tree.root z.1 z.2
    return ((z, accepted), Tree.evaluations tree, transcript)

def BreaksKnowledgeSoundness (z : Outcome) : Prop :=
  z.accepted ∧ ¬ ∃ w, extractor z.statement z.setupEvaluations z.transcript z.proof = some w ∧
    Relation z.statement w

def KnowledgeSoundness (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), (∀ root, QueryCostAtMost (A root) permutationCallCost Q) →
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

`Adversary` is `Digest → OracleComp RandomPermutationOracles (Statement × Proof)`: given the setup's
commitment (the circuit's index root, the tree's root; it could recompute it with `π`), with coins, `π` and
`π⁻¹`;
`Distinguisher` is `Option Proof → OracleComp RandomPermutationOracles Bool`, quantified after the
statement and the witness (non-adaptive zero knowledge). `sampleCoins` is the prover's coins: twelve
uniform mask words and a uniform word at every padding position of the two hidden tables.
`QueryCostAtMost`, `permutationCallCost`, `runWithRandomPermutation`, `loggedOracles`, `queryPermutation`
are mumbai's (`RandomPermutation.lean`). `PairCollision a b` is `a ≠ b ∧ pair a.1 a.2 = pair b.1 b.2`.

**Knowledge soundness needs no collision clause**: an extracted secret satisfies the relation exactly (the
circuit computes the deployed Keccak-256). `StatementBinds` is the clause a consumer needs who reads from a
statement that `y` names one `x`; it holds outright (it is a pigeonhole on `y`'s preimages), and is not
proved in Lean.

**The bounds are parameters**, `ε`, `δ`, `ζ` (a statement at `ε = 1` says nothing). The end theorems fix
them:

* `ε = Soundness.ksBound` (`formal/EndToEnd/Soundness/RpmV.lean`):
  `ksBound Q = Σ_{i<3} openingBound (2^21 + Q + 6 + i · 10122) + N (2^-128 + 5 N / 2^256) +
  (2^52 + Q + (6 + 3 · 10122) · 2^32)² / 2^508`, `N = 2^21 + Q + 6 + 3 · 10122`, with
  `openingBound x = (x + 10122)(2^-128 + 5 (x + 10122) / 2^256)` (F2's term for one opening); the constants
  count the setup's and the verifier's own calls. About `2^-105` at `Q = 0`, `2^-86` at `2^40`, `2^-62` at
  `2^64` (`formal/EndToEnd/Review/E2ESoundnessNumbers.py`, exact rationals).
* `δ = E2ECompleteness.deltaDeployed = (17 · 2^24 + 8)/2^192 + 2/2^256 + 3 · 2^-277 + (2^48)²/2^508`, below
  `2^-162`: degenerate challenges, a chain query that is not fresh, the three proofs of work (no nonce among
  `2^25`), the permutation as two random oracles.
* `ζ = zkBoundEnd …` (in progress, `formal/EndToEnd/ZK/Main.lean`): about `2^-113` for `Q ≤ 2^126`, its largest
  term the Fiat–Shamir freshness of the honest prover's queries; `HIDING.md`'s conditions (S) and (R) are proven
  for the deployed layouts outside a small set of challenges, which the bound counts.

## The extractor

`extractor stmt setupEvals T proof` (`Security.lean`) is `transcriptExtractorFor (membership logRows)`
(`Extractor.lean`). **The extractor reads the adversary's transcript and the public setup's tree**: the
statement, the proof's first two scalars (the witness table's root), the adversary's transcript `T`, and
the Keccak-256 evaluations of the circuit commitment's Merkle tree (`setupEvals = Tree.evaluations tree`,
a pure function of the tree the setup computed: each leaf's bytes and each node's two children with
their digests), and nothing else: it neither queries `π`, nor sees the verifier's queries, nor runs the
adversary again. (The setup is public; reading its tree lets the extractor climb a witness tree that
reuses the commitment's nodes, which the composed proof in `formal/Compose` needs: its extractor reads
the setup's and the adversary's queries.) From `T`'s forward queries it replays the Keccak-256
evaluations whose whole sponge path the adversary queried, as mumbai's `keccakEvaluationsOfTranscript`
does but with hash maps, keeping those of the two input lengths the witness tree hashes (64 and 512 bytes,
`Replay.transcriptEvaluations`); it indexes the setup's and those evaluations (`Replay.preimageIndex`: each
input's first answer, then a digest and a length to the inputs it answers) and inverts the witness table's
Merkle tree under the root (`Replay.leavesUnder`, mumbai's `committedLeaves` read off the index: `2^20`
leaves of `64` words, each of its `64` lanes a Reed–Solomon word of `n = 2^20` symbols for messages of
`k = 2^19`). It decodes the word in three stages, each run only if the stages before give no witness:

1. **the fast path** (mumbai's `fastStacks`): each lane interpolated from its first `2^19` columns, for a
   word without errors there (an honest proof's);
2. **the unique decoder** (`UniqueDecoding.uniqueStacks`, `Decoder.lean`): Gao's decoder on each lane, which
   recovers the lane's polynomial whenever at most `⌊(n − k)/2⌋ = 2^18` of its columns are wrong, so the
   stack whenever the word agrees with the stack's encoding on at least `(n + k)/2 = 786432` columns;
3. **the list decoder** (mumbai's `decodeStacks`): every stack whose encoding agrees with the word on at
   least the Johnson threshold (`741549` columns), CompPoly's Guruswami–Sudan list decoder over `K` lane by
   lane with prefix pruning (at most `2^18` candidates).

It reads each candidate's table back through the hidden layout (`Layout.readEntry`), takes the cells'
polynomial to the cells' values (`Domain.values`), reads the input rows' `V` cells as bits, and returns the
first candidate's secret that satisfies the relation.

**Its cost** (`Extractor.lean`'s table; read off its loops, not proved), in operations of `K`, `Q` the
transcript's queries, `N` the evaluations read (the setup's `2^20 − 1` and the transcript's):

| Step | Cost |
| --- | --- |
| replay and evaluations | `Q` steps of `O(1)` expected hash-map operations on `200`-byte states, at most `680` bytes copied each; at most two paddings of at most `544` bytes compared per chain |
| index and inversion | `N` insertions keyed by inputs of at most `512` bytes and `N` by digests; `2^20 − 1` node and `2^20` leaf lookups |
| fast path | `64` inverse transforms of `2^19` and forward of `2^20`: about `2^31.4` |
| unique decoder, if the fast path gives no witness | about `2^28.3` per lane plus about `2^21.5` per wrong column of the lane (Gao's Euclid stops after `deg v ≤ e` divisions): about `2^34.3` for a word with few wrong columns, at most `2^45.7` |
| list decoder, if neither gives a witness | multiplicity `1149`, `Y`-degree `1625`, `2^39.3` interpolation conditions per lane; Mulders–Storjohann's reduction `(ℓ+1)³(m'n)² ≈ 2^92.3` per lane (`2^98.3` for the `64`), then Roth–Ruckenstein: infeasible |
| per candidate | the read-back of `2^24` entries, one transform of `2^24`, `33` Keccak-256 |

**The list decoder is the worst case only**: it runs only on a word whose every witness stack's encoding
agrees with it on fewer than `786432` of its `2^20` columns (beyond the unique-decoding radius, within the
Johnson radius); an honest proof's word takes the fast path, a word with a few wrong leaves the unique
decoder. That the unique decoder recovers every word within its radius is Gao's theorem, tested
(`PcsQuotientTest/Decoder.lean`) and not proved here; the soundness proof does not need it.

## The simulator

**Which simulator the end theorem covers.** `ZeroKnowledgeWith` takes the simulator as a parameter; the end
theorem (`formal/EndToEnd/ZK/Main.lean`, `zeroKnowledge_end`; in progress, one hypothesis left, "What is
proved" below) proves it for `formal/QuotientZk`'s simulator in
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
test (below). The test checks the constants' properties by compiled evaluation (`native_decide`); the proofs
check the ones they use by kernel evaluation (`formal/EndToEnd/Bridge/Claims/Constants.lean`:
`isCantor_statementConsts`, `rowVanishing_statementConsts`).

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
* The EVM contract (`crates/evm`) computes the reduction and calls `PCS_OPEN` for the openings; F5 and
  `formal/EndToEnd/Evm` prove that its recorded graph accepts exactly when `verifyWith` does
  (`evm_accepts_iff_verifyWith`), with `PCS_OPEN`'s semantics an explicit definition (`pcsOpen`).

**What is proved** (`formal/README.md`, "End-to-end theorems"; each on `propext`, `Classical.choice`,
`Quot.sound`):

* `KnowledgeSoundness Soundness.ksBound`: **proved, no hypotheses** (`Soundness.knowledgeSoundness`,
  `formal/EndToEnd/Soundness/Final.lean`), from the circuit (F0: `membership`'s satisfying assignments are its
  computation of Keccak-256 membership, the embedding `statementWords`), the reduction's round-by-round
  soundness (F1), WHIR's soundness for this weight on the hidden layouts (F2, `formal/WhirBridge`), the
  composition in the model with extraction from the transcript (F4, `formal/Compose`), and the bridge from
  these definitions to the layers' (`formal/EndToEnd/Bridge`). Stand-alone knowledge soundness, not
  simulation-extractability.
* `Completeness E2ECompleteness.deltaDeployed`: **proved, no hypotheses** (`E2ECompleteness.completeness_end`,
  `formal/EndToEnd/Completeness/E2ECompleteness/Done.lean`): the honest prover's claims hold (F1's
  completeness) and its WHIR openings are accepted (mumbai's completeness of its WHIR prover), with the proofs
  of work, the chain's challenges in the random-oracle model, and the transfer from the permutation.
* `ZeroKnowledgeWith` for `QuotientZk`'s simulator: **in progress** (`formal/EndToEnd/ZK`:
  `zeroKnowledge_deployed_final`, and `zeroKnowledge_deployed_whir` with WHIR's honest prover as the renderer;
  the hypothesis left is `CoreWhir`, the Statement's prover against the skeleton's at a fixed permutation). The
  simulator's tables are computed; its wiring value is still `noncomputable`. `ZeroKnowledge ζ`, for this
  package's heuristic `simulator`, is not proved, so neither is the structure `Theorems` (`Security.lean`),
  whose `zeroKnowledge` field it is.
* `StatementBinds`: a pigeonhole, immediate; not proved in Lean.
* The EVM contract: `formal/EndToEnd/Evm` (`evm_accepts_iff_verifyWith`, `evm_accepts_iff_exists`); the
  bytecode equal to the recorded graph and the `PCS_OPEN` mock equal to `openingWith` by tests.

## Building and testing

On a machine with the dependencies (Mathlib and the rest at mumbai's revisions):

```sh
lake build                                   # the statement: PcsQuotient
lake build PcsQuotientTest differential      # the constants' properties, the unique decoder's
                                             # and the hash-map inversion's tests, the test

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
