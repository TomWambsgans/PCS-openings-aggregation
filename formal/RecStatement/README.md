<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The structure follows formal/UniStatement/README.md. -->

# RecStatement

The recursion's outer proof π2 (`crates/leanvm_rec`, `PI2.md` §2, §8–§9; branch `leanvm-rec` @ 2b22581, the final
protocol: the setup committed as `κ` and `κ + σ`, `ξ = κ(t) + βσ(t)` sent, no `h(t)`, the zero checks as an aligned
coset of ports in closed form `β^15/F(Y)`, the row fold's siblings, the normalised `Q` claim
`(1 + ρ')h + ρ'q = X/(S_d Y)`, one inversion, every `PCS_OPEN` call in `machine.rs`'s one ABI, π1's claims at points the
contract derives from π1-rec3's 14 narrow pair challenges), in the files a reviewer reads:

* **π2's verifier as computable Lean**, step by step as `pi2/verifier.rs` and the contract's order;
* the circuit's tables as **data the Rust emits** (`Data.lean`, with a staleness test; never `σ`);
* the **differential test** against the Rust (the real π1-rec3 + π2 proof and 63 other streams);
* the **verifier-arithmetic lemmas** that `RecPiop`'s rounds and copy argument consume, proved;
* the **end statements** of the whole recursive verifier, stated, not proved, in two parts: π2's, in the
  random-permutation model (`RecKnowledgeSoundness2`, `RecCompleteness2`: the contract accepts only if π1-rec3's recorded
  graph, run with the real Keccak-f[1600] as π2's circuit runs it, accepts the stream π2's extractor outputs);
  end-to-end knowledge soundness against leanVM 42422001's relation as an **explicit reduction**
  (`RecKnowledgeSoundnessReduction`, `Reduction.lean`: the break is bounded by π2's error plus π1-rec3's and the merge
  hazard's experiments at Keccak-f[1600] for two explicit adversaries derived from the attacker, of its queries); and
  the end-to-end corollaries (`RecKnowledgeSoundness`, `RecCompleteness`, `Lv42.Protocol.M3Holds`) under named
  hypotheses about π1-rec3 at Keccak-f[1600]. The soundness ones (`Pi1FsKeccak`, `Pi1HazardKeccak`) are false as stated
  for computationally unbounded adversaries, which grind Keccak-f[1600] offline for free: read them as the Fiat–Shamir
  heuristic for adversaries of bounded Keccak-f[1600] work, which Lean does not model.

No `sorry`, no `native_decide`, every headline definition and theorem on Lean's three axioms (`RecStatement.lean`'s
`#guard_msgs`). It is a library of `formal/EndToEnd` (`RecStatement`, `srcDir = "../RecStatement"`, `warningAsError`),
as `UniStatement` is, whose definitions it reuses (the channel, `E`, the layout words of π1, π1-rec3's contract IV, the
extractor's pieces).

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build RecStatement            # the library; the axiom guards
# the data and the vectors (from the repository root, on h1; ~14 s, 11.6 GB: the real circuit compiled, its setup
# committed, π2's prover on π1-rec3's real witness):
UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_statement -- --ignored statement_data_is_current
REC_STATEMENT_OUT=$PWD/rec_statement_vectors.txt \
  cargo test --release -p leanvm_rec --test lean_statement -- --ignored --nocapture lean_statement_vectors
REC_STATEMENT_VECTORS=$PWD/rec_statement_vectors.txt lake env lean ../RecStatement/RecStatementTest/Runner.lean
```
(`RUSTFLAGS="-C target-cpu=native"` for the Rust; without `UPDATE_LEAN` the first command fails when `Data.lean` is
stale.)

## Reading order

1. [`Basic.lean`](RecStatement/Basic.lean): the circuit as the verifier reads it (`Coeff`, `Lin`, `Formula`, `Pair`,
   `Read`, `PublicTerm`, `Circuit`) and π1's call words (`CallWord`).
2. [`Data.lean`](RecStatement/Data.lean) (generated): π2's circuit for π1-rec3's real proof, D16v: `2^24` positions,
   rows of 16, 55 formulas, 156 pairs (4 pull-less) in 66 groups, 19 reads, 36 public terms (16 the zero coset); π1's
   contract IV, the setup's root, the circuit's digest; π1's three calls.
3. [`Core.lean`](RecStatement/Core.lean): **the arithmetic at `t`, over any field** (`CoreSpec.run`), every
   intermediate value a field of `Out`.
4. [`Spec.lean`](RecStatement/Spec.lean): `Spec::of` (the blocks' constants in `K`, the groups, the zero coset, the
   highest power of `γ`, the walk).
5. [`Verifier.lean`](RecStatement/Verifier.lean): the norm's inverse, the extension, `Spec.core` (the constants over
   `E`), the layouts and layout words, **the IV**, `pairPoint`, **`reduceWith`**, `runWith`/`run`.
6. [`Calls.lean`](RecStatement/Calls.lean): **the six `PCS_OPEN` calls word for word** (`pcsCalls`), π1-rec3's contract
   IV (`pi1IvWith`).
7. [`Security.lean`](RecStatement/Security.lean): π2's circuit with `σ`, `κ` (`Pi2Circuit`: its digest and setup table
   over `F`), the deployment and `RecDeployment.Real`, `PCS_OPEN` decoded under the registry and opened, the contract,
   π1-rec3 at Keccak-f[1600] (its verifier and its recorded graph), the extractors, the experiments,
   **`RecKnowledgeSoundness2`**, **`RecCompleteness2`** (π2's part), the merge hazard on accepted streams
   (`Pi1HazardAccepted`), the hypotheses (`Pi1FsKeccak`, `Pi1HazardKeccak`, `Pi1CompletenessKeccak`,
   `Pi1HazardKeccakHonest`), **`RecKnowledgeSoundness`**, **`RecCompleteness`** (end to end, Prop-premise forms).
   [`Reduction.lean`](RecStatement/Reduction.lean): the derived adversaries (`pi1Adversary`, `hazardAdversary`) and
   **`RecKnowledgeSoundnessReduction`** (end to end, as an explicit reduction).
8. [`Lemmas/`](RecStatement/Lemmas): `Arith` (fractions, digits, the fold, the siblings' fold), `Side` (the pushes'
   sums, the walk), `Subspace` (the indicators' closed form), `Coset` (the zero coset's), `SpecOf` (the transcription's
   hypothesis), `Push`, `Public`, **`Main`** (`checks_claims_iff`), `SpecLink` (`Spec::of`'s constants are `SpecOf`'s).
9. [`RecStatementTest/Runner.lean`](RecStatementTest/Runner.lean): the differential runner.

## Rust → Lean

| Rust (`crates/leanvm_rec/src/pi2`, `leanvm-rec` @ 2b22581) | Lean (`RecStatement.`) |
|---|---|
| `circuit.rs`: `Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit` (but `σ`, `κ`), `max_gamma`, `coset_constants`, `vanishing`, `pair_constants`, `digest` | `Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit`, `Circuit.maxGamma`, `cosetConstants` (`cosetConstantsF`), `vanishing` (`vanishingF`), `pairConstants`, `Pi2Circuit.digestWith` |
| `verifier.rs`: `NAME`, `Spec::of`, `subspace_coefficients`, `zero_coset`, `normalised_constants`, `tag_walk`, `frobenius`, `inverse`, `extension`, `reduce`, `Reduced`, `verify`, `statement_words` | `name`, `Spec.of`, `subspaceCoefficients` (`subspaceCoeffsF`), `zeroCosetOf`, `normalisedConstants`, `tagWalk`, `frobenius`, `normInverse`, `extension`, `reduceWith` (+ `CoreSpec.run`), `Reduced`, `runWith`/`run`, `UniStatement.publicWordsOf` |
| `verifier.rs` (`reduce`'s steps) | `digitsList`, `cellsList`/`foldLevel`, `zHat`, `fraction`, `groupDens`, `walkDens`/`betaTagNext`, `cosetSum`/`bRestList`, `publicSide`, `pushStep`/`pushSums`, `wInvsList`, `foldW` |
| `prover.rs`: `quotient_chunks`, `layouts`, `layout_word`, `layout_words`, `iv`, `Setup::new`'s table | `quotientChunks`, `layoutsOf`, `layoutWord`, `layoutWords`, `ivWith`/`iv`, `Pi2Circuit.setupStack` |
| `contract.rs`: `read_indices`, `number`, `root_word`, `call_words`/`expected_calls`, `registry`; `machine.rs`: `decode`, `root_of_word` | `elementIndices`, `UniStatement.numberWord`, `rootWordOfBytes`, `pcsCalls`, `registryOf`, `decodeWith`, `rootOfWord` |
| `transcript.rs`: `cantor_beta1`, `pair_point`; `circuit/spec.rs`: `CallWord` | `cantorBeta1` (`UniStatement.cantorBeta1`), `pairPoint`, `CallWord` |
| `leanvm_univariate/contract.rs`: `variant_bytes`, `contract_iv_for` | `rec3VariantBytes`, `pi1IvWith` (`UniStatement.variantBytes`, `contractIvForWith`) |

**Deviations, none changing a value**: a `List` stands for a `Vec`, an out-of-range read gives a default (the Rust
would panic; it never does on the circuits tested); the Rust skips a product by a coefficient equal to one, a zero
coefficient of `w_k` and, for a one-pair group, its numerator `1` (here the products are taken); `γ^0` is read from
the powers (`gammas[0] = 1`); the arithmetic's inverse is the field's (the Rust's is the norm's, `normInverse`,
transcribed and checked equal on every vector); the Rust's trace hook (`reduce_traced`) only reads values (the
contract's graph is unchanged: `tests/pi2.rs`'s parity holds).

## The data

`crates/leanvm_rec/src/lean_statement.rs` (`render`) writes `Data.lean` from π2's circuit for π1-rec3's real proof
(`circuit::compile::pi2(record_verifier(REFERENCE, Flock(FLOCK_REC3), Point), D16v)`, then `pi2::adapt`): the shape,
the formulas, the pairs, the reads, the public terms; π1's contract IV (`Compiled::pi1_iv`), the setup's root
(`Setup::new(circuit).root()`), the circuit's digest (`Circuit::digest`); π1's three calls (`spec::Circuit::calls`).
**Not `σ`, not `κ`**: the verifier reads neither; the setup's root and the digest bind them (`RecDeployment.Real`).
`tests/lean_statement.rs`'s `statement_data_is_current` fails when the file is stale. The runner checks, against the
Rust, every constant the Lean derives from it: `Spec.of`'s pairs (`s`, `Ẑ_s(c_p)`), recursion constants, groups,
pull-less pairs, public terms, zero coset, walk, highest power of `γ`; the IV; the layout words; `β_1`; the extension;
the stream's length; π1's contract IV (`pi1Iv` at `UniStatement.reference`, `programIv`, `referenceRoots`) and π1's
calls' constants (the reference layout words, one claim each, `F`'s root word).

## The statements (`Security.lean`, verbatim)

**Two models, which do not compose formally.** π2's circuit computes π1-rec3's Fiat–Shamir challenges with the real
Keccak-f[1600] (a circuit is a fixed function: `RecCircuit.compile_sound`, `keccak_out`); π1-rec3's knowledge soundness
is proved in the random-permutation model (`UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`, 128.49 bits). No
circuit computes a random permutation, which is inherent to recursion, so the statements come in two parts (the
earlier proofs' caveat, AGENTS.md: "the theorems are in the random-permutation model and do not formally compose with
the EVM one, which holds at the real Keccak-f[1600]"):

1. **π2's part, in the random-permutation model** (provable): one random permutation `π` for π2's own Fiat–Shamir, the
   circuit's digest, the commitments and the six openings.
2. **End to end against Lv42's `M3Holds`, as an explicit reduction** (`RecKnowledgeSoundnessReduction`): for every
   adversary `A` of `Q` queries, the break's probability is at most `ε2 Q` plus π1-rec3's Keccak-f[1600] soundness
   experiment for `pi1Adversary D A` plus the merge hazard's experiment for `hazardAdversary D A`. Both derived
   adversaries are `def`s: `A`, its queries logged, then π2's explicit extractor; they make `A`'s queries (at most `Q`,
   a conjunct of the Prop) and run in `A`'s time plus the extractor's (preimage replay, `W`'s inversion and decoding,
   Guruswami–Sudan at `2^24`, π1's graph's checks: polynomial; Lean does not model time). The Fiat–Shamir heuristic is
   applied by the reader to these two adversaries, in their Keccak-f[1600] work (`A`'s offline evaluations plus the
   extractor's graph checks per candidate), the resource it bounds and `Q` does not count.
3. **The Prop-premise corollaries**, under named hypotheses about π1-rec3 **at Keccak-f[1600]**, motivated by π1-rec3's
   random-permutation theorems, and RecGraph's target `Pi1GraphIsVerifier` (graph = verifier off the merge hazard,
   proved). `Pi1FsKeccak` and `Pi1HazardKeccak` quantify over every `OracleComp` adversary and count only its calls of
   `π`; such an adversary computes Keccak-f[1600] for free and grinds π1's challenges offline, so **they are false as
   stated** (`RecCompose/Review/STATEMENT_REVIEW.md`, finding 3): the Fiat–Shamir heuristic for adversaries of bounded
   Keccak-f[1600] work, which Lean does not model. `Pi1CompletenessKeccak` and `Pi1HazardKeccakHonest` are about one
   fixed honest prover, the statement chosen before `π`: no adversary grinds there.

**The merge hazard** (`RecGraph.MergeHazard`) asks that π1-rec3's run draw `t` (challenge 49) and that `t` be a root of
`Z_bad(p_0)`. Reading an undrawn `t` as `0` put every run that stops early, the empty stream included, on the hazard
(`Z_bad(0) = 0`), which made `Pi1HazardKeccak` force `εh ≥ 1` (finding 2). The soundness hazard (`Pi1HazardAccepted`)
also asks that π1-rec3's graph accept the stream (`pi1GraphChecks`).

```lean
structure Pi2Circuit where
  circuit : Circuit
  sigma : ℕ → ℕ
  kappa : ℕ → K

structure RecDeployment where
  pi1 : UniStatement.Deployment
  pi2 : List UInt8 → Pi2Circuit          -- π2's circuit for π1's contract IV (κ's constants)
  pi1Calls : List (List CallWord)
  pi1Stream : (ℕ → K) → Array UInt8     -- π1's stream as π2's witness holds it (RecCircuit's decodeStream)

-- π2's part, in the random-permutation model
def Pi1GraphAccepts (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) (ops : List Pi1Opening) : Prop :=
  ∃ out gops, RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph iv1 input.toList s = some out ∧
    (∀ z ∈ out.zeros, z = 0) ∧ (∀ z ∈ out.nonzeros, z ≠ 0) ∧ out.calls.mapM decodePi1Call = some gops ∧
    gops.map (·.2) = ops.map (·.2) ∧ (gops.take 2).map (·.1) = (ops.take 2).map (·.1)

def RecBreaksKnowledgeSoundness2 (D : RecDeployment) (ext : RecExtractor2) (z : RecOutcome2) : Prop :=
  z.1.2 = true ∧ ¬ ∃ s ops, ext z.2.2.2.1 z.1.1.1 z.2.1 z.2.2.1 z.1.1.2 = some s ∧
    contractPi1Openings (registryOf D.pi1.shape (D.circuitAt z.2.2.2.1.pi1).circuit.logN) z.2.2.2.2 = some ops ∧
    Pi1GraphAccepts (D.pi1IvAt z.2.2.2.1.pi1) z.1.1.1 s ops

def RecKnowledgeSoundness2With (D : RecDeployment) (ext : RecExtractor2) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness2 D ext z] ≤ ε2 Q

def RecKnowledgeSoundness2 (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  RecKnowledgeSoundness2With D (recExtractor2 D) ε2

def RecCompleteness2 (D : RecDeployment) (P2 : Pi2Prover) (δ2 : ℝ≥0∞) : Prop :=
  ∀ (P1 : Pi1Prover D) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows),
    Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = true ∧ v.2 = false] ≤ δ2

-- the merge hazard: the run draws t (challenge 49), t a root of Z_bad(p_0) (RecGraph/Hazard.lean)
def MergeHazard (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) : Prop :=
  let ch := (Id.run (runWithFs (m := Id) (fun s ↦ pure (π s)) reference iv publicInput stream (.flock flockMain) .point
    .rec3 true)).chan.challenges
  50 ≤ ch.size ∧ Hazard (ch.getD 42 0) (ch.getD 49 0)

def Pi1HazardAccepted (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) : Prop :=
  pi1GraphChecks iv1 input s = true ∧ RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 iv1 input.toList s

-- the hypotheses about π1-rec3 at Keccak-f[1600] (the soundness ones false as stated for unbounded adversaries)
def Pi1FsKeccak (D : RecDeployment) (ε1 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Pi1Adversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (A roots evals) permutationCallCost Q) →
    Pr{let z ← pi1KeccakSoundnessExperiment D A}[
      UniStatement.UniBreaksKnowledgeSoundness D.pi1 (UniStatement.uniExtractor D.pi1) z] ≤ ε1 Q

def Pi1HazardKeccak (D : RecDeployment) (εh : ℕ → ℝ≥0∞) : Prop :=
  ∀ (B : Pi1StreamAdversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (B roots evals) permutationCallCost Q) →
    Pr{let z ← pi1HazardExperiment D B}[Pi1HazardAccepted z.1 z.2.1 z.2.2] ≤ εh Q

def Pi1CompletenessKeccak (D : RecDeployment) (P1 : Pi1Prover D) (δ1 : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← pi1KeccakCompletenessExperiment D P1 input rows q}[v = false] ≤ δ1

-- the end-to-end corollaries, against Lv42's M3Holds
def RecBreaksKnowledgeSoundness (D : RecDeployment) (ext : RecExtractor D) (z : RecOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ w, ext z.2.2.2 z.1.1.1 z.2.1 z.2.2.1 z.1.1.2 = some w ∧ D.pi1.Relation w.1 z.1.1.1 w.2

def RecKnowledgeSoundnessWith (D : RecDeployment) (ext : RecExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D ext z] ≤ ε Q

-- end to end, as an explicit reduction (Reduction.lean)
def hazardAdversary (D : RecDeployment) (A : RecAdversary) : Pi1StreamAdversary :=
  fun roots evals ↦ do
    let (z, T) ← (simulateQ loggedOracles (A roots)).run []
    return (z.1, (recExtractor2 D roots z.1 evals T z.2).getD #[])

def pi1Adversary (D : RecDeployment) (A : RecAdversary) : Pi1Adversary :=
  fun roots evals ↦ do
    let (z, T) ← (simulateQ loggedOracles (A roots)).run []
    return (z.1, z.2.pi1Proof ((recExtractor2 D roots z.1 evals T z.2).getD #[]))

def RecKnowledgeSoundnessReduction (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    (∀ roots evals, QueryCostAtMost (pi1Adversary D A roots evals) permutationCallCost Q) ∧
    (∀ roots evals, QueryCostAtMost (hazardAdversary D A roots evals) permutationCallCost Q) ∧
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D (recExtractor D) z] ≤
      ε2 Q +
        Pr{let z ← pi1KeccakSoundnessExperiment D (pi1Adversary D A)}[
          UniStatement.UniBreaksKnowledgeSoundness D.pi1 (UniStatement.uniExtractor D.pi1) z] +
        Pr{let z ← pi1HazardExperiment D (hazardAdversary D A)}[Pi1HazardAccepted z.1 z.2.1 z.2.2]

-- the Prop-premise corollary
def RecKnowledgeSoundness (D : RecDeployment) (ε2 ε1 εh : ℕ → ℝ≥0∞) : Prop :=
  RecGraph.Pi1.Pi1GraphIsVerifier → Pi1FsKeccak D ε1 → Pi1HazardKeccak D εh →
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ ε2 Q + ε1 Q + εh Q

def RecCompletenessWith (D : RecDeployment) (P : RecProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← recCompletenessExperiment D P input rows q}[v = false] ≤ δ

def RecCompleteness (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ1 δh δ2 : ℝ≥0∞) : Prop :=
  RecGraph.Pi1.Pi1GraphIsVerifier → Pi1CompletenessKeccak D P1 δ1 → Pi1HazardKeccakHonest D P1 δh →
    RecCompletenessWith D (composeProver D P1 P2) (δ1 + δh + δ2)
```

* **The contract** `D.contractWith F roots input proof`: π2's IV over `F` (`D.ivWith`: π1-rec3's contract IV at π1's
  setup roots **over Keccak-f[1600]** (`pi1IvAt`), the circuit's digest, π2's setup root, π2's layout words), the run of
  π2's verifier for the circuit `D.circuitAt roots.pi1 = D.pi2 (pi1IvAt roots.pi1)` (its verdict `all ≠ 0`), then the six
  calls (`pcsCalls`, π1's `F` root word and π2's setup root the setup's), each decoded under the registry
  (`decodeWith`) and opened over `F`: π1's by `UniStatement.pcsOpenWith`, π2's by `PcsQuotient.openingWith`. Its verdict
  and calls; `verifierWith` its verdict.
* **The setup** (`D.setupTreesWith`): π1's three trees (`UniStatement.setupTreesWith`) and π2's (`PcsQuotient.commitWith`
  of `κ`, `κ + σ` in the basis `B`, for the circuit at π1's IV).
* **π1-rec3 at Keccak-f[1600]**: `pi1KeccakVerifierWith F` (its IV and run over Keccak-f[1600], `UniStatement.runFs …
  .rec3 true`; its three openings over `F`) for the soundness and completeness hypotheses, whose experiments run on the
  recursive setup; `pi1GraphVerifierWith F` (its recorded graph over Keccak-f[1600], its three calls opened over `F`)
  for π2's completeness.
* **The extractors** (explicit, computable): `recExtractor2` decodes π2's `W` (fast path, unique decoder, list decoder),
  reads π1's stream off each candidate's witness values (`D.pi1Stream`), the first on which π1-rec3's graph's checks hold
  at Keccak-f[1600]; `recExtractor` then runs π1-rec3's own extractor (`UniStatement.uniExtractor`) on that stream and
  the proof's three π1 openings, its row counts the stream's. The extractors take the setup's roots.
* `RecDeployment.Real`: `∀ iv, (D.pi2 iv).circuit = Data.circuit`, π1's calls, the reference shape and program IV, at
  π1's reference IV (`Data.pi1Iv`) the digest and setup root the Rust computed (which bind `σ`, `κ`), and
  `SetupFromCompiler` (σ, κ the Lean compiler's at every **32-byte** IV; π1's contract IV is a Keccak-256 digest,
  `RecDeployment.pi1IvAt_length`). The program `D.pi1.prog` is not pinned. **Inhabited**: `RecCompose.realDeployment`
  (`RecCompose/RealDeployment.lean`, `realDeployment_real`), given `GraphsAgree` and the evaluated `DigestChecked`,
  `SetupRootChecked` (`rec-real-check`).
* **The deployed bytecode** is linked to this model by transcription and test (`contract.rs`'s `parity`,
  `parity_deployable`, and the differential runner below), not by a Lean proof.

## The verifier-arithmetic lemmas (`Lemmas/`, proved)

Over any field of characteristic two, for `RecPiop`'s circuit `G` on a Cantor basis `B` (`ω = Heap.omega B`), under
**`SpecOf S G B pairOf portOf nz pubOf`** (the arithmetic's constants are `Spec::of` of `G`: the normalised recursion's
constants, the pairs enumerating `G.pairs` with their `s` and `Ẑ_s(c_p)`, the groups partitioning them with their
role, pull flag and formula, the zero coset the first `2^k` ports, the other terms the other ports with their tags and
public fingerprints):

* **`ind_eval_closed`** (`Subspace`): at `t ∉ V_m`, `Ẑ_s(t) + Ẑ_s(c_p) ≠ 0` and
  `(G.ind ω p).eval t = w_m(t)/(Ẑ_s(t) + Ẑ_s(c_p))`;
* **`coset_closed`** (`Coset`): `F(Y) = Π_{u<2^k} (Y + β ω_u)` and `Σ_u 1/(Y + βω_u) = β^(2^k−1)/F(Y)`;
* **`cellsList_eq_cellsOf`** (`Arith`): the siblings' fold is `RecPiop.cellsOf` (`ω_{2k+1} = ω_{2k} + 1`);
  **`foldW_eq_foldAt`**: `W`'s fold is `RecPiop.foldAt`;
* **`push_side`** (`Push`): `B ≠ 0`, `S_d ≠ 0`, `Σ_p I_p(t)(E_p + v_0) = w_m A/B`, `1_S(t) = w_m S_n/S_d`;
  **`publicSide_eq`** (`Public`): `D = Π_j d_pub(j)`, and `N = D · T` where no `d_pub` vanishes;
* **`all_ne_zero_iff`** (`Main`): the one inversion carries the two nonzero conditions:
  `all ≠ 0 ↔ w_{m+2}(t) ≠ 0 ∧ c_h + c_q ≠ 0 ∧ PubOK`;
* **`checks_claims_iff`** (`Main`):
  ```lean
  ((S.run inp).all ≠ 0 ∧ (S.run inp).combination = (1 + (S.run inp).rhoQ) * ht + (S.run inp).rhoQ * qt ∧
      (S.run inp).target = sumH ∧ inp.ξ = κt + inp.β * σt ∧ (S.run inp).fold = foldTrue) ↔
    (sq^[G.logN + 2] inp.t ≠ 0 ∧ dPullAt v α β t * G.dPushAt ω v ξ α γ t + (G.zV ω).eval t ≠ 0 ∧
      (∀ j < G.nP, G.dPub ω (pubOf inp.scalars) α β γ j ≠ 0) ∧ sumH = G.target ω (pubOf inp.scalars) α β γ ∧
      ξ = κt + β * σt ∧ G.QClaim ω v ξ α β γ t ht qt ∧ foldAt G.logW (fun k ↦ inp.a.getD k 0) ρ = foldTrue)
  ```
  (`v = cellsOf G.logW ω (fun k ↦ inp.a.getD k 0) t`): the verifier's check passes and its claims hold at the true
  values iff `t ∉ V_{m+2}`, `c_h + c_q ≠ 0` and `RecPiop`'s state after `ρ` holds; **`checks_claims_iff_post2`** states
  the right side with `RecPiop.Post2 G ω Mo pubOf' s cW [α, β, γ] cQ [t] (a ++ [ξ]) [ρ]` itself, for any tables' model
  `Mo` (its `h(t)`, `q(t)`, `Σ_V h`, `κ(t)`, `σ(t)`, `W`'s true fold);
* the claims' points (`Main`): `run_u` (`u_l = w_l/(1 + w_l)`), `run_digitsScale` (`t/w_{m+2} = Π (1 + w_l)^{-1}`), for
  the tables' layer;
* **`normConsts_of_spec`**, **`pairZ_eq_zHat`** (`SpecLink`): `Spec::of`'s constants (`coset_constants`,
  `normalised_constants`, `pair_constants`) are `SpecOf`'s; they commute with a field homomorphism (`K → E`).

## What is tested, what is defined

**Tested** (`RecStatementTest/Runner.lean`, `lake env lean`: compiled evaluation, not the kernel), on **64 vectors** of
the Rust (`crates/leanvm_rec/tests/lean_statement.rs`): **the real proof** (π1-rec3's 1,000-signature proof, then π2's
real proof on its circuit), **31 flips** (one bit of a byte of π1's roots, its elements, `W`'s and `Q`'s roots, every
fold value and `ξ`, the last byte), **3 other public inputs**, **3 truncated and 2 extended streams**, **24 random**
streams and public inputs. On each, the Lean and the Rust agree on every value: the verdict (the stream's error, or the
value required nonzero), the 16 trace steps (every intermediate value of `reduce`), the public scalars and their pair
points, the roots, the four claims, **the six `PCS_OPEN` inputs word for word**, and the compiled contract (revm, every
call attested) calls `PCS_OPEN` with exactly these inputs (the Rust writer asserts it). On every accepted vector the
Lean also decodes each call under the registry (π1's three by π1's layouts, π2's three by π2's), re-encodes it to its
words, and finds π2's decoded claims the reduction's; and the norm's inverse is the field's. The self-tests: the norm's
inverse; the zero coset's closed form (`k ≤ 5`) and `w_k` vanishing on `V_k`; the indicators' cosets at `m = 10`
(`Ẑ_s(ω_i) + Ẑ_s(c_p) = 0` exactly on the coset, every alignment) and the normalised recursion; `β_1`; π1's contract IV
and π1's calls' constants. **Results: 64/64 agree on every value; 59 accepted by both, 5 rejected by both** (the
truncated and extended streams); about 85 s.

The flipped, other-input and random streams are accepted by both: the contract's only check before `PCS_OPEN` is the
one inversion (`all ≠ 0`), which fails only on a degenerate challenge; everything else rests on the openings.

**Defined, not tested here**: `PCS_OPEN`'s WHIR (the Rust has a mock), the extractor, the experiments, the Props. The
setup's commitment (`setupTreeWith`) and the circuit's digest over Keccak-f[1600], of the Lean compiler's `σ`, `κ` at
π1's reference IV, are evaluated against the Rust's values by `rec-real-check` (`RecCompose.DigestChecked`,
`SetupRootChecked`).

## Open points

1. **The Props are proved in [`RecCompose`](../RecCompose/README.md)**, not here: π2's part by
   `RecCompose.recKnowledgeSoundness2_closed` and `RecCompose.Pi2KF.recCompleteness2_pi2_rec3_kf`, end to end by the
   reduction `RecCompose.recKnowledgeSoundness_reduction` and the `_fs` corollaries, at the real deployment from its
   evaluated premises (`formal/README.md`, "The recursive verifier: end theorems"). π2's part (`RecKnowledgeSoundness2`,
   `RecCompleteness2`) is proved there from `SpecOf` for the real circuit (from the circuit compiler, `RecCircuit`,
   and `SpecLink`), the tables' layer (`W`'s and `Q`'s claims as their tables' values: `run_u`, `run_digitsScale`,
   `RecPiop.sum_tablePoly_omega`), the Fiat–Shamir layer
   and the openings, and π2's circuit computing π1-rec3's graph (`RecCircuit.compile_sound`, and `call_inputs`: π2's calls
   rebuild π1's from the ports). The end-to-end corollaries add RecGraph's `Pi1GraphIsVerifier` and the hypotheses.
2. **The random-permutation theorems do not formally compose with the circuit's Keccak-f[1600]**. The Props at
   Keccak-f[1600] are premises whose readings are heuristic, not theorems; `Pi1CompletenessKeccak` at the recursion's
   prover has a proved random-permutation reading (`RecCompose.Pi1KF.pi1CompletenessFs_rpm`, `deltaRec3 < 2^-167`).
   For soundness the meeting point is the reduction `RecKnowledgeSoundnessReduction`: the reader applies the
   Fiat–Shamir heuristic to
   its two explicit derived adversaries (motivated by `uniKnowledgeSoundness_closed_rec3` and `hazard_prob`). The Props
   `Pi1FsKeccak`, `Pi1HazardKeccak` are false as stated for unbounded adversaries (they grind Keccak-f[1600] offline for
   free); `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest` (about the honest prover, justified by
   `uniCompletenessRec3_end_closed` and `hazard_prob`) are not provable. A random-permutation proof of the hazard bound
   for the derived adversary (as `hazard_prob` per uniform `t`) is not done: it would need the sponge-freshness
   argument of π1-rec3's game for challenge 49.
3. **`pi1Stream`** is a field of the deployment: where π2's witness holds π1's stream is the circuit compiler's (the
   stream's hashed bytes are free bits of π2's witness, `RecCircuit.Compiled.decodeStream`); the composition instantiates
   it. **`pi2`** is π2's circuit for π1's contract IV (the seed's constants): at the real deployment, the emitted tables
   at every IV.
4. **`PCS_OPEN`'s WHIR instance is a choice**, as in UniStatement: π1's calls on the plain layout of `2^vars` words (the
   layout word's byte 24), π2's on π2's public layouts (`quotient::opening`); the registry decodes as `machine::decode`.
5. **The degenerate events** (`all = 0`: `t ∈ V_{m+2}`, `c_h + c_q = 0`, a vanishing public denominator) reject; they
   matter for completeness only (`all_ne_zero_iff` names them).
