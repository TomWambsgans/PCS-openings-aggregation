<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# UniComplete

Milestone 4's completeness half for the univariate PIOP of leanVM 42422001 (`crates/leanvm_univariate`,
`SPEC.md` §13 for iteration 2): **a Lean honest prover** (`uniProverWith`, `proveWith`) following SPEC.md and the
Rust prover's message order, **its differential test** against the Rust (the review's honest prover and, through
its own cross-check, `prove_tiny`), and **the proof layers of `UniCompleteness D (uniProver D) δ`**
(`formal/UniStatement/UniStatement/Security.lean`). A library of `formal/EndToEnd` (`UniComplete`,
`srcDir = "../UniComplete"`), plain (non-`module`) Lean files, since it imports `E2ECompleteness`.

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build UniComplete     # every layer; the axiom guards
UNI_HONEST=<vectors> lake env lean ../UniComplete/UniCompleteTest/Runner.lean   # the differential test
```

## The prover (`UniComplete/`)

| module | what |
|---|---|
| `Basic.lean` | the writer `Wr`/`WrM` (`KeccakWriter`: `sendScalar`, `sendRoot`, `sendInteger`, `sampleW`), polynomials (`Poly` = CompPoly's computable `CPolynomial E`), the digits' `w_l`, the novel basis (`ofNovel`), subset sums |
| `Div.lean` | exact division by a monic polynomial in quadratic time (`longDiv`, `divM`, `modM`, `toNovel`), proved equal to Mathlib's `/ₘ`, `%ₘ` and CompPoly's `divByMonic` (`toPoly_divM`, `divM_eq`) |
| `Trace.lean` | the placed trace (`Trace`), `C1`'s and the setup's stacks (`c1Stack`, `setupStackOf`, `placeStack`), `z_T`, the fingerprints |
| `Bus.lean` | the leaves and the product heap (`tableLeaves`, `memoryLeaves`, `bytecodeLeaves`, `heapValues`) |
| `Quotients.lean` | the quotients as exact divisions of their numerators (tree, each block's leaf, the constraints), their chunks in basis `B` (`chunksB`) |
| `Batch.lean` | the batching sumcheck's prover (`denseWeight`, `batchRound`, `batchRounds`, the `λ³` matrices term) |
| `Prover.lean` | `C2` (`c2DataOf`), the values and relations at `t` (`atTOf`, the verifier's own `tablePart` on the values sent), `proveStreamWith` (the stream), `proveWith` (setup trees, IV, seed, stream, the five WHIR openings) |
| `Witness.lean` | `honestTrace D input rows q` (the placed trace read off Lv42's stack through `LeanIsa.cell`, rows moved by `rowPosition`, padding counters `1`), `uniProverWith` |
| `Claims.lean` | what a relation and a combined claim mean on the stacks (`termEval`, `Relation.Holds`, `Combined.Holds`) |
| `Honest.lean` | `TraceHonest` (what an honest placed trace satisfies) and `BadFp` (the bus challenges at which a divided fingerprint vanishes) |
| `FlockProver*.lean` | leanVM's Flock prover as a function (zerocheck with skip, lincheck, slices, ring map) |

The prover is mathematical, not an FFT implementation: columns are interpolated by the additive transform
(`PcsQuotient.Domain.coefficients`), numerators are products of CompPoly polynomials, quotients exact divisions.

## The differential test

`UniCompleteTest/Runner.lean`, interpreted, on the review's four honest point-claim proofs (Flock omitted, memory
and bytecode `2^4`/`2^5`, all six tables): the trace read back from the vector's `C1`, the Lean prover with the
review's stand-in roots writes **the same stream byte for byte (2,896 bytes each) and the same three stacks word
for word**; the Lean verifier accepts it. 4/4, about 6.5 minutes. For the three executions whose stream the Rust
prover's `prove_tiny` (branch `leanvm-univariate-prover2`) records, by the first 8 bytes of its Keccak-256 (memory
and bytecode `2^5, 2^4`, `2^4, 2^5`, `2^5, 2^5`), the Lean prover's stream has the same: 3/3.

## The end theorem (`UniComplete/End.lean`)

```lean
theorem uniCompleteness_end (D : Deployment) (hD : D.shape = reference) (hiv : D.programIv.length ≤ 2 ^ 16) :
    UniCompleteness D (uniProverRP flockProveH D) deltaUni
theorem deltaUni_lt : deltaUni < (2 : ℝ≥0∞)⁻¹ ^ 167
```

`uniProverRP flockProveH D` is `uniProverWith` over the random permutation's two calls (Keccak-256 as the sponge
over the permutation, the permutation itself for WHIR's proofs of work), with Flock's honest prover
(`FlockP.flockProve`). No hypothesis beyond the statement's own (`RowsFit`, `HonestRelation`). The bound is about
`2^-167.97`:

| term | event | where |
|---|---|---|
| `(2^24 − 1)/2^192` | a bus challenge `β` makes a divided fingerprint vanish (≤ `capBound reference = 10,878,976` per `α`) | `Core.badFpCard_reference` |
| `6/2^256` | the bus challenges' chain meets an earlier query | `ProbChain` |
| `3·2^17/2^192` | `y(t)` is a proper prefix of another point on `C1` (≤ `2·2^17` such `t`) | `ProbBadT.badTCard_reference` |
| `2^-200` | `t`'s query is not fresh (below `73·2^28/2^256`) | `ProbTFresh.tQueryFresh_reference` |
| `2^-304` | an opening's proof of work fails for every nonce below `nonceFuel` | `Core.coreFailsOnlyAtPow`, `ProbGrind` |
| `rpmError (2^48)` | the permutation as two random oracles, `≤ 2^48` blocks (prover `≤ 3·2^46`) | `FlockCost`, `ProverCost` |

Off the bad events the honest proof is accepted (`Core.coreAccepts_of`, `Core.accepts_of_trace`): the verifier's run
synchronises with the prover's stream (`SyncVerifier.runWithH_syncs`), every relation at `t` holds and the batch's
terminal is zero (`CoreBatch.batchSyncsAt_front`, from `Mapping.honestTrace_honest`, `AlgC`, `AlgH`, `FlockP`,
`Combine`, `BatchProof`), and the five `PCS_OPEN` calls accept WHIR's honest openings (`Whir.pcsOpen_honest` at
`27, 27, 24, 28, 28` variables; the claims' values, `CoreRun.streamValues`; Flock's matrices' point,
`CoreRun.flockProve_matrixPoint`). The probability layer (`Prob*.lean`) stages the run at the bus challenges and
at `t` (`ProbSplit`, `ProbStaged`); `CoreRun.front_challenges` identifies the staged challenges with the prover's.

The composition: `CoreRun.lean` (the claims' values, Flock's matrices' point, the staged challenges are the
prover's), `CoreBatch.lean` (`BatchHolds` at the prover's state: the stacks' sizes, Flock's pending matrices in the
batch's forms, `¬ BadT` as the slot condition, `C2`'s terms covering their columns, every relation at `t`),
`Core.lean` (`accepts_of_trace`, `coreAccepts_of`, `coreFailsOnlyAtPow`, `badFpCard_reference`), `End.lean`. See
`UniComplete.lean` for every module.

## What the proof found

* **Quotient sizes.** Every honest run under `RowsFit` fits the quotients' sizes: the tree quotient (`≤ 2^h`), the
  memory's and bytecode's leaves (`≤ 2^r − 2`), the tables' (they need `leastRows ≤ (M − 1)(n − 1)`, `M ≥ 3`), the
  constraint quotient (every trace). Counts below a table's `leastRows`, which F1 allows (any count `≤ 2^h`), cannot
  be proved honestly at that shape class; heights `29–31`, which `Shape.validate` allows, exceed the prover's
  interpolation (the `28`-vector basis), and such stacks exceed WHIR's `2^28` words anyway.
* **A completeness gap at `t`.** If `y(t)` is a proper prefix of another point on `C1`, `combine` merges the slot
  terms with that point's and the honest proof is rejected (the Rust has the same: `dense_weight` truncates,
  `weight_at` does not). At most `2·2^17` such `t` per Flock point: the `3·2^17/2^192` term.
* **`t`'s query is `64` bytes**, a Merkle node's length, so its freshness is not by length; it is proved by the chain
  of challenges and `C2`'s tree never asking a `32`-byte input (`ProbTFresh`).
* **Costs.** The prover's Keccak-f blocks are below `3·2^46` (the five WHIR openings alone about `2^47.43`), the
  stream below `2^40` bytes, for a program IV of at most `2^16` bytes.
* Flock has no bad event; no other prover, verifier or SPEC discrepancy was found.
