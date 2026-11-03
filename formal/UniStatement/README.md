<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The structure follows formal/Statement/README.md. -->

# UniStatement

The univariate PIOP for leanVM 42422001 (`crates/leanvm_univariate`, `SPEC.md` there), **at iteration 2**
(`leanvm-univariate` `ad49e74`: `SPEC.md` §13's entries 1–13; milestone 1 was `cee6363`, reviewed at `b948bfc`,
`REVIEW-M1.md`), in the files a reviewer reads: **its verifier as computable Lean**, module by module as
`verifier.rs`, the setup constants as data, the whole verifier with `PCS_OPEN`, the map from its commitments to
`formal/Lv42`'s stack, and **the end statements**, `UniKnowledgeSoundness` and `UniCompleteness`, against leanVM
42422001's relation (`Lv42.Protocol.M3Holds`). Statements only: nothing is proved yet. No `sorry`, no
`native_decide`, every definition the statements rest on on Lean's three axioms (`UniStatement.lean`'s guards).

It is a library of `formal/EndToEnd` (`UniStatement`, `srcDir = "../UniStatement"`), as `Lv42` is, so it shares
that workspace's built `lean_vm` packages (leanerVM `6175f1a0`), `Lv42` and `PcsQuotient` (`formal/Statement`),
whose definitions it reuses: `K`, `E`, Keccak-256 over a permutation, the random-permutation model, the WHIR
opening (`PcsQuotient.openingWith`) and commitment (`commitWith`), the extractor's replay, Merkle inversion and
decoders.

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build UniStatement        # the library; the axiom guards
# the vectors (from the repository root; absolute paths: cargo runs the tests in the crate's directory):
# the measured shapes, the review's honest proofs, and the real prover's proofs (prover2's tests/vectors/*.txt)
UNI_VECTORS_OUT=$PWD/uni_vectors.txt cargo test --release -p leanvm_univariate --test lean_vectors -- --ignored --nocapture lean_vectors
UNI_HONEST_OUT=$PWD/uni_honest.txt cargo test --release -p leanvm_univariate --test review_honest -- --ignored --nocapture lean_honest_vectors
UNI_REAL_VECTORS_DIR=<prover2's tests/vectors> UNI_REAL_OUT=$PWD/uni_real.txt cargo test --release -p leanvm_univariate --test lean_vectors -- --ignored --nocapture lean_real_vectors
cat uni_vectors.txt uni_honest.txt uni_real.txt > all.txt
UNI_VECTORS=$PWD/all.txt lake env lean ../UniStatement/UniStatementTest/Runner.lean   # the runner
```

## Reading order

1. [`Basic.lean`](UniStatement/Basic.lean): `E::new`, `E::pow`, `eq_kernel`, `multilinear_eval`, `poly_eval`,
   `Scalar::bits` (`intBits`).
2. [`Transcript.lean`](UniStatement/Transcript.lean): the contract's Keccak-256 chain over calldata
   (`KeccakChannel`), over a permutation `F` in any monad; the packed integers (`nextInteger`); `sumcheck`; the
   checks collected.
3. [`Domain.lean`](UniStatement/Domain.lean): the Cantor basis, the digits, the coordinate functionals, the
   vanishing polynomials, **the active rows at fixed cosets** and their `Z_act` from a count's bits.
4. [`Tables.lean`](UniStatement/Tables.lean): the six tables, their flushes as `Form`s, their counters.
5. [`Heap.lean`](UniStatement/Heap.lean): the product heap's blocks.
6. [`Claims.lean`](UniStatement/Claims.lean): columns, relations, `combine` (the powers of `ρ`, the prefix merge).
7. [`Flock.lean`](UniStatement/Flock.lean) (**swappable**): BLAKE2s by Flock (`flock_min::verify`,
   `verify_deferred`, `Pending`), the ring map in tower order (`ring_tower.rs`).
8. [`Stacks.lean`](UniStatement/Stacks.lean): the stacks' layouts and a claim's weight at a point (the ring-switch
   term by its map).
9. [`Batch.lean`](UniStatement/Batch.lean) (**swappable**): the batching sumcheck to point claims, with Flock's
   matrices' reduction as its `λ³` term.
10. [`Verifier.lean`](UniStatement/Verifier.lean): `Shape` (the shape class) and `Shape.validate`, `Shape.Valid`,
    `Shape.RowsFit`, the quotients' sizes from the shape (`Shape.c2Columns`, `layoutsOf`), and **`reduceWith`**,
    `verifier.rs`'s `reduce`.
11. [`Run.lean`](UniStatement/Run.lean): the run on calldata (`runWith`, `run`), the verdict, the row counts a
    stream announces (`rowsOf`, `rowsBytes`), the setup constants (the measured shapes, the program's IV).
12. [`Opening.lean`](UniStatement/Opening.lean): the layout words, the contract's IV (`contractIvWith`), the
    reference setup roots, `PCS_OPEN` as the Statement's opening and its inputs word for word (`pcsCalls`), and
    **`verifyWith`**, the whole verifier (the main line: the run, then five calls).
13. [`Mapping.lean`](UniStatement/Mapping.lean): basis `B` ↔ values, the rows' order (`rowPosition`), **`C1`
    read as Lv42's stack**, the setup's tables.
14. [`Security.lean`](UniStatement/Security.lean): the deployment, the setup and its IV, the extractor, the
    experiments, **`UniKnowledgeSoundness`**, **`UniCompleteness`**.
15. [`Rec.lean`](UniStatement/Rec.lean) (the recursion's inner proofs, `leanvm-rec` 4247e37; not imported by
    `UniStatement.lean`, so that nothing above is rebuilt): **`FsShape`** (`main`, `rec1`, `rec2`, `rec3`: the Rust's
    `Main`, `Rec`, `Rec2`, `Rec3`) and **`walk`** (`Slices::TowerWalk`), parameters of `Fs` copies of the functions
    they change (`Flock.zerocheckFs`, `frontFs`, `verifyFs`, `verifyDeferredFs`, the new `verifyWalkedFs` with
    `walkedTerminal` and the BLAKE2s circuit's walk `blake2sRowValues`; `batchFs` with the narrow challenges
    `sampleNarrow` and the paired rounds `sumcheckPairsDrawn`, `pairPoint`, `cantorBeta1`; `reduceWithFs`,
    `runWithFs`, `runFs`, `verifyWithFs`; the IV for a variant `contractIvForWith`), `main` and no walk the default.
    At the default each is the original (`…Fs_main`, `reduceWithFs_main`, `runWithFs_main`, `runFs_main`), so the
    existing statements and proofs keep their meaning. **π1-rec3** (`FLOCK_REC3`, the recursion's) is
    `runFs reference iv publicInput stream (.flock flockMain) .point .rec3 true`, its IV
    `contractIvFor reference (.flock flockMain) .rec3 true programIv referenceRoots`, its three calls `pcsCalls`;
    `formal/RecGraph`'s runner checks it against the Rust verifier and π1-rec3's recorded graph on the real proof
    (`main_line_rec3.txt`) and 24 mutated and random streams.

## Rust → Lean

| Rust (`crates/leanvm_univariate` and `crates/leanvm_flock_gas` at `ad49e74`) | Lean (`UniStatement.`) |
|---|---|
| `transcript.rs`: `KeccakChannel::{next_scalar, next_root, next_integer, sample, finish}`, `keccak_seed`, `challenge_of` | `nextScalar`, `nextRoot`, `nextInteger`, `sample`, `finish`, `seedWith`, `PcsQuotient.Transcript.challengeOf` |
| `transcript.rs`: `Checks::Collect`, `require_zero`; `scalar.rs`: `Scalar::bits` | `Chan.zeros`, `requireZero`; `intBits` |
| `transcript.rs`: `sumcheck`, `sumcheck_round_poly` | `sumcheck`, `roundPoly` |
| `multilinear.rs`: `eq_kernel`, `eq_eval`, `multilinear_eval`, `poly_eval`, `log2_ceil`, `dot` | `eqKernel`, `eqEval`, `multilinearEval`, `polyEval`, `log2Ceil`, `dot` |
| `domain.rs`: `beta`, `point`, `point_e`, `digits`, `coordinate_functionals`, `coordinates_at`, `prefix_vanishing`, `suffix_vanishing`, `vanishing_ratio`, `prefix_vanishing_from_bits`, `coset_offset`, `active_positions`, `is_active`, `active_vanishing_from_bits` | the same names in camel case |
| `layout.rs`: `Form`, `Flushes::{pair, state_derived, state_step, counted, bytecode, memory, memory_cols}`, `flushes_*`, `tables`, `count_columns`, `BLAKE2S_SLOTS`, `SEP_*` | `Form`, `Flushes.*`, `flushes*`, `tables`, `Table.countColumns`, `blake2sSlots`, `sep*` |
| `heap.rs`: `HeapLayout::new`, `Leaves`, `Block` | `HeapLayout.new`, `Leaves`, `Block` |
| `claims.rs`: `Commitment`, `Column` (and `id`), `Term`, `Relation`, `Combined`, `Relations::{push, equal, combine}` | the same; `combine` |
| `stacks.rs`: `StackLayout::{new, words, limbs}`, `EqCache::{row, row_from, selector}`, `limb_basis`; `verifier.rs`: `weight_at`, `RING_TWIST` | `StackLayout.new`, `words`, `limbs`, `rowEq`, `selector`, `limbBasis`, `weightAt` (no cache, no shared work; the same values), `ringTwist` |
| `flock_min.rs`: `verify`, `verify_deferred`, `front`, `ring_end`, `known_weights`, `Pending::{new, rounds, has_slices, terminal, combination}`, `zerocheck`, `row_low_weights`, `reduce_terminal`, `Variant`, `Slices` (with `Tower`), `End` | `Flock.verify`, `Flock.verifyDeferred`, `Flock.front`, `Flock.ringEnd`, `Flock.knownWeights`, `Flock.Pending.*`, `Flock.zerocheck`, … |
| `flock.rs`: `phi`, `fixed_challenges`, `lagrange_weights`, `ring_map`, `ring_switch_weight` (leanVM's order) | `Flock.phi`, …, `Flock.ringMap`, `Flock.ringSwitchCoefficients` |
| `ring_tower.rs`: `ring_map`, `Tower::{theta, leaves}`, `conjugate`, `into_subfield`, `target`, `coefficients`, `weight_at` | `Flock.towerRingMap`, `Flock.towerTheta`, `Flock.towerLeaves`, `Flock.conjugate`, `Flock.intoSubfield`, `Flock.towerTarget`, `Flock.towerCoefficients`, `Flock.towerWeightAt` |
| `verifier.rs`: `Shape` (`heights`, `heap`, `constraint_vars`, `validate`, `least_rows`), `degree`, `factor_columns`, `sent_columns`, `linearise`, `tuple_degree`, `chunks`, `quotient_terms`, `table_part`, `layouts`, `stack_layouts`, `batch`, `reduce`, `Reduced`, `Opening`, `Claims`, `Blake2s`, `FLOCK_*` | `Shape` (the heights), `Shape.validate`, `Shape.leastRows`, `degree`, `factorColumns`, `sentColumns`, `linearise`, `tupleDegree`, `chunks`, `quotientTerms`, `tablePart`, `layoutsOf`, `layouts`, `batch`, **`reduceWith`** (its steps 0, 5 and 6 as `countBits`, `constraintRelation`, `heapRelations`), `Reduced`, `Opening`, `ClaimsMode`, `Blake2s`, `flock*` |
| `contract.rs`: `rust_verifier`, `NAME`, `SetupRoots::REFERENCE`, `shape_bytes`, `layout_word`, `layout_words`, `contract_iv`, `calls` (`opening_words`, `combined_words`); `machine.rs`: `element_word`; `shapes.rs`: `WORKLOADS`, `PROGRAM_IV`, `Shape::of` | `runWith`/`run`, `name`, `referenceRoots`, `shapeBytes`, `layoutWord`, `layoutWords`, `contractIvWith`/`contractIv`, `pcsCalls` (`openingWords`, `combinedWords`), `elementWord`; `workloads`, `programIv`, `shapeOf`/`shapeWith` |
| `machine.rs`: `PCS_OPEN`'s ABI (mocked, `attesting_all`) | `pcsOpenWith` = `PcsQuotient.openingWith` on `plainLayout` (the layout word's `vars`) |
| `contract.rs`: the five calls (C1, C2, setup, A0, B0) | `verifyWith` |

Deviations, none changing a value: a `List`/`Array` stands for a `Vec`, an out-of-range read gives `0` where the
Rust would panic (it never does on the tables and valid shapes); the degrees are `ℕ`, whose subtraction saturates
as the Rust's `degree` does (F5); `EqCache` and lever 1c's shared work are not transcribed (`weightAt` computes the
same products term by term, the twisted points once per point: field arithmetic is exact, so the regrouping gives
the same values); lever 1b's `XOR` network is code generation (`towerTarget` adds each leaf's slices directly, the
sums the network computes); `End::Ring`'s `weight` of `Slices::InContract`, which the univariate verifier never
reads, is not computed; a row count is an `ℕ` (the Rust holds it in a scalar's low limb). **The shape is the
contract's class** (iteration 2, F1): `Shape` holds the memory, the bytecode and the heights (the Rust's `Shape`
holds row counts, of which only `⌈log₂ rows⌉` is read: `shapeWith`); the row counts are the stream's.

## v2 changes (iteration 2, for the branches that build on UniStatement)

Every public name below changed or is new; every other name is milestone 1's, unchanged (the modules too).
**Signatures that changed** (a rebase must update the call sites):

| Name | Milestone 1 (`a998edd`) | Iteration 2 (this branch) |
|---|---|---|
| `Shape` | 4 fields: `logMemory logBytecode heights capacityRows` | 3 fields: `logMemory logBytecode heights`; **`Shape.capacityRows`** is now a definition (`heights.map Shape.leastRows`, same type) |
| `Shape.Valid` | heights `0` (XOR to DEREF) or `≥ 2`, capacities of their heights, memory and bytecode `≥ 2^2` | `heights.length = 6 ∧ shape.validate true` (F5: memory `≥ 2` cells, heights `≤ 31`, BLAKE2S `≥ 7`) |
| `Shape.RowsFit` | the same form, capacity the field | the same form, capacity `leastRows` of the height |
| `reduceWith F shape rows publicWords blake2s mode` | rows an argument | **`reduceWith F shape publicWords blake2s mode`**: the counts are read from the stream; throws `invalidShape` |
| `constraintRelation shape rowCounts parts …` | `rowCounts` | **`constraintRelation shape parts …`** (no `Z_pad`: counters nonzero on every row) |
| `heapRelations shape rowCounts parts …` | `rowCounts` | **`heapRelations shape active parts …`**, `active` each table's `Z_act(t)` |
| `Reduced` | 5 fields | 6: `layouts` added |
| `batch F combined layouts bitSlice` | returns the openings | **`batch F combined layouts bitSlice (ringMap := none) (pending := none)`** returns `(openings, Option Flock.MatrixClaim)` |
| `weightAt claim layout r` | | `weightAt claim layout r (ringMap := none)` (old calls unchanged) |
| `runWith F shape rows iv publicInput announced stream blake2s mode` | rows and seed extras | **`runWith F shape iv publicInput stream blake2s mode`** |
| `run shape rows iv publicInput stream blake2s mode` | | **`run shape iv publicInput stream blake2s mode`** |
| `rowsBytes` | 8-byte words, absorbed in the seed (provisional) | 4-byte big-endian words, the stream's first 24 bytes |
| `UniProof` | 7 fields, `rows` one | 6 fields; **`UniProof.rows`** is now a definition (`rowsOf proof.stream`, same type: `proof.rows` still reads) |
| `verifyWith F shape iv roots input proof` | `RowsFit` checked first; vars from `stackVars` | the same signature; no `RowsFit` check (the run range-checks the counts, as the contract does); each call's `vars` from its layout word |
| `shapeBytes` | `Security.lean`, 8-byte words incl. capacities (provisional) | `Opening.lean`, the Rust's 8 bytes (`log_memory`, `log_bytecode`, six heights) |
| `Deployment.ivWith F roots` | `keccak(programIv ‖ roots ‖ shapeBytes)` (provisional) | `contractIvWith F shape programIv roots` (F2: tag, program IV, roots, shape, the five layout words) |
| `Deployment.logMemory_pos` | | the same statement, re-proved from the new `Shape.Valid` |
| `c1RootOf` | the stream's bytes `0..32` | bytes `24..56` (after the row counts) |
| `lv42Column` (so `lv42Stack`, `uniExtractor`) | table row `x` at `C1`'s row `x`, read at `τ` variables | the same signature; Lv42's row `x` at `C1`'s `rowPosition count h x`, read at the shape's `h`; `QFLOCK`'s instances likewise |
| `flockMain` | `⟨3, .weighted⟩` | `⟨3, .tower⟩` |
| `workloads` | literal | derived from `measured` (the same values) |

**New names**: `UniError.invalidShape`; `nextInteger`, `intBits`; `prefixVanishingFromBits`, `cosetOffset`,
`activePositions`, `isActive`, `activeVanishingFromBits`; `Shape.leastRows`, `Shape.capacityRows` (now a
definition), `degree`, `Shape.validate`, `tableDegrees`, `Shape.constraintDegree`, `Shape.leafDegree`,
`Shape.c2Columns`, `layoutsOf`, `countBits`; `Flock.Slices.tower`, `Flock.towerStages`, `Flock.towerRingMap`,
`Flock.conjugate`, `Flock.intoSubfield`, `Flock.towerTheta`, `Flock.towerLeaves`, `Flock.towerTarget`,
`Flock.towerCoefficients`, `Flock.towerWeightAt`, `Flock.knownWeights`, `Flock.Pending` (`new`, `rounds`,
`hasSlices`, `matrixClaim`, `skipAt`, `terminal`, `combination`), `Flock.Front`, `Flock.front`, `Flock.ringEnd`,
`Flock.verifyDeferred`; `ringTwist`, `StackLayout.words`; `rowsOf`, `measured`; `digestOfBytes32`, `bytesOfHex`,
`referenceRoots`, `layoutCode`, `a0Code`, `b0Code`, `layoutWord`, `layoutWords`, `layoutWordVars`, `ivTag`,
`contractIvWith`, `contractIv`, `be64`, `numberWord`, `elementWord`, `rootWord`, `combinedWords`, `openingWords`,
`pcsCalls`; `rowPosition`. Unchanged but moved in the reading order: `Stacks.lean` now imports `Flock.lean`.

**The Props** (`UniKnowledgeSoundness`, `UniCompleteness`) are textually unchanged; what changed under them: the
row counts are the stream's (`UniProof.rows`), the verifier's IV is the contract's (`Deployment.ivWith`), and
`lv42Stack` reads the rows in their order (`rowPosition`).

## The setup constants as data

* The measured shapes (`measured`, `workloads`: 32 to 2,000 signatures, `reference` the 1,000), the program's IV
  (`programIv`), the transcript's name (`name`), the bytecode's `2^19` instructions.
* The layouts (`layoutsOf shape`: `C1`, `C2`, setup; `C2`'s columns `Shape.c2Columns`) and the heap
  (`Shape.heap`) are functions of the shape, as in the Rust; the test compares the run's with them, their
  variables with the Rust's, their words through the layout words, and their offsets through every claim.
* The contract's constants (F2): the reference setup roots (`referenceRoots`, `SetupRoots::REFERENCE`'s bytes
  read as digests: `digestBytes` gives the Rust's bytes back), the five layout words (`layoutWords`) and the
  contract's IV (`contractIv`), each compared with the Rust's.
* The setup's tables (`Mapping.lean`): `setupStack` (the bytecode's 16 tuple slots in basis `B`, slot `s` of
  coefficient `k` at word `s + 16 k`, and the addresses `g^i`) and `matrixStack` (Flock's `A0`, `B0`,
  `2^28` words); their roots are the WHIR commitments over `π` (`setupTreesWith`), the IV their binding with
  leanVM's program IV, the shape and the layout words (`Deployment.ivWith`).

## The statements (`Security.lean`, verbatim)

```lean
structure Deployment where
  prog : Program
  shape : Shape
  programIv : List UInt8
  valid : shape.Valid
  logBytecode_eq : shape.logBytecode = prog.logSize

abbrev Deployment.inst (D : Deployment) (rows : List ℕ) : Lv42.Protocol.M3Instance :=
  Lv42.Protocol.leanIsaInstance Lv42.Protocol.Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows)

def Deployment.Relation (D : Deployment) (rows : List ℕ) (input : Vector UInt8 32) (q : D.Stack rows) :
    Prop :=
  Lv42.Protocol.M3Holds (D.inst rows) (publicInputOf input.toList) q

noncomputable def uniSoundnessExperiment (D : Deployment) (A : UniAdversary) : ProbComp UniOutcome :=
  runWithRandomPermutation do
    let trees ← setupTreesWith queryPermutation D
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let accepted ← D.verifierWith queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript)

def UniBreaksKnowledgeSoundness (D : Deployment) (ext : UniExtractor D) (z : UniOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ q, ext z.1.1.1 z.2.1 z.2.2 z.1.1.2 = some q ∧ D.Relation z.1.1.2.rows z.1.1.1 q

def UniKnowledgeSoundnessWith (D : Deployment) (ext : UniExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : UniAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← uniSoundnessExperiment D A}[UniBreaksKnowledgeSoundness D ext z] ≤ ε Q

def UniKnowledgeSoundness (D : Deployment) (ε : ℕ → ℝ≥0∞) : Prop :=
  UniKnowledgeSoundnessWith D (uniExtractor D) ε

noncomputable def uniCompletenessExperiment (D : Deployment) (P : UniProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← setupTreesWith queryPermutation D
    match ← P input rows q with
    | none => return false
    | some proof => D.verifierWith queryPermutation trees.roots input proof

def UniCompletenessWith (D : Deployment) (P : UniProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    Pr{let v ← uniCompletenessExperiment D P input rows q}[v = false] ≤ δ

def UniCompleteness (D : Deployment) (P : UniProver D) (δ : ℝ≥0∞) : Prop := UniCompletenessWith D P δ
```

`UniAdversary := SetupRoots → OracleComp RandomPermutationOracles (Vector UInt8 32 × UniProof)`;
`UniProof` is the stream (its first 24 bytes the six row counts, `UniProof.rows := rowsOf stream`) and the five
opening proofs; `UniExtractor D := Vector UInt8 32 → List (List UInt8 × Digest) → OracleQueryLog → (proof :
UniProof) → Option (D.Stack proof.rows)`; `UniProver D := Vector UInt8 32 → (rows : List ℕ) → D.Stack rows →
OracleComp RandomPermutationOracles (Option UniProof)`; `D.Stack rows := LeanVM.Protocol.Column (leanIsaμ D.prog
(D.sizes rows))`; `D.HonestRelation` is `M3Honest`; `D.verifierWith F roots = verifyWith F D.shape (D.ivWith F
roots) roots`, the IV the contract's (`contractIvWith`: tag, program IV, roots, shape, layout words). The model,
`QueryCostAtMost`, `permutationCallCost`, `Pr{…}[…]` are mumbai's and `formal/Statement`'s. **The extractor**
`uniExtractor` is explicit and computable: the transcript's and the setup's Keccak-256 evaluations replayed
(`PcsQuotient.Replay`), `C1`'s Merkle tree inverted under the root the stream names (`c1Word`, the root after the
row counts), the candidate stacks by the fast path, Gao's unique decoder, then the list decoder (`fastStacks`,
`uniqueStacks`, `decodeStacks` at `C1`'s `2^μ`, rate `1/2`), each read as Lv42's stack (`lv42Stack`) at the
proof's row counts, the first satisfying `M3Holds` (decidable). The bounds `ε`, `δ` are parameters.

## The map onto Lv42

`M3Holds I input q = ConstraintsVanish ∧ Balanced ∧ CountsNonzero ∧ PublicLinesHold ∧ aux` (`aux`: the Flock
region `FlockRegion.Holds`), for `I = leanIsaInstance blake2sFlockSpec prog s`, `s = sizesOf shape rows` (the
shape's memory, the proof's row counts; `prog.logSize = logBytecode`), `input = publicInputOf bytes` (lane `k`
the 64-bit big-endian word `k` of the calldata's public input, as the verifier reads it), `q` Lv42's stack of
values (`LeanIsa.layout`: committed columns largest first, the `BLAKE2S` limbs read at `QFLOCK`'s strided
slots).

| `C1` (`UniStatement.Column`) | Lv42 (`LeanIsa.Col`) | encoding |
|---|---|---|
| `memory k`, `k < 3`; `memory 3` | `memCol k`: `MEM_LO, MEM_HI, MEM_TOP`; `MFCNT` | basis `B`, `2^logMem` rows |
| `bytecodeFinal` | `bfcntCol` (`BFCNT`) | basis `B`, `2^logBytecode` |
| `qflock` | `flockCol` (`QFLOCK`) | values in both; Lv42's instance `x` is `C1`'s instance `rowPosition x` |
| `table t i`, not a `BLAKE2S` limb | `⟨opIdx t, i⟩` | basis `B`, `2^h_t`; Lv42's row `x` is `C1`'s row `rowPosition x` |
| `table 5 i`, `9 ≤ i < 27` (the copies) | none: Lv42 reads limb `i − 9` at `QFLOCK`'s cell `slot + 256 x` | `Q_W`: copy = slot on every row |
| `inverse t` (`z_T`) | none | `Q_W`: `z_T Π c = 1` on every row |
| setup `bytecodeTuple`, `address` | `Coord.known (entryColumn prog k)`, `idxColumn` (verifier-known) | the setup, honest |

**The rows' order** (iteration 2, F1b): Lv42's executed rows are a table's first `rows`; the PIOP places them
at the fixed cosets of the count's set bits (`activePositions`), `q_flock`'s instances with them. `rowPosition
count h` maps Lv42's row `x < count` to the `x`-th active row and a padding row `x ≥ count` to the
`(x − count)`-th other row, a bijection of `[0, 2^h)`; Lv42's `τ = ⌈log₂ rows⌉ ≤ h` reads the first `2^τ`
images. The clauses: **ConstraintsVanish**: JUMP's two constraints in `Q_W`, on every row (as Lv42's);
**Balanced**: the heap (tree, root, leaves; a table's leaf identity times `Z_act`, the cosets'), the boundary as
Lv42's (the state push `(1, 1)` and pull `(g^(2^lb−1), 1)` in the root identity; the memory's and bytecode's
push with count 1, pull with the final counts, in their leaves); **CountsNonzero**: `z_T` in `Q_W` on every row;
**PublicLinesHold**: the three lines in `Q_W`; **aux**: Flock on `q_flock`. Padding rows are free on both sides
(their leaves are `1`; Lv42 flushes executed rows only).

## What is tested, what is defined

**Tested** (`UniStatementTest/Runner.lean`, run with `lake env lean`: the interpreter on the compiled
definitions' IR, not the kernel), on **150 vectors** of the Rust at `ad49e74`:

* **The measured shapes** (114, `tests/lean_vectors.rs`'s `lean_vectors`): the 7 configurations of `tests/gas.rs`
  at the reference shape and leanVM's skip in weighted mode (so every Flock path: tower order with one ring term
  and the deferred matrices, tower order with 64 coefficients, the bit-slice end deferred (lever 5a) and not,
  leanVM's order deferred and not, no Flock), the main line at the five other measured shapes, extension W × B
  at the largest; random streams (random counts, and the shape's counts), accepting streams (each check solved
  for the scalar read just before it, the seed's IV the contract's; one under another program IV), **other row
  counts that fit** (`counts`: none, one, `leastRows`, a full table, `2^h − 1`, random, so every coset pattern
  of F1b), **a count out of range** (`badcount`), mutated, truncated, extended streams.
* **The review's honest proofs** (20, `tests/review_honest.rs`'s `lean_honest_vectors`, adapted there to
  iteration 2: the counts announced, the rows at their fixed cosets, padding counters nonzero; real VM runs of 15
  to 31 cycles over all six tables, Flock omitted, memory and bytecode of `2^4`, `2^5`, both claim modes; three
  mutations of each point-claim proof). The real prover's `prove_tiny` writes the same streams byte for byte
  (prover2 `0dd319b`).
* **The real prover's proofs** (16, `lean_real_vectors`): the four real 1,000-signature proofs of
  `leanvm-univariate-prover2`'s `tests/vectors` (`e96e777`: main line, extension B, leanVM's skip, Flock omitted),
  three mutations each (anywhere, a row count, the last scalar).
* On every vector, the Lean and the Rust agree on **every value**: the result (and its error), every challenge,
  every value required zero (the counts' range checks first), the verdict, the number of relations, each stack's
  variables, every opening handed to `PCS_OPEN` (point claims: point and value; weighted and bit-slice claims:
  points, terms in order, value, relations), Flock's `A0`/`B0` claims; the row counts the stream announces; the
  five layout words and the contract's IV (`contractIv` of the program's IV at the reference roots); the run's
  three layouts are `layoutsOf` the shape; every shape is valid (`Shape.validate`). On the real proofs, **every
  `PCS_OPEN` input the contract calls with** (root, layout word, claims), word for word (`pcsCalls`).
* On the honest proofs with their committed stacks: the stream announces the execution's counts, which fit
  (`RowsFit`); the Lean verifier's point claims are **true of the committed `C1`, `C2` and setup stacks**; `C1`
  read as Lv42's columns (`lv42Column`, what `lv42Stack` stacks, the rows through `rowPosition`) satisfies
  **`ConstraintsVanish`, `Balanced`, `CountsNonzero` and `PublicLinesHold`** of Lv42's instance (its own flushes,
  constraints, counts, boundary blocks, public lines and Flock slots; `aux` is not checked: the prover omits
  Flock), with controls (another public input fails the lines, one changed `C1` coefficient fails the bus);
  `setupStack` is the honest setup (the addresses word for word, every run instruction's slots read back). The
  clauses are evaluated on the columns, not through `M3Instance.column`, which reads each cell of the
  `2^15`-word stack through the layout's lift, more than the interpreter affords.
* The Rust's unit tests on the Lean definitions: `domain.rs`'s and `heap.rs`'s (iteration 2's
  `fixed_cosets_from_the_bits`, `prefix_vanishing_from_the_bits` included), `ring_tower.rs`'s (the leaves are
  `x^i`'s coordinates, 1,938 slice terms; the coefficients, the target `Σ_i x^i Φ(s_i)` and the weight at a
  point are the map's; leanVM's order gives another target, a control), `rowPosition` (a bijection, the executed
  rows onto the cosets), the mapping's transform pair, and **the bridge to Lv42's instance** (for each opcode
  table, on random rows, the multisets of pull and push tuples of `layout.rs`'s forms are Lv42's flushes, with a
  control; the counter columns, the widths and the constraints agree).

**Results** (h1, this branch): **150/150 vectors agree on every value; 69 accepted by both, 81 rejected by both**
(accept 22/0, counts 16/0, badcount 0/8, random 3/19, mutate 13/17, truncate 0/8, extend 0/8, honest 8/0,
honest-mutate 0/12, real 4/0, real-mutate 3/9); the 40 checks on the four honest proofs with stacks and the 42
self-tests (18 of the domain, heap, tower and mapping, 24 of the bridge) all hold. About 9 minutes. The random and
mutated acceptances are the configurations with no check in the contract but the counts' range (weighted mode
with the bit-slice end or no Flock, and extension B under the point ABI, lever 5a: its batch terminal is the
bit-slice claim), and mutations after the last check (weighted mode).

The vector writer (`tests/lean_format`) now reads the counts (`Logging::next_integer`: at `ad49e74` it had
none, the trait's default `unimplemented!`, so `lean_vectors` and `lean_honest_vectors` panicked at the stream's
first read there) and writes the setup lines (`PROGRAMIV`, `CONTRACTIV`, `LAYOUTWORDS`) and the counts
(`COUNTS`); `accepting` streams announce counts that fit (the shape's, or given).

**Defined, not tested**: `PCS_OPEN`'s WHIR (the Rust has only a mock), the setup's commitments, the stacking of
`lv42Stack` into the `2^15`-word vector (Lv42's own `Blocks.stackColumn`), the extractor, the experiments, the
Props; `verifyWith`'s run and calls are the tested `run` and `pcsCalls`'s claims.

## Open points

1. **The honest prover is not transcribed**: `UniCompleteness` takes the prover as a parameter. The Rust's
   (`src/prover`, adapted to iteration 2 on `leanvm-univariate-prover2`) and the review's (`tests/review_honest.rs`,
   tiny runs without Flock) are tested against the Lean verifier through their proofs.
2. **`PCS_OPEN`'s WHIR instance is a choice**: the Rust mocks the precompile; the statements take the
   Statement's opening (label, version, layout identifier, rate `1/2`) on the plain layout of each stack, its
   size the call's layout word's `vars` (byte 24). The word's `placed` (the words the blocks fill) and code are
   bound by the contract's IV, not read by this opening (the Rust's precompile reads `placed` to know the
   committed lanes). The root word's reading (here: the two halves as `digestOfScalars` for the stream's roots,
   the bytes as `digestOfBytes32` for the reference setup roots) is the Rust's: its prover sends a root as its two
   WHIR scalars (`prove::halves`, `hash_to_scalars`; `crates/leanvm_rec/REVIEW-REC.md`, R1: before, it sent the
   hash's bytes, which this reading names as another root), and the setup roots are the commitments' hashes
   (`prover::setup::roots`). The extensions
   (weighted claims, the bit-slice claim) have no opening here; `verifyWith` is the main line's.
3. **The row counts and the shape class** (F1): the verifier accepts any count `c ≤ 2^h`, `0` included; the
   quotients are sized for `leastRows h = 2^(h−1) + 1`, so an honest prover needs `c ≥ leastRows h`
   (`Shape.RowsFit`, completeness's hypothesis), and soundness must hold at every `c ≤ 2^h` (Lv42's `τ` may then
   be below `h`; `lv42Column` reads the first `2^τ` rows of `rowPosition`).
4. **REVIEW-M1 F7**: the public input is read as big-endian words (the contract's, documented at `ad49e74`);
   leanVM's digest is little-endian. One function (`publicWordsOf`, which `publicInputOf` shares) changes when the
   contract does.
5. **`EqCache`'s slot rows** are keyed by the point since iteration 2 (lever 1c); `weightAt` never shared them.
6. **Weighted mode with Flock's bit-slice end or no BLAKE2s argument** makes no check in the contract (every
   stream of the right length with counts in range is accepted; `PCS_OPEN` checks all), the point-claim ABI with
   the bit-slice end (extension B) leaves its batch terminal to the bit-slice claim (lever 5a), and every check of
   the main line is affine in the scalar read just before it: sound only with the openings.
7. **Not proved**: the Props; the bridges `reduceWith` ↔ an oracle-level verifier, `lv42Stack` ↔ Lv42's layout
   reading (`Blocks.stackAt_getElem_of_inWindow`), `rowPosition` a bijection (tested), the tower's target
   `= Σ_i x^i Φ(s_i)` (`ring_tower`'s identity, tested: it needs the 64 leaves to be `x^i`'s coordinates and each
   stage `F_j`-linear), the setup's tables ↔ `leanIsaInstance`'s boundary (`entryColumn`, `idxColumn`), and
   `layout.rs`'s forms ↔ Lv42's flushes (tested on random rows) are the next layers' lemmas.
