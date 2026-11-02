<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The structure follows formal/Statement/README.md. -->

# UniStatement

The univariate PIOP for leanVM 42422001 (`crates/leanvm_univariate`, `SPEC.md` there; the verifier at `cee6363`,
reviewed at `b948bfc`, `REVIEW-M1.md`), in the files a reviewer reads: **its verifier as computable Lean**, module
by module as `verifier.rs`, the setup constants as data, the whole verifier with `PCS_OPEN`, the map from its
commitments to `formal/Lv42`'s stack, and **the end statements**, `UniKnowledgeSoundness` and `UniCompleteness`,
against leanVM 42422001's relation (`Lv42.Protocol.M3Holds`). Statements only: nothing is proved yet. No `sorry`,
no `native_decide`, every definition the statements rest on on Lean's three axioms (`UniStatement.lean`'s guards).

It is a library of `formal/EndToEnd` (`UniStatement`, `srcDir = "../UniStatement"`), as `Lv42` is, so it shares
that workspace's built `lean_vm` packages (leanerVM `6175f1a0`), `Lv42` and `PcsQuotient` (`formal/Statement`),
whose definitions it reuses: `K`, `E`, Keccak-256 over a permutation, the random-permutation model, the WHIR
opening (`PcsQuotient.openingWith`) and commitment (`commitWith`), the extractor's replay, Merkle inversion and
decoders.

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build UniStatement        # the library; the axiom guards
# the vectors (from the repository root): the measured shapes, and the review's honest proofs
UNI_VECTORS_OUT=uni_vectors.txt cargo test --release -p leanvm_univariate --test lean_vectors -- --ignored --nocapture
UNI_HONEST_OUT=uni_honest.txt cargo test --release -p leanvm_univariate --test review_honest -- --ignored --nocapture lean_honest_vectors
cat uni_vectors.txt uni_honest.txt > all.txt
UNI_VECTORS=../../all.txt lake env lean ../UniStatement/UniStatementTest/Runner.lean   # the runner (~6 min)
```

## Reading order

1. [`Basic.lean`](UniStatement/Basic.lean): `E::new`, `E::pow`, `eq_kernel`, `multilinear_eval`, `poly_eval`.
2. [`Transcript.lean`](UniStatement/Transcript.lean): the contract's Keccak-256 chain over calldata
   (`KeccakChannel`), over a permutation `F` in any monad; `sumcheck`; the checks collected.
3. [`Domain.lean`](UniStatement/Domain.lean): the Cantor basis, the digits, the coordinate functionals, the
   vanishing polynomials.
4. [`Tables.lean`](UniStatement/Tables.lean): the six tables, their flushes as `Form`s, their counters.
5. [`Heap.lean`](UniStatement/Heap.lean): the product heap's blocks.
6. [`Claims.lean`](UniStatement/Claims.lean): columns, relations, `combine` (the powers of `ρ`, the prefix merge).
7. [`Stacks.lean`](UniStatement/Stacks.lean): the stacks' layouts and a claim's weight at a point.
8. [`Flock.lean`](UniStatement/Flock.lean) (**swappable**): BLAKE2s by Flock (`flock_min::verify`).
9. [`Batch.lean`](UniStatement/Batch.lean) (**swappable**): the batching sumcheck to point claims.
10. [`Verifier.lean`](UniStatement/Verifier.lean): `Shape` (the setup's sizes) and `Shape.Valid`, the row counts
    (`Shape.RowsFit`), and **`reduceWith`**, `verifier.rs`'s `reduce`.
11. [`Run.lean`](UniStatement/Run.lean): the run on calldata (`runWith`, `run`), the verdict, the setup constants
    (the measured shapes, the program's IV), the row counts' bytes (`rowsBytes`).
12. [`Opening.lean`](UniStatement/Opening.lean): `PCS_OPEN` as the Statement's opening, and **`verifyWith`**,
    the whole verifier (the main line: the rows, the run, then five calls).
13. [`Mapping.lean`](UniStatement/Mapping.lean): basis `B` ↔ values, **`C1` read as Lv42's stack**, the setup's
    tables.
14. [`Security.lean`](UniStatement/Security.lean): the deployment, the setup and its IV, the extractor, the
    experiments, **`UniKnowledgeSoundness`**, **`UniCompleteness`**.

## Rust → Lean

| Rust (`crates/leanvm_univariate` at `cee6363`/`b948bfc`, `crates/leanvm_flock_gas`) | Lean (`UniStatement.`) |
|---|---|
| `transcript.rs`: `KeccakChannel::{next_scalar, next_root, sample, finish}`, `keccak_seed`, `challenge_of` | `nextScalar`, `nextRoot`, `sample`, `finish`, `seedWith`, `PcsQuotient.Transcript.challengeOf` |
| `transcript.rs`: `Checks::Collect`, `require_zero` | `Chan.zeros`, `requireZero` |
| `transcript.rs`: `sumcheck`, `sumcheck_round_poly` | `sumcheck`, `roundPoly` |
| `multilinear.rs`: `eq_kernel`, `eq_eval`, `multilinear_eval`, `poly_eval`, `log2_ceil`, `dot` | `eqKernel`, `eqEval`, `multilinearEval`, `polyEval`, `log2Ceil`, `dot` |
| `domain.rs`: `beta`, `point`, `point_e`, `digits`, `coordinate_functionals`, `coordinates_at`, `prefix_vanishing`, `suffix_vanishing`, `vanishing_ratio` | the same names in camel case |
| `layout.rs`: `Form`, `Flushes::{pair, state_derived, state_step, counted, bytecode, memory, memory_cols}`, `flushes_*`, `tables`, `count_columns`, `BLAKE2S_SLOTS`, `SEP_*` | `Form`, `Flushes.*`, `flushes*`, `tables`, `Table.countColumns`, `blake2sSlots`, `sep*` |
| `heap.rs`: `HeapLayout::new`, `Leaves`, `Block` | `HeapLayout.new`, `Leaves`, `Block` |
| `claims.rs`: `Commitment`, `Column` (and `id`), `Term`, `Relation`, `Combined`, `Relations::{push, equal, combine}` | the same; `combine` |
| `stacks.rs`: `StackLayout::{new, limbs}`, `EqCache::{row, selector}`, `limb_basis`; `verifier.rs`: `weight_at` | `StackLayout.new`, `limbs`, `rowEq`, `selector`, `limbBasis`, `weightAt` (no cache; same values) |
| `flock_min.rs`: `verify`, `zerocheck`, `row_low_weights`, `reduce_terminal`, `Variant`, `Slices`, `End`; `flock.rs`: `phi`, `fixed_challenges`, `lagrange_weights`, `ring_map`, `ring_switch_weight` | `Flock.verify`, `Flock.zerocheck`, …, `Flock.ringSwitchCoefficients` |
| `verifier.rs`: `Shape` (`table_rows`, `heights`, `heap`, `constraint_vars`), `factor_columns`, `sent_columns`, `linearise`, `tuple_degree`, `chunks`, `quotient_terms`, `table_part`, `layouts`, `batch`, `reduce`, `Reduced`, `Opening`, `Claims`, `Blake2s`, `FLOCK_*` | `Shape` (heights, `capacityRows`) and the run's `rows`, `factorColumns`, `sentColumns`, `linearise`, `tupleDegree`, `chunks`, `quotientTerms`, `tablePart`, `layouts`, `batch`, **`reduceWith`** (its steps 5 and 6 as `constraintRelation`, `heapRelations`), `Reduced`, `Opening`, `ClaimsMode`, `Blake2s`, `flock*` |
| `contract.rs`: `rust_verifier`, `NAME`; `shapes.rs`: `WORKLOADS`, `PROGRAM_IV`, `Shape::of` | `runWith`/`run`, `name`, `workloads`, `programIv`, `shapeOf`/`shapeWith` |
| `machine.rs`: `PCS_OPEN`'s ABI (mocked, `attesting_all`) | `pcsOpenWith` = `PcsQuotient.openingWith` on `plainLayout` |
| `contract.rs`: `calls` (five calls: C1, C2, setup, A0, B0) | `verifyWith` |

Deviations, none changing a value: a `List`/`Array` stands for a `Vec`, an out-of-range read gives `0` where the
Rust would panic (it never does on the tables and valid shapes); the degrees are `ℕ` where the Rust has `u64`
(the same on valid shapes, `Shape.Valid`); `EqCache` is not transcribed (`weightAt` computes the same products
directly, the twisted points once per point); `End::Ring`'s `weight` of `Slices::InContract`, which the
univariate verifier never reads, is not computed. **The shape is split** (REVIEW-M1 F1): `Shape` is the setup's
part (memory, bytecode, heights, and `capacityRows`, the rows each quotient is sized for), the row counts are
the run's argument (`Z_act`, `Z_pad` from them); at `cee6363`/`b948bfc` both are the contract's constants
(`shapeOf`: `capacityRows` = the rows), as the differential test runs them.

## The setup constants as data

* The measured shapes (`workloads`: 32 to 2,000 signatures, `reference` the 1,000), the program's IV
  (`programIv`), the transcript's name (`name`), the bytecode's `2^19` instructions.
* The layouts (`layouts shape c2Columns`: `C1`, `C2`, setup) and the heap (`Shape.heap`) are functions of the
  shape's heights, as in the Rust; the test compares their variables and, through every claim, their offsets.
* The setup's tables (`Mapping.lean`): `setupStack` (the bytecode's 16 tuple slots in basis `B`, slot `s` of
  coefficient `k` at word `s + 16 k`, and the addresses `g^i`) and `matrixStack` (Flock's `A0`, `B0`,
  `2^28` words); their roots are the WHIR commitments over `π` (`setupTreesWith`), the IV their binding with
  leanVM's program IV and the shape (`Deployment.ivWith`, REVIEW-M1 F2).

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
`UniProof` is the row counts, the stream and the five opening proofs; `UniExtractor D := Vector UInt8 32 → List
(List UInt8 × Digest) → OracleQueryLog → (proof : UniProof) → Option (D.Stack proof.rows)`; `UniProver D :=
Vector UInt8 32 → (rows : List ℕ) → D.Stack rows → OracleComp RandomPermutationOracles (Option UniProof)`;
`D.Stack rows := LeanVM.Protocol.Column (leanIsaμ D.prog (D.sizes rows))`; `D.HonestRelation` is `M3Honest`;
`D.verifierWith F roots = verifyWith F D.shape (D.ivWith F roots) roots` (the proof's rows must fit the shape,
the seed absorbs them, `rowsBytes`). The model, `QueryCostAtMost`, `permutationCallCost`, `Pr{…}[…]` are mumbai's
and `formal/Statement`'s. **The extractor** `uniExtractor` is explicit and computable: the transcript's and the
setup's Keccak-256 evaluations replayed (`PcsQuotient.Replay`), `C1`'s Merkle tree inverted under the root the
stream names (`c1Word`), the candidate stacks by the fast path, Gao's unique decoder, then the list decoder
(`fastStacks`, `uniqueStacks`, `decodeStacks` at `C1`'s `2^μ`, rate `1/2`), each read as Lv42's stack
(`lv42Stack`) at the proof's row counts, the first satisfying `M3Holds` (decidable). The bounds `ε`, `δ` are
parameters.

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
| `qflock` | `flockCol` (`QFLOCK`) | values in both, `2^(8 + τ_BLAKE2S)` |
| `table t i`, not a `BLAKE2S` limb | `⟨opIdx t, i⟩` | basis `B`, `2^τ_t` |
| `table 5 i`, `9 ≤ i < 27` (the copies) | none: Lv42 reads limb `i − 9` at `QFLOCK`'s cell `slot + 256 x` | `Q_W`: copy = slot on every row |
| `inverse t` (`z_T`) | none | `Q_W`: `z_T Π c = 1` on the active rows |
| setup `bytecodeTuple`, `address` | `Coord.known (entryColumn prog k)`, `idxColumn` (verifier-known) | the setup, honest |

The clauses: **ConstraintsVanish**: JUMP's two constraints in `Q_W`, on every row (as Lv42's); **Balanced**: the
heap (tree, root, leaves), the boundary as Lv42's (the state push `(1, 1)` and pull `(g^(2^lb−1), 1)` in the
root identity; the memory's and bytecode's push with count 1, pull with the final counts, in their leaves);
**CountsNonzero**: `z_T` in `Q_W` on the active rows; **PublicLinesHold**: the three lines in `Q_W`;
**aux**: Flock on `q_flock`. Padding rows are free on both sides (their leaves are `1`; Lv42 flushes executed
rows only).

## What is tested, what is defined

**Tested** (`UniStatementTest/Runner.lean`, run with `lake env lean`: the interpreter on the compiled
definitions' IR, not the kernel), on **101 vectors**:

* **The measured shapes** (81, `tests/lean_vectors.rs`): the 7 configurations of `tests/gas.rs` at the reference
  shape, the main line at the five other measured shapes, extension W × B at the largest; random, accepting,
  mutated, truncated, extended streams. Accepting streams are made by solving each check for the scalar read
  just before it.
* **The review's honest proofs** (20, `tests/review_honest.rs`'s `lean_honest_vectors`: its independent prover,
  real VM runs of 15 to 31 cycles over all six tables, Flock omitted, memory and bytecode of `2^4`, `2^5`,
  both claim modes; and three mutations of each point-claim proof).
* On every vector, the Lean and the Rust agree on **every value**: the result (and its error), every challenge,
  every value required zero, the verdict, the number of relations, each stack's variables, every opening handed
  to `PCS_OPEN` (point claims: point and value; weighted and bit-slice claims: points, terms in order, value,
  relations), Flock's `A0`/`B0` claims; and every shape is valid (`Shape.Valid`, the row counts fit).
* On the honest proofs with their committed stacks: the Lean verifier's point claims are **true of the
  committed `C1`, `C2` and setup stacks**; `C1` read as Lv42's columns (`lv42Column`, what `lv42Stack` stacks)
  satisfies **`ConstraintsVanish`, `Balanced`, `CountsNonzero` and `PublicLinesHold`** of Lv42's instance
  (its own flushes, constraints, counts, boundary blocks, public lines and Flock slots; `aux` is not checked:
  the prover omits Flock), with controls (another public input fails the lines, one changed `C1` coefficient
  fails the bus); `setupStack` is the honest setup (the addresses word for word, every run instruction's
  slots read back). The clauses are evaluated on the columns, not through `M3Instance.column`, which reads each
  cell of the `2^15`-word stack through the layout's lift, more than the interpreter affords.
* The Rust's unit tests of `domain.rs` and `heap.rs` on the Lean definitions, the mapping's transform pair
  (`basisValue ∘ bCoefficients = id`, and the verifier's reading at `ω_x` is the value), and **the bridge to
  Lv42's instance**: for each opcode table, on random rows, the multisets of pull and of push tuples of
  `layout.rs`'s forms are Lv42's flushes (Clean's components through `toM3`), with a control; the counter
  columns, the widths and the constraints agree.

**Results** (h1, `0c5991a`): **101/101 vectors agree on every value; 41 accepted by both, 60 rejected by both**
(accept 20/0, random 5/15, mutate 8/19, truncate 0/7, extend 0/7, honest 8/0, honest-mutate 0/12; the random
and mutated acceptances are the configurations with no check in the contract, and a mutation after the main
line's weighted-mode check); the 36 checks on the four honest proofs with stacks all hold; the 34 self-tests
(10 of the domain, heap and mapping, 24 of the bridge) all hold. About 6 minutes.

**Defined, not tested**: `PCS_OPEN`'s WHIR (the Rust has only a mock), the setup's commitments, the stacking of
`lv42Stack` into the `2^15`-word vector (Lv42's own `Blocks.stackColumn`), the extractor, the experiments, the
Props, and the provisional encodings of REVIEW-M1 F1 and F2 (`rowsBytes`, `Deployment.ivWith`).

## Open points

1. **The honest prover is not transcribed**: `UniCompleteness` takes the prover as a parameter. The review's
   prover (`tests/review_honest.rs`) is a test's, for tiny runs without Flock.
2. **`PCS_OPEN`'s WHIR instance is a choice**: the Rust mocks the precompile; the statements take the
   Statement's opening (label, version, layout identifier, rate `1/2`) on the plain layout of each stack. Its
   seed hashes the layout's identifier, which encodes the stack's size, so per-shape layouts are bound there
   (REVIEW-M1 F2's layout ids). The root word's reading (here: the two halves as `digestOfScalars`) is not
   specified by the Rust. The extensions (weighted claims, the bit-slice claim) have no opening here;
   `verifyWith` is the main line's.
3. **REVIEW-M1 F1, F2 in the Rust**: the row counts are still constants (no calldata, no seed), the setup roots
   placeholders (`setup_root(k) = [0x1111·k, 0x2222, 0x3333]`), the IV leanVM's. The statements take the rows
   from the proof, absorbed in the seed after the public input (`rowsBytes`: 8-byte big-endian words), and the
   IV `keccak(leanVM IV ‖ the three roots ‖ shape)` (`Deployment.ivWith`): **provisional encodings**, to align
   with `leanvm-univariate-iter2` when it implements them (the core, `runWith`, already takes the rows and the
   seed's extra bytes as arguments). The quotients are sized for `capacityRows` (F1: `2^(h−1) + 1`; at
   `b948bfc` the rows themselves).
4. **REVIEW-M1 F7**: the public input is read as big-endian words (the contract's); leanVM's digest is
   little-endian. One function (`publicWordsOf`, which `publicInputOf` shares) changes when the contract does.
5. **Degrees in `u64`** (REVIEW-M1 F5): the Rust panics at small heights; `Shape.Valid` (heights `0` with no row
   for XOR, MUL, SET, DEREF, else at least `2`; memory and bytecode at least `2^2`) excludes them, and on valid
   shapes the `ℕ` degrees are the Rust's.
6. **`EqCache`'s slot rows** are keyed by the slot, not the point (`base_id + 1000 + j`): correct only because
   every `q_flock` slot term is at the one point `y(t)`.
7. **Weighted mode with Flock's bit-slice end or no BLAKE2s argument** makes no check in the contract (every
   stream of the right length is accepted; `PCS_OPEN` checks all), and every check of the main line is affine
   in the scalar read just before it: sound only with the openings.
8. **The gas-iteration branch** (`leanvm-univariate-iter2`) changes the ring switch (Lever 1a: tower order;
   `Flock.lean`) and the batch's weights (Levers 1b, 1c; `Stacks.lean`'s `weightAt`, `Batch.lean`): those
   modules are the ones to swap; the vectors would be regenerated from that branch.
9. **Not proved**: the Props; the bridges `reduceWith` ↔ an oracle-level verifier, `lv42Stack` ↔ Lv42's layout
   reading (`Blocks.stackAt_getElem_of_inWindow`), the setup's tables ↔ `leanIsaInstance`'s boundary
   (`entryColumn`, `idxColumn`), and `layout.rs`'s forms ↔ Lv42's flushes (tested on random rows) are the next
   layers' lemmas.
