<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# RecGraph: π1-rec3's recorded verifier graph, its meaning, and graph = verifier

The recursion (`crates/leanvm_rec`) proves π1's verifier inside π2: π2's circuit is compiled from the **recorded
operation graph** of π1's verifier (π1-rec3: `FLOCK_REC3`, `FsShape::Rec3`, `Slices::TowerWalk`, the point-claim ABI,
the reference shape). Compiler correctness splits in two:

1. a satisfied compiled circuit's ports are the graph's evaluation on the stream its free bits encode (the circuit's
   layout is still being optimised: not here);
2. **the graph's evaluation is π1's verifier** (`UniStatement`): this library.

It is a library of `formal/EndToEnd` (`RecGraph`, `srcDir = "../RecGraph"`), as `UniStatement` is.

```sh
cd formal/EndToEnd
systemd-run --scope -q -p MemoryMax=10G lake build RecGraph          # the library and its axiom guards (Emitted: 75 s, 6.5 GB)
# the vectors (from the repository root, on h1):
UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_graph graph_lean_is_current   # rewrites Emitted.lean
REC_VECTORS_OUT=$PWD/rec_vectors.txt cargo test --release -p leanvm_rec --test lean_graph lean_vectors -- --ignored
REC_VECTORS=$PWD/rec_vectors.txt REC_REAL=$PWD/crates/leanvm_univariate/tests/vectors/main_line_rec3.txt \
  lake env lean ../RecGraph/RecGraphTest/Runner.lean                  # the differential runner (about 15 minutes)
```

## Files

- [`Node.lean`](RecGraph/Node.lean): `leanvm_flock_gas::evm::record`'s `Node` (`const`, `statement`, `input` at a byte
  offset with a length, `add`, `mul`, `seed`, `hash` of a state and a run of stream bytes, `low`, `narrow` (π1-rec2's
  160-bit challenges), `bits`, `ringWeight`), `codegen::Word` (`node`, `const`, `stream`), `Graph` (nodes, zero and
  nonzero checks, kernels, `PCS_OPEN` call words, stream length). π1-rec3's pair derivation and the BLAKE2s walk are
  additions and products: no new kinds.
- [`Emitted.lean`](RecGraph/Emitted.lean): **π1-rec3's graph**, written by `crates/leanvm_rec/src/lean.rs` (`render`;
  `tests/lean_graph.rs`'s `graph_lean_is_current` fails while it is stale, `UPDATE_LEAN=1` rewrites it): 165,829
  nodes (164,829 additions and products, 66 Keccak-256 calls), 14 zero checks, no nonzero check, 1 ring-weight kernel,
  3 `PCS_OPEN` calls of 31, 31, 28 words, a stream of 8,272 bytes. Data only: never evaluated by the kernel; it is
  read by the runner (`lake env lean`) only.
- [`Semantics.lean`](RecGraph/Semantics.lean): **`evalGraph F g iv publicInput stream`**, over a permutation `F` of the
  Keccak state in any monad (the random-permutation model's style, as `UniStatement`'s verifier is written): every
  node's value (`stepNode`, `eval.rs`'s, on `UniStatement`'s own readers: `beWordAt`, `seedWith`, `keccak256With`,
  `challengeOf`, `narrowE`, `intBits`, `Flock.towerWeightAt`), then the outputs: each call's bytes, the zeros, the
  nonzeros; none on a stream of another length. `verifierOutputsWith`: the same outputs by `UniStatement`'s verifier
  (`runWithFs`, `pcsCalls`, the zeros collected). **`GraphIsVerifier g shape roots fs walk`**: the target statement.
- [`Record.lean`](RecGraph/Record.lean): **the recorder in Lean** (`RecState`: `Sym::new`'s hash-consing by a
  `HashMap`, `Sym`'s smart constructors `constant`, `add`, `mul`, `bits`, `ringWeight` as `record.rs` has them,
  `Recorder`'s `start`, `input`, `sample` (low or narrow), `statement`), and **programs** over it (`Prog`, a free monad
  whose scalars are node indices): `Prog.record` (the graph), `Prog.run` (the program on `E`, each node evaluated as
  it is made).
- [`Commute.lean`](RecGraph/Commute.lean): **recording commutes with evaluation**, for every program.
- [`Values.lean`](RecGraph/Values.lean): **every operation's node has the operation's meaning** (`op_val`), folds, dropped zeros and ones, `x + x = 0`
  and hash-consed nodes included.
- [`Hazard.lean`](RecGraph/Hazard.lean): the merge hazard and its probability.
- [`Pi1/`](RecGraph/Pi1): π1-rec3's verifier as a program (`Ops`, `Flock`, `Verifier`: `pi1Rec3`, `pi1Graph`), and
  graph = verifier reduced to the program (`Main`).
- [`RecGraphTest/Runner.lean`](RecGraphTest/Runner.lean): the differential runner;
  [`RecGraphTest/Pi1Check.lean`](RecGraphTest/Pi1Check.lean): the program's recording is the Rust's, node for node.
- `formal/UniStatement/UniStatement/Rec.lean`: `UniStatement` extended with π1-rec, π1-rec2, π1-rec3 (`FsShape`, `walk`;
  `formal/UniStatement/README.md`, item 15).

## The theorems (proved, sorry-free, on Lean's three axioms: `RecGraph.lean`'s guards)

```lean
-- Commute.lean: for every program, pure permutation π, IV, public input and stream
theorem run_vals {α : Type} (p : Prog α) (st : RecState) (hk : KInv st) :
    (p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).2.2 =
        evalAll π iv publicInput stream (p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).2.1 ∧
      ((p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).1,
        (p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).2.1) = p.record st ∧
      KInv (p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).2.1

theorem record_eval {α : Type} (p : Prog α) (calls : List (List Word)) (len : Nat) :
    Id.run (evalNodes (m := Id) (fun s ↦ pure (π s)) ((p.record RecState.start).2.graph calls len) iv publicInput
        stream) =
      (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2

-- Values.lean: for a recorder state with the invariant RecInv, and an operation whose operands it holds (OpOK),
-- the operation's node has the operation's meaning on E (Op.value: the constant; the public word; the stream's
-- bytes at the cursor; the challenge of Keccak-256 over π of the state and the bytes read since, narrow or not;
-- the sum; the product; the bit field; ring_tower::weight_at), the smart constructors' folds, dropped zeros and
-- ones, x + x = 0 and hash-consed nodes included
theorem op_val (st : RecState) (h : RecInv st) (o : Op) (hok : OpOK st o) :
    valE (evalAll π iv publicInput stream (st.op o).2) (st.op o).1 =
      Op.value π publicInput stream st (evalAll π iv publicInput stream st) o
theorem op_inv (st : RecState) (h : RecInv st) (o : Op) (hok : OpOK st o) : RecInv (st.op o).2
theorem op_lt (st : RecState) (h : RecInv st) (o : Op) (hok : OpOK st o) : (st.op o).1 < (st.op o).2.nodes.size
theorem record_inv {α : Type} (p : Prog α) (st : RecState) (h : RecInv st) (hs : p.Scoped st) :
    RecInv (p.record st).2
theorem start_inv : RecInv RecState.start
-- and per operation: new_val, constant_val, add_val, mul_val, bits_val, input_val, statement_val, sample_val,
-- ringWeight_val, and their …_inv

-- UniStatement/Rec.lean: the shapes' parameters default to the main line
theorem reduceWithFs_main (shape : Shape) (publicWords : List E) (blake2s : Blake2s) (mode : ClaimsMode) :
    reduceWithFs F shape publicWords blake2s mode .main false = reduceWith F shape publicWords blake2s mode
theorem runFs_main (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) : runFs shape iv publicInput stream blake2s mode .main false =
      run shape iv publicInput stream blake2s mode
```

## Graph = verifier: where it stands

**Route.** `formal/Implementation`'s route (a Lean recorder over the verifier's scalar-generic functions, then
"recording commutes with evaluation") needs the verifier written over a generic scalar. `UniStatement` is written on
`E` (and 55K lines of `UniSound`, `UniComplete`, `FlockSound` unfold it), so its verifier cannot be recorded as it is.
What is here: the recorder and the generic lemma (proved), and the link checked by differential tests.

**Not true as stated.** `GraphIsVerifier Emitted.graph reference referenceRoots .rec3 true` **is false**, and so is
the brief's "for every stream and permutation": `Relations::combine` merges equal points and a point into a longer one
it is a prefix of. The verifier on `E` (the Rust's `rust_verifier` and `UniStatement`, transcribing it) compares the
points' **values**; the recorder compares its **symbols** (node indices), so the graph, the deployed contract and π2's
circuit merge by identity. On `C1`, BLAKE2S's `q_flock` slot terms are at `y(t)` (18 coordinates of `t`) and the ring
switch's term at Flock's point (26 challenges): a slot term reads as many coordinates as its point has, so when Flock's
point starts with `y(t)` the verifier reads the slot terms at 26 coordinates and the graph at 18. The runner exhibits
it: an oracle that answers Keccak-f[1600] but sets `t` and Flock's point's first 18 coordinates (`programmed`,
`gapRun`; every query distinct, so a permutation answers the same) makes the batch's terminal zero differ (the
graph's `5ce27468…`, the verifier's `b68345633…`), while setting `t` alone does not. Under a random permutation such a
coincidence has probability about `2^-192` a coordinate, so it is a soundness-irrelevant event, but the equation holds
only off it. **Decision (the coordinator's): off the event, on the proof side** (the main line's `Z_bad` / `NoMerge`), the Rust's
`combine` unchanged.

**Where the proof stands** (π1-rec3, `leanvm-rec` 4247e37):

1. **The verifier as a program, node for node** (done): `Pi1/Ops.lean`, `Pi1/Flock.lean`, `Pi1/Verifier.lean`
   transcribe `reduce` with `FLOCK_REC3` in the Rust's operation order (every `S::zero()`, `S::one()`, constant, the
   eager iterator steps, the walk, the `XOR` network, the paired batch, `weight_at`'s grouping) as a `Prog`;
   `RecGraphTest/Pi1Check.lean` (`lake env lean`) checks that its Lean recording `Pi1.pi1Graph` is `Emitted.graph`:
   the 165,829 nodes, the 14 zeros, the kernel, the 3 calls' words and the 8,272-byte stream, all equal.
2. **Graph = verifier, reduced to the program** (done): `Pi1/Main.lean`'s `evalGraph_recordedGraph` (from
   `record_eval`): the recorded graph's evaluation is the program's run on `E`; `pi1GraphIsVerifier_of_sim : Pi1Sim →
   Pi1GraphIsVerifier`, the target stated off the hazard:
   ```lean
   def Pi1GraphIsVerifier : Prop :=
     ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
       ¬ MergeHazard π iv publicInput.toList stream →
         evalGraph (m := Id) (fun s ↦ pure (π s)) (recordedGraph pi1Rec3) iv publicInput.toList stream =
           verifierOutputsWith (m := Id) (fun s ↦ pure (π s)) reference referenceRoots iv publicInput.toList stream .rec3
             true
   ```
   **`Pi1Sim`** (done, `Sim/End.lean`: `pi1Sim`, `pi1GraphIsVerifier : Pi1GraphIsVerifier`, no hypotheses, on the
   three standard axioms, `RecGraphTest/EndAxioms.lean`), the program's run on `E` (each operation worth its
   `Op.value`, `op_val`, `record_inv`) against `UniStatement`'s `runWithFs … .rec3 true`, function by function
   (`Sim/`: the judgment `Sim` and the transcript in `Chan`, `Transcript`; Flock in `Flock*`; the tables, relations,
   batch and shapes in `TablePart`, `Relations`, `Batch`, `Shape`; the lockstep `reduce_simQ` in `Compose`; the seed,
   `finish` and the calls' bytes in `Top`, `Calls`): the counts, the transcript (seed, reads, samples,
   narrow samples, the challenges list), `eqKernel` (the Rust's in-place doubling against `UniStatement`'s map),
   Flock (the zerocheck's Lagrange weights, the sumchecks, the walk `blake2sRowValues` against `Rec.lean`'s, the
   terminal, the tower target through the `XOR` network against the direct leaf sums), the digits, `Z_act`, the six
   tables' `linearise`, the constraint and heap relations, `combine` (by node against by value: off the hazard the
   value merges change no weight, `UniSound`'s `CombineEq`, `MergedSelf`, `TermWExtend`, `y_self`), `weight_at` (the
   Rust's grouping against `weightAt`: `UniSound`'s `WeightAtLinear`), the paired batch, the calls' bytes.
3. **The hazard's probability** (done, `Hazard.lean`): `MergeHazard` is `UniSound`'s `Z_bad(t) = 0` at π1-rec3's run
   (`t` its challenge 49, `p_0` = Flock's point's first coordinate, challenge 42); `hazard_card`: for every `p_0`, at
   most `2^19` values of `t`; `hazard_prob`: `≤ 2^19/|E| = 2^-173`, per candidate `C1`, `C2` (the challenges before `t`
   fixed: Flock's point is drawn before `C2`'s root, `t` after it).

## The differential tests (run on h1, `leanvm-rec` 4247e37)

25 vectors (`lean_graph.rs`'s `lean_vectors`): π1-rec3's real 1,000-signature proof (`main_line_rec3.txt`), its stream
with one byte flipped at 6 places (a row count, `C1`'s root twice, Flock's messages, the middle, the last byte), under
2 other public inputs, and 16 pseudo-random streams with random public inputs. On each, four computations agree on every
`PCS_OPEN` call's bytes, every zero check and every nonzero check: Lean's `evalGraph` of `Emitted.graph`, Rust's
`leanvm_rec::eval`, Lean's `UniStatement` at π1-rec3, and the Rust verifier at `FLOCK_REC3`. Also: Lean's IV for
π1-rec3 (`contractIvFor`) is the Rust's (`contract_iv_for`), on the real proof the Lean verifier's and the graph's three
calls are the contract's (`main_line_rec3.txt`'s `pcs_open` lines) and every zero holds, a stream one byte short or
long has no outputs by either, and the programmed oracle above shows the gap (its control agrees).

```text
π1-rec3's graph: 165829 nodes, 14 zeros, 0 nonzeros, 3 calls, a stream of 8272 bytes; 25 vectors
the contract's IV for π1-rec3 (contractIvFor): b64dacfd5e63bf47f8601ef74de51666fa02acbd959fcf6500192f96d4d7fef9, the vectors'
real: 3 calls ([992, 992, 896] bytes), 14 zeros (all hold), 0 nonzeros: the four agree
flip3: … the four agree      (and so for the 23 others)
the real proof (REC_REAL): the Lean verifier's and the graph's 3 calls are the contract's, every zero holds
a stream one byte short or long: no outputs, by the graph and by the verifier
programmed oracle, control (t = t* alone): the graph and the verifier agree
EXPECTED GAP, programmed oracle (Flock's point starting with y(t*)): graph vs verifier: zeros […, 5ce27468d8f822ac:…]
  against […, b68345633e1f0db3:…]
all 25 vectors agree
```
