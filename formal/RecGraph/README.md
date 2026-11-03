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
- [`Values.lean`](RecGraph/Values.lean): **the smart constructors' values**, folds, dropped zeros and ones, `x + x = 0`
  and hash-consed nodes included.
- [`RecGraphTest/Runner.lean`](RecGraphTest/Runner.lean): the differential runner.
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

-- Values.lean: for a recorder state with the invariant, and operands it holds
theorem new_val (st : RecState) (h : Inv st) (n : Node) (hn : ∀ a ∈ reads st.kernels n, a < st.nodes.size) :
    (evalAll π iv publicInput stream (st.new n).2)[(st.new n).1]? =
      some (stepP π iv publicInput stream st.kernels (evalAll π iv publicInput stream st) n)
theorem constant_val (st : RecState) (h : Inv st) (x : E) :
    valE (evalAll π iv publicInput stream (st.constant x).2) (st.constant x).1 = x
theorem add_val (st : RecState) (h : Inv st) (a b : Nat) (ha : a < st.nodes.size) (hb : b < st.nodes.size) :
    valE (evalAll π iv publicInput stream (st.add a b).2) (st.add a b).1 =
      valE (evalAll π iv publicInput stream st) a + valE (evalAll π iv publicInput stream st) b
theorem mul_val (st : RecState) (h : Inv st) (a b : Nat) (ha : a < st.nodes.size) (hb : b < st.nodes.size) :
    valE (evalAll π iv publicInput stream (st.mul a b).2) (st.mul a b).1 =
      valE (evalAll π iv publicInput stream st) a * valE (evalAll π iv publicInput stream st) b
-- and new_inv, constant_inv, add_inv, mul_inv, start_inv: the invariant is kept

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
only off it. Two ways to close it:

- **state it off the bad event**: `evalGraph = verifierOutputsWith` unless two of `combine`'s points are related by
  value and not by symbol (a union bound in the random-permutation model, as the soundness proofs already take);
- **or merge by structure**: make `combine` in the Rust verifier and in `UniStatement` merge points by what they are
  (which challenges, which prefix), a function of the shape alone. Then graph = verifier holds for every stream and
  permutation.

**What is left** for a proof: write π1-rec3's verifier as a `Prog` (the Rust's operation order, so that
`Prog.record`'s graph is `Emitted.graph` node for node, checked by the runner), then prove `Prog.run` of it equal to
`UniStatement`'s `runFs … .rec3 true` off the bad event above, by `run_vals`, `record_eval` and the `…_val` lemmas
(`input`, `sample`, `bits`, `ringWeight` by `new_val`), function by function.

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
