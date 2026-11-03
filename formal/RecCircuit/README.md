<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# RecCircuit: π2's circuit computes π1's recorded verifier

π2 (`crates/leanvm_rec`, SPEC-REC §2.3, §2.4, §10, §12) proves that π1's recorded verifier graph accepts. Its
circuit is compiled from that graph (`crates/leanvm_rec/src/circuit/compile.rs`). This library transcribes the
compiler into Lean, checks the compiled circuit, and proves that a satisfied circuit's ports carry the graph's outputs
on the stream its witness's free bits encode.

## The end theorem (`RecCircuit/End.lean`), no hypotheses left

```lean
theorem Compiled.compile_sound_end (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) : EndStatement g rootsAt iv c w

theorem pi1rec3_end {iv : List UInt8} {c : Compiled}
    (hc : compile (ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) = .ok c) {pub : ℕ → List F192}
    {w : ℕ → K} (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    Compiled.EndStatement RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv c w
```

- **Hypotheses.** `compile (ofRG g rootsAt iv) = .ok c` says that the transcribed compiler ran on the recorded graph
  `g` (`RecGraph.Graph`) and the checker accepted its circuit. `hw` is π2's PIOP relation for that circuit,
  `RecPiop.Circuit.Satisfies`, on a witness of `K` words.
- **`EndStatement`.** On the public input `pubW w` and the stream `streamW r w` that the witness's free bits encode,
  with `V = rgVals g iv (pubW w) (streamW r w)` (`RecGraph.evalNodes` of `g` over Keccak-f[1600]):
  - the statement port carries the public input's four words as RecGraph reads them (`beWordAt`);
  - root `i`'s port carries the big-endian words of the stream's bytes `at + 24, at + 16, at + 8, at`, which are
    `PCS_OPEN`'s root word's limbs: π1's stream carries a root as its root word, its two WHIR scalars
    (`crates/leanvm_rec/REVIEW-REC.md`, R1);
  - the `m`-th zero port carries `V`'s value of the `m`-th zero check whose image is not a constant, and every other
    zero check is 0 (`compile_sound_zero_end`, `compile_sound_zero_const`);
  - **the `PCS_OPEN` inputs π2's verifier rebuilds from the ports** (`Circuit.callInputs`, `spec.rs`'s
    `Circuit::call_inputs`) are `g`'s call words in RecGraph's semantics, call by call and word by word, as
    `PCS_OPEN` takes them (`pcsWord`): a setup root (a constant word 0, the hash as π1's contract holds it) as its root
    word (`machine::root_word`: each 16-byte half reversed). Every other word is byte for byte the same, a stream root
    (already its root word) and pairs' coordinates included (`compile_sound_callInputs`, `compile_sound_calls`).
    Before R1 a stream root's word was reversed too, which named a root other than the one π1's prover commits.
- **Element ports.** `compile_sound_element_end`: element `e`'s port carries `V`'s value of any original node the
  expansion maps to the calls' `e`-th element node.
- **π1-rec3.** `pi1rec3_end` is the end theorem at `RecGraph.Emitted.graph`. That the compiler accepts this graph is
  a run, not a proof. `rec-circuit-emitted` checks that the Rust's graph file is `RecGraph.Emitted.graph`, field by
  field. It then runs `compile` on that very term, in compiled code, and prints a circuit identical to the Rust's.

### How it is proved

- **The circuit computes its expanded graph** (`Sound.lean`). `compile_sound`: every port carries `portMeaning`, the
  values of the expanded graph under `Graph.eval`, a transcription of `eval.rs`. This goes through the layers below.
- **This library's semantics is RecGraph's** (`Agree.lean`). `agree`: on an accepted circuit, every live node of the
  expanded graph has the same value in both semantics. The proof goes node by node (`step_corr`), including the
  `UInt64` word folds (`beWordAt`/`beWord` against `beNat`).
- **The expansion keeps RecGraph's meaning** (`ExpandProof.lean`).
  - `expandSound` proves `ExpandSound`: at every original node, the expanded graph's element at the node's image is
    the original graph's.
  - `Expand.lean` replays the graph on RecGraph's recorder (`RecGraph.RecState`, the Rust's `Sym`), starting from
    `RecState.start`. The proof is an induction over the original nodes (`expandList_inv`).
  - Its invariant (`EInv`) holds four things: `RecInv`; no kernel; the seed at node 0; and each replayed node's image
    denotes the node's element (`Rel`). A state node's image also has the node's value.
  - Each node uses RecGraph's recorder lemmas: `add_val` and `mul_val` (constant folding, `x + 0`, `x · 1`, `x · 0`,
    `x + x`), plus `bits_val`, `new_val` (hash-consing) and `constant_val`.
  - The ring weight uses `WeightSim.lean` (a helper's proof). `weightSym_sim`: `weight_at` on symbols simulates it
    on `E`. `weightAt_eq_tower`: on `E` it is `Flock.towerWeightAt`.
- **The calls** (`Calls.lean`).
  - The calls check (`callsOk`) ties π2's call words to π1's.
  - `pair_val`: a pair's coordinate is `pair_point`'s, on the expanded graph's values (`y_1 = z·z + z`,
    `y_0 = z + β_1 y_1`, `β_1 = UniStatement.cantorBeta1`).
  - The byte lemmas cover the rest: a root port's limbs rebuild the root word (`root_bytes`), and an element port's
    limbs rebuild the element (`limbsE_limbsL`).

### The checks the expansion and the calls need (`Expand.lean`, `Check.lean`)

- **`Graph.typed`, on the original graph, before the expansion:**
  - node 0 is the seed, which π1's recorder makes first;
  - every node reads only earlier nodes;
  - a hash, a challenge and a narrow challenge read a state (the seed or a hash);
  - a sum, a product, a bit field and a ring weight read elements;
  - a ring weight's kernel has `2n + 6` operands, so its map has `towerStages = 6` stages;
  - the checks and the calls name nodes.

  Without the state typing, a dropped `x + 0` could hand a hash a state where the graph has an element.
- **`callsOk`:** π2's call words against π1's, word by word:
  - a constant's bytes, with word 0 the root word of the graph's constant (a setup root's hash);
  - a stream word (word 0 only) is a root port at its offset;
  - a node word (never word 0) is a live constant, an element port's node, or a pair's coordinate of an element
    port's challenge.
- **`zeroConstOk`:** a zero check folded to a constant is 0.

The Rust compiler asserts the same typing (`assert_typed` in `compile.rs`, with tests in `tests/compile_rejects.rs`).
π1-rec3's circuit and the small graphs' circuits are unchanged.

## The layers

| file | what |
|---|---|
| `Spec` | `spec.rs`: positions, regions, blocks, formulas, `σ`, `κ`, ports; `Satisfied` (pull = push, holes excluded) |
| `Graph` | the recorded graph's nodes (RecGraph's constructors) and `Graph.eval`, a transcription of `eval.rs` |
| `Layout`, `Templates`, `Expand`, `Compile` | `layout.rs`, `keccak.rs`, `keccak16.rs`, `units.rs`, `compile.rs`, as Lean code that also records traces |
| `Check` | the checker; `compile` = `compileRaw` + checks |
| `Sat` | the dataflow facts: every placement of a value carries one word (`val_holds`); a gate's value is its formula plus `κ` (`gate_val`) |
| `PolySem` | the formulas' semantics (`build_eval`: a `PolyBuilder`'s polynomial is its sum of terms, XOR cancellation in characteristic 2; `chiB_eval`) |
| `KeccakMath` | `d16_keccakF`: D16v's relations give `keccakF`; `keccak256_bits_multi`: Keccak-256 of any length is the bit-level sponge |
| `Gates` | constants; free bits (`b = b²` in the field `K`, so a bit); copies; XORs; `keccak_rel`, `keccak_out`: a checked Keccak-f instance is Keccak-f[1600] on bits |
| `Sponge` | `sponge_digest`: a checked sponge is Keccak-256 of its message, any number of blocks, `pad10*1` |
| `Pack` | `pack_val`: Horner by 15-bit windows is `Σ_e b_e x^e` |
| `Words` | packings of bits are words; bytes' bits; decoded bytes |
| `Decode` | `checked_of_compile`, `Graph.eval_step`; the free bits are the decoded stream's and public input's bits |
| `Nodes` | `node_inv`: by induction over the expanded graph, every live element node's limbs and every live hash's digest carry its value |
| `Ports` | `ports_carry` |
| `Piop` | `Circuit.toPiop`; `satisfied_of_piop`, `satisfied_of_flow`: RecPiop's relation gives `Satisfied` |
| `Sound` | `compile_sound`: the ports carry the expanded graph's values |
| `Agree` | `step_corr`, `agree`: this library's graph semantics is RecGraph's on every live expanded node |
| `SoundRG` | the ports against `RecGraph.evalNodes`, given `ExpandSound` |
| `WeightSim` | `weightAt_eq_tower`, `weightSym_sim`: the ring switch's weight on `E` and on the recorder's symbols |
| `ExpandProof` | `expandSound`: the expansion keeps RecGraph's elements, on every accepted graph |
| `Calls` | `Circuit.callInputs` (π2's rebuild of π1's `PCS_OPEN` inputs), `pair_val`, `compile_sound_calls`, `compile_sound_callInputs` |
| `End` | `EndStatement`, `compile_sound_end`; `Pi1Rec3`: `pi1rec3_end` |

### What is generic and what is instantiated

- **Generic:**
  - the dataflow lemmas;
  - the Keccak-f relations ⇒ `keccakF`;
  - the sponge for any message length;
  - packing for any bit list;
  - the `E` units;
  - the node induction;
  - the end theorems, for every graph the compiler accepts.
- **Instantiated by the checker:** a check verifies each template's geometry on the actual circuit. That covers which
  values sit at which cells, which formula sits at each producing slot, and `κ`. Each check runs in compiled code and
  the theorems use it only through its lemma. The checker accepts π1-rec3's graph and the three small test graphs.

## How the compiler is trusted

- **Transcription.** The compiler is transcribed step by step, in the Rust's order, and compared with the Rust
  (`RecCircuitTest/Main.lean`, `crates/leanvm_rec/tests/lean_circuit.rs`). The comparison covers the shape, the region
  list, the formula tables, the blocks, the ports, the calls, `κ`, and an FNV-1a hash of `σ` over all 2^24 positions.
  It runs on three small recorded graphs and on π1-rec3's graph, and every comparison is identical. On π1-rec3 the run
  takes about 90 s and 2.7 GB, checker included.
- **Checker.** The checker adds no constraint and changes no circuit: a failing check makes `compile` reject the
  graph.
- **What is proved.** The theorems are about the Lean compiler's circuits. That the Rust builds the same circuit is
  established by the comparison, not by proof.
- **Not transcribed:** the witness and the dead slots' check, which concern the honest prover only.

## Run

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build RecCircuit rec-circuit-diff rec-circuit-emitted
LEAN_CIRCUIT_OUT=out cargo test --release -p leanvm_rec --test lean_circuit -- --include-ignored --nocapture --test-threads 1
.lake/build/bin/rec-circuit-diff out/pi1_rec3.graph > pi1_rec3.lean.circuit && diff out/pi1_rec3.circuit pi1_rec3.lean.circuit
.lake/build/bin/rec-circuit-emitted out/pi1_rec3.graph > pi1_rec3.emitted.circuit && diff out/pi1_rec3.circuit pi1_rec3.emitted.circuit
```

## Findings about `compile.rs`

Neither finding occurs in π1-rec3's graph, and the Lean compiler rejects both. The Rust compiled each of them into an
unsound circuit. It now rejects them too (`compile.rs`, `tests/compile_rejects.rs`), as well as empty hashed reads.
π1-rec3's circuit and `real_gas` are unchanged.

1. **A never-hashed read shorter than 24 bytes.** `compile.rs` makes all three of its limbs free values. The graph
   gives a 16-byte read's `c2`, and an integer's `c1` and `c2`, the value 0; in the circuit they are unconstrained. A
   port fed by such a read could carry any value. π1-rec3's five never-hashed reads are 24-byte scalars.
2. **A bit field of a read wider than 8 bytes.** The circuit's field can take bits past the low limb, which
   `E::bits` would never return (the Rust's evaluation asserts an integer scalar).

The Lean compiler also asserts a few things the Rust takes for granted:

- a hashed read is not empty;
- a region registered twice agrees with itself (a `debug_assert` in the Rust);
- `regionOf` takes the first covering block, as RecPiop does, where the Rust's `row_regions` takes the last. The two
  agree on disjoint blocks, which `check_shape` requires.
