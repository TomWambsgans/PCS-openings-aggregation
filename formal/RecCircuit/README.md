<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# RecCircuit: π2's circuit computes π1's recorded verifier

π2 (`crates/leanvm_rec`, SPEC-REC §2.3, §2.4, §10, §12) proves that π1's recorded verifier graph accepts. Its
circuit is compiled from that graph (`crates/leanvm_rec/src/circuit/compile.rs`). This library transcribes the
compiler into Lean, checks the compiled circuit, and proves that a satisfied circuit's ports carry the graph's outputs
on the stream its witness's free bits encode.

## The end theorems (`RecCircuit/Sound.lean`)

```lean
theorem compile_sound {r : Recorded} {c : Compiled} (hc : compile r = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    ∀ J < c.circuit.ports.size, c.circuit.portLimbs w J = c.portMeaning r w J

theorem compile_sound_zero {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8} {c : Compiled}
    (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) (hz : ∀ id ∈ g.zero, id < g.nodes.size)
    (hE : ExpandFaithful g c (ofRG g rootsAt iv)) :
    ∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs w J = Compiled.limbsL (RecGraph.valE
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) (zeroOrig c (ofRG g rootsAt iv) (c.zeroIndex J)))
```

- **Hypotheses.** `compile r = .ok c` says that the transcribed compiler ran and the checker accepted its circuit.
  `hw` is π2's PIOP relation for that circuit, `RecPiop.Circuit.Satisfies` (branch `lean-rec-piop`), on a witness of
  `K` words. `compile_sound_flow` takes a fixed point of RecPiop's dataflow instead (`copy_iff_flow`).
- **`portMeaning`.** This is what port `J` carries, on `pubW w` and `streamW r w` (the public input and the stream the
  free bits encode):
  - the statement port: the public input's four big-endian words;
  - root `i`'s port: the little-endian words of the stream's bytes `at + 16, at + 24, at, at + 8`, which are
    `PCS_OPEN`'s root word's limbs;
  - element `e`'s port: the limbs of the calls' `e`-th element node's value (for a pair, its challenge);
  - the `m`-th zero port: the limbs of the `m`-th non-constant zero check's value;
  - a padding port: zero.

  All of these are values of the expanded graph (`Graph.eval`, a transcription of `eval.rs`).
- **`compile_sound_zero`** restates the zero ports against RecGraph's semantics (`RecGraph.evalNodes` over
  Keccak-f[1600], branch `lean-rec-graph`). It assumes one named obligation, **`ExpandFaithful`**: the expanded graph,
  evaluated, agrees at every node's image with RecGraph's value of the node. That covers `compile.rs`'s `expand`
  (`Expand.lean`) together with this library's `eval.rs` transcription. Neither is proved.

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
| `Sound` | the end theorems |

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
systemd-run --scope -p MemoryMax=10G lake build RecCircuit rec-circuit-diff
LEAN_CIRCUIT_OUT=out cargo test --release -p leanvm_rec --test lean_circuit -- --include-ignored --nocapture --test-threads 1
.lake/build/bin/rec-circuit-diff out/pi1_rec3.graph > pi1_rec3.lean.circuit && diff out/pi1_rec3.circuit pi1_rec3.lean.circuit
```

## Findings about `compile.rs`

Neither finding occurs in π1-rec3's graph, and the Lean compiler rejects both. The Rust would compile each of them
into an unsound circuit.

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
