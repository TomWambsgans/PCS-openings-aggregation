<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Recursion: a leanVM 42422001 proof verified on the EVM for 44.8K gas

A proof of a leanVM 42422001 execution, verified by recursion. The statement is leanVM 42422001's: the same VM,
tables, bus, BLAKE2s by Flock and public input.

- **π1** is the univariate PIOP of `crates/leanvm_univariate`, with its Fiat–Shamir shape `FsShape::Rec3` /
  `FLOCK_REC3`, and leanVM's WHIR.
- **π2** is a univariate SNARK, here in this crate, of π1's verifier minus its openings. Its circuit is compiled
  from π1's recorded verifier graph.
- **The contract** runs only π2's verifier, then passes π1's and π2's claims to the aggregated `PCS_OPEN`
  precompile. All claims are plain (point, value) claims, `crates/evm/src/machine.rs`'s ABI.
- **Fiat–Shamir and the PCS** use Keccak-256 and leanVM's WHIR in both layers.

Design: [`SPEC-REC.md`](SPEC-REC.md) (§12 lists every change and where it stands); π2's PIOP: [`PI2.md`](PI2.md); the
claims' points: [`SPEC-POINTS.md`](SPEC-POINTS.md); the adversarial review: [`REVIEW-REC.md`](REVIEW-REC.md) (no
attack found).

## Gas (measured on revm; 1,000 leanXMSS signatures, 1,023,109 cycles; claim price `c` = 0)

| | calldata | execution | EIP-7623 | + 21K base | EIP-7976 (64/byte) | claims / calls |
|---|---:|---:|---:|---:|---:|---:|
| **recursive verifier (D16v × π1-rec3)** | 980 B | 29,832 | **44,804** | 65,804 | 62,720 | 7 / 6 |
| `leanvm_univariate`, no recursion | 7,108 B | 192,392 | 305,808 | 326,808 | 454,912 | 5 / 5 |
| leanVM's own verifier (baseline) | 27,068 B | 334,216 | 1,074,620 | 1,095,620 | 1,732,352 | — |

- One contract of 17.6 KB.
- Calldata: the public input 32 B, π1's two roots 64 B, π1's claims 408 B (14 narrow challenges, from which the
  contract derives the 27 coordinates, plus 3 values), π2's two roots 64 B, and π2's 17 values 408 B.
- `PCS_OPEN`'s price is `c` per claim. The WHIR openings themselves go to the aggregated precompile and are not in
  these figures.

## The proof

| | π1 (inner) | π2 (outer) |
|---|---|---|
| statement | leanVM 42422001: 1,000 signatures, 1,023,109 cycles; tables of `2^17`–`2^18` rows, memory `2^21`, bytecode `2^19` | π1's verifier accepts on its public data, minus π1's openings |
| commitments | C1, C2 (`2^27`-word stacks), setup F, A0, B0 | W (`2^24`), Q (`2^27.91` words), setup (σ, κ) |
| size | Keccak-f in its verifier: 107 | `2^24` positions, 94.9% used |
| prover (h1, 16 threads, `-C target-cpu=native`, jemalloc) | 4.8 s, 10.4 GB | 3.2 s + 1.3 s openings, 9.5 GB |
| soundness after the union bounds (modelled, `review/leanvm_rec_params.py`) | PIOP 129.0 bits | copy argument 152.7, `t` 140.6 |

WHIR's six openings are about 129 bits in the query-bounded model, or 126.4 by a plain union. These figures are
modelled and reviewed, not proven.

**Lean** (`formal/RecCompose`; `formal/README.md`, section "The recursive verifier"): π2's part of the end
statement, `RecKnowledgeSoundness2 D pi2Bound`, holds in the random-permutation model, with `pi2Bound(2^64) = 2^-64.93`
(128.93 bits), on this route:
- π2's PIOP (`RecPiop`) and the tables' layer (`pi2Tables`);
- the verifier's arithmetic (`RecStatement`);
- the circuit (`RecCircuit.pi1rec3_end`, `circuitBridge`);
- the contract's π1 openings (`callsPure`).

It implies the end-to-end statements against leanVM 42422001's relation:
- `RecKnowledgeSoundness`, with error `ε2 + ε1 + εh`, and `RecCompleteness`;
- under the Fiat–Shamir heuristic for Keccak-f[1600] alone (`Pi1FsKeccak`, `Pi1HazardKeccak`), justified by π1-rec3's
  random-permutation theorems;
- graph = verifier is proved, and so are all the couplings.

Still open:
- π2's Fiat–Shamir layer (`Pi2FsLayer`).

Checked by evaluation, not by the kernel:
- the compiler accepts π1-rec3's graph;
- the Lean recording of the graph is the emitted one;
- the compiled ports' and calls' meaning, and the setup's columns at every IV.

Named, not proved:
- π2's completeness (`RecCompleteness2`), since π2's honest prover is not transcribed.

## Tests and commands (on h1)

```sh
export RUSTFLAGS="-C target-cpu=native"
cargo test --release -p leanvm_rec                                                             # circuit, PIOP, review tests
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_gas           # gas on the real circuits (see the note below)
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end    # π1-rec3 proof, then π2, then the contract (12 GB)
python3 -I review/leanvm_rec_params.py                                                         # sizes, soundness, gas model
cargo test --release -p leanvm_rec --test lean_statement -- --ignored statement_data_is_current # formal/RecStatement's data
REC_STATEMENT_OUT=$PWD/v.txt cargo test --release -p leanvm_rec --test lean_statement -- --ignored lean_statement_vectors
```

`formal/RecStatement` transcribes π2's verifier in Lean (`src/lean_statement.rs` writes its data and vectors;
`pi2::verifier::reduce_traced` hands every intermediate value to the vectors).

Note on the two gas figures: 44,804 is measured by `real_end_to_end` on the real proof's calldata (980 B, 59 zero
bytes, 56 of them the 14 narrow challenges' high bytes). `real_gas` reports 45,464 for the same configuration, on a
sample stream of 4 zero bytes: the gap, 660 = 55 × (16 − 4), is EIP-7623's price of the 55 more zero bytes, so
`real_gas` does not see the narrow challenges' zero bytes. The execution (29,832) is the same in both. (Before R1,
`REVIEW-REC.md`, the real proof had 60 zero bytes and 44,792: π1's proof was regenerated, its execution unchanged.)

What the tests check:
- **End to end.** π1-rec3's real proof, then π2's proof, then the contract accepts, with `PCS_OPEN` (a decoding
  mock with a registry of layout words) attesting all 7 claims, π1's on the roots π1's prover committed (the
  vector's `whir_root`s, not any contract's words: `REVIEW-REC.md` R1). 18 flipped calldata bytes are each rejected,
  and so are π1's openings held on other roots.
- **The circuit.** Every pull equals its push on the real streams and on mutated and random ones. π1's calls
  rebuilt from π2's ports equal the vector's, and decode to the committed roots; the word before R1 does not.
- **The contract.** It equals the Rust verifier word for word.
