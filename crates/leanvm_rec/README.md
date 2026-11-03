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
| **recursive verifier (D16v × π1-rec3)** | 980 B | 29,832 | **44,792** | 65,792 | 62,720 | 7 / 6 |
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
| prover (h1, 16 threads, `-C target-cpu=native`, jemalloc) | 5.9 s, 10.4 GB | 8.0 s + 1.3 s openings, 11.9 GB |
| soundness after the union bounds (modelled, `review/leanvm_rec_params.py`) | PIOP 129.0 bits | copy argument 152.7, `t` 140.6 |

WHIR's six openings are about 129 bits in the query-bounded model, or 126.4 by a plain union. These figures are
modelled and reviewed, not proven.

**Lean** (`formal/RecCompose`, `formal/README.md` "The recursive verifier"): π2's part of the end statement,
`RecKnowledgeSoundness2 D pi2Bound`, holds in the random-permutation model from π2's named layers, with
`pi2Bound(2^64) = 2^-64.93`, i.e. 128.93 bits. Its route is π2's PIOP (`RecPiop`), the verifier's arithmetic
(`RecStatement`), the circuit (`RecCircuit.pi1rec3_end`) and the contract's π1 openings (`callsPure`). It implies the
end-to-end statements against leanVM 42422001's relation, `RecKnowledgeSoundness` (error `ε2 + ε1 + εh`) and
`RecCompleteness`, under the Fiat–Shamir heuristic for Keccak-f[1600]: `Pi1FsKeccak`, `Pi1HazardKeccak`, justified by
π1-rec3's random-permutation theorems. All couplings are proved. Still open:
- π2's Fiat–Shamir layer;
- the tables' layer;
- the bridge from RecCircuit's end statement to `Pi1GraphAccepts`;
- `Pi1OpeningsAgree`;
- the root-word fix (`fix-pi1-root`): π2's stream carries π1's roots with each half reversed, so the contract decodes
  them to other digests than π1-rec3's.

## Tests and commands (on h1)

```sh
export RUSTFLAGS="-C target-cpu=native"
cargo test --release -p leanvm_rec                                                             # circuit, PIOP, review tests
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_gas           # gas on the real circuits
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end    # π1-rec3 proof, then π2, then the contract (12 GB)
python3 -I review/leanvm_rec_params.py                                                         # sizes, soundness, gas model
cargo test --release -p leanvm_rec --test lean_statement -- --ignored statement_data_is_current # formal/RecStatement's data
REC_STATEMENT_OUT=$PWD/v.txt cargo test --release -p leanvm_rec --test lean_statement -- --ignored lean_statement_vectors
```

`formal/RecStatement` transcribes π2's verifier in Lean (`src/lean_statement.rs` writes its data and vectors;
`pi2::verifier::reduce_traced` hands every intermediate value to the vectors).

What the tests check:
- **End to end.** π1-rec3's real proof, then π2's proof, then the contract accepts, with `PCS_OPEN` (a decoding
  mock with a registry of layout words) attesting all 7 claims. 18 flipped calldata bytes are each rejected.
- **The circuit.** Every pull equals its push on the real streams and on mutated and random ones. π1's five calls
  rebuilt from π2's ports equal the vector's.
- **The contract.** It equals the Rust verifier word for word.
