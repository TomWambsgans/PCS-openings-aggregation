<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# A gas-optimised EVM verifier for leanVM 42422001 proofs

The same statement as leanVM 42422001 — same VM, the six tables and their columns, the bus, BLAKE2s by Flock,
the public input — proved by a different PIOP, designed for the EVM with the aggregated `PCS_OPEN` precompile
(`README.md` of the repository; ABI in `crates/evm/src/machine.rs`). Keccak-256 for Fiat–Shamir and the PCS
(leanVM's WHIR, unchanged). Design: [`SPEC.md`](SPEC.md) (§13: iteration 2, the final verifier); Flock's part:
[`SPEC-FLOCK.md`](SPEC-FLOCK.md); the prover: [`PROVER.md`](PROVER.md); the adversarial review of milestone 1:
[`REVIEW-M1.md`](REVIEW-M1.md).

**The PIOP.** Two proof commitments and three setup commitments. `C1` holds the tables' columns as univariate
polynomials on Cantor subspaces (novel-basis coefficients, so an evaluation at `t` is a multilinear claim) and
Flock's packed witness; after the bus challenges, `C2` holds the bus as a **grand product in a committed binary
heap** (`T(x²+x) = T(x)·T(x+1)` on Cantor cosets; logUp is unsound in characteristic 2) and one quotient per
identity. Every identity is checked at **one random point `t`**; calldata carries only the values that occur in
nonlinear terms (84 field elements); one batching sumcheck leaves **one ABI point claim per commitment** (five
`PCS_OPEN` calls). No GKR, no table sumcheck. BLAKE2s by Flock's sumcheck, with a univariate skip of 3 and the ring
switch evaluated through `K`'s subfield tower.

## Gas (measured on revm; 1,000 leanXMSS signatures, 1,023,109 cycles)

Deployed contracts (EIP-170, ≤ 24,576 bytes each), transaction gas without the 21,000 base; `FIELD_MUL` at 10 gas;
`PCS_OPEN` mocked, its claims priced at `c`. The main line's figures are also measured on the real prover's
calldata (`tests/vectors/`).

| configuration | calldata | execution (contracts) | EIP-7623, `c` = 0 / 2K / 5K / 20K | EIP-7976, `c` = 0 |
|---|---:|---:|---|---:|
| **main line** (ABI point claims, Flock in the contract) | 7,108 B | 192,392 (3) | **305,808** / 315,808 / 330,808 / 405,808 | 454,912 |
| + extension B (a bit-slice claim type in `PCS_OPEN`) | 5,716 B | 95,955 (2) | 228,010 / 228,010 / 228,010 / 307,159 | 365,824 |
| + extensions W and B (weighted claims too) | 4,828 B | 87,211 (2) | 192,580 / 192,580 / 192,580 / 264,243 | 308,992 |
| BLAKE2s left out, ABI (for scale) | 3,508 B | 70,019 (2) | 139,990 | 224,512 |
| **leanVM's verifier** (GKR + Flock), same workload | 27,068 B | 334,216 | **1,074,620** | 1,732,352 |

The main line is 3.5× cheaper than leanVM's verifier, and within 8% of its own EIP-7623 calldata
floor (283,540). **Below 100K is not reachable with BLAKE2s proved by Flock in the contract**: Flock's two sumchecks read
at least 96 scalars (≈ 92K at the floor) and the rest reads 84 values (≈ 80K). It needs BLAKE2s out of the
contract (e.g. a precompile that attests the BLAKE2s R1CS) together with weighted claims: ≈ 84K (measured at
milestone 1 for the configuration without BLAKE2s under extension W; no such precompile exists). `cargo test --release -p leanvm_univariate --test gas --
--ignored --nocapture gas_report` prints every configuration and shape.

## Prover (measured on h1, 8 cores; `RUSTFLAGS="-C target-cpu=native"`, jemalloc)

Real leanVM 42422001 traces (`src/prover/dump/apply.sh` patches leanVM to dump them). Main line, 1,000 signatures:
**6.2 s, 10.4 GB** peak, against leanVM 42422001's own prover on the same machine, 2.13 s and 10.1 GB (2.9×).
Phase table and the skip-3 Flock kernels: [`PROVER.md`](PROVER.md).

## Tests

- `contract_is_the_rust_verifier`, `deployable_is_the_rust_verifier` (`tests/gas.rs`): the contract (straight and
  linked into deployable parts by `crates/evm_link`) computes word for word what the Rust verifier computes — it is
  compiled from the Rust verifier, which is generic over the scalar.
- `tests/evm_vectors.rs`: the committed Rust→EVM vectors of real 1,000-signature proofs (`tests/vectors/`: calldata,
  each `PCS_OPEN` input, verdict, gas) replayed on both builds, plus 13–17 mutations each that must revert.
- `tests/prove_real.rs` (needs a trace; `--ignored`), `tests/prove_tiny.rs`, `tests/review_honest.rs` (an
  independent honest prover), `tests/flock_skip.rs`: the Rust verifier, the WHIR openings and both contract builds
  accept real proofs and reject mutated ones.

## Lean 4 (`formal/`; sorry-free, `propext`, `Classical.choice`, `Quot.sound` only, no `native_decide`)

- **The verifier in Lean**: `formal/UniStatement` — agrees with the Rust on every intermediate value of 150
  differential vectors (69 accepted, 81 rejected by both; real proofs among them).
- **Knowledge soundness**, `UniSound.Closed.uniKnowledgeSoundness_closed` (`formal/UniSound/UniSound/Closed.lean`):
  at the reference deployment (heights `18 18 18 18 17 18`, memory `2^21`, bytecode `2^19`) with leanVM's program
  IV, for every program, an adversary of `Q` permutation calls makes the verifier accept while the explicit
  extractor finds no witness of leanVM 42422001's relation (`Lv42.Protocol.M3Holds`, from leanerVM mumbai
  f0393df4) with probability ≤ `uniBound`, which is ≤ 2^-61 (exactly 2^-61.41) at `Q = 2^64`. In the
  random-permutation model of Keccak-f[1600]; WHIR's openings by `formal/WhirBridge` at 2^24..2^28 words.
- **Completeness**, `UniComplete.uniCompleteness_end` (`formal/UniComplete/UniComplete/End.lean`): the Lean
  honest prover's proofs are rejected with probability δ < 2^-167.
- How the proofs are built and what each layer contributes: `formal/README.md` ("The univariate verifier for
  leanVM 42422001"), `formal/UniSound/UniSound.lean`, `formal/FlockSound/FlockSoundUni.lean`,
  `formal/UniComplete/README.md`.

## Proven, tested, modelled

- **Proven** (Lean): soundness and completeness of the *Lean transcription* of the verifier (main line, reference
  shape), with `PCS_OPEN` modelled as the Statement's WHIR opening verifier, whose soundness is part of the bound
  (the five openings' terms in `uniBound`), as in the Merkle-path proof.
- **Tested, not proven**: that the Rust verifier is the Lean transcription (differential vectors); that the
  contract is the Rust verifier (parity tests; it is compiled from it); that the Rust prover is the Lean honest
  prover (byte-equal streams on the review's and `prove_tiny`'s vectors, which leave Flock out); extensions W and
  B and the other shapes (gas and tests only).
- **Modelled**: the `PCS_OPEN` price `c`, the ≈ 84K figure above, and `review/leanvm_univariate_params.py`'s
  bit counts (an analysis: ≥ 142 bits for the PIOP's rounds; the five WHIR openings at leanVM's ≈ 129-bit
  certificate each, 126.6 bits by a plain union, about 129 in the query-bounded model the Lean proofs use).
- **Restrictions**: stacks of 2^24..2^28 words (the certified WHIR lists), so 128 signatures or more (32 signatures is below); ZK
  not provided (not required).
