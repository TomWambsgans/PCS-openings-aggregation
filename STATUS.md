# Status (branch `keccak-quotient`)

Part of this repository. Updated as work lands.

## What exists

| | Where | State |
|---|---|---|
| Keccak-256 membership circuit (χ gate on bits, 113,114 rows per Keccak-256, 3,878,612 of 2^22 rows) | `crates/quotient/src/circuit.rs` | tested against `sha3` |
| Prover / Rust verifier (2 roots + 5 field elements → 4 claims), sizes 2^17..2^22 rows | `crates/quotient/src/protocol.rs` | tested, incl. tampering and unsupported sizes |
| Openings with leanVM's WHIR, unchanged verifier | `crates/quotient/src/opening.rs` | tested |
| Hiding (zero-knowledge) layouts for the secret tables | `crates/quotient/HIDING.md`, `src/hiding.rs` | exact rank tests; Lean proof in progress |
| EVM verifier (generated from the Rust verifier): selector `verify(bytes32,bytes32,bytes)` = `0xde12c640`, packed 252-byte calldata, index root in storage (owner-gated `setIndexRoot`), three fail-closed `PCS_OPEN` calls, returns the word 1 | `crates/evm` | parity with Rust, adversarial tests |
| Lean: the reduction (F1) for this protocol: knowledge soundness (Q+3)/2^128, HVZK for ideal hiding commitments, completeness, ROM | `formal/` | green, sorry-free, 752 declarations on propext, Classical.choice, Quot.sound |

## Numbers (M4 Max, 16 cores)

- Prover: ~2.2 s for a full proof (reduction ~1.46 s, three openings ~0.76 s), peak memory 5.89 GiB (was 18.65 GiB
  before the memory work; +0.3 GiB for hiding).
- Verifier: reduction < 1 ms; WHIR openings 5 ms. Calldata 252 bytes (selector + 248). Openings 248 / 278 / 333 KiB.
- EVM (2^22 rows), built up step by step, `PCS_OPEN` at price 0 (transaction gas without the 21,000 base, EIP-7623;
  EIP-7976 gives the same once execution dominates):

  | step | execution | transaction |
  |---|---|---|
  | verifier returning the claims | 11,311 | 15,255 |
  | + three `PCS_OPEN` calls, reply checked (success, 32 bytes, word 1), word 1 returned | 12,023 | 15,967 |
  | + selector, no-value check | 12,051 | 16,059 |
  | + index root from storage (cold `SLOAD` + byte reversal) | **14,289** | **18,297** |

  At a claim price c (4 claims in 3 calls): 18,297 / 26,297 / 38,297 / 98,297 for c = 0 / 2,000 / 5,000 / 20,000.
  Deployment: 6,308-byte code, 1,426,798 gas.

## Reviews and their outcome

- **Lean formal layer**: the core is sound (axiom sweep, bounds recomputed by hand, an independent Rust↔Lean
  comparison of every claim coordinate). But the end theorems hold for every wiring — for a degenerate one they say
  nothing — and the circuit argument was not connected to them; the README overstated ZK and the computability of
  the extractor/simulator. → docs corrected; new layer F0 (the deployed circuit in Lean, the zero/one pinning, the
  statement embedding, a non-vacuous end theorem) in progress.
- **EVM contract + `PCS_OPEN`**: no contract/Rust mismatch (> 6,000 random calldata, all single-bit flips, all
  lengths, crafted degenerate proofs); claims bound byte for byte; gas reproduced opcode by opcode. Fixed: the call
  check failed open on any non-empty return data; the reachable degenerate rejection was untested; `calldata()`
  dropped a nonzero root limb; empty success data; ETH accepted; unchecked `push2` offsets; the mock now rejects bad
  lengths.
- **Implementation (#1)**: no soundness break. ZK was broken as built (calldata-only distinguisher; unpadded
  openings) → fixed by the hiding layouts (both attacks are regression tests that now fail). `log_rows` range:
  fixed. Gas formulas correct.

## In progress

Reviews: prover-memory/`pcs` changes; end-to-end cryptography; the hiding design. FV: F0a (end theorem for a χ
circuit), F0b (the deployed circuit in Lean, Keccak gadget proofs), F2 (WHIR soundness bridge to leanerVM `mumbai`),
F3 (hiding layouts in Lean), F4a (the Keccak-256 chain in the random-permutation model), the `Statement` package
(explicit computable extractor/simulator, executable verifier differential-tested against Rust).

## Known open items

- End-to-end Lean theorem (F0–F5 of `formal/README.md`).
- The hiding conditions are checked exactly at random challenges/claim points, not yet proven for all (F3).
- Possible gas saving: absorb the index root into the transcript in the byte order `PCS_OPEN` takes, to drop the
  132-gas byte reversal.
