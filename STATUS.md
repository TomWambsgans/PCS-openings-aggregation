# Status (branch `keccak-quotient`)

Part of this repository. Updated as work lands; the newest state is at the top of each section.

## What exists

| | Where | State |
|---|---|---|
| Keccak-256 membership circuit (χ gate on bits, 113,114 rows per Keccak-256, 3,878,612 of 2^22 rows) | `crates/quotient/src/circuit.rs` | tested against `sha3` |
| Prover / Rust verifier (2 roots + 5 field elements → 4 claims) | `crates/quotient/src/protocol.rs` | tested, incl. tampering |
| Openings with leanVM's WHIR, unchanged verifier | `crates/quotient/src/opening.rs` | tested |
| Hiding (zero-knowledge) layouts for the secret tables | `crates/quotient/HIDING.md`, `src/hiding.rs` | exact rank tests; Lean proof in progress |
| EVM verifier (generated from the Rust verifier) + mock `PCS_OPEN` precompile | `crates/evm` | parity with Rust; gas below |
| Lean: the reduction (F1) for this protocol: knowledge soundness (Q+3)/2^128, HVZK, completeness, ideal commitments, ROM | `formal/` | green, sorry-free, axioms: propext, Classical.choice, Quot.sound |

## Numbers (M4 Max, 16 cores)

- Prover: ~2.2 s for a full proof (reduction ~1.46 s, three openings ~0.76 s), peak memory 5.89 GiB (was 18.65 GiB before the memory work; +0.3 GiB for hiding).
- Verifier: reduction < 1 ms; WHIR openings 5 ms. Calldata 248 bytes. Openings 248 / 278 / 333 KiB.
- EVM: 11,944 execution gas with the three `PCS_OPEN` calls at price 0 (11,311 returning the claims); transaction without the 21,000 base: 15,900 at claim price 0, 23,900 at 2,000, 35,900 at 5,000, 95,900 at 20,000 (4 claims, 3 calls; EIP-7623 and EIP-7976 agree, execution dominates the floor).

## Reviews and their outcome

- Adversarial review: EVM contract + `PCS_OPEN` — no contract/Rust mismatch (> 6,000 random calldata, every single-bit
  flip, all lengths 0..312, 24 crafted degenerate proofs); claims are bound to the proof (captured precompile inputs
  equal the Rust openings byte for byte); gas reproduced opcode by opcode. Findings, being fixed with the EVM
  realism work: the call check fails open on any non-empty return data (medium: require success, 32 bytes, word 1);
  the only reachable rejection (a prover can make `d·d' + w_m = 0` without grinding) was untested (now tested);
  `calldata()` drops a nonzero root limb (low); success returns empty data, ETH not refused, `push2` offsets
  unchecked, the mock does not reject bad input lengths cheaply (low/info).
- Adversarial review #1 (implementation): no soundness break. ZK was broken as built (calldata-only distinguisher
  through deterministic roots; unpadded openings) → fixed by the hiding layouts (both attacks are now regression
  tests that fail). `log_rows` range: fixed (`supported`, `VerifyError::Shape`, 17..=22). Gas formulas correct.

## In progress

Adversarial reviews: Lean formal layer; prover-memory/`pcs` changes; EVM + `PCS_OPEN`; end-to-end cryptography; the hiding design. FV: WHIR soundness bridge to leanerVM `mumbai` (F2); `Statement` package with explicit extractor/simulator and an executable verifier differential-tested against Rust (F4/F5); Lean theorem for the hiding layouts (F3); the Keccak-256 chain in the random-permutation model (F4a). EVM: function selector, index root in storage, deployment cost.

## Known open items

- End-to-end Lean theorem (commitments as Merkle trees + WHIR, both transcripts, the extractor) — layers F2–F5 of `formal/README.md`.
- The hiding conditions are checked exactly at random challenges/claim points, not proven for all (F3).
