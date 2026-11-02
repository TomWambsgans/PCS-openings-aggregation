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
| Lean: the reduction (F1) for this protocol: knowledge soundness (Q+3)/2^128 (rounds 2^-166, 2^-164, 3/q, with margin for list unions up to 2^18), HVZK for ideal hiding commitments, completeness, ROM | `formal/` | green, sorry-free, 761 declarations on propext, Classical.choice, Quot.sound |
| Lean: WHIR openings (F2): leanerVM `mumbai`'s proven `stackedSpec` covers our opening check; ROM soundness for leanVM's transcript shape | `formal/WhirBridge` (built on h1 against mumbai's `lean_vm`) | sorry-free; our current opening seed is the gap → being changed to the proven form |
| Lean: hiding (F3): same view distribution for two tables with the same claims on the good challenges; unopened rows keep ≥ 2,368 / 3,840 bits | `formal/QuotientSecurity/Hiding/` | sorry-free; condition (R) is a hypothesis (provable only to ~2^-54 so far) → layout redesign in progress |

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

- **End-to-end cryptography**: no soundness break at our sizes: after the union bounds over WHIR's level-0 Johnson
  lists (no OOD sample at level 0), every reduction round keeps ≥ 130 bits (`review/whir_params.py`). But: claims on
  one commitment must be opened together (a split opening of the quotient table's two claims would be forgeable at
  ~2^111: the mock and the contract do it right; now documented as a requirement); with leanerVM's generic list cap
  the copy round as bounded in the paper drops to 125 bits → a tighter Lean bound is in progress; WHIR's code-side
  accounting omits a factor leanerVM proves (leanerVM's certified parameters are fine; forwarded to the F2 bridge);
  the opening seed should bind the layout and version (planned). Two concrete ZK attacks on the pre-hiding code
  (solving the masks from the opened mask lane; per-coset fingerprints that deanonymize the Merkle path) → being
  re-run against the hidden layouts by the hiding reviewer. Fourteen overclaims → wording corrected (README section
  after the design note, doc comments, `formal/README.md`).
- **Prover memory / `pcs` changes**: the claim holds (identical proofs across 674 randomized WHIR cases, 160 opening
  layouts, thread counts, x86 NTT constants; 5.58 GiB measured). Found: an aliasing pattern in the NTT encode that Miri
  flags as UB — pre-existing in leanVM, copied once more by the memory work — and an empty-claims panic → fix agent
  running (with a report for leanVM upstream).

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
- **Prover memory / `pcs` (adversarial, on 411866f)**: the lean paths make the dense prover's bytes. Differential
  tests cover commitments, re-encoded rows, lean levels, the lane-tensor prover and openings. The whole-protocol
  digests are pinned. Fixed:
  - aliasing UB in the in-place NTT encodes, leanVM's included (Miri, both borrow models; reported in
    `UPSTREAM.md`);
  - an opening of no claims panicked.

  `Table::new_in` / `hidden_in` now check, in debug builds, that the fill writes every word. Noted, not changed:
  `prove` recomputes σ's coset values for every proof.

## In progress

Rust: per-proof randomness (OS RNG + KDF binding statement and witness) and the opening seed in the form F2 proves
(fixed prefix with layout and version, root read from the proof); a hidden layout for which condition (R) holds for
every challenge. FV: F0a (end theorem for χ circuits: zero/one pinning, statement embedding), F0b (the deployed
circuit in Lean, Keccak gadget proofs), F4a (the Keccak-256 chain in the random-permutation model), the `Statement`
package (computable extractor/simulator, executable verifier differential-tested against Rust).

## Known open items

- End-to-end Lean theorem (F0–F5 of `formal/README.md`).
- Condition (R) of the hiding layouts: proven only to ~2^-54 (layout redesign in progress).
- `UPSTREAM.md`: issues in vendored leanVM code to report upstream (an aliasing UB, now fixed here; a planner
  divide-by-zero; documentation errors).
- Possible gas saving: absorb the index root into the transcript in the byte order `PCS_OPEN` takes, to drop the
  132-gas byte reversal.
