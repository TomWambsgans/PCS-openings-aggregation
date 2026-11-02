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
| Lean: WHIR openings (F2): random-oracle soundness of `opening::verify` itself (the new seed; hidden witness and quotient layouts, public wiring) at 2^17..2^22 rows: an accepted opening has a candidate of the root's Johnson list satisfying all its claims, except with (QA+10122)(2^-128 + 5(QA+10122)/2^256) ≤ 2^-63 for QA ≤ 2^64 (`ours_sound`) | `formal/WhirBridge` (built on h1 against mumbai's `lean_vm`) | sorry-free, three standard axioms, no `native_decide` (556 declarations swept); the Lean mirror equals the Rust by test (`Test/Check.lean` accepts real proofs of all three openings, rejects tampered ones), not by proof; pruned paths not formalised; two random oracles, not the RPM |
| Lean: hiding (F3): for two tables with the same claims, the **linear part** of an opening's view (lane rounds, folded table, opened rows) has the same distribution on the good challenges; unopened rows keep ≥ 2,368 / 3,840 bits; uniform padding | `formal/QuotientSecurity/Hiding/` | sorry-free; condition (R) is a hypothesis with **no bound in Lean** (holds in every test, `rounds_are_free_at_full_size`) → layout redesign in progress; not yet in the view: the roots, Merkle siblings, grinding nonces, Fiat–Shamir (the random-oracle step, F3b, in progress); not instantiated with the deployed layout |
| Lean: the end theorem for the deployed circuit (F0a, F0b): an accepted proof's cells are a computation of the deployed 2^22-row circuit whose input bits give `x` and a path with `y = H(x | 0x11..)` and the path from `H(x | 0x22..)` ending at `root`, except with (Q+3)/2^128 (`soundness_membership_deployed`); Keccak-256 checked against mumbai's spec (`keccak256_bits`) | `formal/Circuit/`, `formal/QuotientSecurity/{CircuitLayout,Pinning,Deployed}.lean` | sorry-free, three standard axioms, no `native_decide`; σ equals Rust's by a hash of both dumps, not by proof; the concrete field (x, Y and `coordWeight` as in Rust) is a hypothesis → F0c in progress |
| Lean: composition (F4, first step): the reduction with real Merkle roots, list-sound commitments, an explicit extractor (climb the witness tree, decode), ROM: ε_W + ε_σ + ε_Q + (Q+6+Q_V)(2^-128 + 4(Q+6+Q_V)/2^256) | `formal/Compose/` | sorry-free; the three opening terms are hypotheses (F2's events, other model); the decoder is a parameter; next: one model, an extractor reading only the adversary's queries, the RPM |
| Lean: the reduction's Keccak-256 chain (F4a): knowledge soundness with `transcript.rs`'s chain byte for byte, in the ROM and in leanerVM's RPM: (Q+8)(2^-163 + 3(Q+8)/2^256) + Q²/2^509 | `formal/QuotientRpm/` | sorry-free, propext, Classical.choice, Quot.sound; ideal commitments; the byte-level `Wire` (statement decoding, limbs) is a parameter, not yet tied to Rust |

## Numbers (M4 Max, 16 cores)

- Prover: ~2.2 s for a full proof (reduction ~1.46 s, three openings ~0.76 s), peak memory 5.89 GiB (was 18.65 GiB
  before the memory work; +0.3 GiB for hiding).
- Verifier: reduction < 1 ms; WHIR openings 5 ms. Calldata 252 bytes (selector + 248). Openings 248 / 278 / 333 KiB.
- EVM (2^22 rows), built up step by step, `PCS_OPEN` at price 0 (transaction gas without the 21,000 base, EIP-7623;
  EIP-7976 gives the same once execution dominates):

  | step | execution | transaction |
  |---|---|---|
  | verifier returning the claims | 11,311 | 15,267 |
  | + three `PCS_OPEN` calls, reply checked (success, 32 bytes, word 1), word 1 returned | 12,023 | 15,979 |
  | + selector, no-value check | 12,051 | 16,071 |
  | + index root from storage (cold `SLOAD` + byte reversal) | **14,289** | **18,309** |

  At a claim price c (4 claims in 3 calls): 18,309 / 26,309 / 38,309 / 98,309 for c = 0 / 2,000 / 5,000 / 20,000.
  (Transaction gas moves by 12 for each calldata byte that is zero in one proof and not in another: the report's
  proof, since the per-proof randomness, has one zero byte, the one before it two.)
  Deployment: 6,308-byte code, 1,426,798 gas.

## Reviews and their outcome

- **End-to-end cryptography**: no soundness break at our sizes: after the union bounds over WHIR's level-0 Johnson
  lists (no OOD sample at level 0), every reduction round keeps ≥ 130 bits (`review/whir_params.py`). But: claims on
  one commitment must be opened together (a split opening of the quotient table's two claims would be forgeable at
  ~2^111: the mock and the contract do it right; now documented as a requirement); with leanerVM's generic list cap
  the copy round as bounded in the paper drops to 125 bits → a tighter Lean bound is in progress; WHIR's code-side
  accounting omits a factor leanerVM proves (leanerVM's certified parameters are fine; forwarded to the F2 bridge);
  the opening seed now binds the layout and a version, in the form F2 proves. Two concrete ZK attacks on the pre-hiding code
  (solving the masks from the opened mask lane; per-coset fingerprints that deanonymize the Merkle path) → being
  re-run against the hidden layouts by the hiding reviewer. Fourteen overclaims → wording corrected (`AGENTS.md`, doc comments, `formal/README.md`).
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
- **Lean F2 and F3 (adversarial, on 25d06ea)**: axioms clean (263 + 173 declarations), vendored WHIR files
  byte-identical to leanVM `c445e3d5`, query counts / grinding / folds and the list bounds match. But:
  - F2 covers only the wiring opening: its Lean layout and weight closure are the public ones, while the witness
    and quotient openings use hidden layouts (the bridge's own `Test/Check.lean` rejects real proofs of both;
    `formal/Review/HiddenWeight.lean` shows mumbai's `verifyWhir` with the hidden closure accepts them, so the gap
    is the transcription) → being extended;
  - F3's view is the linear part only: the roots, Merkle siblings, nonces and Fiat–Shamir rest on an unformalised
    random-oracle step, and it is the interactive, per-table, honest-verifier statement → F3b started;
  - (R) has no Lean bound; the end theorem is not instantiated with the deployed layout → with the layout redesign;
  - the Lean samples uniform padding, the prover a CSPRNG (statistical ZK in the model, computational in the
    generator as deployed) → documented.
  Docs corrected (this file; `formal/README.md`).

## In progress

Rust: a hidden layout for which condition (R) holds for every challenge. (Done: per-proof randomness, OS RNG + KDF binding statement and witness; the opening seed in the form F2 proves, `opening::iv`.) FV: F0c (the concrete field), F2 for the hidden layouts and the new seed, F3b (zero knowledge of the whole non-interactive proof in the ROM/RPM, explicit simulator), F4 (composition: WHIR roots instead of ideal commitments, one knowledge-soundness theorem with an explicit extractor), the `Statement` package (computable extractor/simulator, executable verifier differential-tested against Rust).

## Known open items

- End-to-end Lean theorem (F0–F5 of `formal/README.md`).
- Condition (R) of the hiding layouts: a hypothesis in Lean, unbounded there (≈ 2^-53 estimated in `HIDING.md`, not
  proven; layout redesign in progress).
- Zero knowledge is statistical for uniform prover randomness (what the Lean samples). As deployed, the masks are
  Keccak-256 KDF outputs of a 32-byte OS seed, and the padding is ChaCha12 keyed by Keccak-256 of the KDF's padding
  seed, per table and lane: zero knowledge against adversaries that
  cannot tell that generator from uniform (as for any implementation that does not draw every bit from a physical
  source).
- `UPSTREAM.md`: issues in vendored leanVM code to report upstream (an aliasing UB, now fixed here; a planner
  divide-by-zero; documentation errors).
- Possible gas saving: absorb the index root into the transcript in the byte order `PCS_OPEN` takes, to drop the
  132-gas byte reversal.
