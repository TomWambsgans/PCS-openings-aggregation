# Status (branch `keccak-quotient`)

Part of this repository. Updated as work lands.

## What exists

| | Where | State |
|---|---|---|
| Keccak-256 membership circuit (χ gate on bits, 113,114 rows per Keccak-256, 3,878,612 of 2^22 rows) | `crates/quotient/src/circuit.rs` | tested against `sha3` |
| Prover / Rust verifier (2 roots + 5 field elements → 4 claims), sizes 2^17..2^22 rows | `crates/quotient/src/protocol.rs` | tested, incl. tampering and unsupported sizes |
| Openings with leanVM's WHIR, unchanged verifier | `crates/quotient/src/opening.rs` | tested |
| Hiding (zero-knowledge) layouts for the secret tables: every lane's first piece random, 7 random lanes, and a 9-entry gadget (lanes 31, 30 copy lanes 0, 1; the overflow lane zero) checked as one extra zero-valued claim, which makes condition (R) hold for every challenge outside a small set | `crates/quotient/HIDING.md`, `src/hiding.rs`, `src/opening.rs` | exact rank tests; costs unchanged; Lean below |
| EVM verifier (generated from the Rust verifier): selector `verify(bytes32,bytes32,bytes)` = `0xde12c640`, packed 252-byte calldata, index root in storage (owner-gated `setIndexRoot`), three fail-closed `PCS_OPEN` calls, returns the word 1 | `crates/evm` | parity with Rust, adversarial tests |
| Lean: the reduction (F1) for this protocol: knowledge soundness (Q+3)/2^128 (rounds 2^-166, 2^-164, 3/q, with margin for list unions up to 2^18), HVZK for ideal hiding commitments, completeness, ROM | `formal/` | green, sorry-free, 761 declarations on propext, Classical.choice, Quot.sound |
| Lean: WHIR openings (F2): random-oracle soundness of `opening::verify` itself (the new seed; hidden witness and quotient layouts, public wiring) at 2^17..2^22 rows: an accepted opening has a candidate of the root's Johnson list satisfying all its claims, except with (QA+10122)(2^-128 + 5(QA+10122)/2^256) ≤ 2^-63 for QA ≤ 2^64 (`ours_sound`) | `formal/WhirBridge` (built on h1 against mumbai's `lean_vm`) | sorry-free, three standard axioms, no `native_decide` ; the Lean mirror equals the Rust by test, not by proof (`Test/Check.lean`: real witness/quotient proofs at 2^17 rows; the review's `F2Differential.lean`: the deployed wiring opening at 2^22, Rust and Lean agreeing on the honest proof and 7 tamperings); the hidden layouts are the gadget layout's (589 declarations swept); pruned paths not formalised; two random oracles, not the RPM |
| Lean: hiding (F3): for two tables with the same claims, the **linear part** of an opening's view (lane rounds, folded table, opened rows) has the same distribution on the good challenges; unopened rows keep ≥ 2,368 / 3,840 bits; uniform padding | `formal/QuotientSecurity/Hiding/` | sorry-free; condition (R) **proven for every challenge** with no coordinate in {0, 1} for the gadget layout (`GadgetLayout.roundsReached`), given the solvers' span (bound in progress) → the gadget layout's end theorem and its instantiation with the deployed layouts in progress; the roots, Merkle siblings, nonces and Fiat–Shamir: F3b (`formal/QuotientZk`, `zk_rom` proven generically; instantiation, joint simulator, RPM lift in progress) |
| Lean: the end theorem for the deployed circuit (F0a, F0b, F0c): an accepted proof's cells are a computation of the deployed 2^22-row circuit whose input bits give `x` and a path with `y = H(x | 0x11..)` and the path from `H(x | 0x22..)` ending at `root`, except with (Q+3)/2^128 (`soundness_membership_deployed`); Keccak-256 checked against mumbai's spec (`keccak256_bits`); over `primitives`' F192 (CompPoly's `BF64.Ext3`, mumbai's `E`: both moduli irreducible, `card = 2^192`), with x = `F192::new(2,0,0)`, Y = `F192::Y`, `bit_weight`, `coordinate_weight` and `statement::halves` transcribed and proved equal to the theorem's, and no field hypothesis left (`soundness_membership_deployed_concrete`) | `formal/Circuit/`, `formal/QuotientSecurity/{CircuitLayout,Pinning,Deployed,DeployedConcrete}.lean`, `formal/Field/` | sorry-free, three standard axioms, no `native_decide`; σ equals Rust's by a hash of both dumps, not by proof; the Rust's F192 arithmetic equals the Lean field's by test vectors (`Field/Test.lean`, kernel-checked products, against `crates/quotient/tests/lean_field_vectors.rs`), not by proof |
| Lean: composition (F4): knowledge soundness of the deployed verifier (the chain, then `opening::verify` three times) with real Merkle roots, the circuit's root built by a setup with the oracle, every opening term from F2's `ours_sound`, and a computable extractor reading only the adversary's queries (decoder: mumbai's Guruswami–Sudan `decodeStacks`, exact for F2's candidates): ≈ 2^-62 for Q ≤ 2^64 (`knowledgeSoundness_wired_setup_bits`), mumbai's two-oracle model | `formal/Compose/` | sorry-free, three standard axioms; left: the three claim maps (the Rust verifier's opening claims read as F1's claims, in progress), the RPM version (in progress) |
| Lean: completeness: the honest prover's proof (reduction + three openings, gadget layouts) is accepted for any hash and randomness except on challenges of density < 2^-163 (and grinding failure ≤ 2^-277 per opening in the ROM), on the deployed instance with no circuit, wiring, weight or basis hypothesis (`completeness_deployed_concrete`, `_keccak`): the honest assignment is the deployed circuit evaluated on `membership_inputs` and equals `Circuit.outputs` (which therefore satisfies every gate), its public bits are the statement's (F0b's `membership_public`), the deployed σ keeps each cell's source, the basis is `beta()`'s 24 words (kernel-checked Cantor basis, determined by the low-bit rule; `crates/quotient/tests/lean_beta_vector.rs`) | `formal/Completeness/`, `formal/QuotientSecurity/{DeployedHonest,DeployedBasis}.lean` | sorry-free, three standard axioms (`#guard_msgs` in `Completeness.lean`), no `native_decide`; challenges uniform by assumption (no ROM theorem for the chain's honest queries) |
| Lean: the implementation is the model (F5): the recorded operation graph the EVM contract is compiled from, emitted as Lean (`Graph.lean`, a test fails if stale), is proved equal to the model's verifier: it reaches the `PCS_OPEN` calls exactly when the Rust check passes, and passes exactly the model's claims (`graph_is_verifier`, `graph_words`) | `formal/Implementation/`, `crates/evm/src/lean.rs` | sorry-free; bytecode = graph by the parity tests; the graph's field product = the concrete field's by 3,000 differential vectors (proof in progress) |
| Lean: zero knowledge of the non-interactive proof (F3b + joint), random-oracle model: an explicit computable simulator (programs the Fiat–Shamir challenges, the opened leaves from the simulated view, fresh hashes for unopened leaves; cost the honest prover's oracle calls) with advantage εFS + 2^-165 + 2^-2200 for the deployed skeleton (`zk_deployed_joint`); per opening, the gadget layout's hiding theorem with (Q), WeightsFit and the layout facts proven for the deployed witness/quotient layouts at 17..22 | `formal/QuotientZk/`, `formal/QuotientSecurity/Hiding/` | sorry-free, three standard axioms; open: εFS (Fiat–Shamir freshness, in progress), the link between the Lean skeleton and the Rust prover (trace test in progress), a builder of tables with given claims for the simulator, the RPM version (in progress); prover randomness uniform (deployed: computational in ChaCha12) |
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

- leanVM's own PIOP verifier (commit 42422001: Flock + BLAKE2s), Keccak transcript, claims to `PCS_OPEN`, measured
  the same way (`crates/leanvm_flock_gas`): for leanVM's benchmark (1,290 leanXMSS signatures) 335,627 execution,
  27,140 calldata bytes, 1,077,470 transaction gas (EIP-7623, without the base; calldata binds), 4 claims in 4 calls;
  the Keccak-GKR version (4af2cddd) about 4.8 M (modelled from measured parts). The straight-line code is 117 KB, over
  the contract size limit (loops or several contracts needed, not measured).

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

Rust: done (the gadget layout; per-proof randomness, OS RNG + KDF binding statement and witness; the opening seed in the form F2 proves, `opening::iv`.) FV: F2 for the hidden layouts and the new seed, F3b (zero knowledge of the whole non-interactive proof in the ROM/RPM, explicit simulator), F4 (composition: WHIR roots instead of ideal commitments, one knowledge-soundness theorem with an explicit extractor), the `Statement` package (computable extractor/simulator, executable verifier differential-tested against Rust).

## Known open items

- End-to-end Lean theorem (F0–F5 of `formal/README.md`).
- Condition (R): proven in Lean for the gadget layout given the solvers' span; that span's failure bound and the
  end theorem for the deployed layouts are in progress.
- Zero knowledge is statistical for uniform prover randomness (what the Lean samples). As deployed, the masks are
  Keccak-256 KDF outputs of a 32-byte OS seed, and the padding is ChaCha12 keyed by Keccak-256 of the KDF's padding
  seed, per table and lane: zero knowledge against adversaries that
  cannot tell that generator from uniform (as for any implementation that does not draw every bit from a physical
  source).
- `UPSTREAM.md`: issues in vendored leanVM code to report upstream (an aliasing UB, now fixed here; a planner
  divide-by-zero; documentation errors).
- Possible gas saving: absorb the index root into the transcript in the byte order `PCS_OPEN` takes, to drop the
  132-gas byte reversal.
