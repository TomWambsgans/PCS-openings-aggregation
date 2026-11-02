# Status

Part of this repository. Updated as work lands.

## End-to-end theorems

`formal/Statement` (`PcsQuotient`) states what is proved, in the files a reviewer reads: the relation
(Keccak-256 Merkle membership over the deployed Keccak-256), the proof format, the verifier, the honest prover,
the extractor, the simulator and the experiments, all in one random permutation. `formal/EndToEnd` proves these
statements from the layers below. Every theorem in this section is sorry-free and depends only on `propext`,
`Classical.choice` and `Quot.sound` (checked by `#guard_msgs` in each library).

**Knowledge soundness: proved, no hypotheses.**
`Soundness.knowledgeSoundness : PcsQuotient.KnowledgeSoundness Soundness.ksBound`
(`formal/EndToEnd/Soundness/Final.lean`).

- The experiment: the setup computes the circuit's commitment over π. The adversary is given its root, has coins,
  π and π⁻¹ (at most Q calls), and outputs a statement and a proof. The verifier runs over π. The bad event: the
  verifier accepts and the extractor returns no secret satisfying the relation.
- The bound: ksBound(Q) is about 2^-105 at Q = 0, 2^-86 at Q = 2^40 and 2^-62 at Q = 2^64 (just above, by a factor
  1 + 2^-43); it reaches 1 near Q = 2^125 (`formal/EndToEnd/Review/E2ESoundnessNumbers.py`, exact rationals). Its
  terms: the three WHIR openings (F2's `ours_sound`), the reduction's rounds union-bounded over the roots'
  candidate lists, and the transfer from the permutation to two random oracles.
- The extractor (`PcsQuotient.extractor`, `formal/Statement/PcsQuotient/Extractor.lean`) is an explicit,
  computable, straight-line function. It reads the statement, the proof, the adversary's transcript and the
  public setup tree; it does not query π or rerun the adversary. It replays the transcript and inverts the
  witness table's Merkle tree with hash maps (proved equal to mumbai's lists), then decodes the word in three
  stages, each only if the ones before give no witness: interpolation (about 2^31.4 operations of K), Gao's
  unique decoder (about 2^34.3 for a word with few wrong columns, at most 2^45.7 within the radius 2^18), and
  the Guruswami–Sudan list decoder beyond that radius (about 2^98 per word: infeasible). The costs are read off
  the loops (`Extractor.lean`'s table), not proved. That Gao's decoder recovers every word within its radius
  is tested, not proved; the soundness proof does not need it.
- Scope: stand-alone knowledge soundness, not simulation-extractability.

**Completeness: proved, no hypotheses.**
`E2ECompleteness.completeness_end : PcsQuotient.Completeness deltaDeployed`
(`formal/EndToEnd/Completeness/E2ECompleteness/Done.lean`).

- For every statement and secret of the relation, the Statement's honest prover with uniform coins, then the
  verifier, in one random permutation, rejects with probability at most δ.
- δ = (17·2^24 + 8)/2^192 + 2/2^256 + 3·2^-277 + (2^48)²/2^508 < 2^-162 (`deltaDeployed_lt`): degenerate
  challenges, a chain query that is not fresh, the three proofs of work, the permutation as two random oracles.

**The EVM contract is the Statement's verifier: proved, with tested links.**
`Evm.evm_accepts_iff_verifyWith`, `Evm.evm_accepts_iff_exists` (`formal/EndToEnd/Evm/`).

- The contract's recorded operation graph (F5), run on the calldata `quotient.rs` writes and the stored index
  root, accepts exactly when `PcsQuotient.verifyWith` accepts at π = Keccak-f[1600]. Over all calldata, it
  accepts exactly the calldata of a proof that `PcsQuotient.verify` accepts.
- `PCS_OPEN`'s semantics is an explicit definition (`pcsOpen`, `Evm/PcsOpen.lean`): the input read back as the
  precompile reads it, then `PcsQuotient.opening` of the layout it names.
- Tested, not proved: the bytecode computes the graph (`crates/evm` parity tests); `FIELD_MUL` and `KECCAK256`
  are the Lean operations (`mulE` is proved to be `F192`'s product); the `PCS_OPEN` mock (`machine.rs`) is the
  Rust `opening::verify`, which is `PcsQuotient.openingWith` (the Statement's differential test). The theorems
  hold for whatever index root is stored (`setIndexRoot` is owner-gated).

**Zero knowledge: in progress.**
The target is `PcsQuotient.ZeroKnowledgeWith s₀ zkSimulator rpmSimOracle ζ`, with the simulator named in the
statement (`formal/EndToEnd/ZK/With.lean`, `Simulator.lean`).

- Proved: `zeroKnowledge_deployed_final` (`ZK/Final.lean`: the fields, F1's facts, the honest tables' claims
  and the coins' bijection discharged) and `zeroKnowledge_deployed_whir` (`ZK/ProverBridge.lean`: WHIR's honest
  prover as the renderer). Two of their hypotheses are proved: the prover makes no proof with probability
  δNone < 2^-162 (`E2ECompleteness.hnone_deployed`), and it makes at most 12·(2^24 + 2^70) calls of π
  (`hprover_whir`, given the wiring rows' length).
- The bound: ζ(Q) ≈ 2^-113 for Q ≤ 2^126 (`zkBoundEnd`, `zkBoundEnd_le`). Its terms:
  - 2^-113, Fiat–Shamir freshness of the honest prover's queries (`fsFresh_setup_deployed_bits`):
    6·Q'(c + Q')/2^256 ≈ 2^-113.4 for Q' = 2^24 + 2^70 oracle operations (worst-case grinding counted) and
    c = 2^19 public rows, plus 6(c + Q')·2^-191 ≈ 2^-118.4 (the claims' windows) and c·2^-2368;
  - 2^-165 + 2^-125 + 2/2^192 (`epsHV`): the joint model's bad challenges, the degenerate scales and row, the
    degenerate masks;
  - δNone < 2^-162: the prover makes no proof;
  - 2^-2200: an unopened leaf is asked, or two collide;
  - (Qp + 2^23 + Q)²/2^508: the permutation as two random oracles (at most 2^-256).
- Remaining: `CoreWhir`, being proved (a statement about programs, no probability: at a fixed permutation, the
  Statement's prover's proof is `fmt` of the skeleton's); then one theorem with no hypothesis. The simulator is
  being made fully computable: its tables are computed by Gaussian elimination
  (`QuotientZk/Instance/Builder.lean`, run on `F192` in `Test/Builder.lean`); `sigmaAtD` (the wiring value) and
  `deployedSimV` are still `noncomputable`.

**Modelling assumptions, for all of the above.**

- Keccak-f[1600] is one random permutation, and Keccak-256 is its sponge. It serves the chain, the Merkle trees,
  the openings' duplex and the circuit's commitment. The relation is over the deployed Keccak-256.
- The prover's randomness is uniform. As deployed, the masks are Keccak-256 KDF outputs of a 32-byte OS seed and
  the padding is ChaCha12, so zero knowledge is computational in that generator.
- The Statement's definitions are the Rust by differential tests (`formal/Statement/PcsQuotientTest`), not by
  proof: reductions at 2^16..2^23 rows, whole proofs (honest and tampered) at 2^17 rows and, in the soundness
  review, at 2^22, the circuit commitments (the membership circuit's at 2^22), the prover's streams. The
  Statement's WHIR proofs carry full Merkle paths; the test expands the Rust's pruned ones.
- Trusted as in mumbai: the Lean kernel, and mumbai's definitions the Statement reuses (Keccak-256, the model,
  the WHIR verifier, its prover's pieces, the list decoder).

## The layers

| | Where | State |
|---|---|---|
| Keccak-256 membership circuit (χ gate on bits, 113,114 rows per Keccak-256, 3,878,612 of 2^22 rows) | `crates/quotient/src/circuit.rs` | tested against `sha3` |
| Prover / Rust verifier (2 roots + 5 field elements → 4 claims), sizes 2^17..2^22 rows | `crates/quotient/src/protocol.rs` | tested, incl. tampering and unsupported sizes |
| Openings with leanVM's WHIR, unchanged verifier | `crates/quotient/src/opening.rs` | tested |
| Hiding (zero-knowledge) layouts for the secret tables: every lane's first piece random, 7 random lanes, and a 9-entry gadget (lanes 31, 30 copy lanes 0, 1; the overflow lane zero) checked as one extra zero-valued claim, which makes condition (R) hold for every challenge outside a small set | `crates/quotient/HIDING.md`, `src/hiding.rs`, `src/opening.rs` | exact rank tests; costs unchanged; Lean below |
| EVM verifier (generated from the Rust verifier): selector `verify(bytes32,bytes32,bytes)` = `0xde12c640`, packed 252-byte calldata, index root in storage (owner-gated `setIndexRoot`), three fail-closed `PCS_OPEN` calls, returns the word 1 | `crates/evm` | parity with Rust, adversarial tests |
| Lean F0, the deployed circuit (F0a, F0b, F0c): an accepted proof's cells are a computation of the deployed 2^22-row circuit whose input bits give `x` and a path with `y = H(x \| 0x11..)` and the path from `H(x \| 0x22..)` ending at `root`, except with (Q+3)/2^128 (`soundness_membership_deployed`); Keccak-256 checked against mumbai's spec (`keccak256_bits`); over `primitives`' F192 (CompPoly's `BF64.Ext3`, mumbai's `E`: both moduli irreducible, `card = 2^192`), with no field hypothesis left (`soundness_membership_deployed_concrete`) | `formal/Circuit/`, `formal/QuotientSecurity/{CircuitLayout,Pinning,Deployed,DeployedConcrete}.lean`, `formal/Field/` | sorry-free, three standard axioms, no `native_decide`; σ equals the Rust's by a hash of both dumps, not by proof; the Rust's F192 arithmetic equals the Lean field's by test vectors (`Field/Test.lean`, against `crates/quotient/tests/lean_field_vectors.rs`), not by proof |
| Lean F1, the reduction: knowledge soundness (Q+3)/2^128 (rounds 2^-166, 2^-164, 3/q, with margin for list unions up to 2^18), HVZK for ideal hiding commitments, completeness, ROM | `formal/QuotientSecurity` | sorry-free, 761 declarations on propext, Classical.choice, Quot.sound |
| Lean F2, the WHIR openings: random-oracle soundness of `opening::verify` itself (the seed; the hidden witness and quotient layouts with the gadget, the public wiring layout) at 2^17..2^22 rows: an accepted opening has a candidate of the root's Johnson list satisfying all its claims, except with (QA+10122)(2^-128 + 5(QA+10122)/2^256) ≤ 2^-63 for QA ≤ 2^64 (`ours_sound`) | `formal/WhirBridge` | sorry-free, three standard axioms, no `native_decide` (589 declarations swept); mumbai's two-oracle model (the permutation: F4); the Lean mirror equals the Rust by test (`Test/Check.lean` at 2^17; the review's `F2Differential.lean` at 2^22), not by proof; pruned paths not formalised |
| Lean F3, hiding of one opening: for two tables with the same claims, the linear part of the view (lane rounds, folded table, opened rows) differs on any event by at most 1/\|E\| + (12\|E\| + 3\|K\|²)/\|E\|² < 2^-188, for the deployed witness and quotient layouts at 2^17..2^22 rows (`deployed_prEvent_le`); conditions (S) and (R) proven at every challenge outside a small set (`μ = 0`, a coordinate of `φ` in {0, 1}, two of `φ₀, φ₁, φ₂` in K; `GadgetLayout.roundsReached`); unopened rows keep ≥ 2,368 / 3,840 bits | `formal/QuotientSecurity/Hiding/` | sorry-free; uniform padding; the roots, siblings, nonces and Fiat–Shamir are F3b's |
| Lean F3b, zero knowledge of the non-interactive proof: an explicit simulator (it programs the Fiat–Shamir challenges, takes the opened rows from the simulated view and fresh digests for the unopened leaves) with advantage εFS + 2^-165 + 2^-2200 for the deployed skeleton (`zk_deployed_joint`), + Q²/2^508 in the RPM (`zk_rpm_deployed_joint'`); εFS proved (`fsFresh_deployed`: ≤ 2^-54 for a distinguisher's precomputation up to 2^127; from an empty cache with the setup, 2^-113, `fsFresh_setup_deployed_bits`); the joint model instantiated for the deployed prover (`zk_rpm_deployed_instance`) | `formal/QuotientZk/` | sorry-free, three standard axioms; `skel` equals the Rust prover by a differential test, not by proof (`QuotientZk/Test/SkelTrace.lean`, `crates/quotient/tests/skel_trace.rs`: at 2^17 every Fiat–Shamir query, tree, grind and the proof byte for byte; at 2^17..2^22 the draws, messages and trees against the derived shapes; the differences are listed in `formal/README.md`); end to end: above |
| Lean F4a, the reduction's Keccak-256 chain: knowledge soundness with `transcript.rs`'s chain byte for byte, in the ROM and in leanerVM's RPM: (Q+8)(2^-163 + 3(Q+8)/2^256) + Q²/2^509 | `formal/QuotientRpm/` | sorry-free, propext, Classical.choice, Quot.sound; ideal commitments; the `Wire` is a parameter (the Statement's chain is F4's `chainWith`: `EndToEnd/Bridge/Chain.lean`) |
| Lean F4, composition: the chain, real Merkle roots, then `opening::verify` three times; every opening term F2's `ours_sound`; the circuit's root built by a setup over the oracle; a computable extractor reading the adversary's and the setup's queries; the claim maps `reduce`'s (`knowledgeSoundness_deployed_rust`, two-oracle model, ≈ 2^-62 for Q ≤ 2^64); in the random-permutation model (`knowledgeSoundness_wired_setup_rpm_bits`; at the deployed claim maps, `Soundness.knowledgeSoundness_rust_rpm`) | `formal/Compose/`, `formal/EndToEnd/Soundness/RpmV.lean` | sorry-free, three standard axioms; decoder mumbai's Guruswami–Sudan `decodeStacks` (exact for F2's candidates) |
| Lean, the completeness layer: the honest prover's proof (reduction and three openings, gadget layouts) is accepted for any hash and randomness except on challenges of density < 2^-163 and failed grinding (≤ 2^-277 per opening in the ROM), on the deployed instance with no circuit, wiring, weight or basis hypothesis (`completeness_deployed_concrete`, `_keccak`); the honest assignment is the deployed circuit evaluated on `membership_inputs`, equal to `Circuit.outputs`; the basis is `beta()`'s 24 words (kernel-checked; `crates/quotient/tests/lean_beta_vector.rs`) | `formal/Completeness/`, `formal/QuotientSecurity/{DeployedHonest,DeployedBasis}.lean` | sorry-free, three standard axioms, no `native_decide`; the challenges in the random-oracle and permutation models: `formal/EndToEnd/Completeness` |
| Lean F5, the implementation is the model: the recorded operation graph the EVM contract is compiled from, emitted as Lean (`Graph.lean`, a test fails if stale), is proved equal to the model's verifier: it reaches the `PCS_OPEN` calls exactly when the Rust check passes, and passes exactly the model's claims (`graph_is_verifier`, `graph_words`) | `formal/Implementation/`, `crates/evm/src/lean.rs` | sorry-free; bytecode = graph by the parity tests; the graph's limb product proved equal to the concrete field's (`isF192_primitives`, so `graph_is_verifier_F192`); that the Rust computes that limb product is tested (3,000 differential vectors) |
| Lean, the bridge: the Statement's definitions are the proof layers': its circuit is F0b's (`membership_eq`, builder step by builder step), its openings F2's (`openingWith_eq_ourVerifier`), its chain F4's (`reduceWith_eq`), its claims `reduce`'s (`claimsAt_eq_reduce`), its setup the wiring stack's tree (`setupBridge`), its extractor's read-back F4's table (`readsSecret_final`) | `formal/EndToEnd/Bridge/` | sorry-free, three standard axioms; nothing of the 2^22-row circuit is evaluated |
| Lean, end to end | `formal/EndToEnd/` | above |

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

- **End-to-end knowledge soundness (adversarial; `formal/EndToEnd/Review/E2ESoundness.lean`,
  `E2ESoundnessNumbers.py`)**: the end theorem is on the three standard axioms (`#guard_msgs`), and the
  statement's definitional closure was swept for axioms, opaque, `implemented_by` and `extern` constants
  (`#review_sweep`). Checked: the two experiments share one setup and one verifier, and the deployed verifier is
  the experiment's at π = Keccak-f[1600] (`deployedVerifier_eq`); the extractor ignores the adversary's coins
  (`extractor_coins`); the honest prover, run as an adversary, is accepted at least as often as in the
  completeness experiment (`honest_accepted_ge`), so completeness makes the theorem non-vacuous
  (`nonvacuous_of_completeness`; with `completeness_end`, acceptance with probability ≥ 1 − 2^-162, an
  instantiation not compiled in one file); ksBound recomputed in exact rationals; at 2^22 rows the Lean verifier
  accepts the Rust's honest proof and rejects 14 tamperings, and the Lean commitment of the circuit is the Rust's
  (run on h1, not proved). Found, and changed:
  - the extractor was efficient only on words with no errors: its fast path fails on one wrong symbol, and it then
    ran the Guruswami–Sudan decoder (about 2^98 operations per word) → Gao's unique decoder added between the two
    (about 2^34.3 for a word with few wrong columns, at most 2^45.7 within the radius); Guruswami–Sudan only beyond
    the unique-decoding radius; the cost table in `Extractor.lean`;
  - mumbai's transcript replay is quadratic → hash maps for the replay and the Merkle inversion, proved equal to
    mumbai's lists (`Soundness/Replay.lean`);
  - the adversary was not given the setup's root → `Adversary` takes it (`Digest → OracleComp …`); the theorem
    re-proved, with the same ksBound;
  - stale lines in `formal/README.md`, `formal/Statement/README.md` and docstrings → corrected.
- **End-to-end cryptography**: no soundness break at our sizes: after the union bounds over WHIR's level-0 Johnson
  lists (no OOD sample at level 0), every reduction round keeps ≥ 130 bits (`review/whir_params.py`). But: claims on
  one commitment must be opened together (a split opening of the quotient table's two claims would be forgeable at
  ~2^111: the mock and the contract do it right; now documented as a requirement); with leanerVM's generic list cap
  the copy round as bounded in the paper drops to 125 bits → tightened in Lean (F1: the copy round
  `(4N + 8)/q`, and every round times `L²` at most 2^-128 for lists up to 2^18); WHIR's code-side
  accounting omits a factor leanerVM proves (leanerVM's certified parameters are fine; forwarded to the F2 bridge);
  the opening seed now binds the layout and a version, in the form F2 proves. Two concrete ZK attacks on the pre-hiding code
  (solving the masks from the opened mask lane; per-coset fingerprints that deanonymize the Merkle path) → fixed by
  the hiding layouts; both are regression tests (Implementation #1, below). Fourteen overclaims → wording corrected (`AGENTS.md`, doc comments, `formal/README.md`).
- **Prover memory / `pcs` changes**: the claim holds (identical proofs across 674 randomized WHIR cases, 160 opening
  layouts, thread counts, x86 NTT constants; 5.58 GiB measured). Found: an aliasing pattern in the NTT encode that Miri
  flags as UB — pre-existing in leanVM, copied once more by the memory work — and an empty-claims panic → fixed
  (the adversarial `pcs` review below; reported in `UPSTREAM.md`).

- **Lean formal layer**: the core is sound (axiom sweep, bounds recomputed by hand, an independent Rust↔Lean
  comparison of every claim coordinate). But the end theorems hold for every wiring — for a degenerate one they say
  nothing — and the circuit argument was not connected to them; the README overstated ZK and the computability of
  the extractor/simulator. → docs corrected; new layer F0 (the deployed circuit in Lean, the zero/one pinning, the
  statement embedding, a non-vacuous end theorem), now done (F0a–F0c).
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
    is the transcription) → extended: F2 now covers the hidden layouts with the gadget;
  - F3's view is the linear part only: the roots, Merkle siblings, nonces and Fiat–Shamir rest on an unformalised
    random-oracle step, and it is the interactive, per-table, honest-verifier statement → F3b (`formal/QuotientZk`),
    and zero knowledge end to end, in progress (`formal/EndToEnd/ZK`);
  - (R) has no Lean bound; the end theorem is not instantiated with the deployed layout → with the layout
    redesign: (S) and (R) proven, the end theorem instantiated (`deployed_prEvent_le`);
  - the Lean samples uniform padding, the prover a CSPRNG (statistical ZK in the model, computational in the
    generator as deployed) → documented.
  Docs corrected (this file; `formal/README.md`).

## Remaining

- Zero knowledge end to end: prove `CoreWhir`; assemble one theorem with no hypothesis; make the simulator fully
  computable (`sigmaAtD`, `deployedSimV`).
- Tested, not proved: the bytecode computes the graph; `FIELD_MUL` and `KECCAK256` are the Lean operations; the
  `PCS_OPEN` mock is `opening::verify`, and that is `PcsQuotient.openingWith`; the Statement's definitions are the
  Rust; the Rust verifier's expansion of pruned Merkle paths; the extractor's cost table and Gao's decoder.
- Not stated: simulation-extractability. `StatementBinds` (immediate) is not proved in Lean. The Statement's own
  `simulator` (`ZeroKnowledge ζ`, the field `Theorems.zeroKnowledge`) is a tested heuristic that no theorem covers.
- Outside the theorems: the `PCS_OPEN` aggregation layer must check all the claims of one call in one opening (the
  mock does); the deployed generator (ChaCha12 and the Keccak-256 KDF) must be indistinguishable from uniform.
- `UPSTREAM.md`: issues in vendored leanVM code to report upstream (an aliasing UB, now fixed here; a planner
  divide-by-zero; documentation errors).
- Possible gas saving: absorb the index root into the transcript in the byte order `PCS_OPEN` takes, to drop the
  132-gas byte reversal.

