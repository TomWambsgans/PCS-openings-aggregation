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
- Not vacuous: the honest prover, run as an adversary, is accepted with probability at least 1 − δ
  (`honest_accepted_in_soundness`, `formal/EndToEnd/Review/E2ECompletenessReview.lean`).
- Scope: stand-alone knowledge soundness, not simulation-extractability.

**Completeness: proved, no hypotheses.**
`E2ECompleteness.completeness_end : PcsQuotient.Completeness deltaDeployed`
(`formal/EndToEnd/Completeness/E2ECompleteness/Done.lean`).

- For every statement and secret of the relation, the Statement's honest prover with uniform coins, then the
  verifier, in one random permutation, rejects with probability at most δ.
- δ = (17·2^24 + 8)/2^192 + 2/2^256 + 3·2^-277 + (2^48)²/2^508 ≈ 2^-163.91 (`deltaDeployed_lt`: below 2^-162).
  The terms: degenerate challenges (2^-163.91); a chain query that is not fresh (2^-255); the proofs of work
  (3·2^-277 ≈ 2^-275.4; the proof bounds the whole run's grinding failure by 2^-304, `grinding_le` in
  `Grinding.lean`); the permutation as two random oracles (2^-412, for at most 2^48 block calls; the run makes
  exactly 114,098,677,826,653 < 2^47, `hcost_exact`).
- The coins do not matter: the same δ holds for every fixed value of the masks and the paddings
  (`completeness_every_coins`, `formal/EndToEnd/Review/E2ECompletenessReview.lean`). So completeness does not
  depend on the uniform-coins model, only on the coins being independent of π.
- The prover is the Statement's. A differential test finds it equal to the Rust prover's reduction stream (nine
  scalars) at 2^17 rows, on a small circuit; it does not compare the openings, and was not run at 2^22. The
  deployed Rust prover is therefore trusted for completeness.

**Zero knowledge: proved, no hypotheses.**
`PcsQuotient.EndToEnd.zeroKnowledge_closed : PcsQuotient.ZeroKnowledgeWith s₀ (zkSimulator …) rpmSimOracle
(zkBoundEnd ((2^24 + 2^70)·12) fmtBudget (· ↦ deltaNone))` (`formal/EndToEnd/ZK/CoreMain.lean`).

- For every statement and secret of the relation and every distinguisher of at most Q calls of π and π⁻¹, fixed
  after them (non-adaptive), its verdicts on the honest proof and on the simulator's proof (the simulator
  answering its queries, the permutation programmable) differ in probability by at most ζ(Q).
- The simulator is explicit and named in the statement (`zkSimulator`, `rpmSimOracle`:
  `formal/EndToEnd/ZK/With.lean`, `Simulator.lean`). It reads no witness. It draws the Fiat–Shamir challenges
  first and programs them, takes the messages and opened rows from the joint honest-verifier simulator (WHIR's
  honest prover on tables built from uniform values), and answers unopened leaves with fresh digests. Its
  computable form is in progress (its tables are computed by Gaussian elimination,
  `QuotientZk/Instance/Builder.lean`).
- Scope: single-proof zero knowledge. `realExperiment` starts from an empty permutation, the prover goes first,
  and the distinguisher queries π and π⁻¹ only after it has the proof. Not covered: oracle queries before the
  proof (a distinguisher's precomputation, or auxiliary input that depends on π), and several proofs under one
  π. So Fiat–Shamir freshness is taken from an empty cache (`c₀ = []`), and `FSFresh`'s inherent |c₀|·2^-191
  term (a distinguisher that guessed a challenge before the proof) is identically 0 here; a pre-proof phase is
  planned, which will make it nonzero.
- The proof goes through the non-degenerate chain (`QuotientZk/Instance/Nondeg.lean`: `jointHVZKε_of_linkV`,
  `prob_not_goodT_bits`, `prob_not_claimsND_le`; `zk_rpm_skel_approx`), which asks the honest tables' claims only
  off the degenerate challenges and masks (`ClaimsND`). The earlier joint-model theorems that ask them at every
  mask (`zk_rpm_deployed_instance`, `zk_rpm_deployed_jointV_fs'`, `jointHVZK_of_linkV`, `joint_hzkV`,
  `zk_deployed_joint(_fs)`, `zk_rpm_deployed_joint(_fs)(')`, `joint_hzk`, `jointHVZK_of_link`) are kept but
  superseded: the honest tables do not meet their hypotheses (`EndToEnd/Review/E2EZkNondeg.lean`: where the
  witness claim's scale vanishes, the verifier's value is 0).
- The bound: ζ(Q) ≈ 2^-113 for Q ≤ 2^126 (`zkBoundEnd`, `zkBoundEnd_le`). Its terms:
  - 2^-113, Fiat–Shamir freshness of the honest prover's queries (`fsFresh_setup_deployed_bits`):
    6·Q'(c + Q')/2^256 ≈ 2^-113.4 for Q' = 2^24 + 2^70 oracle operations (worst-case grinding counted) and
    c = 2^19 public rows, plus 6(c + Q')·2^-191 ≈ 2^-118.4 (the claims' windows) and c·2^-2368;
  - 2^-165 + 2^-125 + 2/2^192 (`epsHV`): the joint model's bad challenges, the degenerate scales and row, the
    degenerate masks;
  - deltaNone < 2^-162: the prover makes no proof, or meets degenerate α, β (`hbad_deployed`);
  - 2^-2200: an unopened leaf is asked, or two collide;
  - (Qp + 2^23 + Q)²/2^508, Qp = 12·(2^24 + 2^70) the prover's calls of π (`hprover_whir`): the permutation as
    two random oracles (at most 2^-256).
- Two statement changes on the way. The deterministic core (`CoreWhir`: at a fixed permutation, `fmt` of the
  skeleton's proof is the Statement's prover's proof) is false at degenerate α, β, where the Statement's coset
  division is not F1's quotient; it is now stated off them (`CoreWhirG`, proved as `coreD`), and the degenerate
  α, β are charged to deltaNone. `fmt`'s `fillRun` now ends at the program's `fail` as at its `ret`, as mumbai's
  `runFrom` does.

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
- Scope: the three theorems above are about `verifyWith` in the random-permutation model; this one holds at the
  real Keccak-f[1600]. They do not formally compose: a probability over a random permutation does not transfer
  to a fixed hash.

**Modelling assumptions, for all of the above.**

- Keccak-f[1600] is one random permutation, and Keccak-256 is its sponge. It serves the chain, the Merkle trees,
  the openings' duplex and the circuit's commitment. The relation is over the deployed Keccak-256.
- The prover's randomness is uniform in the model. As deployed (`Randomness::derive`, `protocol.rs`), a 32-byte
  seed comes from the OS; a key is Keccak-256 of a tag, the seed, the transcript's label (the circuit's
  commitment and the statement) and a digest of the witness's cells; the masks are the words of Keccak-256(tag ‖
  key ‖ k) for k = 0, 1, 2; the padding seed is Keccak-256(tag ‖ key), each table's seed Keccak-256 of a label,
  the table's name and it (`table_seed`), and each lane's padding is ChaCha12 keyed by Keccak-256(table seed ‖
  lane) (`opening.rs`). Deployed zero knowledge is therefore computational in that generator. Completeness holds
  for every fixed coins (above); soundness does not involve the prover.
- The Statement's definitions are the Rust by differential tests (`formal/Statement/PcsQuotientTest`), not by
  proof: reductions at 2^16..2^23 rows, whole proofs (honest and tampered) verified at 2^17 rows and, in the
  soundness review, at 2^22, the circuit commitments (the membership circuit's at 2^22), and the prover's
  reduction stream at 2^17 (above). The Statement's WHIR proofs carry full Merkle paths; the test expands the
  Rust's pruned ones. For zero knowledge, the Lean skeleton (which `coreD` relates to the Statement's prover)
  makes the Rust prover's queries and proof byte for byte at 2^17 rows (`crates/quotient/tests/skel_trace.rs`).
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
| Lean F3b, zero knowledge of the non-interactive proof: an explicit simulator (it programs the Fiat–Shamir challenges, takes the opened rows from the simulated view and fresh digests for the unopened leaves) with advantage εFS + εhv + 2^-2200 for the deployed skeleton (`zk_deployed_bits`), + Q²/2^508 in the RPM; εFS proved (`fsFresh_deployed`: ≤ 2^-54 for a distinguisher's precomputation up to 2^127; from an empty cache with the setup, 2^-113, `fsFresh_setup_deployed_bits`); the joint model for the deployed prover with the honest tables' claims off the degenerate challenges and masks (`Instance/Nondeg.lean`: `jointHVZKε_of_linkV`, εhv = 2^-165 + 2^-125 and the view within εz = 2/2^192, together epsHV; `zk_rpm_skel_approx`), which `zeroKnowledge_closed` uses. Superseded (kept; their all-masks `hT₁`/`hT₂`, `hTW`/`hTQ` are not met by the honest tables): `zk_deployed_joint(_fs)`, `zk_rpm_deployed_joint(_fs)(')`, `zk_rpm_deployed_jointV_fs'`, `zk_rpm_deployed_instance` | `formal/QuotientZk/` | sorry-free, three standard axioms; `skel` equals the Rust prover by a differential test, not by proof (`QuotientZk/Test/SkelTrace.lean`, `crates/quotient/tests/skel_trace.rs`: at 2^17 every Fiat–Shamir query, tree, grind and the proof byte for byte; at 2^17..2^22 the draws, messages and trees against the derived shapes; the differences are listed in `formal/README.md`); end to end: above |
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

- **End-to-end zero knowledge (adversarial; `formal/EndToEnd/Review/E2EZk{Axioms,Closed,Nondeg}.lean`)**: the
  end theorem `zeroKnowledge_closed` is on the three standard axioms, and every theorem of this repository's
  modules in the `ZK` library's closure was swept (10,616 theorems, none on another axiom); it rests on the
  non-degenerate chain (`jointHVZKε_of_linkV`, `prob_not_claimsND_le`, `prob_not_goodT_bits`), not on the
  all-masks theorems; the simulator's arguments hold no witness. Found, and changed in the docs:
  - the all-masks joint-model theorems (`zk_rpm_deployed_instance`, `zk_rpm_deployed_jointV_fs'`,
    `jointHVZK_of_linkV`, `joint_hzkV`, `zk_deployed_joint(_fs)`, `zk_rpm_deployed_joint(_fs)(')`, `joint_hzk`,
    `jointHVZK_of_link`) were presented as the deployed result, but the honest tables do not meet their
    `hTW`/`hTQ` (`hT₁`/`hT₂`) at degenerate challenges and masks (`valsW c v = 0` where
    `claimScale 2 23 t = 0`, `E2EZkNondeg.lean`) → kept, marked superseded (their docstrings, `formal/README.md`,
    `Instance/Main.lean`'s header, `ZK/Assembly.lean`, the F3b row here);
  - the scope was undocumented → single-proof zero knowledge stated (`Security.lean`'s `ZeroKnowledgeWith`,
    the Statement README, `formal/README.md`, above), and `FSFresh`'s inherent |c₀|·2^-191 term noted as 0 in the
    end theorem (`c₀ = []`);
  - slack in ζ (the skeleton's grinding fuel; Pr[row ∈ K]) → under "Remaining", as possible improvements;
  - stale lines (`coreClose_of_joint`'s lemmas under old names; `ProverBridge.lean`'s bound without
    2^-125 + 2/2^192; `Nondeg.lean`'s (2^26 + 4|K|)/|E| for the proved (26·2^25 + 4|K|)/|E|, and "every good
    challenge"; `Deployed/Main.lean`'s "`FSFresh` not proved here"; `HIDING.md`'s open items) → corrected;
  - the simulator was called compiled/computable → "an explicit simulator; its computable form is in progress".
- **End-to-end completeness (adversarial; `formal/EndToEnd/Review/E2ECompletenessReview.lean`)**: the end
  theorem is on the three standard axioms, and the statement's closure was swept (`#review_sweep`). Proved there:
  `Relation` is satisfiable (`relation_self`), and an explicit secret's statement is accepted with probability at
  least 1 − δ (`w₀_accepted`); the same δ for every fixed coins (`completeness_every_coins`); the exact block
  count (`hcost_exact`: 114,098,677,826,653 < 2^47); knowledge soundness is not vacuous: the honest prover, run as
  an adversary in the knowledge-soundness experiment (same setup, same verifier), is accepted with probability at
  least 1 − δ (`honest_accepted_in_soundness`). Found, and changed in the docs:
  - the Statement's prover was said to output the Rust prover's stream, but the differential test compares only
    the reduction's nine scalars, at 2^17 rows on a small circuit → stated so; the deployed Rust prover is
    trusted for completeness;
  - the three theorems are about `verifyWith` in the random-permutation model and do not formally compose with
    the EVM theorem at the real Keccak-f[1600] → stated;
  - the deployed key derivation, and that completeness holds for every coins → documented;
  - the proofs-of-work term: the end-to-end proof bounds the whole run's grinding failure by 2^-304
    (`grinding_le`), not by `ours_romComplete`'s per-opening bound → stated;
  - stale lines (the completeness hypotheses "left", `E2ECompleteness.lean`'s module doc, "bounds not yet
    known" in the Statement README and `Security.lean`, "non-vacuity not proved" in `E2ESoundness.lean`,
    "challenges uniform by assumption" here) → corrected.
- **End-to-end knowledge soundness (adversarial; `formal/EndToEnd/Review/E2ESoundness.lean`,
  `E2ESoundnessNumbers.py`)**: the end theorem is on the three standard axioms (`#guard_msgs`), and the
  statement's definitional closure was swept for axioms, opaque, `implemented_by` and `extern` constants
  (`#review_sweep`). Checked: the two experiments share one setup and one verifier, and the deployed verifier is
  the experiment's at π = Keccak-f[1600] (`deployedVerifier_eq`); the extractor ignores the adversary's coins
  (`extractor_coins`); the honest prover, run as an adversary, is accepted at least as often as in the
  completeness experiment (`honest_accepted_ge`), so completeness makes the theorem non-vacuous
  (`nonvacuous_of_completeness`; with `completeness_end`, acceptance with probability ≥ 1 − 2^-162, since
  compiled as `honest_accepted_in_soundness` in the completeness review); ksBound recomputed in exact
  rationals; at 2^22 rows the Lean verifier accepts the Rust's honest proof and rejects 14 tamperings, and the
  Lean commitment of the circuit is the Rust's (run on h1, not proved). Found, and changed:
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
    and zero knowledge end to end (`formal/EndToEnd/ZK`, `zeroKnowledge_closed`);
  - (R) has no Lean bound; the end theorem is not instantiated with the deployed layout → with the layout
    redesign: (S) and (R) proven, the end theorem instantiated (`deployed_prEvent_le`);
  - the Lean samples uniform padding, the prover a CSPRNG (statistical ZK in the model, computational in the
    generator as deployed) → documented.
  Docs corrected (this file; `formal/README.md`).

## Remaining

- The zero-knowledge simulator's computable form (in progress; its tables are computed, `sigmaAtD` and
  `deployedSimV` are still `noncomputable`).
- Zero knowledge is single-proof: no distinguisher query before the proof, no second proof under the same π.
  A pre-proof phase (the distinguisher's queries before the proof) is planned; it will make `FSFresh`'s
  |c₀|·2^-191 term nonzero (`QuotientZk/Deployed/Fresh.lean`; 0 in the end theorem today, `c₀ = []`).
- Possible improvements to ζ (slack, documented only):
  - ζ's dominant 2^-113 (Fiat–Shamir freshness) comes from the skeleton's grinding fuel, 2^64 nonces a grind
    (`QuotientZk/Deployed/Skeleton.lean`'s `queryPhase`, `qpBound` in `Deployed/Bound.lean`: 2^70 operations),
    while the Statement's prover tries 2^25 (`nonceFuel`). At that fuel εFS ≤ 2^-157
    (`E2EZkNondeg.lean`: `epsFS (2^19) (2^24 + 2^31) 2^-191 2^-2368 ≤ 2^-157`), and ζ would be about 2^-125;
  - the 2^-125 term of epsHV is almost entirely Pr[row ∈ K] (the 4|K|/|E| = 2^-126 of `card_not_TND_le`'s
    26·2^25 + 4|K|): `goodT` excludes a row in K because `prob_not_claimsND_le` takes the values uniform in E. A
    challenge-dependent mask bound (2/|K| for the masks at a row in K, whose values are uniform in K; 2/|E|
    elsewhere) would avoid it, epsHV then below 2^-161, and with both changes ζ about 2^-157.
- Tested, not proved: the bytecode computes the graph; `FIELD_MUL` and `KECCAK256` are the Lean operations; the
  `PCS_OPEN` mock is `opening::verify`, and that is `PcsQuotient.openingWith`; the Statement's definitions are the
  Rust; the Rust verifier's expansion of pruned Merkle paths; the extractor's cost table and Gao's decoder.
- The deployed Rust prover is trusted for completeness: the Statement's prover is compared with it on the
  reduction's nine scalars at 2^17 rows only (not the openings, not at 2^22).
- The random-permutation theorems and the EVM theorem (at the real Keccak-f[1600]) do not formally compose.
- Not stated: simulation-extractability. `StatementBinds` (immediate) is not proved in Lean. The Statement's own
  `simulator` (`ZeroKnowledge ζ`, the field `Theorems.zeroKnowledge`) is a tested heuristic that no theorem covers.
- Outside the theorems: the `PCS_OPEN` aggregation layer must check all the claims of one call in one opening (the
  mock does); the deployed generator (ChaCha12 and the Keccak-256 KDF) must be indistinguishable from uniform.
- `UPSTREAM.md`: issues in vendored leanVM code to report upstream (an aliasing UB, now fixed here; a planner
  divide-by-zero; documentation errors).
- Possible gas saving: absorb the index root into the transcript in the byte order `PCS_OPEN` takes, to drop the
  132-gas byte reversal.

