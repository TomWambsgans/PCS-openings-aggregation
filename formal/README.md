# Formal verification of `crates/quotient`

Goal: knowledge soundness, completeness and statistical zero knowledge of the membership proof that
`crates/quotient` builds and `crates/evm` verifies, proved in Lean 4 end to end, with the **extractor and the
simulator as explicit, computable definitions in the statements** so that a reviewer can check that they are
efficient (the target: F1's extractor reads the proof's polynomials in the ideal model, and F1's extractor and
simulator are `noncomputable`; the computable ones are the `Statement` package's work, F4/F5) (Lean has no running-time theorem; the convention is leanerVM's: a fixed straight-line extractor
that reads only the adversary's oracle transcript, its cost read off its loops).

Toolchain and dependency revisions are leanerVM `mumbai`'s (Lean `v4.34.1`, Mathlib `d13f23b7`, VCVio
`afa6593f`, CompPoly `572f9973`, ArkLib `4dae3acf`), so its results can be imported rather than reproved. The
starting point is leanVM's `formal/quotient` (branch `PCS-openings-aggregation`), whose README is kept as
[`README.upstream.md`](README.upstream.md): sorry-free proofs of the reduction for the BLAKE2s/full-adder
circuit, with ideal commitments.

## Layers

| | What | Source | Status |
|---|---|---|---|
| F0 | The circuit: a Lean definition of the deployed wiring (`quotient::circuit::membership`), proof that a satisfying assignment is its computation and that this computation is Keccak-256 membership; the constants (Cantor basis, `τ`, `b`, the bit weights) as computable definitions whose hypotheses are checked | new (found missing by the Lean review: `Instance.soundness` holds for every wiring, so for a degenerate one it says nothing) | **done for a circuit given as a parameter** (`CircuitLayout.lean`, `Pinning.lean`, `Statement.lean`): `Instance.soundness_circuit`: for an instance whose wiring lays a loop-free χ circuit `C` (`Laid`: input cells on the cycle of what they read, word 5's 128 bits on the zero's cycle, word 4's bit 0 the one's anchor and its other bits on the zero's) and whose weights are `coordinate_weight`'s (`bit_weight(j)` = `x^j`, `Y x^(j-64)`, with `x ≠ 1`, `Y ≠ 1`), an accepted proof of `statementWords x Y y root` (`statement::halves` of `y`, `root`, then `(1, 0, 0, 0)`) holds `C`'s computation on some input bits with public words 0–3 the halves of `(y, root)`, except with probability `(Q + 3) / 2^128`; `soundness_circuit_bits`: with the 128 bit weights independent over `GF(2)`, its public bits are the bytes' bits as `circuit::public_words` reads them. Derived from `Instance.soundness` and `cells_determined` (bridged by `Instance.cells_determined`; zero then one pinned by `zero_pinned`, `one_pinned`); the cone of both reaches the circuit argument. Not vacuous: `wiringOf C` meets `Laid` (`laid_wiringOf`) and the cells of every computation of `C` satisfy the relation on it (`relation_wiringOf`, `relation_statementWords`). Sorry-free, on `propext`, `Classical.choice`, `Quot.sound`. **To do**: the deployed circuit as a Lean `C : ChiCircuit (Fin (2^22))` with `Laid` for the deployed wiring (or `I.wiring = wiringOf C`), its computation being Keccak-256 membership, and `x`, `Y` of `F192` with independent bit weights |
| F1 | The reduction (five field elements → four claims): round-by-round knowledge soundness, completeness, honest-verifier ZK, Fiat–Shamir in the ROM, **ideal commitments** | ported from leanVM `formal/quotient` and adapted (below): `2^22` rows, the χ gate on bits (degree 2), degree bounds, the circuit argument (bits, no carries) | done for the reduction: `lake build` green, sorry-free, end theorems on `propext`, `Classical.choice`, `Quot.sound` (761 declarations swept, `formal/Review/Axioms.lean`). Its zero knowledge is for ideal *hiding* commitments only: the deployed roots and openings are F3's (and the masks of the five values have no slack, so nothing else may reveal an evaluation of a witness polynomial). `Instance.soundness`, `zero_knowledge`, `completeness` hold for every wiring; `soundness_circuit` (F0) is for a wiring that lays a χ circuit |
| F2 | WHIR openings list-sound for our claims (some member of the root's level-0 list satisfies all claims of one opening) | leanerVM `mumbai`, `lean_vm` `Whir/Sound`: `stackedSpec` holds for any multiaffine weights; ours are | **done for the deployed openings** in [`WhirBridge/`](WhirBridge/README.md) (sorry-free, `propext`, `Classical.choice`, `Quot.sound`; 589 declarations swept, no `native_decide`): `ours_sound`, Fiat–Shamir soundness in the two-oracle ROM of `opening::verify` itself (version-2 transcript: IV `keccak256(prefix ‖ claims)`, zero public digest, root read from the proof and checked; no claim rejected) for the witness and quotient (hidden, **the redesigned layouts for condition (R)**: overflow lane 32, random lanes 33..39, the gadget) and wiring (public) layouts at every `2^17..2^22` rows: an adversary of `QA` queries outputting a root, claims and a proof makes it accept while every candidate **table** (`Table::read`) of the root's extracted word violates a claim with probability ≤ `(QA + 10122)(2^-128 + 5(QA + 10122)/2^256)` ≤ `2^-63` for `QA ≤ 2^64`. The Lean `Layout` has every field of the Rust's, both branches of the weight closure transcribed with the gadget's term (the gadget one more stack claim of value zero, batched with `λ^m`; every weight multiaffine; `holds_iff` for the hidden layouts' claims, `gadget_holds_iff`: the gadget says the pattern lanes' `β`-combination at its entries is zero; the event, on the claims only, implies mumbai's doom, which counts the gadget); `Test/Check.lean` accepts the Rust's deployed witness and quotient openings, rejects them without the gadget's term, and recomputes the 18 prefixes. Level-0 candidates per root exported: ≤ 9,952 (wiring), 7,908 (witness), 3,564 (quotient). Not covered: the random-permutation model, pruned paths, the Rust being the Lean mirror (test evidence), extraction from the adversary's queries alone, composition with the reduction (F4) |
| F3 | Hiding openings: the padded tables (base field `K = GF(2^64)`, challenges in `E = GF(2^192)`, first fold 6); then (F3b) the roots, Merkle siblings, nonces and Fiat–Shamir in the random-oracle and random-permutation models, with an explicit simulator | new (the ZK-WHIR note, adapted to `K ⊂ E`; `membership-zk.md` of leanVM's branch for the sibling argument) | Lean: `formal/QuotientSecurity/Hiding/` (sorry-free): for two tables with the same claims, the views (lane rounds, the folded table, every opened row) have the same distribution on the good challenges (`hidden_view_evalDistEq`), and differ by at most Pr[(R) fails] + ~2^-127 on any event (`hidden_prEvent_le_bound`; (S) bounded by `card_not_span_four_le`); unopened rows keep ≥ 2,368 / 3,840 bits (`unopened_row_le`). Condition (R) (`RoundsReached`) is a hypothesis with no bound in Lean (estimated ≈ 2^-53 in `HIDING.md`, not proven); a layout change that makes it hold for all challenges is being designed. The view is the linear part only: not modelled are the level-0 roots (in calldata), the Merkle siblings, the grinding nonces and Fiat–Shamir (F3b, in progress; `formal/Review/HidingReview.lean`'s `stack_ne_of_entry_ne`: hiding of the roots rests on that random-oracle step). Per table, interactive, honest verifier; (Q) and `WeightsFit` are hypotheses, not yet instantiated with the deployed layout. The padding is uniform here; the prover's comes from a CSPRNG (ChaCha12 keyed by a Keccak-256 KDF of an OS seed), so as deployed the hiding is computational in that generator |
| F4 | Composition: commitments as Merkle trees over Keccak-256 in the random-permutation model, the reduction's Keccak-256 chain, the openings' duplex; extraction from the adversary's transcript (`mumbai`'s `Statement/Extractor.lean` decodes WHIR words by Guruswami–Sudan) | `mumbai` `common` (sponge indifferentiability, ROM→RPM), `lean_vm` extraction | **the chain (F4a) done** in [`QuotientRpm/`](#the-keccak-256-chain-f4a) (sorry-free, `propext`, `Classical.choice`, `Quot.sound`): the reduction with `transcript.rs`'s chain, byte for byte, in the ROM and in leanerVM's RPM, ideal commitments (a root is Keccak-256 of an injective encoding of the message). **Real commitments composed with the openings (F4b)** in [`Compose/`](Compose/README.md) (sorry-free, same three axioms): the chain absorbs the proof's roots, every round union-bounded over the roots' candidate lists (`L₁` for `(α, β, γ)`, `L₁ L₂` for `t`, `ρ`; `≤ 2^-128` per query for lists up to `2^18`, `2^-138` with the certified `7908` / `3564`), the Merkle extraction from the transcript (computable, stable; mumbai's `extract` without collisions, `wordOfMerkle_eq_extract`), in the ROM and in mumbai's two-oracle model. The general statements (`knowledgeSoundness_merkle`, `_kc`) take the openings' doomed events as hypotheses: events in F2's oracle model, **not** literally F2's (any openings' verifier; `merkleWord` and a decoder for `extract`, `Candidates`, `Layout.tableEval`; F1's polynomial identities for `reduce`'s multilinear claims; the final transcript for the cache at the end of the opening), and their extractor reads every Keccak-256 query of the run. **The deployed composition** (`Deployed.lean`, `knowledgeSoundness_deployed_setup`): the circuit's commitment computed with the oracle before the adversary runs (`withSetup`, `wiringSetup`) and used in the chain's label and as the wiring opening's root; the chain, then `opening::verify` three times (F2's `ourVerifier`); the extractor reads the setup's and the adversary's queries only (`adversaryExtractor`; a verifier answer equal to an announced root costs `2/2^256` per query); the witness and quotient terms **are** F2's `ours_sound` (`prEvent_EW_le`, `prEvent_EQ_le`, through the run's prefix as `romExperiment`, the stage cache read off the transcript): `openingBound (QS + Q + 6) + εσ + openingBound (QS + Q + 6 + 2 QO) + N (max L₁ (L₁ L₂) · roundError + 5 N / 2^256)`, `N = QS + Q + 6 + 3 QO`. Hypotheses left: the decoders and claims matched to F1's (`WitnessMatch`, `QuotientMatch`), the wiring term `εσ` (its discharge, the honest root's only candidate being the wiring table, to do), the RPM transfer (to do) |
| F5 | The implementation is the model: the EVM contract and the Rust verifier are generated from one recorded operation graph (`crates/evm/src/record.rs`); emit that graph as a Lean term too and prove it equals the model's verifier | new | to do |

## The Keccak-256 chain (F4a)

`QuotientRpm/` (library `QuotientRpm`, which needs leanerVM `mumbai`'s `statement` and `common` packages,
pinned in `lakefile.toml`) lifts the reduction's knowledge soundness from an abstract random oracle on
`(statement, messages)` to the transcript `crates/quotient/src/transcript.rs` computes.

- **The chain** (`Bytes.lean`, `Chain.lean`): the seed is Keccak-256 of the label `pcs-quotient-kc1 ‖
  index_root ‖ y ‖ root` (112 bytes); each challenge is Keccak-256 of the state and of the scalars sent since
  the last one, each a 32-byte big-endian word (`[0; 8] ‖ c2 ‖ c1 ‖ c0`, `scalarWord`), and is the state's low
  192 bits (`stateLimbs`: limb `i` is bytes `24 − 8i .. 32 − 8i`, big-endian); a root is two scalars, its
  128-bit halves read as little-endian words (`rootScalars`), i.e. sixteen zero bytes and the half reversed
  (`rootWords_eq`). The verifier (`Wire.verifyWith`, over any hash in any monad): root, `α`, `β`, `γ`, root,
  `t`, five values, `ρ`, as in `reduce`. A `Wire` holds what the chain reads besides the proof: the circuit's
  commitment, how the statement's 64 bytes are read as `Params`' statement, the field's limbs, and the two
  messages' encodings. **Commitments are ideal**: the proof carries the polynomials and the root the chain
  absorbs is Keccak-256 of an injective encoding of them, binding up to a collision (counted).
- **Random oracle on transcripts** (`ChainRom.lean`, `FreshBad.lean`, `Uniform.lean`): against a random oracle
  `H : bytes → 32 bytes`, a fresh query is bad (`chainBad`) when its answer collides with an earlier answer or
  sits where an earlier input holds a state or a root (`Coll`, at most `(3|H| + 2)/2^256`), or when it is a
  chain input whose challenge(s) turn the round's state from lost to won (`FirstBad`, `SecondBad`,
  `ThirdBad`: the first round's three hashes are treated as one triple of uniform states; the parse is unique
  given a collision-free history, so the three are exclusive, each at most `roundError`). The low 192 bits of
  a uniform state are uniform (`prEvent_chal`, every limb triple having `256^8` states). An accepted proof of
  cells that fail the relation makes a fresh query bad (`trace_chainBad`, through `bad_of_accepts` of
  `Joint.lean`); with an eager-table lemma whose bad events see the history (`prEvent_randomOracle_le_of_freshBad`,
  after VCVio's `prEvent_randomOracle_le_of_bad_queries`): **`knowledgeSoundness_chain`**, at most
  `(Q + 8)(roundError + 3(Q + 8)/2^256)` for `Q` adversary queries (the verifier's eight hashes counted).
- **The random-permutation model** (`Rpm.lean`): the experiment `rpmExperiment` has the adversary (coins, `π`,
  `π⁻¹`) and the verifier hashing with Keccak-256 over the same `π`; `common`'s `runK_expand`, `runK_relabel`
  and `keccak256_transfer` move it to the ROM against `advS` (cost `Q²/2^509`, `Q` the permutation calls of
  the whole game), leanerVM's derandomization removes the simulator's coins (`exists_det`).
  **`knowledgeSoundness_rpm`**: `(Q + 8)(roundError + 3(Q + 8)/2^256) + Q²/2^509`; at the protocol's sizes
  (`roundError_le`: `≤ 2^-163`, the identities' degree `2^29` over `2^192`) **`knowledgeSoundness_rpm_bits`**
  and, for every circuit, **`Instance.soundness_rpm`**: `(Q + 8)(2^-163 + 3(Q + 8)/2^256) + Q²/2^509`.

## Zero knowledge of the non-interactive proof (F3b)

`QuotientZk/` (library `QuotientZk`, sorry-free, `propext`, `Classical.choice`, `Quot.sound`) proves
statistical zero knowledge of the proof the Rust prover outputs (calldata and the three openings: roots,
multiproofs and opened rows, the stream, grinding nonces) in the random-oracle model, with the simulator an
explicit computable definition in the statement. The prover's randomness is uniform (the deployed masks and
padding come from ChaCha12 keyed by a Keccak KDF of a 32-byte OS seed: the deployed statement is computational
in that PRG).

- **The model** (`Rom/Defs.lean`): the prover is a public *skeleton* of four operations, a random-oracle query
  (`pub`), a Fiat–Shamir query (`chal`, its answer the next challenge), the next message (`msg`) and the digest of
  a secret table's leaf (`leaf`); an implementation answers them. The real prover (`implReal`): the random oracle
  and the secret. **The simulator** (`sim`): draws the `n` challenges, then the view from the honest-verifier
  simulator `simV`, then runs the same skeleton with `implView`: the `c`-th Fiat–Shamir query answered by the
  `c`-th drawn challenge and written into the oracle's cache (programming), messages and opened rows from the
  simulated view, a fresh private digest at every unopened leaf (so siblings and roots hash fresh values);
  everything else, grinding included, from its own lazily sampled oracle. It outputs the proof and the cache the
  distinguisher then queries. Cost: the honest prover's oracle operations (the skeleton, at most `2^70` at the
  deployed shapes, worst-case grinding counted; the expected grinding is `2^17` permutations a level, 16 levels),
  with no table, plus `simV`. `Check.lean` runs it (`runIO`) on a toy protocol.
- **`zk_rom`** (`Rom/Main.lean`): for every distinguisher of at most `QD` queries, the real game and the
  simulated one output `true` with probabilities within `εFS + εhv + N (|c₀| + QP + QD) δ + N² δ₂`: real →
  fresh challenges (until a Fiat–Shamir input was already answered, `εFS`, `FS.lean`) → challenges drawn first
  (the same, `Tape.lean`) → unopened leaves kept apart (the same, `Split.lean`) → the simulator's implementation
  with the honest view (until an unopened row is asked or two collide, `Merkle.lean`; bounded by the rows'
  entropy, `MerkleBound.lean`, `Entropy.lean`) → the simulated view (`εhv`).
- **The deployed prover** (`Deployed/`): `skel` transcribes, at the level of its oracle calls, the reduction's
  Keccak-256 chain (F4a's bytes), leanVM's Merkle trees (`H(row image)`, `H(left ‖ right)`) and
  `PrunedMerklePaths`, the overwrite duplex (four scalars with tags, a draw a permutation, the fifth scalar a
  permutation of its own), grinding (smallest 17-bit nonce from 0) and `recursive_prover`'s order of events;
  `deployedShape` the three openings at `2^22` rows. `skel_queryBound`, `skelBound_deployed`: at most `2^70`
  operations. The entropy hypotheses of `zk_rom` are **proved** from each secret table's factorization
  (`Factors`: the joint view a function of the rest of the randomness and of the table's F3 view, its padding
  independent) and the redesigned layout's row entropy (`row_entropy` for any layout whose entries below the
  gadget are free, `gadget_stackR_of_onFirst` for `GadgetLayout`; pairs of rows too): `δ = 2^-64(L-3)`,
  `2^-2368` (40 lanes) and `2^-3840` (63). **`zk_deployed_bits`**: `εFS + εhv + 2^-2200`.
- **What stays a hypothesis**: `JointHVZK` (the interactive protocol's honest-verifier zero knowledge, F1 with F3
  and the gadget's (R)); `FSFresh` (the honest prover's Fiat–Shamir inputs fresh but with probability `εFS`: every
  such input holds the previous chain state or duplex capacity, or a fresh root; a collision bound not formalized);
  `Factors` for the deployed prover (structural: the masks and the two paddings are independent and WHIR's
  messages after the first fold are functions of `f¹`); that `skel` is the Rust prover (transcribed, not
  differential-tested). The lift to leanerVM's random-permutation model is separate (`QuotientZk/Rpm.lean`).

## End-to-end completeness (`Completeness/`)

`Completeness/` (package `pcs-quotient-completeness`, built like `Compose/` against leanerVM `mumbai`'s
`lean_vm`; sorry-free, every end theorem on `propext`, `Classical.choice`, `Quot.sound`, checked by
`#guard_msgs` in `Completeness.lean`) proves that **the honest prover's proof is accepted by the deployed
verifier**, the three openings included, for every hash function and permutation (the deployed Keccak-256 and
Keccak-f[1600] among them), except on an explicit set of challenges, on the deployed instance (circuit, σ,
weights, Cantor basis) with no hypothesis left (`completeness_deployed_concrete`).

- **The verifier** (`deployedVerify`, `Deployed.lean`): the transcript's challenges from the proof's roots and
  values (`Transcript`; `keccakTranscript` is `transcript.rs`'s chain, `Chain.lean`), `reduce`'s own check
  (`RustCheck`: every `1 + w_k(t)`, `k ≤ 25`, the copy denominator and the rows' polynomial nonzero, else
  `VerifyError::Degenerate`), and the four claims, at the points and with the values of
  `claims_iff_accepts` (F1's coordinate-by-coordinate comparison with `reduce`), opened by
  `opening::verify` (`WhirBridge.openingVerifyWithHash`) on `witness_layout(22)`, `wiring_layout(22)` and
  `quotient_layout(22)`, the quotient table's two claims in one opening.
- **The honest prover** (`honestRun`, `honestProve`), precisely specified (noncomputable: tables by
  `exists_table`, a quotient by `Classical.choose` of its `K`-preimage): the assignment the circuit computes
  from the secret, the witness table (the cells' novel-basis coefficients over `K`, the masks at
  `2^24 + 4i + j`), its hidden stack (`Layout.fillNew` = `Table::hidden`, any padding) and root, F1's
  `Params.honest` second message, the quotient table (its slots' limbs over `K`, `Honest.lean`), its stack and
  root, the five values, and mumbai's compiled WHIR prover for each opening (`honestOpen`).
- **`completeness_end`** (`HiddenOpenings.lean`): if the honest prover returns a proof (it fails only when a
  17-bit proof-of-work search finds no nonce below the fuel, `exists_failed_pow`) and its challenges are not
  degenerate (`¬ BadAB`: no `α + w(x) + β x` vanishes at a cell; `¬ Degenerate`: the Rust check passes at
  `t`), the verifier accepts. **`completeness_end_bad_set`**: for each witness (secret and masks) one set
  `Bad` of triples `(α, β, t)`, independent of the hash, the transcript and the padding, of density at most
  `(17 · 2^24 + 8) / 2^192 < 2^-163` (`Reduction.bad_fraction_le`, `bad_bound_lt`: `2 · 2^24` cells times two
  denominators for `(α, β)`, then `11 · 2^24 + 8` roots of the product `reduce` inverts and `2^26 − 1` of the
  `1 + w_k`), outside which the honest proof is accepted. The openings' proofs of work, in the random-oracle
  model: at most `2^-277` per opening at a fuel of `2^25` (`ours_romComplete`, from mumbai's `romComplete`).
- **The pieces**: the circuit (`Circuit.lean`: `honest_relation`, F0a's `relation_statementWords` for any wiring
  keeping what the cells carry); the
  reduction (`Reduction.lean`: `honest_accepts`, F1's `honest_consistent` and `accepts_of_consistent`); the
  tables (`Tables.lean`, `Honest.lean`, `Read.lean`: novel-basis tables of bounded support over `K`, the gate
  quotient over `K` (`qGate_mem_lifts`), the honest degrees (`q ≤ 3 · 2^24 + 9249`, the gate's
  `≤ 7 · 2^22 + 22`), the honest tables vanish off `witness_layout`'s and `quotient_chunks`' chunks, `mle` is
  the openings' `Σ_t T(t) eq(t, p)`); the hidden stacks (`HiddenFill.lean`: `Table::read` of the honest stack is
  the table, the gadget cancels; `HiddenOpenings.lean`: with F2's `holds_iff` and `extra_holds_iff`); the
  wiring opening (`Wiring.lean`); mumbai's WHIR completeness (`Opening.lean`: `honestOpen_accepts` for any
  stacking whose stack claims hold, `openingVerify_honest`, `romComplete_ours`).
- **The deployed circuit, σ, weights and basis** (`Membership.lean`, `QuotientSecurity/DeployedHonest.lean`,
  `QuotientSecurity/DeployedBasis.lean`): the interface the theorems above take for the circuit,
  `MembershipCircuit` (the `ChiCircuit`, the assignment it computes from a secret, and Keccak-256 correctness
  forward), is built from F0b's `deployed` (`deployedMembership`). The assignment is `deployed` evaluated on
  `membership_inputs(s)` (`ChiCircuit.eval`, row by row in rank order: it satisfies every gate and holds the
  inputs, `eval_satisfies`, `eval_input`, and is the only such computation, `eq_eval`), which is the Rust's
  `Circuit::outputs` (`deployedAssign_eq_outputs`: `Circuit.outputs` computes it, its second loop running the
  rows in rank order; so `outputs_satisfies`, F0b's open point); its public bits are the
  statement's by F0b's `membership_public` applied to it (`deployedAssign_public`), this file's `Secret` read as
  F0b's (`Secret.toPcs`: `pair` is F0b's `H` of the concatenation, the path folded the same way). The wiring
  hypothesis is now `WiringKeeps I.wiring M.C` (every cell and its successor carry the same source; `wiringOf C`
  meets it), and **the deployed σ** (`membership.sigma`, soundness's `deployedSigma`) meets it
  (`deployedSigma_cellSrc`: `finish`'s σ is the cyclic successor among one slot's cells, `wiring_slot`, and a
  slot names one source). The instance is soundness's `deployedInstance` with `beta()`'s basis
  (`deployedInstanceE`; `deployedBasis`: the 24 words of `domain.rs`'s `beta()`, a Cantor basis of `F64 = K`
  checked by the kernel, its vectors after the first of low bit clear, which determines it,
  `deployedBasis_unique`; `crates/quotient/tests/lean_beta_vector.rs` asserts the words of the Rust), `hB`,
  `hc`, `hw` by definition. **`completeness_deployed_concrete`**: on that instance, for each witness one set
  `Bad` of `(α, β, t)` of density `< 2^-163` outside which, for every transcript, hash, permutation and padding,
  the honest proof (when the openings' proofs of work succeed) is accepted; **`completeness_deployed_keccak`**
  the same on `transcript.rs`'s chain (`deployedChain`). No circuit, wiring, weight or basis hypothesis remains
  (`completeness_deployed_basis`: any Cantor basis of `K`; `completeness_deployed_sigma`: any instance with the
  deployed σ). **Not covered**: a random-oracle theorem for the chain's honest challenges (the
  density above is over uniform `(α, β, t)`; an honest run's chain queries are fresh but for collisions, a few
  `Q² / 2^256`), one experiment holding both the chain and the openings' proofs of work, `log_rows < 22`, and
  that the Rust is this Lean (F5; the claims' values by F1's review, the openings by F2's tests).

## The port to this protocol (F1)

`README.upstream.md` describes leanVM's circuit; this protocol differs in three ways, and the Lean files now
describe this one.

- **The gate** (`Protocol.lean`'s `gate`, `quotient::protocol`'s `gate`): `V + X + C + Y·C`, that is
  `V = X ⊕ (C ∧ ¬Y)` on bits (Keccak's χ), of degree 2, with no `θ` and no carries. `θ = β_1` stays in `Params`:
  it places a row's four cells at `x, x + 1, x + θ, x + θ + 1`.
- **The circuit argument** (`Circuit.lean`): `ChiCircuit` replaces `AdderCircuit`. An input row reads its own
  output in `X`, `Y` and `C` (`quotient::circuit::Builder::input`), so its gate is `v + v + v + v·v = v^2 + v`
  and `input_is_bit`: it holds `0` or `1`; every other row reads constants or rows of lower rank, and
  `gate_output`: on bits the gate gives `V = chiOf X Y C`, a bit. `ChiCircuit.determined`: two assignments, in
  any field of characteristic 2, that satisfy every gate and agree on the inputs agree everywhere, and every
  output is a bit (no `GF(4)`). `cells_determined`, `copy_iterate`, `word_pins`, `Wired` are as before, on bits.
- **The size**: `2^22` rows, cells named by `m = 24` bits (`22 + 2`, the opaque `le24`), `N = 2^24` cells;
  the tables have `m + 1 = 25` (witness), `m = 24` (wiring) and `m + 6 = 30` (quotient) variables, as
  `claims_iff_accepts_ofCantor` states them (the WHIR stacks of `opening::Layout` are not modelled: a table
  of the layout is a table whose other chunks are zero).

**The bounds, re-derived** (`Degrees.lean`, `Concrete.lean`, `Bits.lean`). `Bounds.identity` is the largest
of the bounds on the terms of the two identities (upstream summed them): with the gate of degree 2 it is
`max (max (2 * denominator) cells + max cells rows + quotient) (2 * denominator + max (pub + cell) (2 * cell))`
(the terms `D D' h`, `v_cells q`, `v_rows (D D' q_gate + v_cells j)`, `pub w D D'`, `D D' gate`; it bounds the
product the verifier inverts too). At the instance's table sizes
(witness polynomials `2^23`, quotients `2^26`, wiring and cells `2^24`, rows `2^22`, public weight
`2^24 + 9 * 2^10`): a cell's polynomial `4 * 2^23 + 3`, a denominator `3 * 2^24 + 4`, and
`Params.ofCantor_identity_eq`: the identities' degree is at most `11 * 2^24 + 8` (`11 N` and a little, the copy
identity's `D D' h`; the sum was `2^28 + 2^22 + 9230`), so `Params.ofCantor_identity_le_margin`: at most `2^28`
(and `Params.ofCantor_identity`: at most `2^29`). The public weight's degree (`natDegree_membershipPub_le`) is
`Σ_{11 ≤ j < 24} 2^j + 11 * 2^10 = 2^24 + 9 * 2^10`. The three round errors over `q = 2^192`
(`rbrError_le`): the copy argument `(4 N + 8) / q = (2^26 + 8) / 2^192`, about `2^-166` (was
`(2 N^2 + 4 N + 8) / q`, about `2^-143`; below), the identities `(11 * 2^24 + 8) / 2^192 < 2^-164`, the last
`3 / 2^192`; each `≤ 2^-128`, so `knowledgeSoundness_bits`, `knowledgeSoundness_ofCantor`,
`knowledgeSoundness_membership`, `Instance.soundness` give `(Q + 3) / 2^128`.

*The first challenge, tight* (`card_consistent_le`, `card_copy_le`, `LogDerivative.lean`). Upstream excluded
`2 N^2` values of `β` (any two poles meeting) and `2 N q^2` triples with a vanishing denominator. Now, if the
copy from `x₁` to `σ x₁` fails: a consistent triple has, at every cell, both denominators zero or neither
(`consistent_denominators`: the copy identity at a cell is `D D' h = D + D' + pub w D D'`), and where none
vanishes the sum of logarithmic derivatives meets the target. The pole `w(σ x₁) + β σ x₁` of the first term of
`σ x₁` is cancelled only by the first term of another cell (`N - 1` values of `β`) or the second term of a
cell other than `x₁` (`N - 1` values; the second term of `x₁` has the same label and another value): outside
these `2 N - 2` values (`poleBetas`) the cleared polynomial in `α` is not zero and of degree at most `2 N`, and
every consistent `α` is a root of it (one at which a cell's two denominators vanish together too). So at most
`(2 N - 2) q + 2 N q` pairs `(α, β)` per `γ`, and with the other cases (a gate fails: `2 N q^2`; a word fails:
`(2 N + words) q^2`) at most `(4 N + words) q^2` triples. This also beats the `(6 N + 8) / q` of the review,
which still counted the triples with a vanishing denominator apart.

*The margin for WHIR's lists* (`rbrError_mul_sq_le`, `rbrError_list_margin`, `rbrError_list_margin_ofCantor`,
`roundError_mul_sq_le`). With WHIR without an out-of-domain sample at level 0, each challenge is
union-bounded over the level-0 Johnson lists involved: `L` for `(α, β, γ)` and for `ρ`, `L^2` for `t`. For any
`L ≤ 2^18` (leanerVM's generic list hypothesis; its certified parameters give `L ≤ 7908`) and identities of
degree at most `2^28`, every round error times `L^2` stays at most `2^-128`: on the instance
`2^36 (2^26 + 8) / 2^192`, about `2^-130`, `2^36 (11 * 2^24 + 8) / 2^192`, about `2^-128.5`, and
`3 * 2^36 / 2^192`. Both tightenings are needed: upstream's first round times `2^18` is `2^-125`, and the
summed degree `2^28 + 2^22 + 9230` times `2^36` exceeds `2^-128`.
Zero knowledge: `zkError = (2 N + 4 * 2^22) / q = 3 * 2^24 / 2^192` (`zkError_le`, the mask's vanishing
polynomial `w_22` in the row variable). The honest messages (`honest_legal`, for a first message of degree
`2^22 + 2`): copy quotient at most `3 * 2^24 + 9249`, gate quotient at most `7 * 2^22 + 22`, both within the
quotient table's `2^26`. Completeness's uncounted rejection (`1 + w_k(t) = 0` for some `k ≤ m + 1`) is now
about `2^26 / q`.

**The claims against the Rust `reduce`.** Reviewed coordinate by coordinate for this protocol: the witness,
wiring and quotient claims' points and values, the sum claim, the cells of the row of `t`, the gate, the
public weight's product, the target, the rows' polynomial and the rejection; the comparison is written out
above `claims_iff_accepts_ofCantor` (`Concrete.lean`). No mismatch; `reduce` is leanVM's but for the gate,
which is the model's `gate` on `cellAt`.

## What will be trusted (the target)

The Keccak-f\[1600\] permutation behaves as a random permutation (leanerVM's model; note that one Keccak-256 serves
the reduction's transcript, the WHIR Merkle trees and the statement's own Merkle tree, so the model must be the
shared random permutation, not a private oracle as in F1); the Lean kernel and the three standard axioms; until
F0 is done, that the circuit committed as the index root is a Lean `C` meeting `Laid` whose computation is the statement (the step from such a `C` to the end theorem is proved: `soundness_circuit`); the EVM bytecode generator and revm with `FIELD_MUL` (differential tests, not proofs);
the PCS_OPEN aggregation layer, which must check all the claims of each call in one opening; the Rust prover (only completeness depends on it).
