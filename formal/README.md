# Formal verification of `crates/quotient`

Knowledge soundness, completeness and statistical zero knowledge of the membership proof that `crates/quotient`
builds and `crates/evm` verifies, in Lean 4. **The statement** is [`Statement/`](Statement/README.md), a Lake
package of definitions and end statements only, on leanerVM `mumbai`'s `Statement/`: the relation, the proof
format, the verifier (computable, differential-tested against the Rust), the honest prover, the extractor and
the simulator, and `KnowledgeSoundness`, `Completeness`, `ZeroKnowledge(With)` in the random-permutation model.
The extractor is an explicit, computable definition in the statements, so that a reviewer can check what it
reads and that it is efficient; the simulator the zero-knowledge theorem covers is named in its statement: an
explicit simulator, compiled in `zeroKnowledge_closed_computable`. Lean has no running-time theorem; the convention is
leanerVM's: a fixed straight-line extractor, its cost read off its loops. Here the extractor reads the
statement, the proof, the adversary's transcript and the public setup tree (the circuit commitment's Merkle
tree). **The proofs** of the statements are in [`EndToEnd/`](#end-to-end-theorems), from the layers F0–F5 below.

Toolchain and dependency revisions are leanerVM `mumbai`'s (Lean `v4.34.1`, Mathlib `d13f23b7`, VCVio
`afa6593f`, CompPoly `572f9973`, ArkLib `4dae3acf`), so its results can be imported rather than reproved. The
starting point is leanVM's `formal/quotient` (branch `PCS-openings-aggregation`), whose README is kept as
[`README.upstream.md`](README.upstream.md): sorry-free proofs of the reduction for the BLAKE2s/full-adder
circuit, with ideal commitments.

**The univariate PIOP for leanVM 42422001** (`crates/leanvm_univariate`, milestone 4): its verifier transcribed
and differential-tested, with its end statements `UniKnowledgeSoundness` and `UniCompleteness` against
[`Lv42/`](Lv42)'s relation `M3Holds`, is [`UniStatement/`](UniStatement/README.md), a library of `EndToEnd/`;
its knowledge soundness is proved, with no hypothesis, in `UniSound/` and `FlockSound/`
([below](#the-univariate-verifier-for-leanvm-42422001-knowledge-soundness)).

**The recursion's inner verifier as a graph** (`crates/leanvm_rec`, π1-rec3): [`RecGraph/`](RecGraph/README.md), a
library of `EndToEnd/`: π1-rec3's recorded verifier graph (written by the Rust, data only), its semantics over any
permutation, the Lean recorder with "recording commutes with evaluation", and **graph = `UniStatement`'s verifier at
π1-rec3** (`UniStatement/UniStatement/Rec.lean`), proved off the merge hazard (`RecGraph.Pi1.pi1GraphIsVerifier`, no
other hypothesis; the hazard, `y(t)` starting like `w` or Flock's point, has probability at most `2^19/|E|`:
`hazard_prob`). The recorded graph is the Rust's node for node (`RecGraphTest/Pi1Check.lean`, by computation), and
an oracle under which the graph and the verifier differ on the hazard is exhibited (`RecGraphTest/Runner.lean`).

**The recursion's outer verifier** (`crates/leanvm_rec`, π2): [`RecStatement/`](RecStatement/README.md), a library of
`EndToEnd/`: π2's verifier as computable Lean (the seed and IV, the public data in the stream, the arithmetic at `t`
over any field, the six `PCS_OPEN` calls word for word), the circuit's tables as data the Rust emits (with a staleness
test), differential-tested on the real π1-rec3 + π2 proof and 63 other streams (64/64 agree on every value); the
verifier-arithmetic lemmas that [`RecPiop/`](RecPiop)'s rounds consume (proved: the indicators' and the zero coset's
closed forms, the siblings' fold, and `checks_claims_iff`: the checks pass and the claims hold iff `t ∉ V_{m+2}`,
`c_h + c_q ≠ 0` and `RecPiop.Post2`); and the recursive verifier's end statements, stated, not proved, in two parts,
since π2's circuit computes π1's Fiat–Shamir with the real Keccak-f[1600] while π1-rec3's soundness is proved in the
random-permutation model: π2's part in that model (`RecKnowledgeSoundness2`, `RecCompleteness2`: the contract accepts
only if π1-rec3's recorded graph, at Keccak-f[1600], accepts the stream π2's extractor outputs); end-to-end knowledge
soundness against `Lv42`'s `M3Holds` as an explicit reduction (`RecKnowledgeSoundnessReduction`: π2's error plus
π1-rec3's and the merge hazard's experiments at Keccak-f[1600] for two explicit adversaries derived from the attacker);
and the corollaries `RecKnowledgeSoundness`, `RecCompleteness` under named hypotheses about π1-rec3 at Keccak-f[1600]
(`Pi1FsKeccak` and its kin; the soundness ones false as stated for unbounded adversaries, the Fiat–Shamir heuristic
for bounded ones).

## End-to-end theorems

`EndToEnd/` (a Lake workspace, `EndToEnd/lakefile.toml`) proves the Statement's end statements about the
Statement's own definitions. Every theorem below is sorry-free and depends only on `propext`,
`Classical.choice` and `Quot.sound`, checked by `#guard_msgs` in each library (so no `native_decide`).

- **Knowledge soundness: proved, no hypotheses.** `Soundness.knowledgeSoundness :
  PcsQuotient.KnowledgeSoundness Soundness.ksBound` (`EndToEnd/Soundness/Final.lean`, library `Soundness`). In
  one random permutation π: the setup computes the circuit's commitment over π; the adversary is given its root,
  makes at most `Q` calls of π and π⁻¹ (its coins free), and outputs a statement and a proof. The probability
  that the verifier accepts while `PcsQuotient.extractor` returns no secret satisfying `PcsQuotient.Relation`
  (Keccak-256 Merkle membership over the deployed Keccak-256) is at most `ksBound Q`: about `2^-105` at `Q = 0`,
  `2^-86` at `2^40`, `2^-62` at `2^64` (`EndToEnd/Review/E2ESoundnessNumbers.py`). The extractor queries
  no π and does not rerun the adversary: a hash-map replay and Merkle inversion (proved equal to mumbai's
  lists), then interpolation, Gao's unique decoder, and the Guruswami–Sudan list decoder only beyond the
  unique-decoding radius (the cost table in `Statement/PcsQuotient/Extractor.lean`: about `2^34.3` operations of
  `K` for a word with few wrong columns, at most `2^45.7` within the radius, about `2^98` beyond it). This is
  stand-alone knowledge soundness, not simulation-extractability. The proof: F4's random-permutation theorem at
  the deployed claim maps (`Soundness.knowledgeSoundness_rust_rpm`); the Statement's experiment coupled to F4's
  (the same setup and adversary, the verifiers run last); the bridge's three facts (`EndToEnd/Bridge/Facts.lean`:
  `setupBridge_final`, `verifierBridge_final`, `readsSecret_final`).
- **Completeness: proved, no hypotheses.** `E2ECompleteness.completeness_end : PcsQuotient.Completeness
  deltaDeployed` (`EndToEnd/Completeness/E2ECompleteness/Done.lean`, library `E2ECompleteness`). For every
  statement and secret of the relation, the Statement's honest prover with uniform coins, then the verifier, in
  one random permutation, rejects with probability at most `deltaDeployed = (17 · 2^24 + 8)/2^192 + 2/2^256 +
  3 · 2^-277 + (2^48)²/2^508 ≈ 2^-163.91`: degenerate challenges (`2^-163.91`), a chain query that is not fresh
  (`2^-255`), the proofs of work (`2^-275.4`; the proof bounds the whole run's grinding failure by `2^-304`,
  `grinding_le`), the permutation as two random oracles (`2^-412`; the run makes exactly `114 098 677 826 653 <
  2^47` block calls, `hcost_exact`) ("End-to-end completeness", below). The same `δ` holds for every fixed value
  of the coins (`completeness_every_coins`, `EndToEnd/Review/E2ECompletenessReview.lean`), so the uniform-coins
  model does not matter for completeness. The prover is the Statement's; the deployed Rust prover is trusted
  for completeness (below).
- **Zero knowledge: proved, no hypotheses.** `PcsQuotient.EndToEnd.zeroKnowledge_closed :
  PcsQuotient.ZeroKnowledgeWith s₀ (zkSimulator …) rpmSimOracle (zkBoundEnd ((2^24 + 2^70)·12) fmtBudget
  (· ↦ deltaNone))` (`EndToEnd/ZK/CoreMain.lean`, library `ZK`). For every statement and secret of the relation and
  every distinguisher of at most `Q` calls of π and π⁻¹ fixed after them, its verdicts on the honest proof and on
  the simulator's proof (the permutation programmable) differ in probability by at most `ζ Q ≈ 2^-113` for
  `Q ≤ 2^126`. The simulator is named in the statement (`zkSimulator`, `rpmSimOracle`) and reads no witness: an
  explicit simulator; `zeroKnowledge_closed_computable` restates the theorem with a compiled simulator (no axiom and no `noncomputable` constant in its closure) (its tables by Gaussian
  elimination, `QuotientZk/Instance/Builder.lean`). **Scope: single-proof zero knowledge.** `realExperiment` starts from an
  empty permutation, the prover goes first, and the distinguisher queries `π`, `π⁻¹` only after the proof; not
  covered are oracle queries before the proof (precomputation, auxiliary input depending on `π`) and several
  proofs under one `π` (a pre-proof phase is planned).
  The largest term of `ζ` is Fiat–Shamir freshness, `2^-113` (`6 Q'(c + Q')/2^256 ≈ 2^-113.4` for the honest
  prover's `Q' = 2^24 + 2^70` oracle operations, worst-case grinding counted, and `c = 2^19` public rows); the
  others are `epsHV = 2^-165 + 2^-125 + 2/2^192` (bad challenges, degenerate scales and masks), `deltaNone <
  2^-162` (the prover makes no proof or meets degenerate `α, β`), `2^-2200` (unopened leaves) and
  `(Qp + 2^23 + Q)²/2^508 ≤ 2^-256` (the permutation). Two statement changes were needed: the deterministic core
  `CoreWhir` is false at degenerate `α, β` and is stated off them (`CoreWhirG`, proved as `coreD`), those `α, β`
  charged to `deltaNone`; `fmt`'s `fillRun` ends at the program's `fail` as at its `ret` (as mumbai's `runFrom`).
  Details: "Zero knowledge end to end", below.
- **The EVM contract is the Statement's verifier.** `Evm.evm_accepts_iff_verifyWith` (`EndToEnd/Evm/Contract.lean`,
  library `Evm`): on the calldata of a statement and proof, the contract's recorded operation graph (F5), with the
  stored index root and `PCS_OPEN` modelled by an explicit definition (`pcsOpen`, `Evm/PcsOpen.lean`: the input read
  as the precompile reads it, then `PcsQuotient.opening`), accepts exactly when `PcsQuotient.verifyWith` accepts
  at π = Keccak-f[1600]. `Evm.evm_accepts_iff_exists` (`Evm/Calldata.lean`): over all calldata, the contract accepts
  exactly the calldata of a proof that `PcsQuotient.verify` accepts. So the contract runs the verifier the three
  theorems above are about, up to the tested links below; their probabilities are over a random permutation and
  do not formally transfer to the real Keccak-f[1600] ("Scope", below).

**What is trusted.**

- The Lean kernel and the three standard axioms.
- **The models**: Keccak-f[1600] is one random permutation, and Keccak-256 is its sponge; every hash of the protocol
  is over that one π (the chain, the Merkle trees, the openings' duplex, the circuit's commitment), and the relation
  is over the deployed Keccak-256. The prover's randomness is uniform. As deployed (`Randomness::derive`,
  `crates/quotient/src/protocol.rs`): a key is Keccak-256 of a tag, a 32-byte OS seed, the transcript's label (the
  circuit's commitment, the statement) and a digest of the witness's cells; the masks are the words of
  Keccak-256(tag ‖ key ‖ k), `k = 0, 1, 2`; the padding seed is Keccak-256(tag ‖ key), each table's seed is
  derived from it (`table_seed`), and each lane's padding is ChaCha12 keyed by Keccak-256(table seed ‖ lane).
  Deployed zero knowledge is therefore computational in that generator; completeness holds for every coins.
- **Scope**: the three theorems are about the Statement's `verifyWith` in the random-permutation model; the EVM
  theorem holds at the real Keccak-f[1600]. They do not formally compose: a probability over a random
  permutation does not transfer to a fixed hash.
- **mumbai's definitions** that the Statement reuses: Keccak-256 and Keccak-f[1600], the random-permutation model,
  the WHIR verifier `verifyStackedOpening` (mumbai tests it against leanVM's), its prover's pieces, the list decoder.
- **Tested, not proved**:
  - the Statement's definitions are the Rust (`Statement/PcsQuotientTest/Differential.lean`: reductions at `2^16`
    to `2^23` rows, whole proofs honest and tampered verified at `2^17` rows, and at `2^22` in the soundness
    review, the circuit commitments; the Rust's pruned Merkle paths expanded to the Statement's full ones);
  - the Statement's prover against the Rust's: the reduction's stream of nine scalars, at `2^17` rows on a small
    circuit only (the openings are not compared); for zero knowledge, the Lean skeleton, which `coreD` relates to
    the Statement's prover, makes the Rust prover's queries and proof byte for byte at `2^17` rows
    (`crates/quotient/tests/skel_trace.rs`);
  - the EVM bytecode computes the recorded graph (`crates/evm`'s parity tests); `FIELD_MUL` and `KECCAK256` are
    the Lean operations (`mulE` is proved to be `F192`'s product; the Rust's `F192` arithmetic by test vectors);
  - the `PCS_OPEN` mock (`crates/evm/src/machine.rs`) is the Rust `opening::verify`, which is
    `PcsQuotient.openingWith` (the differential test);
  - the extractor's cost table (read off its loops), and Gao's decoder recovering every word within its radius
    (`PcsQuotientTest/Decoder.lean`; the soundness proof does not need it).
- **Outside the theorems**: the `PCS_OPEN` aggregation layer, which must check all the claims of one call in one
  opening; the index root in the contract's storage (the theorems hold for whatever root is stored; a fixed owner
  may change it). The Rust prover is not trusted for soundness. Completeness and zero knowledge are about the
  Statement's prover; the deployed Rust prover is trusted for completeness (the tests above are its only link).
- **Not covered**: simulation-extractability; zero knowledge against a distinguisher that queries `π` before
  the proof, or for several proofs under one `π` (the theorem is single-proof); the Statement's own heuristic
  `simulator` (`ZeroKnowledge ζ`); `StatementBinds` (immediate, not proved in Lean).

**Building.** As [`WhirBridge/`](WhirBridge/README.md#building), against a built leanerVM `6175f1a0` at
`formal/leanervm` (on h1 a link to `/root/pcs-quotient-fv/leanervm`):

```sh
cd formal/EndToEnd
lake build Soundness E2ECompleteness Evm ZK        # the end theorems; #guard_msgs checks their axioms
lake env lean Review/E2ESoundness.lean             # the knowledge-soundness review
lake env lean Review/E2ECompletenessReview.lean    # the completeness review
python3 -I Review/E2ESoundnessNumbers.py           # ksBound in exact rationals
```

## The univariate verifier for leanVM 42422001: knowledge soundness

Four libraries of `EndToEnd/`: **`UniStatement`** (`UniStatement/`: the verifier, the extractor
`uniExtractor`, `UniKnowledgeSoundness`), **`UniSound`** (`UniSound/`: the PIOP's round-by-round soundness,
the code-level and last links, the Fiat–Shamir layer, the identity model `UniSound/Ids`), **`FlockSound`**
(`FlockSound/FlockSound`: sumcheck, univariate-skip, lincheck and ring-switch soundness over the cube) and
**`FlockSoundUni`** (`FlockSound/FlockSoundUni`: Flock's interface instance `flockSoundInstance`, the
reference deployment's numbers, the end theorems). The end theorem (`UniSound/UniSound/Closed.lean`):

```lean
theorem uniKnowledgeSoundness_closed (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61
```

For every deployment at the reference shape (`reference`: heights `18 18 18 18 17 18`, memory `2^21`, bytecode
`2^19`) with leanVM's program IV, and every program, the univariate verifier is knowledge sound for the explicit
extractor `uniExtractor`: an adversary of `Q` calls of `π` and `π⁻¹` makes it accept while the extractor finds no
stack satisfying leanVM 42422001's relation with probability at most `uniBound (2^32/|E|) Q`, which is `2^-61.41`
at `Q = 2^64` (`EndToEnd/Review/UniSoundnessNumbers.py`, exact rationals: the five openings' doom terms
`2^-61.68`, the seed tag's `2^-64`, the list term `2^-69.44`). `hD` and `hIv` say which deployment it is; nothing
else is assumed. Sorry-free, on `propext`, `Classical.choice`, `Quot.sound` (`#guard_msgs`), no `native_decide`.
The proof's route and what each layer contributes are in `UniSound/UniSound.lean`'s report.

**At `≥ 128` bits** (`UniSound/UniSound/Closed128.lean`), the same theorem with a tighter error, still with no
hypothesis:

```lean
theorem uniKnowledgeSoundness_closed128 (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundness D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
```

```
uniBound128 e Q = N (ε + 5N/2^256) + N (9952² e + 8N/2^256) + 2N²/2^256 + (2^81 + Q)²/2^508,
N = 2^33 + Q,  ε = εExact = 269 · 2^-137 = 2^-128.93
```

It is `2^-64.87` at `Q = 2^64`, or 128.87 bits as `Q / ε` (`EndToEnd/Review/UniSoundnessNumbers128.py`, exact
rationals). The terms are: the openings `2^-64.93`, the list term `2^-69.44`, and the chain's collisions, the seed's
pair and the openings' failure term at `2^-125`, `2^-127` and `2^-125.7`. Three changes produce it, all in the
proof; the Rust and the transcript are unchanged:

1. **The exact WHIR certificate** (`WhirBridge/WhirBridge/Exact.lean`). mumbai's ladder check is re-decided at
   the rational threshold `269 · 2^-137` instead of `2^-128`, by `decide +kernel` on the certificates' `Nat`
   numbers at `2^24 ..= 2^28` (`chkLevelsQ`, `chkQ_large`, `chkLevelsQ_sound`). The weakest group is
   `2^-128.949` (`2^26`, level 0's queries; the smallest numerator passing at `2^-137` is `266`). The opening
   chain then takes the per-group bound `ε` as a parameter (`stackedAtE` … `variantCertE`, `ours_sound_public_atE`,
   instance `ours_sound_public_exact`).
2. **The openings charged once** (`WhirBridge/WhirBridge/Union.lean`, `Compose/Compose/FirstDoom.lean`). Shapes
   with distinct prefixes form one Fiat–Shamir family (`union_sound`: `(QA + QV)(ε + 5(QA + QV)/2^256)` for all
   of them together). A fresh query extends at most one opening's transcript, because every IV hashes its
   layout's prefix and its claims. Doom is read at the run's end (`DoomF`, `Compose/Compose/Final128Defs.lean`);
   the union adversary runs the whole experiment and names the first doomed opening, whose verifier then replays
   from the run's cache (`run_replay_of_mem_support`). The theorem, **generic in the number and shapes of the
   openings**:

   ```lean
   theorem prEvent_doomF_le {F St M Pf : Type} [SampleableType F] (ε : ℝ≥0∞)
       (shs : List (ExactShape ε)) (hpre : (shs.map fun s => openingPrefix s.L s.R).Nodup)
       (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
       (hops : ∀ o ∈ ops, ∃ s ∈ shs, s.L = o.S.L ∧ s.R = o.S.R)
       (X : OracleComp KeccakCalls (PreK Pf F)) (QX : ℕ) (hX : IsTotalQueryBound X QX)
       (QV : ℕ) (hQV : ∀ s ∈ shs, s.QO ≤ QV) :
       Pr{let z ← (simulateQ randomOracle (expL view X ops)).run' ∅}[DoomF view ops z] ≤
         ((QX + (ops.map fun o => o.S.QO).sum + QV : ℕ) : ℝ≥0∞) *
           (ε + ((5 * (QX + (ops.map fun o => o.S.QO).sum + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256)
   ```

   `prEvent_doomF_le_large` instantiates it for any openings on plain layouts of `2^24 ..= 2^28` words
   (`largeShapes`, `εExact`, `QV = 9018`): the recursion's six openings are of this kind.
3. **The seed through a pair of answers** (`Compose/Compose/ListChainU128.lean`, `ListChainUDoom128.lean`,
   `SeedPair.lean`). The chain is separated from its label by the label's first 32 bytes (`NoPre`,
   `chain_uniqueU'`), not by the 16-byte tag. The univariate label `name ‖ iv ‖ input` starts with
   `name ‖ iv[0:16]`, where `iv` is the answer to the IV query (`hlab`, `UniSound.hlab_uni`). A step input that
   is the label therefore needs two answers, one being `name ‖` the other's first 16 bytes (`PairTr`). That has
   probability at most `Q²/2^256` (`prEvent_pairTr_le_sq`, by a budgeted potential on the cache), in place of
   the tag's `2^-128` per query. `knowledgeSoundness_listChainU_closed128` is the composed theorem with the
   tag-free bad events, its three terms explicit.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked as above
systemd-run --scope -p MemoryMax=10G lake build UniSound FlockSoundUni FlockSoundUni.PendingShape \
  FlockSoundUni.Good FlockSoundUni.Game
python3 -I Review/UniSoundnessNumbers.py      # uniBound in exact rationals
python3 -I Review/UniSoundnessNumbers128.py   # uniBound128 in exact rationals
```

## π1-rec3: the recursion's inner verifier (knowledge soundness and completeness)

π1-rec3 (`crates/leanvm_rec/SPEC-REC.md` §12 items 5, 7, 8, §1.4; `SPEC-POINTS.md`) is the univariate verifier with
`α = (c, c², c⁴, c⁸)`, Flock's zerocheck coordinates as squares of one challenge, Flock's lincheck terminal walked
(no `A0`, `B0` claims: three openings), and the batch two variables a round with narrow (160-bit) challenges. Its
statement is `UniStatement/UniStatement/RecSecurity.lean`'s (`UniKnowledgeSoundnessRec3`, `UniCompletenessRec3`, over
`Rec.lean`'s `verifyWithFs … .rec3 true`); the proofs are `UniSound/UniSound/Rec3*` (report: `UniSound/Rec3.lean`),
`FlockSound/FlockSound/{Kronecker, FlockSq}.lean`, `FlockSound/FlockSoundUni/{Rec3*, Walk*}.lean` and
`UniComplete/UniComplete/Rec3*`.

```lean
theorem UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3 (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundnessRec3 D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
theorem UniComplete.Rec3.uniCompletenessRec3_end_closed (D : Deployment) (hD : D.shape = reference)
    (hiv : D.programIv.length ≤ 2 ^ 16) : UniCompletenessRec3 D (uniProverRec3RP flockProve3H D) deltaRec3
```

`uniBound128 (2^35/|E|)` is `2^-64.494` at `Q = 2^64` (128.49 bits; `Review/UniRec3Numbers.py`): every round errs
with probability at most `2^35/|E|`, the narrow pairs' `8 · 2^32/|E|` the largest (the bus `16 N/|E|`, Flock's squares
`(2^22 − 1)/|E|`). `deltaRec3 < 2^-167` (about `2^-167.97`). No hypothesis beyond the deployment's: the walked
terminal is the matrices' product sum because the BLAKE2s circuit walk computes `A0 w`, `B0 w` (`rowValues_spec`,
`FlockSoundUni/Walk.lean`, by simulating Lv42's circuit builder), whence the walk's lemma and its converse
(`walkLemma_of_rows`, `walkLemmaConverse_of_rows`, `FlockSoundUni/WalkAlg.lean`).

```sh
cd formal/EndToEnd   # on h1
systemd-run --scope -p MemoryMax=10G lake build UniSound.Rec3 UniComplete.Rec3EndClosed
python3 -I Review/UniRec3Numbers.py           # uniBound3, uniBound128 at 2^35/|E|, the rounds' bits
```

## The recursive verifier: end theorems (`RecCompose/`)

> **Status (2026-11-05): the statements below are under repair.** An adversarial review of the statements
> ([`RecCompose/Review/STATEMENT_REVIEW.md`](RecCompose/Review/STATEMENT_REVIEW.md)) found that, as stated, the end
> theorems are vacuous or carry no bound, though their proofs are valid:
> - `Pi2Circuits` asks the compiler to accept π1-rec3's graph at IVs of every length, and it rejects long ones, so no
>   `Pi2Circuits` exists;
> - completeness uses a π1 prover whose Fiat–Shamir is over the random permutation rather than Keccak-f[1600].
>
> The fixes are in progress. Until they land, read the theorems below as proved implications, not as end results.

The recursive EVM verifier (`crates/leanvm_rec`) runs π2's verifier, then six `PCS_OPEN` calls. Its statements are
[`RecStatement`](RecStatement/README.md)'s. They come in two parts, because π2's circuit computes π1-rec3's Fiat–Shamir
with the real Keccak-f[1600] while π1-rec3's soundness is proved in the random-permutation model. The library
[`RecCompose/`](RecCompose/README.md) proves part 1 from π2's layers, bounds it in bits, and proves part 1 ⇒ part 2.
The end theorems are in `RecCompose/FsClosed.lean` (π2's Fiat–Shamir layer proved), `Final.lean` and `End.lean`:

```lean
theorem RecCompose.recKnowledgeSoundness_reduction (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (hchk : Pi2ViewChecked C) :
    RecKnowledgeSoundnessReduction D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
theorem RecCompose.recKnowledgeSoundness2_closed (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (hchk : Pi2ViewChecked C) :
    RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
theorem RecCompose.recKnowledgeSoundness_closed_fs (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (hchk : Pi2ViewChecked C) (ε1 εh : ℕ → ℝ≥0∞)
    (h1 : Pi1FsKeccak D ε1) (hh : Pi1HazardKeccak D εh) :
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ pi2Bound Q + ε1 Q + εh Q
theorem RecCompose.recCompleteness_end_fs (D : RecDeployment) (hD : D.Real) (P1 : Pi1Prover D) (P2 : Pi2Prover)
    (δ2 : ℝ≥0∞) (h2 : RecCompleteness2 D P1 P2 δ2) (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1)
    (hh : Pi1HazardKeccakHonest D P1 δh) : RecCompletenessWith D (composeProver D P1 P2) (δ1 + δh + δ2)
```

**The headline is `recKnowledgeSoundness_reduction`**, with no Fiat–Shamir premise. `RecKnowledgeSoundnessReduction D
pi2Bound` (`RecStatement/Reduction.lean`) says: for every adversary `A` of `Q` calls of `π`, `π⁻¹` against the recursive
verifier, the derived adversaries `pi1Adversary D A` and `hazardAdversary D A` make at most `Q` calls, and

```
Pr[contract accepts ∧ recExtractor fails] ≤ pi2Bound Q
    + Pr[pi1Adversary D A breaks π1-rec3, Fiat–Shamir over Keccak-f[1600]]   (pi1KeccakSoundnessExperiment)
    + Pr[hazardAdversary D A hits the merge hazard on an accepted stream]     (pi1HazardExperiment, Pi1HazardAccepted)
```

The derived adversaries are `def`s: `A`, its queries logged, then π2's explicit extractor `recExtractor2` (preimage
replay, `W`'s inversion, the fast path, unique and Guruswami–Sudan decoding at `2^24`, π1's graph's checks), which makes
no query. They run in `A`'s time plus the extractor's, a polynomial; Lean does not model time. The reader applies the
Fiat–Shamir heuristic for Keccak-f[1600] to these two adversaries. The merge hazard (`RecGraph.MergeHazard`) asks that
π1-rec3's run draw `t` (challenge 49), and `Pi1HazardAccepted` that π1-rec3's graph accept the stream, so the empty
stream is off it (`RecCompose/Review/StatementReview.lean`: `not_mergeHazard_empty`, `emptyAdversary_hazard_zero`).

The `_fs` forms are its corollaries under `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh`. **These two Props are false as stated**:
they quantify over every `OracleComp` adversary and count only its calls of `π`, so an adversary grinds π1's
Keccak-f[1600] challenges offline for free. They are kept as the Fiat–Shamir heuristic for adversaries of bounded
Keccak-f[1600] work, which Lean does not model.

They are `Final.lean`'s `recKnowledgeSoundness2_final`, `recKnowledgeSoundness_final_fs` (kept) with their hypothesis
`hfs : Pi2FsLayer D` discharged by `pi2FsLayer_real`, the circuit's facts `Fa` by `pi2Facts hD C hchk` and the ports' and
calls' meaning by `statementPortMeaning`, `zeroPortsMeaning`, `callWordsAgree`, `pi1CallsLayouts_of_real`. `recKnowledgeSoundness_closed` and `recCompleteness_end` state the `RecStatement` Props `RecKnowledgeSoundness D
pi2Bound ε1 εh` and `RecCompleteness D P1 P2 δ1 δh δ2` themselves. Their own premise `Pi1GraphIsVerifier` is proved
(`RecGraph.Pi1.pi1GraphIsVerifier`), so the `_fs` forms keep only `Pi1FsKeccak ε1` and `Pi1HazardKeccak εh` (false as
stated, above), or `Pi1CompletenessKeccak δ1` and `Pi1HazardKeccakHonest δh` (about the fixed honest prover, the
statement chosen before `π`: no grinding; motivated by `uniCompletenessRec3_end_closed` and `RecGraph.hazard_prob`). The
`_fs` soundness bound is `pi2Bound Q + ε1 Q + εh Q`.

**ε2 = `pi2Bound`** is `2^-64.93` at `Q = 2^64`, i.e. 128.93 bits as `Q / ε2` (`pi2Bound_le_bits`;
`EndToEnd/Review/RecSoundnessNumbers.py`, exact rationals). Its terms:
- π2's three openings, charged once: `2^-64.93`, at `269 · 2^-137` per fresh query.
- π2's rounds times their lists: `N · 2^-140.60 = 2^-76.60`. By `pi2_rounds_le`, the copy argument over `L_W` gives
  153.13 bits, the identity at `t` over `L_W L_Q` 140.60, and `W`'s fold at `ρ` 163.01.
- The collisions: `2^-125`.
- The seed's pair: `2^-127`.

**Proved** (sorry-free, on Lean's three axioms, checked with `#guard_msgs`):
- Part 1 from π2's layers: `recKnowledgeSoundness2_of_layers`, `recExtractFrom2_of_mem`.
- π2's extraction from the Fiat–Shamir layer and the tables' layer: `pi2Extraction_of_layers`. It uses `RecPiop.piop`
  per setup, `pi2_rounds_le`, `hbind` from `bind_elem`/`bind_root` on the compiler's checked ports, and
  `checks_claims_iff_post2`.
- The tables' layer itself: `pi2Tables` builds `W`'s polynomial, its fold values and the sibling trick, `h` and `q` in
  the novel basis, and the setup's `σ`, `κ`, with the four claims as their values.
- The circuit's corollary: `circuitBridge` from RecCircuit's `pi1rec3_end`; the root word `pi1RootWordOk`, after the
  root-word fix.
- The calldata's π1 openings are the contract's: `callsPure`.
- The couplings: `experimentsAgree`, `hazardCoupling`, `pi1Coupling`, `pi1OpeningsAgree`, `completenessAgree`,
  `completenessPi1Coupling`, by eager sampling and the logging lemmas.
- π1-rec3's run's shape: `pi1RunShape`, `pi1RunOpenings`.
- **The circuit's facts and the ports' and calls' meaning** (`lean-pi2-facts`): `Pi2Facts D C` is `pi2Facts hD C hchk`
  (`Facts.lean`), from the compiled circuits and the evaluated view check `Pi2ViewChecked C`. `SpecOf` of
  `Spec.of Data.circuit` against the compiled circuit (`specOf_data`, `FactsSpecOf.lean`): the pairs the slots of the
  blocks' non-forward roles, the groups `Spec.of`'s partition with their formulas the roles' values, the recursion's and
  the pairs' constants (SpecLink, the coset constants nonzero by the basis's independence), the zero coset, the walk and
  the terms from `Data` by kernel decision (`List.mergeSort` taken off sorted lists), the public terms the ports'
  fingerprints of `pubOfC`; validity by `validB_sound` (`Valid.lean`). `statementPortMeaning`, `zeroPortsMeaning`,
  `callWordsAgree` (`Meanings.lean`: π2's scalars on an accepted run, the root ports' limbs rebuilding the stream's 32
  bytes, the element ports' limbs the elements); `pi1CallsLayouts_of_real` (`Layouts.lean`). **Found**: `Pi2Facts`'
  field `pub_K` (every public limb in `K` at every scalar list) contradicted `SpecOf.term_value` (at every scalar list)
  at the four-limb ports, so `Pi2Facts` could not be built; it is now `pub_canon` (limbs in `K` with the public
  fingerprint at every `γ` are the public limbs), which is what the binding needs (`hbind_of`). `StatementPortMeaning`
  now asks for a run π2's verifier accepts (on a rejected stream π2's scalars are empty).
- **π2's Fiat–Shamir layer and openings**, `Pi2FsLayer D` at the real deployment: `pi2FsLayer_real` (`FsClosed.lean`),
  the port of UniSound's `Fs128`/`FsGame128`/`FsFinal128` to π2's transcript. The chain `pi2Spec` (the seed
  `name ‖ iv ‖ input`, the public data's 472 bytes before `W`'s root); the six `PCS_OPEN` calls as `WhirOp`s on
  `p2Shapes` (π1's `C1`, `C2` plain `2^27`, `F` plain `2^24`; `W` plain `2^24`, the setup `2^25`, `Q` `2^28`), charged
  once (`Compose.prEvent_doomF_le`); the seed's pair (`prEvent_pairTr_expL_le`); the bridges from
  `recSoundnessExperiment2` to the composed game: the setup (`pi2SetupBridge`: π1's three trees then π2's, its table a
  function of π1's roots), the IV (four Keccak-256 calls, moved into the adversary), the verifier (`pi2VerifierBridge`
  on the walk `pi2Walk`), the extractor's reading (`pi2ExtractBridge`). Two generalisations of the framework were
  needed (`Compose.knowledgeSoundness_listChainU_closed128S`, `ListChainUDoom128S.lean`): π2's setup table and π2's
  PIOP are functions of the setup's roots (π1's contract IV), which the setup computes over `π`, so the setup's
  opening's stack and the protocol are read off the setup's output.

Part 1 ⇒ part 2 has no hypothesis left.

**π2's completeness** (`lean-pi2-complete`; `Pi2CallsOpen.lean`, `Pi2ProbStaged.lean`):

```lean
theorem RecCompose.Pi2O.recCompleteness2_pi2_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hhash : Pi2HashBeforeAlpha D C (pi2Facts hD C hchk) P1k) (htf : Pi2TFresh D C (pi2Facts hD C hchk) P1k εt)
    (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel))
theorem RecCompose.Pi2G.delta2_pi2_le {N : ℕ} {εt : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ht : εt ≤ (2 : ℝ≥0∞)⁻¹ ^ 200) :
    delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164
```

and `recCompleteness_pi2_closed_fs` (the same inputs, `Pi1CompletenessKeccak D P1 δ1`, `Pi1HazardKeccakHonest D P1 δh`):
`RecCompletenessWith D (composeProver D P1 (pi2Prover …)) (δ1 + δh + delta2 …)`.

* **π2's honest prover** (`Pi2Prover.lean`: `pi2ProveStreamWith`, `pi2ProveWith`, `prover.rs` transcribed over any
  Keccak-256 and permutation; `pi2Prover`, `Pi2CompleteEnd.lean`: the setup, the IVs, a witness by `Classical.choose`,
  π1's three openings then π2's). **Differential test** (`RecComposeTest/Pi2Prover.lean`, vectors from
  `crates/leanvm_rec/tests/lean_pi2_prover.rs`, `spec::example()` padded to `2^9`, `2^10` positions): the setup's,
  `W`'s and `Q`'s roots and the stream byte for byte, 2/2.
* **The algebra** (`Pi2Honest*.lean`, `pi2_honest`): a satisfying witness's honest stacks satisfy π2's four claims and
  `all ≠ 0` off `BadCopy` (a copy denominator zero: at most `2N·|E|²` triples, `card_badCopy_le`) and `BadT`
  (`t ∈ V_{m+2}` or `c_h + c_q = 0` at `t`: at most `8N` values, `card_badT_le`), from `Σ_V h = T` (`sum_hValues`)
  and `q = num /ₘ Z_V` of degree below `4N`.
* **The core** (`pi2_accepts`): off those events the contract accepts the honest proof, at any Keccak-256 and
  permutation: the verifier reads the prover's stream back (`runWith_honest`), WHIR accepts the honest openings at
  π2's three layouts (`pi2Open_honest`, `Pi2Whir.lean`), π1's three calls are those the graph accepted
  (`pi2Pi1Openings`, from `circuitBridge`).
* **The probability**: the staged random-oracle bound (`Pi2Prob.lean`, `prEvent_staged3_triple_le`, `rpm_le_rom`) and
  the grinding (`rejectGood_pi2`, ProbGrind's potential). **δ2** `≤ 2^-164` (about `2^-164.7`;
  `RecCompose/Review/Pi2Delta2.py`): the copy argument `(2^25 + 36)/2^192 = 2^-167.0`, `t` `2^27/2^192 = 2^-165`, `α`'s
  repetition `2^-256`, `εt ≤ 2^-200`, the grinding `≤ 2^-300` (about `2^-319`), `rpmError (2^50) = 2^-408`.
* **Found**: the F-only contract cannot carry the grinding argument (it answers Keccak-256 and the permutation
  independently), so π2's verifier, contract, IV, setup and graph verifier are restated with Keccak-256 an explicit call
  (`Pi2CompleteH.lean`, equal at the sponge); the experiment is an inequality, not an equality (P1 returning `none`).

**Closed** (`lean-pi2-run`; `Pi2Closed.lean`): P1 is π1-rec3's honest prover (`pi1Rec3Prover D`, its two-call
program `p1k D`, no more a parameter), and every provable input of `recCompleteness2_pi2_closed` is proved:

```lean
theorem RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_final {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) (p1k D) εα) :
    RecCompleteness2 D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel))
theorem RecCompose.Pi2Sim.delta2_rec3_le {εα : ℝ≥0∞} (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 201) :
    delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164
```

and `recCompleteness_pi2_rec3_final_fs` (with `Pi1CompletenessKeccak D (pi1Rec3Prover D) δ1`,
`Pi1HazardKeccakHonest D (pi1Rec3Prover D) δh`): `RecCompletenessWith D (composeProver D (pi1Rec3Prover D) (pi2Prover …))
(δ1 + δh + delta2' …)`. How each input went:

* `Pi2WitnessComplete`: **proved** (`Pi2W.pi2WitnessComplete`, `RecCircuit/Complete.lean`): the honest witness in value
  order, from four completeness checks added to the compiler's checker (`completeSlots`, `completeValues`,
  `completeGiven`, `completeCover`; the real graph passes them at both IVs, `rec-view-check`, now about 20 minutes).
* `Pi2ExperimentLe`: **proved** (`Pi2SimExp.pi2ExperimentLe_p1k`): π2's code commutes with simulation
  (`Pi2SimMorph`), the eager model per permutation (`perm_kc`), the staged run at pure functions (`Pi2SimAt`).
* `Pi2RunAt`: **not provable as stated** (on a π1 proof with no honest witness the staged run hashes `fixLen 536`'s
  zeros where the prover hashes its `64`-byte input), and **not needed**: `Pi2SimCore.rejectGood_pi2_good` uses the
  staged run's verdict and priors where the graph accepts (`stagedAt_good`).
* `Pi2RunDuplex`, `Pi2RunCost`: **proved** (`pi2RunDuplex_p1k`; `pi2RunCost_p1k`, `N = pi2RunN ≈ 2^47.9 ≤ 2^50`).
* `Pi2HashBeforeAlpha`: **false** at π1-rec3's prover (it hashes `s₂ = H(s₁)`, 32 bytes, before `α`): replaced by
  `Pi2AlphaFresh εα` (`Pi2Chain`: `Holds2`, `α`'s chain with stage A's 32-byte inputs counted, `(2N + 1)/2^256`).
* `Pi2TFresh`: **proved** from `Pi2RunCost` and `Pi2AlphaFresh` (`pi2TFresh_of`, `tFreshBound2 ≤ 2^-200`; `Q`'s leaves
  depend on `s₃`, so the argument counts 64-byte queries beginning with an answer, `Pi2TFresh.lean`).
* `Pi2Pi1Openings`: proved (`pi2Pi1Openings`).

**The named inputs left**:

| Input | What | Who closes it |
|---|---|---|
| `Pi2Circuits D`, `hroots`, `GraphsAgree` | the Lean compiler (with its completeness checks) accepts π1-rec3's graph at every π1 IV; `recordedGraph pi1Rec3 = Emitted.graph` | **checked by evaluation**, not by the kernel (`rec-circuit-emitted`, `RecGraphTest/Pi1Check.lean`) |
| `Pi2ViewChecked C` | at every π1 IV the compiled circuit passes `viewCheck` | **checked by evaluation** (`rec-view-check`) |
| `Pi2AlphaFresh D C Fa (p1k D) εα` | `α`'s 536-byte input is not hashed before its query but with probability `εα` (`εα ≤ 2^-201` for `2^-164`) | **proved where the graph accepts** (`lean-pi2-alpha`, below); not needed |
| `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest` (end to end only) | π1-rec3 at Keccak-f[1600] | the Fiat–Shamir heuristic (π1-rec3's random-permutation theorems) |

The earlier form (`recCompleteness2_pi2_closed`, any `P1`, `P1k`, the named staged facts) is kept.

**`α`'s freshness** (`lean-pi2-alpha`; `RecCompose/Pi2Alpha*.lean`, see [`RecCompose/README.md`](RecCompose/README.md)):
the only inputs left are the run-checked ones (and, end to end, the Fiat–Shamir premises):

```lean
theorem RecCompose.Pi2Alpha.recCompleteness2_pi2_rec3_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) :
    RecCompleteness2 D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel))
theorem RecCompose.Pi2Alpha.delta2_alpha_le :
    delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164
theorem RecCompose.Pi2Alpha.recCompleteness_pi2_rec3_closed_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D (pi1Rec3Prover D) δ1)
    (hh : Pi1HazardKeccakHonest D (pi1Rec3Prover D) δh) :
    RecCompletenessWith D (composeProver D (pi1Rec3Prover D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel))
```

* **`εα = alphaBound = 4 · (2 · setupR + 2^47 + 3 · gOpen + 4) / 2^256 ≈ 2^-207.0`** (`alphaBound_le`: `≤ 2^-204`);
  `εt = tFreshBound2 pi2RunN εα ≤ 2^-200`; **δ2 ≤ 2^-164** (about `2^-164.7`, as before: the copy argument's and `t`'s
  terms dominate).
* **Found**: `Pi2AlphaFresh` as stated (every outcome of stage A) is not what the proof can give: where π1-rec3's graph
  does not accept (π1's prover returning none, or public values not matching the reads), `pi2Staged`'s `α` input is
  `fixLen`'s `536` zeros, and nothing shows π1-rec3's prover (which may hash `536`-byte inputs) does not hash those.
  Those outcomes are rejected, so the staged bounds ask `α`'s and `t`'s freshness only where the graph accepted
  (`Pi2AlphaG.Holds3`); there it is proved.
* **How**: π2's IV starts by hashing `σ`'s `4 · 2^24 = 2^26` bytes, longer than every Keccak-256 input before it
  (`Pi2AlphaLen`: π1-rec3's prover, its WHIR openings, the graph's openings, the setup twice), so its answer is uniform;
  each later hash (the circuit digest, the IV, the seed, `α`'s input) holds the previous answer at a fixed offset, so
  it is fresh but with probability `(K + 4) / 2^256`, `K ≤ 2^47.01` the inputs hashed before `σ` (`Pi2AlphaChain`).
* `Pi2WitnessComplete` is no more an argument (proved, `Pi2W.pi2WitnessComplete`); the `Pi2Sim` forms with `hal` are
  kept.

```sh
cd formal/EndToEnd   # on h1
systemd-run --scope -p MemoryMax=10G lake build RecCompose
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check   # Pi2ViewChecked, evaluated
python3 -I Review/RecSoundnessNumbers.py     # pi2Bound in exact rationals
```

## Layers

| | What | Source | Status |
|---|---|---|---|
| F0 | The circuit: a Lean definition of the deployed wiring (`quotient::circuit::membership`), proof that a satisfying assignment is its computation and that this computation is Keccak-256 membership; the constants (Cantor basis, `τ`, `b`, the bit weights) as computable definitions whose hypotheses are checked | new (found missing by the Lean review: `Instance.soundness` holds for every wiring, so for a degenerate one it says nothing) | **done** (F0a for a circuit given as a parameter: `CircuitLayout.lean`, `Pinning.lean`, `Statement.lean`): `Instance.soundness_circuit`: for an instance whose wiring lays a loop-free χ circuit `C` (`Laid`: input cells on the cycle of what they read, word 5's 128 bits on the zero's cycle, word 4's bit 0 the one's anchor and its other bits on the zero's) and whose weights are `coordinate_weight`'s (`bit_weight(j)` = `x^j`, `Y x^(j-64)`, with `x ≠ 1`, `Y ≠ 1`), an accepted proof of `statementWords x Y y root` (`statement::halves` of `y`, `root`, then `(1, 0, 0, 0)`) holds `C`'s computation on some input bits with public words 0–3 the halves of `(y, root)`, except with probability `(Q + 3) / 2^128`; `soundness_circuit_bits`: with the 128 bit weights independent over `GF(2)`, its public bits are the bytes' bits as `circuit::public_words` reads them. Derived from `Instance.soundness` and `cells_determined` (bridged by `Instance.cells_determined`; zero then one pinned by `zero_pinned`, `one_pinned`); the cone of both reaches the circuit argument. Not vacuous: `wiringOf C` meets `Laid` (`laid_wiringOf`) and the cells of every computation of `C` satisfy the relation on it (`relation_wiringOf`, `relation_statementWords`). **The deployed circuit** (F0b, `Circuit/`, `QuotientSecurity/Deployed.lean`; F0c, `Field/`, `QuotientSecurity/DeployedConcrete.lean`): `soundness_membership_deployed`: an accepted proof's cells are a computation of the deployed `2^22`-row circuit whose input bits give `x` and a path with `y = H(x ‖ 0x11..)` and the path from `H(x ‖ 0x22..)` ending at `root`, except with `(Q + 3) / 2^128`; Keccak-256 checked against mumbai's spec (`keccak256_bits`); `soundness_membership_deployed_concrete`: the same over `primitives`' `F192` (CompPoly's `BF64.Ext3`) with `x`, `Y`, the bit and coordinate weights and `statement::halves` transcribed and proved equal to the theorem's, no field hypothesis left. Sorry-free, on `propext`, `Classical.choice`, `Quot.sound`, no `native_decide`. σ equals the Rust's by a hash of both dumps (and the Statement's circuit is F0b's, `EndToEnd/Bridge/Circuit.lean`'s `membership_eq`) |
| F1 | The reduction (five field elements → four claims): round-by-round knowledge soundness, completeness, honest-verifier ZK, Fiat–Shamir in the ROM, **ideal commitments** | ported from leanVM `formal/quotient` and adapted (below): `2^22` rows, the χ gate on bits (degree 2), degree bounds, the circuit argument (bits, no carries) | done for the reduction: `lake build` green, sorry-free, end theorems on `propext`, `Classical.choice`, `Quot.sound` (761 declarations swept, `formal/Review/Axioms.lean`). Its zero knowledge is for ideal *hiding* commitments only: the deployed roots and openings are F3's (and the masks of the five values have no slack, so nothing else may reveal an evaluation of a witness polynomial). `Instance.soundness`, `zero_knowledge`, `completeness` hold for every wiring; `soundness_circuit` (F0) is for a wiring that lays a χ circuit |
| F2 | WHIR openings list-sound for our claims (some member of the root's level-0 list satisfies all claims of one opening) | leanerVM `mumbai`, `lean_vm` `Whir/Sound`: `stackedSpec` holds for any multiaffine weights; ours are | **done for the deployed openings** in [`WhirBridge/`](WhirBridge/README.md) (sorry-free, `propext`, `Classical.choice`, `Quot.sound`; 589 declarations swept, no `native_decide`): `ours_sound`, Fiat–Shamir soundness in the two-oracle ROM of `opening::verify` itself (version-2 transcript: IV `keccak256(prefix ‖ claims)`, zero public digest, root read from the proof and checked; no claim rejected) for the witness and quotient (hidden, **the redesigned layouts for condition (R)**: overflow lane 32, random lanes 33..39, the gadget) and wiring (public) layouts at every `2^17..2^22` rows: an adversary of `QA` queries outputting a root, claims and a proof makes it accept while every candidate **table** (`Table::read`) of the root's extracted word violates a claim with probability ≤ `(QA + 10122)(2^-128 + 5(QA + 10122)/2^256)` ≤ `2^-63` for `QA ≤ 2^64`. The Lean `Layout` has every field of the Rust's, both branches of the weight closure transcribed with the gadget's term (the gadget one more stack claim of value zero, batched with `λ^m`; every weight multiaffine; `holds_iff` for the hidden layouts' claims, `gadget_holds_iff`: the gadget says the pattern lanes' `β`-combination at its entries is zero; the event, on the claims only, implies mumbai's doom, which counts the gadget); `Test/Check.lean` accepts the Rust's deployed witness and quotient openings, rejects them without the gadget's term, and recomputes the 18 prefixes. Level-0 candidates per root exported: ≤ 9,952 (wiring), 7,908 (witness), 3,564 (quotient). **Extended to public layouts of `2^24..2^28` words for a leanVM PIOP** ([`WhirBridge/Large*.lean`](WhirBridge/README.md#public-layouts-at-224--228-a-univariate-leanvm-piop); the sweep now 676 declarations): `ours_sound_public` for every `Layout::new` layout of `(table, height)` chunks that passes its assertions (`Layout.new_valid`, one generic proof), the ladders, `L₀` = 9,952 / 7,908 / 6,296 / 4,473 / 3,564 and the verifier's `QO` = 7,183 .. 9,018 at `log_n` = 24 .. 28 by kernel decision, the union over one, two, three roots' lists (`L₁L₂ < 2^27`). Not covered here, and done in F4: the random-permutation model, extraction from the adversary's queries alone, the composition with the reduction. Not covered: pruned paths, the Rust being the Lean mirror (test evidence) |
| F3 | Hiding openings: the padded tables (base field `K = GF(2^64)`, challenges in `E = GF(2^192)`, first fold 6); then (F3b) the roots, Merkle siblings, nonces and Fiat–Shamir in the random-oracle and random-permutation models, with an explicit simulator | new (the ZK-WHIR note, adapted to `K ⊂ E`; `membership-zk.md` of leanVM's branch for the sibling argument) | Lean: `formal/QuotientSecurity/Hiding/` (sorry-free): for two tables with the same claims, the views (lane rounds, the folded table, every opened row) have the same distribution on the good challenges (`hidden_view_evalDistEq`), and differ by at most Pr[(R) fails] + ~2^-127 on any event (`hidden_prEvent_le_bound`; (S) bounded by `card_not_span_four_le`); unopened rows keep ≥ 2,368 / 3,840 bits (`unopened_row_le`). For that first layout, condition (R) (`RoundsReached`) is a hypothesis (estimated ≈ 2^-53 in `HIDING.md`). **The deployed layouts, with the gadget** (`GadgetTheorem.lean`, `Deployed.lean`): (S) and (R) proven, not assumed, at every challenge `(μ, φ)` with `μ ≠ 0`, no coordinate of `φ` in `{0, 1}` and at most one of `φ₀, φ₁, φ₂` in `K` (`Solve.span_cube_erase`, `GadgetLayout.roundsReached`), (Q) and `WeightsFit` proven for the deployed weights, and **`deployed_prEvent_le`**: for the witness and quotient tables at `2^17 .. 2^22` rows, two tables with the same claims give experiments within `1/\|E\| + (12·\|E\| + 3·\|K\|²)/\|E\|² < 2^-188` on any event. The view is the linear part only: the level-0 roots (in calldata), the Merkle siblings, the grinding nonces and Fiat–Shamir are F3b's (below; `formal/Review/HidingReview.lean`'s `stack_ne_of_entry_ne`: hiding of the roots rests on that random-oracle step). Per table, interactive, honest verifier. The padding is uniform here; the prover's comes from a CSPRNG (ChaCha12 keyed by a Keccak-256 KDF of an OS seed), so as deployed the hiding is computational in that generator |
| F4 | Composition: commitments as Merkle trees over Keccak-256 in the random-permutation model, the reduction's Keccak-256 chain, the openings' duplex; extraction from the adversary's transcript (`mumbai`'s `Statement/Extractor.lean` decodes WHIR words by Guruswami–Sudan) | `mumbai` `common` (sponge indifferentiability, ROM→RPM), `lean_vm` extraction | **the chain (F4a) done** in [`QuotientRpm/`](#the-keccak-256-chain-f4a) (sorry-free, `propext`, `Classical.choice`, `Quot.sound`): the reduction with `transcript.rs`'s chain, byte for byte, in the ROM and in leanerVM's RPM, ideal commitments (a root is Keccak-256 of an injective encoding of the message). **Real commitments composed with the openings (F4b)** in [`Compose/`](Compose/README.md) (sorry-free, same three axioms): the chain absorbs the proof's roots, every round union-bounded over the roots' candidate lists (`L₁` for `(α, β, γ)`, `L₁ L₂` for `t`, `ρ`; `≤ 2^-128` per query for lists up to `2^18`, `2^-138` with the certified `7908` / `3564`), the Merkle extraction from the transcript (computable, stable; mumbai's `extract` without collisions, `wordOfMerkle_eq_extract`), in the ROM and in mumbai's two-oracle model. The general statements (`knowledgeSoundness_merkle`, `_kc`) take the openings' doomed events as hypotheses: events in F2's oracle model, **not** literally F2's (any openings' verifier; `merkleWord` and a decoder for `extract`, `Candidates`, `Layout.tableEval`; F1's polynomial identities for `reduce`'s multilinear claims; the final transcript for the cache at the end of the opening), and their extractor reads every Keccak-256 query of the run. **The deployed composition** (`Deployed.lean`, `DeployedWired.lean`, `WiringSetup.lean`; **`knowledgeSoundness_wired_setup(_bits)`**): the setup computes the Merkle tree of the wiring stack's word with the oracle before the adversary runs (`stackSetup`, `2^20` queries at `2^22` rows); its root is in the chain's label and is the wiring opening's root; the chain, then `opening::verify` three times (F2's `ourVerifier`); the computable extractor reads the adversary's queries only (`adversaryExtractor`, decoder `tableCode`: mumbai's Guruswami–Sudan `decodeStacks`); **all three openings' terms are F2's `ours_sound`** (`prEvent_EWw_le`, `prEvent_Eσw_le`, `prEvent_EQw_le`; `QO = 10122` derived from F2's `variantQueries_eq`), the wiring term discharged: the setup's queries make the root's extracted word the stack's word (`extract_wiringSetup`), whose only candidate at the level-0 Johnson threshold is the stack (`candidates_honest`; rate `1/2`, Johnson radius ≈ 0.293 < distance 1/2): `openingBound (QS + Q + 6) + openingBound (QS + Q + 6 + QO) + openingBound (QS + Q + 6 + 2 QO) + N (2^-128 + 5 N / 2^256)`, `N = QS + Q + 6 + 3 QO` (about `2^-62` for `Q ≤ 2^64`). **The claim maps** `reduce`'s, `WitnessClaims`, `QuotientClaims`, `WiringClaims` discharged (`Compose/Claims.lean`: `knowledgeSoundness_deployed_rust`). **In the random-permutation model** (`Compose/Rpm.lean`: `knowledgeSoundness_wired_setup_rpm_bits`, `+ (QSπ + Q + 7 + 3 QOπ)² / 2^508`; at the deployed claim maps `Soundness.knowledgeSoundness_rust_rpm`, `EndToEnd/Soundness/RpmV.lean`), which the end-to-end theorem uses. Nothing left |
| F5 | The implementation is the model: the EVM contract and the Rust verifier are generated from one recorded operation graph (`crates/evm/src/record.rs`); emit that graph as a Lean term too and prove it equals the model's verifier | new | **done for the graph** in [`Implementation/`](Implementation.lean) (sorry-free, no `native_decide`; end theorems on `propext`, `Classical.choice`, `Quot.sound`): `Implementation/Graph.lean` is the deployed contract's recorded graph (631 nodes, 122 output words, 1 nonzero check), written by `crates/evm/src/lean.rs` (`graph_lean_is_current` fails when stale); `Interp.lean` interprets it on calldata as `codegen.rs` compiles each node (EVM words, `XOR`, `FIELD_MUL` = `mulE`, Keccak-256 of `MSTORE`d words, `CALLDATALOAD` and shifts), for any hash. Proved, in any field with `F192`'s limbs (`IsF192`: `XOR` is `+`, `mulE` is `*`; the Frobenius node is then `x^(2^64)`, `frobOK`): a Lean transcription of `reduce` finds every node it asks for and gives exactly the contract's words and nonzero check (`Program.reduceIds_eq`, kernel evaluation); those nodes hold `reduce`'s formulas (per-node semantics, the norm inversion is `x⁻¹`), which are the claims and denominator of `claims_iff_accepts_ofCantor` on `membershipParams` with the graph's constants checked by computation (`consts`: Cantor basis, `b`, `tau`, extension); on `calldataOf` the leaves are `Wire.verifyWith`'s Keccak-256 chain byte for byte (`leafVals_calldataOf`); so `graph_reaches_iff` (the contract reaches its `PCS_OPEN` calls iff the denominators' product is nonzero), `graph_words` (it hands them the root words of `r₁`, the index root, `r₂`, the layout ids and the model's four claims) and **`graph_is_verifier`**: with those claims true of tables whose polynomials are a model proof's messages, the contract accepts iff no `1 + w_k(t)` vanishes and `Wire.verifyWith` accepts, for the deployed `Wire` (`wire`: index root an input, `statement::halves`, `F192` limbs, coefficient encodings of the ideal commitments). **On the concrete field** (`Implementation/Field192.lean`): `isF192_primitives` discharges `IsF192` for F0c's `Primitives.F192` (CompPoly's `BF64.Ext3`) with its Rust limbs `(c0, c1, c2)` (`limbsEquiv`): `mulE` is its product, the core being `mul64_eq` (Rust's shift-fold `reduce` of the carry-less product is CompPoly's `reduce (carryLessMul a b)` for all 64-bit `a`, `b`: both are the remainder of the same polynomial modulo `x^64 + x^4 + x^3 + x + 1`, `clmul_eq_carryLessMul`, `reduce64_eq_reduce`; a structural proof, no `bv_decide`); so **`graph_is_verifier_F192`**, `graph_words_F192`, `graph_reaches_iff_F192` hold with no field hypothesis. **Tested, not proved**: bytecode = graph (`crates/evm` parity tests); the interpreter = the Rust verifier (`Implementation/Diff.lean`, 3,000 random calldata, 0 disagreements); the Rust's `F192` arithmetic = `mulE` (`mulE` transcribes its software `clmul` and `reduce`; the transcription and the Karatsuba and PMULL paths are checked by those tests and `Field/Test.lean`'s vectors); the `PCS_OPEN` mock is `opening::verify`, which is `PcsQuotient.openingWith` (the Statement's differential test). **To the Statement's verifier**: `EndToEnd/Evm` (`evm_accepts_iff_verifyWith`, `evm_accepts_iff_exists`) |

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
explicit definition in the statement (`sim` is compiled for any compiled view simulator, `Check.lean` runs it;
the deployed simulator is compiled in `zeroKnowledge_closed_computable`). The prover's randomness is uniform (the deployed
masks and padding come from ChaCha12 keyed by a Keccak KDF of a 32-byte OS seed: the deployed statement is
computational in that PRG).

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
- **`FSFresh`, proved** (`Deployed/Fresh/`, `Deployed/Fresh.lean`; `fsFresh_deployed`): the honest prover's
  Fiat–Shamir inputs are fresh but with probability
  `εFS = Q · 6 (|c₀| + Q) / 2^256 + 2 (|c₀| + Q) · 3 εc + |c₀| δ₀` (`Q = skelBound`), `≤ 2^-54` for
  `|c₀| ≤ 2^127` (`fsFresh_deployed_bits`), for a prover `P` whose secret rows are Keccak-256 inputs longer than
  192 bytes, whose witness table needs no challenge and has a first row of min-entropy `δ₀` (`2^-2368`), whose
  openings' messages begin, after 5, 128 and 242 challenges, with claims whose first 24 bytes are a window `cw j`
  of the fifth (`ρ`) or fourth (`t`) chain state of min-entropy `εc` (`2^-191`: `ρ`'s limbs, `t / (1 + t)`), and
  with `242 ≤ P.n`. The run is tracked with a flag *bad*, raised when a fresh answer lands where it should not
  (its digest the start of an input held, or the root words at its end, or another answer's digest; its
  capacity an input's or zero; its seed state an input; at the fourth and fifth states, a claims window of an
  input): `Pr[bad]` is the first two terms (`Fresh/Prob.lean`, a potential-weighted bad-event budget). Off
  *bad*, Hoare triples over the whole skeleton (`Fresh/Core.lean` … `Fresh/Skel.lean`, `trip_skel`) show every
  Fiat–Shamir input fresh: the chain's first input (label state, which may be public, then the witness root)
  through the root, fresh because the first leaf is (`|c₀| δ₀`); each later chain input through the previous
  state; each opening's seed through the claims' window (the IV hashes public data, so its freshness is the
  claims' challenge: the inherent `|c₀| · 2^-191`); every draw through the duplex's fresh capacity, grinding
  included (tries differ in the nonce lane; an exhausted grind leaves a fresh draw input). The inherent
  `|c₀| · 2^-191` is identically `0` in the end theorem: `c₀ = []` there (`fsFresh_setup_deployed_bits`, from an
  empty cache before the proof; `epsFS`'s first argument holds only the setup's `2^19` public rows); a pre-proof
  phase for the distinguisher is planned, which will make it nonzero. **`zk_deployed_fs`**,
  **`zk_deployed_fs_bits`**: `2^-54 + εhv + 2^-2200`; with the joint model `zk_deployed_joint_fs`:
  `2^-54 + 2^-165 + 2^-2200`, and in the random-permutation model `zk_rpm_deployed_joint_fs`,
  `zk_rpm_deployed_joint_fs'` (`QuotientZk/FreshJoint.lean`; the latter also without `hrow`, `hduplex`):
  `2^-54 + 2^-165 + 2^-2200 + Q² / 2^508`. **These three joint-model theorems are superseded** (as are
  `zk_deployed_joint`, `jointHVZK_of_link`, `joint_hzk`, `zk_rpm_deployed_joint(')`): they ask the honest
  tables' claims (`hT₁`, `hT₂`) at every mask with no `ClaimsND`, which the honest tables do not meet at
  degenerate challenges and masks; the deployed result goes through `jointHVZKε_of_linkV` (below).
- **The joint model instantiated** (`QuotientZk/Instance/`). The deployed quotient claim's point reads the
  five values (`vCells(t)/claimDen(α, β, t, a, s)`), so `Joint.lean`'s openings (weights from the challenges
  alone) cannot carry it: `JointV.lean` is the same chain over `ChV = Chal × Vals` (`modelV`, `jointSimV`,
  `LinkV`, `factors_singleV`, `factors_pairV`; its `joint_hzkV`, `jointHVZK_of_linkV`,
  `zk_rpm_deployed_jointV_fs'`, same bound, are superseded, as above). For the deployed prover: the schedule
  (`394` steps: `5 + 123 + 114 + 152` draws, `openDraws`) and the challenges of the oracle's answers (`chOf`, an
  equivalence with what no challenge reads, so **`hch`** `chOf_uniform`; causality `chOf_take_*`,
  `Challenges.lean`); the two openings at `2^22` rows (`openW`, `openQ`: `witness_layout(22)`,
  `quotient_layout(22)` with the gadget `1, Y, Y²`, the verifier's claims `modelWitness`, `modelQuotient`,
  `modelSum`, the novel basis at the opened positions: level 0's queries then fillers, `224`/`225`) and their
  **`Conditions`** (`Openings.lean`); the prover `Pb` (the claims' bytes at the openings' starts, then any
  public renderer `R` of the part of the joint view drawn for by then; leaves the 64-word images of the stacks'
  rows) and **`LinkV`** (`link`: the view from the joint view by causality, injective leaves, the free vectors
  from the novel basis's degrees, `Prover.lean`); **`FSFresh`'s conditions** (`Fresh.lean`: `hcw` at `2^-191`,
  `hrow₀` at `2^-2368`, the three `ClaimsAt`, long rows, `hcK`, `hn`); the simulator's tables `simTW`, `simTQ`
  built by a computable Gaussian elimination (`Instance/Builder.lean`: the claimed values met whenever some
  table meets them, `claims_simTW`, `claims_simTQ`; the scan stops at full rank, at most every entry).
  `zk_rpm_deployed_instance` (`Instance/Main.lean`) assembles these with `zk_rpm_deployed_jointV_fs'`, and is
  **superseded**: its `hTW`, `hTQ` ask the honest tables' claims at every mask, which they do not meet (where
  `claimScale 2 23 t = 0` the verifier's witness value `valsW` is `0`, `EndToEnd/Review/E2EZkNondeg.lean`). For the
  end statement, `deployedJointData`, `deployedJointData_valid` (`EndToEnd/ZK/Joint.lean`) take the same pieces
  with `hTW`, `hTQ` under `ClaimsND` only: their hypotheses are the field, F1's, and **the honest tables meeting the
  verifier's claims off the degenerate challenges and masks**, all discharged for the deployed instance in
  `EndToEnd/ZK/Final.lean` (`hTWD`, `hTQD`, `ZK/FactsClaims.lean`, from `Completeness/`'s tables); every renderer
  `R` (WHIR's honest prover is one) and every pair of such tables is covered. The simulator's tables are computed
  (`Test/Builder.lean` runs the builder on `F192`).
- **The degenerate challenges and masks** (`QuotientZk/Instance/Nondeg.lean`), the chain the end theorem uses:
  the honest tables meet the verifier's claims only under `ClaimsND` (the claims' scales `1 + w_k(t)`, `k < 26`,
  nonzero, the row `t^4 + t` outside `K`, the copy denominator `claimDen · vRows(t)` nonzero at the masks' five
  values); **`joint_hzkV_nd`**, **`jointHVZKε_of_linkV`**: `joint_hzkV` and `jointHVZK_of_linkV` with `hT₁`,
  `hT₂` required only there, at `goodT` challenges (`prob_not_goodT_bits`: `2^-165 + 2^-125`), the masks
  failing `ClaimsND` with probability at most `2/|E|` (`prob_not_claimsND_le`), the views then within it
  (`view_vclose`); with `QuotientZk.DRpm.zk_rpm_skel_approx` (`RpmDeployed.lean`, from `zk_rom_approx`):
  `epsHV = 2^-165 + 2^-125 + 2/2^192` in the end theorem.
- **What stays a hypothesis here**: the honest tables' claims and F1's facts on the witness (discharged end to
  end, above); that `skel` and `Pb` are the Rust prover (transcribed; `skel` equal by test, not by proof: see the
  next item; the Statement's prover against the skeleton is `ProverBridge`, "Zero knowledge end to end"). The
  lift to leanerVM's random-permutation model is separate (`QuotientZk/Rpm*.lean`, `RpmJoint.lean`,
  `RpmDiscipline.lean`).
- **`skel` against the Rust prover, by test** (`QuotientZk/Test/SkelTrace.lean`, executable `skeltrace`;
  `crates/quotient/tests/skel_trace.rs`, feature `skel-trace`, which records every Keccak call of a proof through
  test-only hooks): at `2^17` rows `skel`, run as compiled with mumbai's Keccak-256 and Keccak-f[1600] as the
  oracle, on the prover's statement, secret leaf digests and messages (cut from its transcript at its draws),
  makes the prover's queries byte for byte: the label and the five chain steps, the three IVs and seeds, the 254
  draws and 17 overflow permutations (capacity included), the 11 grinds (the smallest nonce, every try from 0),
  the 11 trees (sizes and roots); its proof is the prover's (roots, values, streams, opened positions, siblings).
  The differences, none touching zero knowledge: two public queries in another order (the witness tree before
  the label; the wiring tree, the prover's setup, after `ρ`); the prover's queries the skeleton does not make
  (the three layout ids, which the skeleton takes as constants and `c₀` can hold; its own `verify` replaying the
  chain; and the key derivation of its randomness, all on its 32-byte secret seed but the cells' digest, whose
  outputs only feed it: the skeleton's randomness is uniform, as documented); and grinding's closing
  permutation, a discarded draw in the prover, the last try in the skeleton (the same query). At every size
  `2^17 .. 2^22` the prover's draws, the scalars it absorbs between them, its trees' sizes and its stream are
  the grammar of the shape derived from WHIR's configuration, which at `2^22` is `deployedShape` (the numbers
  and the IV prefixes with the real layout ids). `skel` itself is not run at `2^22`: its trees' `levelUp` nests
  one bind a pair, quadratic to run (`2^17` rows: 6 minutes).

## Zero knowledge end to end (`EndToEnd/ZK`)

The Statement states zero knowledge for a simulator given as a parameter, `PcsQuotient.ZeroKnowledgeWith s₀ sim
simOracle ζ` (`Statement/PcsQuotient/Security.lean`); `ZeroKnowledge ζ` is that at the Statement's own
`simulator`, a tested heuristic that no theorem covers. **`zeroKnowledge_end`** (`EndToEnd/ZK/Main.lean`,
library `ZK`; `propext`, `Classical.choice`, `Quot.sound`, guarded in `ZK/Axioms.lean`) proves
`ZeroKnowledgeWith s₀ (zkSimulator pp simV skelOf fmt) rpmSimOracle ζ` under named hypotheses: the simulator
the theorem covers is in its statement. The hypotheses are discharged step by step below;
**`zeroKnowledge_closed`** (`ZK/CoreMain.lean`) has none. **Scope**: single-proof zero knowledge.
`realExperiment` runs the prover first in an empty, lazily sampled `π`, and the distinguisher queries `π` and
`π⁻¹` only after it has the proof; a distinguisher's queries before the proof (precomputation, auxiliary input
depending on `π`) and several proofs under one `π` are not covered. So the Fiat–Shamir freshness bound is taken
with an empty cache before the proof (`c₀ = []`, `fsFresh_setup_deployed_bits`), and `FSFresh`'s inherent
`|c₀| · 2^-191` term is `0` here; a pre-proof phase is planned, which will make it nonzero.

**The simulator** (`zkSimulator`, `ZK/With.lean`; `rpmSimulator`, `rpmSimOracle`, `ZK/Simulator.lean`; an
explicit simulator; as stated, `deployedSimV` and `sigmaAtD` are `noncomputable`, and
`zeroKnowledge_closed_computable` restates the theorem with a compiled simulator (no axiom and no `noncomputable` constant in its closure), proven equal). It reads the statement
and public data, never the witness: `pp stmt`, the skeleton model's public part (the number `n` of
Fiat–Shamir challenges, when each secret table is committed, which positions are opened: functions of the
challenges), `simV stmt`, the joint honest-verifier simulator (`jointSim`: the four values
uniform in `K` or `E` and the wiring value `σ(t)`, the two secret tables built from them with the verifier's
claims, opened by the honest WHIR algorithm with fresh paddings, the wiring table's opening), and the skeleton
`skelOf stmt` (`skelSetup`: the circuit's commitment, then `Deployed.skel`). Its state is the indifferentiability
simulator's (the permutation's edges it has answered, the rooted sponge states) and a random oracle's cache of
Keccak-256 and of the permutation.

1. Draw the `n` challenges uniformly; compute the view `simV σ` (messages and opened rows).
2. Run the skeleton (`QuotientZk.sim` on `skelRec`): every hash a lazily sampled random-oracle query, the `c`-th
   Fiat–Shamir query answered by the `c`-th challenge and written into the cache (programming), the messages
   and opened rows from the view, a fresh private digest at every unopened leaf of a secret table (so the trees'
   nodes and roots hash fresh values), grinding run as the prover runs it; record the duplex's permutation calls.
3. Set the state to that record and the cache; read the Statement's proof from the skeleton's (`fmt`,
   `ZK/Format.lean`: the reduction's nine scalars; per opening the stream, and the verifier's program replayed
   from the claims it computes, the full Merkle path of every queried position, in the verifier's order,
   produced from the pruned multiproofs; within `2^23` calls of `π`, answered as below).
4. Answer every query of the distinguisher: coins forwarded; `π` and `π⁻¹` on lanes, read as bytes, by
   `common`'s two-oracle simulator `S₂` (`simulator2`): a recorded edge from the record (so the duplex the
   distinguisher recomputes from the proof meets the programmed challenges), a fresh forward query that ends a
   sponge path padding a message `m` by the cache's Keccak-256 of `m` completed by uniform bits, any other fresh
   forward query by the cache's permutation answer, a fresh inverse query by a uniform state.

**Its cost**: no call of a real `π`; step 1, `n` uniform draws and `jointSim` (four samples, two table builds,
two WHIR openings with fresh paddings, the wiring opening: the honest prover's opening work; counted below,
"The simulator compiled"); step 2, the
skeleton's at most `2^24 + 2^70` operations (`skelSetup_queryBound`; worst-case grinding counted, `2^17`
expected tries a grind), each a cache lookup, a programmed answer or a uniform digest; step 3, `fmt`'s calls;
step 4, per query one step of `S₂` (lookups in its edges and rooted states, the unpadding of one path, at most
one cache lookup or uniform answer and one uniform state).

**The theorem** (`zeroKnowledge_deployed_end`, `ZK/End.lean`; `zeroKnowledge_end` for any valid joint model):
`ζ Q = εR Q + 2^-113 + epsHV + 2^24 (2^24 + 2^70 + 2^23 + Q) 2^-2368 + 2^48 2^-2368 + (Qp + 2^23 + Q)² / 2^508`,
`epsHV = 2^-165 + 2^-125 + 2/2^192`, for a distinguisher of `Q` calls of `π` and `π⁻¹` (coins free), at most
`εR Q + 2^-113 + epsHV + 2^-2200 + (Qp + 2^23 + Q)² / 2^508` for `Q ≤ 2^126` (`zkBoundEnd_le`). **The
degenerate challenges and masks** (`QuotientZk/Instance/Nondeg.lean`): the honest tables meet the verifier's
claims only where it divides by no zero (`1 + w_k(t)`, `k < 26`; the copy denominator `claimDen · vRows(t)`
of the masked values), so the joint model asks `hT₁`, `hT₂` only under `ClaimsND`; its good challenges are
`goodT` (`good` and `TND`: the scales and the row `t^4 + t` outside `K`, failing with probability at most
`(26·2^25 + 4|K|)/|E| ≤ 2^-125`), and at a `goodT` challenge the masks fail `ClaimsND` with probability at
most `2/|E|` (`claimDen` a monic quadratic in a value uniform in `E`, F1); the honest view is then within
`2/|E|` of the simulator's (`view_vclose`, `VClose`; `zk_rom_approx`, `zk_rpm_skel_approx`). Proved: the
distinguisher's coins removed (`ZK/Coins.lean`, a tape drawn first), the ideal experiment of `zkSimulator`
equal to `QuotientZk`'s simulated game (`rpmIdeal_eq`), `QuotientZk`'s closeness from the joint model
(`coreClose_of_joint`: `zk_rpm_skel_approx`, `jointHVZKε_of_linkV`, `factors_singleV`, `factors_pairV`),
`skelSetup`'s operations, duplex discipline and Fiat–Shamir freshness (`fsFresh_setup_deployed_bits`,
`2^-113`), the real experiment's coins drawn outside the model (`realExperiment_coins`), `fmt`'s budget
(`fmt_queryBound`), the Statement's coins `decodeCoins` of uniform words (`sampleCoinsP_eq`,
`coinsMatch_of_bijective`), the joint model of the deployed prover (`deployedJointData_valid`; its public part
and view simulator the simulator's by definition, `pub_deployed`, `simV_deployed`).
**Named**: the field and F1's facts on the statement and the witness, the simulator's public functions, the
honest tables' claims off the degenerate challenges and masks (`deployedJointData_valid`'s hypotheses); the
prover's permutation budget `Qp`; a bijection `e` of the skeleton model's randomness onto the Statement's coins'
words; `ProverBridge` (`εR`: the Statement's
prover at the coins `decodeCoins (e s)` against the skeleton's prover `proverJ` on `skelSetup` at `s`, then
`fmt`: the proof-of-work fuel `2^25` with no proof on failure, the replayed chain and the order of public queries,
the proof's format; the skeleton trace test's list of differences is the checklist).

**The deployed instance plugged in** (`zeroKnowledge_deployed_final`, `ZK/Final.lean`): the fields `K = F64`,
`E = F192` (`[E : K] = 3`, the cards, `1, Y, Y²` independent, the words and limbs: `ZK/FactsField.lean`), F1's
facts on the deployed instance (`beta()`'s basis, the deployed σ, `coordinate_weight`'s weights; the statement's
words `statement::halves`; the witness the cells of F0b's honest assignment of the secret, `w_22`; the relation:
`ZK/FactsF1.lean`), the simulator's public functions (`inKD`, the limbs `y`, `y²` zero; the wiring polynomial),
the honest tables' claims (Completeness's witness and quotient tables placed on `witness_layout(22)`,
`quotient_layout(22)`; the layouts' claims on a placed table are its multilinear claims, `ZK/FactsLayout.lean`;
F1's completeness passed to the tables, `ZK/FactsClaims.lean`: `hTWD`, `hTQD`) and the coins' bijection
(`eD`: the masks' words, each lane's padding words, the overflow lane's stream shifted past its held pieces as
`Layout.stackOf` reads it) discharged. **Named**: the renderer `R`, the prover's permutation budget `Qp`
(`hprover`: the skeleton hashes the renderer's rows, so it depends on `R`), `ProverBridge` at
`decodeCoins ∘ eD`. The simulator's tables `simTW`, `simTQ` are computed (`QuotientZk/Instance/Builder.lean`'s
Gaussian elimination in `deployedRep`'s coordinates); its wiring value (`sigmaAtD`, `P₀D.sigmaPoly.eval`) and
`deployedSimV` are `noncomputable` as stated; the compiled simulator (`zeroKnowledge_closed_computable`) is below.

**The prover bridge's parts and the bound** (`ZK/ProverBridge*.lean`, `ZK/Budget.lean`, `ZK/CoreBad.lean`).
With WHIR's honest prover as the renderer (`whirRenderer`), `ProverBridge` follows from a deterministic core at
a fixed permutation and a bound on `badProb`, the probability that the prover makes no proof or meets degenerate
`α, β` (`proverBridge_of_detG`). Proved: `badProb ≤ deltaNone < 2^-162` (`hbad_deployed`, from completeness's
staged run; `E2ECompleteness.hnone_deployed` for no proof alone); the prover's budget `Qp = 12 · (2^24 + 2^70)`
calls of π (`hprover_whir`); the duplex and grinding (`ProverBridgeDuplex.lean`), the trees and the expansion of
the pruned multiproofs (`ProverBridgeMerkle.lean`). The bound is then `ζ Q = deltaNone + 2^-113 + epsHV +
2^24 (2^24 + 2^70 + 2^23 + Q) 2^-2368 + 2^48 2^-2368 + (Qp + 2^23 + Q)² / 2^508 ≈ 2^-113` for `Q ≤ 2^126`
(`zkBoundEnd_le`), its largest term Fiat–Shamir freshness (`fsFresh_setup_deployed_bits`: `6 Q'(c + Q')/2^256 +
6 (c + Q') 2^-191 + c 2^-2368`, `Q' = 2^24 + 2^70` the skeleton's operations with worst-case grinding,
`c = 2^19` the setup's public rows).

**Rendered by WHIR's honest prover** (`zeroKnowledge_final`, `ZK/CoreEnd.lean`): the Statement's
`ZeroKnowledgeWith` at `zkBoundEnd ((2^24 + 2^70)·12) fmtBudget (· ↦ deltaNone)` (`deltaNone < 2^-162`) for
`zkSimulator` with the renderer `whirRenderer deployedRep stmt` per statement, on `skelSetup` at the deployed
public data (`stmtBytesD`, the layouts' identifiers, the wiring codeword's rows), from the **deterministic core
`CoreD`** (`ZK/CoreDefs.lean`): for every permutation at which the Statement's prover makes a proof and its
`α, β` are not degenerate, `fmt` makes that proof of the skeleton's. **`zeroKnowledge_closed`**
(`ZK/CoreMain.lean`) is it with `CoreD` proved (`coreD`): no hypothesis is left. `CoreWhir` (every
permutation) is false: at degenerate `α, β` the Statement's coset division is not F1's quotient, which the joint
model's `TQD` is; `badProb` (no proof, or degenerate `α, β`) is bounded instead (`hbad_deployed`,
`ZK/CoreBad.lean`, from completeness's staged run) and enters `ProverBridge` (`proverBridge_of_detG`). `fmt`'s
`fillRun` ends at the program's `fail` as at its `ret` (mumbai's `runFrom` does). Proved towards `CoreD`: the
joint model's stacks and leaves are the Statement's codeword rows (`ZK/CoreTables*.lean`), the view's lane
rounds and folded table are mumbai's arrays' (`ZK/CoreView*.lean`), the verifier's program follows the
skeleton's events at the three ladders (`ZK/CoreFollows.lean`), `runFrom` and `fmt`'s production on events
(`ZK/CoreEv.lean`, `ZK/CoreFill.lean`), the skeleton's opening on events (`ZK/CoreSkel.lean`), their lockstep
(`drive`, `ZK/CoreDrive.lean`), `fmt` within its budget (`ZK/CoreBudget*.lean`), the reduction's chain, values,
claims and seeds (`ZK/CoreRed*.lean`), the renderer's messages, the honest script's drive of the Statement's
level-0 word (`ZK/CoreRender*.lean`), an opening end to end (`ZK/CoreOpen.lean`), and the assembly
(`ZK/CoreMain*.lean`).

**The simulator compiled** (`ZK/ComputableClosed.lean`, `ZK/Computable.lean`, `ZK/ComputableFacts.lean`,
`QuotientZk/Instance/Compiled.lean`). **`zeroKnowledge_closed_computable (s₀)`**: `ZeroKnowledgeWith s₀
zkSimulatorClosed rpmSimOracle (zkBoundEnd ((2^24 + 2^70)·12) fmtBudget (· ↦ deltaNone))`, no hypothesis, for
**`zkSimulatorClosed`**, a `def` (compiled), **equal as a function to `zeroKnowledge_closed`'s simulator**
(`zkSimulatorClosed_eq`; its samplers `formal/Field`'s `instSampleableTypeF64`, `instSampleableTypeF192`, as
there). The definition chain: `zkSimulatorClosed = zkSimulatorC stmtBytesD idWD idσD idQD rowsWDc`;
`zkSimulatorC = zkSimulator (· ↦ deployedPub deployedRep) (stmt ↦ deployedSimVc (whirRendererC deployedRep
stmt) stmt) (stmt ↦ skelSetup …) fmt` (`zkSimulatorC_eq`); `deployedSimVc R stmt σ = outP … R σ <$>
jointSimVm deployedRep peD (tgtD stmt) F192.Y inKD sigmaAtC (chOf deployedRep.limbs σ)` (`deployedSimVc_eq`:
`= deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y R inKD sigmaAtD`). What replaces each `noncomputable`
part, proved equal:

* the parameters `P₀D` by their **public evaluations** `peD` (`peD_matches`): `θ = β₁`, `v_cells(t) = S^24(t)`,
  `v_rows(t) = Π_{r < 2^22} (t − x_r)` (`rowsAtC`), `pub(γ)(t)` by its product formula (`pubAtC`), the target
  `Σ_J γ^J w_J` (`tgtD`); the verifier's formulas on them (`claimDenP`, `claimValueP`, `pointQP`, `valsQP`,
  `claimMsgP`, `outP`);
* **`σ(t)`** (`sigmaAtC`, `sigmaAtC_eq`): the wiring polynomial is the Lagrange interpolant on the `2^24`
  cells; on the span of a Cantor basis the nodal polynomial is `S^24`, of derivative `1`, so every barycentric
  weight is `1` and `σ(t) = Σ_p r_p Π_{q ≠ p} (t − v_q)`, accumulated in one pass (`lagAcc`): `3·2^24`
  products, no inversion;
* the openings' **novel basis at the opened positions** (`encOf`, `encTab`, `subRoots`; `encOf_eq`): the
  normalizers `W_k(v_k)` (`O(ℓ²)`), per opened position the `ℓ` values `Ŵ_k(K(p))`, an entry `X_y` the
  product of its bits'; the claims' points compiled (`pointWc`, `pointQP`, `pointSc`);
* the tables as data (`solW`, `solQ`: `Builder.lean`'s elimination, `sparse_solW`, `sparse_solQ`) and the
  level-0 views **stored in arrays once** (`viewW`, `viewQ`, `memoL0`; `viewW_eq`, `viewQ_eq`), so the
  renderer reads the view at each step without recomputing it (`jointSimVm`, `jointSimVm_eq`);
* WHIR's honest renderer (`whirRendererC`, `whirRendererC_eq`) and the wiring codeword's rows (`rowsWDc`,
  `rowsWDc_eq`): the same programs, compiled.

**The audit** (`#computational_axioms`, after `Compose/DecoderAxioms.lean`): every constant
`zkSimulatorClosed` reaches outside proofs and types, followed through its definition: **no axiom**
(`Classical.choice` only in proofs, `#print axioms` lists it from the fields' instances' proofs), no
`noncomputable`, `implemented_by`, `extern` or `opaque` constant outside Lean's core (`#guard_msgs`, also for
`zkSimulatorDeployed` and `whirRendererC`). **Runs** (`EndToEnd/Review/ZkSimulatorEval.lean`, `#eval`): the
recurrence `W_k` is the subspace product (`k ≤ 8`) and vanishes on its subspace; an encoding entry is its
bits' product; `lagAcc` interpolates on the cube of `6` bits (at a cell and off the cells); `θ`, `v_cells`,
`pub` and the witness claim's bytes (`624`) at a sample challenge; and **`σ` at a cell is its successor's point**
(`sigmaAtC (nodeE 5) = succE 5`, the deployed `2^24`-cell accumulation, about an hour interpreted:
`0.25` ms a cell). The whole simulator is not run: its view alone is up to about `2·10^14` operations.

**Its cost** (operations of `K = GF(2^64)`, `E = GF(2^192)`; `ZK/Computable.lean`'s module doc): `394`
challenge draws; the view once: `σ(t)` (`3·2^24` products in `E`, `2·24·2^24` additions in `K`), the four
values, the paddings (`40·2^19 + 63·2^22` words), the two eliminations (`O(k(4·10^3 m + r² + r 2^r))` for `k`
scanned entries, `k = 6, 9` at a generic challenge; `v_rows(t)`, `2^22` products), the encodings (`ℓ²` per
opened position), the six lane rounds (at most `21` message evaluations, each at most `2^(ℓ+7)` reads of the
batched weight, `≈ 8·10^3`, `2·10^4` operations a read), the folded tables, the opened rows (`|Q|·|ι|·2^ℓ`
reads of at most `ℓ` products): **at most about `1.2·10^13` (witness) and `2.3·10^14` (quotient)
operations, dominated by the lane rounds' claim weights**; per message one
run of WHIR's honest prover up to the step on the stored view (at most one opening of `2^25`, `2^24` or `2^28`
words); the skeleton's `2^24 + 2^70` worst-case operations (grinding; `2^17` expected tries a grind); `fmt`'s
`2^23` calls of `S₂`; per distinguisher query one step of `S₂`.

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
  deployed σ). **Not covered here**: a random-oracle theorem for the chain's honest challenges (the
  density above is over uniform `(α, β, t)`; an honest run's chain queries are fresh but for collisions, a few
  `Q² / 2^256`) and one experiment holding both the chain and the openings' proofs of work (both proved in
  `EndToEnd/Completeness`, below); `log_rows < 22`; that the Rust is this Lean (F5; the claims' values by F1's
  review, the openings by F2's tests).

**To the Statement's `Completeness δ`** (`EndToEnd/Completeness/`, library `E2ECompleteness`; sorry-free,
`propext`, `Classical.choice`, `Quot.sound`, checked by `#guard_msgs` in `E2ECompleteness.lean`):
`completeness_of_staged` proves `PcsQuotient.Completeness ((17 · 2^24 + 8) / 2^192 + 2 / 2^256 + εpow +
N² / 2^508)` and `completeness_deployed` the deployed `δ < 2^-162` (`N = 2^48` block calls,
`εpow = 3 · 2^-277`, `deltaDeployed_lt`), from the staged form of the experiment (`Staged.Holds`). Proved: the
**random-oracle theorem for the chain's honest challenges** (`Chain.lean`, `prEvent_staged_le`: in the two-call
random-oracle model the `α`, `β`, `t` queries are fresh by their lengths, `96` and `32` bytes, which the Merkle
trees and the label never hash, but for `s₂ = s₁` or `s₃ = s₀`, so `(α, β, t)` lies in `Bad` with probability at
most `|Bad| / 2^576 + 2 / 2^256`, for any challenge map with at most `2^64` digests per value); the transcript's
`challengeOf` is such a map (`Regular.lean`); the transfer from the random permutation to the two random oracles
for any honest computation following the duplex discipline (`Transfer.lean`, `rpm_le_rom`, mumbai's
indifferentiability, `N² / 2^508`); `Bad` is `completeness_deployed_concrete`'s set for the secret and the masks
(`badSet`, density `badSet_density`; `completeness_bad_set`'s set on the deployed instance). **The staged form
for the Statement's experiment, proved** (`Staged.Holds`, `Assemble.lean`): the Statement's setup, prover and
verifier with Keccak-256 an explicit call (`WithHash.lean`: `setupWithH`, `proverWithH`, `verifyWithH`, equal to
the Statement's at `keccak256With F` and commuting with simulation); the experiment coins first (the raw coin
words swapped with the setup, `Experiment.lean`, `completenessExperiment_eq_expH`); the run in the chain's shape
(`Staging.lean`, `expH_eq_staged`, generic in the circuit so that no definitional check evaluates the deployed
circuit); nothing of `32` or `96` bytes hashed before `α` or between `γ` and `t` (`HashLen.lean`: 512-byte
leaves, 64-byte nodes, the 112-byte label); the duplex discipline (`Duplex.lean`, `duplexVm_stagedRun`: every
opening, prover's and verifier's, starts its own duplex at a zero capacity). **The last two hypotheses of
`completeness_deployed_cost_rej`, proved**: `RejectGood (3 · 2^-277)` (`Grinding.lean`, `rejectGood_deployed`: in
the two-call random-oracle model the run is rejected at non-degenerate challenges with probability at most
`3 · 2^-277`; the Statement's prover is accepted at non-degenerate challenges when its proofs of work succeed, the
prover bridge `Prover*.lean`, with mumbai's proof-of-work potential over the whole run's log: the grinding fails
with probability below `2^-304`, `grinding_le`, within the stated `3 · 2^-277`; not `formal/Completeness`'s
per-opening `ours_romComplete`) and the block count (`Cost.lean`, `hcost_deployed`: at most `2^48` block calls;
exactly `114 098 677 826 653 < 2^47`, the review's `hcost_exact`). So **`completeness_end`** (`Done.lean`):
`PcsQuotient.Completeness deltaDeployed`, no hypothesis, `deltaDeployed ≈ 2^-163.91`. The review
(`Review/E2ECompletenessReview.lean`) adds `completeness_every_coins`: the same `δ` for every fixed value of the
coins.

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
