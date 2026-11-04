<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Second adversarial review of the recursive verifier's end statements

Reviewed at f774b11 (`fix-rec-iv`). It covers statements and definitions, not proofs. The headline theorems are
`RecCompose.recKnowledgeSoundness_reduction` and `recKnowledgeSoundness2_closed` (`FsClosed.lean`), and
`RecCompose.Pi2KF.recCompleteness2_pi2_rec3_kf`, `recCompleteness_pi2_rec3_kf_fs` and `delta2_kf_le`
(`Pi2KFEnd.lean`). It also covers their definitions and the first review's "Fixed" paragraphs
([`STATEMENT_REVIEW.md`](STATEMENT_REVIEW.md)), which it treats as claims to check.

Evidence (this directory):

- [`StatementReview2.lean`](StatementReview2.lean). It elaborates on h1 against the f774b11 build with no error and no
  `sorry`, on `propext`, `Classical.choice`, `Quot.sound` (`#guard_msgs`):
  `cd formal/EndToEnd && systemd-run --scope -q -p MemoryMax=12G lake env lean ../RecCompose/Review/StatementReview2.lean`.
- [`IvSample.lean`](IvSample.lean). It was run as the executable `rec-iv-sample` in an h1 copy. Its `lean_exe` stanza
  is now committed (`formal/EndToEnd/lakefile.toml`).

**Verdict.** No statement is wrong in the sense of the first review: none is vacuous or trivially satisfied, and none
has a bound that cannot apply. The first review's fixes close their findings. What remains:

- One universally quantified evaluated premise. `IvChecked` covers `2^256` IVs and is evaluated at 3 of them, with 9 more running at hand-off.
  Code reading supports it strongly, but nothing proves it.
- A completeness prover that is a Lean transcription. It has never been tested against the Rust prover.
- An honest-hazard premise `δh` with no random-permutation reading.
- Documentation that is in places too strong, and in one place too weak (the "matrices gap" is empty).

## Findings, ranked

### 1. The completeness theorems' π1 prover is a Lean transcription, never tested against the Rust π1-rec3 prover (misleading doc)

`Pi1KF.pi1Rec3ProverKF D = pi1ProverFs hKF D`, which is UniComplete's `proveRec3With` with its hash split
(`Pi1KF.lean:84-111`). `UniComplete/UniComplete/Rec3Prover.lean` says it "follows `prove.rs` and `batch.rs`
(`prove_pairs`) at `FLOCK_REC3`". It has no differential test:

- UniComplete's only runner (`UniCompleteTest/Runner.lean`, README "The differential test") covers the main-line prover
  with **Flock omitted**, at memory and bytecode sizes `2^4`/`2^5`.
- `RecComposeTest/` tests π2's prover only (`Pi2Prover.lean`, at `2^9`, `2^10`).
- Nothing under `UniCompleteTest/`, `RecComposeTest/` or `Review/` runs `proveRec3With`, `uniProverRec3With` or
  `pi1Rec3ProverKF` against Rust output (grep: no hits).

The repository links π1-rec3's Rust prover to the Lean side only through acceptance: RecStatement's differential
runner checks that one real Rust π1-rec3 + π2 proof is accepted by the Lean verifier.

So `recCompleteness2_pi2_rec3_kf` and `recCompleteness_pi2_rec3_kf_fs` are completeness theorems for **a** Lean honest
prover that the deployed verifier accepts. They say nothing about the deployed Rust prover. The docs say otherwise:

- `Pi1KF.lean:23`: "`pi1ProverFs Hfs D`: **the deployed π1 prover** over the random permutation".
- `Pi1KF.lean:17`, `Pi2KFEnd.lean:16`, `formal/README.md` ("superseded by the same theorems at **the prover the
  recursion runs**").

The membership verifier's docs (AGENTS.md, `formal/README.md`: "the deployed Rust prover is trusted for completeness
(the tests above are its only link)") carry the caveat that is missing here. π2's prover has the same issue in a
weaker form. It is tested at toy sizes only, and it takes its witness by `Classical.choose` among `Pi2Good` witnesses
(`Pi2CompleteEnd.lean:62-64`; the first review's finding 6, item not fixed).

**Fix.** Say "UniComplete's Lean π1-rec3 prover (a transcription of `prove.rs` at `FLOCK_REC3`, not differentially
tested); the deployed Rust prover is trusted for completeness". Better, add a rec3 differential test: the Lean
`streamRunKF` against the Rust `prove` at a small shape, comparing stream bytes as UniComplete's runner does for the
main line.

**Caveat added, no test** (`fix-rec-docs2`). The rec3 differential test was started and then dropped for time; it is
still to do. What the attempt found: the Rust π1-rec3 prover refuses every small Flock shape tried (memory/bytecode
logs 5/7, 6/7, 7/7, 5/8, 6/8, with 77 to 205 BLAKE2S rows; Flock needs a BLAKE2S height of at least 7,
`verifier.rs:65`). `prove_pairs` fails with "a stack shorter than the batch ends inside a pair"
(`crates/leanvm_univariate/src/prover/batch.rs:295-296`): a stack with an odd number of variables is accepted only if it
is the largest, and at these sizes the setup stack has 15 variables while `C1` has 16 or 17. By the attempt's
reading (not checked further), the Lean `batchRounds3` zero-extends such a stack instead, so the two provers would
differ there by construction; not at the reference shape, where the Rust prover runs. A test needs a shape whose odd stacks are the largest, or a Rust `prove_pairs` that zero-extends.
A synthetic trace with real BLAKE2s compressions and Flock's own `q_flock` witness (`log_n = 21`, 128 instances)
passed its checks up to that point. The docs now carry the membership side's caveat, "the deployed Rust prover is trusted for completeness;
the Lean prover is a transcription", for π1 (`Pi1KF.lean`'s module docstring and `pi1ProverFs`, `Pi2KFEnd.lean`,
`formal/README.md`'s "The recursion's π1 prover") and for π2 (`Pi2CompleteEnd.pi2Prover`, compared with the Rust on
`spec::example()` at `2^9`, `2^10` only, its witness `Classical.choose`; `formal/README.md`'s "π2's honest prover").
The status note of `formal/README.md` lists it as open.

### 2. `IvChecked` is a universal over `2^256` IVs. No counterexample exists by code reading or by 9 more evaluations, but it is unproved, and one bad IV would void every end theorem (open premise; docs honest, but the risk is understated)

Every headline theorem takes `C : Pi2Circuits D` and `Pi2ViewChecked C`. At `realDeployment` these come from
`IvChecked : ∀ iv, iv.length = 32 → ivCheck iv = true` (`RealDeployment.lean`). In the model π1's setup roots are
outputs of `π`, so `pi1IvAt roots` ranges over essentially every 32-byte value, and the `∀` is genuinely needed.

The failure mode is not "fails with small probability". If `ivCheck` failed at **any one** 32-byte IV, `IvChecked`
would be false, and every end theorem at `realDeployment` (soundness and completeness) would have an uninhabited
hypothesis. The deployed contract uses one IV (`Data.pi1Iv`, evaluated). The other `2^256 − 1` matter only to the
model.

**Searching for a failing IV, by reading.** The IV enters exactly three places:

- `RecCircuit/Compile.lean:181`: `constantBits NAME ++ constantBits r.iv ++ publicCopy`.
- `Check.lean:280-281`: `seedMessage iv`, which the checker compares with the recorded sponge message.
- `Check.lean:464`: `r.iv.length == 32`.

The grep over `RecCircuit/` finds no other use. Reading those paths:

- **One block.** `NAME` is 16 bytes (`Graph.lean:102`), so the seed's message is 80 bytes, below the 136-byte rate.
  It is absorbed as block 0 only. In later blocks the builder would treat the bits differently: a `.one` makes a
  `fresh 1` and a `xor`, a `.zero` makes nothing (`Templates.lean:265-273`). That would be a structural IV
  dependence, so the 80-byte bound is load-bearing.
- **Allocation is value-oblivious.** Block 0's `.zero`/`.one` reach `permute` as `fresh 0`/`fresh 1`
  (`Templates.lean:184-187`). `fresh` allocates its slot without reading `k` (`Templates.lean:32-51`), and `setKappa`
  writes `κ` only when `k ≠ 0`, after the same `isExpr` check (`Layout.lean:258-261`). No constant cell is shared or
  deduplicated.
- **The checker reads these cells only by value.** It checks a seed input bit as `constOk x 0` or `constOk x 1`
  (`Check.lean:180-181, 196`), and the message against `seedMessage iv` built from the same `constantBits`.

So the compiled circuit at `iv` should be the zero IV's with `κ = 1` added at the positions of `iv`'s one-bits, and
`ivCheck` should be constant. Nothing in `validB`, `viewOf`, `callsOf`, `streamAgree` or the completeness checks reads
those 256 `κ` values other than through `constOk`. I found no IV where it fails.

**Evaluated.** `rec-iv-sample` ran on h1 (f774b11 build; three processes in parallel, each under `MemoryMax=12G`). It
covered 6 pseudo-random IVs and 3 structured ones: the reference IV with bit 0 flipped, a single low bit, a single high
bit. For each, it checked `ivCheck`, and whether `logN`, `logWidth`, regions, blocks, `σ`, ports and calls are equal to
the reference IV's circuit. It also took the symmetric difference of the sparse `κ` (expected: only `1`-valued entries,
size moving by the popcount difference). **Status at hand-off: the reference circuit had compiled in all three runs (19,143 `κ` entries, popcount 146, as
`rec-real-check`). The nine sampled IVs' lines were not yet printed** (about 13 minutes per IV, three runs in
parallel). Their logs are `/root/pcs-quotient-fv/review2/sample-{0,3,1000}.log` on h1. Append them here, then delete
`review2`.

**Results** (appended by `fix-rec-docs2`; h1, `rec-iv-sample 3 0`, `3 3`, `3 1000`, about 25 minutes an IV per
process). Each line: `ivCheck`; whether `logN`, `logWidth`, regions, blocks, `σ`, ports and calls equal the reference
IV's; `κ`'s entries, the symmetric difference with the reference's (`+` only here, `-` only there), whether every entry
of it is a `1`, and whether `κ`'s size moved by the popcount difference.

| index | IV | popcount | `ivCheck` | structure equal | `κ` entries | difference | all ones | size check |
|---|---|---|---|---|---|---|---|---|
| 0 | `85d3ff47f89be87938bfb1cfc77ed52002e8d3c27f2c1e217ae436b0b31da1ff` | 141 | true | true | 19138 | +70 −75 | true | true |
| 3 | `55c2aed426cc58a15dee8a807ad51d242d491e7d944888853393aec21ecd7a76` | 122 | true | true | 19119 | +48 −72 | true | true |
| 1000 | `b74dacfd5e63bf47f8601ef74de51666fa02acbd959fcf6500192f96d4d7fef9` | 147 | true | true | 19144 | +1 −0 | true | true |
| 1 | not finished | | | | | | | |
| 2 | not finished | | | | | | | |
| 4 | not finished | | | | | | | |
| 5 | not finished | | | | | | | |
| 1001 | not finished | | | | | | | |
| 1002 | not finished | | | | | | | |

**3 of 9 sampled IVs evaluated: all hold** (`ivCheck` true, the structure equal, the `κ` difference only `1`s of the expected size). The union of the differences' positions over these IVs: 198 positions, all in `92175..96255` and `≡ 92175 mod 16` (yes), a set of at most 256 slots: the seed's IV constants, one slot a bit. Not finished at hand-off: indices [1, 2, 4, 5, 1001, 1002] (the three runs still going; `review2` kept).

**Fix.**

1. Add `IvSample`'s structural comparison to `rec-real-check`. It is a much stronger evaluated statement than three
   `ivCheck` booleans: a whole circuit equal up to a `κ`-patch on a fixed 256-position set.
2. Record the reading argument above in `RealDeployment.lean`'s docstring. It is the reason to believe `IvChecked`.
3. To remove the premise, choose one of two routes:
   - **(a) Proof.** Prove `compile (ofRG g ra iv) = patchκ P iv (compile (ofRG g ra zeroIv))` for a fixed position list
     `P`. Then prove the checker's verdict invariant under the patch. The first part is a simulation of `compileM` in
     which only `fresh`'s `k` differs, about 1,200 lines that pass `k` through untouched. The second needs only that
     `P`'s cells are read by `constOk` alone.
   - **(b) Redesign.** Make the IV a public input of π2's circuit, like the statement's 256 bits (`publicCopy`), not
     `κ` constants. One compile then serves every IV, and `IvChecked` collapses to the one evaluated check.
4. Until then, say in the end-theorem docstrings that a single failing IV would make them vacuous.

### 3. The honest-hazard premise `δh` has no random-permutation reading, unlike `δ1`, but the docs pair them as both backed by RPM theorems (misleading doc)

`recCompleteness_pi2_rec3_kf_fs` bounds the contract's rejection of an honest proof by `δ1 + δh + δ2`. For
`δ1 = Pi1CompletenessKeccak D (pi1Rec3ProverKF D) δ1`, the random-permutation reading is proved
(`Pi1KF.pi1CompletenessFs_rpm`, `deltaRec3 < 2^-167`). For `δh = Pi1HazardKeccakHonest D (pi1Rec3ProverKF D) δh`,
nothing is proved even in the random-permutation model. `RecGraph.hazard_prob` is a counting statement about a
uniform `t` with `p_0` fixed, not a game. `deltaRec3`'s `BadT` term is a different event: `y(t)` a proper prefix of a
`C1` point, not `Z_bad(t) = 0`. The docs nonetheless say:

- `formal/README.md:548` (the named-inputs table): "the Fiat–Shamir heuristic (π1-rec3's **random-permutation
  theorems**)";
- `RecStatement/README.md:332`: "justified by `uniCompletenessRec3_end_closed` and `hazard_prob`";
- `Security.lean:56-59`: "justified by …".

The soundness hazard `εh` is in the same position, but its docs are honest ("Not done": `Security.lean`,
`RecStatement/README.md` open point 2).

**Fix.** Prove the RPM reading `Pi1HazardKeccakHonest`-at-`π` for `pi1ProverFs (keccak256With π)`. UniComplete's
π1-rec3 staging at `t` (`Rec3ProbStaged`, `Rec3ProbTFresh`) already makes `t` fresh and uniform given the challenges
before it. `hazard_card` then gives `2^19/|E|` plus the freshness term, about `2^-173`. Until then, say
"`δh`: motivated by `hazard_prob` only; no game bounds it".

### 4. The "known gap" of `pi1KeccakVerifierWith` is empty: at Keccak-f[1600] it is π1-rec3's deployed verifier (misleading doc, in the conservative direction)

`pi1KeccakVerifierWith` (`Security.lean:405-425`) omits `verifyWithFs`'s final check that `r.matrices = none` at the
walk. The first review (finding 4, "Found"), `Pi1KFCore.lean:242` ("it does not check a matrices' claim") and
`Pi1KF.verifierFs_le` ("rejects at most as often") treat it as a superset verifier. It is not one. π1-rec3's run never
returns a matrices' claim. Flock's walked branch outputs `none`, and `batchFs` with nothing pending returns `none`
(`UniStatement/Rec.lean:514-516, 464-482`). The repository has already proved this:
`RecCompose.pi1RunShape`/`runWithFs_shape` (`RunShape.lean`), for every permutation. `StatementReview2.lean` proves:

- `strict_eq`: the verifier with `verifyWithFs`'s three-armed matrices check restored is `pi1KeccakVerifierWith`, at
  every lawful monad and opening hash `F`, at the reference shape.
- `keccak_eq_verifierRec3`: at `F = Keccak-f[1600]`, `pi1KeccakVerifierWith D roots input proof` equals
  `D.verifierRec3With roots input proof`. That is π1-rec3's deployed verifier, the verifier of
  `UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`.

**On the question asked.** If the verifier really were weaker, the reduction would stay a true, proved inequality: a
weaker verifier only enlarges the π1 term. The reader's Fiat–Shamir premise about that term would then concern a
verifier other than π1-rec3's, and the RPM theorem would not motivate it directly. That would matter for
interpretation, not for soundness of the proof. It does not arise: the π1 term is about π1-rec3's verifier, its
Fiat–Shamir at Keccak-f[1600], its openings over `π`.

**Fix.** Restate `verifierFs_le` as an equality (or note `strict_eq`). Correct the "accepts at least what π1-rec3's
verifier accepts" remark in `STATEMENT_REVIEW.md` finding 4 and the `Pi1KFCore.lean:242` docstring. Optionally restore
the check in `pi1KeccakVerifierWith` for transcription fidelity.

**Fixed** (`fix-rec-docs2`). `Pi1KF.verifierFs_le` is replaced by the equality **`Pi1KF.verifierFs_eq`**
(`Pi1KFRpm.lean`): at the reference shape, in every lawful monad and at every hash `F`,
`pi1VerifierFsWith F F D roots input p = D.verifierRec3With F roots input p`, from `runWithFs_shape` through
`bind_congr_of_holds` (the reviewer's `strict_eq`, generalised from `runFs` to `runWithFs F`). With
`pi1VerifierFsWith_kf` it gives **`Pi1KF.pi1KeccakVerifierWith_kf_eq`**, the reviewer's `keccak_eq_verifierRec3` in
every lawful monad. `pi1CompletenessFs_rpm` uses the equality. The remarks are corrected (`Pi1KFRpm.lean`'s module
docstring, `Pi1KFCore.lean`'s `pi1KeccakVerifier_of_calls`, `STATEMENT_REVIEW.md` finding 4, `RecCompose/README.md`).
The check is not restored in `pi1KeccakVerifierWith`: the equality makes it unnecessary, and the Statement is
unchanged.

### 5. `keccak_accepts`'s `¬ BadKF` and `contract_rejects_le` (clarification; cosmetic)

The question assumed `contract_rejects_le` was conditional on `¬ BadKF`. It is not: `contract_rejects_le`
(`Review/Pi1ProverReview.lean:71-89`) is unconditional. It is
`Pr[contract rejects] ≤ Pr[π1's Keccak completeness experiment rejects] + Pr[honest hazard] + Pr[graph accepts ∧ contract rejects]`,
from `completenessPi1Coupling` and the proved `pi1GraphIsVerifier`.

`¬ BadKF` enters only `challenges_match` and `keccak_accepts`, the non-vacuity witnesses that the Keccak-f[1600]
verifier accepts the honest proof. No end theorem uses `BadKF`. Its probability at Keccak-f[1600] is part of the
heuristic premise `δ1`; at `π` it is inside `deltaRec3` (`BadFp`, `BadT`).

`keccak_accepts` also carries `hπ : prover = some π`, which is not shown satisfiable at any instance. The prover's
`none` (grinding beyond `nonceFuel`) is likewise inside `δ1`. So "graph accepts" in `RecCompleteness2` is the likely
event exactly when the heuristic `δ1` is small. That is consistent, and documented by `contract_rejects_le`.

**Fixed** (`fix-rec-docs2`). `Review/Pi1ProverReview.lean` (its module docstring, `challenges_match`, `keccak_accepts`,
`contract_rejects_le`), `formal/README.md` and `RecCompose/README.md` now say that `contract_rejects_le` is
unconditional and that `¬ BadKF` enters only the two non-vacuity witnesses; `keccak_accepts`'s `hπ` is noted.

### 6. Stale or imprecise docs (cosmetic)

- `Pi2CompleteEnd.lean:55`: `Pi2WitnessComplete` is still called a "Named input … (not transcribed; the Rust's witness
  generation and `Circuit::check` establish it)". It is proved: `Pi2W.pi2WitnessComplete`, which the KF theorems use.
- `RecStatement/README.md`, "Open points" 1 says "The Props are not proved". `RecCompose` proves them, so it should
  point there. Open point 2 says `Pi1CompletenessKeccak` and `Pi1HazardKeccakHonest` "are not provable". Their Keccak
  readings are heuristic, and the first has a proved RPM reading.
- `formal/README.md:286`: "Status (2026-11-05)". The f774b11 commits are of 2026-11-04.
- `Pi1HazardAccepted` asks `pi1GraphChecks`, not the full `Pi1GraphAccepts` that `breaks_cases` has. It is a larger
  event than needed: harmless, since the term is only larger, but the docstring "on a stream π1-rec3's graph accepts"
  should say "whose graph checks hold".
- The derived adversaries' time is documented as "a polynomial". The Keccak-f[1600] work the heuristic counts is `A`'s
  offline work plus the extractor's graph checks per candidate. Say so, since that is the resource the heuristic bounds
  and the reduction's `Q` does not.

**Fixed** (`fix-rec-docs2`), item by item: `Pi2WitnessComplete`'s docstring points to `Pi2W.pi2WitnessComplete`;
`RecStatement/README.md`'s open point 1 points to `RecCompose`'s theorems and open point 2 says the Keccak readings are
heuristic, `Pi1CompletenessKeccak`'s with a proved RPM reading; `formal/README.md`'s status note is rewritten as the
current status after both reviews; `Pi1HazardAccepted`'s docstring says it asks only `pi1GraphChecks`, a larger event
than needed; `Reduction.lean`'s docstrings, `RecStatement/README.md` and `formal/README.md` name the derived
adversaries' Keccak-f[1600] work as the resource the heuristic bounds.

## Answers to the questions

**1. Inhabitation.** Yes, from evaluated checks only. `NonVacuity.inhabited` gives
`∃ D (_ : D.Real) (C : Pi2Circuits D), C.rootsAt = Emitted.rootsAt ∧ GraphsAgree ∧ Pi2ViewChecked C`. Those are
exactly the premises of `recKnowledgeSoundness_reduction`, `recKnowledgeSoundness2_closed` and
`Pi2KF.recCompleteness2_pi2_rec3_kf`, which the file instantiates (`reduction`, `soundness2`,
`nonVacuity_completeness2_kf`). The `_fs` forms add only the documented heuristic Props. There is no extra hypothesis:
the four variables are `GraphsAgree`, `IvChecked`, `DigestChecked`, `SetupRootChecked`. Each is evaluated as the very
expression it names:

- `realPi2_ref` is `rfl`.
- `GraphsAgree` is checked field by field on all six `Graph` fields, with `DecidableEq`-derived `BEq`.
- No `implemented_by`/`extern` occurs in `formal/` or leanerVM, so compiled evaluation runs the definitions.

`realDeployment`'s data is the deployed system's where it matters:

- `Data.circuit` and `Data.pi1Calls` are emitted by the Rust, and `viewCheck` compares the compiled view and calls to
  them at each IV.
- `σ`, `κ` are the Lean compiler's. At `Data.pi1Iv` their digest and setup root equal the Rust's (evaluated).
- `pi1Stream` is the Lean compiler's decoding, a model choice used only by the extractor.

Leaving `D.pi1.prog` unpinned does not matter. `realDeployment_real`, `pi2Circuits_real` and `pi2ViewChecked_real` hold
for **every** `prog` with `hprog`, so inhabitation transfers from `prog0` to leanVM 42422001's program (not transcribed
in Lean), given that its log size is `reference.logBytecode`. The deployed `F` root is not linked to that program in
Lean, since the model computes it over `π`. That is documented.

**2. `IvChecked`.** See finding 2. Reading `Compile.lean`, `Templates.lean`, `Layout.lean` and `Check.lean`, the IV
enters at one line of the builder and two of the checker. The builder is value-oblivious there: a one-block seed,
`fresh` allocation independent of `k`, `κ` written only when nonzero. The checker reads those cells only through
`constOk`. I found no failing IV. A cheap strengthening is the structural comparison of `IvSample.lean`, running at 9
more IVs at hand-off. A real one is route (a) or (b) of finding 2.

**3. The reduction.**

- **Explicit.** `pi1Adversary` and `hazardAdversary` are `def`s (`Reduction.lean:46-56`): `A`, logged, then the
  computable `recExtractor2`. The query conjuncts are part of the proved Prop, so the "at most `Q`" is a theorem. Time
  is documented only, honestly.
- **The right game.** `pi1KeccakSoundnessExperiment` has the recursive setup over `π`, then the adversary given roots
  and evaluations, then `pi1KeccakVerifierWith` (Fiat–Shamir `runFs` at Keccak-f[1600], openings `pcsOpenWith π`).
  This is π1-rec3's deployed verifier at Keccak (finding 4), and the same shape as `uniSoundnessExperimentRec3` with
  the Fiat–Shamir instantiated.
- **The matrices gap** is empty (finding 4). The reduction would have been sound either way.

**4. The hazard.** It is non-trivial now:

- `MergeHazard` asks `50 ≤ ch.size`, and `Pi1HazardAccepted` asks `pi1GraphChecks`.
- `not_mergeHazard_empty`, `emptyAdversary_hazard_zero` and `hazardAdversary_default` show that the zero-query
  adversary and the extractor-failure default are off it.

It is the event `pi1GraphIsVerifier` needs. `breaks_cases` splits on `MergeHazard` exactly at a stream with
`Pi1GraphAccepts`, and `pi1GraphIsVerifier` is proved for `¬ MergeHazard` at every permutation. `Pi1HazardAccepted`'s
`pi1GraphChecks` is weaker than `Pi1GraphAccepts`, which is harmless.

`εh` is justified nowhere beyond `hazard_prob` (a uniform `t`, `p_0` fixed), as documented. It is plausible: `t` is
full-width (`sample F`, not narrow), drawn after `p_0`, and `Z_bad` has at most `2^19` roots.

**5. Completeness.**

- **The prover.** `pi1Rec3ProverKF` has the right hashes. Fiat–Shamir (IV, seed, stream, Flock's draws) is the pure
  `keccak256`. The trees and WHIR openings (with their grinding) are over `π`, matching the graph, the contract's IV
  and `PCS_OPEN` in the model. It is not tested against the Rust prover (finding 1).
- **δ2** is not the full failure probability. It bounds `Pr[graph accepts ∧ contract rejects]`. The full bound is
  `δ1 + δh + δ2` in `recCompleteness_pi2_rec3_kf_fs`, with `δ1` heuristic (RPM reading proved) and `δh` heuristic
  (no RPM reading, finding 3).
- **`Pi1CompletenessKeccak`** at this prover is non-trivial. It is equivalent to `Pi1CompletenessFs D (pure ∘ keccakF1600)`,
  its RPM reading holds at `2^-167`, and off `BadKF` the Keccak verifier provably accepts.
- **`contract_rejects_le`** has no `¬ BadKF` condition (finding 5).

**6. Overclaims.** Findings 1, 3 and 6. The `_fs` soundness forms with false premises are documented as such
everywhere I looked (`Security.lean`, `Reduction.lean`, `FsClosed.lean`, the three READMEs).

## Checked and found sound

- **First review, finding 1 (long IVs).** Fixed. Every per-IV premise is at `iv.length = 32`. Consumers reach
  `pi1IvAt` via `pi1IvAt_length`, proved for both branches of `contractIvForWith`. The residual is `IvChecked`
  (finding 2 here).
- **First review, finding 2 (trivial hazard).** Fixed as above.
- **First review, finding 3 (Fiat–Shamir premises false).** Fixed by `RecKnowledgeSoundnessReduction`. The Props are
  kept and labelled false as stated.
- **First review, finding 4 (prover over `π`).** Fixed. `pi1Rec3ProverKF_fs_kf` holds by `rfl`, and the prover's
  trees are the verifier's setup trees: `keccak_accepts` is stated at `setupTreesWith` of the same permutation.
- **First review, finding 5 (no `Real` deployment).** Fixed. `DigestChecked` and `SetupRootChecked` are evaluated as
  stated, and are still used by no proof (documented).
- **First review, finding 6.** Fixed except the `Classical.choose` witness item.
- **The reduction's inequality.** `breaks_cases` covers every break. The three events' bounds are the three couplings,
  and the summands are exactly `RecKnowledgeSoundnessReduction`'s.
- **`delta2_kf_le`** is literally `Pi2Alpha.delta2_alpha_le`. The expression is identical (`alphaBound` is
  `Pi2Sim.alphaBound` under `open`).
- **No `implemented_by`/`extern`** in the evaluated code paths (`formal/` and leanerVM, grep).

## What was run

- `StatementReview2.lean`: `strict_eq` and `keccak_eq_verifierRec3`, on the three axioms (h1,
  `/root/pcs-quotient-fv/review2`, a copy of `rec-iv` at f774b11).
- `rec-iv-sample 3 0`, `3 3`, `3 1000` (h1, `review2`): still running at hand-off. The reference IV's line is printed;
  the per-IV lines are pending (finding 2).
