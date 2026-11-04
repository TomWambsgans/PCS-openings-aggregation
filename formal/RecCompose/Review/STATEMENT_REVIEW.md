<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Adversarial review of the recursive verifier's end statements

Reviewed at `main` f7c640f (`lean-pi2-alpha`). It covers the statements and their definitions, not the proofs:
`RecCompose.recKnowledgeSoundness2_closed`, `recKnowledgeSoundness_closed`, `recKnowledgeSoundness_closed_fs`
(`FsClosed.lean`); `RecCompose.Pi2Alpha.recCompleteness2_pi2_rec3_closed`, `recCompleteness_pi2_rec3_closed_fs`,
`delta2_alpha_le` (`Pi2AlphaEnd.lean`); the Props of `RecStatement/RecStatement/Security.lean`, `RecDeployment.Real`,
`Pi2Circuits`, `Pi2ViewChecked`, `GraphsAgree`.

The Lean evidence is in [`StatementReview.lean`](StatementReview.lean). It elaborates on h1 against the built
`pi2-alpha` tree with no error and no `sorry`, on `propext`, `Classical.choice`, `Quot.sound`:

```sh
cd formal/EndToEnd && systemd-run --scope -q -p MemoryMax=10G lake env lean ../RecCompose/Review/StatementReview.lean
```

## Findings, ranked

### 1. `Pi2Circuits D` and `Pi2ViewChecked C` quantify over every `List UInt8`, so at long IVs they are false (statement wrong: every end theorem is vacuous; evaluated)

`Pi2Circuits.compile_ok : ∀ iv, compile (ofRG pi1Graph rootsAt iv) = .ok (compiled iv)` and
`Pi2ViewChecked C : ∀ iv, viewCheck (C.compiled iv) = true` range over IVs of **every length**. The compiler hashes the
IV in the seed (`constantBits NAME ++ constantBits r.iv ++ publicCopy`, `Compile.lean:181`). Every 136 bytes of IV
add one Keccak-f[1600] instance, and the circuit's size is computed from its rows (`Layout.lean:399`,
`logRows := log2 (nextPow2 totalRows)`). Past some length, `viewOf.logN ≠ 24 = Data.circuit.logN` (or the compiler
fails), and then no `C : Pi2Circuits D` with `Pi2ViewChecked C` exists.

**Evaluated: the compiler rejects π1-rec3's graph at a 49,152-byte IV.** The program is [`LongIv.lean`](LongIv.lean)
(this directory), built in the h1 copy as an executable `rec-long-iv` (its `lean_exe` stanza is not committed). It runs
`RecCircuit.compile (ofRG Emitted.graph Emitted.rootsAt (List.replicate 49152 0xff))`, compiled code as
`rec-view-check`, and took about 55 minutes and 8.8 GB:

```
iv of 49152 bytes: the compiler rejects the graph: the checker rejects the circuit: graph
```

So `compile_ok` fails at that IV and **`Pi2Circuits D` is uninhabited for every `D`**. This rests on compiled
evaluation, the same trust as the repository's own "checked by evaluation". Independently of the checker, an IV of
`136 · 2^21` bytes adds `2^21` Keccak-f instances, more rows than `2^20`, so `viewOf.logN > 24` and `viewCheck` fails.

Every theorem reviewed takes `C : Pi2Circuits D` (and `hchk`; `pi2Facts hD C hchk` is built from them), so **every
reviewed end theorem, soundness and completeness, is vacuously true as stated**. Only 32-byte IVs are needed:
`pi1IvAt` returns `digestBytes` of a Keccak-256 output.

Even at 32-byte IVs the premises are "checked by evaluation" at **two** of the `2^256` IVs (`rec-view-check`: π1's
reference IV and the zero IV). The `∀ iv` is genuinely needed in the model, because the setup's roots, and hence π1's
IV, are random under `π`. No uniformity argument (that the compiler's structure does not depend on the IV's value) is
stated or proved. Some IV dependence is visible: κ has 19,143 entries at the reference IV and 18,997 at the zero IV
(`view9b.log`). `formal/README.md`'s table says "the Lean compiler … accepts π1-rec3's graph at every π1 IV … checked
by evaluation", which overstates it. `Pi2Circuits.stream_eq` (`∀ iv ∀ w, D.pi1Stream w = streamW … iv w`) is a
functional equation that no evaluation checks, at any IV.

**Fix.** (a) Restrict `compile_ok`, `stream_eq`, `Pi2ViewChecked` and `SetupFromCompiler` to `iv.length = 32` (or to
the IVs in the range of `pi1IvAt`). (b) Prove the IV-uniformity of the compiler. The IV enters only as the values of
`fresh` cells in the seed's single block when `|NAME| + 32 + 32 ≤ 135`. Show that `compile`'s structure (regions,
blocks, ports, `viewOf`, `callsOf`, `validB`, `streamW`) does not depend on those values, and that κ's values do in the
way `SetupFromCompiler` takes. Until (b) is done, call the premise "evaluated at two IVs, assumed at the others".

**Fixed, (a) only** (`fix-rec-iv`). `Pi2Circuits.compile_ok`, `stream_eq`, `Pi2Layers`' fields, `Pi2ViewChecked` and
`RecDeployment.SetupFromCompiler` take `iv.length = 32`. Their consumers reach `pi1IvAt` through
`RecDeployment.pi1IvAt_length` (`RecCompose/IvLength.lean`; π1's contract IV is `digestBytes` of a Keccak-256 output)
and `Pi2Circuits.compile_okAt`, `stream_eqAt`. The checker itself rejects every other length (`graphOk`:
`r.iv.length == 32`), which is the "graph" rejection of the 49,152-byte run. At the real deployment
(`RecCompose/RealDeployment.lean`) the per-IV premises reduce to one `Bool` per IV, **`IvChecked`**: `ivCheck iv` is the
compile, `viewCheck`, and `streamAgree` with the reference IV's circuit. `stream_eq` follows from `streamAgree` at every
IV (`streamW_eq_of_streamAgree`), so it is no longer an unchecked functional equation. `SetupFromCompiler` holds by
construction. `IvChecked` is **stated for every 32-byte IV, evaluated at three** (π1's reference IV, the zero IV, the
all-ones IV: `rec-real-check`) and assumed at the others.

(b) is **not done**. The κ difference is accounted for. The IV's 256 bits are the seed's permutation-input constants,
`fresh 0`/`fresh 1`, and a `0` is not stored in the sparse `κ`. So 19,143 − 18,997 = 146 = the reference IV's one-bits.
Besides `κ`, the IV is in the seed sponge's message and block-0 input traces, in `nodeOk`'s `seedMessage iv` and in
`graphOk`'s length check. Proving (b) means a relational simulation of the builder (`compileM`, the templates,
`finish`: about 1,200 lines of monadic code, `κ` being write-only until `finish`) and a transfer of the checker
(680 lines) and of `validB`. The 256 IV positions also have to be shown to be expression slots that no other gate
reads `κ` at. That was out of reach here. The three evaluated IVs set each IV constant both ways.

### 2. The end-to-end knowledge-soundness bound is at least 1 (statement wrong, proved)

`Pi1HazardKeccak D εh` cannot hold with `εh Q < 1` for any `Q`, so `recKnowledgeSoundness_closed_fs` (and the Prop
`RecKnowledgeSoundness D pi2Bound ε1 εh` of `recKnowledgeSoundness_closed`) only ever give a bound
`pi2Bound Q + ε1 Q + εh Q ≥ 1`.

**Proof** (`StatementReview.lean`):
- `zBad_eval_zero`, `hazard_at_zero`: `y_0` is a linearised polynomial `Σ a_m X^(2^m)`, so `Z_bad(0) = 0` and
  `RecGraph.Hazard p0 0` holds for every `p0`.
- `challenges_empty`: on the empty stream π1-rec3's run (`runWithFs … reference iv input #[] …`) stops at the first
  read (`countBits` → `takeBytes` → `streamExhausted`) and draws no challenge. So `t = ch.getD 49 0 = 0`.
- `mergeHazard_empty`: so `MergeHazard keccakF1600 iv input #[]` holds for **every** IV and input.
- `pi1HazardKeccak_trivial : Pi1HazardKeccak D εh → ∀ Q, 1 ≤ εh Q`. Its witness is an adversary that makes no
  query and outputs the empty stream.
- `recKnowledgeSoundness_fs_bound_trivial : Pi1HazardKeccak D εh → 1 ≤ pi2Bound Q + ε1 Q + εh Q`.

The same default reaches the derived adversary. `Part2.hazardAdversary` outputs `(recExtractor2 …).getD #[]`, the
empty stream whenever π2's extractor fails, which is a hazard by `mergeHazard_empty`. So even the reduction form of the
theorem, with its explicit derived adversaries, has a hazard term at least `Pr[π2's extraction fails]`.

The documentation says the opposite: `Security.lean` ("justified by `RecGraph.hazard_prob` (`2^19/|E|` a challenge)"),
`formal/README.md` ("the `_fs` forms keep only the Fiat–Shamir heuristic") and `RecCompose/README.md`.

**Fix.** Ask for the hazard only on runs that reach challenge 49, for example on streams whose graph checks hold
(`pi1GraphChecks iv input s = true`), in `MergeHazard`, `Pi1HazardKeccak`, `Pi1HazardKeccakHonest` and `HazardEvent`.
`breaks_cases` only needs the hazard on streams with `Pi1GraphAccepts`, so the coupling survives. Finding 3 still
applies after this fix.

**Fixed** (`fix-rec-hazard-fs`). `RecGraph.MergeHazard` asks `50 ≤ ch.size` (the run draws `t`), `NoHazardAt` likewise,
and `RecGraph.Pi1.pi1GraphIsVerifier` is re-proved on the larger domain (`not_noHazard_of_mono` keeps the drawn count).
The soundness hazard is `RecStatement.Pi1HazardAccepted` (`pi1GraphChecks` and `MergeHazard`) in `Pi1HazardKeccak`,
`HazardEvent`, `HazardCoupling`; `Pi1HazardKeccakHonest` reads the restated `MergeHazard`. `StatementReview.lean` now
proves `not_mergeHazard_empty`, `not_pi1HazardAccepted_empty`, `hazardAdversary_default` and
`emptyAdversary_hazard_zero` (the zero-query adversary hits the hazard with probability `0`). Not done: a
random-permutation proof of the hazard bound for the derived adversary (it needs the sponge-freshness argument of
π1-rec3's game at challenge 49); `hazard_prob` remains the per-uniform-`t` motivation.

### 3. The Fiat–Shamir premises are false as stated, for computationally unbounded adversaries (statement wrong)

`Pi1FsKeccak` and `Pi1HazardKeccak` quantify over every `OracleComp RandomPermutationOracles` adversary and count only
its calls of `π`, `π⁻¹`. Such an adversary may compute anything else for free, including Keccak-f[1600], which is a
fixed public function here. π1's challenges are Keccak-f[1600] of the stream, so the adversary can grind the clear
prover messages (or a root's bytes, which the graph does not open) offline at no query cost:

- **Hazard, even after fix 1.** Write an honest-looking π1 stream (the graph opens nothing, so the roots may be any
  bytes), then search offline over the free bytes until `t` lands on one of the `≤ 2^19` hazardous values. That is
  about `2^173` offline evaluations and zero queries. `Classical.choose` writes such an adversary directly whenever
  such a stream exists, which is heuristically certain.
- **`Pi1FsKeccak`.** Commit a non-satisfying table with `π` (a few honest-prover costs, `≪ 2^64` queries). Then, for
  each round, search offline over the prover message until the Keccak-derived challenge escapes the round's doom
  (`≈ 1/ε` tries). Open honestly. `uniExtractor` decodes the non-satisfying table, so the adversary breaks with
  probability ≈ 1.

"Justified by π1-rec3's random-permutation theorem" does not transfer. In the RPM every grinding step costs a query,
which is exactly what `uniKnowledgeSoundness_closed_rec3` charges. Against a fixed function the Fiat–Shamir heuristic
is a statement about *efficient* adversaries, and no Lean adversary class here expresses efficiency. So the `_fs` end
theorems are implications from premises that are, heuristically certainly, false. They are not "the Fiat–Shamir
heuristic" in the usual sense.

The `Pi1FsKeccak` docstring also says "against the adversaries of the recursive setup (those built from π2's: they run
π2's adversary and π2's extractor)". The definition quantifies over **all** `Pi1Adversary`.

**Fix.** State the end-to-end result as an explicit reduction, which the proofs already contain
(`ExperimentsAgree`, `HazardCoupling`, `Pi1Coupling`, `breaks_cases`):

```lean
theorem recKnowledgeSoundness_reduction … (A : RecAdversary) (Q : ℕ) (hQ : ∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) :
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D (recExtractor D) z] ≤
      pi2Bound Q
      + Pr{let z ← pi1HazardExperiment D (hazardAdversary D A)}[HazardOnAccepted z]          -- with fix 1
      + Pr{let z ← pi1KeccakSoundnessExperiment D (pi1Adversary D A)}[UniBreaksKnowledgeSoundness …]
```

Say in the documentation that the derived adversaries run in `A`'s time plus π2's extractor's (Guruswami–Sudan at
`2^24`, polynomial), and that the heuristic is applied by the reader to them. Keep `Pi1FsKeccak` and the others as
named Props, but document them as false for unbounded adversaries, or drop them.

**Fixed** (`fix-rec-hazard-fs`). `RecStatement.RecKnowledgeSoundnessReduction` (`RecStatement/Reduction.lean`) is the
reduction above, with the resource statements as conjuncts (each derived adversary makes at most `Q` calls of `π`,
`π⁻¹`); `pi1Adversary`, `hazardAdversary` moved there. `RecCompose.recKnowledgeSoundness_reduction` (`FsClosed.lean`)
proves it at `pi2Bound` from the same inputs as `recKnowledgeSoundness2_closed`, through
`recKnowledgeSoundnessReduction_of_part1`, `_end`, `_final`. The Prop-premise forms are its corollaries
(`recKnowledgeSoundness_of_reduction`), `Pi1FsKeccak` and `Pi1HazardKeccak` documented as false as stated for
unbounded adversaries. Completeness's `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest` quantify over one fixed honest
prover, the statement chosen before `π`, so no grinding applies there (given finding 4's fix).

### 4. The completeness theorems' π1 prover hashes its Fiat–Shamir over `π`, but the graph and verifier hash it over Keccak-f[1600] (statement wrong)

`pi1Rec3Prover D = uniProverRec3With (keccak256With queryPermutation) queryPermutation …`
(`StatementReview.pi1Rec3Prover_fs_over_pi`, by `rfl`). Its IV (`contractIvRec3Of H`), seed (`seedOf H`) and stream
(`proveStreamRec3With H`) are all Keccak-256 over the random `π`. The other side of the experiments hashes with the
real Keccak-f[1600]: `pi1GraphVerifierWith` (`RecGraph.evalGraphDeployed`, with IV `pi1IvAt`) in
`recCompletenessExperiment2`, and `pi1KeccakVerifierWith` (`pi1Iv`, `runFs`) in `Pi1CompletenessKeccak`. In the model
`π` is independent of Keccak-f[1600]. So the IVs differ (with probability `1 − 2^-256`), every challenge differs, and
π1's honest proof fails π1's checks (sumcheck consistency and the like) except with probability around `2^-180`.

Consequences:
- **`Pi1CompletenessKeccak D (pi1Rec3Prover D) δ1` holds only for `δ1 ≈ 1`.** So `recCompleteness_pi2_rec3_closed_fs`
  (and `recCompleteness_pi2_rec3_final_fs`, `recCompleteness_pi2_closed_fs` at this `P1`) gives no meaningful bound:
  `δ1 + δh + δ2 ≥ δ1 ≈ 1`.
- **`recCompleteness2_pi2_rec3_closed`** bounds `Pr[graph accepts ∧ contract rejects]`, and "graph accepts" is itself
  an event of probability around `2^-180` at this `P1`. The theorem is true and proved, but δ2 ≤ 2^-164 says almost
  nothing about the honest run. The work in the proof (the α chain, `stagedAt_good`, `pi2_accepts`) is real, but the
  conditioning event is the rare one.
- The type's own docstring says otherwise: `Pi1Prover` (Security.lean:649) is "π1-rec3's prover (in the recursion, its
  Fiat–Shamir over Keccak-f[1600], its openings over `π`)". So does `Pi1CompletenessKeccak`'s ("π1-rec3 is complete
  with its Fiat–Shamir instantiated by Keccak-f[1600]"): there only the verifier is instantiated.

**Fix.** Define the recursion's π1 prover with two hashes: Fiat–Shamir (IV, seed, stream) by Keccak-256 over
`pure ∘ keccakF1600`, and the commitments' trees and WHIR openings over `π`. `proveRec3With` must take a separate
Merkle hash for `commitReal`. Restate `RecCompleteness2` and the `_fs` theorems at that prover. Then
`Pi1CompletenessKeccak` is the honest-prover Fiat–Shamir heuristic (prover and verifier at the same function).
"Graph accepts" becomes the likely event, and δ2's analysis must be redone for it: α's chain counted π1's prover's
hashes as `π` queries, and they would no longer be.

**Fixed** (`fix-rec-pi1prover`). `RecCompose.Pi1KF.pi1Rec3ProverKF D` (`Pi1KF.lean`) is `uniProverRec3With2 hKF
(keccak256With queryPermutation) queryPermutation (flockProve3H hKF) D.pi1`: `proveRec3With2 Hfs Hm F` splits
UniComplete's hash into the Fiat–Shamir `Hfs` (IV, seed, stream, Flock's draws) and the trees' `Hm` (setup, commitments,
WHIR), `hKF = pure ∘ keccak256` (no query); `proveRec3With2 H H F = proveRec3With H F` by `rfl`. The theorems at it
are `Pi2KF.recCompleteness2_pi2_rec3_kf`, `recCompleteness_pi2_rec3_kf_fs` (`Pi2KFEnd.lean`), same δ2
(`εα = alphaBound ≈ 2^-207`, `εt ≤ 2^-200`, `δ2 ≤ 2^-164`): every count bounds the new prover's, whose Fiat–Shamir is
no oracle call (the old and new provers are two simulations of one three-call program, so the discipline, the block
count `2^47` and the census transfer, `Pi1KFTransfer.lean`). The old theorems are kept, marked superseded.
Non-vacuity (`Review/Pi1ProverReview.lean`, elaborated on h1): the prover's Fiat–Shamir is `keccak256` by `rfl`; off
π1-rec3's completeness bad events at its own challenges (`BadKF`) the Keccak-f[1600] verifier's run on its stream
draws its challenges (`pi1KF_challenges`) and `pi1KeccakVerifierWith` accepts its proof at every permutation
(`pi1KF_accepts`, `Pi1KFCore.lean`); `contract_rejects_le`: the contract's rejection is at most π1's completeness at
Keccak-f[1600] plus the honest hazard plus the bounded event. `Pi1CompletenessKeccak D (pi1Rec3ProverKF D) δ1` is
`Pi1CompletenessFs D (pure ∘ keccakF1600) δ1` (`pi1CompletenessKeccak_iff`), whose random-permutation reading
`Pi1CompletenessFs D queryPermutation deltaRec3` is proved (`pi1CompletenessFs_rpm`, `deltaRec3 < 2^-167`,
`Pi1KFRpm.lean`); the Keccak reading stays a heuristic premise. Not done: the graph form of `pi1KF_accepts` at a fixed
permutation (it holds in probability through `completenessPi1Coupling`). Found: `pi1KeccakVerifierWith` does not check
`r.matrices = none`, unlike `verifyWithFs` with the walk, so it accepts at least what π1-rec3's verifier accepts
(harmless for completeness; `verifierFs_le`).

### 5. `RecDeployment.Real` pins the Rust's digest and setup root, but nothing checks them against the Lean compiler, and no proof uses them (misleading; vacuity risk)

`Real` contains `digestWith (D.pi2 Data.pi1Iv) = Data.digest` and `setupTreeWith … .root = Data.setupRoot`, together
with `SetupFromCompiler` (σ, κ are the Lean compiler's). So `Real ∧ Pi2Circuits D` is satisfiable only if the Lean
compiler's σ, κ at the reference IV hash to the Rust's digest and root, that is, equal the Rust's. The repository
evaluates neither digest nor root for the Lean compiler's real circuit. `RecComposeTest/Pi2Prover.lean` checks setup
roots on `spec::example()` at `2^9`, `2^10` only, and `rec-view-check` compares the view (no σ, κ).

No proof in `RecCompose` uses these two components: grepping `hD.` finds `hD.1`, `hD.2.1`, `hD.2.2.1`, `hD.2.2.2.1`
and `hD.2.2.2.2.2.2`, never `hD.2.2.2.2.1` or `hD.2.2.2.2.2.1`. They are the only link between the model's contract,
which computes π2's IV from σ, κ over `π`, and the deployed contract, which hard-codes `inst.iv` computed by the Rust
from its digest and root (`contract.rs:74`). That link is therefore neither proved nor checked.

No `D` with `D.Real` is exhibited anywhere. `D.pi2` beyond the reference IV, `D.pi1Stream` and `D.pi1.prog` are free,
and they are pinned only through `Pi2Circuits` or not at all (`prog`).

**Fix.** Add an evaluated check (as `rec-view-check` does) that `digestWith` and `setupTreeWith` of the compiled
circuit at `Data.pi1Iv` give `Data.digest` and `Data.setupRoot`. Construct `realDeployment` (σ, κ from the compiler,
`pi1Stream := streamW` at the reference IV) and state `realDeployment.Real` as evaluated. Or drop the unused clauses
from `Real` and say plainly that the deployed IV constant is the Rust's, linked by test.

**Fixed** (`fix-rec-iv`). `RecCompose.realDeployment prog hprog` (`RealDeployment.lean`) is a concrete deployment.
π2's circuit at each IV is `pi2CircuitOf` of the Lean compiler's (`compiledAt iv`), π1's stream is `streamW` at the
reference IV, and the program is a parameter. `realDeployment_real : (realDeployment prog hprog).Real` follows from
`GraphsAgree` and two run-checked `Prop`s, `DigestChecked` and `SetupRootChecked` (Real's two clauses, as expressions at
`realPi2 Data.pi1Iv`), evaluated by `rec-real-check` (both `true` on h1: the digest `6fbe9c1c…e96c` and the root `792968e9…d870` are the Rust's; `IvChecked` at the reference, zero and all-ones IVs: `true`, `true`, `true`). `Review/NonVacuity.lean` builds `Pi2Circuits`,
`Pi2ViewChecked` and `Real` for `realDeployment prog0 rfl` from the evaluated `Prop`s and instantiates
`recKnowledgeSoundness_reduction`, `recKnowledgeSoundness2_closed` and `Pi2Alpha.recCompleteness2_pi2_rec3_closed`
there. The two clauses are still used by no proof; their role (the link to the deployed contract's constant IV) is
documented in `Real`'s docstring.

### 6. Documentation drift (misleading doc / cosmetic)

- `Security.lean:41–42` and the `RecKnowledgeSoundness` docstring still call `Pi1GraphIsVerifier` "provable, not yet
  proved". It is proved (`RecGraph.Pi1.pi1GraphIsVerifier`, three axioms).
- `RecCompose/README.md` gives `rec-view-check` as "about 3 minutes, 3 GB". `formal/README.md` says about 20
  minutes, and `view9b.log` shows 9.3 minutes per IV.
- The EVM bytecode of the recursive contract has no Lean link. The membership verifier has
  `Evm.evm_accepts_iff_verifyWith`; here the link is Rust parity tests (`contract.rs` `parity`, `parity_deployable`)
  plus the `RecStatement` differential runner (64 streams). The docs do not claim more, but the end-to-end summary
  ("the contract runs π2's verifier, then six `PCS_OPEN` calls. Its statements are RecStatement's") reads as if the
  statement's verifier were the deployed one. Say "by transcription and test".
- `pi2Prover` takes its witness by `Classical.choose` among `Pi2Good` witnesses, not the compiler's witness
  generation. The completeness argument works for any good witness. Stating `RecCompleteness2` for every
  witness-selection function satisfying `Pi2Good` would cover the deployed generator literally.
- `D.pi1.prog` is not pinned by `Real`. The theorems are for every program of the reference shape. That is a strength,
  but "leanVM 42422001's relation" should say "for the deployment's program".

**Fixed** (`fix-rec-iv`), except the `pi2Prover` item. `Pi1GraphIsVerifier` is called proved in `Security.lean`.
`rec-view-check`'s timing is about 9.3 minutes an IV in `RecCompose/README.md` and `formal/README.md`. The bytecode's
link "by transcription and test" is stated in `Security.lean`, `RecStatement/README.md` and `formal/README.md`. `D.pi1.prog`
is deliberately not pinned (`Real`'s docstring, `realDeployment`'s parameter): the theorems are for the deployment's
program, any program of the reference shape.

## Checked and found sound

- **The relation and the public input.** `RecBreaksKnowledgeSoundness` asks for `D.pi1.Relation w.1 z.1.1.1 w.2`
  (`M3Holds` of `leanIsaInstance blake2sFlockSpec prog` at the extracted row counts) for the public input the contract
  was called with (`z.1.1.1`). It is not decoupled from the calldata.
- **The extractor is explicit and computable.** `recExtractor2` (preimage replay of the adversary's log and the setup's
  evaluations, `committedWord`, fast, unique and Guruswami–Sudan candidates, `pi1GraphAcceptsB` against `pi1OpsOf`),
  then `uniExtractor`. All are `def`s. Its search tests the contract's own π1 openings (fix 1 of the statements), so
  the conclusion `Pi1GraphAccepts` with `contractPi1Openings` of the actual calls is not weaker than what the
  extractor decides.
- **The adversary class and query counting.** `QueryCostAtMost (A roots) permutationCallCost Q` counts the adversary's
  `π` and `π⁻¹` calls, with coins free. The setup's and the verifier's calls are in `pi2N Q = 2^33 + Q`. The openings
  term is `pi2N Q · 269 · 2^-137` (charged per query of the whole run). `pi2Bound_le_bits` holds for `Q ≤ 2^64`.
- **π2's part (`RecKnowledgeSoundness2`) would be meaningful once finding 1 is fixed** (restrict to 32-byte IVs).
  Its premises are `Real`, `C`, `hroots`, `GraphsAgree` and
  `hchk` (see 1 and 5). It is not circular: the conclusion is about π1's graph at Keccak-f[1600] on the extracted
  stream, and the premises say nothing about π1's soundness.
- **The Fiat–Shamir premises are about π1 only** (`pi1KeccakSoundnessExperiment`, `pi1HazardExperiment`). None
  mentions π2's contract, so none implies the conclusion by itself. The problem is that they are false (2, 3), not
  that they are circular.
- **The contract model.** `contractWith` matches `contract.rs` and `codegen.rs`. It runs π2's verifier (exact calldata
  length, as `CALLDATASIZE` at `codegen.rs:201–204`; `finish` in the model), then exactly six calls in the order
  `C1`, `C2`, `F`, `W`, setup, `Q`. π1's `F` root word and π2's setup root are the setup's. Each call is decoded under
  the registry (a known layout word, `k ≥ 1`, the exact length, elements' top 64 bits zero) and opened with π1's plain
  layout or π2's layouts.
- **`GraphsAgree`** is IV-independent, so one evaluation suffices. **`hroots`** is a field equation on `C`.
- **`Pi1GraphIsVerifier`** is proved for every permutation function, including Keccak-f[1600], so the `_fs` forms do
  not hide it.
- **Completeness's range.** `RecCompletenessWith` and `RecCompleteness2` hold for every `input`, `rows` with
  `RowsFit`, and every `M3Honest` stack. That is not a restricted subset, modulo the wrong π1 prover (4).
  `delta2_alpha_le`: `delta2' pi2RunN alphaBound (tFreshBound2 …) (…)` collects the copy, `t`, α, `εt`, grinding and
  RPM terms. `δ2` is π2's part only. The full failure is `δ1 + δh + δ2` (see 4).
- **`Pi2RunAt`, `Pi2HashBeforeAlpha`** are not hypotheses of the reviewed theorems, as documented. `Pi2AlphaFresh` and
  `Pi2WitnessComplete` are proved inside them.

## What was run

- `StatementReview.lean` (this directory), elaborated on h1 (`/root/pcs-quotient-fv/review-rec`, a `cp -a` of
  `pi2-alpha`): `pi1HazardKeccak_trivial`, `recKnowledgeSoundness_fs_bound_trivial` and `pi1Rec3Prover_fs_over_pi` on
  `[propext, Classical.choice, Quot.sound]`.
- The long-IV compile (finding 1): [`LongIv.lean`](LongIv.lean), run as the executable `rec-long-iv 49152` in the h1
  copy (its `lean_exe` stanza is not committed).
