<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# WhirBridge: our WHIR openings under leanerVM `mumbai`'s proofs

`crates/quotient/src/opening.rs` opens every claim on a committed table with leanVM's WHIR, unchanged.
[leanerVM](https://github.com/Verified-zkEVM/leanerVM) `mumbai` (commit `6175f1a0`, MIT OR Apache-2.0;
its `leanvm-rev` is leanVM `c445e3d5`, the commit our `crates/verifier` is vendored from) proves leanVM's
verifier knowledge sound. This package states, in Lean, how much of that covers **our** use, and proves
what follows from mumbai's theorems. Everything here is sorry-free and depends on `propext`,
`Classical.choice` and `Quot.sound` only.

| File | What |
|---|---|
| `WhirBridge/Opening.lean` | `openingCheck`: `opening::verify` as a program of mumbai's verifier language, line by line (`Layout`, `Layout.new`, `eqBits`, `lambdas`, `target`, `parts`, `weight`). **`openingCheck_eq`**: it *is* mumbai's `verifyStackedOpening log_n R (stackClaims L claims)` after the length check. **`isMultiaffine_claimWeight`**: each claim's weight is multiaffine on the stack's `log_n` coordinates. |
| `WhirBridge/Sound.lean` | **`openingSpec`**: round-by-round soundness of `openingCheck` for every admissible layout and every list of claims, from mumbai's `stackedSpec` with the deployed codes. The numbers (`whirEps_le`, `eBatch_le`, `eBatch_one`, `eBatch_two`, `listMax_ours`), our three layouts (`witnessLayout`, `wiringLayout`, `quotientLayout`, transcribed from `protocol.rs`) and `layouts_ok`. |
| `WhirBridge/Table.lean` | **`holds_iff`**: a stack satisfies a claim's stack weight exactly when the **table** it stands for has the claimed multilinear value; **`openingDoom_iff`**: mumbai's doom is "every candidate's table violates a claim". `layouts_valid`. |
| `WhirBridge/Variant.lean` | **`variant_sound`**, **`variant_sound_table`**: Fiat–Shamir soundness in the two-oracle random-oracle model, from mumbai's `romSound`, of the opening **with leanVM's transcript shape** (root absorbed as commitment 0), for a fixed statement, the second in table terms; `variant_bound_le`: at most `2^-63` against `2^64` queries. |
| `Test/Check.lean` | Runs `openingVerifyWithHash` (the Lean `opening::verify`, mumbai's Keccak) on an opening proof made by the Rust prover (`crates/quotient/tests/whir_bridge_vector.rs`: two claims, 27 lanes out of order with a gap, `placed` short of the stack, the pruned paths expanded): **the honest proof is accepted**, a wrong value, a changed stream scalar and a changed leaf word are rejected (14 s, interpreted). |
| `WhirBridge/Gaps.lean` | `openingVerifyWithHash`: **our actual transcript** compiled (root hashed into the seed); `OpeningRomSound`: the theorem it needs, stated and not proved; the list of missing pieces. `layouts_nodup`. |

## Building

The package builds against a built checkout of leanerVM placed at `../leanervm` (so `formal/leanervm`
here, gitignored), sharing `lean_vm`'s packages (`packagesDir`), so nothing is fetched or rebuilt:

```sh
git clone https://github.com/Verified-zkEVM/leanerVM ../leanervm
cd ../leanervm && git checkout 6175f1a07f0dc33bd3d640de0063d1006143ee91 && cd lean_vm
lake exe cache get && python3 -I ../lake-build.py . LeanVM     # several CPU-hours
cd ../../WhirBridge && lake build                                # a minute or two
cargo test -p quotient --release --test whir_bridge_vector -- --ignored   # from the repository root
lake env lean --run Test/Check.lean ../../target/whir_bridge_vector.txt
```

On `h1` it lives at `/root/pcs-quotient-fv/whir-bridge` next to `/root/pcs-quotient-fv/leanervm`. The
bridge needs only `lean_vm`'s protocol modules (`LeanVM.Protocol.*`, not the guest's kernel-checked
certificates): `python3 -I ../lake-build.py . LeanVM.Protocol.Whir.Sound.Spec
LeanVM.Protocol.Whir.Params.Deployed LeanVM.Protocol.EndToEnd.Sound.Assemble LeanVM.Protocol.LeanVMSound`
builds them in about 6.5 minutes from mumbai's Mathlib cache.

## The Rust against mumbai's model

mumbai's `verifyWhir` (`Statement/LeanVmVerifier.lean:1505-1553`, a transcription of `verifier.py` at
`c445e3d5`) against the vendored `crates/verifier/src/whir.rs`, and `openingCheck` against
`crates/quotient/src/opening.rs`. The vendored `whir.rs`, `transcript.rs`, `merkle.rs`, `multilinear.rs`,
`field.rs` and `hash.rs` are byte-identical, past their two-line headers, to leanVM `c445e3d5`'s (checked
against a fetch of that commit, mumbai's `leanvm-tree.sh`), so what mumbai's fuzzing establishes of leanVM's
Rust verifier holds of ours.

* **Parameters.** `derive_config` (`whir.rs:34-60`) is `Whir.ladder` (`LeanVmVerifier.lean:110-161`): the
  same folds (6, then 4 or what remains while more than 5 variables remain), rate rule, window `15..28`,
  rates `1..4`; the query table `WHIR_QUERIES` (`whir.rs:20-25`) is `queryTable` (`:126`), checked equal
  entry by entry (56 rows). `QUERY_GRINDING_BITS = 17` is `queryGrindingBits`.
* **The level loop** (`whir.rs:154-269` / `whirLevels`, `:1505-1546`): the first round polynomial, the fold
  rounds, the next commitment and its out-of-domain claim, the proof of work, `sample_queries`
  (`whir.rs:72-87` / `sampleQueriesAux`, `:1392`), the batching challenge, the level-0 rows reversed and
  dotted with `eq_kernel` (`whir.rs:204-215` / `:1530`), the deeper rows through `ext_row`, the glued claims
  (`whir.rs:223-239` / `glue`, `:1490`), the tail rounds, and the terminal check with the weight read at
  `point[6..] ++ point[..6]` (`whir.rs:261` / `:1542`), `induced_weight` (`whir.rs:108-123` /
  `inducedWeight`, `:1437`): the same operations in the same order. **No mismatch** in the WHIR verifier
  beyond these, none of which matters for soundness:
  - **`placed` and pruned paths.** The Rust level-0 rows carry `ceil(placed / 2^(log_n-6))` words, the rest
    of each 64-word leaf a zero prefix rebuilt by `PrunedMerklePaths::expand` (`whir.rs:195-202`,
    `merkle.rs:79-146`, the prefix at `:101`); mumbai's `Proof` has one full path per query and no
    `placed` (`commitStack`, `:1556-1562`, width `2^6`). The expansion checks the same roots, so it only
    restricts what is accepted; it is not formalised (mumbai says the same of leanVM:
    `Statement/LeanVm.lean:60`).
  - **A final level with no tail round** (`message_log = 0`): the Rust checks `weight · residual = 0`
    (`whir.rs:244-266`), mumbai's `tailRounds 0` fails (`:1477`). No ladder reaches it: the last level
    leaves 2 to 5 variables.
  - The Rust `eq_eval`/`dot` assert equal lengths and `induced_weight` checks its point's length, where
    mumbai's truncate (`multilinear.rs:72-88`); every call site passes equal lengths.
* **The opening** (`opening.rs:222-288` / `openingCheck`): the length check, `λ`, `λ_i = λ^i` (the Rust
  builds one power for no claim, never read: `dot_lambdas`), the target, and the weight closure: per
  claim `eq(p[..ℓ], x[..ℓ]) · Σ_l λ_i · eq_bits(p[ℓ..], block_l) · eq(bits(l), x[ℓ..])`, transcribed
  fold by fold. Its `F192` lane weights lifted by `ext` (`opening.rs:201-203`) are the verifier's `E`:
  both fields are `K[y]/(y^3+y+1)`, `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` (`crates/primitives/src/field/gf2_64x3.rs:3`,
  `crates/verifier/src/field.rs:3`).
* **Executed**: the Lean mirror with the deployed Keccak accepts a proof of the Rust prover, so the seed's
  bytes, `LABEL`, `λ`, the target, the weight closure and mumbai's `verifyWhir` agree with `opening::verify`
  on it (`Test/Check.lean`); test evidence, as mumbai's for leanVM.
* **The one mismatch that matters is the transcript, not the verifier**: `verify_whir` takes the root
  as an argument (`whir.rs:148, 157`) and `opening::verify` seeds its duplex with
  `(keccak256(LABEL), keccak256(root ‖ claims))` (`opening.rs:151-161, 233-234`), never absorbing the
  root; mumbai's model reads every root from the proof (`Prog.commit`, absorbed as two scalars,
  `LeanVmVerifier.lean:1556-1562`, `WithHash.lean:106`). See the gaps.

## What covers us

**mumbai's `stackedSpec`** (`lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean:273`), through `whirSpec`
(`:135`), is stated for **any** list of stack claims `(w, v)` whose weights are multiaffine on the stack's
`μ` coordinates, `w : List E → E` an arbitrary function: our closure qualifies. Its hypotheses and how
they are met:

| Hypothesis | Met by |
|---|---|
| `Whir.ladder μ R = some (level :: rest)`, `level.fold = 6`, `6 ≤ μ` | admissible `(μ, R)`: `15 ≤ μ ≤ 28`, `1 ≤ R ≤ 4` (`exists_ladder`, `deployed_spec_hyps`); ours `μ ∈ {24, 25, 28}`, `R = 1`, for every `13 ≤ log_rows ≤ 22` (`layouts_ok`) |
| `(codes 0).κ = μ − 6`, `(codes 0).R = R`, `LadderArith`, `whirEps ≤ εmax` | the deployed codes, certified for all 56 shapes by kernel evaluation (`Params/Deployed.lean:179`, `shapeOK_all`) |
| every claim's weight multiaffine on `μ` coordinates | `isMultiaffine_claimWeight` (proved here) |
| the doom `StackedPre`: the level-0 commitment has the stack's shape and every candidate of its word (the Johnson list at level 0's threshold) violates a claim | `openingDoom_iff`: every candidate's **table** violates a claim (proved here) |

`openingSpec` packages it for `openingCheck`; `variant_sound` composes it into mumbai's `romSound`
(`Compile/Rom/Sound.lean:196`).

## Errors at our sizes (rate 1/2)

| | witness | wiring | quotient |
|---|---|---|---|
| table variables / `log_n` / lanes (at `LOG_ROWS = 22`) | 25 / 25 / 33 | 24 / 24 / 64 | 30 / 28 / 59 |
| WHIR levels, queries | 5: 224, 56, 32, 23, 17 | 5: 224, 56, 32, 23, 17 | 6: 225, 56, 32, 23, 18, 14 |
| per-group escape `εmax` (every group after `λ`, discounted by its proof of work) | `2^-128` | `2^-128` | `2^-128` |
| batching challenge `λ` (the lead, `(J−1)·L₀/2^192`) | `0` (one claim) | `0` (one claim) | `≤ 2^-174` (two claims; `≤ 3564/2^192 ≈ 2^-180.2` with the shape's own list bound) |
| level-0 Johnson list `L₀` (candidates per root) | `≤ 7908` | `≤ 9952` | `≤ 3564` |

The `2^-128` is mumbai's certificate (`whirEps (deployedCodes μ R) config ≤ 2^-128`): at our three shapes
it certifies at `2^-128` and not at `2^-129` (`shapeOK 129 μ 1 = false`, evaluated), the query counts
being tuned to it. In the random-oracle model (`variant_sound`, the transcript with leanVM's shape, one
fixed statement): an adversary of `Q_A` queries makes the verifier accept while every candidate of the
extracted root word violates a claim with probability at most

`(Q_A + 10122) · (2^-128 + 5 (Q_A + 10122) / 2^256)`, about `Q_A · 2^-128`, at most `2^-63` for `Q_A ≤ 2^64` (`variant_bound_le`),

`10122` bounding the verifier's queries over every admissible shape (mumbai's `whirBound`).

## Assumptions

Keccak-256 and Keccak-f[1600] are independent random oracles (mumbai's two-oracle model; leanVM's own
theorem then moves to one random permutation). The adversary is classical and its code is fixed before
the oracles are sampled. The Rust verifier is mumbai's model (test evidence, not proof), and the pruned
paths expand as `expand` says (not formalised). Extraction is mumbai's straight-line `extract` (the word a
root commits to, read off the oracle's answers) and Guruswami–Sudan list decoding of the level-0 word
(`Statement/Extractor.lean`): the extractor returns the list, its running time read off its loops.

## Gaps

What mumbai's proofs do not cover of our opening (stated in `Gaps.lean`):

1. **Our transcript.** The root is hashed into the seed with the claims and never absorbed; mumbai's
   `romSound` needs every root read by the program (`runProofWithHash` starts with no commitment,
   `WithHash.lean:106`; `RootOk` forbids commitments in the seed's root history, `Compile/Rom/Decode.lean:253`;
   `Fail` recognises roots only inside permutation inputs, `RootOf`, `Compile/Rom/Log.lean:379`).
   `OpeningRomSound` states the theorem for `openingVerifyWithHash`; it needs a generalisation of
   `romSound` to seeds that carry roots (the root history holding `Ev.commit` with the `extract`ed word,
   `Fail` extended to the root inside the seeding hash input, `final_ineq` and `step_ineqH` re-proved).
   The certificate side is done (`openingSpec`). **Alternatively change the Rust**: absorb the root as the
   opening's first two stream scalars and seed with `keccak256(LABEL ‖ claims)`; then `variant_sound`
   applies.
2. **Adversarial statements.** `variant_sound` is for a fixed statement. Claims chosen by the adversary
   (ours come out of the reduction's transcript) need a family `Seeds (List Claim)` naming the claims
   (`Seeds.inj`) and one program for all statements, as mumbai builds for leanVM
   (`EndToEnd/Sound/Statements.lean`: `anyProgram`, `stmtHistory`, `anyCert`, `leanVmSeeds`). Note that
   `seed`'s encoding is injective only for a fixed layout (no lengths, and `LABEL` is shared by the three
   openings): fine for three fixed verifiers, not for one family over layouts.
3. **List decoding, no out-of-domain sample at level 0.** An accepted opening yields a candidate among
   the up to `L₀` tables of the root's Johnson list satisfying **all** its claims jointly (the quotient
   table's two claims bind one table), not a unique table. The reduction's soundness must hold for each
   of the `L₀` candidates fixed by each root before its challenges: a union bound multiplying its
   per-table error by `L₀ ≤ 2^13.3` (`listMax_ours`; mumbai's global bound `2^18`), as mumbai does for
   leanVM's phases.
4. **Composition of the three transcripts with the reduction's**: the reduction must read the words
   extracted when each root entered its transcript (mumbai's `extract_take_eq`).
5. **The random-permutation model** (mumbai's `LeanVMRpm.lean`), **pruned paths and `placed`**, and **the
   Rust being the model**: as above, not formalised here, as in mumbai for leanVM.
6. **Extraction from the adversary's queries only**: `variant_sound` reads the extracted word off the
   final cache (the verifier's answers included), as mumbai's `romSound` does; mumbai's further step to an
   extractor reading the adversary's transcript alone (`Sound.extractor_of_extracted`,
   `Sound.prEvent_logged2_root_le`, `LeanVMSound.lean`, at `Q_V/2^256`) is not taken here.
7. **Hiding** (zero knowledge of the openings) is out of scope (layer F3 of `formal/README.md`).

## Build on h1

leanerVM `6175f1a0` cloned at `/root/pcs-quotient-fv/leanervm`; `lake exe cache get` then
`lake-build.py` (10 jobs, 36 GB) of the WHIR and soundness modules: 931 modules in 6 min 30 s
(0.97 CPU-hours), then the whole `LeanVM` target (see the report for its time). The bridge builds in about
two minutes against it.
