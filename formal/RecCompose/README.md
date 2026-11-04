<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# RecCompose: the recursive verifier's end theorems

The recursive EVM verifier for leanVM 42422001 proofs (`crates/leanvm_rec`): the contract runs π2's verifier, then six
`PCS_OPEN` calls (π1's `C1`, `C2`, `F`; π2's `W`, the setup, `Q`). Its statements are `RecStatement`'s
(`RecStatement/Security.lean`), in two parts, since π2's circuit computes π1-rec3's Fiat–Shamir with the real
Keccak-f[1600] while π1-rec3's soundness is proved in the random-permutation model:

1. **π2's part, in the random-permutation model**: `RecKnowledgeSoundness2 D ε2` (if the contract accepts, π2's
   extractor outputs π1's stream on which π1-rec3's recorded graph over Keccak-f[1600] accepts, its three calls the
   contract's), `RecCompleteness2 D P1 P2 δ2`;
2. **end to end, against Lv42's `M3Holds`**: `RecKnowledgeSoundness D ε2 ε1 εh`, `RecCompleteness D P1 P2 δ1 δh δ2`,
   Props whose own hypotheses are `RecGraph.Pi1.Pi1GraphIsVerifier`, `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh` (and the
   completeness analogues): the Fiat–Shamir heuristic for Keccak-f[1600], justified by π1-rec3's random-permutation
   theorems (`UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`, `UniComplete.Rec3.uniCompletenessRec3_end_closed`)
   and `RecGraph.hazard_prob`.

This library proves part 1 from π2's layers, its bound in bits, and part 1 ⇒ part 2.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only
systemd-run --scope -p MemoryMax=10G lake build RecCompose     # the theorems; #guard_msgs checks their axioms
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check   # Pi2ViewChecked at two IVs (about 3 minutes, 3 GB)
python3 -I Review/RecSoundnessNumbers.py                        # ε2 = pi2Bound in exact rationals
```

## The end theorems (`End.lean`)

See the section "The recursive verifier" of [`../README.md`](../README.md) for the statements verbatim and the list of
named inputs; the files:

| File | What |
|---|---|
| `Basic.lean` | π2's outcome's fields; `W`'s candidates and their witness values as π2's extractor reads them; `pi1GraphAcceptsB_iff`; `recExtractFrom2_of_mem` (one accepted candidate suffices). |
| `Part1.lean` | `CallsPure`, `Pi2Extraction`, `Pi2Layers`; **`recKnowledgeSoundness2_of_layers`**. |
| `Circuit.lean` | `Pi2Layers.circuit` from RecCircuit's `pi1rec3_end` and `CircuitBridge`; `compile_ok` from the compiler's run on the emitted graph and `GraphsAgree`; `Pi1RootWordOk` (the root-word fix's named dependence). |
| `Numbers.lean` | **`pi2Bound`** (`ε2`), `pi2_rounds_le` (RecPiop's three rounds times their lists, at most `2^-140.60`), **`pi2Bound_le_bits`** (`≤ 2^-64` for `Q ≤ 2^64`). |
| `Part2.lean` | the derived adversaries (`hazardAdversary`, `pi1Adversary`), the three events, `ExperimentsAgree`, `HazardCoupling`, `Pi1Coupling`; **`recKnowledgeSoundness_of_part1`**. |
| `Complete.lean` | `CompletenessAgree`, `CompletenessPi1Coupling`; **`recCompleteness_of_part1`**. |
| `Layers.lean` | `Pi2FsLayer` (π2's Fiat–Shamir layer, proved in `FsClosed.lean`), `Pi2Tables` (the tables' layer, open), `Pi2Circuits`, `Pi2Facts`; `pi2Piop` (`RecPiop.piop` per setup), `hbind_of`, `indep_K`, `satisfies_congr`; **`pi2Extraction_of_layers`**, `pi2Layers_of`. |
| `Holds.lean`, `Chan.lean`, `Pi2Run.lean`, `CallsPure.lean` | postconditions in any lawful monad (`Holds`), the channel's reads (`Reads`), π2's run's public data independent of the permutation (`runWith_post`); **`callsPure`**. |
| `Rpm.lean`, `Couplings.lean` | the logging lemmas, eager comparisons per permutation; **`experimentsAgree`**, **`hazardCoupling`**, **`pi1Coupling`** (under `Pi1OpeningsAgree`). |
| `OpeningsAgree.lean`, `RunOpenings.lean` | **`pi1OpeningsAgree`** (from `pi1RunShape`, `pi1RunOpenings`, `pi1CallsShape_data`), **`pi1RunOpenings`**. |
| `RpmC.lean`, `Pi1Decode.lean`, `CompleteCouplings.lean`, `RunShape.lean` | eager comparisons, π1's call bytes decoded back; **`completenessAgree`**, **`completenessPi1Coupling`**, **`pi1RunShape`**. |
| `Tables.lean` | **`pi2Tables`** (the tables' layer, from `Pi2SetupColumns`), `cells_wFold`, `claim_wFold`, `claim_quotient`, `claim_sum`, `claim_setup`, `sum_novP_omega`. |
| `Bridge.lean` | **`circuitBridge`** (from `StatementPortMeaning`, `ZeroPortsMeaning`, `CallWordsAgree`, `Pi1CallsLayouts`). |
| `End.lean` | `recKnowledgeSoundness2_real`, **`recKnowledgeSoundness_end`**, `recKnowledgeSoundness_end_real`, **`recCompleteness_end`**, **`recKnowledgeSoundness_end_fs`**, **`recCompleteness_end_fs`**. |
| `ViewDefs.lean`, `View.lean` | **`viewOf`** (`pi2::adapt` transcribed), `callsOf`, `validB`, **`viewCheck`** (evaluated by `rec-view-check`, `RecComposeTest/ViewCheck.lean`); the slots, `groupsOf_perm`, `groupsOf_mem`. |
| `Valid.lean` | **`validB_sound`**: `validB` gives `RecPiop.Circuit.Valid` of `toPiop`. |
| `FactsAlg.lean`, `FactsSpec.lean`, `FactsSpecOf.lean` | the formulas' and terms' values, `pubOfC`; `Data`'s facts by kernel decision; **`specOf_data`**. |
| `Facts.lean` | `Pi2ViewChecked`; **`pi2Facts`** (`Pi2Facts D C`), `pubOfC_canon`, `pi2Facts_pubOf`. |
| `Meanings.lean` | **`statementPortMeaning`**, **`zeroPortsMeaning`**, **`callWordsAgree`** for `pi2Facts`. |
| `Layouts.lean` | **`pi1CallsLayouts_of_real`** (`stackLayout_words`). |
| `Final.lean` | **`recKnowledgeSoundness2_final`**, **`recKnowledgeSoundness_final`**, **`recKnowledgeSoundness_final_fs`**: the end theorems from the named inputs left. |
| `FsDefs.lean` | π2's Fiat–Shamir layer's objects: the chain `pi2Spec` (`ChainSpecU` over π2's transcript: the label `name ‖ iv ‖ input`, the public data's 472 bytes before `W`'s root), the proof `P2Pf` and its view, the six openings `p2Ops` (π1's `C1`, `C2`, `F`, π2's `W`, the setup, `Q`), the setup's stacks `p2Stk`, the composed setup `p2Setup`, the IV `p2IvKC4`, the composed verifier `p2Ver`, the bridge facts' Props. |
| `FsOps.lean` | the openings' `OKP`, coverage, `hS_p2` (the setup's claim), `ClaimOn` as F2's `tableEval` on public layouts (`claimOn_iff`, `readEntry_public`), the shapes at once (`p2Shapes`), `maxErrK_p2`. |
| `FsSetup.lean`, `FsExtract.lean`, `FsWalk.lean` | **`pi2SetupBridge`**, the setup's facts and `okp_setupOp`; **`pi2ExtractBridge`**; **`pi2Walk`** (π2's run is the chain), **`pi2WalkReject`**, `pi2Scalars_real`. |
| `FsVerifier.lean`, `FsCouple.lean`, `FsCost.lean` | **`pi2VerifierBridge`** (the contract's six calls below the composed openings), **`pi2GameLeV`** (the coupling), the composed verifier's cost, the IV moved into the adversary (`expU_p2IvAdv`), `hlab_p2`. |
| `Pi2Witness.lean` | **`pi2WitnessComplete hD C hchk : Pi2WitnessComplete D C (pi2Facts hD C hchk)`** (π2's completeness input 1): on a stream π1-rec3's graph accepts, RecCircuit's honest witness (`RecCircuit/Complete.lean`) and the public values `valuesOf` (the roots' 32 bytes of the stream, the element ports' values) are an honest witness; the ports: the statement's the input's words, the roots' the stream's, the zero ports `0` (the graph's checks, `zero_port_sat`). |
| `FsGame.lean`, `FsClosed.lean` | **`pi2FsLayer_of`** (through `Compose.knowledgeSoundness_listChainU_closed128S`, `prEvent_doomF_le`, `prEvent_pairTr_expL_le`, `le_pi2BoundE`); **`pi2FsLayer_real`** (`Pi2FsLayer D` proved at the real deployment); **`recKnowledgeSoundness2_closed`**, **`recKnowledgeSoundness_closed`**, **`recKnowledgeSoundness_closed_fs`**: `Final.lean`'s end theorems without `hfs`, `Fa`, `hstmt`, `hzero`, `hcalls`, `hlay` (their inputs `C`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C`). |

## The statements' fixes (in `RecStatement/Security.lean`, found by this composition)

1. **π2's extractor searches by the whole acceptance.** It searched `W`'s list for the first candidate whose π1
   stream passes the graph's checks. A word within the list-decoding radius of two codewords (rate `1/2`: both within
   Johnson's `0.29`, the first within `1/4`, so the unique decoder lists it first) can make that candidate's stream an
   honest π1 proof of another transcript while the openings' claims hold of the second: the extractor would output a
   stream whose calls are not the contract's, and `RecKnowledgeSoundness2` would fail. It now searches by
   `pi1GraphAcceptsB` against the contract's π1 openings read off the calldata (`pi1OpsOf`).
2. **The derived π1 adversaries are given the setup's evaluations.** π2's extractor reads them. With the roots alone,
   the adversary built from π2's must recompute the setup: `ε1` would be charged at its `2^27` and more extra calls, not
   at `Q`, and π1-rec3's extractor would read a transcript that holds them, not π2's adversary's.
3. **π2's completeness is for π1-rec3's prover, on honest statements.** Stated for every `P1`, a `P1` of unbounded
   queries can grind its proof (the graph still accepting) until π2's honest run hits a degenerate challenge (`all = 0`).

## The root-word finding

π2's stream carries π1's `C1`, `C2` roots as `rootWordOfBytes` of π1's stream bytes (each 16-byte half reversed): the
real vectors' π2 stream starts `b25c056f…cef8`, π1's `C1` root is `f30c504d…b05f`. The contract decodes that word to
`digestOfBytes32 raw`, while π1-rec3's verifier and WHIR open at `rootOf (halves raw) = rootOfWord raw` (evaluated).
So `Pi1GraphAccepts`'s roots disagreed on honest proofs, and the contract opened π1's commitments at other digests.
The fix (`fix-pi1-root`, merged at `leanvm-rec` 613b2fa) is in π1's prover: it now writes each root as its root word
(`hash_to_scalars`), as π2's prover and UniComplete's honest prover do. `RecCircuit.pcsWord` passes stream roots as
they are, so `Pi1RootWordOk` is `pi1RootWordOk` (`rfl`).

## π2's completeness, closed (`lean-pi2-run`)

| File | What |
|---|---|
| `Pi2P1.lean` | `p1k D` (π1-rec3's honest prover over the two calls), `pi1Rec3Prover D`. |
| `Pi2SimMorph.lean` | π2's code (setup, IV, graph verifier, run, contract, prover, `expW2`, stages) commutes with monad morphisms; `sim_expW2`, `sim_stageA/B/C`. |
| `Pi2SimAt.lean` | `stream_split`, `tInput_pre2_length` (`536` bytes), `stagedAt`, `runAt_staged`, **`stagedAt_good`**. |
| `Pi2SimExp.lean` | `perm_kc`, `experiment_eq_kc`, **`pi2ExperimentLe_p1k`**; `Pi2RunAt` as stated is not provable (no honest witness). |
| `Pi2SimCore.lean` | `rejects_at_good`, **`rejectGood_pi2_good`** (no `Pi2RunAt`). |
| `Pi2Chain.lean`, `Pi2TFresh.lean`, `Pi2TFreshPi2.lean` | `Holds2` (`Pi2AlphaFresh` for the false `Pi2HashBeforeAlpha`), `recCompleteness2_of_staged2`, `delta2'`; **`pi2TFresh_of`**. |
| `Pi2RunDuplex.lean`, `Pi2RunCost.lean` | **`pi2RunDuplex_p1k`**, **`pi2RunCost_p1k`** (`pi2RunN ≤ 2^50`). |
| `Pi2SimEnd.lean`, `Pi2Closed.lean` | **`recCompleteness2_pi2_rec3_final`**, **`recCompleteness_pi2_rec3_final_fs`**, `delta2_rec3_le` (`≤ 2^-164`). |
