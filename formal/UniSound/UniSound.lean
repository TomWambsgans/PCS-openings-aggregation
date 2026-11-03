-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Prog
import UniSound.FlockInterface
import UniSound.Prob
import UniSound.Sumcheck
import UniSound.Piop
import UniSound.PiopSound
import UniSound.Fs
import UniSound.Bus
import UniSound.Final
import UniSound.Mle
import UniSound.FsChain
import UniSound.FsOps
import UniSound.FsProof
import UniSound.FinalFs
import UniSound.FsCost
import UniSound.FsGame
import UniSound.FsCouple
import UniSound.FsWalk
import UniSound.FsExtract
import UniSound.FsVerifier
import UniSound.FsWalkProof
import UniSound.FsFinal
import UniSound.PendingLink
import UniSound.CodeBase
import UniSound.CodeTables
import UniSound.CodeBatch
import UniSound.CodeShape
import UniSound.CodeLink
import UniSound.FinalLink
import UniSound.FsSetup
import UniSound.Ids.Assembly
import UniSound.Ids.Align

/-!
# UniSound: knowledge soundness of the univariate verifier for leanVM 42422001

`UniStatement.UniKnowledgeSoundness D ε` (`formal/UniStatement`, iteration 2) for the main line
(Flock's slices in tower order, point claims), **`UniSound.uniKnowledgeSoundness`** and
**`uniKnowledgeSoundness_bits`** (`Final.lean`): `ε Q = uniBound (2^32 / |E|) Q`, at most `2^-61`
for `Q ≤ 2^64`, from the PIOP's round-by-round soundness (proved) and named hypotheses.

| File | What |
|---|---|
| `Prog.lean` | Chain programs: a verifier phase as rounds of reads, checks and challenges (`ChainProg`, `run`). |
| `FlockInterface.lean` | **The Flock hypothesis** `FlockSound κ`: Flock's front as a chain program, round-by-round sound from `FlockRegion.Holds` to its ring-switch claim and its pending matrices' reduction. |
| `Prob.lean` | Uniform challenges by counting (`prEvent_draws_card`), Schwartz–Zippel (`prEvent_root_le`), powers (`card_powComb_le`), the batch's two combinations (`prEvent_twoLevel_le`). |
| `Sumcheck.lean` | The batching sumcheck, generic in its weights (`SumOracle`, `ProdSum`, `step_sound`: `2 / |E|` a round). |
| `Piop.lean` | The PIOP's rounds (`uniRounds`), the identity model (`UniIds`), the states (`uniPre`, `uniPost`) and errors (`uniErr`). |
| `PiopSound.lean` | **`uniPiop`**: the PIOP is round-by-round sound (every round proved). |
| `Fs.lean` | The code-level link (`UniCode`), the last link (`UniFinal`), the Fiat–Shamir layer (`FsLayer`), the bound (`uniBound`). |
| `Bus.lean` | Round `0` from `formal/Heap`: the bus model (`BusModel`), **`BusModel.mainSound`** (`4N/|E|` and the constraints' batching), `UniIds.ofBus`. |
| `Mle.lean` | The sumcheck's folds are the claims' multilinear extensions (`foldAll_eq_sum`, `mleStk_eq_foldAll`): glue for `UniFinal`; the pending term's target `PendingTerminalLink`. |
| `CodeBase.lean`, `CodeTables.lean`, `CodeBatch.lean`, `CodeShape.lean` | The code-level link's layers: fixed reads, loops of fixed reads, observational equivalence (`obsOf`), the row counts, `tablePart` as `tableReads` reads, `batch` as its rounds (`batch_eq`), `C2`'s columns the shape's (`c2Columns_run`). |
| `CodeLink.lean` | **`uniCode`**: `UniCode D hFlock valsCount (varsOf (layoutsOf D.shape))`, `reduceWith` on the main line as the chain program `mainProg` (`link_obs`), Flock's segment by `hFlock.link`. |
| `FinalLink.lean` | **`uniFinal`**: `UniFinal` for the identity model whose batch is the verifier's (`batchProd`, `batchTargetOf`), under `WeightMle`, `LayoutVarsSmall`, `FlockPendingShaped`; the batch's algebra `terminal_sumState`; **`uniKnowledgeSoundness_code`**, the end theorem with both links in place. |
| `Ids/Align.lean` | **`BatchIsVerifiers` for the identity model**: its relations at `t` are the code-level link's (`relsAt_eq`: `relsOf` = `flockClaim (mainRels …)`, a table's part reading exactly `tableReads` values, `tablePartOf_eq`), its combined claims the run's (`runClaims_eq`), its batch the verifier's (`prodOf_eq_batchProd`, `targetOf_eq_batchTargetOf`, `batchIsVerifiers_of`, `batchIsVerifiers_ids`, under `FlockGood`); `nVOf_eq_of`. |
| `PendingLink.lean` | **`pendingTerminalLink`**: the batch's `λ³` product at its point is the pending reduction's terminal times the zero extension (`multilinear_eval` as the extension, substitution into `Â0`, `B̂0`). |
| `Final.lean` | **`uniKnowledgeSoundness`**, **`uniKnowledgeSoundness_bits`**, **`uniKnowledgeSoundness_bus`**. |
| `FsChain.lean` | The univariate transcript as `Compose.ChainSpecU` (`uniSpec`: 24-byte scalars, the root's reversed halves, the seed's 16-byte tag, the row counts before `C1`'s root), the PIOP lifted to the chain's statement (`liftPiop`), the proof the chain reads (`UPf`, `uView`). |
| `FsOps.lean` | The five `PCS_OPEN` calls as `WhirOp`s on plain layouts (`uniOps`: `C1`, `C2` by `tableCode`; the setup's stack, `A0`, `B0` at the setup's roots), the check (`uniCheck`), `good` (`uniGood`, `uniGoodS`). |
| `FsCost.lean` | `uniNumbers_of`: the composed verifier's calls of `π` below `2^80` (every query short), from the chain's `< 2^10` queries and every round's `≤ 2^30` scalars; `fsLayer_of_game'`. |
| `FinalFs.lean` | **`uniKnowledgeSoundness_game`**: the end theorem with `FsLayer` replaced by `UniShapes`, `UniNumbers`, `UniGameLe`. |
| `FsProof.lean` | **`fsLayer_of_game`**: `FsLayer` from the game bridge (`UniGameLe`) and the numbers (`UniNumbers`), through `Compose.knowledgeSoundness_listChainU_closed_rpm`: the setup's three trees, the openings' matches, the last link, the bound. |
| `FsGame.lean` | **`fsLayer_of_gameV`**: `FsLayer` from the coupling **`UniGameLeV`** (the contract's IV computed by the verifier, `uVerIv`, as the univariate experiment computes it; `FsProof.lean`'s `UniGameLe`, the IV in the adversary, is not provable outcome by outcome), `UniNumbers` and `UniIv`: `rpm_le_kcS` with that verifier, the IV moved into the two-oracle adversary (`expU_ivAdv`; its log entry of `programIv.length + 280` bytes leaves `C1`'s word, `extractorK_append`), the two-oracle theorem, the bound (`le_uniBoundV`). |
| `FsCouple.lean` | **`uniGameLeV_of`**: `UniGameLeV` from three bridge facts, `UniSetupBridge`, `UniVerifierBridge`, `UniExtractBridge` (the common prefix, the IV, `step_le`), as `formal/EndToEnd/Soundness/Final.lean`; **`fsLayer_of_bridges`**. |
| `FsWalk.lean` | The verifier bridge's interface: `uLen`, `uAccB`, **`UniWalk`** (on a stream of the main line's length the walk is the chain), **`UniWalkReject`**, `UniOutRoots` (proved for `uniCodeAt`). |
| `FsSetup.lean` | **`uniSetupBridge_of_small`**: `UniSetupBridge` under `LayoutVarsSmall` (false without: a layout word's byte reads the setup's variables mod `256`). |
| `FsExtract.lean` | **`uniExtractBridge`**: `UniExtractBridge` under `LayoutVarsSmall` (the Statement's word is mumbai's committed leaves, the two Merkle words agree, the list decoder's list holds the candidate), as `Soundness/Extract.lean`. |
| `FsVerifier.lean` | **`uniVerifierBridge_of_walk`**: the verifier bridge `UniVerifierBridge` (`FsCouple.lean`) from the walk's two halves (`UniWalk`, `UniWalkReject`, `FsWalk.lean`) and `UniOutRoots`: the same chain on both sides, then the Statement's five `PCS_OPEN` calls as F2's early-stop openings (`Bridge.openingWith_eq_ourVerifier'`) below the composed ones, acceptance giving `uniCheck`. |
| `FsFinal.lean` | **`uniGameLeV_holds`**, **`fsLayer_holds`**: the coupling and the Fiat–Shamir layer proved, from `LayoutVarsSmall`, `UniShapes`, `UniIv` and the chain's numbers. |
| `FsWalkProof.lean` | **`uniWalk`**, **`uniWalkReject`**: the verifier bridge's walk (`FsWalk.lean`'s `UniWalk`, `UniWalkReject`) for every code-level link: on a stream of the main line's length the walk is the chain (`progRun`: any chain program on a stream holding its bytes is the chain's steps; the row counts, the seed, `finish`), on another length every outcome rejects (`Consumes`). |

## What is proved, what is assumed

**Proved** (sorry-free, Lean's three axioms): the univariate PIOP's round-by-round soundness
(`uniPiop`: round `0` from the bus model, `BusModel.mainSound`, `busError N + (ncv − 1)/|E|`; Flock's
rounds from Flock's interface; `t` by Schwartz–Zippel over every identity, `degSum / |E|`; `ρ, λ` by
the two combinations, `(nRel − 1 + 3) / |E|`; each batching-sumcheck round `2 / |E|`, generic in
the weights, the pending matrices' sum as one more product); its first state is the relation and
its last follows from the verifier's checks with true claims (`hpre_uniPiop`, `hlink_uniPiop`);
the bound in bits (`uniBound_le_bits`).

**Assumed** (the end theorem's hypotheses, each a named Lean object):

1. `hFlock : FlockSound κ` — **Flock** (`FlockInterface.lean`; the Flock agent's).
2. `B : BusModel D κ` — round `0`'s bridges: the verifier's heap `hd` well formed and realizing
   Lv42's bus when the limb copies hold (`realizes`; `formal/Heap`'s open items: the leaves as
   Lv42's flushes, the padded rows' leaves `1`), the constraint vectors' vanishing giving
   `ConstraintsVanish`, `CountsNonzero`, `PublicLinesHold` and the copies (`cvec_ok`), Flock's
   column as Lv42's region (`aux_of_flock`), the tuple counts (`hpush`, `hpull`).
3. `J : UniIdsRest D hFlock B` — the identities as polynomials in `t` (`polys`, `deg_le`,
   `main_of_polys`: zero polynomials give the heap and the batched constraints on the domain,
   Heap's `tree_of_quotient`, `leaf_of_padded`, the restriction `R_b`, the coset reading), the
   relations at `t` (`diffs`, `diffs_eval`, `diffs_flock`, `diffs_pending`), the batch's products
   (`prod`, `target`, `batch_start`: `combine` and `weightAt` are the `ρ`- and `λ`-combinations).
4. `C : UniCode D hFlock nV V` — the code-level link: `reduceWith` after the row counts is the
   chain program on `uniRounds`. **Constructed** (`CodeLink.lean`): `uniCode D hFlock hκ :
   UniCode D hFlock valsCount (varsOf (layoutsOf D.shape))` for every deployment whose `BLAKE2S`
   height is `κ`, Flock's segment by `hFlock.link`; `uniCodeAt` at the identity model's numbers.
5. `hFin : UniFinal …` — the last link: the batch's terminal with true claims is the last state.
   **Constructed** (`FinalLink.lean`): `uniFinal` for the identity model whose batch is the
   verifier's (`prod = batchProd`, `target = batchTargetOf`), under three named hypotheses:
   `WeightMle` (each claim's weight at the batch's point is the fold of its cube values; it fails
   when a `q_flock` slot term's point `y(t)` is a proper prefix of another `C1` point, a polynomial
   coincidence in `t`: `combine` then lengthens the point and `weightAt` reads the slot's row on
   `8 + |point|` coordinates, overlapping the selector's), `LayoutVarsSmall` (fewer than `256`
   variables per stack, the layout word's byte), `FlockPendingShaped` (discharged for
   `flockSoundInstance`: `FlockSoundUni/PendingShape.lean`'s `flockPendingShaped`). The `λ³` term
   is `pendingTerminalLink` (`PendingLink.lean`). `uniKnowledgeSoundness_code` (and, with Flock's
   instance, `FlockSound.Uni.uniKnowledgeSoundness_flock`) is the end theorem with both in place.
6. `hFs : FsLayer …` — the Fiat–Shamir layer, **proved** (`fsLayer_of_gameV`, `FsGame.lean`):
   `Compose.ListChainU`'s chain over the univariate encoding, the random-permutation transfer for a
   setup of three trees (`Compose.rpm_le_kcS`) with the contract's IV in the verifier, the five
   openings' doom terms by F2, the decoders, the last link; from the numbers (`UniNumbers`, from the
   chain's `< 2^10` queries and rounds of `≤ 2^30` scalars), the program IV's length (`UniIv`) and
   the coupling `UniGameLeV`, itself **proved** from three bridge facts (`uniGameLeV_of`,
   `FsCouple.lean`): the setup's (`uniSetupBridge_of_small`) and the extractor's
   (`uniExtractBridge`), both under `LayoutVarsSmall`, and the verifier's (`uniVerifierBridge_of_walk`
   with the walk's `uniWalk`, `uniWalkReject`, `FsWalkProof.lean`): **`fsLayer_holds`**
   (`FsFinal.lean`), `FsLayer` at `uniCodeAt` from the deployment's numbers alone. The reference
   deployment's numbers (`UniShapes`, `LayoutVarsSmall`, `UniIv`, `κ = 18`, the chain's `86`
   queries) are `formal/FlockSound/FlockSoundUni/GameNumbers.lean`'s; `FlockSoundUni/Game.lean`
   gives the end theorems with the layer in place: **`uniKnowledgeSoundness_fs`** (every deployment,
   its numbers as hypotheses) and **`uniKnowledgeSoundness_reference_fs`** (the reference deployment,
   no Fiat–Shamir hypothesis left).
7. Numbers: `4 N + ncv ≤ 2^32`, Flock's rounds' errors at most `2^32 / |E|`, `degSum ≤ 2^32`,
   `nRel + 2 ≤ 2^32`.

The build fails if the end theorems' axioms grow beyond Lean's three standard ones.
-/

/-- info: 'UniSound.uniKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness

/-- info: 'UniSound.uniKnowledgeSoundness_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness_bits

/-- info: 'UniSound.uniPiop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniPiop

/-- info: 'UniSound.uniBound_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniBound_le_bits

/-- info: 'UniSound.SumOracle.step_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.SumOracle.step_sound

/-- info: 'UniSound.uniKnowledgeSoundness_bus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness_bus

/-- info: 'UniSound.BusModel.mainSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.BusModel.mainSound

/-- info: 'UniSound.prEvent_twoLevel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.prEvent_twoLevel_le

/-- info: 'UniSound.fsLayer_of_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer_of_game

/-- info: 'UniSound.hlink_uni' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.hlink_uni

/-- info: 'UniSound.hok_uni' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.hok_uni
/-- info: 'UniSound.pendingTerminalLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.pendingTerminalLink

/-- info: 'UniSound.link_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.link_obs

/-- info: 'UniSound.uniCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniCode

/-- info: 'UniSound.uniFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniFinal

/-- info: 'UniSound.terminal_sumState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.terminal_sumState

/-- info: 'UniSound.uniKnowledgeSoundness_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness_code

/-- info: 'UniSound.uniVerifierBridge_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniVerifierBridge_of_walk

/-- info: 'UniSound.uniWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniWalk

/-- info: 'UniSound.uniWalkReject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniWalkReject

/-- info: 'UniSound.Ids.tablePartOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.tablePartOf_eq

/-- info: 'UniSound.Ids.relsAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.relsAt_eq

/-- info: 'UniSound.Ids.runClaims_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.runClaims_eq

/-- info: 'UniSound.Ids.prodOf_eq_batchProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.prodOf_eq_batchProd

/-- info: 'UniSound.Ids.targetOf_eq_batchTargetOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.targetOf_eq_batchTargetOf

/-- info: 'UniSound.Ids.batchIsVerifiers_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.batchIsVerifiers_of

/-- info: 'UniSound.Ids.batchIsVerifiers_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.batchIsVerifiers_ids

/-- info: 'UniSound.Ids.nVOf_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.nVOf_eq_of
