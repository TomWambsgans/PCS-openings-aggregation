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
| `Mle.lean` | The sumcheck's folds are the claims' multilinear extensions (`foldAll_eq_sum`, `mleStk_eq_foldAll`): glue for `UniFinal`. |
| `Final.lean` | **`uniKnowledgeSoundness`**, **`uniKnowledgeSoundness_bits`**, **`uniKnowledgeSoundness_bus`**. |

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
   chain program on `uniRounds`.
5. `hFin : UniFinal …` — the last link: the batch's terminal with true claims is the last state.
6. `hFs : FsLayer …` — the Fiat–Shamir layer: `ListChainK`'s closed random-permutation theorem
   ported to the univariate transcript, its five openings, its setup and `uniExtractor`.
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
