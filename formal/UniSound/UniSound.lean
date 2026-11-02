-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Prog
import UniSound.FlockInterface
import UniSound.Prob
import UniSound.Sumcheck
import UniSound.Piop
import UniSound.PiopSound
import UniSound.Fs
import UniSound.Final

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
| `Final.lean` | **`uniKnowledgeSoundness`**, **`uniKnowledgeSoundness_bits`**. |

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

/-- info: 'UniSound.prEvent_twoLevel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.prEvent_twoLevel_le
