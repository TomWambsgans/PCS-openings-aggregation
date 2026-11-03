-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Rec3.FlockInterface3
import UniSound.Rec3.Piop3
import UniSound.Rec3.PiopSound3
import UniSound.Rec3.Fs3
import UniSound.Rec3.Final3
import UniSound.Rec3.BusSq
import UniSound.Rec3.Narrow
import UniSound.Rec3.Pairs
import UniSound.Rec3.Batch3
import UniSound.Rec3.Ids3
import UniSound.Rec3.Ref3
import UniSound.Rec3.FsFinal3
import UniSound.Rec3.Numbers3
import UniSound.Rec3.CodeLink3
import UniSound.Rec3.Closed3
import UniSound.Rec3.FinalLink3
import UniSound.Rec3.FinalRef3
import UniSound.Rec3.FsFinal128_3
import UniSound.Rec3.Final128_3
import UniSound.Rec3.Closed128_3
import UniSound.Rec3.ClosedRec3

/-!
# π1-rec3: knowledge soundness of the recursion's inner verifier

π1-rec3 (`crates/leanvm_rec/SPEC-REC.md` §12 items 5, 7, 8, §1.4; `SPEC-POINTS.md`; `crates/leanvm_univariate`'s
`FLOCK_REC3`, `FsShape::Rec3`) is the main line's univariate verifier for leanVM 42422001 with four changes, each a
new lemma here:

| change | lemma | error a round |
|---|---|---|
| `α = (c, c², c⁴, c⁸)` of one challenge | `BusSq.lean`: `card_sideProduct_sq_collision_le` (two-variable Schwartz–Zippel, degree `16` a tuple), `BusModel.mainSoundSq` | `16 N / |E| + (ncv − 1)/|E|` |
| Flock's zerocheck coordinates `c', c'², c'⁴, …` | `FlockSound/Kronecker.lean`: `kron` (base-2 Kronecker substitution), `kron_eq_zero_iff`, `card_kronBad_le`, `zerocheck_sound_sq`; `FlockSound/FlockSq.lean`: `flock_front_sq` | `(2^(4+κ) − 1)/|E|` |
| Flock's lincheck terminal walked (no `A0`, `B0` claims) | `FlockSoundUni/Walk.lean` (the walk is the matrices' product sum), `Rec3Walk.lean` (`walkSpec_of`), `FlockSound/FlockSq.lean`'s `flock_sound_walked` | none: a check |
| the batch two variables a round, narrow challenges | `Narrow.lean` (`card_narrowE_fiber_le`: fibers of `2^32`), `Pairs.lean` (`psum_V2`, `pairSum`, `ProdSum.pairOracle`, `PairOracle.step_sound`, `batchState3_step`, `cantorBeta1_spec`) | `8 · 2^32/|E|` a pair, `2 · 2^32/|E|` the last |

The proof: Flock's interface `FlockSound3` (`FlockInterface3.lean`) and its instance (`FlockSoundUni/Rec3*.lean`:
`flockProg3`, `flock_link3`, `flockBad3`, `catches3`, `flockSound3_of`); the PIOP's rounds, states and errors
(`Piop3.lean`) and its round-by-round soundness `uniPiop3` (`PiopSound3.lean`); the identity model reused from the
main line's at the expanded transcripts (`Ids3.lean`: `ids3Of`, the batch without the pending term); the named links
(`Fs3.lean`: `UniCode3`, `UniFinal3`, `FsLayer3`, `uniBound3` with three openings) and the end theorem from them
(`Final3.lean`: `uniKnowledgeSoundness3`, `uniBound3_le_bits`); the reference deployment (`Ref3.lean`).

**The links, proved**: the code-level link (`CodeBatch3.lean`, `CodeLink3.lean`: `uniCode3`, `uniCode3At`, up to
`obsOf3`, since `sampleNarrow` records the narrow challenge where a chain program records the raw draw), the last link
(`FinalLink3.lean`, `FinalRef3.lean`: `uniFinal3_ref`), the Fiat–Shamir layer (`Fs*3.lean`: `fsLayer3_holds`, three
openings; `Fs*128_3.lean`: `fsLayer128_3_holds`, the openings charged once at the exact certified `269 · 2^-137`).

**The end theorem** (`ClosedRec3.lean`): `uniKnowledgeSoundness_closed_rec3_of_rows` — at the reference deployment
with leanVM's program IV, knowledge sound with error `uniBound128 (2^35/|E|) Q ≤ 2^-64` for `Q ≤ 2^64`
(`2^-64.494` at `2^64`: 128.49 bits, `EndToEnd/Review/UniRec3Numbers.py`), from `RowsSpec` (the BLAKE2s circuit walk
`blake2sRowValues` computes `A0 w`, `B0 w`: `FlockSoundUni/Walk.lean`); `walkLemma_of_rows` (`FlockSoundUni/WalkAlg.lean`)
turns it into the walk's lemma. The weakest round is a narrow pair's, `8 · 2^32/|E| = 2^-157`, the bound `e` of every
round (`2^-130.4` times the lists' `9952²`).
-/

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3_of_rows

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_128_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_128_of_walk

/-- info: 'FlockSound.Uni.walkLemma_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.walkLemma_of_rows

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_of_walk

/-- info: 'UniSound.fsLayer3_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer3_holds

/-- info: 'UniSound.Rec3Ref.uniFinal3_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniFinal3_ref

/-- info: 'UniSound.uniPiop3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniPiop3

/-- info: 'UniSound.uniKnowledgeSoundness3_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness3_bits

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_ref

/-- info: 'UniSound.BusModel.mainSoundSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.BusModel.mainSoundSq

/-- info: 'UniSound.batchState3_step_rec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.batchState3_step_rec3

/-- info: 'UniSound.Ids.ids3Of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.ids3Of
