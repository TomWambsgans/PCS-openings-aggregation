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
-/

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
