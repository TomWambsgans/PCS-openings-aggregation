-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Rec3.Pairs
import UniSound.Rec3.Piop3

/-!
# π1-rec3's batch, round by round: the `PairBatch` instance

**`pairBatchRec3 np`**: the paired, narrow batching sumcheck of π1-rec3 (`np` pair rounds at `β_1 = cantorBeta1`,
challenges `narrowE` of the hash's, then one plain narrow round) as `Piop3.lean`'s `PairBatch np`: its state
`BatchState3 cantorBeta1 narrowE` (`Pairs.lean`), a pair round's error `8 · 2^32 / |E|` (degree `8`, a uniform draw
from `2^160` values), the last plain round's `2 · 2^32 / |E|`.
-/

namespace UniSound

open LeanVM.Parameters UniStatement
open scoped ENNReal

/-- **π1-rec3's batch** as the PIOP's `PairBatch`. -/
noncomputable def pairBatchRec3 (np : ℕ) : PairBatch np where
  St := BatchState3 cantorBeta1 narrowE
  St_nil := batchState3_nil cantorBeta1 narrowE
  errPair := ((8 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  errLast := ((2 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  step := fun P tg rs m hv hr => batchState3_step_rec3 P np tg rs m hv hr

theorem pairBatchRec3_errPair (np : ℕ) :
    (pairBatchRec3 np).errPair ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (by norm_num)) _

theorem pairBatchRec3_errLast (np : ℕ) :
    (pairBatchRec3 np).errLast ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (by norm_num)) _

end UniSound

/-- info: 'UniSound.pairBatchRec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.pairBatchRec3
