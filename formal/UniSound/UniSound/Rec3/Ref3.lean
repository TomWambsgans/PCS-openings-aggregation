-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The assembly follows `Closed.lean` (the main line's).
import UniSound.Rec3.Final3
import UniSound.Rec3.Ids3
import UniSound.Rec3.Batch3
import UniSound.Ids.Assembly
import UniSound.Ids.Remaining
import FlockSoundUni.GameNumbers
import UniSound.Closed

/-!
# π1-rec3 at the reference deployment: the pieces and the numbers

At the reference shape (`κ = 18`, the batch's `27 = 2 · 13 + 1` variables):

* **Flock**: `flock3Ref hw = flockSound3_of (tx_of_flockTx κ) hw` (the walk's fact `hw : WalkSpec κ`);
* **the identity model**: `ids3Ref D hD hw = ids3Of …` at the main line's reference arguments (`busBound`,
  `idsHyps_ref`, `50,708,397`, `135`, `idsGaps_ref … idsRemainingRef`), `np = 13`;
* **the batch**: `pairBatchRec3 13`;
* **the numbers** (`hMain_ref3`, `hFl_ref3`, `hdeg_ref3`, `hrel_ref3`): round `0`'s error `16 N + 29 ≤ 2^35` times
  `1/|E|` (`N = busBound reference`, `4 N + 30 ≤ 2^32`), Flock's rounds' `≤ (2^22 + 90)/|E|`, the identities' and the
  merge polynomial's degrees `50,708,397 + 2^19 ≤ 2^35`, `135` relations: every round at most `2^35/|E|`, the pairs'
  `8 · 2^32/|E|` the largest.

**`uniKnowledgeSoundness_rec3_ref`**: π1-rec3 is knowledge sound at the reference deployment with error
`uniBound3 (2^35/|E|)`, at most `2^-61` for `Q ≤ 2^64`, given the walk's fact, the code-level link `C`, the last link
and the Fiat–Shamir layer (each proved elsewhere: `Rec3/Closed3.lean` assembles them).
-/

namespace UniSound.Rec3Ref

open UniStatement LeanVM.Parameters FlockSound.Uni UniSound.Ids
open scoped ENNReal

variable (D : Deployment) (hD : D.shape = reference)

/-- **π1-rec3's Flock at the reference**, from the walk's fact. -/
noncomputable abbrev flock3Ref (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    FlockSound3 (D.shape.heights.getD opBlake2s 0) :=
  flockSound3_of (tx_of_flockTx _) hw

include hD in
theorem batchVars_ref3 : batchVars D.shape = 2 * 13 + 1 := by
  rw [batchVars_eq, hD, varsOf_reference]

/-- **π1-rec3's identity model at the reference.** -/
noncomputable def ids3Ref (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    UniIds3 D (flock3Ref D hw) 13 :=
  ids3Of D (busBound D.shape) (idsHyps_ref D hD) 50708397 135
    (idsGaps_ref D hD (flockSoundInstance _) 50708397 135 (idsRemainingRef D hD _)) (tx_of_flockTx _) hw 13
    (batchVars_ref3 D hD)

theorem hMain_ref3 (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    (ids3Ref D hD hw).errMain ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  refine (busModelRef D hD).errMainSq_le ?_
  have h := UniSound.Closed.hB_ref D hD
  omega

include hD in
theorem hFl_ref3 (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) (j : ℕ) :
    (flock3Ref D hw).err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  refine (flockSound3_err_le (tx_of_flockTx _) hw j).trans (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _)
  rw [hκ_reference D hD]
  norm_num

theorem hdeg_ref3 (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    (ids3Ref D hD hw).degSum + (ids3Ref D hD hw).degBad ≤ 2 ^ 35 := by
  have h := UniSound.Closed.hdeg_ref D hD
  have e : (ids3Ref D hD hw).degSum + (ids3Ref D hD hw).degBad =
      (UniSound.Closed.idsRef D hD).degSum + (UniSound.Closed.idsRef D hD).degBad := rfl
  omega

theorem hrel_ref3 (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) :
    (ids3Ref D hD hw).nRel + 2 ≤ 2 ^ 35 := by
  show max 135 1 + 2 ≤ 2 ^ 35
  norm_num

/-- **π1-rec3 at the reference deployment, from its named links**: knowledge sound for `uniExtractor` with error
`uniBound3 (2^35/|E|) Q`, at most `2^-61` for `Q ≤ 2^64`, given the walk's fact `hw`, the code-level link `C`, the
last link `hFin` and the Fiat–Shamir layer `hFs`. -/
theorem uniKnowledgeSoundness_rec3_ref (hw : WalkSpec (D.shape.heights.getD opBlake2s 0))
    (C : UniCode3 D (flock3Ref D hw) (ids3Ref D hD hw).nV 13)
    (hFin : UniFinal3 D (flock3Ref D hw) (ids3Ref D hD hw) (pairBatchRec3 13) C)
    (hFs : FsLayer3 D (flock3Ref D hw) (ids3Ref D hD hw).nV 13 C) :
    UniKnowledgeSoundnessRec3 D (uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness3_bits (flock3Ref D hw) (ids3Ref D hD hw) (pairBatchRec3 13) C hFin hFs
    (hMain_ref3 D hD hw) (hFl_ref3 D hD hw) (hdeg_ref3 D hD hw) (hrel_ref3 D hD hw)
    (pairBatchRec3_errPair 13) (pairBatchRec3_errLast 13)

end UniSound.Rec3Ref

/-- info: 'UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.uniKnowledgeSoundness_rec3_ref
