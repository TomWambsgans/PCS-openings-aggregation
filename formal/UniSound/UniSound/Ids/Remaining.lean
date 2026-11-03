-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Assembly
import UniSound.Ids.Counts
import UniSound.Ids.Degrees
import UniSound.Ids.BcTuple

/-!
# What remained, proved at the reference shape

**`idsRemainingRef`**: `IdsRemaining D Fl 50708397 135` for a deployment at the reference shape: the
identities' degrees sum to at most `50,708,397 < 2^25.6` (`degBound_reference`), at most `135`
relations (`relCount_reference`), no limbs for a table's columns past its width (`c1Absent`), the
setup's bytecode tuple at `(α, ω_x)` (`bcTupleEval_reference`).

**`uniKnowledgeSoundness_ref'`**: `uniKnowledgeSoundness_ref` with these, and its numbers
(`ncv = 30 ≤ 100`, `d ≤ 2^31`, `max n 1 + 2 ≤ 2^32`) by `norm_num`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement
open scoped ENNReal

/-- **What remained, at the reference shape.** -/
theorem idsRemainingRef (D : Deployment) (hS : D.shape = reference) {κ : ℕ} (Fl : FlockSound κ) :
    IdsRemaining D Fl 50708397 135 where
  degBound := degBound_reference D Fl hS
  relCount := relCount_reference D Fl hS
  absent := c1Absent D.shape
  bcTuple := bcTupleEval_reference D hS

/-- **Knowledge soundness at the reference shape**, with `B` and `J` constructed and what remained
proved: under the Flock hypothesis, the code-level links and the Fiat–Shamir layer. -/
theorem uniKnowledgeSoundness_ref' (D : Deployment) (hS : D.shape = reference)
    (hFlock : FlockSound (D.shape.heights.getD opBlake2s 0))
    (C : UniCode D hFlock (nVOf D.shape) (batchVars D.shape))
    (hFin : UniFinal D hFlock (UniIds.ofBus hFlock (busModelRef D hS)
      (idsRestRef D hS hFlock 50708397 135 (idsRemainingRef D hS hFlock))) C)
    (hFs : FsLayer D hFlock (nVOf D.shape) (batchVars D.shape) C)
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_ref D hS hFlock 50708397 135 (idsRemainingRef D hS hFlock) C hFin hFs
    (by norm_num [ncvOf_eq]) hFl (by norm_num) (by norm_num)

end UniSound.Ids

/-- info: 'UniSound.Ids.idsRemainingRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.idsRemainingRef

/-- info: 'UniSound.Ids.uniKnowledgeSoundness_ref'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.uniKnowledgeSoundness_ref'
