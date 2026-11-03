-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The interface is `UniSound.FlockSound3`
-- (`formal/UniSound/UniSound/Rec3/FlockInterface3.lean`); the instance follows `Instance.lean` (the main line's).
import FlockSoundUni.Rec3Catch
import UniSound.Rec3.FlockInterface3

/-!
# π1-rec3's Flock interface instance

**`flockSound3_of tx hw : UniSound.FlockSound3 κ`**: the chain program `flockProg3 κ` and its link `flock_link3`,
the main line's reading `outOf κ ∘ expandFd κ` (`outOf_expandFd`), the walk (`hw : WalkSpec κ`: on a completed
transcript whose walk's zero vanishes, the reading's pending claim is its sum; `Rec3Walk.lean` proves it from the
walk's lemma), the bad family `flockBad3 κ` of sizes `dBound3 κ`, which catches (`catches3`, given the main line's
evaluator transcription `Tx κ`). Round `j`'s error `Σ_i dBound3 κ j i / |E|`: `(2^(4 + κ) − 1)/|E|` for the
squares' challenge (Kronecker, `2^22 − 1` at `κ = 18`: `sum_dBound3_le`), the main line's after; every round's at most
`(2^(4 + κ) + 90)/|E|` (`flockSound3_err_le`).
-/

namespace FlockSound.Uni

open UniSound LeanVM.Parameters UniStatement Finset
open scoped ENNReal

variable {κ : ℕ}

/-- **The walk's fact the instance takes**: on a completed transcript of π1-rec3's Flock rounds whose zero (the
walk's) vanishes, the main line's reading's pending claim is its sum. -/
def WalkSpec (κ : ℕ) : Prop :=
  ∀ (done : Done) (tl : List E), DoneFits (flockRounds3 κ) done → (flockProg3 κ).ZerosVanish done tl →
    PendingHolds (outOf κ (expandFd κ done)).2.2

/-- **π1-rec3's Flock interface**, from the evaluator transcription and the walk's fact. -/
noncomputable def flockSound3_of (tx : Tx κ) (hw : WalkSpec κ) : UniSound.FlockSound3 κ where
  prog := flockProg3 κ
  rounds_root := flockProg3_root κ
  tail_eq := flockProg3_tail κ
  link := fun F ↦ flock_link3 κ F
  outM d := outOf κ (expandFd κ d)
  out_end done _ hfit := outOf_expandFd κ done (by rintro rfl; exact hfit)
  walk := hw
  S := stateOf (flockBad3 κ)
  err j := ((∑ i ∈ range ((((flockRounds3 κ)[j]?).map (·.ns)).getD 0 + 1), dBound3 κ j i : ℕ) : ℝ≥0∞) /
    (Fintype.card E : ℝ≥0∞)
  S_nil := stateOf_nil (flockBad3 κ)
  step j hj qf done msg hfit _ := by
    show Pr{let c ← Compose.draws E (((flockRounds3 κ)[j]'hj).ns + 1)}[¬ stateOf (flockBad3 κ) qf done ∧
      stateOf (flockBad3 κ) qf (done ++ [(msg, c)])] ≤
      ((∑ i ∈ range ((((flockRounds3 κ)[j]?).map (·.ns)).getD 0 + 1), dBound3 κ j i : ℕ) : ℝ≥0∞) /
        (Fintype.card E : ℝ≥0∞)
    have hlen : done.length = j := by
      rw [doneFits_length hfit, List.length_take]
      have : j < (flockRounds3 κ).length := hj
      omega
    have h := step_le (flockBad3 κ) (dBound3 κ) (card_flockBad3 κ) qf done msg
      ((flockRounds3 κ)[j]'hj).ns
    rw [hlen] at h
    rw [List.getElem?_eq_getElem (show j < (flockRounds3 κ).length from hj), Option.map_some, Option.getD_some]
    exact h
  finish qf done hfit hend hpend := catches3 tx qf done hfit hend hpend

/-- **Every round's error is at most `(2^(4 + κ) + 90)/|E|`.** -/
theorem flockSound3_err_le (tx : Tx κ) (hw : WalkSpec κ) (j : ℕ) :
    (flockSound3_of tx hw).err j ≤ ((2 ^ (4 + κ) + 90 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (sum_dBound3_le κ j)) _

end FlockSound.Uni

/-- info: 'FlockSound.Uni.flockSound3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockSound3_of

/-- info: 'FlockSound.Uni.flockSound3_err_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockSound3_err_le

/-- info: 'FlockSound.Uni.catches3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.catches3

/-- info: 'FlockSound.Uni.flock_link3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flock_link3
