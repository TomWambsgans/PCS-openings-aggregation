-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.Catch
import FlockSoundUni.Transcription

/-!
# Flock's interface instance, closed

The catch (`catches_of_tx`) takes the evaluator transcription `Tx κ`; `flockTx κ` proves it
(`Transcription.lean`: the skip's interpolation, the fixed coordinates, `E::pow`, the tower target and
ring claim, the pending claim and sum). So **`flockSoundInstance κ : UniSound.FlockSound κ`** is the
one Flock hypothesis of the end theorem, discharged: the chain program `flockProg κ` and its link
`flock_link`, the bad family `flockBad κ` of sizes `dBound κ`, round `j`'s error `roundErr κ j / |E|`
(`4 + κ`, `15`, `2` per zerocheck round, `3`, `2` per lincheck round, `6`) and `εFlock = (66 + 3κ)/|E|`.
-/

namespace FlockSound.Uni

open UniSound
open scoped ENNReal

/-- The transcription in the form the catch takes. -/
theorem tx_of_flockTx (κ : ℕ) : Tx κ :=
  let h := flockTx κ
  ⟨h.fixed, h.epow, h.interp, h.target, h.ring, h.claim, h.sum⟩

/-- **Flock's interface instance**, closed: the one Flock hypothesis of the end theorem. -/
noncomputable def flockSoundInstance (κ : ℕ) : UniSound.FlockSound κ :=
  flockSound_of_tx (tx_of_flockTx κ)

/-- **Its rounds' errors**: round `j` of `23 + κ`, `roundErr κ j / |E|`. -/
theorem flockSoundInstance_err (κ j : ℕ) (hj : j < 23 + κ) :
    (flockSoundInstance κ).err j = (roundErr κ j : ℝ≥0∞) / (Fintype.card LeanVM.Parameters.E : ℝ≥0∞) :=
  flockSound_err (tx_of_flockTx κ) j hj

/-- **Flock's error per candidate**: `(66 + 3κ)/|E|`. -/
theorem flockSoundInstance_error (κ : ℕ) :
    (flockSoundInstance κ).flockError =
      ((66 + 3 * κ : ℕ) : ℝ≥0∞) / (Fintype.card LeanVM.Parameters.E : ℝ≥0∞) :=
  flockSound_error (tx_of_flockTx κ)

end FlockSound.Uni
