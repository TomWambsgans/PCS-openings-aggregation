-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The hypothesis is `formal/UniSound`'s
-- `FlockPendingShaped` (`FinalLink.lean`); the instance is `Instance.lean`'s `flockSoundInstance`.
import FlockSoundUni.Instance
import UniSound.FinalLink

/-!
# Flock's pending reduction has its shape: `FlockPendingShaped` for `flockSoundInstance`

The batch's last link (`UniSound.uniFinal`) needs, of Flock's chain program, that its pending
reduction has the shape `multilinear_eval` reads as multilinear extensions (`Pending.Shaped`), that
the slices are sent, and at most `15` rounds. For `flockSoundInstance κ` (`flockProg κ`): the skip's
weights are `lagrangeWeights (2^k) z` for `k = 6 − |rowLow|` (`2^k` of them whatever the lengths),
the row and column points have at most `3` and `8` coordinates, and the slices are the last round's
64 scalars. **`flockPendingShaped`**, and **`uniKnowledgeSoundness_flock`**: the end theorem with Flock's
interface, the code-level link and the last link in place.
-/

namespace FlockSound.Uni

open UniSound UniStatement LeanVM.Parameters
open scoped ENNReal

theorem flockSoundInstance_prog (κ : ℕ) : (flockSoundInstance κ).prog = flockProg κ := rfl

theorem pending_new_shaped (z α rLc : E) (rowLow chiIn chiInPrime slices : List E)
    (hrl : rowLow.length ≤ 3) (hci : chiIn.length ≤ 8) (hsl : slices.length = 64) :
    Pending.Shaped (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some slices)) ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some slices)).hasSlices = true ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some slices)).rounds ≤ 15 := by
  simp only [Pending.Shaped, Flock.Pending.new, Flock.rowLowWeights, Flock.Pending.rounds,
    Flock.Pending.hasSlices, Flock.packing, Option.getD_some, Option.isSome_some, lagrangeWeights_length,
    List.length_append, matrixVars, blake2sR1csLogSize]
  exact ⟨⟨fun _ => trivial, Or.inl (by rw [hsl]; rfl), by omega⟩, trivial, by omega⟩

/-- **Flock's pending reduction has its shape** (`FlockPendingShaped`) for the closed instance. -/
theorem flockPendingShaped (κ : ℕ) : FlockPendingShaped (flockSoundInstance κ) := by
  intro fd hfd
  rw [flockSoundInstance_prog] at hfd ⊢
  change DoneFits (flockRounds κ) fd at hfd
  have hsplit : flockRounds κ = ([⟨false, 0, 3 + κ⟩, ⟨false, 8, 0⟩] ++ List.replicate (11 + κ) ⟨false, 2, 0⟩ ++
      [⟨false, 2, 0⟩] ++ List.replicate 8 ⟨false, 2, 0⟩) ++ [⟨false, 64, 5⟩] := rfl
  rw [hsplit] at hfd
  obtain ⟨d1, d2, rfl, h1, h2⟩ := UniSound.doneFits_append_split _ _ _ hfd
  rcases d2 with _ | ⟨x, _ | ⟨y, d2⟩⟩ <;> simp only [DoneFits, and_false] at h2
  have hl1 : d1.length = 22 + κ := by
    rw [UniSound.doneFits_length _ _ h1]
    simp
    omega
  have hx : (rd ((d1 ++ [x]).drop (22 + κ)) 0).1.2.length = 64 := by
    rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]
    exact h2.1.2
  show Pending.Shaped (outOf κ (d1 ++ [x])).2.2 ∧ (outOf κ (d1 ++ [x])).2.2.hasSlices = true ∧
    (outOf κ (d1 ++ [x])).2.2.rounds ≤ 15
  unfold outOf flockOut
  exact pending_new_shaped _ _ _ _ _ _ _ (by simp) (by simp) hx

/-- **Knowledge soundness with Flock's interface, the code-level link and the last link in place**
(`flockSoundInstance`, `uniCodeAt`, `uniFinal`, `flockPendingShaped`): the end theorem for an
identity model whose numbers and batch are the verifier's, under `WeightMle`, `LayoutVarsSmall`, the
Fiat–Shamir layer and the end theorem's numbers. -/
theorem uniKnowledgeSoundness_flock {D : Deployment} (κ : ℕ) (hκ : D.shape.heights.getD opBlake2s 0 = κ)
    (B : BusModel D κ) (J : UniIdsRest D (flockSoundInstance κ) B)
    (hnV : J.nV = valsCount) (hV : J.V = varsOf (layoutsOf D.shape))
    (hbatch : BatchIsVerifiers D (flockSoundInstance κ) (UniIds.ofBus (flockSoundInstance κ) B J))
    (hW : WeightMle D (flockSoundInstance κ) J.zb) (hcount : CountsZero D (flockSoundInstance κ))
    (hsmall : LayoutVarsSmall D)
    (hFs : FsLayer D (flockSoundInstance κ) J.nV J.V (uniCodeAt D (flockSoundInstance κ) hκ J.nV J.V hnV hV))
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32)
    (hFl : ∀ j, (flockSoundInstance κ).err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : J.degSum + J.degBad ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_code (flockSoundInstance κ) hκ B J hnV hV hbatch hW hsmall
    (flockPendingShaped κ) hcount hFs hB hFl hdeg hrel

end FlockSound.Uni

/-- info: 'FlockSound.Uni.flockPendingShaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockPendingShaped

/-- info: 'FlockSound.Uni.uniKnowledgeSoundness_flock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniKnowledgeSoundness_flock
