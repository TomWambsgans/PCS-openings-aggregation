-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The Fiat–Shamir layer is
-- `formal/UniSound`'s `fsLayer_of_bridges` (`FsCouple.lean`); the rest `PendingShape.lean`'s
-- `uniKnowledgeSoundness_flock`.
import FlockSoundUni.PendingShape
import UniSound.FsWalk
import UniSound.FsSetup

/-!
# The end theorem with the Fiat–Shamir layer reduced to its bridge facts

**`uniKnowledgeSoundness_bridges`**: `uniKnowledgeSoundness_flock` with its hypothesis
`hFs : FsLayer …` replaced by what `UniSound.fsLayer_of_bridges` proves it from: the deployment's
stacks (`UniShapes`), its program IV (`UniIv`), the chain's numbers (`< 2^10` queries, rounds of
`≤ 2^30` scalars), and the coupling's bridge facts: the setup's (`UniSetupBridge`) proved
(`uniSetupBridge_of_small`, from `LayoutVarsSmall`), `UniVerifierBridge`, `UniExtractBridge`.
-/

namespace FlockSound.Uni

open UniSound UniStatement LeanVM.Parameters
open scoped ENNReal

/-- **Knowledge soundness, the Fiat–Shamir layer reduced to its bridge facts**: the end theorem with
Flock's interface, the code-level link and the last link in place, under `WeightMle`,
`LayoutVarsSmall`, the deployment's numbers and the three bridges. -/
theorem uniKnowledgeSoundness_bridges {D : Deployment} (κ : ℕ)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (B : BusModel D κ)
    (J : UniIdsRest D (flockSoundInstance κ) B)
    (hnV : J.nV = valsCount) (hV : J.V = varsOf (layoutsOf D.shape))
    (hprod : ∀ s c1 ch fd c2 t vals rho lam,
      J.prod s c1 ch fd c2 t vals rho lam = batchProd D (flockSoundInstance κ) s c1 ch fd c2 t vals rho lam)
    (htarget : ∀ s c1 ch fd c2 t vals rho lam,
      J.target s c1 ch fd c2 t vals rho lam = batchTargetOf D (flockSoundInstance κ) s ch fd t vals rho lam)
    (hW : WeightMle D (flockSoundInstance κ)) (hsmall : LayoutVarsSmall D) (hs : UniShapes D)
    (hI : UniIv D)
    (hnQ : (uSpec (flockSoundInstance κ) valsCount (varsOf (layoutsOf D.shape))).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds (flockSoundInstance κ) valsCount (varsOf (layoutsOf D.shape)), r.nv ≤ 2 ^ 30)
    (hVer : UniVerifierBridge D (flockSoundInstance κ) J.nV J.V
      (uniCodeAt D (flockSoundInstance κ) hκ J.nV J.V hnV hV) hs)
    (hX : UniExtractBridge D (flockSoundInstance κ) J.nV J.V hs)
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32)
    (hFl : ∀ j, (flockSoundInstance κ).err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : J.degSum ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 := by
  have hnQ' : (uSpec (flockSoundInstance κ) J.nV J.V).K.nQ ≤ 2 ^ 10 := by
    rw [hnV, hV]
    exact hnQ
  have hnv' : ∀ r ∈ uRounds (flockSoundInstance κ) J.nV J.V, r.nv ≤ 2 ^ 30 := by
    rw [hnV, hV]
    exact hnv
  exact uniKnowledgeSoundness_flock κ hκ B J hnV hV hprod htarget hW hsmall
    (fsLayer_of_bridges D (flockSoundInstance κ) J.nV J.V _ hs hnQ' hnv' hI (uniSetupBridge_of_small D hs hsmall) hVer hX) hB hFl hdeg
    hrel

end FlockSound.Uni

/-- info: 'FlockSound.Uni.uniKnowledgeSoundness_bridges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniKnowledgeSoundness_bridges
