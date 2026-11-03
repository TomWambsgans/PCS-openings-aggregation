-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The Fiat–Shamir layer is
-- `formal/UniSound`'s `fsLayer_of_bridges` (`FsCouple.lean`); the rest `PendingShape.lean`'s
-- `uniKnowledgeSoundness_flock`.
import FlockSoundUni.PendingShape
import UniSound.FsWalk
import UniSound.FsSetup
import UniSound.FsExtract
import UniSound.FsVerifier
import UniSound.FsFinal
import FlockSoundUni.GameNumbers

/-!
# The end theorem with the Fiat–Shamir layer proved

* **`uniKnowledgeSoundness_fs`**: `uniKnowledgeSoundness_flock` with its hypothesis `hFs : FsLayer …`
  proved (`UniSound.fsLayer_holds`) from the deployment's numbers: its stacks (`UniShapes`,
  `LayoutVarsSmall`), its program IV (`UniIv`), the chain's `< 2^10` queries and rounds of `≤ 2^30`
  scalars.
* **`uniKnowledgeSoundness_reference_fs`**: the same at the reference deployment (`reference`'s
  shape, leanVM's program IV), every number in place (`GameNumbers.lean`): no Fiat–Shamir
  hypothesis is left.
* The stages before: `uniKnowledgeSoundness_bridges` (the three bridge facts as hypotheses),
  `uniKnowledgeSoundness_reference_game` (the verifier's bridge as one),
  `uniKnowledgeSoundness_reference_walk` (the walk's two facts as hypotheses).
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
    (fsLayer_of_bridges D (flockSoundInstance κ) J.nV J.V _ hs hnQ' hnv' hI (uniSetupBridge_of_small D hs hsmall) hVer
      (uniExtractBridge D (flockSoundInstance κ) J.nV J.V hs hsmall)) hB hFl hdeg
    hrel

/-- **Knowledge soundness at the reference deployment** (`reference`'s shape, leanVM's program IV):
`uniKnowledgeSoundness_bridges` at `κ = 18` with the deployment's numbers (`GameNumbers.lean`:
`hκ_reference`, `uniShapes_reference`, `layoutVarsSmall_reference`, `uniIv_of`, `hnQ_flock'`,
`hnv_flock'`, `hFl_flock`) and the setup's and extractor's bridges in place. What is left: the bus
model and the identity model's rest (`B`, `J`, `hB`, `hdeg`, `hrel`, the batch `hprod`, `htarget`),
`WeightMle`, and the verifier's bridge `UniVerifierBridge`. -/
theorem uniKnowledgeSoundness_reference_game {D : Deployment} (hD : D.shape = reference)
    (hIv : D.programIv = programIv) (B : BusModel D 18) (J : UniIdsRest D (flockSoundInstance 18) B)
    (hnV : J.nV = valsCount) (hV : J.V = varsOf (layoutsOf D.shape))
    (hprod : ∀ s c1 ch fd c2 t vals rho lam,
      J.prod s c1 ch fd c2 t vals rho lam = batchProd D (flockSoundInstance 18) s c1 ch fd c2 t vals rho lam)
    (htarget : ∀ s c1 ch fd c2 t vals rho lam,
      J.target s c1 ch fd c2 t vals rho lam = batchTargetOf D (flockSoundInstance 18) s ch fd t vals rho lam)
    (hW : WeightMle D (flockSoundInstance 18))
    (hVer : UniVerifierBridge D (flockSoundInstance 18) J.nV J.V
      (uniCodeAt D (flockSoundInstance 18) (hκ_reference D hD) J.nV J.V hnV hV)
      (uniShapes_reference D hD))
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32) (hdeg : J.degSum ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_reference hD hIv B J hnV hV hprod htarget hW
    (uniSetupBridge_of_small D _ (layoutVarsSmall_reference D hD)) hVer
    (uniExtractBridge D _ J.nV J.V _ (layoutVarsSmall_reference D hD)) hB hdeg hrel

/-- **Knowledge soundness at the reference deployment, the verifier's bridge from the walk**
(`uniVerifierBridge_of_walk`, `uniOutRoots_uniCodeAt`): `uniKnowledgeSoundness_reference_game` with
`UniVerifierBridge` replaced by the walk's two facts, `UniWalk` (on a stream of the main line's
length the walk is the chain) and `UniWalkReject` (on another, it rejects). -/
theorem uniKnowledgeSoundness_reference_walk {D : Deployment} (hD : D.shape = reference)
    (hIv : D.programIv = programIv) (B : BusModel D 18) (J : UniIdsRest D (flockSoundInstance 18) B)
    (hnV : J.nV = valsCount) (hV : J.V = varsOf (layoutsOf D.shape))
    (hprod : ∀ s c1 ch fd c2 t vals rho lam,
      J.prod s c1 ch fd c2 t vals rho lam = batchProd D (flockSoundInstance 18) s c1 ch fd c2 t vals rho lam)
    (htarget : ∀ s c1 ch fd c2 t vals rho lam,
      J.target s c1 ch fd c2 t vals rho lam = batchTargetOf D (flockSoundInstance 18) s ch fd t vals rho lam)
    (hW : WeightMle D (flockSoundInstance 18))
    (hWalk : UniWalk D (flockSoundInstance 18) J.nV J.V
      (uniCodeAt D (flockSoundInstance 18) (hκ_reference D hD) J.nV J.V hnV hV))
    (hRej : UniWalkReject D (flockSoundInstance 18) J.nV J.V)
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32) (hdeg : J.degSum ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_reference_game hD hIv B J hnV hV hprod htarget hW
    (uniVerifierBridge_of_walk D _ J.nV J.V _ _ hWalk hRej
      (uniOutRoots_uniCodeAt D _ (hκ_reference D hD) J.nV J.V hnV hV)) hB hdeg hrel

/-- **Knowledge soundness, the Fiat–Shamir layer proved**: the end theorem with Flock's interface,
the code-level link, the last link and the Fiat–Shamir layer in place, under `WeightMle`, the bus
model, the identity model's rest and the deployment's numbers. -/
theorem uniKnowledgeSoundness_fs {D : Deployment} (κ : ℕ)
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
    (fsLayer_holds D (flockSoundInstance κ) hκ J.nV J.V hnV hV hs hsmall hI hnQ' hnv') hB hFl hdeg
    hrel

/-- **Knowledge soundness at the reference deployment, the Fiat–Shamir layer proved**: no hypothesis
of the Fiat–Shamir layer is left; what is left is the bus model and the identity model's rest
(`B`, `J`, `hB`, `hdeg`, `hrel`, the batch `hprod`, `htarget`) and `WeightMle`. -/
theorem uniKnowledgeSoundness_reference_fs {D : Deployment} (hD : D.shape = reference)
    (hIv : D.programIv = programIv) (B : BusModel D 18) (J : UniIdsRest D (flockSoundInstance 18) B)
    (hnV : J.nV = valsCount) (hV : J.V = varsOf (layoutsOf D.shape))
    (hprod : ∀ s c1 ch fd c2 t vals rho lam,
      J.prod s c1 ch fd c2 t vals rho lam = batchProd D (flockSoundInstance 18) s c1 ch fd c2 t vals rho lam)
    (htarget : ∀ s c1 ch fd c2 t vals rho lam,
      J.target s c1 ch fd c2 t vals rho lam = batchTargetOf D (flockSoundInstance 18) s ch fd t vals rho lam)
    (hW : WeightMle D (flockSoundInstance 18))
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32) (hdeg : J.degSum ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_reference_walk hD hIv B J hnV hV hprod htarget hW
    (uniWalk D _ J.nV J.V _) (uniWalkReject D _ J.nV J.V
      (uniCodeAt D (flockSoundInstance 18) (hκ_reference D hD) J.nV J.V hnV hV)) hB hdeg hrel

end FlockSound.Uni

/-- info: 'FlockSound.Uni.uniKnowledgeSoundness_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniKnowledgeSoundness_fs

/-- info: 'FlockSound.Uni.uniKnowledgeSoundness_reference_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniKnowledgeSoundness_reference_fs

/-- info: 'FlockSound.Uni.uniKnowledgeSoundness_reference_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniKnowledgeSoundness_reference_walk

/-- info: 'FlockSound.Uni.uniKnowledgeSoundness_bridges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniKnowledgeSoundness_bridges

/-- info: 'FlockSound.Uni.uniKnowledgeSoundness_reference_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniKnowledgeSoundness_reference_game
