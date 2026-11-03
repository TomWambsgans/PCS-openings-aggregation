-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Closed.lean`'s
-- `uniKnowledgeSoundness_closed` with `FsGame128.lean`'s Fiat–Shamir layer (`fsLayer128_holds`) in
-- place of `fsLayer_holds`; every other link is `Closed.lean`'s.
import UniSound.Closed
import UniSound.FsFinal128

/-!
# Knowledge soundness of the univariate verifier for leanVM 42422001, closed, at `≥ 128` bits

**`uniKnowledgeSoundness_closed128`**: `uniKnowledgeSoundness_closed` with the error
`uniBound128 (2^32 / |E|) Q`, **at most `2^-64` for `Q ≤ 2^64`** (`2^-64.87` at `Q = 2^64`, 128.87 bits
as `Q / ε`: `EndToEnd/Review/UniSoundnessNumbers128.py`, exact rationals). No hypothesis.

The bound's three changes against `uniBound` (`Fs128.lean`): the five WHIR openings charged once, as
one union family whose bad events are per fresh query (`Compose.prEvent_doomF_le`), at the exact
certified per-group bound `269 · 2^-137` (`WhirBridge.εExact`) instead of `5 · 2^-128` per query; the
seed separated by a pair of answers (`name ‖ iv[0:16]`, `iv` an answer: `2 N² / 2^256`) instead of a
tag (`2^-128` per query); the rest as `uniBound`'s.

The route: `fsLayer128_holds` (the Fiat–Shamir layer at `uniBound128`, from the coupling
`uniGameLeV_holds`), then `Final.lean`'s `uniKnowledgeSoundness` step with `FsLayer128`
(`uniKnowledgeSoundness128`: the PIOP `uniPiop`, its errors `uniErr_le`, round `0`'s relation
`hpre_uniPiop`, the last link `hlink_uniPiop` of `uniFinal`), at `Closed.lean`'s reference instance
(`idsRef`, `busModelRef`, `batchIsVerifiers_ref`, `weightMle_ref`, `hB_ref`, `hdeg_ref`, `hrel_ref`).
-/

namespace UniSound.Closed

open UniStatement LeanVM.Parameters FlockSound.Uni UniSound.Ids
open scoped ENNReal

attribute [local irreducible] UniSound.Ids.combAt UniSound.Ids.ringMapAt

/-- **`uniKnowledgeSoundness` with the Fiat–Shamir layer at `≥ 128` bits** (`Final.lean`'s step, with
`FsLayer128`). -/
theorem uniKnowledgeSoundness128 {D : Deployment} {κ : ℕ} (hFlock : FlockSound κ)
    (I : UniIds D hFlock) (C : UniCode D hFlock I.nV I.V) (hFin : UniFinal D hFlock I C)
    (hFs : FsLayer128 D hFlock I.nV I.V C)
    (hMain : I.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 32) (hrel : I.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) :=
  hFs (uniPiop hFlock I) _ (uniErr_le hFlock I hMain hFl hdeg hrel) (hpre_uniPiop hFlock I)
    (hlink_uniPiop hFlock I C hFin)

/-- **Knowledge soundness of the univariate verifier for leanVM 42422001, closed, at `≥ 128` bits**:
for every deployment at the reference shape with leanVM's program IV (and every program), the
verifier is knowledge sound for the explicit extractor `uniExtractor`, with error
`uniBound128 (2^32 / |E|) Q` at `Q` calls of `π` and `π⁻¹`, at most `2^-64` for `Q ≤ 2^64`. No
hypothesis. -/
theorem uniKnowledgeSoundness_closed128 (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundness D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  refine ⟨?_, uniBound128_le_bits⟩
  have hnV : (idsRef D hD).nV = valsCount := idsRef_nV D hD
  have hnQ : (uSpec (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) (idsRef D hD).nV
      (idsRef D hD).V).K.nQ ≤ 2 ^ 10 :=
    hnQ_flock' _ _ _ (by rw [hκ_reference D hD]; decide)
      (by have := varsOf_reference_le D hD; show varsOf (layoutsOf D.shape) ≤ 64; omega)
  have hnv : ∀ r ∈ uRounds (flockSoundInstance (D.shape.heights.getD opBlake2s 0))
      (idsRef D hD).nV (idsRef D hD).V, r.nv ≤ 2 ^ 30 :=
    hnv_flock' _ _ _ (by rw [hnV]; exact valsCount_le.trans (by decide))
  have hFs := fsLayer128_holds D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) rfl
    (idsRef D hD).nV (idsRef D hD).V hnV rfl (uniShapes_reference D hD)
    (layoutVarsSmall_reference D hD) (uniIv_of D hIv) hnQ hnv
  exact uniKnowledgeSoundness128 (flockSoundInstance (D.shape.heights.getD opBlake2s 0))
    (UniIds.ofBus (flockSoundInstance _) (busModelRef D hD) (idsRef D hD)) _
    (uniFinal D _ rfl (UniIds.ofBus (flockSoundInstance _) (busModelRef D hD) (idsRef D hD)) hnV rfl
      (batchIsVerifiers_ref D hD) (weightMle_ref D hD) (layoutVarsSmall_reference D hD)
      (flockPendingShaped _))
    hFs ((busModelRef D hD).errMain_le (hB_ref D hD))
    (hFl_flock _ (by rw [hκ_reference D hD]; decide)) (hdeg_ref D hD) (hrel_ref D hD)

end UniSound.Closed

/-- info: 'UniSound.Closed.uniKnowledgeSoundness_closed128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Closed.uniKnowledgeSoundness_closed128
