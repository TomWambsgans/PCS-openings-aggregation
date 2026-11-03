-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `formal/UniStatement`'s
-- `UniKnowledgeSoundness` (`Security.lean`); the end theorem it instantiates is
-- `formal/FlockSound/FlockSoundUni/Game.lean`'s `uniKnowledgeSoundness_fs`.
import FlockSoundUni.Game
import FlockSoundUni.Good
import UniSound.Ids.Align
import UniSound.Ids.WeightMle
import UniSound.Ids.Remaining

/-!
# Knowledge soundness of the univariate verifier for leanVM 42422001, closed

**`uniKnowledgeSoundness_closed`**: for every deployment at the reference shape (`reference`: 1,000
signatures, heights `18 18 18 18 17 18`, memory `2^21`, bytecode `2^19`) with leanVM's program IV
(`programIv`), and **every program**, the univariate verifier is knowledge sound against leanVM
42422001's relation for the explicit extractor `uniExtractor`, with error `uniBound (2^32 / |E|) Q` at
`Q` calls of `π` and `π⁻¹`, at most `2^-61` for `Q ≤ 2^64` (`2^-61.41` at `Q = 2^64`:
`EndToEnd/Review/UniSoundnessNumbers.py`, exact rationals). **No hypothesis.**

It is `FlockSound.Uni.uniKnowledgeSoundness_fs` (Flock's instance, the code-level and last links, the
Fiat–Shamir layer `fsLayer_holds`) at `κ = h_B` with:

* the bus model and the identity model of `formal/UniSound/UniSound/Ids` (`busModelRef`, `idsRestRef`
  at `idsRemainingRef`: degrees `≤ 50,708,397`, `≤ 135` relations), the values read at `t` counted as
  the code reads them (`nVOf_eq_of`, `valsCount ≤ 122`);
* the batch the verifier's (`batchIsVerifiers_of`, `Ids/Align.lean`), Flock's result the main line's
  (`flockGood`, `FlockSoundUni/Good.lean`);
* the weights multilinear off `Z_bad`'s roots (`weightMle_ref`, from `Ids/WeightMle.lean`'s
  `combAt_mle` and the alignment);
* the counts in range from the chain program's round-`0` zero (`countsZero`, inside
  `uniKnowledgeSoundness_fs`'s last link);
* the numbers: `4 N + ncv ≤ 2^32` (`busBound_reference`, `ncvOf_eq`), the identities' and `Z_bad`'s
  degrees `≤ 2^32` (`50,708,397 + 2^19`), `135 + 2 ≤ 2^32`, and the reference shape's from
  `GameNumbers.lean` (`uniShapes_reference`, `layoutVarsSmall_reference`, `uniIv_of`, `hnQ_flock'`,
  `hnv_flock`, `hFl_flock`).
-/

namespace UniSound.Closed

open UniStatement LeanVM.Parameters FlockSound.Uni UniSound.Ids
open scoped ENNReal

-- A combined claim and the ring map are matched, never computed: unfolding them reaches `relsOf` on
-- the tables (the elaborator's lazy unfolding otherwise picks them before a pair's projection).
attribute [local irreducible] UniSound.Ids.combAt UniSound.Ids.ringMapAt

section Ref

variable (D : Deployment) (hD : D.shape = reference)

/-- **The identity model's rest at the reference deployment** (`idsRestRef` at `idsRemainingRef`),
for Flock's instance at the deployment's `BLAKE2S` height. -/
noncomputable def idsRef :
    UniIdsRest D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) (busModelRef D hD) :=
  idsRestRef D hD _ 50708397 135 (idsRemainingRef D hD _)

/-- **The values read at `t`** are the code's (`nVOf_eq_of`, `valsCount ≤ 122`). -/
theorem idsRef_nV : (idsRef D hD).nV = valsCount := by
  show nVOf D.shape = valsCount
  refine nVOf_eq_of D.shape ?_
  have h : tablesReads + 7 ≤ 122 := valsCount_le
  omega

/-- **The identity model's batch is the verifier's** (`batchIsVerifiers_of`, Flock's result the main
line's by `flockGood`). -/
theorem batchIsVerifiers_ref :
    BatchIsVerifiers D (flockSoundInstance (D.shape.heights.getD opBlake2s 0))
      (UniIds.ofBus (flockSoundInstance _) (busModelRef D hD) (idsRef D hD)) :=
  batchIsVerifiers_of D _ (busModelRef D hD) (idsRef D hD) rfl rfl
    fun fd hfd ↦ flockGood _ _ (batchVars_ge D.shape) fd hfd

/-- **The weights are multilinear off `Z_bad`'s roots** (`WeightMle` at the identity model's merge
polynomial): the run's claims are the commitments' combined claims (`runClaims_eq`), each
multilinear (`combAt_mle_ref`). -/
theorem weightMle_ref :
    WeightMle D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) (idsRef D hD).zb := by
  intro s ch fd t vals rho r _ hfd hch _ hz hr x hx
  obtain ⟨h1, h2⟩ := runClaims_eq D (flockSoundInstance _) s ch fd t vals rho (by omega)
  rw [h1] at hx
  rw [h2, ← batchVars_eq]
  rw [← batchVars_eq] at hr
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
  rw [layoutOf_eq]
  have hz' : (zBad D.shape (((flockSoundInstance (D.shape.heights.getD opBlake2s 0)).prog.out fd []).1.getD
      0 0)).eval t ≠ 0 := hz
  have hg := flockGood (D.shape.heights.getD opBlake2s 0) (batchVars D.shape) (batchVars_ge D.shape) fd hfd
  have key := combAt_mle_ref D hD (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s ch fd t vals
    rho hg hz' r hr c
  exact key

/-- **Round `0`'s error**: `4 N + ncv ≤ 2^32` (`busBound_reference`, `ncvOf_eq`). -/
theorem hB_ref : 4 * (busModelRef D hD).N + (busModelRef D hD).ncv ≤ 2 ^ 32 := by
  show 4 * busBound D.shape + ncvOf D.shape ≤ 2 ^ 32
  rw [ncvOf_eq, hD]
  exact le_trans (Nat.add_le_add_left (by norm_num : (30 : ℕ) ≤ 100) _) busBound_reference

/-- **`t`'s error**: the identities' degrees and `Z_bad`'s, `50,708,397 + 2^19 ≤ 2^32`. -/
theorem hdeg_ref : (idsRef D hD).degSum + (idsRef D hD).degBad ≤ 2 ^ 32 := by
  show 50708397 + zBadDeg D.shape ≤ 2 ^ 32
  unfold zBadDeg
  rw [Eval.coordinateFunctionals_size, hκ_reference D hD]
  norm_num

/-- **`ρ, λ`'s error**: `135` relations. -/
theorem hrel_ref : (idsRef D hD).nRel + 2 ≤ 2 ^ 32 := by
  show max 135 1 + 2 ≤ 2 ^ 32
  norm_num

end Ref

/-- **Knowledge soundness of the univariate verifier for leanVM 42422001, closed**: for every
deployment at the reference shape with leanVM's program IV (and every program), the verifier is
knowledge sound for the explicit extractor `uniExtractor`, with error `uniBound (2^32 / |E|) Q` at
`Q` calls of `π` and `π⁻¹`, at most `2^-61` for `Q ≤ 2^64`. No hypothesis. -/
theorem uniKnowledgeSoundness_closed (D : Deployment) (hD : D.shape = reference)
    (hIv : D.programIv = programIv) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_fs (D.shape.heights.getD opBlake2s 0) rfl (busModelRef D hD) (idsRef D hD)
    (idsRef_nV D hD) rfl (batchIsVerifiers_ref D hD) (weightMle_ref D hD)
    (layoutVarsSmall_reference D hD) (uniShapes_reference D hD) (uniIv_of D hIv)
    (hnQ_flock' _ _ _ (by rw [hκ_reference D hD]; decide)
      (by have := varsOf_reference_le D hD; omega))
    (hnv_flock _ _) (hB_ref D hD) (hFl_flock _ (by rw [hκ_reference D hD]; decide))
    (hdeg_ref D hD) (hrel_ref D hD)

end UniSound.Closed

/-- info: 'UniSound.Closed.uniKnowledgeSoundness_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Closed.uniKnowledgeSoundness_closed

/-- info: 'UniSound.Closed.weightMle_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Closed.weightMle_ref

/-- info: 'UniSound.Closed.batchIsVerifiers_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Closed.batchIsVerifiers_ref
