-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Final.lean`'s end theorems with π2's Fiat–Shamir layer
-- proved (`pi2FsLayer_real`), as `formal/UniSound/UniSound/FsFinal128.lean`'s `fsLayer128_holds` for π1.
import RecCompose.Final
import RecCompose.FsGame
import RecCompose.FsCouple
import RecCompose.FsCost
import FlockSoundUni.GameNumbers

/-!
# π2's Fiat–Shamir layer, proved, and the end theorems without it

**`pi2FsLayer_real`**: `Pi2FsLayer D` at the real deployment (`RecDeployment.Real D`), no other hypothesis:
`pi2FsLayer_of` (FsGame.lean) with its bridges proved, the coupling `pi2GameLeV` (FsCouple.lean, from the setup's bridge
`pi2SetupBridge`, the verifier's `pi2VerifierBridge` on the walk `pi2Walk`, `pi2WalkReject`, and the extractor's
reading `pi2ExtractBridge`) and the composed verifier's facts (FsCost.lean), π1's shape the reference
(`uniShapes_reference`, `layoutVarsSmall_reference`).

**`recKnowledgeSoundness2_closed`**, **`recKnowledgeSoundness_closed`**, **`recKnowledgeSoundness_closed_fs`**: `Final.lean`'s
end theorems without `hfs` (and, `lean-pi2-complete`, without `hcol`: `pi2SetupColumns_of_real`).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol
open scoped ENNReal

attribute [local instance high] Completeness.instSampleableTypeE_completeness

/-- **π2's Fiat–Shamir layer at the real deployment** (`Pi2FsLayer D`): for every family over the setup's roots of
round-by-round sound protocols on π2's rounds, their errors times the lists of the roots before them at most `e`,
whose first state is a property `P` of `W`'s candidate and whose last state follows from π2's check with the four
claims true, the contract accepts while no candidate of `W`'s committed word has `P` with probability at most
`pi2BoundE e Q`. -/
theorem pi2FsLayer_real (D : RecDeployment) (hD : D.Real) : Pi2FsLayer D := by
  have hs : UniSound.UniShapes D.pi1 := FlockSound.Uni.uniShapes_reference D.pi1 hD.2.2.1
  have hv : (UniStatement.setupLayout D.pi1.shape).vars < 256 :=
    UniSound.layoutOf_setup D.pi1.shape ▸ FlockSound.Uni.layoutVarsSmall_reference D.pi1 hD.2.2.1 .setup
  exact pi2FsLayer_of D hD hs
    (fun P A => pi2GameLeV D hD hs hv (pi2VerifierBridge D hD pi2Walk pi2WalkReject) P A)
    (duplexVm_p2Ver D) (cost_p2Ver D hD) (isTotalQueryBound_p2IvAdv D) (expU_p2IvAdv D hs)
    (extractorK_ivLog D hD) (hlab_p2 D hs) (p2BreaksRel_congr D) (by rw [nQ_p2]; norm_num)

/-- **π2's part, at the real deployment, closed in its Fiat–Shamir layer**: `RecKnowledgeSoundness2 D pi2Bound`,
`pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64` (128.93 bits as `Q / ε2`). -/
theorem recKnowledgeSoundness2_closed (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa) (hcalls : CallWordsAgree D C Fa)
    (hlay : Pi1CallsLayouts D) :
    RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  recKnowledgeSoundness2_final D hD C Fa (pi2FsLayer_real D hD) hroots hg hstmt hzero hcalls hlay

/-- **End to end, against Lv42's `M3Holds`, closed in π2's Fiat–Shamir layer**. -/
theorem recKnowledgeSoundness_closed (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa) (hcalls : CallWordsAgree D C Fa)
    (hlay : Pi1CallsLayouts D) (ε1 εh : ℕ → ℝ≥0∞) : RecKnowledgeSoundness D pi2Bound ε1 εh :=
  recKnowledgeSoundness_final D hD C Fa (pi2FsLayer_real D hD) hroots hg hstmt hzero hcalls hlay ε1 εh

/-- **End to end under the Fiat–Shamir heuristic for Keccak-f[1600] alone, closed in π2's Fiat–Shamir layer**. -/
theorem recKnowledgeSoundness_closed_fs (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa) (hcalls : CallWordsAgree D C Fa)
    (hlay : Pi1CallsLayouts D) (ε1 εh : ℕ → ℝ≥0∞) (h1 : Pi1FsKeccak D ε1) (hh : Pi1HazardKeccak D εh) :
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ pi2Bound Q + ε1 Q + εh Q :=
  recKnowledgeSoundness_final_fs D hD C Fa (pi2FsLayer_real D hD) hroots hg hstmt hzero hcalls hlay ε1 εh h1 hh

end RecCompose

/-- info: 'RecCompose.pi2FsLayer_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2FsLayer_real

/-- info: 'RecCompose.recKnowledgeSoundness2_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_closed

/-- info: 'RecCompose.recKnowledgeSoundness_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_closed

/-- info: 'RecCompose.recKnowledgeSoundness_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_closed_fs
