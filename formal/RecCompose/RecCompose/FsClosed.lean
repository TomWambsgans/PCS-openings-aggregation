-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Final.lean`'s end theorems with π2's Fiat–Shamir layer
-- proved (`pi2FsLayer_real`), as `formal/UniSound/UniSound/FsFinal128.lean`'s `fsLayer128_holds` for π1.
import RecCompose.Final
import RecCompose.Meanings
import RecCompose.Layouts
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

**`recKnowledgeSoundness_reduction`** (the headline end-to-end soundness theorem), **`recKnowledgeSoundness2_closed`**,
**`recKnowledgeSoundness_closed`**, **`recKnowledgeSoundness_closed_fs`**: `Final.lean`'s
end theorems without `hfs` (and, `lean-pi2-complete`, without `hcol`: `pi2SetupColumns_of_real`), and (`lean-pi2-facts`)
without the circuit's facts and the ports' and calls' meaning: `Fa` is `pi2Facts hD C hchk` (`Facts.lean`), `hstmt`,
`hzero`, `hcalls` are `statementPortMeaning`, `zeroPortsMeaning`, `callWordsAgree` (`Meanings.lean`), `hlay` is
`pi1CallsLayouts_of_real` (`Layouts.lean`). Their inputs left: the compiled circuits `C : Pi2Circuits D` at the emitted
graph's roots (`hroots`), the Lean recording the emitted graph (`GraphsAgree`), and the view check `Pi2ViewChecked C`,
all three **checked by evaluation** (`rec-circuit-emitted`, `RecGraphTest/Pi1Check.lean`, `rec-view-check`).
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

/-- **π2's part, at the real deployment, closed in its Fiat–Shamir layer and the circuit's facts**:
`RecKnowledgeSoundness2 D pi2Bound`, `pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64` (128.93 bits as `Q / ε2`). -/
theorem recKnowledgeSoundness2_closed (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (hchk : Pi2ViewChecked C) :
    RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  recKnowledgeSoundness2_final D hD C (pi2Facts hD C hchk) (pi2FsLayer_real D hD) hroots hg
    (statementPortMeaning hD C hchk) (zeroPortsMeaning hD C hchk) (callWordsAgree hD C hchk) (pi1CallsLayouts_of_real hD)

/-- **The recursive verifier's knowledge soundness, end to end, as an explicit reduction** (against Lv42's `M3Holds`,
closed in π2's Fiat–Shamir layer and the circuit's facts): `RecKnowledgeSoundnessReduction D pi2Bound`, and
`pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64`. For every adversary `A` of `Q` calls of `π` and `π⁻¹` against the recursive
verifier, the derived adversaries `pi1Adversary D A` and `hazardAdversary D A` (`A`, then π2's explicit extractor)
make at most `Q` calls, and

`Pr[the contract accepts ∧ recExtractor fails] ≤ pi2Bound Q + Pr[pi1Adversary D A breaks π1-rec3 at Keccak-f[1600]]
                                                    + Pr[hazardAdversary D A hits the merge hazard on an accepted stream]`.

No Fiat–Shamir hypothesis: bounding the last two terms is the Fiat–Shamir heuristic for Keccak-f[1600], applied by the
reader to two explicit adversaries that run in `A`'s time plus π2's extractor's. -/
theorem recKnowledgeSoundness_reduction (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (hchk : Pi2ViewChecked C) :
    RecKnowledgeSoundnessReduction D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  ⟨recKnowledgeSoundnessReduction_final D hD C (pi2Facts hD C hchk) (pi2FsLayer_real D hD) hroots hg
    (statementPortMeaning hD C hchk) (zeroPortsMeaning hD C hchk) (callWordsAgree hD C hchk) (pi1CallsLayouts_of_real hD),
    pi2Bound_le_bits⟩

/-- **End to end, against Lv42's `M3Holds`, closed in π2's Fiat–Shamir layer and the circuit's facts**, the Prop-premise
corollary (`Pi1FsKeccak`, `Pi1HazardKeccak`: false as stated for unbounded adversaries). -/
theorem recKnowledgeSoundness_closed (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (hchk : Pi2ViewChecked C) (ε1 εh : ℕ → ℝ≥0∞) :
    RecKnowledgeSoundness D pi2Bound ε1 εh :=
  recKnowledgeSoundness_final D hD C (pi2Facts hD C hchk) (pi2FsLayer_real D hD) hroots hg
    (statementPortMeaning hD C hchk) (zeroPortsMeaning hD C hchk) (callWordsAgree hD C hchk) (pi1CallsLayouts_of_real hD)
    ε1 εh

/-- **End to end under `Pi1FsKeccak` and `Pi1HazardKeccak` alone, closed in π2's Fiat–Shamir layer and the circuit's
facts**. The two premises are false as stated (they quantify over adversaries that grind Keccak-f[1600] offline for
free): read them as the Fiat–Shamir heuristic for adversaries of bounded Keccak-f[1600] work, which Lean does not
model. The statement without them is `recKnowledgeSoundness_reduction`. -/
theorem recKnowledgeSoundness_closed_fs (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (hchk : Pi2ViewChecked C) (ε1 εh : ℕ → ℝ≥0∞)
    (h1 : Pi1FsKeccak D ε1) (hh : Pi1HazardKeccak D εh) :
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ pi2Bound Q + ε1 Q + εh Q :=
  recKnowledgeSoundness_final_fs D hD C (pi2Facts hD C hchk) (pi2FsLayer_real D hD) hroots hg
    (statementPortMeaning hD C hchk) (zeroPortsMeaning hD C hchk) (callWordsAgree hD C hchk) (pi1CallsLayouts_of_real hD)
    ε1 εh h1 hh

end RecCompose

/-- info: 'RecCompose.pi2FsLayer_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2FsLayer_real

/-- info: 'RecCompose.recKnowledgeSoundness2_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_closed

/-- info: 'RecCompose.recKnowledgeSoundness_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_reduction

/-- info: 'RecCompose.recKnowledgeSoundness_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_closed

/-- info: 'RecCompose.recKnowledgeSoundness_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_closed_fs
