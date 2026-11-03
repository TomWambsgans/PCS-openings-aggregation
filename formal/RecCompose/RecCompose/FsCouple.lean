-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `formal/UniSound/UniSound/FsCouple.lean`
-- (`prefixU`, `uniSoundnessExperiment_eq`, `rpmGameS_eq`, `step_le`, `uniGameLeV_of`), with
-- `formal/EndToEnd/Soundness/Final.lean`'s `prEvent_le_of_continuations`.
import RecCompose.FsVerifier
import RecCompose.FsExtract
import RecCompose.FsWalk
import Soundness.Final

/-!
# π2's experiment and the composed game, coupled

**`pi2GameLeV`**: the coupling `Pi2GameLeV` (π2's experiment's break, `Pi2FsLayer`'s event, is at most as likely as the
composed random-permutation game's, `rpmGameS` of `p2Setup`, `p2Adv` and the composed verifier with π2's IV `p2Ver`,
the event `P2BreaksRel` on the proof with its IV and the setup's log and the adversary's Keccak-256 evaluations), from
the setup bridge (`pi2SetupBridge`), the verifier bridge (`Pi2VerifierBridge`, a hypothesis here) and the extractor's
reading (`pi2ExtractBridge`):

* both experiments are the setup's trees and the adversary given their roots, its queries logged (`prefix2`,
  `recSoundnessExperiment2_eq`, `rpmGameS2_eq` by the setup bridge: `p2Adv A (rootsB2 t)` is `A t.roots`, since
  `rootsOfOut (rootsB2 t) = t.roots`), then their verifiers on the same state of the permutation
  (`Soundness.prEvent_le_of_continuations`);
* there both first compute π2's IV, the same four Keccak-256 calls (`ivWith_eq_p2IvKC4`: the circuit's digest's three,
  then the IV's), then (`step2_le`) π2's event is impossible if π2's extractor's list holds a candidate with `P`, and
  otherwise follows from the contract's acceptance, which the verifier bridge bounds by the composed check with the six
  openings accepting, on whose outcomes `P2BreaksRel` holds: the check gives the stream's `944` bytes, so every
  composed candidate is in π2's extractor's list (`pi2ExtractBridge`), at the setup's roots and the statement's
  public scalars (`pi2Pubs_pubBytes`, `pi2Scalars_real`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local instance high] Completeness.instSampleableTypeE_completeness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack RecStatement.layoutWords

/-! ## The coupling's statement -/

/-- **The game bridge**: π2's experiment's break (the contract accepts while no candidate of `W`'s committed word has
`P`) is at most as likely as the composed random-permutation game's, of the setup's four trees, π2's adversary
(`p2Adv`) and the composed verifier with π2's IV (`p2Ver`), the event read on the proof with its IV (`ivOut2`), the
setup's log and the Keccak-256 evaluations of the adversary's permutation transcript. -/
def Pi2GameLeV (D : RecDeployment) (hs : UniSound.UniShapes D.pi1) (P : RecSetupRoots → Pi2St → Stk → Prop) : Prop :=
  ∀ A : RecAdversary,
    Pr{let z ← recSoundnessExperiment2 D A}[acc z = true ∧
        ¬ ∃ w ∈ outcomeCandidates D z, P (rts z) (pi2StmtOf D z) (stkOf w)] ≤
      Pr{let z ← Common.runWithRandomPermutation (rpmGameS (p2Setup D hs) p2Fix (p2Adv A) (p2Ver D))}[
        P2BreaksRel D P (ivOut2 z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))]

/-! ## The common prefix -/

/-- The proof the composed game's verifier reads, from the setup's trees and the adversary's output. -/
def piOf2 (a : RecSetupTrees × ((Vector UInt8 32 × RecProof) × Common.OracleQueryLog)) : P2Pf :=
  ⟨a.2.1.1, a.2.1.2, Vector.replicate 32 0, rootsB2 a.1⟩

/-- **The common prefix**: the setup's trees over `π`, then the adversary given their roots, its queries logged. -/
noncomputable def prefix2 (D : RecDeployment) (A : RecAdversary) :
    OracleComp Common.RandomPermutationOracles
      (RecSetupTrees × ((Vector UInt8 32 × RecProof) × Common.OracleQueryLog)) :=
  D.setupTreesWith Common.queryPermutation >>= fun t =>
    (simulateQ Common.loggedOracles (A t.roots)).run [] >>= fun p => pure (t, p)

theorem recSoundnessExperiment2_eq (D : RecDeployment) (A : RecAdversary) :
    recSoundnessExperiment2 D A = Common.runWithRandomPermutation (prefix2 D A >>= fun a =>
      D.contractWith Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2 >>= fun v =>
        pure (((a.2.1, v.1), a.1.evaluations, a.2.2, a.1.roots, v.2) : RecOutcome2)) := by
  unfold recSoundnessExperiment2 prefix2
  simp only [bind_assoc, pure_bind]

theorem rootsOfOut_rootsB2 (t : RecSetupTrees) : rootsOfOut (rootsB2 t) = t.roots := by
  unfold rootsOfOut rootsB2 RecSetupTrees.roots
  rw [show UniSound.rootsOfS (toB t.pi1.bytecode.root, toB t.pi1.a0.root, toB t.pi1.b0.root) = t.pi1.roots from
    UniSound.rootsOfS_rootsB t.pi1, Soundness.ofB_toB_root]

theorem run_logged_p2Adv (A : RecAdversary) (s : SOut) :
    (simulateQ Common.loggedOracles (p2Adv A s)).run [] =
      (fun p => ((⟨p.1.1, p.1.2, Vector.replicate 32 0, s⟩ : P2Pf), p.2)) <$>
        (simulateQ Common.loggedOracles (A (rootsOfOut s))).run [] := by
  rw [p2Adv, simulateQ_map, StateT.run_map]

theorem rpmGameS2_eq (D : RecDeployment) (hs : UniSound.UniShapes D.pi1) (hS : Pi2SetupBridge D hs)
    (A : RecAdversary) :
    Common.runWithRandomPermutation (rpmGameS (p2Setup D hs) p2Fix (p2Adv A) (p2Ver D)) =
      Common.runWithRandomPermutation (prefix2 D A >>= fun a =>
        simulateQ keccakCallsOverQueryPermutation (p2Ver D (piOf2 a)) >>= fun v =>
          pure ((piOf2 a, v), setupTr2 a.1, a.2.2)) := by
  unfold rpmGameS prefix2
  rw [hS]
  simp only [bind_map_left, bind_assoc, pure_bind, run_logged_p2Adv, rootsOfOut_rootsB2]
  rfl

/-! ## π2's IV -/

/-- **The Statement's IV is the composed one**: the circuit's digest's three Keccak-256 calls, then the IV's, over `π`. -/
theorem ivWith_eq_p2IvKC4 (D : RecDeployment) (hD : RecDeployment.Real D) (π : P2Pf) :
    D.ivWith Common.queryPermutation (p2Roots π) =
      (fun x => x.2.2.2.toList) <$> simulateQ keccakCallsOverQueryPermutation (p2IvKC4 D π) := by
  have hlog : (D.circuitAt (p2Roots π).pi1).circuit.logN = cc.logN := by
    rw [RecDeployment.circuitAt, hD.1]
  unfold RecDeployment.ivWith Pi2Circuit.digestWith RecStatement.ivWith p2IvKC4 ivIn digIn sigmaBytes kappaBytes
  dsimp only
  rw [hlog]
  generalize RecStatement.layoutWords cc.logN = lw
  obtain ⟨w, q, s⟩ := lw
  simp only [simulateQ_bind, simulateQ_pure, UniSound.simulateQ_hash256, bind_map_left, map_bind, map_pure,
    bind_assoc, pure_bind, Bridge.toB_toList]

theorem p2Roots_piOf2 (a : RecSetupTrees × ((Vector UInt8 32 × RecProof) × Common.OracleQueryLog)) :
    p2Roots (piOf2 a) = a.1.roots :=
  rootsOfOut_rootsB2 a.1

/-! ## The verifiers, outcome by outcome -/

section Step

variable (D : RecDeployment) (hD : RecDeployment.Real D) (P : RecSetupRoots → Pi2St → Stk → Prop)

/-- **The statement's public scalars at the composed view**, on a stream of `944` bytes. -/
theorem stOf_p2View (hD : RecDeployment.Real D) (π : P2Pf) (hsz : π.proof.stream.size = sLen) :
    stOf (p2View π).1 = (π.input, pi2Scalars D (p2Roots π) π.input π.proof.stream) := by
  show (π.input, pi2Pubs (Spec.of cc) π.input.toList (pubBytes π.proof.stream).toArray) = _
  rw [pi2Pubs_pubBytes _ _ (by rw [hsz]; decide), pi2Scalars_real D hD.1 _ π.input π.proof.stream hsz]

include hD in
/-- **One outcome of the setup and the adversary**: π2's event after π2's contract is at most as likely as the
composed event after the composed verifier, from any state of the permutation. -/
theorem step2_le (hV : Pi2VerifierBridge D)
    (a : RecSetupTrees × ((Vector UInt8 32 × RecProof) × Common.OracleQueryLog))
    (s : Common.PermutationEdges LeanVM.Semantics.KeccakState) :
    Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
        (D.contractWith Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2)).run' s}[
        (fun z : RecOutcome2 => acc z = true ∧
          ¬ ∃ w ∈ outcomeCandidates D z, P (rts z) (pi2StmtOf D z) (stkOf w))
          ((a.2.1, v.1), a.1.evaluations, a.2.2, a.1.roots, v.2)] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (p2Ver D (piOf2 a)))).run' s}[
        (fun z : (P2Pf × ((Bytes32 × Bytes32 × Bytes32 × Bytes32) × (List (List E) × List Bool))) ×
            Transcript × Common.OracleQueryLog =>
          P2BreaksRel D P (ivOut2 z.1, z.2.1 ++ evalTr (permutationQueries z.2.2)))
          ((piOf2 a, v), setupTr2 a.1, a.2.2)] := by
  -- both first compute π2's IV
  have hL : D.contractWith Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2 =
      simulateQ keccakCallsOverQueryPermutation (p2IvKC4 D (piOf2 a)) >>= fun x =>
        contractRest Common.queryPermutation D (p2Roots (piOf2 a)) x.2.2.2.toList a.2.1.1 a.2.1.2 := by
    rw [contractWith_eq, ← p2Roots_piOf2, ivWith_eq_p2IvKC4 D hD, bind_map_left]
  have hR : simulateQ keccakCallsOverQueryPermutation (p2Ver D (piOf2 a)) =
      simulateQ keccakCallsOverQueryPermutation (p2IvKC4 D (piOf2 a)) >>= fun x =>
        (fun v => (x, v)) <$> simulateQ keccakCallsOverQueryPermutation
          (verU pi2Spec p2View (opsRun p2View (p2Ops D)) (setIv2 x.2.2.2 (piOf2 a))) := by
    rw [p2Ver, simulateQ_bind]
    simp only [simulateQ_map]
  rw [hL, hR]
  refine Soundness.mono_bind Common.lazyRandomPermutationOracles _ _ _ _ _ (fun x s' => ?_) s
  -- π2's extractor finds a candidate with `P`: no break
  by_cases hext : ∃ w ∈ wCandidates D a.1.roots (preimagesOf a.1.evaluations a.2.2) a.2.1.2,
      P a.1.roots (a.2.1.1, pi2Scalars D a.1.roots a.2.1.1 a.2.1.2.stream) (stkOf w)
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ ?_)) zero_le
    intro v _ hb
    exact hb.2 hext
  -- otherwise no candidate of the composed extractor has `P`, on a stream of `944` bytes
  have hnone : ∀ v : List (List E) × List Bool, p2Check (setIv2 x.2.2.2 (piOf2 a)) v.1 →
      ∀ c ∈ extractorK (fun i => (p2Tc i).commit) p2View
        ((setIv2 x.2.2.2 (piOf2 a), v), setupTr2 a.1 ++ evalTr (permutationQueries a.2.2)),
        ∀ q, c = some q → ¬ P (p2Roots (setIv2 x.2.2.2 (piOf2 a)))
          (stOf (p2View (setIv2 x.2.2.2 (piOf2 a))).1) q := by
    intro v hc c hcm q hq hP
    subst hq
    have hsz : (setIv2 x.2.2.2 (piOf2 a)).proof.stream.size = sLen := hc.1
    obtain ⟨w, hw, hwq⟩ := pi2ExtractBridge D hD a.1 a.2.2 (setIv2 x.2.2.2 (piOf2 a), v) q
      (by rw [hsz]; decide) hcm
    refine hext ⟨w, hw, ?_⟩
    rw [hwq]
    rw [stOf_p2View D hD _ hsz] at hP
    have hr : p2Roots (setIv2 x.2.2.2 (piOf2 a)) = a.1.roots := p2Roots_piOf2 a
    rw [hr] at hP
    exact hP
  have hacc := hV (setIv2 x.2.2.2 (piOf2 a)) s'
  calc _ ≤ Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (contractRest Common.queryPermutation D
          (p2Roots (piOf2 a)) x.2.2.2.toList a.2.1.1 a.2.1.2)).run' s'}[v.1 = true] :=
        prEvent_mono _ _ _ fun v hv => hv.1
    _ ≤ _ := hacc
    _ ≤ _ := by
      rw [UniSound.run'_map_lazy, prEvent_map]
      exact prEvent_mono _ _ _ fun v hv => ⟨hv.1, hv.2, hnone v hv.1⟩

end Step

/-! ## The coupling -/

/-- **The coupling**: π2's experiment's break is at most as likely as the composed game's, from the setup bridge, the
verifier bridge (`hV`) and the extractor's reading. -/
theorem pi2GameLeV (D : RecDeployment) (hD : RecDeployment.Real D) (hs : UniSound.UniShapes D.pi1)
    (hv : (UniStatement.setupLayout D.pi1.shape).vars < 256) (hV : Pi2VerifierBridge D)
    (P : RecSetupRoots → Pi2St → Stk → Prop) : Pi2GameLeV D hs P := by
  intro A
  rw [recSoundnessExperiment2_eq D A, rpmGameS2_eq D hs (pi2SetupBridge D hD hs hv) A]
  exact Soundness.prEvent_le_of_continuations (prefix2 D A)
    (fun a => D.contractWith Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2)
    (fun a => simulateQ keccakCallsOverQueryPermutation (p2Ver D (piOf2 a)))
    (fun a v => (((a.2.1, v.1), a.1.evaluations, a.2.2, a.1.roots, v.2) : RecOutcome2))
    (fun a v => ((piOf2 a, v), setupTr2 a.1, a.2.2))
    (fun z => acc z = true ∧ ¬ ∃ w ∈ outcomeCandidates D z, P (rts z) (pi2StmtOf D z) (stkOf w))
    (fun z => P2BreaksRel D P (ivOut2 z.1, z.2.1 ++ evalTr (permutationQueries z.2.2)))
    fun a s => step2_le D hD P hV a s

end RecCompose

/-- info: 'RecCompose.pi2GameLeV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2GameLeV

/-- info: 'RecCompose.ivWith_eq_p2IvKC4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.ivWith_eq_p2IvKC4
