-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsCouple.lean` (`uniGameLeV_of`)
-- for π1-rec3's experiment (`UniStatement.uniSoundnessExperimentRec3`, `Deployment.verifierRec3With`).
import UniSound.Rec3.FsGame3
import UniSound.FsCouple

/-!
# π1-rec3's experiment and the composed game, coupled

**`uniGameLeV3_of`**: the coupling `UniGameLeV3` from three bridge facts, as `FsCouple.lean`'s:

* **`UniSetupBridge`** (the setup, unchanged: `FsCouple.lean`'s, proved by `uniSetupBridge_of_small`);
* **`UniVerifierBridge3`** (the verifier): from any state of the lazily sampled permutation, the Statement's
  `verifyWithFs … .rec3 true` (the run on the stream, its early stops, the three `PCS_OPEN` calls) accepts at most
  as often as the composed verifier (the chain on `rec3Rounds`, the three openings) satisfies `uniCheck3` and all
  three openings accept;
* **`UniExtractBridge3`** (the extractor's reading, at π1-rec3's view of the stream): a candidate of `C1`'s root
  that the composed extractor reads off the setup's log and the adversary's transcript, satisfying the relation,
  makes the Statement's `uniExtractor` (unchanged) find a stack satisfying it.

The proof is `FsCouple.lean`'s: the common prefix (`prefixU`), then both verifiers first compute π1-rec3's IV, the
same Keccak-256 call (`ivRec3With_eq`), then `step_le3`.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## The bridge facts -/

section Bridges

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
  (hs : UniShapes D)

/-- **VERIFIER** (π1-rec3): from any state of the lazily sampled permutation, the Statement's π1-rec3 verifier on
a proof (its IV, roots, input and univariate proof) accepts at most as often as the composed verifier on it passes
`uniCheck3` with every opening accepting. -/
def UniVerifierBridge3 : Prop :=
  ∀ (π : UPf) (s : Common.PermutationEdges KeccakState),
    Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
        (verifyWithFs Common.queryPermutation D.shape π.iv.toList π.roots π.input π.proof .rec3 true)).run' s}[
        b = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (verU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np))
            (opsRun (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)) π))).run' s}[
        uniCheck3 D F3 nV np C π v.1 ∧ ∀ k < (uOps3 D F3 nV np C hs).length, v.2.getD k false = true]

/-- **EXTRACTOR READING** (π1-rec3's view): a candidate stack of `C1`'s root that the composed extractor reads off
the setup's log and a permutation transcript, satisfying leanVM 42422001's relation at the proof's statement,
makes the Statement's extractor, on the setup's evaluations and that transcript, find a stack satisfying it. -/
def UniExtractBridge3 : Prop :=
  ∀ (t : SetupTrees) (T : Common.OracleQueryLog) (z : UPf × (List (List E) × List Bool)) (q : Stk),
    some q ∈ extractorK (fun i => (uniTc hs i).commit) (uView (uRounds3 F3 nV np))
        (z, setupTr t ++ evalTr (permutationQueries T)) →
      Rel D (uSt3 F3 nV np z.1) q →
        ∃ q', uniExtractor D z.1.input t.evaluations T z.1.proof = some q' ∧
          D.Relation z.1.proof.rows z.1.input q'

end Bridges

/-! ## The experiments, a common prefix then the verifiers -/

theorem uniSoundnessExperimentRec3_eq (D : Deployment) (A : UniAdversary) :
    uniSoundnessExperimentRec3 D A = Common.runWithRandomPermutation (prefixU D A >>= fun a =>
      D.verifierRec3With Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2 >>= fun acc =>
        pure (((a.2.1, acc), a.1.evaluations, a.2.2) : UniOutcome)) := by
  unfold uniSoundnessExperimentRec3 prefixU
  simp only [bind_assoc, pure_bind]

theorem rpmGameS_eq3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ)
    (C : UniCode3 D F3 nV np) (hs : UniShapes D) (hS : UniSetupBridge D hs) (A : UniAdversary) :
    Common.runWithRandomPermutation
        (rpmGameS (uSetup D hs) uFix (uAdv A) (uVerIv3 D F3 nV np C hs)) =
      Common.runWithRandomPermutation (prefixU D A >>= fun a =>
        simulateQ keccakCallsOverQueryPermutation (uVerIv3 D F3 nV np C hs (piOf a)) >>= fun v =>
          pure ((piOf a, v), setupTr a.1, a.2.2)) := by
  unfold rpmGameS prefixU
  rw [hS]
  simp only [bind_map_left, bind_assoc, pure_bind, run_logged_uAdv, rootsOfS_rootsB, uFix_rootsB]
  rfl

/-! ## The verifiers, outcome by outcome -/

section Step

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
  (hs : UniShapes D)

/-- **One outcome of the setup and the adversary**: π1-rec3's event after the Statement's verifier is at most as
likely as the composed event after the composed verifier, from any state of the permutation. -/
theorem step_le3 (hV : UniVerifierBridge3 D F3 nV np C hs) (hX : UniExtractBridge3 D F3 nV np hs)
    (a : SetupTrees × ((Vector UInt8 32 × UniProof) × Common.OracleQueryLog))
    (s : Common.PermutationEdges KeccakState) :
    Pr{let acc ← (simulateQ Common.lazyRandomPermutationOracles
        (D.verifierRec3With Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2)).run' s}[
        UniBreaksKnowledgeSoundness D (uniExtractor D) (((a.2.1, acc), a.1.evaluations, a.2.2))] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (uVerIv3 D F3 nV np C hs (piOf a)))).run' s}[
        UniBreaksRel3 D F3 nV np C hs
          (ivOut (piOf a, v), setupTr a.1 ++ evalTr (permutationQueries a.2.2))] := by
  -- both verifiers first compute π1-rec3's IV
  have hL : D.verifierRec3With Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2 =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInput3 D a.1.roots)) >>= fun iv =>
        verifyWithFs Common.queryPermutation D.shape iv.toList a.1.roots a.2.1.1 a.2.1.2 .rec3 true := by
    rw [Deployment.verifierRec3With, ivRec3With_eq, bind_map_left]
  have hR : simulateQ keccakCallsOverQueryPermutation (uVerIv3 D F3 nV np C hs (piOf a)) =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInput3 D a.1.roots)) >>= fun iv =>
        (fun v => (iv, v)) <$> simulateQ keccakCallsOverQueryPermutation
          (verU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np))
            (opsRun (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)) (setIv iv (piOf a))) := by
    rw [uVerIv3, simulateQ_bind]
    simp only [simulateQ_map]
    rfl
  rw [hL, hR]
  refine Soundness.mono_bind Common.lazyRandomPermutationOracles _ _ _ _ _ (fun iv s' => ?_) s
  -- the Statement's extractor finds a stack: no break
  by_cases hext : ∃ q, uniExtractor D a.2.1.1 a.1.evaluations a.2.2 a.2.1.2 = some q ∧
      D.Relation a.2.1.2.rows a.2.1.1 q
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ ?_)) zero_le
    intro acc _ hb
    exact hb.2 hext
  -- otherwise no candidate of the composed extractor satisfies the relation
  have hnone : ∀ (v : List (List E) × List Bool), ∀ c ∈ extractorK (fun i => (uniTc hs i).commit)
      (uView (uRounds3 F3 nV np))
      ((setIv iv (piOf a), v), setupTr a.1 ++ evalTr (permutationQueries a.2.2)),
      ∀ q, c = some q → ¬ Rel D (uSt3 F3 nV np (setIv iv (piOf a))) q := by
    intro v c hc q hq hrel
    subst hq
    exact hext (hX a.1 a.2.2 (setIv iv (piOf a), v) q hc hrel)
  have hacc := hV (setIv iv (piOf a)) s'
  calc _ ≤ Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
          (verifyWithFs Common.queryPermutation D.shape iv.toList a.1.roots a.2.1.1 a.2.1.2 .rec3
            true)).run' s'}[b = true] := prEvent_mono _ _ _ fun b hb => hb.1
    _ ≤ _ := hacc
    _ ≤ _ := by
      rw [run'_map_lazy, prEvent_map]
      exact prEvent_mono _ _ _ fun v hv => ⟨hv.1, hv.2, hnone v⟩

end Step

/-! ## The coupling -/

/-- **The coupling from the bridge facts**: the setup bridge, π1-rec3's verifier bridge and the extractor's reading
make π1-rec3's experiment's break at most as likely as the composed game's. -/
theorem uniGameLeV3_of (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ)
    (C : UniCode3 D F3 nV np) (hs : UniShapes D) (hS : UniSetupBridge D hs)
    (hV : UniVerifierBridge3 D F3 nV np C hs) (hX : UniExtractBridge3 D F3 nV np hs) :
    UniGameLeV3 D F3 nV np C hs := by
  intro A
  rw [uniSoundnessExperimentRec3_eq D A, rpmGameS_eq3 D F3 nV np C hs hS A]
  exact Soundness.prEvent_le_of_continuations (prefixU D A)
    (fun a => D.verifierRec3With Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2)
    (fun a => simulateQ keccakCallsOverQueryPermutation (uVerIv3 D F3 nV np C hs (piOf a)))
    (fun a acc => (((a.2.1, acc), a.1.evaluations, a.2.2) : UniOutcome))
    (fun a v => ((piOf a, v), setupTr a.1, a.2.2))
    (UniBreaksKnowledgeSoundness D (uniExtractor D))
    (fun z => UniBreaksRel3 D F3 nV np C hs (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2)))
    fun a s => step_le3 D F3 nV np C hs hV hX a s

end UniSound

/-- info: 'UniSound.uniGameLeV3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniGameLeV3_of
