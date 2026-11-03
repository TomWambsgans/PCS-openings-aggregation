-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows
-- `formal/EndToEnd/Soundness/Final.lean` of this repository (`prEvent_le_of_continuations`,
-- `soundnessExperiment_eq`, `rpmGame_eq`, `step_le`) and `Soundness/Hypotheses.lean` (the bridge
-- facts as propositions about definitions).
import UniSound.FsGame
import Soundness.Final

/-!
# The univariate experiment and the composed game, coupled

**`uniGameLeV_of`**: the coupling `UniGameLeV` from three bridge facts, each a statement about
definitions or one verifier run, as `formal/EndToEnd/Soundness/Hypotheses.lean`'s for the
membership proof:

* **`UniSetupBridge`** (the setup): the composed setup over `π`, logged (`uSetup`: the three trees
  of `stackSetupS` at the plain shapes), is the Statement's `setupTreesWith` over `π`, its roots as
  bytes (`rootsB`) and its log the trees' evaluations (`setupTr`);
* **`UniVerifierBridge`** (the verifier): from any state of the lazily sampled permutation, the
  Statement's `verifyWith` (the run on the stream, its early stops, the five `PCS_OPEN` calls)
  accepts at most as often as the composed verifier (the chain over the univariate encoding and the
  five openings, `verU`) satisfies `uniCheck` and all five openings accept;
* **`UniExtractBridge`** (the extractor's reading): a candidate of `C1`'s root that the composed
  extractor reads off the setup's log and the adversary's permutation transcript, and that satisfies
  leanVM 42422001's relation, makes the Statement's `uniExtractor` find a stack satisfying it.

The proof: both experiments are the setup's trees and the adversary given their roots, its queries
logged (`prefixU`, `uniSoundnessExperiment_eq`, `rpmGameS_eq` by `UniSetupBridge`), then their
verifiers on the same state of the permutation (`Soundness.prEvent_le_of_continuations`); there
both first compute the contract's IV, the same Keccak-256 call (`ivWith_eq`), then (`step_le`) the
Statement's event is impossible if its extractor finds a stack, and otherwise follows from the
verifier's acceptance, which `UniVerifierBridge` bounds by the composed event's.
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

/-- The setup's roots as bytes. -/
def rootsB (t : SetupTrees) : Bytes32 × Bytes32 × Bytes32 :=
  (toB t.bytecode.root, toB t.a0.root, toB t.b0.root)

/-- The setup's Keccak-256 evaluations as a transcript. -/
def setupTr (t : SetupTrees) : Transcript := t.evaluations.map fun e => (e.1, toB e.2)

/-- **SETUP**: the composed setup over `π`, logged, is the Statement's `setupTreesWith` over `π`, its
roots as bytes, its log the trees' evaluations. -/
def UniSetupBridge (D : Deployment) (hs : UniShapes D) : Prop :=
  simulateQ keccakCallsOverQueryPermutation (loggedKC (uSetup D hs)) =
    (fun t : SetupTrees => (rootsB t, setupTr t)) <$> setupTreesWith Common.queryPermutation D

section Bridges

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)
  (hs : UniShapes D)

/-- **VERIFIER**: from any state of the lazily sampled permutation, the Statement's verifier on a
proof (its IV, roots, input and univariate proof) accepts at most as often as the composed verifier
on it passes `uniCheck` with every opening accepting. -/
def UniVerifierBridge : Prop :=
  ∀ (π : UPf) (s : Common.PermutationEdges KeccakState),
    Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
        (verifyWith Common.queryPermutation D.shape π.iv.toList π.roots π.input π.proof)).run' s}[
        b = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (verU (uSpec Fl nV V) (uView (uRounds Fl nV V))
            (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)) π))).run' s}[
        uniCheck D Fl nV V C π v.1 ∧ ∀ k < (uOps D Fl nV V C hs).length, v.2.getD k false = true]

/-- **EXTRACTOR READING**: a candidate stack of `C1`'s root that the composed extractor reads off the
setup's log and a permutation transcript, satisfying leanVM 42422001's relation at the proof's
statement, makes the Statement's extractor, on the setup's evaluations and that transcript, find a
stack satisfying it. -/
def UniExtractBridge : Prop :=
  ∀ (t : SetupTrees) (T : Common.OracleQueryLog) (z : UPf × (List (List E) × List Bool)) (q : Stk),
    some q ∈ extractorK (fun i => (uniTc hs i).commit) (uView (uRounds Fl nV V))
        (z, setupTr t ++ evalTr (permutationQueries T)) →
      Rel D (uSt Fl nV V z.1) q →
        ∃ q', uniExtractor D z.1.input t.evaluations T z.1.proof = some q' ∧
          D.Relation z.1.proof.rows z.1.input q'

end Bridges

/-! ## The experiments, a common prefix then the verifiers -/

theorem rootsOfS_rootsB (t : SetupTrees) : rootsOfS (rootsB t) = t.roots := by
  simp only [rootsOfS, rootsB, SetupTrees.roots, Soundness.ofB_toB_root]

/-- The proof the composed game's verifier reads, from the setup's trees and the adversary's
output. -/
def piOf (a : SetupTrees × ((Vector UInt8 32 × UniProof) × Common.OracleQueryLog)) : UPf :=
  ⟨a.2.1.1, a.2.1.2, Vector.replicate 32 0, a.1.roots⟩

/-- **The common prefix**: the setup's trees over `π`, then the adversary given their roots, its
queries logged. -/
noncomputable def prefixU (D : Deployment) (A : UniAdversary) :
    OracleComp Common.RandomPermutationOracles
      (SetupTrees × ((Vector UInt8 32 × UniProof) × Common.OracleQueryLog)) :=
  setupTreesWith Common.queryPermutation D >>= fun t =>
    (simulateQ Common.loggedOracles (A t.roots)).run [] >>= fun p => pure (t, p)

theorem uniSoundnessExperiment_eq (D : Deployment) (A : UniAdversary) :
    uniSoundnessExperiment D A = Common.runWithRandomPermutation (prefixU D A >>= fun a =>
      D.verifierWith Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2 >>= fun acc =>
        pure (((a.2.1, acc), a.1.evaluations, a.2.2) : UniOutcome)) := by
  unfold uniSoundnessExperiment prefixU
  simp only [bind_assoc, pure_bind]

theorem run_logged_uAdv (A : UniAdversary) (s : Bytes32 × Bytes32 × Bytes32) :
    (simulateQ Common.loggedOracles (uAdv A s)).run [] =
      (fun p => ((⟨p.1.1, p.1.2, Vector.replicate 32 0, rootsOfS s⟩ : UPf), p.2)) <$>
        (simulateQ Common.loggedOracles (A (rootsOfS s))).run [] := by
  rw [uAdv, simulateQ_map, StateT.run_map]

theorem uFix_rootsB (t : SetupTrees) (π : UPf) : uFix (rootsB t) π = { π with roots := t.roots } := by
  rw [← rootsOfS_rootsB t]
  rfl

theorem run'_map_lazy {α β : Type} (f : α → β) (X : OracleComp Common.RandomPermutationOracles α)
    (s : Common.PermutationEdges KeccakState) :
    (simulateQ Common.lazyRandomPermutationOracles (f <$> X)).run' s =
      f <$> (simulateQ Common.lazyRandomPermutationOracles X).run' s := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, StateT.run'_eq,
    Functor.map_map]

theorem rpmGameS_eq (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ)
    (C : UniCode D Fl nV V) (hs : UniShapes D) (hS : UniSetupBridge D hs) (A : UniAdversary) :
    Common.runWithRandomPermutation
        (rpmGameS (uSetup D hs) uFix (uAdv A) (uVerIv D Fl nV V C hs)) =
      Common.runWithRandomPermutation (prefixU D A >>= fun a =>
        simulateQ keccakCallsOverQueryPermutation (uVerIv D Fl nV V C hs (piOf a)) >>= fun v =>
          pure ((piOf a, v), setupTr a.1, a.2.2)) := by
  unfold rpmGameS prefixU
  rw [hS]
  simp only [bind_map_left, bind_assoc, pure_bind, run_logged_uAdv, rootsOfS_rootsB, uFix_rootsB]
  rfl

/-! ## The verifiers, outcome by outcome -/

section Step

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)
  (hs : UniShapes D)

/-- **One outcome of the setup and the adversary**: the Statement's event after the Statement's
verifier is at most as likely as the composed event after the composed verifier, from any state of
the permutation. -/
theorem step_le (hV : UniVerifierBridge D Fl nV V C hs) (hX : UniExtractBridge D Fl nV V hs)
    (a : SetupTrees × ((Vector UInt8 32 × UniProof) × Common.OracleQueryLog))
    (s : Common.PermutationEdges KeccakState) :
    Pr{let acc ← (simulateQ Common.lazyRandomPermutationOracles
        (D.verifierWith Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2)).run' s}[
        UniBreaksKnowledgeSoundness D (uniExtractor D) (((a.2.1, acc), a.1.evaluations, a.2.2))] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (uVerIv D Fl nV V C hs (piOf a)))).run' s}[
        UniBreaksRel D Fl nV V C hs
          (ivOut (piOf a, v), setupTr a.1 ++ evalTr (permutationQueries a.2.2))] := by
  -- both verifiers first compute the contract's IV
  have hL : D.verifierWith Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2 =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInput D a.1.roots)) >>= fun iv =>
        verifyWith Common.queryPermutation D.shape iv.toList a.1.roots a.2.1.1 a.2.1.2 := by
    rw [Deployment.verifierWith, ivWith_eq, bind_map_left]
  have hR : simulateQ keccakCallsOverQueryPermutation (uVerIv D Fl nV V C hs (piOf a)) =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInput D a.1.roots)) >>= fun iv =>
        (fun v => (iv, v)) <$> simulateQ keccakCallsOverQueryPermutation
          (verU (uSpec Fl nV V) (uView (uRounds Fl nV V))
            (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)) (setIv iv (piOf a))) := by
    rw [uVerIv, simulateQ_bind]
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
      (uView (uRounds Fl nV V))
      ((setIv iv (piOf a), v), setupTr a.1 ++ evalTr (permutationQueries a.2.2)),
      ∀ q, c = some q → ¬ Rel D (uSt Fl nV V (setIv iv (piOf a))) q := by
    intro v c hc q hq hrel
    subst hq
    exact hext (hX a.1 a.2.2 (setIv iv (piOf a), v) q hc hrel)
  have hacc := hV (setIv iv (piOf a)) s'
  calc _ ≤ Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
          (verifyWith Common.queryPermutation D.shape iv.toList a.1.roots a.2.1.1 a.2.1.2)).run' s'}[
          b = true] := prEvent_mono _ _ _ fun b hb => hb.1
    _ ≤ _ := hacc
    _ ≤ _ := by
      rw [run'_map_lazy, prEvent_map]
      exact prEvent_mono _ _ _ fun v hv => ⟨hv.1, hv.2, hnone v⟩

end Step

/-! ## The coupling -/

/-- **The coupling from the bridge facts**: the setup bridge, the verifier bridge and the extractor's
reading make the univariate experiment's break at most as likely as the composed game's. -/
theorem uniGameLeV_of (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ)
    (C : UniCode D Fl nV V) (hs : UniShapes D) (hS : UniSetupBridge D hs)
    (hV : UniVerifierBridge D Fl nV V C hs) (hX : UniExtractBridge D Fl nV V hs) :
    UniGameLeV D Fl nV V C hs := by
  intro A
  rw [uniSoundnessExperiment_eq D A, rpmGameS_eq D Fl nV V C hs hS A]
  exact Soundness.prEvent_le_of_continuations (prefixU D A)
    (fun a => D.verifierWith Common.queryPermutation a.1.roots a.2.1.1 a.2.1.2)
    (fun a => simulateQ keccakCallsOverQueryPermutation (uVerIv D Fl nV V C hs (piOf a)))
    (fun a acc => (((a.2.1, acc), a.1.evaluations, a.2.2) : UniOutcome))
    (fun a v => ((piOf a, v), setupTr a.1, a.2.2))
    (UniBreaksKnowledgeSoundness D (uniExtractor D))
    (fun z => UniBreaksRel D Fl nV V C hs (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2)))
    fun a s => step_le D Fl nV V C hs hV hX a s

/-- **The Fiat–Shamir layer from the bridge facts.** -/
theorem fsLayer_of_bridges (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ)
    (C : UniCode D Fl nV V) (hs : UniShapes D) (hnQ : (uSpec Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds Fl nV V, r.nv ≤ 2 ^ 30) (hI : UniIv D) (hS : UniSetupBridge D hs)
    (hV : UniVerifierBridge D Fl nV V C hs) (hX : UniExtractBridge D Fl nV V hs) :
    FsLayer D Fl nV V C :=
  fsLayer_of_gameV' D Fl nV V C hs hnQ hnv hI (uniGameLeV_of D Fl nV V C hs hS hV hX)

end UniSound

/-- info: 'UniSound.uniGameLeV_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniGameLeV_of

/-- info: 'UniSound.fsLayer_of_bridges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer_of_bridges
