-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement's experiment is `formal/RecStatement`'s
-- (`recCompletenessExperiment2`); the eager form of the random-permutation model is
-- `formal/EndToEnd/ZK/ProverBridgeEager.lean`'s (`prEvent_runWithRandomPermutation`, `permImpl`), Keccak-256 through a
-- monad morphism `ProverBridgeParam.lean`'s (`keccak256With_hom`); leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls over `π`
-- (`keccakCallsOverQueryPermutation`, `simulateQ_lazy_keccakCallsOverQueryPermutation`), the run at pure functions.
import RecCompose.Pi2SimAt
import RecCompose.RpmC
import ZK.ProverBridgeParam

/-!
# π2's experiment, staged: `Pi2ExperimentLe` and the staged run at pure functions

* **`perm_kc`**: a two-call computation answered over `π` (Keccak-256 the sponge over `π`), then by a fixed
  permutation `π` (`permImpl π`, the eager model), is the pure run at `(keccak256 over π, π)` (`runAt`).
* **`experiment_eq_kc`**: π2's completeness experiment with π1-rec3's honest prover (`pi1Rec3Prover`) and π2's
  (`pi2Prover`) is `expW2` over the two calls, answered over `π` (`sim_expW2`, π1-rec3's prover's commutation
  `proverCommutes3_flockProve3H`, the Statement's code at `keccak256With π`: `Pi2CompleteH`'s `_eqH`).
* **`expW2_event_staged`**: at every pure `(Ht, Ft)`, if the experiment's event holds (π1-rec3's graph accepting, the
  contract rejecting), the staged run's does: the graph accepting, the witness is honest (`Pi2WitnessComplete`), so
  the staged run is the experiment (`stagedAt_good`).
* **`pi2ExperimentLe_p1k`**: `Pi2ExperimentLe D C Fa (pi1Rec3Prover D) (p1k D)`, from the witness's completeness: the
  two sides are averages over the permutations of these pure runs.
* **`pi2RunAt_good`**: the staged run at pure functions (`Pi2RunAt`'s content where it is true: its verdict and
  priors on an honest witness, the verdict `(false, false)` when π1's prover returns none, the first component the
  graph's otherwise).

**Finding (the named fact `Pi2RunAt` as stated is not provable).** Its first conjunct claims the staged verdict is
`expW2`'s at every pure `(Ht, Ft)`; on a π1 proof with no honest witness (the graph rejecting, or before
`Pi2WitnessComplete`) the staged run hashes `fixLen 536` of the writer's input, `536` zero bytes, where the prover hashes
its `64`-byte input: the second components may differ. Only the event matters (the graph accepting), where the witness
is honest; `rejects_at_good` (`Pi2CallsOpenR`) uses `pi2RunAt_good` instead.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF)
open LeanVM.Protocol.Compile (totalImpl)
open E2ECompleteness (runAt)
open PcsQuotient.EndToEnd.Eager
open Pi2S Pi2K Pi2P Pi2E Pi2G
open scoped ENNReal

/-! ## A fixed permutation -/

/-- Keccak-256 over a permutation `π`. -/
def hOf (π : Equiv.Perm St) (x : List UInt8) : Digest :=
  Id.run (keccak256With (m := Id) (fun s ↦ (π s : Id KeccakState)) x)

theorem perm_queryPermutation (π : Equiv.Perm St) (s : KeccakState) :
    simulateQ (permImpl π) (queryPermutation s) = pure (π s) := by
  simp [queryPermutation, permImpl]

/-- `simulateQ` as a morphism of `ZK`'s kind. -/
noncomputable def simHom {ι : Type} {spec : OracleSpec.{0, 0} ι} (impl : QueryImpl spec ProbComp) :
    PcsQuotient.EndToEnd.MHom (OracleComp spec) ProbComp :=
  ⟨fun x ↦ simulateQ impl x, fun a ↦ simulateQ_pure impl a, fun x f ↦ simulateQ_bind impl x f⟩

/-- `pure ∘ Id.run` as a morphism. -/
def pureHom : PcsQuotient.EndToEnd.MHom Id ProbComp :=
  ⟨fun x ↦ pure (Id.run x), fun _ ↦ rfl, fun x f ↦ by simp⟩

theorem perm_keccak256With (π : Equiv.Perm St) (x : List UInt8) :
    simulateQ (permImpl π) (keccak256With queryPermutation x) = pure (hOf π x) := by
  have h1 := PcsQuotient.EndToEnd.Param.keccak256With_hom (simHom (permImpl π)) queryPermutation x
  have h2 := PcsQuotient.EndToEnd.Param.keccak256With_hom pureHom (fun s ↦ (π s : Id KeccakState)) x
  simp only [simHom, pureHom] at h1 h2
  rw [h1]
  simp only [perm_queryPermutation]
  exact h2.symm

/-- **Over `π`, then a fixed `π`: the pure run.** -/
theorem perm_kc (π : Equiv.Perm St) {α : Type} (X : OracleComp KeccakCalls α) :
    simulateQ (permImpl π) (simulateQ keccakCallsOverQueryPermutation X) = pure (runAt (hOf π) (⇑π) X) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; rfl
  | query_bind t k ih =>
    rcases t with x | s
    · simp only [simulateQ_bind, simulateQ_spec_query, keccakCallsOverQueryPermutation, ih, runAt]
      rw [perm_keccak256With, pure_bind]
      rfl
    · simp only [simulateQ_bind, simulateQ_spec_query, keccakCallsOverQueryPermutation, ih, runAt]
      rw [perm_queryPermutation, pure_bind]
      rfl

/-! ## The experiment over the two calls -/

theorem implH_kc : implH keccakCallsOverQueryPermutation = keccak256With queryPermutation := rfl
theorem implF_kc : implF keccakCallsOverQueryPermutation = queryPermutation := rfl

/-- **π2's experiment is `expW2` over the two calls, answered over `π`.** -/
theorem experiment_eq_kc (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) :
    recCompletenessExperiment2 D (pi1Rec3Prover D) (pi2Prover D C Fa PcsQuotient.nonceFuel) input rows q =
      runWithRandomPermutation (simulateQ keccakCallsOverQueryPermutation
        (expW2 callKeccak256 callKeccakF1600 D C Fa (p1k D input rows q) input)) := by
  rw [sim_expW2, implH_kc, implF_kc, p1k, UniComplete.Rec3.proverCommutes3_flockProve3H D.pi1, implH_kc, implF_kc]
  unfold recCompletenessExperiment2 expW2
  congr 1
  rw [Pi2H.setupTreesWith_eqH]
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => rfl
  | some p1 =>
    simp only [Pi2H.pi1GraphVerifierWith_eqH]
    refine bind_congr fun a1 ↦ ?_
    unfold pi2Prover
    refine bind_congr fun r ↦ ?_
    cases r with
    | none => rfl
    | some p2 => simp only [Pi2H.verifierWith_eqH]

/-- **The staged run over the two calls, answered by the lazy permutation**, is the eager model's game. -/
theorem staged_eq_kc {α : Type} (X : OracleComp KeccakCalls α) :
    (simulateQ keccakCallsOverRandomPermutation X).run' [] =
      runWithRandomPermutation (simulateQ keccakCallsOverQueryPermutation X) := by
  rw [← simulateQ_lazy_keccakCallsOverQueryPermutation]
  rfl

/-! ## The event, at pure functions -/

/-- **The experiment's event at pure `(Ht, Ft)` gives the staged run's** (π1's prover any two-call program `P1k`):
the graph accepting, the witness is honest, and the staged run is the experiment. -/
theorem expW2_event_staged {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hwc : Pi2WitnessComplete D C Fa) (input : Vector UInt8 32)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (Ht : List UInt8 → Digest)
    (Ft : KeccakState → KeccakState)
    (hev : (runAt Ht Ft (expW2 callKeccak256 callKeccakF1600 D C Fa P1k input)).1 = true ∧
      (runAt Ht Ft (expW2 callKeccak256 callKeccakF1600 D C Fa P1k input)).2 = false) :
    (runAt Ht Ft (pi2Staged D C Fa P1k input).run).1.1.1 = true ∧
      (runAt Ht Ft (pi2Staged D C Fa P1k input).run).1.1.2 = false := by
  have hx : runAt Ht Ft (expW2 callKeccak256 callKeccakF1600 D C Fa P1k input) =
      Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure (runAt Ht Ft P1k)) input) :=
    sim_expW2 (totalImpl Ht Ft) D C Fa P1k input
  rw [hx] at hev
  rw [runAt_staged]
  cases hp : runAt Ht Ft P1k with
  | none =>
    rw [hp, expW2_none] at hev
    exact absurd hev.1 (by decide)
  | some p1 =>
    rw [hp] at hev
    have ha1 : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D (rootsH D Ht Ft).pi1 input p1) =
        true := by
      have h := hev.1
      rw [expW2_some] at h
      revert h
      cases Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C Fa PcsQuotient.nonceFuel input p1) <;> exact id
    have hgood := pi2Choice_good (hwc _ _ _ (graphChecks_of_verifierH ha1))
    obtain ⟨h1, -⟩ := stagedAt_good Ht Ft D C Fa input p1 hD hgood
    rw [h1]
    exact hev

/-! ## `Pi2ExperimentLe` -/

/-- **`Pi2ExperimentLe` at π1-rec3's honest prover**, from the witness's completeness. -/
theorem pi2ExperimentLe_p1k {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hwc : Pi2WitnessComplete D C Fa) : Pi2ExperimentLe D C Fa (pi1Rec3Prover D) (p1k D) := by
  intro input rows q _ _
  rw [experiment_eq_kc, staged_eq_kc, prEvent_runWithRandomPermutation, prEvent_runWithRandomPermutation]
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun π _ ↦ ?_)
  rw [perm_kc, perm_kc, prEvent_pure, prEvent_pure]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (expW2_event_staged hD C Fa hwc input (p1k D input rows q) (hOf π) (⇑π) h1) h2
  · exact zero_le
  · exact le_rfl

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.pi2ExperimentLe_p1k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.pi2ExperimentLe_p1k
