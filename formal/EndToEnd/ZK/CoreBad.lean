-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the model (`runWithRandomPermutation`, `queryPermutation`), the two calls over
-- the permutation (`keccakCallsOverQueryPermutation`, `keccakCallsOverRandomPermutation`,
-- `simulateQ_lazy_keccakCallsOverQueryPermutation`) and, through `E2ECompleteness`, the transfer
-- to two random oracles (`rpm_le_rom`) and mumbai's proof-of-work potential.
import ZK.CoreDefs
import E2ECompleteness.NoneProb

/-!
# The statement's prover fails or meets degenerate `α, β` with probability at most `deltaNone`

`proverBridge_of_detG` (`CoreDefs.lean`) asks for `badProb stmt w c ≤ δ`: the probability, over the
random permutation, that the statement's prover makes no proof **or** that its first two chain
challenges `α, β` are degenerate (`BadABD`, the first part of the completeness side's `badSet`).
**`hbad_deployed`** proves it at `δ = deltaNone`, the bound of `hnone_deployed`
(`E2ECompleteness/NoneProb.lean`), by the same proof:

* **the staged run carries `α, β`** (`abDet_eq_staged`): `abWith` is `proveWith`'s prefix, so with
  Keccak-256 a call (`abWithHG`) it is stage A then the chain's first two hashes (`abStagedG`,
  `abWithHG_eq_staged`), whose challenges are the staged prover's `z.2.1, z.2.2.1`
  (`abStagedG_id`), at every hash function and permutation;
* **with `π` drawn first** (`Eager.prEvent_runWithRandomPermutation`), both `badProb` and the
  staged prover's event against the sponge over the random permutation are averages over `π` of
  deterministic runs (`sim_badWith`; `sim_keccakCalls`: the two calls over `π` are Keccak-256 over
  `π`, `kH π`, and `π`), equal for every `π` (`proverDet_eq_staged`, `abDet_eq_staged`): hence
  **`badProb_eq_staged`**;
* **the bound** (`prEvent_proverStaged_bad_le`): as `prEvent_proverStaged_none_le`, the event
  splits on `z.2 ∈ badSet`; inside, the density of `badSet`; outside, degenerate `α, β` are
  excluded (they are in `badSet`), so the event is a missing proof at non-degenerate challenges, a
  failed nonce search.
-/

open OracleComp OracleSpec Common
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH)
open PcsQuotient.Domain PcsQuotient.Transcript
open scoped ENNReal

/- The fields' instances of `formal/Field` (`F64`, `F192`), as `CoreDefs.lean` has them. -/
attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

namespace PcsQuotient.EndToEnd

open Eager (St permImpl)
open E2ECompleteness (commitWithH startWithH squeezeWithH stageAG proverStagedG proverStaged
  implHF chainIn cellsOf proverWithH badSet deltaNone)

set_option linter.unusedSectionVars false

/-! ## The statement's `α, β` with Keccak-256 a call -/

section Generic

variable (circuit : PcsQuotient.Circuit) (cells : Array K) (masks : Masks) (witnessPad : Padding)
  (stmt : Statement)

/-- **`abWith` with Keccak-256 `H`**, for any circuit and cells. -/
def abWithHG {m : Type → Type} [Monad m] (H : Bytes → m Digest) : m (E × E) := do
  let mv := cellVars circuit.logRows
  let indexTree ← commitWithH H mv circuit.wiringTable
  let wHat := coefficients mv 0 cells
  let wStack := witnessStack circuit.logRows wHat (maskEntries masks) witnessPad
  let witnessTree ← commitWithH H (mv + 1) wStack
  let c ← startWithH H (label indexTree.root stmt)
  let witnessRoot := digestScalars witnessTree.root
  let c := (c.absorb witnessRoot.1).absorb witnessRoot.2
  let (α, c) ← squeezeWithH H c
  let (β, _) ← squeezeWithH H c
  return (α, β)

/-- **The staged prefix up to `α, β`**: stage A with no setup, then the chain's first two hashes. -/
def abStagedG : OracleComp KeccakCalls (E × E) := do
  let x ← stageAG (pure default) circuit cells masks witnessPad stmt
  let s₁ ← callKeccak256 (chainIn x.2.1 x.2.2)
  let s₂ ← callKeccak256 (digestBytes s₁)
  return (challengeOf s₁, challengeOf s₂)

/-- `abWithHG` commutes with any simulation of the calls. -/
theorem simulateQ_abWithHG {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) :
    simulateQ impl (abWithHG circuit cells masks witnessPad stmt callKeccak256) =
      abWithHG circuit cells masks witnessPad stmt (implH impl) := by
  simp only [abWithHG, simulateQ_bind, simulateQ_pure, E2ECompleteness.simulateQ_commitWithH,
    E2ECompleteness.simulateQ_startWithH, E2ECompleteness.simulateQ_squeezeWithH]

/-- **With two calls, `abWith` is the staged prefix.** -/
theorem abWithHG_eq_staged :
    abWithHG circuit cells masks witnessPad stmt callKeccak256 =
      abStagedG circuit cells masks witnessPad stmt := by
  simp only [abWithHG, abStagedG, stageAG, startWithH, squeezeWithH, bind_assoc, pure_bind,
    chainIn, Chain.absorb, List.nil_append, List.append_nil, List.flatMap_nil, List.cons_append,
    List.flatMap_cons]

/-- **At functions, the staged prefix's challenges are the staged prover's first two.** -/
theorem abStagedG_id (H : Bytes → Digest) (F : KeccakState → KeccakState) (quotientPad : Padding)
    (fuel : ℕ) :
    (simulateQ (implHF H F) (abStagedG circuit cells masks witnessPad stmt)).run =
      ((simulateQ (implHF H F)
          (proverStagedG circuit cells masks witnessPad quotientPad fuel stmt)).run.2.1,
        (simulateQ (implHF H F)
          (proverStagedG circuit cells masks witnessPad quotientPad fuel stmt)).run.2.2.1) := by
  simp only [abStagedG, proverStagedG, E2ECompleteness.staged, simulateQ_bind, simulateQ_pure]
  rfl

end Generic

/-- `abWith` is `abWithHG` at Keccak-256 over `F`, on the membership circuit's cells. -/
theorem abWith_eqHG {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)
    (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding) :
    abWith F stmt w c =
      abWithHG (membership logRows) (cellsOf w) c.1 c.2.1 stmt (keccak256With F) := by
  simp only [abWith, abWithHG, E2ECompleteness.commitWith_eqH]
  rfl

/-! ## The runs with `π` drawn -/

/-- **Keccak-256 over `π`**, a function. -/
def kH (π : Equiv.Perm St) : Bytes → Digest := fun x ↦ (keccak256With (permId π) x).run

/-- Keccak-256 over `π` in `Id` is `kH π` (each value read through `Id.run`). -/
theorem kH_eq (π : Equiv.Perm St) : (keccak256With (permId π) : Bytes → Id Digest) = kH π := by
  funext x
  exact (fun y : Id Digest ↦ (rfl : y = Id.run y)) (keccak256With (permId π) x)

theorem sim_keccak256With (π : Equiv.Perm St) (x : Bytes) :
    simulateQ (permImpl π) (keccak256With queryPermutation x) = pure (kH π x) := by
  have h1 := Param.keccak256With_hom (simHom (permImpl π)) queryPermutation x
  have h2 := Param.keccak256With_hom (idHom ProbComp) (permId π) x
  simp only [simHom_app, sim_queryPermutation] at h1
  simp only [idHom_app] at h2
  rw [h1]
  exact h2.symm

/-- **The two calls over `π`, with `π` drawn**, are the run with Keccak-256 over `π` and `π`. -/
theorem sim_keccakCalls (π : Equiv.Perm St) {β : Type} (X : OracleComp KeccakCalls β) :
    simulateQ (permImpl π) (simulateQ keccakCallsOverQueryPermutation X) =
      pure (simulateQ (implHF (kH π) π) X).run := by
  have h := (simHom (permImpl π)).app_simulateQ keccakCallsOverQueryPermutation X
  simp only [simHom_app] at h
  rw [h, ← simulateQ_pure_eq (implHF (kH π) π) X]
  congr 1
  funext t
  rcases t with x | s
  · exact sim_keccak256With π x
  · exact sim_queryPermutation π s

/-- **The statement's proof at `π` is the staged prover's**, run at Keccak-256 over `π` and `π`. -/
theorem proverDet_eq_staged (π : Equiv.Perm St) (stmt : Statement) (w : Secret)
    (c : Masks × Padding × Padding) :
    proverDet π stmt w c = (simulateQ (implHF (kH π) π) (proverStaged stmt w c)).run.1 := by
  have h := congrArg Id.run (congrArg (simulateQ (implHF (kH π) π))
    (E2ECompleteness.proverWithH_eq_staged stmt w c))
  rw [simulateQ_map, E2ECompleteness.simulateQ_proverWithH, E2ECompleteness.implH_implHF,
    E2ECompleteness.implF_implHF, Id.run_map] at h
  unfold proverDet
  rw [PcsQuotient.prover, E2ECompleteness.proverWith_eqH, kH_eq]
  exact h

/-- **The statement's `α, β` at `π` are the staged prover's first two challenges.** -/
theorem abDet_eq_staged (π : Equiv.Perm St) (stmt : Statement) (w : Secret)
    (c : Masks × Padding × Padding) :
    abDet π stmt w c =
      ((simulateQ (implHF (kH π) π) (proverStaged stmt w c)).run.2.1,
        (simulateQ (implHF (kH π) π) (proverStaged stmt w c)).run.2.2.1) := by
  have h1 := simulateQ_abWithHG (membership logRows) (cellsOf w) c.1 c.2.1 stmt (implHF (kH π) π)
  rw [abWithHG_eq_staged] at h1
  have h2 := abStagedG_id (membership logRows) (cellsOf w) c.1 c.2.1 stmt (kH π) π c.2.2 nonceFuel
  rw [h1] at h2
  unfold abDet
  rw [abWith_eqHG]
  exact h2

/-! ## `badProb` on the staged run -/

/-- **The staged run's bad event**: no proof, or its first two challenges are degenerate. -/
def BadStaged (w : Secret) (m : Masks) (z : Option PcsQuotient.Proof × (E × E × E)) : Prop :=
  z.1 = none ∨ BadABD w m (z.2.1, z.2.2.1)

open Classical in
theorem badEvent_iff (π : Equiv.Perm St) (stmt : Statement) (w : Secret)
    (c : Masks × Padding × Padding) :
    ((proverDet π stmt w c).isNone || decide (BadABD w c.1 (abDet π stmt w c))) = true ↔
      BadStaged w c.1 (simulateQ (implHF (kH π) π) (proverStaged stmt w c)).run := by
  rw [proverDet_eq_staged, abDet_eq_staged]
  simp only [Bool.or_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none, BadStaged]

/-- **`badProb` is the staged prover's bad event** against the sponge over the random
permutation. -/
theorem badProb_eq_staged (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding) :
    badProb stmt w c =
      Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (proverStaged stmt w c)).run' []}[
        BadStaged w c.1 z] := by
  classical
  have hR : (simulateQ keccakCallsOverRandomPermutation (proverStaged stmt w c)).run' [] =
      runWithRandomPermutation
        (simulateQ keccakCallsOverQueryPermutation (proverStaged stmt w c)) := by
    rw [runWithRandomPermutation, simulateQ_lazy_keccakCallsOverQueryPermutation]
  rw [hR]
  rw [badProb]
  rw [Eager.prEvent_runWithRandomPermutation (fun b ↦ b = true)]
  rw [Eager.prEvent_runWithRandomPermutation (fun z ↦ BadStaged w c.1 z)]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun π _ ↦ ?_)
  rw [sim_badWith, sim_keccakCalls, prEvent_pure, prEvent_pure]
  exact if_congr (badEvent_iff π stmt w c) rfl rfl

/-! ## The bound -/

/-- **For fixed coins, the staged prover makes no proof or meets degenerate `α, β` with
probability at most `deltaNone`.** -/
theorem prEvent_proverStaged_bad_le (stmt : Statement) (w : Secret) (hrel : Relation stmt w)
    (c : Masks × Padding × Padding) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (proverStaged stmt w c)).run' []}[
      BadStaged w c.1 z] ≤ deltaNone := by
  unfold deltaNone
  refine E2ECompleteness.rpm_le_rom _ (E2ECompleteness.duplexVm_proverStaged stmt w c)
    (E2ECompleteness.cost_proverStaged stmt w c) (fun z ↦ BadStaged w c.1 z) ?_
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _
    (fun z : Option PcsQuotient.Proof × (E × E × E) ↦ z.2 ∈ badSet w c.1)).trans
    (add_le_add ?_ ?_)
  · -- The challenges in the degenerate set.
    refine (E2ECompleteness.prEvent_proverStagedG_mem_le (membership logRows) (cellsOf w) c.1
      c.2.1 c.2.2 nonceFuel stmt (badSet w c.1)).trans ?_
    rw [add_comm]
    exact add_le_add (E2ECompleteness.badSet_density w c.1) le_rfl
  · -- Outside it, degenerate `α, β` are excluded: a failed nonce search.
    have hfuel : nonceFuel ≤ 2 ^ 64 := by norm_num [nonceFuel]
    have hfuel0 : nonceFuel ≠ 0 := by norm_num [nonceFuel]
    refine (prEvent_mono _ _ (fun z : Option PcsQuotient.Proof × (E × E × E) ↦
      z.1 = none ∧ z.2 ∉ badSet w c.1) fun z hz ↦ ⟨?_, hz.2⟩).trans ?_
    · rcases hz.1 with h | h
      · exact h
      · refine absurd ?_ hz.2
        simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl h
    · exact (E2ECompleteness.prEvent_proverStagedG_none_le (membership logRows) (cellsOf w) c.1
        c.2.1 c.2.2 nonceFuel stmt hfuel hfuel0 (E2ECompleteness.tailReduces_proverStaged stmt w hrel c)
        (E2ECompleteness.isTotalQueryBound_of_queryCostAtMost
          (E2ECompleteness.cost_proverStaged stmt w c))).trans E2ECompleteness.grinding_le

/-- **`hbad` of the bridge** (`proverBridge_of_detG`): for a statement and a witness of the
relation, for every coins `c`, the statement's prover makes no proof or meets degenerate `α, β`
with probability at most `deltaNone < 2^-162`. -/
theorem hbad_deployed :
    ∀ stmt w, Relation stmt w → ∀ c, badProb stmt w c ≤ E2ECompleteness.deltaNone := by
  intro stmt w hrel c
  rw [badProb_eq_staged]
  exact prEvent_proverStaged_bad_le stmt w hrel c

end PcsQuotient.EndToEnd

/-- info: 'PcsQuotient.EndToEnd.hbad_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.hbad_deployed
