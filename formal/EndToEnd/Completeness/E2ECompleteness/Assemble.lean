-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the duplex discipline `DuplexVm` and the block cost `hashBlocks`.
import E2ECompleteness.HashLen
import E2ECompleteness.End

/-!
# The deployed experiment, staged

`deployedStaged stmt w` is the `Staged` of `End.lean` for the Statement's experiment: the raw coins
(`rawDist`), and for each draw the stages of `Staging.lean` on the deployed circuit. Proved here:

* `Staged.Holds.experiment` (`deployedStaged_experiment`): the completeness experiment is, in
  distribution, the coins then the staged run against the random permutation
  (`completenessExperiment_eq_expH`, `expH_eq_staged`);
* `hashA`, `hashB` (`hashOK_stageAG`, `hashOK_stageBG`).

**`completeness_deployed_staged`**: `PcsQuotient.Completeness deltaDeployed` from the three
remaining facts about the deployed staged run `stagedRun`: the duplex discipline, at most `2^48`
block calls, and the grinding bound at non-degenerate challenges (`RejectGood`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open LeanVM.Prover (Tree)
open PcsQuotient
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

/-- **The deployed experiment's stages**: the raw coins, and the stages on the deployed circuit. -/
noncomputable def deployedStaged (stmt : Statement) (w : Secret) : Staged where
  Coins := RawCoins
  α := AuxA
  β := Tree × Array K
  coins := rawDist
  masks c := (coinsOf c).1
  A c := stageAG (setupWithH callKeccak256) (membership logRows) (cellsOf w) (coinsOf c).1
    (coinsOf c).2.1 stmt
  B c := stageBG (membership logRows) (cellsOf w) (coinsOf c).2.2
  C _ := stageCG (membership logRows) nonceFuel logRows stmt

theorem deployedStaged_run (stmt : Statement) (w : Secret) (c : RawCoins) :
    (deployedStaged stmt w).run c = stagedRun stmt w (coinsOf c) := rfl

theorem deployedStaged_experiment (stmt : Statement) (w : Secret) :
    completenessExperiment stmt w =ᵈ ((deployedStaged stmt w).coins >>= fun c ↦ (fun z ↦ z.1) <$>
      (simulateQ keccakCallsOverRandomPermutation ((deployedStaged stmt w).run c)).run' []) := by
  refine (completenessExperiment_eq_expH stmt w).trans ?_
  have e : (fun c ↦ (simulateQ keccakCallsOverRandomPermutation (expH stmt w (coinsOf c))).run' []) =
      fun c ↦ (fun z ↦ z.1) <$>
        (simulateQ keccakCallsOverRandomPermutation ((deployedStaged stmt w).run c)).run' [] := by
    funext c
    rw [expH_eq_staged, deployedStaged_run, simulateQ_map, StateT.run'_eq, StateT.run'_eq,
      StateT.run_map, Functor.map_map, Functor.map_map]
  rw [e]
  rfl

/-- **The grinding at non-degenerate challenges**: in the two-call random-oracle model the deployed
staged run is rejected while its `(α, β, t)` is outside `badSet` with probability at most `εpow`. -/
def RejectGood (εpow : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ c : RawCoins,
    Pr{let z ← (simulateQ ro (stagedRun stmt w (coinsOf c))).run' ∅}[
      z.1 = false ∧ z.2 ∉ badSet w (coinsOf c).1] ≤ εpow

/-- **`Staged.Holds` for the deployed experiment**, from the duplex discipline, the block count and
the grinding. -/
theorem deployedStaged_holds {N : ℕ} {εpow : ℝ≥0∞}
    (hdup : ∀ stmt w coins, DuplexVm (stagedRun stmt w coins) [])
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks N)
    (hrej : RejectGood εpow) (stmt : Statement) (w : Secret) (hrel : Relation stmt w) :
    (deployedStaged stmt w).Holds stmt w N εpow where
  experiment := deployedStaged_experiment stmt w
  duplex c := hdup stmt w (coinsOf c)
  cost c := hcost stmt w (coinsOf c)
  hashA _ := hashOK_stageAG _ hashOK_setupWithH _ _ _ _ _
  hashB _ a s₁ s₂ s₃ := hashOK_stageBG _ _ _ a s₁ s₂ s₃
  rejectGood c := hrej stmt w hrel c

/-- **`PcsQuotient.Completeness deltaDeployed`** from the duplex discipline of the deployed staged
run, its at most `2^48` block calls, and the grinding bound `3 · 2^-277` at non-degenerate
challenges. -/
theorem completeness_deployed_staged
    (hdup : ∀ stmt w coins, DuplexVm (stagedRun stmt w coins) [])
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48))
    (hrej : RejectGood (3 * (2 : ℝ≥0∞)⁻¹ ^ 277)) :
    PcsQuotient.Completeness deltaDeployed :=
  completeness_deployed fun stmt w hrel ↦
    ⟨deployedStaged stmt w, deployedStaged_holds hdup hcost hrej stmt w hrel⟩

end E2ECompleteness
