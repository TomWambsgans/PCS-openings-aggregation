-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The model (`RandomPermutationOracles`, `runWithRandomPermutation`, `lazyRandomPermutationOracles`) is
-- leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`).
import ZK.Assembly

/-!
# The real bridge, split: the prover's coins, then the prover at fixed coins

`RealBridge` (`ZK/Assembly.lean`) compares the statement's `realExperiment` (the coins drawn by the
model's coin queries, `sampleCoins`, then the honest prover over the lazily sampled permutation) with
`QuotientZk`'s `realGameRpmD` (uniform randomness `s` of the skeleton model, then the skeleton's prover
over the permutation). The coins touch no permutation: they can be drawn first, outside the model
(`realExperiment_coins`: `sampleCoinsP`, the same draws as a `ProbComp`). So `RealBridge` follows from
(`realBridge_of`):

* **`CoinsMatch coinsOf`**: the statement's coins are the image of the skeleton model's uniform
  randomness under `coinsOf` (the masks and the two paddings read off `s`), in distribution;
* **`ProverBridge`**: at every fixed `s`, the statement's prover on the coins `coinsOf s`, then the
  distinguisher, is within `εR Q` of the skeleton's prover on `s`, then the distinguisher reading
  `fmt` of the skeleton's proof, both against the lazily sampled permutation. No secret randomness is
  left: this is the comparison of two programs over one random permutation (the circuit's commitment
  computed over `π` against the skeleton's constant, the proof-of-work fuel, the replayed chain, the
  proof's format).
-/

open OracleComp OracleSpec Common
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto View)

set_option linter.unusedSectionVars false

/-! ## Computations of coins alone -/

/-- A query is a coin. -/
def isCoin : RandomPermutationOracles.Domain → Unit → Prop
  | .inl _, _ => True
  | .inr _, _ => False

/-- **`X` queries coins only.** -/
def CoinsOnly {α : Type} (X : OracleComp RandomPermutationOracles α) : Prop :=
  IsQueryBound X () isCoin fun _ _ ↦ ()

theorem coinsOnly_pure {α : Type} (a : α) : CoinsOnly (pure a : OracleComp RandomPermutationOracles α) :=
  trivial

theorem CoinsOnly.bind {α β : Type} {X : OracleComp RandomPermutationOracles α}
    {f : α → OracleComp RandomPermutationOracles β} (hX : CoinsOnly X) (hf : ∀ a, CoinsOnly (f a)) :
    CoinsOnly (X >>= f) :=
  isQueryBound_bind (fun _ _ ↦ ()) (fun _ _ _ _ h ↦ ⟨h, h⟩) (fun _ _ _ _ _ ↦ ⟨rfl, rfl⟩) hX hf

theorem coinsOnly_coin (n : ℕ) :
    CoinsOnly (liftM (RandomPermutationOracles.query (.inl n)) :
      OracleComp RandomPermutationOracles (Fin (n + 1))) :=
  (isQueryBound_query_iff _ _ _ _).mpr trivial

theorem CoinsOnly.map {α β : Type} {X : OracleComp RandomPermutationOracles α} (f : α → β)
    (hX : CoinsOnly X) : CoinsOnly (f <$> X) :=
  (isQueryBound_map_iff X f _ _ _).mpr hX

theorem coinsOnly_mapM {α β : Type} (f : α → OracleComp RandomPermutationOracles β)
    (hf : ∀ a, CoinsOnly (f a)) : ∀ l : List α, CoinsOnly (l.mapM f)
  | [] => coinsOnly_pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b ↦ (coinsOnly_mapM f hf l).bind fun _ ↦ coinsOnly_pure _

theorem coinsOnly_coinWord : CoinsOnly coinWord :=
  (coinsOnly_coin _).bind fun _ ↦ coinsOnly_pure _

theorem coinsOnly_sampleMasks : CoinsOnly sampleMasks := by
  unfold sampleMasks
  exact (coinsOnly_mapM _ (fun _ ↦ coinsOnly_coinWord) _).bind fun _ ↦ coinsOnly_pure _

theorem coinsOnly_samplePadding (L : Layout) : CoinsOnly (samplePadding L) := by
  unfold samplePadding
  exact (coinsOnly_mapM _ (fun _ ↦ coinsOnly_coinWord) _).bind fun _ ↦ coinsOnly_pure _

theorem coinsOnly_coins (L₁ L₂ : Layout) :
    CoinsOnly (do return (← sampleMasks, ← samplePadding L₁, ← samplePadding L₂)) :=
  coinsOnly_sampleMasks.bind fun _ ↦ (coinsOnly_samplePadding L₁).bind fun _ ↦
    (coinsOnly_samplePadding L₂).bind fun _ ↦ coinsOnly_pure _

theorem coinsOnly_sampleCoins : CoinsOnly sampleCoins :=
  coinsOnly_coins (witnessLayout logRows) (quotientLayout logRows)

/-- Coins as a `ProbComp` (a permutation query, which a computation of coins alone never asks,
answered by the zero state). -/
def coinsImpl : QueryImpl RandomPermutationOracles ProbComp
  | .inl n => $[0..n]
  | .inr _ => pure (Vector.replicate 25 0)

/-- **A computation of coins alone leaves the permutation's edges as they were**, its output drawn
as the coins draw it. -/
theorem run_coinsOnly {α : Type} (X : OracleComp RandomPermutationOracles α) (hX : CoinsOnly X)
    (E : PermutationEdges LeanVM.Semantics.KeccakState) :
    (simulateQ lazyRandomPermutationOracles X).run E = (fun a ↦ (a, E)) <$> simulateQ coinsImpl X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    unfold CoinsOnly at hX
    rw [isQueryBound_query_bind_iff] at hX
    rcases t with n | q
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, map_bind]
      change (liftM ($[0..n]) : StateT _ ProbComp _).run E >>= _ = $[0..n] >>= _
      simp only [StateT.run, liftM, monadLift, MonadLift.monadLift, StateT.lift, bind_assoc,
        pure_bind]
      refine bind_congr fun u ↦ ?_
      exact ih u (hX.2 u)
    · exact absurd hX.1 (by simp [isCoin])

/-- **The statement's prover's coins** (`sampleCoins`), drawn as a `ProbComp`. -/
noncomputable def sampleCoinsP : ProbComp (Masks × Padding × Padding) :=
  simulateQ coinsImpl sampleCoins

/-- **The coins drawn first**: the real experiment draws the prover's coins outside the model, then
runs the prover and the distinguisher against the lazily sampled permutation. -/
theorem realExperiment_coins (stmt : Statement) (w : Secret) (D : Distinguisher) :
    realExperiment stmt w D = (sampleCoinsP >>= fun c ↦
      runWithRandomPermutation (prover queryPermutation stmt w c >>= D)) := by
  unfold realExperiment runWithRandomPermutation sampleCoinsP
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    run_coinsOnly _ coinsOnly_sampleCoins, bind_map_left, map_bind]
  refine bind_congr fun c ↦ ?_
  rw [StateT.run'_eq]

/-! ## The split -/

section Split

variable {S : Type} [SampleableType S]

/-- **The coins match**: the statement's prover's coins are `coinsOf` of the skeleton model's uniform
randomness, in distribution. -/
def CoinsMatch (coinsOf : S → Masks × Padding × Padding) : Prop :=
  sampleCoinsP =ᵈ coinsOf <$> ($ᵗ S)

/-- **The prover bridge at fixed coins**: for every coin-free distinguisher `D₀` of at most `Q` calls
and every randomness `s` of the skeleton model, the statement's prover on `coinsOf s` then `D₀` is
within `εR Q` of the skeleton's prover `P` on `s` then `D₀` reading `fmt` of its proof, both against the
lazily sampled permutation. -/
def ProverBridge (stmt : Statement) (w : Secret) (P : Proto S Inp Out Msg Tbl Pos)
    (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (coinsOf : S → Masks × Padding × Padding) (εR : ℕ → ℝ≥0∞) : Prop :=
  ∀ (D₀ : Option Proof → OracleComp PermSpec Bool) (Q : ℕ), (∀ pf, IsTotalQueryBound (D₀ pf) Q) →
    ∀ s, Close (runWithRandomPermutation (prover queryPermutation stmt w (coinsOf s) >>= fun pf ↦
        simulateQ liftPerm (D₀ pf)))
      (runWithRandomPermutation (QuotientZk.DRpm.zkGameRpmD P skel (fun pf ↦ fmt pf >>= D₀) s))
      (εR Q)

/-- **`RealBridge` from the coins and the prover at fixed coins.** -/
theorem realBridge_of (stmt : Statement) (w : Secret) (P : Proto S Inp Out Msg Tbl Pos)
    (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (coinsOf : S → Masks × Padding × Padding) (εR : ℕ → ℝ≥0∞) (hc : CoinsMatch coinsOf)
    (hp : ProverBridge stmt w P skel fmt coinsOf εR) : RealBridge stmt w P skel fmt εR := by
  intro D₀ Q hD₀
  rw [realExperiment_coins]
  have h1 := EvalDistEq.bind_left hc fun c ↦ runWithRandomPermutation
    (prover queryPermutation stmt w c >>= fun pf ↦ simulateQ liftPerm (D₀ pf))
  rw [bind_map_left] at h1
  refine ((Close.of_evalDistEq h1).trans
    (QuotientZk.Close.bind_const _ _ _ _ fun s ↦ hp D₀ Q hD₀ s)).mono ?_
  simp

end Split

end PcsQuotient.EndToEnd
