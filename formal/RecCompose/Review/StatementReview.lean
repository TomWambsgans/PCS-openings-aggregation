-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The statement review's Lean evidence (`STATEMENT_REVIEW.md`). Run from `formal/EndToEnd` on h1:
--   systemd-run --scope -q -p MemoryMax=10G lake env lean ../RecCompose/Review/StatementReview.lean
import RecCompose.Pi2AlphaEnd
import RecCompose.RpmC
import RecGraph.Sim.Compose

/-!
# Evidence for the statement review

1. `hazard_at_zero`: `Hazard p0 0` for every `p0` (`y_0` is a linearised polynomial, so `Z_bad(0) = 0`).
2. `challenges_empty`: on the empty stream π1-rec3's run aborts before drawing a challenge, so `t = getD 49 0 = 0`.
3. `mergeHazard_empty`: so `MergeHazard keccakF1600 iv input #[]` for every IV and input.
4. `pi1HazardKeccak_trivial`: so `Pi1HazardKeccak D εh` forces `1 ≤ εh Q` for every `Q` (an adversary of no query
   outputs the empty stream), and the end-to-end soundness bound `pi2Bound Q + ε1 Q + εh Q` is at least one.
5. `pi1Rec3Prover_fs_over_pi`: the π1 prover of the completeness theorems computes its Fiat–Shamir (IV, seed, stream)
   with Keccak-256 over `π`, not over Keccak-f[1600] as the graph and `pi1KeccakVerifierWith` do.
-/

namespace RecCompose.StatementReview

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement
open OracleComp OracleSpec Common Polynomial
open scoped ENNReal

theorem yP_eval_zero (a : Array (Array K)) (l : ℕ) : (UniSound.Ids.yP a l).eval (0 : E) = 0 := by
  unfold UniSound.Ids.yP
  generalize List.range a.size = L
  induction L with
  | nil => simp
  | cons m L ih =>
    simp only [List.map_cons, List.sum_cons, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, ih]
    simp

theorem zBad_eval_zero (S : UniStatement.Shape) (p0 : E) : (UniSound.Ids.zBad S p0).eval (0 : E) = 0 := by
  unfold UniSound.Ids.zBad
  generalize UniStatement.coordinateFunctionals (S.heights.getD opBlake2s 0) = a
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, yP_eval_zero, zero_add, zero_mul]

theorem hazard_at_zero (p0 : E) : RecGraph.Hazard p0 0 := zBad_eval_zero reference p0

theorem challenges_empty (iv input : List UInt8) :
    (Id.run (runWithFs (m := Id) (fun s ↦ pure (keccakF1600 s)) reference iv input #[] (.flock flockMain) .point
      .rec3 true)).chan.challenges = #[] := by
  simp only [runWithFs, reduceWithFs, RecGraph.Sim.hvalid, countBits, nextInteger, takeBytes, Chan.start]
  rfl

theorem mergeHazard_empty (iv input : List UInt8) :
    RecGraph.MergeHazard keccakF1600 iv input #[] := by
  unfold RecGraph.MergeHazard
  simp only [challenges_empty]
  exact hazard_at_zero _

/-- The zero-query adversary: the empty stream, whatever the setup. -/
def emptyAdversary : Pi1StreamAdversary := fun _ _ ↦ pure (Vector.replicate 32 0, #[])

/-- The hazard experiment's game, before the permutation is drawn. -/
def hazGame (D : RecDeployment) (B : Pi1StreamAdversary) :
    OracleComp RandomPermutationOracles (List UInt8 × Vector UInt8 32 × Array UInt8) := do
  let trees ← D.setupTreesWith queryPermutation
  let (z, _) ← (simulateQ loggedOracles (B trees.roots trees.evaluations)).run []
  return (D.pi1IvAt trees.roots.pi1, z)

theorem hazGame_support (D : RecDeployment) :
    ∀ a ∈ support (hazGame D emptyAdversary), RecGraph.MergeHazard keccakF1600 a.1 a.2.1.toList a.2.2 := by
  intro a ha
  simp only [hazGame, emptyAdversary, simulateQ_pure, StateT.run_pure, pure_bind, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at ha
  obtain ⟨_, _, rfl⟩ := ha
  exact mergeHazard_empty _ _

theorem pi1HazardKeccak_trivial (D : RecDeployment) (εh : ℕ → ℝ≥0∞) (h : Pi1HazardKeccak D εh) (Q : ℕ) :
    1 ≤ εh Q := by
  have hq : ∀ roots evals, QueryCostAtMost (emptyAdversary roots evals) permutationCallCost Q := by
    intro roots evals
    unfold QueryCostAtMost emptyAdversary
    simp
  refine le_trans (le_of_eq ?_) (h emptyAdversary Q hq)
  symm
  change Pr{let z ← runWithRandomPermutation (hazGame D emptyAdversary)}[
    RecGraph.MergeHazard keccakF1600 z.1 z.2.1.toList z.2.2] = 1
  rw [PcsQuotient.EndToEnd.Eager.prEvent_runWithRandomPermutation]
  have h1 : ∀ π : Equiv.Perm PcsQuotient.EndToEnd.Eager.St,
      Pr{let z ← simulateQ (PcsQuotient.EndToEnd.Eager.permImpl π) (hazGame D emptyAdversary)}[
        RecGraph.MergeHazard keccakF1600 z.1 z.2.1.toList z.2.2] = 1 :=
    fun π ↦ RpmC.prEvent_perm_eq_one π _ _ (hazGame_support D)
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- **The end-to-end knowledge-soundness bound is trivial** wherever `Pi1HazardKeccak` holds. -/
theorem recKnowledgeSoundness_fs_bound_trivial (D : RecDeployment) (ε1 εh : ℕ → ℝ≥0∞)
    (hh : Pi1HazardKeccak D εh) (Q : ℕ) : 1 ≤ pi2Bound Q + ε1 Q + εh Q :=
  (pi1HazardKeccak_trivial D εh hh Q).trans le_add_self

/-- **π1's prover in the completeness theorems** hashes its Fiat–Shamir with Keccak-256 over `π`. -/
theorem pi1Rec3Prover_fs_over_pi (D : RecDeployment) :
    Pi2G.pi1Rec3Prover D = UniComplete.Rec3.uniProverRec3With (keccak256With queryPermutation) queryPermutation
      (UniComplete.Rec3.flockProve3H (keccak256With queryPermutation)) D.pi1 := rfl

end RecCompose.StatementReview

#print axioms RecCompose.StatementReview.pi1HazardKeccak_trivial
#print axioms RecCompose.StatementReview.pi1Rec3Prover_fs_over_pi
