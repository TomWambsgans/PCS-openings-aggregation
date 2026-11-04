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
3. Before the fix (`fix-rec-hazard-fs`), `MergeHazard` read the undrawn `t` as `0`, so the empty stream was on the
   hazard for every IV and input, `Pi1HazardKeccak D εh` forced `1 ≤ εh Q` (an adversary of no query outputs the empty
   stream), and the end-to-end bound `pi2Bound Q + ε1 Q + εh Q` was at least one (`pi1HazardKeccak_trivial`, at
   3c6b6e4). **After the fix** `MergeHazard` asks that the run draw `t` (at least 50 challenges), and the soundness
   hazard `Pi1HazardAccepted` also that π1-rec3's graph accept the stream:
   * `not_mergeHazard_empty`, `not_pi1HazardAccepted_empty`: the empty stream is not on the hazard, at every IV and
     input;
   * `emptyAdversary_hazard_zero`: the zero-query adversary that refuted `Pi1HazardKeccak` now hits it with
     probability `0`;
   * `hazardAdversary_default`: the derived hazard adversary's default output (π2's extractor failing) is not on it.
4. (Finding 3, `RecStatement.RecKnowledgeSoundnessReduction`): the end-to-end soundness theorem is now a reduction to
   two explicit adversaries, with no Fiat–Shamir premise; the Props `Pi1FsKeccak`, `Pi1HazardKeccak` remain, documented
   as false for unbounded adversaries.
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

/-- **The empty stream is not on the hazard** (finding 2, fixed): its run draws no challenge, so not `t`. -/
theorem not_mergeHazard_empty (iv input : List UInt8) :
    ¬ RecGraph.MergeHazard keccakF1600 iv input #[] := by
  intro h
  have h50 := h.drawn
  rw [challenges_empty] at h50
  simp at h50

/-- **Nor on the soundness hazard.** -/
theorem not_pi1HazardAccepted_empty (iv : List UInt8) (input : Vector UInt8 32) :
    ¬ Pi1HazardAccepted iv input #[] :=
  fun h ↦ not_mergeHazard_empty iv input.toList h.2

/-- **The derived hazard adversary's default output is not on the hazard**: where π2's extractor outputs nothing,
`hazardAdversary` outputs the empty stream. -/
theorem hazardAdversary_default (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (evals : List (List UInt8 × Digest)) (T : OracleQueryLog) (proof : RecProof)
    (h : recExtractor2 D roots input evals T proof = none) :
    ¬ Pi1HazardAccepted (D.pi1IvAt roots.pi1) input ((recExtractor2 D roots input evals T proof).getD #[]) := by
  rw [h, Option.getD_none]
  exact not_pi1HazardAccepted_empty _ _

/-- The zero-query adversary: the empty stream, whatever the setup. -/
def emptyAdversary : Pi1StreamAdversary := fun _ _ ↦ pure (Vector.replicate 32 0, #[])

/-- The hazard experiment's game, before the permutation is drawn. -/
def hazGame (D : RecDeployment) (B : Pi1StreamAdversary) :
    OracleComp RandomPermutationOracles (List UInt8 × Vector UInt8 32 × Array UInt8) := do
  let trees ← D.setupTreesWith queryPermutation
  let (z, _) ← (simulateQ loggedOracles (B trees.roots trees.evaluations)).run []
  return (D.pi1IvAt trees.roots.pi1, z)

theorem hazGame_support_not (D : RecDeployment) :
    ∀ a ∈ support (hazGame D emptyAdversary), ¬ Pi1HazardAccepted a.1 a.2.1 a.2.2 := by
  intro a ha
  simp only [hazGame, emptyAdversary, simulateQ_pure, StateT.run_pure, pure_bind, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at ha
  obtain ⟨_, _, rfl⟩ := ha
  exact not_pi1HazardAccepted_empty _ _

/-- **The zero-query adversary no longer refutes `Pi1HazardKeccak`**: it hits the hazard with probability `0` (it
refuted the premise before the fix, with probability `1`). -/
theorem emptyAdversary_hazard_zero (D : RecDeployment) :
    Pr{let z ← pi1HazardExperiment D emptyAdversary}[Pi1HazardAccepted z.1 z.2.1 z.2.2] = 0 := by
  change Pr{let z ← runWithRandomPermutation (hazGame D emptyAdversary)}[Pi1HazardAccepted z.1 z.2.1 z.2.2] = 0
  rw [PcsQuotient.EndToEnd.Eager.prEvent_runWithRandomPermutation]
  have h0 : ∀ π : Equiv.Perm PcsQuotient.EndToEnd.Eager.St,
      Pr{let z ← simulateQ (PcsQuotient.EndToEnd.Eager.permImpl π) (hazGame D emptyAdversary)}[
        Pi1HazardAccepted z.1 z.2.1 z.2.2] = 0 :=
    fun π ↦ prEvent_eq_zero_of_forall_mem_support _ _ fun a ha ↦
      hazGame_support_not D a (RpmC.support_simulateQ_subset _ _ ha)
  simp only [h0, Finset.sum_const_zero, mul_zero]

/-- **π1's prover in the completeness theorems** hashes its Fiat–Shamir with Keccak-256 over `π`. -/
theorem pi1Rec3Prover_fs_over_pi (D : RecDeployment) :
    Pi2G.pi1Rec3Prover D = UniComplete.Rec3.uniProverRec3With (keccak256With queryPermutation) queryPermutation
      (UniComplete.Rec3.flockProve3H (keccak256With queryPermutation)) D.pi1 := rfl

end RecCompose.StatementReview

#print axioms RecCompose.StatementReview.not_pi1HazardAccepted_empty
#print axioms RecCompose.StatementReview.hazardAdversary_default
#print axioms RecCompose.StatementReview.emptyAdversary_hazard_zero
#print axioms RecCompose.StatementReview.pi1Rec3Prover_fs_over_pi
