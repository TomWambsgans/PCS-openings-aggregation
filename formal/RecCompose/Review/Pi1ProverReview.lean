-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Non-vacuity of the completeness theorems at the recursion's π1 prover (`STATEMENT_REVIEW.md`, finding 4's fix).
-- Run from `formal/EndToEnd` on h1:
--   systemd-run --scope -q -p MemoryMax=10G lake env lean ../RecCompose/Review/Pi1ProverReview.lean
import RecCompose.Pi2KFEnd
import RecCompose.Pi1KFCore
import RecCompose.Pi1KFRpm
import RecCompose.CompleteCouplings
import RecCompose.RunShape

/-!
# Finding 4, fixed: the completeness theorems are about honest proofs the graph accepts

The review's refutation (`StatementReview.pi1Rec3Prover_fs_over_pi`) was that the completeness theorems' π1 prover
hashed its Fiat–Shamir over `π` while the graph and `pi1KeccakVerifierWith` hash it over Keccak-f[1600]. At the new
prover (`Pi1KF.pi1Rec3ProverKF`, `Pi2KF.recCompleteness2_pi2_rec3_kf`, `recCompleteness_pi2_rec3_kf_fs`):

1. **`pi1Rec3ProverKF_fs_kf`**: its Fiat–Shamir hash is `hKF = pure ∘ keccak256`, Keccak-256 over the real
   Keccak-f[1600]: the graph's and `runFs`'s (`Pi1KF.runFs_eq`: `runFs` is `runWithFsH (pure ∘ keccak256)`;
   `Pi1KF.pi1Iv_eq`: π1's contract IV is the prover's `contractIvRec3Of keccak256`), by `rfl`.
2. **`challenges_match`** (`Pi1KF.pi1KF_challenges`): at every pure trees' hash, off π1-rec3's completeness bad
   events at the prover's own challenges (`BadKF`: a bus challenge `β` making a fingerprint vanish, `t` a bad point),
   the Keccak-f[1600] verifier's run on the prover's stream draws exactly the prover's challenges and accepts.
3. **`keccak_accepts`** (`Pi1KF.pi1KF_accepts`): at every permutation, off `BadKF`, `pi1KeccakVerifierWith` (Fiat–Shamir
   over Keccak-f[1600], openings over the permutation) accepts the new prover's honest proof. So the old refutation
   (the honest proof failing π1's checks but with probability about `2^-180`) no longer applies.
4. **`contract_rejects_le`**: the end-to-end bound's event is the contract's rejection of π2's proof of an honest π1
   proof: `Pr[contract rejects] ≤ Pr[graph rejects] + Pr[graph accepts ∧ contract rejects]`, and `Pr[graph rejects]`
   is at most π1's completeness experiment at Keccak-f[1600] plus the honest hazard
   (`completenessPi1Coupling`, `pi1FsCompletenessExperiment_kf`). The first is the Fiat–Shamir reading of a theorem
   proved in the random-permutation model (**`rpm_reading`**: `deltaRec3 < 2^-167`), not a probability-one event.
   **It is unconditional**: no `¬ BadKF` hypothesis. `¬ BadKF` enters only items 2 and 3, the non-vacuity witnesses
   that the Keccak-f[1600] verifier accepts the honest proof; no end theorem uses `BadKF`. Its probability at
   Keccak-f[1600] is part of the heuristic premise `δ1`, and at `π` it is inside `deltaRec3` (`BadFp`, `BadT`)
   (`STATEMENT_REVIEW_2.md`, finding 5).
-/

namespace RecCompose.Pi1ProverReview

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement
open OracleComp OracleSpec Common
open Pi1KF
open scoped ENNReal

/-- **1. The new prover's Fiat–Shamir is Keccak-256 over the real Keccak-f[1600].** -/
theorem pi1Rec3ProverKF_fs_kf (D : RecDeployment) :
    pi1Rec3ProverKF D = uniProverRec3With2 (fun x ↦ pure (keccak256 x)) (keccak256With queryPermutation)
      queryPermutation (UniComplete.Rec3.flockProve3H fun x ↦ pure (keccak256 x)) D.pi1 := rfl

/-- **2. The verifier's challenges on the honest stream are the prover's**, off π1's completeness bad events. A
non-vacuity witness: `¬ BadKF` enters here and in `keccak_accepts` only, not in `contract_rejects_le` or an end
theorem. -/
theorem challenges_match (Hm : List UInt8 → Digest) (D : Deployment) (hD : D.shape = reference)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation rows input q) (hbad : ¬ BadKF Hm D input rows q) :
    (runFs D.shape (RecStatement.pi1Iv D.shape D.programIv
        (UniComplete.setupTreesOf (m := Id) Hm (UniComplete.honestTrace D input rows q)).roots)
        input.toList (streamRunKF keccak256 Hm (UniComplete.Rec3.flockProve3 (m := Id) (Pure.pure ∘ keccak256))
          D.programIv (UniComplete.honestTrace D input rows q)).1.stream (.flock flockMain) .point .rec3
          true).chan.challenges =
      (streamRunKF keccak256 Hm (UniComplete.Rec3.flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv
        (UniComplete.honestTrace D input rows q)).2.challenges :=
  (pi1KF_challenges Hm D hD input rows q hfit hrel hbad).1

/-- **3. The Keccak-f[1600] verifier accepts the honest proof**, at every permutation, off π1's bad events. A
non-vacuity witness, as `challenges_match`; `hπ` (the prover returns a proof, grinding within `nonceFuel`) is not shown
satisfiable here, and the prover's `none` is inside `δ1`. -/
theorem keccak_accepts (D : Deployment) (hD : D.shape = reference) (F : KeccakState → KeccakState)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation rows input q) (π : UniProof)
    (hπ : uniProverRec3With2 (m := Id) hKF (hOfF F) F (UniComplete.Rec3.flockProve3H hKF) D input rows q = some π)
    (hbad : ¬ BadKF (hOfF F) D input rows q) :
    Id.run (pi1KeccakVerifierWith (m := Id) (fun s ↦ pure (F s)) D
      (Id.run (setupTreesWith (m := Id) (fun s ↦ pure (F s)) D)).roots input π) = true :=
  pi1KF_accepts D hD F input rows q hfit hrel π hπ hbad

/-- **4. The bound's event is the contract's rejection of an honest proof**, up to π1's completeness at Keccak-f[1600]
and the honest hazard. Unconditional: unlike `challenges_match` and `keccak_accepts`, it takes no `¬ BadKF`. -/
theorem contract_rejects_le (D : RecDeployment) (hD : D.pi1.shape = reference) (P2 : Pi2Prover)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    Pr{let v ← recCompletenessExperiment2 D (pi1Rec3ProverKF D) P2 input rows q}[v.2 = false] ≤
      (Pr{let v ← pi1FsCompletenessExperiment D (fun s ↦ pure (keccakF1600 s)) input rows q}[v = false] +
        Pr{let z ← pi1HonestHazardExperiment D (pi1Rec3ProverKF D) input rows q}[
          ∃ iv s, z = some (iv, s) ∧ RecGraph.MergeHazard keccakF1600 iv input.toList s]) +
      Pr{let v ← recCompletenessExperiment2 D (pi1Rec3ProverKF D) P2 input rows q}[v.1 = true ∧ v.2 = false] := by
  calc Pr{let v ← recCompletenessExperiment2 D (pi1Rec3ProverKF D) P2 input rows q}[v.2 = false]
      ≤ Pr{let v ← recCompletenessExperiment2 D (pi1Rec3ProverKF D) P2 input rows q}[
          v.1 = false ∨ (v.1 = true ∧ v.2 = false)] :=
        prEvent_mono _ _ _ fun v hv ↦ by
          cases h : v.1
          · exact Or.inl rfl
          · exact Or.inr ⟨rfl, hv⟩
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
        refine add_le_add ?_ le_rfl
        rw [pi1FsCompletenessExperiment_kf]
        exact completenessPi1Coupling D hD pi1RunShape _ P2 RecGraph.Pi1.pi1GraphIsVerifier input rows q

/-- **π1's completeness term at the random-permutation reading** is `deltaRec3 < 2^-167`, not one. -/
theorem rpm_reading {D : RecDeployment} (hD : D.Real) :
    Pi1CompletenessFs D queryPermutation UniComplete.Rec3.deltaRec3 ∧
      UniComplete.Rec3.deltaRec3 < (2 : ℝ≥0∞)⁻¹ ^ 167 :=
  ⟨pi1CompletenessFs_rpm D hD.2.2.1 (Pi2KF.hIv_real hD), UniComplete.Rec3.deltaRec3_lt'⟩

end RecCompose.Pi1ProverReview

/-- info: 'RecCompose.Pi1ProverReview.challenges_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1ProverReview.challenges_match

/-- info: 'RecCompose.Pi1ProverReview.keccak_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1ProverReview.keccak_accepts

/-- info: 'RecCompose.Pi1ProverReview.contract_rejects_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1ProverReview.contract_rejects_le

/-- info: 'RecCompose.Pi1ProverReview.rpm_reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1ProverReview.rpm_reading
