-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Real
import ZK.Simulator

/-!
# Zero knowledge of the membership proof: the end theorem

**`zeroKnowledge_end`**: `PcsQuotient.ZeroKnowledge (zkBoundDeployed Qp Qfmt εR (fun _ ↦ 0))`, from
`zeroKnowledge_deployed` (`ZK/Assembly.lean`: `QuotientZk`'s random-permutation theorem on the deployed
skeleton, `FSFresh` and the duplex discipline proved, the coins of the distinguisher removed) with

* the real bridge split (`ZK/Real.lean`): the statement's coins are the skeleton model's uniform
  randomness read by `coinsOf` (`CoinsMatch`), and at fixed coins the statement's prover is within `εR`
  of the skeleton's (`ProverBridge`);
* the ideal bridge exact (`ZK/Simulator.lean`): the statement's ideal experiment is that of
  `rpmSimulator` (`QuotientZk`'s simulator in the statement's shape) at the joint model's public data.

`ζ Q = εR Q + epsFSDeployed + 2^-165 + 2^24 (2^70 + Qfmt + Q) 2^-2368 + 2^48 2^-2368 +
(Qp + Qfmt + Q)² / 2^508`, at most `εR Q + 2^-113 + 2^-165 + 2^-2200 + (Qp + Qfmt + Q)² / 2^508` for
`Qfmt + Q ≤ 2^127` (`zkBoundDeployed_le`).
-/

open OracleComp OracleSpec Common Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **Zero knowledge of the membership proof**, `PcsQuotient.ZeroKnowledge` at
`zkBoundDeployed Qp Qfmt εR (fun _ ↦ 0)`. Named hypotheses, for each statement and witness of the
relation: the joint model of the deployed prover (`J stmt w`, `JointData.Valid`), the prover's
permutation budget (`hprover`), the formatting's (`hfmt`), the coins (`hcoins`), the prover at fixed
coins (`hbridge`), and the statement's ideal experiment being `rpmSimulator`'s (`hI`). -/
theorem zeroKnowledge_end
    (J : Statement → Secret → JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂)
    (stmtD : Statement → QuotientZk.Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (sh : Statement → QuotientZk.Deployed.Shape)
    (hsh : ∀ stmt, sh stmt = QuotientZk.Deployed.deployedShape (stmtD stmt) idW idσ idQ rowsW)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (coinsOf : Rand K ι₁ Y₁ ι₂ Y₂ → Masks × Padding × Padding)
    (Qp Qfmt : ℕ) (εR : ℕ → ℝ≥0∞) (s₀ : RpmSimState)
    (hfmt : ∀ pf, IsTotalQueryBound (fmt pf) Qfmt)
    (hvalid : ∀ stmt w, Relation stmt w → (J stmt w).Valid)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (J stmt w).P keccak256OverPermutation queryPermutation
        (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (QuotientZk.Deployed.skel (sh stmt))) permutationCallCost Qp)
    (hcoins : CoinsMatch coinsOf)
    (hbridge : ∀ stmt w, Relation stmt w →
      ProverBridge stmt w (J stmt w).P (QuotientZk.Deployed.skel (sh stmt)) fmt coinsOf εR)
    (hI : ∀ stmt w, Relation stmt w → ∀ D, idealExperiment stmt D =
      rpmIdeal (J stmt w).P (J stmt w).simV (QuotientZk.Deployed.skel (sh stmt)) fmt s₀ D) :
    ZeroKnowledge (zkBoundDeployed Qp Qfmt εR fun _ ↦ 0) :=
  zeroKnowledge_deployed_rpmSimulator J stmtD idW idσ idQ rowsW hrows sh hsh fmt Qp Qfmt εR s₀ hfmt
    hvalid hprover
    (fun stmt w hw ↦ realBridge_of stmt w _ _ fmt coinsOf εR hcoins (hbridge stmt w hw)) hI

end PcsQuotient.EndToEnd
