-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Real
import ZK.Simulator
import ZK.Setup

/-!
# Zero knowledge of the membership proof: the end theorem

**`zeroKnowledge_end`**: `PcsQuotient.ZeroKnowledge (zkBoundEnd Qp Qfmt εFS εR)`, from
`zeroKnowledge_of_bridges` (`ZK/Assembly.lean`: `QuotientZk`'s random-permutation theorem, the joint
model's honest-verifier zero knowledge and factorizations, the coins of the distinguisher removed) on
the skeleton of the statement's prover, `skelSetup` (`ZK/Setup.lean`: the circuit's commitment computed
over `π` first, then the deployed skeleton; at most `2^24 + 2^70` operations, its duplex discipline
proved), with

* the real bridge split (`ZK/Real.lean`): the statement's coins are the skeleton model's uniform
  randomness read by `coinsOf` (`CoinsMatch`), and at fixed coins the statement's prover is within `εR`
  of the skeleton's (`ProverBridge`);
* the ideal bridge exact (`ZK/Simulator.lean`): the statement's ideal experiment is that of
  `rpmSimulator` (`QuotientZk`'s simulator in the statement's shape, compiled) at the joint model's
  public data and `skelSetup`.

`ζ Q = εR Q + εFS + 2^-165 + 2^24 (2^24 + 2^70 + Qfmt + Q) 2^-2368 + 2^48 2^-2368 +
(Qp + Qfmt + Q)² / 2^508`, at most `εR Q + εFS + 2^-165 + 2^-2200 + (Qp + Qfmt + Q)² / 2^508` for
`Qfmt + Q ≤ 2^127` (`zkBoundEnd_le`). `εFS` is `skelSetup`'s Fiat–Shamir freshness (`hFS`): `QuotientZk`'s
`fsFresh_deployed` is for `Deployed.skel` from an initial cache `c₀`, here the setup's tree, which gives
`epsFS (2^24) (2^70) 2^-191 2^-2368`, about `2^-113`, once carried over to `skelWith`.
-/

open OracleComp OracleSpec Common Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-- **The end theorem's error**: `zkBound` at the skeleton's `2^24 + 2^70` operations, the ideal bridge
exact. A function of the distinguisher's calls `Q` of `π` and `π⁻¹`. -/
noncomputable def zkBoundEnd (Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  zkBound (2 ^ 24 + 2 ^ 70) Qp Qfmt εFS εR fun _ ↦ 0

/-- **The end theorem's error at our sizes**: for a distinguisher and a formatting of at most
`2^127` calls together, `ζ Q ≤ εR Q + εFS + 2^-165 + 2^-2200 + (Qp + Qfmt + Q)² / 2^508`. -/
theorem zkBoundEnd_le (Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR : ℕ → ℝ≥0∞) (Q : ℕ)
    (hQ : Qfmt + Q ≤ 2 ^ 127) :
    zkBoundEnd Qp Qfmt εFS εR Q ≤
      εR Q + (εFS + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹ +
        ((Qp + (Qfmt + Q) : ℕ) ^ 2 : ℝ≥0∞) / 2 ^ 508) := by
  have h : 2 ^ 24 + 2 ^ 70 + (Qfmt + Q) ≤ 2 ^ 128 := by
    have : (2 : ℕ) ^ 24 + 2 ^ 70 + 2 ^ 127 ≤ 2 ^ 128 := by norm_num
    omega
  have h2 := zkBound_le (2 ^ 24 + 2 ^ 70) Qp Qfmt εFS εR (fun _ ↦ 0) Q h
  simpa [zkBoundEnd] using h2

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **Zero knowledge of the membership proof**, `PcsQuotient.ZeroKnowledge` at `zkBoundEnd`. The
skeleton of the statement's prover is `skelSetup (stmtBytes stmt) idW idσ idQ rowsW` (the wiring
codeword's `2^19` rows). Named hypotheses, for each statement and witness of the relation: the joint
model of the deployed prover (`J stmt w`, `JointData.Valid`), `skelSetup`'s Fiat–Shamir freshness
(`hFS`), the prover's permutation budget (`hprover`), the formatting's (`hfmt`), the coins (`hcoins`),
the prover at fixed coins (`hbridge`), and the statement's ideal experiment being `rpmSimulator`'s
(`hI`). -/
theorem zeroKnowledge_end
    (J : Statement → Secret → JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂)
    (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (coinsOf : Rand K ι₁ Y₁ ι₂ Y₂ → Masks × Padding × Padding)
    (Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR : ℕ → ℝ≥0∞) (s₀ : RpmSimState)
    (hfmt : ∀ pf, IsTotalQueryBound (fmt pf) Qfmt)
    (hvalid : ∀ stmt w, Relation stmt w → (J stmt w).Valid)
    (hFS : ∀ stmt w, Relation stmt w →
      QuotientZk.Deployed.FSFresh (J stmt w).P (skelSetup (stmtBytes stmt) idW idσ idQ rowsW) [] εFS)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (J stmt w).P keccak256OverPermutation queryPermutation
        (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost Qp)
    (hcoins : CoinsMatch coinsOf)
    (hbridge : ∀ stmt w, Relation stmt w →
      ProverBridge stmt w (J stmt w).P (skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt coinsOf εR)
    (hI : ∀ stmt w, Relation stmt w → ∀ D, idealExperiment stmt D =
      rpmIdeal (J stmt w).P (J stmt w).simV (skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt s₀
        D) :
    ZeroKnowledge (zkBoundEnd Qp Qfmt εFS εR) :=
  zeroKnowledge_of_bridges J (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt
    (2 ^ 24 + 2 ^ 70) Qp Qfmt εFS εR (fun _ ↦ 0)
    (fun stmt ↦ skelSetup_queryBound (stmtBytes stmt) idW idσ idQ rowsW hrows) hfmt hvalid hFS
    (fun stmt w _ ↦ duplexDiscipline_skelSetup _ (QuotientZk.DRpm.rowFn_ofBytes (J stmt w).Pb) _ _ _ _
      _)
    hprover
    (fun stmt w hw ↦ realBridge_of stmt w _ _ fmt coinsOf εR hcoins (hbridge stmt w hw))
    (fun stmt w hw ↦ idealBridge_rpm _ _ _ _ stmt s₀ (hI stmt w hw))

end PcsQuotient.EndToEnd
