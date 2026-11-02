-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.With
import ZK.Setup
import QuotientZk.Deployed.Fresh.Setup

/-!
# Zero knowledge of the membership proof: the end theorem

**`zeroKnowledge_end`**: `PcsQuotient.ZeroKnowledgeWith s₀ (zkSimulator pp simV skelOf fmt) rpmSimOracle
(zkBoundEnd Qp Qfmt εR)`: zero knowledge **for the simulator named in the statement**,
`zkSimulator` (`ZK/With.lean`: `QuotientZk`'s random-permutation simulator in the statement's shape,
compiled, at the public part `pp stmt` of the prover and the joint view simulator `simV stmt`), on the
skeleton of the statement's prover `skelSetup` (`ZK/Setup.lean`: the circuit's commitment computed over
`π` first, then the deployed skeleton; at most `2^24 + 2^70` operations, its duplex discipline proved, its
Fiat–Shamir freshness `2^-113`: `QuotientZk.Deployed.Fresh.fsFresh_setup_deployed_bits`).

It is `zeroKnowledgeWith_of_core` with `QuotientZk`'s closeness of the real and simulated games proved
from the joint model (`coreClose_of_joint`: `zk_rpm_skel_approx`, `jointHVZKε_of_linkV`,
`factors_singleV`, `factors_pairV`), and the real bridge split (`realBridge_of`: `CoinsMatch`,
`ProverBridge`).

`ζ Q = εR Q + 2^-113 + epsHV + 2^24 (2^24 + 2^70 + Qfmt + Q) 2^-2368 + 2^48 2^-2368 +
(Qp + Qfmt + Q)² / 2^508` (`zkBoundEnd`), `epsHV = 2^-165 + 2^-125 + 2/2^192` (the joint model's bad
challenges, `goodT`: F1's and the openings' `2^-165`, the claims' scales and the row `2^-125`; its
degenerate masks, `ClaimsND`, `2/2^192`), at most
`εR Q + 2^-113 + epsHV + 2^-2200 + (Qp + Qfmt + Q)² / 2^508` for `Qfmt + Q ≤ 2^127` (`zkBoundEnd_le`).
-/

open OracleComp OracleSpec Common Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint
open QuotientZk.Instance (ChV LinkV jointSimV jointHVZKε_of_linkV factors_singleV factors_pairV)
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto View)

/-- **The end theorem's error**: `zkBound` at the skeleton's `2^24 + 2^70` operations, its Fiat–Shamir
freshness `2^-113`, the ideal bridge exact. A function of the distinguisher's calls `Q` of `π` and
`π⁻¹`. -/
noncomputable def zkBoundEnd (Qp Qfmt : ℕ) (εR : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  zkBound (2 ^ 24 + 2 ^ 70) Qp Qfmt ((2 : ℝ≥0∞) ^ 113)⁻¹ εR fun _ ↦ 0

/-- **The end theorem's error at our sizes**: for a distinguisher and a formatting of at most
`2^127` calls together, `ζ Q ≤ εR Q + 2^-113 + epsHV + 2^-2200 + (Qp + Qfmt + Q)² / 2^508`. -/
theorem zkBoundEnd_le (Qp Qfmt : ℕ) (εR : ℕ → ℝ≥0∞) (Q : ℕ) (hQ : Qfmt + Q ≤ 2 ^ 127) :
    zkBoundEnd Qp Qfmt εR Q ≤
      εR Q + (((2 : ℝ≥0∞) ^ 113)⁻¹ + epsHV + ((2 : ℝ≥0∞) ^ 2200)⁻¹ +
        ((Qp + (Qfmt + Q) : ℕ) ^ 2 : ℝ≥0∞) / 2 ^ 508) := by
  have h : 2 ^ 24 + 2 ^ 70 + (Qfmt + Q) ≤ 2 ^ 128 := by
    have : (2 : ℕ) ^ 24 + 2 ^ 70 + 2 ^ 127 ≤ 2 ^ 128 := by norm_num
    omega
  have h2 := zkBound_le (2 ^ 24 + 2 ^ 70) Qp Qfmt ((2 : ℝ≥0∞) ^ 113)⁻¹ εR (fun _ ↦ 0) Q h
  simpa [zkBoundEnd] using h2

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **`QuotientZk`'s closeness of the real and simulated games, from the joint model**:
`zk_rpm_skel_approx` with `jointHVZKε_of_linkV` (`epsHV`) and `factors_singleV`, `factors_pairV`
(`2^-2368`),
for a valid joint model `J` on a skeleton of at most `QP` operations (`FSFresh` with `εFS`, the duplex
discipline, at most `Qp` permutation calls of the prover), the proof formatted by `fmt` of at most
`Qfmt` calls. -/
theorem coreClose_of_joint (J : JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂) (hv : J.Valid)
    (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof)) (QP Qp Qfmt : ℕ)
    (εFS : ℝ≥0∞) (hskel : IsTotalQueryBound skel QP)
    (hfmt : ∀ pf, IsTotalQueryBound (fmt pf) Qfmt)
    (hFS : QuotientZk.Deployed.FSFresh J.P skel [] εFS)
    (hduplex : QuotientZk.DRpm.DuplexDiscipline J.P skel)
    (hprover : ∀ s, QueryCostAtMost (QuotientZk.DRpm.proverJ J.P keccak256OverPermutation
      queryPermutation (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s skel)
      permutationCallCost Qp) :
    CoreClose J.P J.simV skel fmt fun Q ↦ zkBound QP Qp Qfmt εFS (fun _ ↦ 0) (fun _ ↦ 0) Q := by
  intro D₀ Q hD₀
  let D : QuotientZk.Deployed.Proof → OracleComp PermSpec Bool := fun pf ↦ fmt pf >>= D₀
  have hD : ∀ pf, IsTotalQueryBound (D pf) (Qfmt + Q) := fun pf ↦
    isTotalQueryBound_bind (hfmt pf) fun x ↦ hD₀ x
  have hQ : ∀ s, QueryCostAtMost (QuotientZk.DRpm.zkGameRpmD J.P skel D s)
      permutationCallCost (Qp + (Qfmt + Q)) := fun s ↦
    Common.QueryCostAtMost.bind (hprover s) fun pf ↦ queryCost_liftPerm _ _ (hD pf)
  have hHV := jointHVZKε_of_linkV J.P hv.h3 J.P₀ hv.hE J.stmtE J.gK J.van hv.hvan hv.hsat
    hv.hvan0 hv.hq hv.hK hv.hN hv.hdeg J.inK hv.hinK J.sigmaAt hv.hsig J.wir J.S₁ J.S₂ hv.hS₁
    hv.hS₂ J.T₁ J.T₂ J.cl₁ J.cl₂ hv.hT₁ hv.hT₂ J.simT₁ J.simT₂ hv.hsimT₁ hv.hsimT₂ J.lk hv.hch
  have hfac := factors_singleV hv.hS₁ hv.hS₂ hv.h3 hv.hK hv.h40₁ hv.h40₂ J.lk
  have hfac₂ := factors_pairV hv.hS₁ hv.hS₂ hv.h3 hv.hK hv.h40₁ hv.h40₂ J.lk
  have hmain := QuotientZk.DRpm.zk_rpm_skel_approx J.P skel J.simV _ εFS
    (1 / 2 ^ 165 + 1 / 2 ^ 125) (2 / 2 ^ 192)
    ((2 : ℝ≥0∞) ^ 2368)⁻¹ ((2 : ℝ≥0∞) ^ 2368)⁻¹ QP (Qfmt + Q) (Qp + (Qfmt + Q)) hskel hFS hHV.1 hHV.2
    (fun σ k x hx v y ↦ (hfac σ k x hx y).some.bound v)
    (fun σ k x k' x' hx hx' hne v ↦ (hfac₂ σ k x k' x' hx hx' hne).some.bound v)
    (QuotientZk.DRpm.rowFn_ofBytes J.Pb) hduplex D hD hQ
  rw [QuotientZk.Deployed.card_positions] at hmain
  refine hmain.mono (le_of_eq ?_)
  simp only [zkBound, epsHV, zero_add, add_zero]

/-- **Zero knowledge of the membership proof for the simulator in the statement**,
`PcsQuotient.ZeroKnowledgeWith s₀ (zkSimulator pp simV skelOf fmt) rpmSimOracle (zkBoundEnd …)`, the
skeleton `skelOf stmt = skelSetup (stmtBytes stmt) idW idσ idQ rowsW`. Named hypotheses, for each
statement and witness of the relation: the joint model of the deployed prover (`J stmt w`,
`JointData.Valid`), whose prover's public part is `pp stmt` (`hpub`) and whose view simulator is
`simV stmt` (`hsimV`); the prover's permutation budget
(`hprover`); the formatting's (`hfmt`); the coins (`hcoins`); the statement's prover at fixed coins
(`hbridge`). -/
theorem zeroKnowledge_end
    (J : Statement → Secret → JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂)
    (pp : Statement → PubProto) (simV : Statement → List Out → ProbComp (View Msg Inp Tbl Pos))
    (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (fmt : Statement → QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (coinsOf : Rand K ι₁ Y₁ ι₂ Y₂ → Masks × Padding × Padding)
    (Qp Qfmt : ℕ) (εR : ℕ → ℝ≥0∞) (s₀ : RpmSimState)
    (hfmt : ∀ stmt pf, IsTotalQueryBound (fmt stmt pf) Qfmt)
    (hvalid : ∀ stmt w, Relation stmt w → (J stmt w).Valid)
    (hpub : ∀ stmt w, Relation stmt w → PubProto.of (J stmt w).P = pp stmt)
    (hsimV : ∀ stmt w, Relation stmt w → (J stmt w).simV = simV stmt)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (J stmt w).P keccak256OverPermutation queryPermutation
        (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost Qp)
    (hcoins : CoinsMatch coinsOf)
    (hbridge : ∀ stmt w, Relation stmt w →
      ProverBridge stmt w (J stmt w).P (skelSetup (stmtBytes stmt) idW idσ idQ rowsW) (fmt stmt)
        coinsOf εR) :
    ZeroKnowledgeWith s₀
      (zkSimulator pp simV (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt)
      rpmSimOracle (zkBoundEnd Qp Qfmt εR) := by
  have hFS : ∀ stmt w, Relation stmt w → QuotientZk.Deployed.FSFresh (J stmt w).P
      (skelSetup (stmtBytes stmt) idW idσ idQ rowsW) [] ((2 : ℝ≥0∞) ^ 113)⁻¹ := fun stmt w hw ↦ by
    have hv := hvalid stmt w hw
    exact QuotientZk.Deployed.Fresh.fsFresh_setup_deployed_bits (stmtBytes stmt) idW idσ idQ rowsW
      hrows (J stmt w).P (J stmt w).cw hv.hcw hv.hrow₀ (fun s h k x ↦ ⟨_, rfl, hv.hlong s h k x⟩)
      hv.hcK hv.hclW hv.hclσ hv.hclQ hv.hn
  have h := zeroKnowledgeWith_of_core (fun stmt w ↦ (J stmt w).P) pp simV
    (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt s₀ εR
    (fun Q ↦ zkBound (2 ^ 24 + 2 ^ 70) Qp Qfmt ((2 : ℝ≥0∞) ^ 113)⁻¹ (fun _ ↦ 0) (fun _ ↦ 0) Q) hpub
    (fun stmt w hw ↦ realBridge_of stmt w _ _ (fmt stmt) coinsOf εR hcoins (hbridge stmt w hw))
    (fun stmt w hw ↦ by
      rw [← hsimV stmt w hw]
      exact coreClose_of_joint (J stmt w) (hvalid stmt w hw) _ (fmt stmt) (2 ^ 24 + 2 ^ 70) Qp Qfmt
        ((2 : ℝ≥0∞) ^ 113)⁻¹
        (skelSetup_queryBound (stmtBytes stmt) idW idσ idQ rowsW hrows) (hfmt stmt) (hFS stmt w hw)
        (duplexDiscipline_skelSetup _ (QuotientZk.DRpm.rowFn_ofBytes (J stmt w).Pb) _ _ _ _ _)
        (hprover stmt w hw))
  have he : (fun Q ↦ εR Q + zkBound (2 ^ 24 + 2 ^ 70) Qp Qfmt ((2 : ℝ≥0∞) ^ 113)⁻¹ (fun _ ↦ 0)
      (fun _ ↦ 0) Q) = zkBoundEnd Qp Qfmt εR := by
    funext Q
    simp only [zkBoundEnd, zkBound, zero_add, add_zero]
  rw [he] at h
  exact h

end PcsQuotient.EndToEnd
