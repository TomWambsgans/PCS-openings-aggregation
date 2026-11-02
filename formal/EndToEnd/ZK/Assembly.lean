-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The model (`RandomPermutationOracles`, `QueryCostAtMost`, `permutationCallCost`) is leanerVM's
-- (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`;
-- `Common.QueryCostAtMost.bind` from its `common`).
import ZK.Coins
import QuotientZk.FreshJoint
import QuotientZk.Instance.JointV
import QuotientZk.Instance.Nondeg

/-!
# `PcsQuotient.ZeroKnowledge` from `formal/QuotientZk`

The end statement `PcsQuotient.ZeroKnowledge ζ` (`formal/Statement`, `Security.lean`) from
`QuotientZk.DRpm.zk_rpm_skel_approx` (zero knowledge of a skeleton prover in mumbai's
random-permutation model, the honest-verifier simulator within `εz`) with the joint model's
honest-verifier zero knowledge and factorizations (`QuotientZk.Instance.jointHVZKε_of_linkV`,
`factors_singleV`, `factors_pairV`: the joint model whose openings read the five values, as the
deployed quotient claim's point does, the honest tables' claims required off the degenerate
challenges and masks, `ClaimsND`), for an explicit `ζ` (`zkBound`), and the distinguisher's coins
removed (`ZK/Coins.lean`).

**Two theorems.** `zeroKnowledge_of_bridges` for any skeleton (`FSFresh` and the duplex discipline
named); **`zeroKnowledge_deployed`** for the deployed skeleton (`QuotientZk.Deployed.skel` at the
deployed shape, `2^22` rows), where both are proved (`fsFresh_deployed` from no query before the proof,
`epsFSDeployed ≤ 2^-113`; `duplexDiscipline_skel`).

**What is assumed, by name.** For each statement and witness of the relation:

* **the joint model of the deployed prover** (`JointData`, its hypotheses `JointData.Valid`): the
  prover `Pb` of `QuotientZk`'s skeleton model (its rows byte strings, `ofBytes`), the reduction's
  parameters, the two secret openings `S₁`, `S₂` (`SecretOpening` over `ChV`: the challenges and the
  five values), the honest and simulated tables and their claims, the `LinkV` between the prover and
  the joint model, and `fsFresh_deployed`'s conditions on the prover — the hypotheses of
  `QuotientZk.Instance.zk_rpm_deployed_jointV_fs'` but with the honest tables' claims (`hT₁`, `hT₂`)
  asked only under `ClaimsND`, as `jointHVZKε_of_linkV` takes them (that theorem asks them at every
  mask, which the honest tables do not meet: it is superseded), which the joint-model instance
  provides for the deployed prover (`ZK/Joint.lean`: `deployedJointData`, `deployedJointData_valid`);
* the prover's **permutation budget** (`hprover`: at most `Qp` calls of `π` in the real game's proof);
* **the two bridges** between the statement's experiments and `QuotientZk`'s games, for every
  coin-free distinguisher `D₀` of the statement's proofs, `fmt` turning the skeleton's proof into the
  statement's (mumbai's full Merkle paths from the pruned ones: public, by at most `Qfmt` `π` calls):
  * `RealBridge`: `realExperiment` is within `εR` of `realGameRpmD P skel (fmt · >>= D₀)` (the
    statement's prover is the skeleton's: the circuit's commitment the statement's prover computes over
    `π` where the skeleton's chain reads it as a constant, the proof-of-work fuel `2^25` with no proof on
    failure, the replayed chain and the wiring tree's position, and the proof's format are the
    differences, each public or negligible);
  * `IdealBridge`: `simGameRpmD P simV skel (fmt · >>= D₀)` is within `εI` of `idealExperiment`,
    `simV` the joint simulator (`JointData.simV`). `ZK/Simulator.lean` gives the statement-shaped
    simulator for which it holds with `εI = 0`.

**The bound** (`zkBound`, a function of the distinguisher's calls `Q` of `π` and `π⁻¹`):
`εR Q + εFS + epsHV + 2^24 (QP + Qfmt + Q) 2^-2368 + 2^48 2^-2368 + (Qp + Qfmt + Q)² / 2^508 + εI Q`,
`epsHV = 2^-165 + 2^-125 + 2/2^192` (the joint model's bad challenges, `goodT`, and its degenerate
masks, `ClaimsND`; below `2^-124`), for a skeleton of `QP` operations, a prover of `Qp`
permutation calls, `fmt` of `Qfmt`; at most
`εR Q + εFS + epsHV + 2^-2200 + (Qp + Qfmt + Q)² / 2^508 + εI Q` when `QP + Qfmt + Q ≤ 2^128`
(`zkBound_le`). Deployed (`zkBoundDeployed`): `QP = 2^70`, `εFS = epsFSDeployed ≤ 2^-113`, so at most
`εR Q + 2^-113 + epsHV + 2^-2200 + (Qp + Qfmt + Q)² / 2^508 + εI Q` for `Qfmt + Q ≤ 2^127`
(`zkBoundDeployed_le`).
-/

open OracleComp OracleSpec Common Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint QuotientZk.Deployed.Fresh
open QuotientZk.Instance (ChV LinkV jointSimV jointHVZK_of_linkV jointHVZKε_of_linkV ClaimsND
  factors_singleV factors_pairV)
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto View uniformList)

set_option linter.unusedSectionVars false

/-! ## The joint model of the deployed prover -/

/-- **The joint model of the deployed prover, its data**: the skeleton model's prover `P` (its
randomness the masks and the two paddings), the reduction's parameters and the witness's polynomials,
the simulator's public functions (`inK`, `sigmaAt`), the wiring opening, the two secret openings (over
`ChV`: their claims' weights may read the five values), the honest tables `T₁`, `T₂`, the verifier's
claims `cl₁`, `cl₂`, the simulator's tables `simT₁`, `simT₂`, and the `LinkV`
(`QuotientZk.Instance.zk_rpm_deployed_jointV_fs'`'s arguments). -/
structure JointData (K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type) [Field K] [Field E]
    [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
    [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂] where
  /-- The prover of the skeleton model, its secret rows byte strings (`QuotientZk.DRpm.ofBytes`). -/
  Pb : Proto (Rand K ι₁ Y₁ ι₂ Y₂) (List UInt8) Out Msg Tbl Pos
  /-- The bytes the openings' claims are hashed from, as functions of a challenge (`fsFresh_deployed`'s
  `cw`: the witness, wiring and quotient openings' claims). -/
  cw : Fin 3 → QuotientRpm.Bytes32 → List UInt8
  P₀ : Params E
  stmtE : Fin P₀.words → E
  gK : Fin 4 → K[X]
  van : K[X]
  inK : E → Bool
  sigmaAt : E → E
  wir : Chal E Γ₁ Γ₂ Γw → W
  S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁
  S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂
  T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K
  T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K
  cl₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₁.m → E
  cl₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₂.m → E
  simT₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₁ → Y₁ → K
  simT₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₂ → Y₂ → K
  lk : LinkV (QuotientZk.DRpm.ofBytes Pb) P₀ gK van wir T₁ T₂ S₁ S₂

section Joint

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- The prover of the skeleton model, its rows read as Keccak-256's inputs. -/
abbrev JointData.P (J : JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂) :
    Proto (Rand K ι₁ Y₁ ι₂ Y₂) Inp Out Msg Tbl Pos :=
  QuotientZk.DRpm.ofBytes J.Pb

/-- **The joint simulator's view** at the oracle's answers `σ`: `jointSimV` at the challenges they
give, read as the skeleton's view (`LinkV.out`). -/
def JointData.simV (J : JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂) :
    List Out → ProbComp (View Msg Inp Tbl Pos) :=
  fun σ ↦ J.lk.out σ <$> jointSimV J.inK J.sigmaAt J.wir J.S₁ J.S₂ J.simT₁ J.simT₂ (J.lk.chOf σ)

/-- **The joint model's hypotheses** (`zk_rpm_deployed_jointV_fs'`'s, by the same names): F1's (`h3`, `hE`,
`hvan`, `hsat`: the witness satisfies the relation, `hvan0`), the sizes (`hq`, `hK`, `hN`, `hdeg`, `h40₁`,
`h40₂`), the simulator's public functions (`hinK`, `hsig`), each secret opening's conditions (`hS₁`,
`hS₂`: (Q), `WeightsFit`, the layout's lanes), the claims of the honest tables off the degenerate
challenges and masks (`hT₁`, `hT₂`, under `ClaimsND`: the claims' scales, the row outside `K`, the copy
denominator) and of the simulated tables (`hsimT₁`, `hsimT₂`), the challenges uniform (`hch`); and `fsFresh_deployed`'s conditions on the
prover (`hcw`: the claims' bytes read a challenge through windows of min-entropy `2^-191`; `hrow₀`: the
witness table's first row of min-entropy `2^-2368`; `hlong`: rows longer than `192` bytes; `hcK`: the
witness table committed first; `hclW`, `hclσ`, `hclQ`: the openings' claims at their places; `hn`). -/
structure JointData.Valid (J : JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂) : Prop where
  h3 : finrank K E = 3
  hE : J.P₀.Exact
  hvan : ∀ x : J.P₀.T, aeval (rowPoly.eval (x : E)) J.van = 0
  hsat : J.P₀.Sat J.stmtE (J.P₀.cells (committed J.gK J.van 0))
  hvan0 : J.van ≠ 0
  hq : Fintype.card E = 2 ^ 192
  hK : Fintype.card K = 2 ^ 64
  hN : J.P₀.nCells = 2 ^ 24
  hdeg : J.van.natDegree ≤ 2 ^ 22
  h40₁ : 40 ≤ Fintype.card ι₁
  h40₂ : 40 ≤ Fintype.card ι₂
  hinK : ∀ e, J.inK e = true ↔ e ∈ Set.range (algebraMap K E)
  hsig : ∀ t, J.sigmaAt t = J.P₀.sigmaPoly.eval t
  hS₁ : J.S₁.Conditions
  hS₂ : J.S₂.Conditions
  hT₁ : ∀ c, good J.P₀ J.gK J.van c → ∀ m, ClaimsND (K := K) J.P₀ J.gK J.van c m →
    J.S₁.claims (c, redMsgs J.P₀ J.gK J.van c.1.1.2 m) (J.T₁ c m) =
      J.cl₁ c (redMsgs J.P₀ J.gK J.van c.1.1.2 m)
  hT₂ : ∀ c, good J.P₀ J.gK J.van c → ∀ m, ClaimsND (K := K) J.P₀ J.gK J.van c m →
    J.S₂.claims (c, redMsgs J.P₀ J.gK J.van c.1.1.2 m) (J.T₂ c m) =
      J.cl₂ c (redMsgs J.P₀ J.gK J.van c.1.1.2 m)
  hsimT₁ : ∀ c, good J.P₀ J.gK J.van c → ∀ v, J.S₁.claims (c, v) (J.simT₁ c v) = J.cl₁ c v
  hsimT₂ : ∀ c, good J.P₀ J.gK J.van c → ∀ v, J.S₂.claims (c, v) (J.simT₂ c v) = J.cl₂ c v
  hch : J.lk.chOf <$> uniformList Out J.P.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw))
  hcw : ∀ j y, Pr{let u ← $ᵗ Out}[J.cw j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹
  hrow₀ : ∀ y, Pr{let s ← $ᵗ (Rand K ι₁ Y₁ ι₂ Y₂)}[J.P.rowFn s [] 0 0 = y] ≤ ((2 : ℝ≥0∞) ^ 2368)⁻¹
  hlong : ∀ s h k x, 192 < (J.Pb.rowFn s h k x).length
  hcK : J.Pb.cK 0 = 0
  hclW : ClaimsAt J.P 5 4 (J.cw 0)
  hclσ : ClaimsAt J.P 128 3 (J.cw 1)
  hclQ : ClaimsAt J.P 242 3 (J.cw 2)
  hn : 242 ≤ J.Pb.n

end Joint

/-! ## The bridges between the statement's experiments and `QuotientZk`'s games -/

section Bridges

variable {S : Type} [SampleableType S]

/-- **The real bridge**: for every coin-free distinguisher `D₀` of the statement's proofs with at most
`Q` calls of `π` and `π⁻¹`, the statement's `realExperiment` is within `εR Q` of `QuotientZk`'s real
game in the random-permutation model (`realGameRpmD`) for the prover `P` on the skeleton `skel`, the
distinguisher reading the statement's proof `fmt pf` of the skeleton's proof `pf`. -/
def RealBridge (stmt : Statement) (w : Secret) (P : Proto S Inp Out Msg Tbl Pos)
    (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof)) (εR : ℕ → ℝ≥0∞) :
    Prop :=
  ∀ (D₀ : Option Proof → OracleComp PermSpec Bool) (Q : ℕ), (∀ pf, IsTotalQueryBound (D₀ pf) Q) →
    Close (realExperiment stmt w fun pf ↦ simulateQ liftPerm (D₀ pf))
      (QuotientZk.DRpm.realGameRpmD P skel fun pf ↦ fmt pf >>= D₀) (εR Q)

/-- **The ideal bridge**: likewise, `QuotientZk`'s simulated game (`simGameRpmD`, the view simulator
`simV`) is within `εI Q` of the statement's `idealExperiment`. -/
def IdealBridge (stmt : Statement) (P : Proto S Inp Out Msg Tbl Pos)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos))
    (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof)) (εI : ℕ → ℝ≥0∞) :
    Prop :=
  ∀ (D₀ : Option Proof → OracleComp PermSpec Bool) (Q : ℕ), (∀ pf, IsTotalQueryBound (D₀ pf) Q) →
    Close (QuotientZk.DRpm.simGameRpmD P simV skel fun pf ↦ fmt pf >>= D₀)
      (idealExperiment stmt fun pf ↦ simulateQ liftPerm (D₀ pf)) (εI Q)

end Bridges

/-! ## The bound -/

/-- **The joint model's error**: its bad challenges (`goodT`: F1's and the openings' `2^-165`, the
claims' scales and the row `2^-125`) and its degenerate masks (`ClaimsND`, `2/2^192`). -/
noncomputable def epsHV : ℝ≥0∞ := 1 / 2 ^ 165 + 1 / 2 ^ 125 + 2 / 2 ^ 192

/-- **The zero-knowledge error** for a distinguisher of `Q` calls of `π` and `π⁻¹`: the bridges'
`εR Q`, `εI Q`; Fiat–Shamir's `εFS`; the joint model's `epsHV`; the unopened rows'
entropy `2^24 (QP + Qfmt + Q) δ + 2^48 δ`, `δ = 2^-2368` (`QP` the skeleton's operations, `Qfmt` the
formatting's calls); the random permutation's `(Qp + Qfmt + Q)² / 2^508` (`Qp` the prover's calls). -/
noncomputable def zkBound (QP Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR εI : ℕ → ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  εR Q + (εFS + epsHV +
    (((2 ^ 24 * (QP + (Qfmt + Q)) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 2368)⁻¹ +
      (((2 ^ 24) ^ 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 2368)⁻¹) +
    ((Qp + (Qfmt + Q) : ℕ) ^ 2 : ℝ≥0∞) / 2 ^ 508) + εI Q

/-- **The bound at our sizes**: with `QP + Qfmt + Q ≤ 2^128` (the deployed skeleton has at most `2^70`
operations), the entropy terms are at most `2^-2200`. -/
theorem zkBound_le (QP Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR εI : ℕ → ℝ≥0∞) (Q : ℕ)
    (hQ : QP + (Qfmt + Q) ≤ 2 ^ 128) :
    zkBound QP Qp Qfmt εFS εR εI Q ≤
      εR Q + (εFS + epsHV + ((2 : ℝ≥0∞) ^ 2200)⁻¹ +
        ((Qp + (Qfmt + Q) : ℕ) ^ 2 : ℝ≥0∞) / 2 ^ 508) + εI Q := by
  unfold zkBound
  have h := QuotientZk.Deployed.merkleTerm_le (QP + (Qfmt + Q)) hQ
  have h48 : ((2 ^ 24) ^ 2 : ℕ) = 2 ^ 48 := by norm_num
  rw [h48]
  gcongr

/-! ## The assembly -/

/-- A coin-free distinguisher as a computation of the model calls `π` and `π⁻¹` as often. -/
theorem queryCost_liftPerm {α : Type} (X : OracleComp PermSpec α) :
    ∀ n, IsTotalQueryBound X n →
      QueryCostAtMost (simulateQ liftPerm X) permutationCallCost n := by
  induction X using OracleComp.inductionOn with
  | pure a => intro n _; simp only [simulateQ_pure]; trivial
  | query_bind q k ih =>
    intro n h
    rw [isTotalQueryBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, liftPerm]
    rw [Common.isWeightBound_query_bind_iff]
    exact ⟨h.1, fun u ↦ ih u (n - 1) (h.2 u)⟩

section Main

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **Zero knowledge of the membership proof, `PcsQuotient.ZeroKnowledge`**, at `zkBound`. For each
statement and witness of the relation, the deployed prover is the joint model `J stmt w` (valid) on the
skeleton `skel stmt` (at most `QP` operations; `FSFresh` with `εFS`; the duplex discipline; at most `Qp`
permutation calls), and the statement's experiments are within `εR`, `εI` of `QuotientZk`'s real and
simulated games (`RealBridge`, `IdealBridge`, the proof formatted by `fmt` of at most `Qfmt` calls). -/
theorem zeroKnowledge_of_bridges
    (J : Statement → Secret → JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂)
    (skel : Statement → OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (QP Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR εI : ℕ → ℝ≥0∞)
    (hskel : ∀ stmt, IsTotalQueryBound (skel stmt) QP)
    (hfmt : ∀ pf, IsTotalQueryBound (fmt pf) Qfmt)
    (hvalid : ∀ stmt w, Relation stmt w → (J stmt w).Valid)
    (hFS : ∀ stmt w, Relation stmt w → QuotientZk.Deployed.FSFresh (J stmt w).P (skel stmt) [] εFS)
    (hduplex : ∀ stmt w, Relation stmt w →
      QuotientZk.DRpm.DuplexDiscipline (J stmt w).P (skel stmt))
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (J stmt w).P keccak256OverPermutation queryPermutation
        (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s (skel stmt))
        permutationCallCost Qp)
    (hreal : ∀ stmt w, Relation stmt w → RealBridge stmt w (J stmt w).P (skel stmt) fmt εR)
    (hideal : ∀ stmt w, Relation stmt w →
      IdealBridge stmt (J stmt w).P (J stmt w).simV (skel stmt) fmt εI) :
    ZeroKnowledge (zkBound QP Qp Qfmt εFS εR εI) := by
  apply zeroKnowledge_of_coinFree
  intro stmt w hw D₀ Q hD₀
  have hv := hvalid stmt w hw
  set Jw := J stmt w with hJw
  let D : QuotientZk.Deployed.Proof → OracleComp PermSpec Bool := fun pf ↦ fmt pf >>= D₀
  have hD : ∀ pf, IsTotalQueryBound (D pf) (Qfmt + Q) := fun pf ↦
    isTotalQueryBound_bind (hfmt pf) fun x ↦ hD₀ x
  have hQ : ∀ s, QueryCostAtMost (QuotientZk.DRpm.zkGameRpmD Jw.P (skel stmt) D s)
      permutationCallCost (Qp + (Qfmt + Q)) := fun s ↦
    Common.QueryCostAtMost.bind (hprover stmt w hw s) fun pf ↦ queryCost_liftPerm _ _ (hD pf)
  have hHV := jointHVZKε_of_linkV Jw.P hv.h3 Jw.P₀ hv.hE Jw.stmtE Jw.gK Jw.van hv.hvan hv.hsat
    hv.hvan0 hv.hq hv.hK hv.hN hv.hdeg Jw.inK hv.hinK Jw.sigmaAt hv.hsig Jw.wir Jw.S₁ Jw.S₂ hv.hS₁
    hv.hS₂ Jw.T₁ Jw.T₂ Jw.cl₁ Jw.cl₂ hv.hT₁ hv.hT₂ Jw.simT₁ Jw.simT₂ hv.hsimT₁ hv.hsimT₂ Jw.lk hv.hch
  have hfac := factors_singleV hv.hS₁ hv.hS₂ hv.h3 hv.hK hv.h40₁ hv.h40₂ Jw.lk
  have hfac₂ := factors_pairV hv.hS₁ hv.hS₂ hv.h3 hv.hK hv.h40₁ hv.h40₂ Jw.lk
  have hmain := QuotientZk.DRpm.zk_rpm_skel_approx Jw.P (skel stmt) Jw.simV _ εFS
    (1 / 2 ^ 165 + 1 / 2 ^ 125) (2 / 2 ^ 192)
    ((2 : ℝ≥0∞) ^ 2368)⁻¹ ((2 : ℝ≥0∞) ^ 2368)⁻¹ QP (Qfmt + Q) (Qp + (Qfmt + Q)) (hskel stmt)
    (hFS stmt w hw) hHV.1 hHV.2 (fun σ k x hx v y ↦ (hfac σ k x hx y).some.bound v)
    (fun σ k x k' x' hx hx' hne v ↦ (hfac₂ σ k x k' x' hx hx' hne).some.bound v)
    (QuotientZk.DRpm.rowFn_ofBytes Jw.Pb)
    (hduplex stmt w hw) D hD hQ
  rw [QuotientZk.Deployed.card_positions] at hmain
  have h := ((hreal stmt w hw D₀ Q hD₀).trans hmain).trans (hideal stmt w hw D₀ Q hD₀)
  refine h.mono (le_of_eq ?_)
  simp only [zkBound, epsHV]

/-- `epsFS` grows with the operations. -/
theorem epsFS_mono (c : ℕ) {Q Q' : ℕ} (h : Q ≤ Q') (εc δ₀ : ℝ≥0∞) :
    epsFS c Q εc δ₀ ≤ epsFS c Q' εc δ₀ := by
  unfold epsFS
  have h1 : (Q : ℝ≥0∞) ≤ Q' := by exact_mod_cast h
  have h2 : ((c + Q : ℕ) : ℝ≥0∞) ≤ ((c + Q' : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.add_le_add_left h c
  gcongr

/-- **The Fiat–Shamir error of the deployed skeleton** (`fsFresh_deployed` with no query before the
proof: the random-permutation game starts from no edge), at most `2^70` operations:
`2^70 · 6 · 2^70 / 2^256 + 2 · 2^70 · 3 · 2^-191`, about `2^-113`. -/
noncomputable def epsFSDeployed : ℝ≥0∞ :=
  epsFS 0 (2 ^ 70) ((2 : ℝ≥0∞) ^ 191)⁻¹ ((2 : ℝ≥0∞) ^ 2368)⁻¹

set_option exponentiation.threshold 4000 in
/-- `epsFSDeployed ≤ 2^-113`: `6·2^140 + 6·2^135 ≤ 2^143` over `2^256`. -/
theorem epsFSDeployed_le : epsFSDeployed ≤ ((2 : ℝ≥0∞) ^ 113)⁻¹ := by
  have hN : 2 ^ 70 * 6 * (0 + 2 ^ 70) + 2 * (0 + 2 ^ 70) * 3 * 2 ^ 65 + 0 ≤ 2 ^ 143 := by norm_num
  have e1 : ((2 : ℝ≥0∞) ^ 191)⁻¹ = 2 ^ 65 * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
    two_pow_inv_split 191 65 256 rfl
  have e2 : ((2 : ℝ≥0∞) ^ 113)⁻¹ = 2 ^ 143 * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
    two_pow_inv_split 113 143 256 rfl
  unfold epsFSDeployed epsFS
  rw [e1, e2, div_eq_mul_inv]
  set U := ((2 : ℝ≥0∞) ^ 256)⁻¹
  calc _ = ((2 ^ 70 * 6 * (0 + 2 ^ 70) + 2 * (0 + 2 ^ 70) * 3 * 2 ^ 65 + 0 : ℕ) : ℝ≥0∞) * U := by
        push_cast; ring
    _ ≤ ((2 ^ 143 : ℕ) : ℝ≥0∞) * U := by gcongr
    _ = 2 ^ 143 * U := by norm_num

/-- **The zero-knowledge error of the deployed proof** (`zkBound` at the deployed skeleton's `2^70`
operations and `epsFSDeployed`), a function of the distinguisher's calls `Q`. -/
noncomputable def zkBoundDeployed (Qp Qfmt : ℕ) (εR εI : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  zkBound (2 ^ 70) Qp Qfmt epsFSDeployed εR εI

/-- **The deployed error at our sizes**: for a distinguisher and a formatting of at most `2^127` calls
together, `zkBoundDeployed Q ≤ εR Q + 2^-113 + epsHV + 2^-2200 + (Qp + Qfmt + Q)² / 2^508 + εI Q`. -/
theorem zkBoundDeployed_le (Qp Qfmt : ℕ) (εR εI : ℕ → ℝ≥0∞) (Q : ℕ) (hQ : Qfmt + Q ≤ 2 ^ 127) :
    zkBoundDeployed Qp Qfmt εR εI Q ≤
      εR Q + (((2 : ℝ≥0∞) ^ 113)⁻¹ + epsHV + ((2 : ℝ≥0∞) ^ 2200)⁻¹ +
        ((Qp + (Qfmt + Q) : ℕ) ^ 2 : ℝ≥0∞) / 2 ^ 508) + εI Q := by
  have h : 2 ^ 70 + (Qfmt + Q) ≤ 2 ^ 128 := by
    have : (2 : ℕ) ^ 70 + 2 ^ 127 ≤ 2 ^ 128 := by norm_num
    omega
  refine (zkBound_le _ _ _ _ _ _ Q h).trans ?_
  gcongr
  exact epsFSDeployed_le

/-- **Zero knowledge of the membership proof on the deployed skeleton**, `FSFresh` and the duplex
discipline proved (`fsFresh_deployed`, `duplexDiscipline_skel`): `PcsQuotient.ZeroKnowledge` at
`zkBoundDeployed`, for each statement and witness of the relation the prover being the joint model
`J stmt w` (valid: `JointData.Valid`) on the deployed skeleton (`skel (sh stmt)`, `sh stmt` the deployed
shape at `2^22` rows: the chain's public input `stmtD stmt`, the layouts' identifiers, the wiring
codeword's rows), with at most `Qp`
permutation calls (`hprover`), and the statement's experiments within `εR`, `εI` of `QuotientZk`'s
games (`RealBridge`, `IdealBridge`; the proof formatted by `fmt` of at most `Qfmt` calls).

This skeleton reads the circuit's commitment as a constant (`(stmtD stmt).indexRoot`); the statement's
prover computes it over `π`, so its `RealBridge` holds only with a large `εR` (a distinguisher may
recompute the commitment). The end theorem (`ZK/Main.lean`, `zeroKnowledge_end`) is on `skelSetup`
(`ZK/Setup.lean`), which computes it first. -/
theorem zeroKnowledge_deployed
    (J : Statement → Secret → JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂)
    (stmtD : Statement → QuotientZk.Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (sh : Statement → QuotientZk.Deployed.Shape)
    (hsh : ∀ stmt, sh stmt = QuotientZk.Deployed.deployedShape (stmtD stmt) idW idσ idQ rowsW)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (Qp Qfmt : ℕ) (εR εI : ℕ → ℝ≥0∞)
    (hfmt : ∀ pf, IsTotalQueryBound (fmt pf) Qfmt)
    (hvalid : ∀ stmt w, Relation stmt w → (J stmt w).Valid)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (J stmt w).P keccak256OverPermutation queryPermutation
        (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (QuotientZk.Deployed.skel (sh stmt))) permutationCallCost Qp)
    (hreal : ∀ stmt w, Relation stmt w →
      RealBridge stmt w (J stmt w).P (QuotientZk.Deployed.skel (sh stmt)) fmt εR)
    (hideal : ∀ stmt w, Relation stmt w →
      IdealBridge stmt (J stmt w).P (J stmt w).simV (QuotientZk.Deployed.skel (sh stmt)) fmt
        εI) :
    ZeroKnowledge (zkBoundDeployed Qp Qfmt εR εI) := by
  have hb : ∀ stmt, QuotientZk.Deployed.skelBound (sh stmt) ≤ 2 ^ 70 := fun stmt ↦ by
    rw [hsh]; exact QuotientZk.Deployed.skelBound_deployed (stmtD stmt) idW idσ idQ rowsW hrows
  refine zeroKnowledge_of_bridges J (fun stmt ↦ QuotientZk.Deployed.skel (sh stmt)) fmt (2 ^ 70) Qp
    Qfmt epsFSDeployed εR εI
    (fun stmt ↦ (QuotientZk.Deployed.skel_queryBound (sh stmt)).mono (hb stmt)) hfmt
    hvalid (fun stmt w hw ↦ ?_) (fun stmt w hw ↦ ?_) hprover hreal hideal
  · have hv := hvalid stmt w hw
    have hfs : QuotientZk.Deployed.FSFresh (J stmt w).P (QuotientZk.Deployed.skel (sh stmt)) []
        (epsFS 0 (QuotientZk.Deployed.skelBound (sh stmt)) ((2 : ℝ≥0∞) ^ 191)⁻¹
          ((2 : ℝ≥0∞) ^ 2368)⁻¹) := by
      rw [hsh]
      exact fsFresh_deployed (stmtD stmt) idW idσ idQ rowsW (J stmt w).P [] (J stmt w).cw _ _
        hv.hcw hv.hrow₀ (fun s h k x ↦ ⟨_, rfl, hv.hlong s h k x⟩) hv.hcK hv.hclW hv.hclσ hv.hclQ
        hv.hn
    exact le_trans hfs (epsFS_mono 0 (hb stmt) _ _)
  · exact QuotientZk.DRpm.duplexDiscipline_skel _ (QuotientZk.DRpm.rowFn_ofBytes (J stmt w).Pb) _

end Main

end PcsQuotient.EndToEnd
