-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The model (`RandomPermutationOracles`, `QueryCostAtMost`, `permutationCallCost`) is leanerVM's
-- (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`;
-- `Common.QueryCostAtMost.bind` from its `common`).
import ZK.Coins
import QuotientZk.RpmJoint

/-!
# `PcsQuotient.ZeroKnowledge` from `formal/QuotientZk`

The end statement `PcsQuotient.ZeroKnowledge ζ` (`formal/Statement`, `Security.lean`) from
`QuotientZk.DRpm.zk_rpm_skel` (zero knowledge of a skeleton prover in mumbai's random-permutation
model) with the joint model's honest-verifier zero knowledge and factorizations
(`QuotientZk.Joint.jointHVZK_of_link`, `factors_single`, `factors_pair`), for an explicit `ζ`
(`zkBound`), and the distinguisher's coins removed (`ZK/Coins.lean`).

**What is assumed, by name.** For each statement and witness of the relation:

* **the joint model of the deployed prover** (`JointData`, its hypotheses `JointData.Valid`): the
  prover `P` of `QuotientZk`'s skeleton model, the reduction's parameters, the two secret openings
  `S₁`, `S₂` (`SecretOpening`), the honest and simulated tables and their claims, and the `Link` between
  `P` and the joint model — exactly `zk_rpm_deployed_joint`'s hypotheses, which the joint-model
  instance (`formal/QuotientZk/Instance/`) is to provide;
* **`FSFresh`** and **`DuplexDiscipline`** of the skeleton (being proved separately) and the prover's
  permutation budget (`hprover`);
* **the two bridges** between the statement's experiments and `QuotientZk`'s games, for every
  coin-free distinguisher `D₀` of the statement's proofs, `fmt` turning the skeleton's proof into the
  statement's (mumbai's full Merkle paths from the pruned ones: public, by `π` calls):
  * `RealBridge`: `realExperiment` is within `εR` of `realGameRpmD P skel (fmt · >>= D₀)` (the
    statement's prover is the skeleton's: the setup's wiring tree, the proof-of-work fuel `2^25`, the
    replayed chain and the proof's format are the differences, each public or negligible);
  * `IdealBridge`: `idealExperiment` is within `εI` of `simGameRpmD P simV skel (fmt · >>= D₀)`, `simV`
    the joint simulator (`JointData.simV`). `ZK/Simulator.lean` gives the statement-shaped simulator for
    which it holds with `εI = 0`.

**The bound** (`zkBound`): `εR Q + εFS + 2^-165 + 2^24 (QP + Qfmt + Q) 2^-2368 + 2^48 2^-2368 +
(Qp + Qfmt + Q)² / 2^508 + εI Q`, for a distinguisher of `Q` calls of `π` and `π⁻¹`, a skeleton of
`QP` operations, a prover of `Qp` permutation calls, `fmt` of `Qfmt`; at most
`εR Q + εFS + 2^-165 + 2^-2200 + (Qp + Qfmt + Q)² / 2^508 + εI Q` when `QP + Qfmt + Q ≤ 2^128`
(`zkBound_le`).
-/

open OracleComp OracleSpec Common Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto View uniformList)

set_option linter.unusedSectionVars false

/-! ## The joint model of the deployed prover -/

/-- **The joint model of the deployed prover, its data**: the skeleton model's prover `P` (its
randomness the masks and the two paddings), the reduction's parameters and the witness's polynomials,
the simulator's public functions (`inK`, `sigmaAt`), the wiring opening, the two secret openings, the
honest tables `T₁`, `T₂`, the verifier's claims `cl₁`, `cl₂`, the simulator's tables `simT₁`, `simT₂`,
and the `Link` (`zk_rpm_deployed_joint`'s arguments). -/
structure JointData (K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type) [Field K] [Field E]
    [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
    [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂] where
  P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) Inp Out Msg Tbl Pos
  P₀ : Params E
  stmtE : Fin P₀.words → E
  gK : Fin 4 → K[X]
  van : K[X]
  inK : E → Bool
  sigmaAt : E → E
  wir : Chal E Γ₁ Γ₂ Γw → W
  S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁
  S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂
  T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K
  T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K
  cl₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₁.m → E
  cl₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₂.m → E
  simT₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₁ → Y₁ → K
  simT₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₂ → Y₂ → K
  lk : Link P P₀ gK van wir T₁ T₂ S₁ S₂

section Joint

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **The joint simulator's view** at the oracle's answers `σ`: `jointSim` at the challenges they give,
read as the skeleton's view (`Link.out`). -/
def JointData.simV (J : JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂) :
    List Out → ProbComp (View Msg Inp Tbl Pos) :=
  fun σ ↦ J.lk.out σ <$> jointSim J.inK J.sigmaAt J.wir J.S₁ J.S₂ J.simT₁ J.simT₂ (J.lk.chOf σ)

/-- **The joint model's hypotheses** (`zk_rpm_deployed_joint`'s, by the same names): F1's (`h3`, `hE`,
`hvan`, `hsat`: the witness satisfies the relation, `hvan0`), the sizes (`hq`, `hK`, `hN`, `hdeg`, `h40₁`,
`h40₂`), the simulator's public functions (`hinK`, `hsig`), each secret opening's conditions (`hS₁`,
`hS₂`: (Q), `WeightsFit`, the layout's lanes), the claims of the honest and simulated tables (`hT₁`,
`hT₂`, `hsimT₁`, `hsimT₂`), the challenges uniform (`hch`), and the secret rows byte strings (`hrow`). -/
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
  hT₁ : ∀ c, good J.P₀ J.gK J.van c → ∀ m,
    J.S₁.claims c (J.T₁ c m) = J.cl₁ c (redMsgs J.P₀ J.gK J.van c.1.1.2 m)
  hT₂ : ∀ c, good J.P₀ J.gK J.van c → ∀ m,
    J.S₂.claims c (J.T₂ c m) = J.cl₂ c (redMsgs J.P₀ J.gK J.van c.1.1.2 m)
  hsimT₁ : ∀ c, good J.P₀ J.gK J.van c → ∀ v, J.S₁.claims c (J.simT₁ c v) = J.cl₁ c v
  hsimT₂ : ∀ c, good J.P₀ J.gK J.van c → ∀ v, J.S₂.claims c (J.simT₂ c v) = J.cl₂ c v
  hch : J.lk.chOf <$> uniformList Out J.P.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw))
  hrow : ∀ s h k x, ∃ m, J.P.rowFn s h k x = .inl m

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

/-- **The zero-knowledge error** for a distinguisher of `Q` calls of `π` and `π⁻¹`: the bridges'
`εR Q`, `εI Q`; Fiat–Shamir's `εFS`; the joint model's bad challenges `2^-165`; the unopened rows'
entropy `2^24 (QP + Qfmt + Q) δ + 2^48 δ`, `δ = 2^-2368` (`QP` the skeleton's operations, `Qfmt` the
formatting's calls); the random permutation's `(Qp + Qfmt + Q)² / 2^508` (`Qp` the prover's calls). -/
noncomputable def zkBound (QP Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR εI : ℕ → ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  εR Q + (εFS + 1 / 2 ^ 165 +
    (((2 ^ 24 * (QP + (Qfmt + Q)) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 2368)⁻¹ +
      (((2 ^ 24) ^ 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 2368)⁻¹) +
    ((Qp + (Qfmt + Q) : ℕ) ^ 2 : ℝ≥0∞) / 2 ^ 508) + εI Q

/-- **The bound at our sizes**: with `QP + Qfmt + Q ≤ 2^128` (the deployed skeleton has at most `2^70`
operations), the entropy terms are at most `2^-2200`. -/
theorem zkBound_le (QP Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR εI : ℕ → ℝ≥0∞) (Q : ℕ)
    (hQ : QP + (Qfmt + Q) ≤ 2 ^ 128) :
    zkBound QP Qp Qfmt εFS εR εI Q ≤
      εR Q + (εFS + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹ +
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
  have hHV := jointHVZK_of_link Jw.P hv.h3 Jw.P₀ hv.hE Jw.stmtE Jw.gK Jw.van hv.hvan hv.hsat
    hv.hvan0 hv.hq hv.hK hv.hN hv.hdeg Jw.inK hv.hinK Jw.sigmaAt hv.hsig Jw.wir Jw.S₁ Jw.S₂ hv.hS₁
    hv.hS₂ Jw.T₁ Jw.T₂ Jw.cl₁ Jw.cl₂ hv.hT₁ hv.hT₂ Jw.simT₁ Jw.simT₂ hv.hsimT₁ hv.hsimT₂ Jw.lk hv.hch
  have hfac := factors_single hv.hS₁ hv.hS₂ hv.h3 hv.hK hv.h40₁ hv.h40₂ Jw.lk
  have hfac₂ := factors_pair hv.hS₁ hv.hS₂ hv.h3 hv.hK hv.h40₁ hv.h40₂ Jw.lk
  have hmain := QuotientZk.DRpm.zk_rpm_skel Jw.P (skel stmt) Jw.simV _ εFS (1 / 2 ^ 165)
    ((2 : ℝ≥0∞) ^ 2368)⁻¹ ((2 : ℝ≥0∞) ^ 2368)⁻¹ QP (Qfmt + Q) (Qp + (Qfmt + Q)) (hskel stmt)
    (hFS stmt w hw) hHV.1 hHV.2 (fun σ k x hx v y ↦ (hfac σ k x hx y).some.bound v)
    (fun σ k x k' x' hx hx' hne v ↦ (hfac₂ σ k x k' x' hx hx' hne).some.bound v) hv.hrow
    (hduplex stmt w hw) D hD hQ
  rw [QuotientZk.Deployed.card_positions] at hmain
  have h := ((hreal stmt w hw D₀ Q hD₀).trans hmain).trans (hideal stmt w hw D₀ Q hD₀)
  refine h.mono (le_of_eq ?_)
  simp only [zkBound]

end Main

end PcsQuotient.EndToEnd
