-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Main
import ZK.Joint

/-!
# Zero knowledge of the membership proof, the joint model instantiated

**`zeroKnowledge_deployed_end`**: `zeroKnowledge_end` (`ZK/Main.lean`) with the joint model of the
deployed prover instantiated (`deployedJointData`, valid by `deployedJointData_valid`, `ZK/Joint.lean`):

`ZeroKnowledgeWith s₀ (zkSimulator (fun _ ↦ deployedPub rep) (deployedSimV …) skelOf fmt) rpmSimOracle
(zkBoundEnd Qp Qfmt εR)`.

**The simulator, concretely.** Its public part `deployedPub rep` is the deployed prover's (`nRaw`
challenges, the witness table committed first and the quotient table after three, the opened
positions `PbOpened` the challenges give); its view simulator `deployedSimV` is `jointSimV` (the
simulated values, the simulator's tables `simTW`, `simTQ` opened by the honest openings `openW`,
`openQ` with fresh paddings) read through the deployed prover's public renderer (`out`), at the
challenges the oracle's answers give (`chOf`). Neither reads the witness: they equal the joint model's
for every witness by definition (`pub_deployed`, `simV_deployed`).

**Named**: the fields (`h3`, `hq`, `hK`, `hY`), F1's facts on the statement and the witness (`hE`, `hN`,
`hvan`, `hsat`, `hvan0`, `hdeg`), the simulator's public functions (`hinK`, `hsig`), the honest tables'
claims (`hTW`, `hTQ`); the prover's and the formatting's permutation budgets; `CoinsMatch`;
`ProverBridge`.
-/

open OracleComp OracleSpec Common Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto View)

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
  [CharP K 2] [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]
  [SampleableType E]

/-- **The deployed prover's public part**: `nRaw` challenges, the witness table committed after none
and the quotient table after three, the positions `PbOpened` opens. -/
def deployedPub (rep : QuotientZk.Instance.Rep K E) : PubProto :=
  ⟨nRaw, PbcK, PbOpened (E := E) rep⟩

/-- **The deployed view simulator**: `jointSimV` at the challenges the oracle's answers give, read
through the deployed prover's public renderer `out` (its secret arguments unused, here zero). -/
noncomputable def deployedSimV (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E)
    (stmt : Fin P₀.words → E) (Y : E) (R : Renderer K E) (inK : E → Bool) (sigmaAt : E → E) :
    List Out → ProbComp (View Msg Inp Tbl Pos) :=
  fun σ ↦ out rep P₀ 0 0 stmt Y (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ 0) R σ <$>
    jointSimV inK sigmaAt (fun _ ↦ ()) (openW rep Y) (openQ rep P₀ Y) (simTW rep Y)
      (simTQ rep P₀ stmt Y) (chOf rep.limbs σ)

theorem pub_deployed (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (stmt : Fin P₀.words → E)
    (Y : E) (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (R : Renderer K E) (inK : E → Bool)
    (sigmaAt : E → E) :
    PubProto.of (deployedJointData rep P₀ stmt Y gK van TW TQ R inK sigmaAt).P = deployedPub rep :=
  rfl

theorem simV_deployed (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (stmt : Fin P₀.words → E)
    (Y : E) (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (R : Renderer K E) (inK : E → Bool)
    (sigmaAt : E → E) :
    (deployedJointData rep P₀ stmt Y gK van TW TQ R inK sigmaAt).simV =
      deployedSimV rep P₀ stmt Y R inK sigmaAt :=
  rfl

/-- **Zero knowledge of the membership proof, the joint model instantiated.** For the fields'
representations `rep`, the reduction's parameters `P₀`, the statement's words `stmtE stmt`, the
extension's `Y`, the witness's polynomials `gK stmt w`, `van stmt w`, the honest tables
`TW stmt w`, `TQ stmt w`, the public renderer `R` and the simulator's public functions `inK`, `sigmaAt`:
`ZeroKnowledgeWith` for `zkSimulator` at `deployedPub rep` and `deployedSimV`, on `skelSetup`, at
`zkBoundEnd Qp Qfmt εR`. -/
theorem zeroKnowledge_deployed_end (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (Y : E)
    (R : Renderer K E) (inK : E → Bool) (sigmaAt : E → E) (stmtE : Statement → Fin P₀.words → E)
    (gK : Statement → Secret → Fin 4 → K[X]) (van : Statement → Secret → K[X])
    (TW : Statement → Secret → (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : Statement → Secret → E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K)
    (h3 : finrank K E = 3) (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64)
    (hY : LinearIndependent K ![1, Y, Y ^ 2]) (hE : P₀.Exact) (hN : P₀.nCells = 2 ^ 24)
    (hvan : ∀ stmt w, Relation stmt w → ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) (van stmt w) = 0)
    (hsat : ∀ stmt w, Relation stmt w →
      P₀.Sat (stmtE stmt) (P₀.cells (committed (gK stmt w) (van stmt w) 0)))
    (hvan0 : ∀ stmt w, Relation stmt w → van stmt w ≠ 0)
    (hdeg : ∀ stmt w, Relation stmt w → (van stmt w).natDegree ≤ 2 ^ 22)
    (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (hTW : ∀ stmt w, Relation stmt w → ∀ c, good P₀ (gK stmt w) (van stmt w) c → ∀ m,
      (openW rep Y).claims (c, redMsgs P₀ (gK stmt w) (van stmt w) c.1.1.2 m) (TW stmt w m) =
        valsW c (redMsgs P₀ (gK stmt w) (van stmt w) c.1.1.2 m))
    (hTQ : ∀ stmt w, Relation stmt w → ∀ c, good P₀ (gK stmt w) (van stmt w) c → ∀ m,
      (openQ rep P₀ Y).claims (c, redMsgs P₀ (gK stmt w) (van stmt w) c.1.1.2 m)
          (TQ stmt w c.1.1.1 m) =
        valsQ P₀ (stmtE stmt) Y c (redMsgs P₀ (gK stmt w) (van stmt w) c.1.1.2 m))
    (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (coinsOf : Rand K ιW YW ιQ YQ → Masks × Padding × Padding)
    (Qp Qfmt : ℕ) (εR : ℕ → ℝ≥0∞) (s₀ : RpmSimState)
    (hfmt : ∀ pf, IsTotalQueryBound (fmt pf) Qfmt)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (deployedJointData rep P₀ (stmtE stmt) Y (gK stmt w)
          (van stmt w) (TW stmt w) (TQ stmt w) R inK sigmaAt).P keccak256OverPermutation
        queryPermutation (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost Qp)
    (hcoins : CoinsMatch coinsOf)
    (hbridge : ∀ stmt w, Relation stmt w →
      ProverBridge stmt w (deployedJointData rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w)
        (TW stmt w) (TQ stmt w) R inK sigmaAt).P (skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt
        coinsOf εR) :
    ZeroKnowledgeWith s₀
      (zkSimulator (fun _ ↦ deployedPub rep)
        (fun stmt ↦ deployedSimV rep P₀ (stmtE stmt) Y R inK sigmaAt)
        (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt)
      rpmSimOracle (zkBoundEnd Qp Qfmt εR) :=
  zeroKnowledge_end (fun stmt w ↦ deployedJointData rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w)
      (TW stmt w) (TQ stmt w) R inK sigmaAt) (fun _ ↦ deployedPub rep)
    (fun stmt ↦ deployedSimV rep P₀ (stmtE stmt) Y R inK sigmaAt) stmtBytes idW idσ idQ rowsW hrows
    fmt coinsOf Qp Qfmt εR s₀ hfmt
    (fun stmt w hw ↦ deployedJointData_valid rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w)
      (TW stmt w) (TQ stmt w) R inK sigmaAt h3 hq hK hY hE (hvan stmt w hw) (hsat stmt w hw)
      (hvan0 stmt w hw) hN (hdeg stmt w hw) hinK hsig (hTW stmt w hw) (hTQ stmt w hw))
    (fun stmt _ _ ↦ pub_deployed rep P₀ (stmtE stmt) Y _ _ _ _ R inK sigmaAt)
    (fun stmt _ _ ↦ simV_deployed rep P₀ (stmtE stmt) Y _ _ _ _ R inK sigmaAt)
    hprover hcoins hbridge

end PcsQuotient.EndToEnd
