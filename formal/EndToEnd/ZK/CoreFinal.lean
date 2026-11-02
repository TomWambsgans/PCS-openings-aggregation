-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoreDefs

/-!
# Zero knowledge, rendered by WHIR's honest prover

`zeroKnowledge_deployed_endR`: `zeroKnowledge_deployed_end` (`ZK/End.lean`) with a renderer per
statement. **`zeroKnowledge_whirD`**: at the deployed instance (`ZK/Final.lean`'s facts), the renderer
`whirRenderer deployedRep stmt`, the prover bridge from the deployed core `CoreD` and `badProb ≤ δ`
(`ZK/CoreDefs.lean`).
-/

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open LeanVM.Parameters Primitives
open scoped ENNReal

/- The fields' instances of `formal/Field` (`F64`, `F192`), as `ZK/Final.lean` has them: the
completeness side's imports bring others of the same types. -/
attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

namespace PcsQuotient.EndToEnd

set_option linter.unusedSectionVars false

section Generic

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
  [CharP K 2] [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]
  [SampleableType E]

/-- `zeroKnowledge_deployed_end` (`ZK/End.lean`) with **a renderer per statement** (`R stmt`: WHIR's
honest prover reads the statement's claims). -/
theorem zeroKnowledge_deployed_endR (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (Y : E)
    (R : Statement → Renderer K E) (inK : E → Bool) (sigmaAt : E → E)
    (stmtE : Statement → Fin P₀.words → E)
    (gK : Statement → Secret → Fin 4 → K[X]) (van : Statement → Secret → K[X])
    (TW : Statement → Secret → (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : Statement → Secret → E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K)
    (h3 : Module.finrank K E = 3) (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64)
    (hY : LinearIndependent K ![1, Y, Y ^ 2]) (hE : P₀.Exact) (hN : P₀.nCells = 2 ^ 24)
    (hvan : ∀ stmt w, Relation stmt w → ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) (van stmt w) = 0)
    (hsat : ∀ stmt w, Relation stmt w →
      P₀.Sat (stmtE stmt) (P₀.cells (committed (gK stmt w) (van stmt w) 0)))
    (hvan0 : ∀ stmt w, Relation stmt w → van stmt w ≠ 0)
    (hdeg : ∀ stmt w, Relation stmt w → (van stmt w).natDegree ≤ 2 ^ 22)
    (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (hTW : ∀ stmt w, Relation stmt w → ∀ c, good P₀ (gK stmt w) (van stmt w) c → ∀ m,
      ClaimsND (K := K) P₀ (gK stmt w) (van stmt w) c m →
      (openW rep Y).claims (c, redMsgs P₀ (gK stmt w) (van stmt w) c.1.1.2 m) (TW stmt w m) =
        valsW c (redMsgs P₀ (gK stmt w) (van stmt w) c.1.1.2 m))
    (hTQ : ∀ stmt w, Relation stmt w → ∀ c, good P₀ (gK stmt w) (van stmt w) c → ∀ m,
      ClaimsND (K := K) P₀ (gK stmt w) (van stmt w) c m →
      (openQ rep P₀ Y).claims (c, redMsgs P₀ (gK stmt w) (van stmt w) c.1.1.2 m)
          (TQ stmt w c.1.1.1 m) =
        valsQ P₀ (stmtE stmt) Y c (redMsgs P₀ (gK stmt w) (van stmt w) c.1.1.2 m))
    (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (e : Rand K ιW YW ιQ YQ → CoinWords) (he : Function.Bijective e)
    (Qp : ℕ) (εR : ℕ → ℝ≥0∞) (s₀ : RpmSimState)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (deployedJointData rep P₀ (stmtE stmt) Y (gK stmt w)
          (van stmt w) (TW stmt w) (TQ stmt w) (R stmt) inK sigmaAt).P keccak256OverPermutation
        queryPermutation (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost Qp)
    (hbridge : ∀ stmt w, Relation stmt w →
      ProverBridge stmt w (deployedJointData rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w)
        (TW stmt w) (TQ stmt w) (R stmt) inK sigmaAt).P (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)
        (fmt stmt) (decodeCoins ∘ e) εR) :
    ZeroKnowledgeWith s₀
      (zkSimulator (fun _ ↦ deployedPub rep)
        (fun stmt ↦ deployedSimV rep P₀ (stmtE stmt) Y (R stmt) inK sigmaAt)
        (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt)
      rpmSimOracle (zkBoundEnd Qp fmtBudget εR) :=
  zeroKnowledge_end (fun stmt w ↦ deployedJointData rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w)
      (TW stmt w) (TQ stmt w) (R stmt) inK sigmaAt) (fun _ ↦ deployedPub rep)
    (fun stmt ↦ deployedSimV rep P₀ (stmtE stmt) Y (R stmt) inK sigmaAt) stmtBytes idW idσ idQ rowsW
    hrows fmt (decodeCoins ∘ e) Qp fmtBudget εR s₀ fmt_queryBound
    (fun stmt w hw ↦ deployedJointData_valid rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w)
      (TW stmt w) (TQ stmt w) (R stmt) inK sigmaAt h3 hq hK hY hE (hvan stmt w hw) (hsat stmt w hw)
      (hvan0 stmt w hw) hN (hdeg stmt w hw) hinK hsig (hTW stmt w hw) (hTQ stmt w hw))
    (fun stmt _ _ ↦ pub_deployed rep P₀ (stmtE stmt) Y _ _ _ _ (R stmt) inK sigmaAt)
    (fun stmt _ _ ↦ simV_deployed rep P₀ (stmtE stmt) Y _ _ _ _ (R stmt) inK sigmaAt)
    hprover (coinsMatch_of_bijective e he) hbridge

end Generic


/-- **Zero knowledge of the membership proof, rendered by WHIR's honest prover**: the deployed
instance (`ZK/Final.lean`'s facts), the renderer `whirRenderer deployedRep stmt` per statement, the
bridge from the deployed core and `badProb ≤ δ`; at `zkBoundEnd Qp fmtBudget (· ↦ δ)`. -/
theorem zeroKnowledge_whirD (Qp : ℕ) (δ : ℝ≥0∞) (s₀ : RpmSimState)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (jdW stmt w).P keccak256OverPermutation
        queryPermutation (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytesD stmt) idWD idσD idQD rowsWD)) permutationCallCost Qp)
    (hcore : ∀ stmt w, Relation stmt w → CoreD stmt w)
    (hbad : ∀ stmt w, Relation stmt w → ∀ s, badProb stmt w ((decodeCoins ∘ eD) s) ≤ δ) :
    ZeroKnowledgeWith s₀
      (zkSimulator (fun _ ↦ deployedPub deployedRep)
        (fun stmt ↦ deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y
          (Render.whirRenderer deployedRep stmt) inKD sigmaAtD)
        (fun stmt ↦ skelSetup (stmtBytesD stmt) idWD idσD idQD rowsWD) fmt)
      rpmSimOracle (zkBoundEnd Qp fmtBudget fun _ ↦ δ) :=
  zeroKnowledge_deployed_endR deployedRep P₀D F192.Y (fun stmt ↦ Render.whirRenderer deployedRep stmt)
    inKD sigmaAtD stmtWD (fun _ w ↦ gKD w) (fun _ _ ↦ vanD) (fun _ w ↦ TWD w) (fun _ w ↦ TQD w)
    finrank_KE card_E card_K linIndep_Y hED hND (fun _ _ _ ↦ hvanD) (fun stmt w hw ↦ hsatD stmt w hw)
    (fun _ _ _ ↦ hvan0D) (fun _ _ _ ↦ hdegD) inKD_iff (fun _ ↦ rfl) (fun _ w _ ↦ hTWD w)
    (fun stmt w hw ↦ hTQD stmt w hw) stmtBytesD idWD idσD idQD rowsWD length_rowsWD eD eD_bijective
    Qp (fun _ ↦ δ) s₀ hprover
    (fun stmt w hw ↦ proverBridge_deployed stmt w δ (hcore stmt w hw) (hbad stmt w hw))

end PcsQuotient.EndToEnd
