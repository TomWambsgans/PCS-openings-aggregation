-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.ProverBridgeReduce
import ZK.ProverBridgeRender
import ZK.End

/-!
# The prover bridge of the deployed prover, rendered by WHIR's honest prover

`zeroKnowledge_deployed_end` (`ZK/End.lean`) names `ProverBridge … εR` (`ZK/Real.lean`). Here:

* **the renderer** is fixed: `whirRenderer rep stmt` (`ProverBridgeRender.lean`), WHIR's honest prover
  on the available joint view, at `K = GF(2^64)`, `E = GF(2^192)`;
* **`proverBridge_whir`**: `ProverBridge` of the deployed joint model with that renderer, at
  `εR Q = δ`, from
  - **`CoreWhir`** (a statement about programs, no probability: `ProverBridgeReduce.lean`): for every
    permutation `π` of the Keccak state and every completion of the skeleton's oracle (`gH`, `gF`),
    whenever the statement's prover run with `π` makes a proof, `fmt` run with `π` turns the
    skeleton's proof (`skelDet`, the deployed prover `Pb` against the oracle `Gof (kDet π) π gH gF`)
    into that proof;
  - **`hnone`**: the statement's prover makes no proof (a proof of work exhausting its `2^25`
    nonces, or a degenerate challenge) with probability at most `δ`, for every coins of the
    skeleton model's randomness;
* **`zeroKnowledge_deployed_whir`**: `zeroKnowledge_end` (`ZK/Main.lean`) with that joint model, the
  renderer per statement (the simulator knows the statement), and the bridge from `CoreWhir` and
  `hnone`: `ZeroKnowledgeWith` at `zkBoundEnd Qp fmtBudget (fun _ ↦ δ)`, that is
  `δ + 2^-113 + 2^-165 + 2^-2200 + (Qp + 2^23 + Q)² / 2^508` for `Q ≤ 2^126`.

What `CoreWhir` contains (the skeleton trace test's list of differences, `formal/README.md`, made a
statement about programs; the random permutation, the repeated queries, the queries' order and the
grinding past `2^25` are gone, `ProverBridgeEager.lean`, `ProverBridgeReduce.lean`):
the trees (the skeleton's `levels` and the statement's `buildTreeM`; `fmt`'s full paths from the pruned
multiproofs), the encodings (the chain's label, roots and values; the IVs' bytes; the duplex's lanes),
the tables (the secret leaves `PbRow` are the bytes of the statement's codewords' rows, at the coins
`coinsOf s`), the values and claims (the joint view's are the statement's), and the openings (the
verifier's program at the deployed layouts runs in the skeleton's order, and WHIR's honest script on
the statement's stack sends what `hybridScript` sends on the view's lane rounds and folded table).
-/

open OracleComp OracleSpec Common Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open LeanVM.Parameters (K E)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto View)
open Eager (St)

set_option linter.unusedSectionVars false

section Deployed

variable [Fintype E]

/-- **The probability that the statement's prover makes no proof** at the coins `c`. -/
noncomputable def noneProb (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding) : ℝ≥0∞ :=
  Pr{let r ← runWithRandomPermutation (prover queryPermutation stmt w c)}[r = none]

/-- **The deterministic core of the deployed prover rendered by WHIR's honest prover**: for every
coins `s` of the skeleton model, permutation `π` and completions `gH`, `gF`, whenever the statement's
prover with `π` makes the proof `x`, `fmt` with `π` makes `x` of the skeleton's proof against
`Gof (kDet π) π gH gF`. -/
def CoreWhir (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (stmtE : Fin P₀.words → E) (Y : E)
    (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (stmt : Statement) (w : Secret)
    (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (coinsOf : RandD K → Masks × Padding × Padding) : Prop :=
  ∀ (s : RandD K) (π : Equiv.Perm St) (gH : List UInt8 → KSt) (gF : KSt → DigestBytes) (x : Proof),
    proverDet π stmt w (coinsOf s) = some x →
      fmtDet π stmt (skelDet (QuotientZk.DRpm.ofBytes
        (Pb rep P₀ gK van stmtE Y TW TQ (Render.whirRenderer rep stmt))) (Gof (kDet π) π gH gF) s
        skel) = some x

variable [Fintype K] [SampleableType K] [SampleableType E]

/-- **The prover bridge of the deployed prover with WHIR's honest prover as its renderer**, at
`εR Q = δ`. -/
theorem proverBridge_whir (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (stmtE : Fin P₀.words → E) (Y : E)
    (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (inK : E → Bool) (sigmaAt : E → E)
    (stmt : Statement) (w : Secret) (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (coinsOf : RandD K → Masks × Padding × Padding) (δ : ℝ≥0∞)
    (hcore : CoreWhir rep P₀ stmtE Y gK van TW TQ stmt w skel coinsOf)
    (hnone : ∀ s, noneProb stmt w (coinsOf s) ≤ δ) :
    ProverBridge stmt w (deployedJointData rep P₀ stmtE Y gK van TW TQ
      (Render.whirRenderer rep stmt) inK sigmaAt).P skel (fmt stmt) coinsOf (fun _ ↦ δ) :=
  proverBridge_of_det stmt w _ skel coinsOf δ hcore hnone

/-- **Zero knowledge of the membership proof, the joint model instantiated with WHIR's honest prover
as the renderer** (`zeroKnowledge_deployed_end` with `R = whirRenderer rep stmt` and its
`ProverBridge` from `CoreWhir` and `hnone`): `ZeroKnowledgeWith` at `zkBoundEnd Qp fmtBudget (· ↦ δ)`. -/
theorem zeroKnowledge_deployed_whir (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (Y : E) (inK : E → Bool)
    (sigmaAt : E → E) (stmtE : Statement → Fin P₀.words → E)
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
    (Qp : ℕ) (δ : ℝ≥0∞) (s₀ : RpmSimState)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (deployedJointData rep P₀ (stmtE stmt) Y (gK stmt w)
          (van stmt w) (TW stmt w) (TQ stmt w) (Render.whirRenderer rep stmt) inK sigmaAt).P
        keccak256OverPermutation queryPermutation (QuotientZk.DRpm.coinR KSt)
        (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost Qp)
    (hcore : ∀ stmt w, Relation stmt w →
      CoreWhir rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w) (TW stmt w) (TQ stmt w) stmt w
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW) (decodeCoins ∘ e))
    (hnone : ∀ stmt w, Relation stmt w → ∀ s, noneProb stmt w ((decodeCoins ∘ e) s) ≤ δ) :
    ZeroKnowledgeWith s₀
      (zkSimulator (fun _ ↦ deployedPub rep)
        (fun stmt ↦ deployedSimV rep P₀ (stmtE stmt) Y (Render.whirRenderer rep stmt) inK sigmaAt)
        (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt)
      rpmSimOracle (zkBoundEnd Qp fmtBudget fun _ ↦ δ) :=
  zeroKnowledge_end (fun stmt w ↦ deployedJointData rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w)
      (TW stmt w) (TQ stmt w) (Render.whirRenderer rep stmt) inK sigmaAt) (fun _ ↦ deployedPub rep)
    (fun stmt ↦ deployedSimV rep P₀ (stmtE stmt) Y (Render.whirRenderer rep stmt) inK sigmaAt)
    stmtBytes idW idσ idQ rowsW hrows fmt (decodeCoins ∘ e) Qp fmtBudget (fun _ ↦ δ) s₀
    fmt_queryBound
    (fun stmt w hw ↦ deployedJointData_valid rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w)
      (TW stmt w) (TQ stmt w) _ inK sigmaAt h3 hq hK hY hE (hvan stmt w hw) (hsat stmt w hw)
      (hvan0 stmt w hw) hN (hdeg stmt w hw) hinK hsig (hTW stmt w hw) (hTQ stmt w hw))
    (fun stmt _ _ ↦ pub_deployed rep P₀ (stmtE stmt) Y _ _ _ _ _ inK sigmaAt)
    (fun stmt _ _ ↦ simV_deployed rep P₀ (stmtE stmt) Y _ _ _ _ _ inK sigmaAt)
    hprover (coinsMatch_of_bijective e he)
    (fun stmt w hw ↦ proverBridge_whir rep P₀ (stmtE stmt) Y (gK stmt w) (van stmt w) (TW stmt w)
      (TQ stmt w) inK sigmaAt stmt w _ _ δ (hcore stmt w hw) (hnone stmt w hw))

end Deployed

end PcsQuotient.EndToEnd

/--
info: 'PcsQuotient.EndToEnd.proverBridge_whir' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.proverBridge_whir

/--
info: 'PcsQuotient.EndToEnd.zeroKnowledge_deployed_whir' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed_whir
