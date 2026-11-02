-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Assembly
import QuotientZk.Instance.Main

/-!
# The joint model of the deployed prover, instantiated

`deployedJointData`: the `JointData` of the deployed prover, from `formal/QuotientZk/Instance/`:
its prover `Pb` (`Instance/Prover.lean`: the claims' bytes at the openings' starts, then any public
renderer `R` of the available joint view; leaves the 64-word images of the stacks' rows), the claims'
windows `cwD`, the openings `openW`, `openQ` (`Instance/Openings.lean`: `witness_layout(22)`,
`quotient_layout(22)` with the gadget, the verifier's claims, the novel basis at the opened
positions), the honest tables `TW`, `TQ`, the simulator's tables `simTW`, `simTQ` (`Instance/Builder.lean`:
computed by a Gaussian elimination, with the verifier's claimed values whenever some table has them,
`claims_simTW`, `claims_simTQ`) and the link `link`.

**`deployedJointData_valid`**: `JointData.Valid` from

* the field: `[E : K] = 3`, `|E| = 2^192`, `|K| = 2^64`, `1, Y, Y²` independent (and `rep`: `K`'s
  64-bit words, `E`'s limbs);
* F1's hypotheses on the statement and the witness (`hE`, `hvan`, `hsat`, `hvan0`, `hN`, `hdeg`) and
  the simulator's public functions (`hinK`, `hsig`), as `JointData.Valid` has them;
* **the honest tables meet the verifier's claims** off the degenerate challenges and masks (`hTW`,
  `hTQ`, under `ClaimsND`: the claims' scales `1 + w_k(t)`, the row outside `K`, the copy
  denominator `claimDen · vRows(t)`; at the degenerate ones the verifier divides by zero).

Every other field of `Valid` is proved (`Instance/Main.lean`, `Instance/Fresh.lean`).
-/

open OracleComp OracleSpec Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt)

namespace PcsQuotient.EndToEnd

set_option linter.unusedSectionVars false

section Deployed

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
  [CharP K 2] [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]
  [SampleableType E]

/-- **The joint model of the deployed prover**, for the fields' representations `rep`, the
reduction's parameters `P₀` and statement `stmt`, the extension's `Y`, the witness's polynomials
`gK` and the vanishing polynomial `van`, the honest tables `TW`, `TQ`, the message renderer `R`, and
the simulator's public functions `inK`, `sigmaAt`. -/
noncomputable def deployedJointData (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (stmt : Fin P₀.words → E)
    (Y : E) (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (R : Renderer K E) (inK : E → Bool)
    (sigmaAt : E → E) :
    JointData K E ΓW ΓQ Γσ Unit ιW YW (Fin 224) (L0View E ιW YW (Fin 224) K) ιQ YQ (Fin 225)
      (L0View E ιQ YQ (Fin 225) K) where
  Pb := Pb rep P₀ gK van stmt Y TW TQ R
  cw := cwD rep
  P₀ := P₀
  stmtE := stmt
  gK := gK
  van := van
  inK := inK
  sigmaAt := sigmaAt
  wir := fun _ => ()
  S₁ := openW rep Y
  S₂ := openQ rep P₀ Y
  T₁ := T₁ TW
  T₂ := T₂ TQ
  cl₁ := clW rep Y
  cl₂ := clQ rep P₀ stmt Y
  simT₁ := simTW rep Y
  simT₂ := simTQ rep P₀ stmt Y
  lk := link rep P₀ gK van stmt Y TW TQ R

/-- **The deployed joint model is valid**, given the field, F1's hypotheses, the simulator's public
functions and the honest tables' claims. -/
theorem deployedJointData_valid (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (stmt : Fin P₀.words → E) (Y : E)
    (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (R : Renderer K E) (inK : E → Bool)
    (sigmaAt : E → E)
    (h3 : finrank K E = 3) (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64)
    (hY : LinearIndependent K ![1, Y, Y ^ 2])
    (hE : P₀.Exact) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hN : P₀.nCells = 2 ^ 24) (hdeg : van.natDegree ≤ 2 ^ 22)
    (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (hTW : ∀ c, good P₀ gK van c → ∀ m, ClaimsND (K := K) P₀ gK van c m →
      (openW rep Y).claims (c, redMsgs P₀ gK van c.1.1.2 m) (TW m) =
        valsW c (redMsgs P₀ gK van c.1.1.2 m))
    (hTQ : ∀ c, good P₀ gK van c → ∀ m, ClaimsND (K := K) P₀ gK van c m →
      (openQ rep P₀ Y).claims (c, redMsgs P₀ gK van c.1.1.2 m) (TQ c.1.1.1 m) =
        valsQ P₀ stmt Y c (redMsgs P₀ gK van c.1.1.2 m)) :
    (deployedJointData rep P₀ stmt Y gK van TW TQ R inK sigmaAt).Valid where
  h3 := h3
  hE := hE
  hvan := hvan
  hsat := hsat
  hvan0 := hvan0
  hq := hq
  hK := hK
  hN := hN
  hdeg := hdeg
  h40₁ := by rw [card_ιW]
  h40₂ := by rw [card_ιQ]; norm_num
  hinK := hinK
  hsig := hsig
  hS₁ := conditionsW rep h3 hY
  hS₂ := conditionsQ rep P₀ h3 hY
  hT₁ c hc m hnd := (hTW c hc m hnd).trans (claims_simTW (hTW c hc m hnd)).symm
  hT₂ c hc m hnd := (hTQ c hc m hnd).trans (claims_simTQ (hTQ c hc m hnd)).symm
  hsimT₁ _ _ _ := rfl
  hsimT₂ _ _ _ := rfl
  hch := chOf_uniform rep.limbs
  hcw := hcw_deployed rep hq
  hrow₀ := hrow₀_Pb rep P₀ gK van stmt Y TW TQ h3 hK R
  hlong := hlong_Pb rep P₀ gK van stmt Y TW TQ R
  hcK := hcK_Pb rep P₀ gK van stmt Y TW TQ R
  hclW := claimsAt_W rep P₀ gK van stmt Y TW TQ R
  hclσ := claimsAt_σ rep P₀ gK van stmt Y TW TQ R
  hclQ := claimsAt_Q rep P₀ gK van stmt Y TW TQ R
  hn := hn_Pb rep P₀ gK van stmt Y TW TQ R

end Deployed

end PcsQuotient.EndToEnd

/--
info: 'PcsQuotient.EndToEnd.deployedJointData_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.deployedJointData_valid
