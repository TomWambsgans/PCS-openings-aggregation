-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.RpmDeployed

/-!
# Zero knowledge of the deployed proof in the random-permutation model: the end statements

The random-permutation-model versions of `zk_deployed`, `zk_deployed_bits` and
`zk_deployed_joint` (`Deployed/Main.lean`, `JointDeployed.lean`), for the deployed prover hashing
with Keccak-256 and calling Keccak-f[1600] over the random permutation `π`, every distinguisher
`D` of at most `QD` queries of `π` and `π⁻¹`, and the explicit simulator `simGameRpmD`
(`RpmDeployed.lean`):

* **`zk_rpm_deployed`**: `εFS + εhv + 2^24 (skelBound sh + QD) δ + 2^48 δ₂ + Q² / 2^508`;
* **`zk_rpm_deployed_bits`**: at `2^22` rows, `δ = δ₂ = 2^-2368`, `QD ≤ 2^127`:
  `εFS + εhv + 2^-2200 + Q² / 2^508`;
* **`zk_rpm_deployed_joint`**: with the joint model's honest-verifier zero knowledge
  (`jointHVZK_of_link`) and its factorizations (`factors_single`, `factors_pair`):
  `εFS + 2^-165 + 2^-2200 + Q² / 2^508`.

`Q` bounds the real game's permutation calls on every path (`hQ`). Beyond `zk_deployed`'s
hypotheses (`hFS` with an empty cache before the proof, the HVZK, the factorizations): `hrow` (the
secret tables' rows are byte strings), `hduplex` (the prover's permutation calls follow the duplex
discipline), `hQ`.

**Superseded**: `zk_rpm_deployed_joint` asks the honest tables' claims (`hT₁`, `hT₂`) at every mask,
which the honest tables do not meet at degenerate challenges and masks; the deployed result is
`zeroKnowledge_closed` through `jointHVZKε_of_linkV` (`Instance/Nondeg.lean`) and
`zk_rpm_skel_approx` (`RpmDeployed.lean`).
-/

open OracleComp OracleSpec Common
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec Proof)
open scoped ENNReal

namespace QuotientZk.DRpm

set_option linter.unusedSectionVars false

section Deployed

variable {S : Type} [SampleableType S]

/-- **Zero knowledge of the deployed proof in the random-permutation model.** For the deployed
skeleton (`Deployed.skel sh`, at most `skelBound sh` operations) and a prover `P` whose view factors
through each secret table, every distinguisher `D` of at most `QD` queries of `π` and `π⁻¹`, with
the real game of at most `Q` permutation calls on every path, tells the real game from the
simulated one with advantage at most
`εFS + εhv + 2^24 (skelBound sh + QD) δ + 2^48 δ₂ + Q² / 2^508`. -/
theorem zk_rpm_deployed (sh : Deployed.Shape) (P : Proto S Inp Out Msg Tbl Pos)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εFS εhv δ δ₂ : ℝ≥0∞) (QD Q : ℕ)
    (hFS : Deployed.FSFresh P (Deployed.skel sh) [] εFS) (hHV : Deployed.JointHVZK P simV good εhv)
    (hfac : ∀ σ k x, P.opened σ k x = false → ∀ y,
      Nonempty (Deployed.Factors P σ (fun s => P.rows s σ k x = y) δ))
    (hfac₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') →
      Nonempty (Deployed.Factors P σ (fun s => P.rows s σ k x = P.rows s σ k' x') δ₂))
    (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m)
    (hduplex : DuplexDiscipline P (Deployed.skel sh))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpmD P (Deployed.skel sh) D s) permutationCallCost Q) :
    Close (realGameRpmD P (Deployed.skel sh) D) (simGameRpmD P simV (Deployed.skel sh) D)
      (εFS + εhv + ((2 ^ 24 * (Deployed.skelBound sh + QD) : ℕ) * δ + (2 ^ 48 : ℕ) * δ₂) +
        (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) := by
  have h := zk_rpm_skel P (Deployed.skel sh) simV good εFS εhv δ δ₂ (Deployed.skelBound sh) QD Q
    (Deployed.skel_queryBound sh) hFS hHV.1 hHV.2
    (fun σ k x hx v y => (hfac σ k x hx y).some.bound v)
    (fun σ k x k' x' hx hx' hne v => (hfac₂ σ k x k' x' hx hx' hne).some.bound v)
    hrow hduplex D hD hQ
  rw [Deployed.card_positions] at h
  simpa [show (2 ^ 24) ^ 2 = 2 ^ 48 by norm_num] using h

/-- **Zero knowledge of the deployed proof in the random-permutation model, at our sizes**: the
deployed shape (`2^22` rows), the layouts' `δ = δ₂ = 2^-2368`, at most `2^127` queries of the
distinguisher: advantage at most `εFS + εhv + 2^-2200 + Q² / 2^508`. -/
theorem zk_rpm_deployed_bits (stmt : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rows : List (List UInt8)) (hrows : rows.length = 2 ^ 19) (sh : Deployed.Shape)
    (hsh : sh = Deployed.deployedShape stmt idW idσ idQ rows) (P : Proto S Inp Out Msg Tbl Pos)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εFS εhv : ℝ≥0∞) (QD Q : ℕ) (hQD : QD ≤ 2 ^ 127)
    (hFS : Deployed.FSFresh P (Deployed.skel sh) [] εFS)
    (hHV : Deployed.JointHVZK P simV good εhv)
    (hfac : ∀ σ k x, P.opened σ k x = false → ∀ y,
      Nonempty (Deployed.Factors P σ (fun s => P.rows s σ k x = y) ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (hfac₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') →
      Nonempty (Deployed.Factors P σ (fun s => P.rows s σ k x = P.rows s σ k' x')
        ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m)
    (hduplex : DuplexDiscipline P (Deployed.skel sh))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost
      (zkGameRpmD P (Deployed.skel sh) D s)
      permutationCallCost Q) :
    Close (realGameRpmD P (Deployed.skel sh) D)
      (simGameRpmD P simV (Deployed.skel sh) D)
      (εFS + εhv + ((2 : ℝ≥0∞) ^ 2200)⁻¹ + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) := by
  have hb : Deployed.skelBound sh ≤ 2 ^ 70 := by
    rw [hsh]; exact Deployed.skelBound_deployed stmt idW idσ idQ rows hrows
  refine (zk_rpm_deployed sh P simV good εFS εhv _ _ QD Q hFS hHV hfac hfac₂ hrow hduplex D hD
    hQ).mono (add_le_add (add_le_add le_rfl (Deployed.merkleTerm_le _ ?_)) le_rfl)
  have : (2 : ℕ) ^ 70 + 2 ^ 127 ≤ 2 ^ 128 := by norm_num
  omega

end Deployed

/-! ## With the joint model -/

section Joint

open Polynomial Module QuotientSecurity QuotientSecurity.Hiding QuotientZk.Joint

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **Superseded**: its hypotheses `hT₁`/`hT₂` are not met by the honest tables at degenerate
challenges/masks; the deployed result is `zeroKnowledge_closed` through `jointHVZKε_of_linkV`
(`Instance/Nondeg.lean`). (`hT₁`, `hT₂` ask the honest tables' claims at every mask, with no
`ClaimsND`.)

**Zero knowledge of the deployed proof in the random-permutation model, with the joint
model**: `zk_deployed_joint`'s statement with the deployed hashing over the random permutation.
For the deployed skeleton and a prover that is the joint model, every distinguisher of at most
`QD ≤ 2^127` queries of `π` and `π⁻¹`, the real game making at most `Q` permutation calls, tells
the real game from the simulated one (`simGameRpmD` with the joint simulator) with advantage at
most `εFS + 2^-165 + 2^-2200 + Q² / 2^508`. Remaining: `zk_deployed_joint`'s hypotheses (`hFS`
and the joint model's), and `hrow`, `hduplex`, `hQ`. -/
theorem zk_rpm_deployed_joint (stmtD : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19) (sh : Deployed.Shape)
    (hsh : sh = Deployed.deployedShape stmtD idW idσ idQ rowsW)
    (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) Inp Out Msg Tbl Pos)
    (εFS : ℝ≥0∞) (QD Q : ℕ) (hQD : QD ≤ 2 ^ 127)
    (hFS : Deployed.FSFresh P (Deployed.skel sh) []
      εFS)
    (h3 : finrank K E = 3) (P₀ : Params E) (hE : P₀.Exact) (stmt : Fin P₀.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P₀.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22) (h40₁ : 40 ≤ Fintype.card ι₁) (h40₂ : 40 ≤ Fintype.card ι₂)
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P₀ gK van c → ∀ m, S₁.claims c (T₁ c m) = cl₁ c (redMsgs P₀ gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P₀ gK van c → ∀ m, S₂.claims c (T₂ c m) = cl₂ c (redMsgs P₀ gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P₀ gK van c → ∀ v, S₁.claims c (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P₀ gK van c → ∀ v, S₂.claims c (simT₂ c v) = cl₂ c v)
    (lk : Link P P₀ gK van wir T₁ T₂ S₁ S₂)
    (hch : lk.chOf <$> uniformList Out P.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw)))
    (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m)
    (hduplex : DuplexDiscipline P
      (Deployed.skel sh))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost
      (zkGameRpmD P (Deployed.skel sh) D s)
      permutationCallCost Q) :
    Close (realGameRpmD P (Deployed.skel sh) D)
      (simGameRpmD P (fun σ => lk.out σ <$> jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
        (Deployed.skel sh) D)
      (εFS + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹ + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) :=
  zk_rpm_deployed_bits stmtD idW idσ idQ rowsW hrows sh hsh P _ _ εFS (1 / 2 ^ 165) QD Q hQD hFS
    (jointHVZK_of_link P h3 P₀ hE stmt gK van hvan hsat hvan0 hq hK hN hdeg inK hinK sigmaAt hsig
      wir S₁ S₂ hS₁ hS₂ T₁ T₂ cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂ lk hch)
    (factors_single hS₁ hS₂ h3 hK h40₁ h40₂ lk) (factors_pair hS₁ hS₂ h3 hK h40₁ h40₂ lk)
    hrow hduplex D hD hQ

end Joint

end QuotientZk.DRpm
