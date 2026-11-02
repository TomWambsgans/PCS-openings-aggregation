-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Fresh
import QuotientZk.RpmJoint
import QuotientZk.RpmDiscipline

/-!
# The joint-model end statements with `FSFresh` discharged

`zk_deployed_joint` (`JointDeployed.lean`) and `zk_rpm_deployed_joint` (`RpmJoint.lean`) with their
remaining ZK hypothesis `FSFresh` replaced by `fsFresh_deployed_bits`'s conditions on the prover
(long rows, the witness table first with a first row of min-entropy `2^-2368`, claims reading a
challenge through windows of min-entropy `2^-191`, `242 ≤ P.n`):

* **`zk_deployed_joint_fs`**: `2^-54 + 2^-165 + 2^-2200` (random-oracle model, `|c₀| + QD ≤ 2^127`);
* **`zk_rpm_deployed_joint_fs`**: `2^-54 + 2^-165 + 2^-2200 + Q² / 2^508` (random-permutation
  model, an empty cache before the proof); **`zk_rpm_deployed_joint_fs'`**: the same with
  `RpmDiscipline.lean`'s `hrow` and `hduplex` discharged too (a prover `ofBytes Pb`).
-/

open OracleComp OracleSpec Polynomial Module QuotientSecurity QuotientSecurity.Hiding Common
open QuotientZk.Deployed.Fresh
open scoped ENNReal NNReal

namespace QuotientZk.Joint

section Fresh

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **Zero knowledge of the deployed proof with the joint model, `FSFresh` discharged**: for the
deployed skeleton and a prover that is the joint model and meets `fsFresh_deployed`'s conditions,
every distinguisher of at most `QD` queries (`|c₀| + QD ≤ 2^127`) has advantage at most
`2^-54 + 2^-165 + 2^-2200`. -/
theorem zk_deployed_joint_fs (stmtD : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) Deployed.Inp Deployed.Out Deployed.Msg Deployed.Tbl
      Deployed.Pos)
    (c₀ : List (Deployed.Inp × Deployed.Out)) (QD : ℕ) (hQ : c₀.length + QD ≤ 2 ^ 127)
    (cw : Fin 3 → QuotientRpm.Bytes32 → List UInt8)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Deployed.Out}[cw j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ (Rand K ι₁ Y₁ ι₂ Y₂)}[P.rowFn s [] 0 0 = y] ≤
      ((2 : ℝ≥0∞) ^ 2368)⁻¹)
    (hrowL : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0)) (hclσ : ClaimsAt P 128 3 (cw 1))
    (hclQ : ClaimsAt P 242 3 (cw 2)) (hn : 242 ≤ P.n)
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
    (hch : lk.chOf <$> uniformList Deployed.Out P.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw)))
    (D : Deployed.Proof → OracleComp (Deployed.Inp →ₒ Deployed.Out) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD) :
    Close (realGame P (Deployed.skel (Deployed.deployedShape stmtD idW idσ idQ rowsW)) c₀ D)
      (simGame P (fun σ => lk.out σ <$> jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
        (Deployed.skel (Deployed.deployedShape stmtD idW idσ idQ rowsW)) c₀ D)
      (((2 : ℝ≥0∞) ^ 54)⁻¹ + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹) :=
  zk_deployed_joint stmtD idW idσ idQ rowsW hrows P c₀ _ QD hQ
    (fsFresh_deployed_bits stmtD idW idσ idQ rowsW hrows P c₀ (by omega) cw hcw hrow₀ hrowL hcK
      hclW hclσ hclQ hn)
    h3 P₀ hE stmt gK van hvan hsat hvan0 hq hK hN hdeg h40₁ h40₂ inK hinK sigmaAt hsig wir S₁ S₂
    hS₁ hS₂ T₁ T₂ cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂ lk hch D hD

end Fresh

end QuotientZk.Joint

namespace QuotientZk.DRpm

open QuotientZk.Joint
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec Proof)

section Fresh

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **Zero knowledge of the deployed proof in the random-permutation model, with the joint model,
`FSFresh` discharged** (`fsFresh_deployed_bits` with an empty cache before the proof): advantage at
most `2^-54 + 2^-165 + 2^-2200 + Q² / 2^508`. -/
theorem zk_rpm_deployed_joint_fs (stmtD : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19) (sh : Deployed.Shape)
    (hsh : sh = Deployed.deployedShape stmtD idW idσ idQ rowsW)
    (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) Inp Out Msg Tbl Pos)
    (QD Q : ℕ) (hQD : QD ≤ 2 ^ 127)
    (cw : Fin 3 → QuotientRpm.Bytes32 → List UInt8)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ (Rand K ι₁ Y₁ ι₂ Y₂)}[P.rowFn s [] 0 0 = y] ≤
      ((2 : ℝ≥0∞) ^ 2368)⁻¹)
    (hrowL : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0)) (hclσ : ClaimsAt P 128 3 (cw 1))
    (hclQ : ClaimsAt P 242 3 (cw 2)) (hn : 242 ≤ P.n)
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
    (hduplex : DuplexDiscipline P (Deployed.skel sh))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost
      (zkGameRpmD P (Deployed.skel sh) D s)
      permutationCallCost Q) :
    Close (realGameRpmD P (Deployed.skel sh) D)
      (simGameRpmD P (fun σ => lk.out σ <$> jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
        (Deployed.skel sh) D)
      (((2 : ℝ≥0∞) ^ 54)⁻¹ + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹ + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) :=
  zk_rpm_deployed_joint stmtD idW idσ idQ rowsW hrows sh hsh P _ QD Q hQD
    (by rw [hsh]; exact (fsFresh_deployed_bits stmtD idW idσ idQ rowsW hrows P [] (Nat.zero_le _) cw
      hcw hrow₀ hrowL hcK hclW hclσ hclQ hn))
    h3 P₀ hE stmt gK van hvan hsat hvan0 hq hK hN hdeg h40₁ h40₂ inK hinK sigmaAt hsig wir S₁ S₂
    hS₁ hS₂ T₁ T₂ cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂ lk hch
    (fun s h k x => by obtain ⟨b, hb, -⟩ := hrowL s h k x; exact ⟨b, hb⟩) hduplex D hD hQ

/-- **`zk_rpm_deployed_joint'` with `FSFresh` discharged** (`RpmDiscipline.lean`: no `hrow`, no
`hduplex`): for a prover whose leaf rows are byte strings longer than 192 bytes (`ofBytes Pb`) and
that meets `fsFresh_deployed_bits`'s other conditions and is the joint model, advantage at most
`2^-54 + 2^-165 + 2^-2200 + Q² / 2^508`. -/
theorem zk_rpm_deployed_joint_fs' (stmtD : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19) (sh : Deployed.Shape)
    (hsh : sh = Deployed.deployedShape stmtD idW idσ idQ rowsW)
    (Pb : Proto (Rand K ι₁ Y₁ ι₂ Y₂) (List UInt8) Out Msg Tbl Pos)
    (QD Q : ℕ) (hQD : QD ≤ 2 ^ 127)
    (cw : Fin 3 → QuotientRpm.Bytes32 → List UInt8)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ (Rand K ι₁ Y₁ ι₂ Y₂)}[(ofBytes Pb).rowFn s [] 0 0 = y] ≤
      ((2 : ℝ≥0∞) ^ 2368)⁻¹)
    (hlong : ∀ s h k x, 192 < (Pb.rowFn s h k x).length) (hcK : Pb.cK 0 = 0)
    (hclW : ClaimsAt (ofBytes Pb) 5 4 (cw 0)) (hclσ : ClaimsAt (ofBytes Pb) 128 3 (cw 1))
    (hclQ : ClaimsAt (ofBytes Pb) 242 3 (cw 2)) (hn : 242 ≤ Pb.n)
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
    (lk : Link (ofBytes Pb) P₀ gK van wir T₁ T₂ S₁ S₂)
    (hch : lk.chOf <$> uniformList Out Pb.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw)))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpmD (ofBytes Pb) (Deployed.skel sh) D s)
      permutationCallCost Q) :
    Close (realGameRpmD (ofBytes Pb) (Deployed.skel sh) D)
      (simGameRpmD (ofBytes Pb)
        (fun σ => lk.out σ <$> jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
        (Deployed.skel sh) D)
      (((2 : ℝ≥0∞) ^ 54)⁻¹ + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹ + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) :=
  zk_rpm_deployed_joint' stmtD idW idσ idQ rowsW hrows sh hsh Pb _ QD Q hQD
    (by rw [hsh]; exact (fsFresh_deployed_bits stmtD idW idσ idQ rowsW hrows (ofBytes Pb) []
      (Nat.zero_le _) cw hcw hrow₀ (fun s h k x => ⟨_, rfl, hlong s h k x⟩) hcK hclW hclσ hclQ hn))
    h3 P₀ hE stmt gK van hvan hsat hvan0 hq hK hN hdeg h40₁ h40₂ inK hinK sigmaAt hsig wir S₁ S₂
    hS₁ hS₂ T₁ T₂ cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂ lk hch D hD hQ

end Fresh

end QuotientZk.DRpm
