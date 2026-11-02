-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.Fresh

/-!
# Zero knowledge of the deployed proof, the joint model instantiated

**`zk_rpm_deployed_instance`**: `zk_rpm_deployed_jointV_fs'` (`JointV.lean`) for the deployed
prover `ofBytes (Pb …)` (`Prover.lean`), its openings `openW`, `openQ` (`Openings.lean`), its
challenges `chOf` (`Challenges.lean`), every hypothesis on them discharged:

* `SecretOpening.Conditions` (`conditionsW`, `conditionsQ`), the link `LinkV` (`link`), `hch`
  (`chOf_uniform`), the lanes `h40` (`card_ιW`, `card_ιQ`);
* `FSFresh`'s conditions (`Fresh.lean`): `hcw_deployed`, `hrow₀_Pb`, `hlong_Pb`, `hcK_Pb`, `claimsAt_W`,
  `claimsAt_σ`, `claimsAt_Q`, `hn_Pb`; `hrow` and `hduplex` by `ofBytes` (`RpmDiscipline.lean`);
* the simulator's tables (`hsimT`): `solveW`, `solveQ` choose a table with the verifier's claimed
  values (`valsW`, `valsQ`) when one exists, and the joint model's claims `cl` are the chosen
  table's, so `hsimT` holds by definition and `hT` follows from the honest table meeting the
  verifier's values (`hTW`, `hTQ`).

**What remains a hypothesis.** The field (`[E : K] = 3`, `|E| = 2^192`, `|K| = 2^64`, characteristic
2, `K`'s 64-bit words and `E`'s limbs `rep`, `1, Y, Y²` independent); F1's (`hE`, `hvan`, `hsat`: the
witness satisfies the relation, `hvan0`, `hN`, `hdeg`) and the simulator's public functions (`hinK`,
`hsig`), as in `zk_rpm_deployed_joint`; **the honest tables meet the verifier's claims**
(`hTW`, `hTQ`: the completeness of the claim maps for the tables `TW`, `TQ` the prover lays on its
stacks, proved for the deployed tables in `formal/Completeness`, a package built against mumbai that
this one cannot import); the permutation budget `hQ`. The statement holds for every renderer `R`
of the messages (WHIR's honest prover is one) and every pair of tables `TW`, `TQ` meeting the
claims.

The simulator `jointSimV … (chOf σ)`, read through `out`, uses `solveW`, `solveQ` (a classical
choice: noncomputable) and no witness.
-/

open OracleComp OracleSpec Polynomial Module QuotientSecurity QuotientSecurity.Hiding QuotientRpm
open QuotientZk.Joint QuotientZk.Deployed.Fresh Common
open QuotientZk.Deployed (Inp Out Msg Item Tbl Pos KSt Proof)
open scoped ENNReal

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

/-! ## The simulator's tables -/

section Solve

variable {K E Ch ι Y Q O : Type} [Field K] [Field E] [Algebra K E]
  [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q] [DecidableEq Q]

/-- **A table with given claims**, chosen when one exists (`0` otherwise). -/
noncomputable def solve (S : SecretOpening K E Ch ι Y Q O) (c : Ch) (val : Fin S.m → E) :
    ι → Y → K :=
  open Classical in if h : ∃ d, S.claims c d = val then h.choose else 0

theorem claims_solve (S : SecretOpening K E Ch ι Y Q O) (c : Ch) (val : Fin S.m → E)
    {d : ι → Y → K} (hd : S.claims c d = val) : S.claims c (solve S c val) = val := by
  classical
  have h : ∃ d, S.claims c d = val := ⟨d, hd⟩
  unfold solve
  rw [dif_pos h]
  exact h.choose_spec

end Solve

section Main

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
  [CharP K 2] [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]
  [SampleableType E]
  (rep : Rep K E) (P₀ : Params E) (stmt : Fin P₀.words → E) (Y : E)

/-- The simulator's witness table: the verifier's claimed value. -/
noncomputable def simTW (c : DChal E) (v : Vals E) : ιW → YW → K :=
  solve (openW rep Y) (c, v) (valsW c v)

/-- The simulator's quotient table. -/
noncomputable def simTQ (c : DChal E) (v : Vals E) : ιQ → YQ → K :=
  solve (openQ rep P₀ Y) (c, v) (valsQ P₀ stmt Y c v)

/-- The joint model's claims: the simulator's tables'. -/
noncomputable def clW (c : DChal E) (v : Vals E) : Fin 1 → E :=
  (openW rep Y).claims (c, v) (simTW rep Y c v)

noncomputable def clQ (c : DChal E) (v : Vals E) : Fin 2 → E :=
  (openQ rep P₀ Y).claims (c, v) (simTQ rep P₀ stmt Y c v)

/-- **Zero knowledge of the deployed proof in the random-permutation model, the joint model
instantiated**: for the deployed skeleton at `2^22` rows and the deployed prover `ofBytes (Pb …)`
(every message renderer `R`, every pair of honest tables `TW`, `TQ` meeting the verifier's
claims), every distinguisher of at most `QD ≤ 2^127` queries of `π` and `π⁻¹`, the real game making
at most `Q` permutation calls, tells the real game from the simulated one with advantage at most
`2^-54 + 2^-165 + 2^-2200 + Q² / 2^508`. -/
theorem zk_rpm_deployed_instance (stmtD : Deployed.Statement) (idW idσ idQ : Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19) (sh : Deployed.Shape)
    (hsh : sh = Deployed.deployedShape stmtD idW idσ idQ rowsW)
    (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (R : Renderer K E)
    (QD Q : ℕ) (hQD : QD ≤ 2 ^ 127)
    (h3 : finrank K E = 3) (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64)
    (hY : LinearIndependent K ![1, Y, Y ^ 2])
    (hE : P₀.Exact) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hN : P₀.nCells = 2 ^ 24) (hdeg : van.natDegree ≤ 2 ^ 22)
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (hTW : ∀ c, good P₀ gK van c → ∀ m,
      (openW rep Y).claims (c, redMsgs P₀ gK van c.1.1.2 m) (TW m) =
        valsW c (redMsgs P₀ gK van c.1.1.2 m))
    (hTQ : ∀ c, good P₀ gK van c → ∀ m,
      (openQ rep P₀ Y).claims (c, redMsgs P₀ gK van c.1.1.2 m) (TQ c.1.1.1 m) =
        valsQ P₀ stmt Y c (redMsgs P₀ gK van c.1.1.2 m))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost
      (DRpm.zkGameRpmD (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)) (Deployed.skel sh) D s)
      permutationCallCost Q) :
    Close (DRpm.realGameRpmD (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)) (Deployed.skel sh) D)
      (DRpm.simGameRpmD (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R))
        (fun σ => out rep P₀ gK van stmt Y TW TQ R σ <$> jointSimV inK sigmaAt (fun _ => ())
          (openW rep Y) (openQ rep P₀ Y) (simTW rep Y) (simTQ rep P₀ stmt Y) (chOf rep.limbs σ))
        (Deployed.skel sh) D)
      (((2 : ℝ≥0∞) ^ 54)⁻¹ + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹ + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) :=
  zk_rpm_deployed_jointV_fs' stmtD idW idσ idQ rowsW hrows sh hsh
    (Pb rep P₀ gK van stmt Y TW TQ R) QD Q hQD (cwD rep) (hcw_deployed rep hq)
    (hrow₀_Pb rep P₀ gK van stmt Y TW TQ h3 hK R) (hlong_Pb rep P₀ gK van stmt Y TW TQ R)
    (hcK_Pb rep P₀ gK van stmt Y TW TQ R) (claimsAt_W rep P₀ gK van stmt Y TW TQ R)
    (claimsAt_σ rep P₀ gK van stmt Y TW TQ R) (claimsAt_Q rep P₀ gK van stmt Y TW TQ R)
    (hn_Pb rep P₀ gK van stmt Y TW TQ R) h3 P₀ hE stmt gK van hvan hsat hvan0 hq hK hN hdeg
    (by rw [card_ιW]) (by rw [card_ιQ]; norm_num) inK hinK sigmaAt hsig (fun _ => ())
    (openW rep Y) (openQ rep P₀ Y) (conditionsW rep h3 hY) (conditionsQ rep P₀ h3 hY) (T₁ TW)
    (T₂ TQ) (clW rep Y) (clQ rep P₀ stmt Y)
    (fun c hc m => (hTW c hc m).trans (claims_solve _ _ _ (hTW c hc m)).symm)
    (fun c hc m => (hTQ c hc m).trans (claims_solve _ _ _ (hTQ c hc m)).symm)
    (simTW rep Y) (simTQ rep P₀ stmt Y) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (link rep P₀ gK van stmt Y TW TQ R) (chOf_uniform rep.limbs) D hD hQ

end Main

end QuotientZk.Instance

/-! ## Axioms -/

/--
info: 'QuotientZk.Instance.zk_rpm_deployed_jointV_fs'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.Instance.zk_rpm_deployed_jointV_fs'

/-- info: 'QuotientZk.Instance.chOf_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.Instance.chOf_uniform

/-- info: 'QuotientZk.Instance.conditionsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.Instance.conditionsW

/-- info: 'QuotientZk.Instance.conditionsQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.Instance.conditionsQ

/-- info: 'QuotientZk.Instance.view_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.Instance.view_eq

/-- info: 'QuotientZk.Instance.hrow₀_Pb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.Instance.hrow₀_Pb

/-- info: 'QuotientZk.Instance.hcw_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.Instance.hcw_deployed

/--
info: 'QuotientZk.Instance.zk_rpm_deployed_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.Instance.zk_rpm_deployed_instance
