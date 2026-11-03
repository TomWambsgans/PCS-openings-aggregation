-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The tables' model is `Tables.lean`'s (`pi2Model`,
-- `claim_wFold`, `claim_quotient`, `claim_sum`, `claim_setup`), the verifier's arithmetic `formal/RecStatement`'s
-- (`checks_claims_iff_post2`), the rounds' states `formal/RecPiop`'s (`Post2`, `qClaim_iff`, `dPushAt_eq`).
import RecCompose.Pi2Honest

/-!
# π2's honest prover: the claims hold and the check passes (`pi2_honest`)

At a setup of the deployment (`Fa : Pi2Facts D C`, `hcol : Pi2SetupColumns D C`), the tables' model `pi2Model` of the
honest stacks is the honest prover's polynomials (`modelW_eq`, `modelSigma_eq`, `modelKappa_eq`, `modelH_eq`,
`modelQ_eq`), its state after `ρ` holds (`pi2_honest_post2`), and so **`pi2_honest`**: off `BadCopy` and `BadT`, the
verifier's one check passes and π2's four claims hold on the honest stacks (`claims_of_model`, the tables' layer's
link read backwards).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

variable {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (hcol : Pi2SetupColumns D C)
  (roots : RecSetupRoots)

theorem logN_G (Fa : Pi2Facts D C) (roots : RecSetupRoots) : (C.G roots).logN = 24 := Fa.logN roots

theorem wPoly_add (m : ℕ) (T T' : ℕ → K) : wPoly m (fun i ↦ T i + T' i) = wPoly m T + wPoly m T' := by
  unfold wPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [UniComplete.Domain.embed_add, C_add, add_mul]

/-! ## The model of the honest stacks -/

/-- **`W`'s model polynomial of the honest stack is the witness's.** -/
theorem modelW_eq (w : ℕ → K) :
    (pi2Model Fa roots hcol).wP (honestW (C.G roots) w) = witnessPoly (C.G roots) w := by
  have hm := view_logN Fa roots
  have h24 := logN_G Fa roots
  show wPoly (D.circuitAt roots.pi1).circuit.logN (wTab D roots (honestW (C.G roots) w)) = _
  have hT : ∀ i < 2 ^ (C.G roots).logN, wTab D roots (honestW (C.G roots) w) i = (wTableB (C.G roots) w).getD i 0 :=
    fun i hi ↦ by
      unfold wTab wLayout
      rw [hm]
      exact readW_honest (C.G roots) w (by omega) hi
  rw [hm, wPoly_congr hT]
  refine poly_eq_of_eval_eq (natDegree_wPoly_lt _ _) (UniComplete.AlgC.novP_natDegree_lt _ _) pi2Omega
    (omega_injOn_N (by omega)) fun i hi ↦ ?_
  unfold wTableB
  rw [wPoly_bCoefficients (by omega) _ (size_wValues _ w) hi, witnessPoly_omega _ w (by omega) hi]
  unfold wValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < (C.G roots).N from hi, dite_true, Option.getD_some]
  rfl

theorem modelSigma_eq : (pi2Model Fa roots hcol).setup.σP = sigmaPoly (C.G roots) := by
  have h24 := logN_G Fa roots
  refine poly_eq_of_eval_eq (pi2Model Fa roots hcol).setup.σ_deg (UniComplete.AlgC.novP_natDegree_lt _ _) pi2Omega
    (omega_injOn_N (by omega)) fun i hi ↦ ?_
  rw [(pi2Model Fa roots hcol).setup.σ_eval i hi, sigmaPoly_omega _ (by omega) hi]

theorem modelKappa_eq : (pi2Model Fa roots hcol).setup.κP = kappaPoly (C.G roots) := by
  have h24 := logN_G Fa roots
  refine poly_eq_of_eval_eq (pi2Model Fa roots hcol).setup.κ_deg (UniComplete.AlgC.novP_natDegree_lt _ _) pi2Omega
    (omega_injOn_N (by omega)) fun i hi ↦ ?_
  rw [(pi2Model Fa roots hcol).setup.κ_eval i hi, kappaPoly_omega _ (by omega) hi]

/-- **`h`'s model polynomial of the honest stack is the prover's.** -/
theorem modelH_eq (w : ℕ → K) (α β γ : E) :
    (pi2Model Fa roots hcol).hP (honestQ (C.G roots) w α β γ) =
      UniComplete.AlgC.novP (C.G roots).logN fun j ↦ (hNovel (C.G roots) w α β γ).getD j 0 := by
  have hm := view_logN Fa roots
  have h24 := logN_G Fa roots
  show hPoly (qTable (D.circuitAt roots.pi1).circuit.logN _) (D.circuitAt roots.pi1).circuit.logN = _
  rw [hm]
  unfold hPoly
  exact UniComplete.AlgC.novP_congr _ fun k hk ↦ qCoef_honest_h _ w α β γ (by omega) hk

/-- **`q`'s model polynomial of the honest stack is the prover's.** -/
theorem modelQ_eq (w : ℕ → K) (α β γ : E) :
    (pi2Model Fa roots hcol).qP (honestQ (C.G roots) w α β γ) =
      UniComplete.AlgC.novP ((C.G roots).logN + 2) fun j ↦ (qNovel (C.G roots) w α β γ).getD j 0 := by
  have hm := view_logN Fa roots
  have h24 := logN_G Fa roots
  show qPoly (qTable (D.circuitAt roots.pi1).circuit.logN _) (D.circuitAt roots.pi1).circuit.logN = _
  rw [hm]
  unfold qPoly
  exact UniComplete.AlgC.novP_congr _ fun k hk ↦ qCoef_honest_q _ w α β γ (by omega) hk

/-! ## `ξ` and the fold values -/

theorem digitsList_take_getD (t : E) {m l : ℕ} (hl : l < m) :
    ((digitsList t (m + 3)).take m).getD l 0 = QuotientSecurity.sq^[l] t := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hl, ← List.getD_eq_getElem?_getD,
    digitsList_getD t (by omega)]

/-- **A half of a `K` array's multilinear extension at the digits** is the basis-`B` polynomial of the half at `t`. -/
theorem mle_extract_eq (a : Array K) (off m : ℕ) (ha : off + 2 ^ m ≤ a.size) (t : E) :
    UniStatement.multilinearEval ((a.extract off (off + 2 ^ m)).toList.map ofK) ((digitsList t (m + 3)).take m) =
      (wPoly m fun i ↦ a.getD (off + i) 0).eval t := by
  have hlen : ((digitsList t (m + 3)).take m).length = m := by simp [digitsList]; omega
  have hs : ((a.extract off (off + 2 ^ m)).map ofK).size = 2 ^ ((digitsList t (m + 3)).take m).length := by
    rw [hlen, Array.size_map, Array.size_extract, Nat.min_eq_left ha]
    exact Nat.add_sub_cancel_left _ _
  have hA := UniComplete.AlgC.mle_eq_sum ((a.extract off (off + 2 ^ m)).map ofK) _ hs
  rw [Array.toList_map] at hA
  rw [hA, hlen, wPoly_eval]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := mem_range.mp hx
  congr 1
  · have hlt : x < min (off + 2 ^ m) a.size - off := by rw [Nat.min_eq_left ha]; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_extract, Array.getD_eq_getD_getElem?]
    simp only [hlt, ite_true]
    cases a[off + x]? <;> rfl
  · refine Finset.prod_congr rfl fun l hl ↦ ?_
    rw [digitsList_take_getD t (mem_range.mp hl)]

theorem size_setupStack (c : Pi2Circuit) : c.setupStack.size = 2 ^ c.circuit.logN + 2 ^ c.circuit.logN := by
  unfold Pi2Circuit.setupStack
  simp [UniComplete.AlgC.bCoefficients_size]

/-- **`ξ` from the setup's halves is `κ(t) + β σ(t)`** at the model's setup polynomials. -/
theorem xiOf_eq (β t : E) :
    xiOf (C.G roots).logN (D.circuitAt roots.pi1).setupStack β t =
      (pi2Model Fa roots hcol).setup.κP.eval t + β * (pi2Model Fa roots hcol).setup.σP.eval t := by
  have hm := view_logN Fa roots
  set c := D.circuitAt roots.pi1 with hc
  have hsz := size_setupStack c
  show _ = (wPoly c.circuit.logN fun i ↦ (kappaB D roots).getD i 0).eval t +
    β * (wPoly c.circuit.logN fun i ↦ (sigmaB D roots).getD i 0).eval t
  rw [← hm]
  unfold xiOf
  simp only
  rw [show 2 * 2 ^ c.circuit.logN = 2 ^ c.circuit.logN + 2 ^ c.circuit.logN by ring]
  have h0 := mle_extract_eq c.setupStack 0 c.circuit.logN (by omega) t
  rw [zero_add] at h0
  rw [h0, mle_extract_eq c.setupStack (2 ^ c.circuit.logN) c.circuit.logN (by omega) t]
  have hk : ∀ i < 2 ^ c.circuit.logN, c.setupStack.getD (0 + i) 0 = (kappaB D roots).getD i 0 := fun i hi ↦ by
    rw [zero_add]; exact (setupStack_getD c hi).1
  have hks : ∀ i < 2 ^ c.circuit.logN, c.setupStack.getD (2 ^ c.circuit.logN + i) 0 =
      (kappaB D roots).getD i 0 + (sigmaB D roots).getD i 0 := fun i hi ↦ by
    rw [Nat.add_comm]; exact (setupStack_getD c hi).2
  rw [wPoly_congr hk, wPoly_congr hks, wPoly_add, Polynomial.eval_add]
  rw [← add_assoc (Polynomial.eval t _), CharTwo.add_self_eq_zero, zero_add]

/-- **The prover's fold values are `W`'s true fold values** of the honest stack. -/
theorem foldValues_eq (w : ℕ → K) (t : E) {k : ℕ} (hk : k < 2 ^ (C.G roots).logW) :
    (foldValues (C.G roots).logN (C.G roots).logW (wTableB (C.G roots) w) t).getD k 0 =
      (pi2Model Fa roots hcol).fold (honestW (C.G roots) w) t k := by
  have hm := view_logN Fa roots
  have hr := view_logRow Fa roots
  have h24 := logN_G Fa roots
  have h4 := Fa.logW roots
  show _ = wFold (D.circuitAt roots.pi1).circuit.logN (D.circuitAt roots.pi1).circuit.logRow
    (wTab D roots (honestW (C.G roots) w)) t k
  rw [hm, hr]
  unfold foldValues wFold
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := mem_range.mp hj
  have hidx : k + 2 ^ (C.G roots).logW * j < 2 ^ (C.G roots).logN := by
    have : 2 ^ (C.G roots).logW * (j + 1) ≤ 2 ^ (C.G roots).logW * 2 ^ ((C.G roots).logN - (C.G roots).logW) :=
      Nat.mul_le_mul_left _ hj'
    rw [← pow_add, Nat.add_sub_cancel' (by omega)] at this
    nlinarith
  congr 1
  · unfold wTab wLayout
    rw [hm, readW_honest (C.G roots) w (by omega) hidx]
  · refine Finset.prod_congr rfl fun l hl ↦ ?_
    rw [digitsList_getD t (by have := mem_range.mp hl; omega)]

end RecCompose

/-- info: 'RecCompose.modelW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.modelW_eq

/-- info: 'RecCompose.xiOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.xiOf_eq

/-- info: 'RecCompose.foldValues_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.foldValues_eq
