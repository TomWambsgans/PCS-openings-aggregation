-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The tables' model is `Tables.lean`'s (`pi2Model`,
-- `pi2Tables`' claims, read backwards), the verifier's arithmetic `formal/RecStatement`'s (`checks_claims_iff_post2`),
-- the rounds' states `formal/RecPiop`'s (`Post2`, `qClaim_iff`, `dPushAt_eq`).
import RecCompose.Pi2HonestMain

/-!
# π2's honest prover: the claims hold and the check passes

* **`pi2_honest_post2`**: off `BadCopy`, the honest stacks reach `RecPiop.Post2` (the identity is zero, `Σ_V h` is the
  target, `ξ` is the setup's value, the fold values are `W`'s true ones);
* **`claims_of_model`**: the verifier's check and the model's values give π2's four claims on the stacks (the tables'
  layer, `pi2Tables`' `claims`, read backwards);
* **`pi2_honest`**: off `BadCopy` and `BadT`, `all ≠ 0` and `Pi2ClaimsHold` at the honest inputs.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

variable {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (hcol : Pi2SetupColumns D C)
  (roots : RecSetupRoots)

theorem length_foldValues (m r : ℕ) (T : Array K) (t : E) : (foldValues m r T t).length = 2 ^ r := by
  simp [foldValues]

/-- **The honest stacks reach the state after `ρ`**, off `BadCopy`. -/
theorem pi2_honest_post2 (w : ℕ → K) (scalars : List E) (α β γ t ρ : E)
    (hw : (C.G roots).Satisfies (Fa.pubOf roots scalars) (RecCircuit.emb w))
    (hbad : ¬ BadCopy (C.G roots) w (Fa.pubOf roots scalars) α β γ) :
    RecPiop.Post2 (C.G roots) pi2Omega (pi2Model Fa roots hcol) (fun _ : Unit ↦ Fa.pubOf roots scalars) ()
      (honestW (C.G roots) w) [α, β, γ] (honestQ (C.G roots) w α β γ) [t]
      ((honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).a ++
        [(honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).ξ]) [ρ] := by
  have hV := Fa.valid roots
  have h24 := logN_G Fa roots
  have h4 := Fa.logW roots
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  have hpull : ∀ i < (C.G roots).N, ¬ (C.G roots).IsHole i →
      RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0 := fun i hi hh h0 ↦ hbad (Or.inl ⟨i, hi, hh, h0⟩)
  have hpush : ∀ i < (C.G roots).N, (C.G roots).dPush pi2Omega (RecCircuit.emb w) α β γ i ≠ 0 :=
    fun i hi h0 ↦ hbad (Or.inr (Or.inl ⟨i, hi, h0⟩))
  have hpub : ∀ j < (C.G roots).nP, (C.G roots).dPub pi2Omega (Fa.pubOf roots scalars) α β γ j ≠ 0 :=
    fun j hj h0 ↦ hbad (Or.inr (Or.inr ⟨j, hj, h0⟩))
  have hW := modelW_eq Fa hcol roots w
  have hσ := modelSigma_eq Fa hcol roots
  have hκ := modelKappa_eq Fa hcol roots
  have hH := modelH_eq Fa hcol roots w α β γ
  have hQ := modelQ_eq Fa hcol roots w α β γ
  have hwv : ∀ j < (C.G roots).N, ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)).eval (pi2Omega j) =
      RecCircuit.emb w j := fun j hj ↦ by rw [hW]; exact witnessPoly_omega _ w (by omega) hj
  have hhv : ∀ i < (C.G roots).N, ((pi2Model Fa roots hcol).hP (honestQ (C.G roots) w α β γ)).eval (pi2Omega i) =
      (hValues (C.G roots) w α β γ).getD i 0 := fun i hi ↦ by rw [hH]; exact hNovel_omega _ w α β γ (by omega) hi
  have hq : (pi2Model Fa roots hcol).qP (honestQ (C.G roots) w α β γ) =
      numPoly (pi2Model Fa roots hcol).setup ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w))
        ((pi2Model Fa roots hcol).hP (honestQ (C.G roots) w α β γ)) α β γ /ₘ (C.G roots).zV pi2Omega := by
    rw [hQ]
    exact novP_qNovel hV (by omega) w α β γ _ _ _ hW hσ hκ hH hwv hhv hpull hpush
  have hid : (C.G roots).idPoly pi2Omega (pi2Model Fa roots hcol).setup
      ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)) ((pi2Model Fa roots hcol).hP (honestQ (C.G roots) w α β γ))
      ((pi2Model Fa roots hcol).qP (honestQ (C.G roots) w α β γ)) α β γ = 0 := by
    rw [hq]
    exact idPoly_qHonest hV (by omega) _ w hwv α β γ hhv hpull hpush
  have hla := length_foldValues (C.G roots).logN (C.G roots).logW (wTableB (C.G roots) w) t
  have hfv : ∀ k < 2 ^ (C.G roots).logW,
      RecPiop.foldVals ((honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).a ++
        [(honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).ξ]) k =
        (pi2Model Fa roots hcol).fold (honestW (C.G roots) w) t k := by
    intro k hk
    unfold RecPiop.foldVals honestInputs
    simp only
    rw [List.getD_append _ _ _ _ (by rw [hla]; exact hk)]
    exact foldValues_eq Fa hcol roots w t hk
  have hxi : RecPiop.xiOf (C.G roots).logW
      ((honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).a ++
        [(honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).ξ]) =
      (pi2Model Fa roots hcol).setup.κP.eval t + β * (pi2Model Fa roots hcol).setup.σP.eval t := by
    unfold RecPiop.xiOf honestInputs
    simp only
    rw [List.getD_append_right _ _ _ _ (by rw [hla]), hla, Nat.sub_self, List.getD_cons_zero]
    exact xiOf_eq Fa hcol roots β t
  unfold RecPiop.Post2 RecPiop.PubOK RecPiop.SumOK RecPiop.abc
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨hpub, ?_, hxi, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun i hi ↦ hhv i (mem_range.mp hi)]
    exact sum_hValues hV w hw α β γ
  · refine (RecPiop.Circuit.qClaim_iff hV hpts (pi2Model Fa roots hcol).setup
      ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)) _ _ α β γ t _ (fun x hx ↦ ?_) hxi).mpr ?_
    · rw [RecPiop.cellsOf_congr _ _ hfv t x]
      exact (pi2Model Fa roots hcol).cells_fold _ t x hx
    · rw [hid, Polynomial.eval_zero]
  · unfold RecPiop.foldAt
    exact Finset.sum_congr rfl fun k hk ↦ by rw [hfv k (mem_range.mp hk)]

/-- **The verifier's check and the model's values give π2's four claims** on the stacks (`pi2Tables`' `claims`, read
backwards). -/
theorem claims_of_model (inp : Inputs E) (cW cQ : Stk)
    (hall : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).all ≠ 0)
    (hc : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).combination =
      (1 + ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).rhoQ) *
          ((pi2Model Fa roots hcol).hP cQ).eval inp.t +
        ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).rhoQ * ((pi2Model Fa roots hcol).qP cQ).eval inp.t)
    (htg : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).target =
      ∑ i ∈ range (C.G roots).N, ((pi2Model Fa roots hcol).hP cQ).eval (pi2Omega i))
    (hξ : inp.ξ = (pi2Model Fa roots hcol).setup.κP.eval inp.t + inp.β * (pi2Model Fa roots hcol).setup.σP.eval inp.t)
    (hf : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).fold =
      RecPiop.foldAt (C.G roots).logW ((pi2Model Fa roots hcol).fold cW inp.t) inp.ρ) :
    Pi2ClaimsHold D roots inp cW cQ := by
  have hS := Fa.spec roots
  have hm := view_logN Fa roots
  have hm24 := view_logN24 Fa roots
  have hr4 := view_logRow4 Fa roots
  set m := (D.circuitAt roots.pi1).circuit.logN with hmdef
  set S := (Spec.of (D.circuitAt roots.pi1).circuit).core with hSdef
  have hSm : S.logN = m := spec_core_logN _
  have hSr : S.logRow = (D.circuitAt roots.pi1).circuit.logRow := spec_core_logRow _
  have hm20 : 20 ≤ m := by omega
  have hT : QuotientSecurity.sq^[(C.G roots).logN + 2] inp.t ≠ 0 := by
    have h := hall
    rw [run_all hS inp] at h
    exact right_ne_zero_of_mul (left_ne_zero_of_mul h)
  rw [← hm] at hT
  have hw : ∀ l < m + 2, 1 + QuotientSecurity.sq^[l] inp.t ≠ 0 := fun l hl ↦ one_add_digit_ne_zero hT hl
  have huw : ∀ l < m + 2, (S.run inp).uList.getD l 0 =
      QuotientSecurity.sq^[l] inp.t / (1 + QuotientSecurity.sq^[l] inp.t) := fun l hl ↦
    run_u hS inp hall (by rw [← hm]; exact hl)
  have hu : (S.run inp).uList.length = m + 2 := by rw [run_uList_length, hSm]
  have hD : (S.run inp).digitsScale = ∏ l ∈ range (m + 2), (1 + QuotientSecurity.sq^[l] inp.t)⁻¹ := by
    rw [run_digitsScale hS inp hall, ← hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `W`'s claim
    unfold ClaimOn
    have hv : (layoutsOf m).1.vars = m := rfl
    rw [hv, run_witnessPoint, hSm, hSr, claim_wFold (by omega) _ inp.t inp.ρ, hf]
    have e : (C.G roots).logW = (D.circuitAt roots.pi1).circuit.logRow := (view_logRow Fa roots).symm
    rw [e]
    rfl
  · -- `Q`'s first claim
    unfold ClaimOn
    have hv : (layoutsOf m).2.1.vars = m + 5 := rfl
    rw [hv, run_quotientPoint, run_quotientValue, spec_core_y0, spec_core_y1, spec_core_scale]
    have hcq := claim_quotient (qZero hm20 cQ) hu hw huw (S.run inp).rhoQ
    unfold qTable at hcq
    rw [hcq, hD, hc]
    show _ = _ * _ * ((1 + _) * (hPoly (qTable m cQ) m).eval inp.t + _ * (qPoly (qTable m cQ) m).eval inp.t)
    unfold hPoly qPoly qTable
    rw [novP_eval_sq, novP_eval_sq]
  · -- `Q`'s second claim
    unfold ClaimOn
    have hv : (layoutsOf m).2.1.vars = m + 5 := rfl
    rw [hv, run_sumPoint, run_sumValue, spec_core_y0, spec_core_y1, spec_core_scale, hSm]
    have hcs := claim_sum (qZero hm20 cQ)
    unfold qTable at hcs
    rw [hcs, htg, ← pow_view_N Fa roots]
    show _ = _ * ∑ i ∈ range (2 ^ m), (hPoly (qTable m cQ) m).eval (pi2Omega i)
    unfold hPoly
    rw [sum_novP_omega (by omega)]
    rfl
  · -- the setup's claim
    unfold ClaimOn
    have hv : (layoutsOf m).2.2.vars = m + 1 := rfl
    rw [hv, run_setupPoint, hSm, claim_setup]
    have hlane : max (m + 1) minCertifiedStack - PcsQuotient.laneFold ≤ m := by
      simp only [minCertifiedStack, PcsQuotient.laneFold]; omega
    have hT0 : ∀ k < 2 ^ m, (layoutsOf m).2.2.readEntry (fun j ↦ (D.circuitAt roots.pi1).setupStack.getD j 0) k =
        (kappaB D roots).getD k 0 := fun k hk ↦ by
      rw [setupLayout_eq hm20, readEntry_ofChunks_two hlane _ (by rw [pow_succ]; omega)]
      exact (setupStack_getD _ hk).1
    have hT1 : ∀ k < 2 ^ m, (layoutsOf m).2.2.readEntry (fun j ↦ (D.circuitAt roots.pi1).setupStack.getD j 0) k +
        (layoutsOf m).2.2.readEntry (fun j ↦ (D.circuitAt roots.pi1).setupStack.getD j 0) (k + 2 ^ m) =
        (sigmaB D roots).getD k 0 := fun k hk ↦ by
      rw [hT0 k hk, setupLayout_eq hm20, readEntry_ofChunks_two hlane _ (by rw [pow_succ]; omega),
        (setupStack_getD _ hk).2]
      show (kappaB D roots).getD k 0 + ((kappaB D roots).getD k 0 + (sigmaB D roots).getD k 0) = _
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [wPoly_congr hT0, wPoly_congr hT1, hξ]
    rfl

include hcol in
/-- **π2's honest prover: the verifier's check passes and its four claims hold**, off the bad challenges. -/
theorem pi2_honest (w : ℕ → K) (scalars : List E) (α β γ t ρ : E)
    (hw : (C.G roots).Satisfies (Fa.pubOf roots scalars) (RecCircuit.emb w))
    (hbad : ¬ BadCopy (C.G roots) w (Fa.pubOf roots scalars) α β γ) (ht : ¬ BadT (C.G roots) w α β γ t) :
    ((Spec.of (D.circuitAt roots.pi1).circuit).core.run
        (honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ)).all ≠ 0 ∧
      Pi2ClaimsHold D roots (honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ)
        (honestW (C.G roots) w) (honestQ (C.G roots) w α β γ) := by
  have hV := Fa.valid roots
  have h24 := logN_G Fa roots
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  set inp := honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ with hinp
  have hpost := pi2_honest_post2 Fa hcol roots w scalars α β γ t ρ hw hbad
  have ha : inp.a.length = 2 ^ (C.G roots).logW := length_foldValues _ _ _ _
  have hT : QuotientSecurity.sq^[(C.G roots).logN + 2] inp.t ≠ 0 := fun h ↦ ht (Or.inl h)
  -- `c_h + c_q` at the verifier's cells is the polynomials' at `t`
  have hW := modelW_eq Fa hcol roots w
  have hcells : ∀ x < (C.G roots).W, RecPiop.cellsOf (C.G roots).logW pi2Omega (fun k ↦ inp.a.getD k 0) inp.t x =
      ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)).eval (inp.t + pi2Omega x) := fun x hx ↦ by
    rw [RecPiop.cellsOf_congr _ _ (a := fun k ↦ inp.a.getD k 0)
      (a' := (pi2Model Fa roots hcol).fold (honestW (C.G roots) w) t)
      (fun k hk ↦ foldValues_eq Fa hcol roots w t hk) inp.t x]
    exact (pi2Model Fa roots hcol).cells_fold _ t x hx
  have hξ := xiOf_eq Fa hcol roots β t
  have hpushAt := RecPiop.Circuit.dPushAt_eq hV hpts (pi2Model Fa roots hcol).setup
    ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)) α β γ t inp.ξ hcells hξ
  have hpullAt : RecPiop.dPullAt (RecPiop.cellsOf (C.G roots).logW pi2Omega (fun k ↦ inp.a.getD k 0) inp.t) α β t =
      (RecPiop.dPullP ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)) α β).eval t := by
    unfold RecPiop.dPullAt RecPiop.dPullP
    rw [hcells 0 (Nat.two_pow_pos _), pi2Omega_zero, add_zero]
    show α + Polynomial.eval t _ + β * t = _
    simp
  have hY : RecPiop.dPullAt (RecPiop.cellsOf (C.G roots).logW pi2Omega (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β
        inp.t * (C.G roots).dPushAt pi2Omega (RecPiop.cellsOf (C.G roots).logW pi2Omega (fun k ↦ inp.a.getD k 0)
          inp.t) inp.ξ inp.α inp.γ inp.t + ((C.G roots).zV pi2Omega).eval inp.t ≠ 0 := by
    intro h0
    apply ht
    right
    show (RecPiop.dPullP (witnessPoly (C.G roots) w) α β *
        (Polynomial.C α + (C.G roots).pushPoly pi2Omega (kappaPoly (C.G roots)) (witnessPoly (C.G roots) w) γ +
          Polynomial.C β * sigmaPoly (C.G roots)) + (C.G roots).zV pi2Omega).eval t = 0
    rw [← hW, ← modelKappa_eq Fa hcol roots, ← modelSigma_eq Fa hcol roots]
    have e : (C.G roots).dPushP pi2Omega (pi2Model Fa roots hcol).setup
        ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)) α β γ =
        Polynomial.C α + (C.G roots).pushPoly pi2Omega (pi2Model Fa roots hcol).setup.κP
          ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)) γ +
            Polynomial.C β * (pi2Model Fa roots hcol).setup.σP := rfl
    rw [← e, Polynomial.eval_add, Polynomial.eval_mul, ← hpullAt, ← hpushAt]
    exact h0
  obtain ⟨hall, hc, htg, hξ', hf⟩ := (checks_claims_iff_post2 (Fa.spec roots) hV inp (pi2Model Fa roots hcol)
    (fun _ : Unit ↦ Fa.pubOf roots scalars) () rfl (honestW (C.G roots) w) (honestQ (C.G roots) w α β γ) ha).mpr
    ⟨hT, hY, hpost⟩
  exact ⟨hall, claims_of_model Fa hcol roots inp _ _ hall hc htg hξ' hf⟩

end RecCompose

/-- info: 'RecCompose.pi2_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2_honest
