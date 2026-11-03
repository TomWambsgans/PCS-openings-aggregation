-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Lemmas.Push
import RecStatement.Lemmas.Public

/-!
# The verifier's checks and claims are `RecPiop`'s state after `ρ`

`PI2.md` §2 steps 6–7: the verifier at `t` (`CoreSpec.run`) requires one value nonzero,
`all = S_d Y · w_{m+2} · D`, and leaves its claims: `Q`'s combination `(1 + ρ')h(t) + ρ'q(t) = X/(S_d Y)`, the sum
`Σ_V h = T`, the setup's `ξ = κ(t) + βσ(t)` and `W`'s fold. Under `SpecOf` (its constants are `RecPiop`'s circuit's on
a Cantor basis):

* **the one inversion carries the two nonzero conditions** (`all_ne_zero_iff`): `all ≠ 0` exactly when `t ∉ V_{m+2}`
  (`w_{m+2}(t) ≠ 0`), `c_h + c_q ≠ 0` (the identity's combination is defined) and every public denominator is nonzero
  (`RecPiop.PubOK`);
* there, `ρ' = c_q/(c_h + c_q)` and `X/(S_d Y) = ((1 + 1_S) d_push + d_pull)/(c_h + c_q)` (`run_rhoQ`,
  `run_combination`: the pushes' sum and the holes by `push_side`, `Z_V(t) = w_m`), and `T` is `RecPiop`'s target
  (`run_target`, `publicSide_eq`);
* **`checks_claims_iff`**: the verifier's check passes and its claims hold at the true values `h(t), q(t), Σ_V h,
  κ(t), σ(t)` and `W`'s true fold, exactly when `t ∉ V_{m+2}`, `c_h + c_q ≠ 0`, and `RecPiop`'s state after `ρ` holds:
  `PubOK`, `SumOK`, the setup's claim, `QClaim` (`RecPiop.Circuit.qClaim_iff_normalised`: the normalised form is the
  multiplied-out identity at `t`) and the fold; **`checks_claims_iff_post2`** is the same with `RecPiop.Post2` itself,
  for any tables' model;
* the claims' points for the tables' layer: `u_l = w_l/(1 + w_l)` (`run_u`) and `Π_l (1 + w_l)^{-1} = t/w_{m+2}`
  (`run_digitsScale`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

section Main

variable {n : ℕ} {S : CoreSpec F} {G : RecPiop.Circuit F} {B : QuotientSecurity.CantorBasis F n}
  {pairOf : ℕ → Block × ℕ} {portOf : ℕ → ℕ} {nz : ℕ} {pubOf : List F → ℕ → List F}

/-- The run's digit `w_l`. -/
theorem run_digit (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) {l : ℕ} (hl : l ≤ G.logN + 2) :
    (S.run inp).digits.getD l 0 = QuotientSecurity.sq^[l] inp.t := by
  show (digitsList inp.t (S.logN + 3)).getD l 0 = _
  exact digitsList_getD inp.t (by rw [hS.logN]; omega)

/-- **The one value the verifier requires nonzero**: `all = S_d · Y · w_{m+2} · D`. -/
theorem run_all (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) :
    (S.run inp).all = (S.run inp).sDen * (S.run inp).y * QuotientSecurity.sq^[G.logN + 2] inp.t *
      (S.run inp).publicDen := by
  rw [← run_digit hS inp le_rfl, ← hS.logN]
  rfl

/-- The public denominator `D = Π_j d_pub(j)`. -/
theorem run_publicDen (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) :
    (S.run inp).publicDen = ∏ j ∈ range G.nP, G.dPub (Heap.omega B) (pubOf inp.scalars) inp.α inp.β inp.γ j :=
  (publicSide_eq hS inp.scalars inp.α inp.β inp.γ).1

/-- `D ≠ 0` is `PubOK`. -/
theorem run_publicDen_ne_zero_iff (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) :
    (S.run inp).publicDen ≠ 0 ↔ ∀ j < G.nP, G.dPub (Heap.omega B) (pubOf inp.scalars) inp.α inp.β inp.γ j ≠ 0 := by
  rw [run_publicDen hS inp, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_range]

/-- The cells' `v`, the pull's denominator. -/
theorem run_dPull (hS : SpecOf S G B pairOf portOf nz pubOf) (hV : G.Valid) (inp : Inputs F) :
    dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t = (S.run inp).dPull := by
  unfold dPullAt
  rw [← run_cells hS hV inp (Nat.two_pow_pos _)]
  rfl

/-- **The identity's coefficients at `t`** (outside `V_m`): `d_push = D_n/B` and `c_h + c_q = Y/B`. -/
theorem run_push (hS : SpecOf S G B pairOf portOf nz pubOf) (hV : G.Valid) (inp : Inputs F)
    (ht : QuotientSecurity.sq^[G.logN] inp.t ≠ 0) :
    G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α inp.γ inp.t =
        (S.run inp).dNum / (S.run inp).den ∧
      dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t *
          G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α
            inp.γ inp.t + (G.zV (Heap.omega B)).eval inp.t = (S.run inp).y / (S.run inp).den := by
  obtain ⟨hden, -, hsum, -⟩ := push_side hS hV inp ht
  have hv0 := run_cells hS hV inp (x := 0) (Nat.two_pow_pos _)
  have hwm := run_digit hS inp (l := G.logN) (by omega)
  have hdp : G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α
      inp.γ inp.t = (S.run inp).dNum / (S.run inp).den := by
    unfold Circuit.dPushAt
    rw [hsum]
    have e : (S.run inp).dNum = (inp.α + (S.run inp).cells.getD 0 0 + inp.ξ) * (S.run inp).den +
        (S.run inp).digits.getD S.logN 0 * (S.run inp).num := rfl
    rw [e, hv0, hS.logN, hwm]
    field_simp
    ring
  refine ⟨hdp, ?_⟩
  rw [hdp, run_dPull hS hV inp, Circuit.zV_eval_eq G B hS.hn]
  have e : (S.run inp).y = (S.run inp).dPull * (S.run inp).dNum + (S.run inp).digits.getD S.logN 0 * (S.run inp).den :=
    rfl
  rw [e, hS.logN, hwm]
  field_simp

/-- **The one inversion carries the two nonzero conditions**: `all ≠ 0` iff `t ∉ V_{m+2}`, `c_h + c_q ≠ 0` and the
public denominators are nonzero. -/
theorem all_ne_zero_iff (hS : SpecOf S G B pairOf portOf nz pubOf) (hV : G.Valid) (inp : Inputs F) :
    (S.run inp).all ≠ 0 ↔
      QuotientSecurity.sq^[G.logN + 2] inp.t ≠ 0 ∧
        dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t *
            G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α
              inp.γ inp.t + (G.zV (Heap.omega B)).eval inp.t ≠ 0 ∧
        ∀ j < G.nP, G.dPub (Heap.omega B) (pubOf inp.scalars) inp.α inp.β inp.γ j ≠ 0 := by
  rw [run_all hS inp, ← run_publicDen_ne_zero_iff hS inp]
  constructor
  · intro h
    have hT : QuotientSecurity.sq^[G.logN + 2] inp.t ≠ 0 := fun h0 ↦ h (by rw [h0]; ring)
    have hm : QuotientSecurity.sq^[G.logN] inp.t ≠ 0 := digit_ne_zero_of_le (by omega) hT
    obtain ⟨hden, -, -, -⟩ := push_side hS hV inp hm
    refine ⟨hT, ?_, fun h0 ↦ h (by rw [h0]; ring)⟩
    rw [(run_push hS hV inp hm).2]
    exact div_ne_zero (fun h0 ↦ h (by rw [h0]; ring)) hden
  · rintro ⟨hT, hY, hP⟩
    have hm : QuotientSecurity.sq^[G.logN] inp.t ≠ 0 := digit_ne_zero_of_le (by omega) hT
    obtain ⟨hden, hsden, -, -⟩ := push_side hS hV inp hm
    rw [(run_push hS hV inp hm).2] at hY
    have hy : (S.run inp).y ≠ 0 := fun h0 ↦ hY (by rw [h0, zero_div])
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hsden hy) hT) hP

/-- Where `all ≠ 0`: `1/(S_d Y)`. -/
theorem run_invP1 (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).invP1 = ((S.run inp).sDen * (S.run inp).y)⁻¹ := by
  have e : (S.run inp).invP1 = (S.run inp).all⁻¹ * (S.run inp).publicDen *
      (S.run inp).digits.getD (S.logN + 2) 0 := rfl
  have ha := run_all hS inp
  rw [e, hS.logN, run_digit hS inp le_rfl, ha]
  rw [ha] at h
  have h1 : (S.run inp).publicDen ≠ 0 := right_ne_zero_of_mul h
  have h2 : QuotientSecurity.sq^[G.logN + 2] inp.t ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  field_simp

/-- **`ρ' = c_q/(c_h + c_q)`**, where `all ≠ 0`. -/
theorem run_rhoQ (hS : SpecOf S G B pairOf portOf nz pubOf) (hV : G.Valid) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).rhoQ = (G.zV (Heap.omega B)).eval inp.t /
      (dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t *
        G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α inp.γ
          inp.t + (G.zV (Heap.omega B)).eval inp.t) := by
  obtain ⟨hT, -, -⟩ := (all_ne_zero_iff hS hV inp).mp h
  have hm : QuotientSecurity.sq^[G.logN] inp.t ≠ 0 := digit_ne_zero_of_le (by omega) hT
  obtain ⟨hden, hsden, -, -⟩ := push_side hS hV inp hm
  have hy : (S.run inp).y ≠ 0 := by
    rw [run_all hS inp] at h; exact right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  rw [(run_push hS hV inp hm).2, Circuit.zV_eval_eq G B hS.hn]
  have e : (S.run inp).rhoQ = (S.run inp).digits.getD S.logN 0 * (S.run inp).den * (S.run inp).sDen *
      (S.run inp).invP1 := rfl
  rw [e, run_invP1 hS inp h, hS.logN, run_digit hS inp (l := G.logN) (by omega)]
  field_simp

/-- **`X/(S_d Y) = ((1 + 1_S) d_push + d_pull)/(c_h + c_q)`**, where `all ≠ 0`. -/
theorem run_combination (hS : SpecOf S G B pairOf portOf nz pubOf) (hV : G.Valid) (inp : Inputs F)
    (h : (S.run inp).all ≠ 0) :
    (S.run inp).combination =
      ((1 + (G.holePoly (Heap.omega B)).eval inp.t) *
          G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α inp.γ
            inp.t + dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t) /
        (dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t *
          G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α inp.γ
            inp.t + (G.zV (Heap.omega B)).eval inp.t) := by
  obtain ⟨hT, -, -⟩ := (all_ne_zero_iff hS hV inp).mp h
  have hm : QuotientSecurity.sq^[G.logN] inp.t ≠ 0 := digit_ne_zero_of_le (by omega) hT
  obtain ⟨hden, hsden, -, hhole⟩ := push_side hS hV inp hm
  have hy : (S.run inp).y ≠ 0 := by
    rw [run_all hS inp] at h; exact right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  obtain ⟨hdp, hY⟩ := run_push hS hV inp hm
  rw [hY, hdp, hhole, run_dPull hS hV inp]
  have e : (S.run inp).combination = (S.run inp).x * (S.run inp).invP1 := rfl
  have ex : (S.run inp).x = ((S.run inp).sDen + (S.run inp).digits.getD S.logN 0 * (S.run inp).sNum) *
      (S.run inp).dNum + (S.run inp).dPull * (S.run inp).den * (S.run inp).sDen := rfl
  rw [e, run_invP1 hS inp h, ex, hS.logN, run_digit hS inp (l := G.logN) (by omega)]
  field_simp

/-- **`T` is `RecPiop`'s target**, where `all ≠ 0`. -/
theorem run_target (hS : SpecOf S G B pairOf portOf nz pubOf) (hV : G.Valid) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).target = G.target (Heap.omega B) (pubOf inp.scalars) inp.α inp.β inp.γ := by
  obtain ⟨-, -, hP⟩ := (all_ne_zero_iff hS hV inp).mp h
  have hpn := (publicSide_eq hS inp.scalars inp.α inp.β inp.γ).2 hP
  have e : (S.run inp).target = (S.run inp).publicNum * (S.run inp).all⁻¹ * (S.run inp).p2 := rfl
  have ep2 : (S.run inp).all = (S.run inp).p2 * (S.run inp).publicDen := rfl
  have hD : (S.run inp).publicDen ≠ 0 := right_ne_zero_of_mul (ep2 ▸ h)
  have hp2 : (S.run inp).p2 ≠ 0 := left_ne_zero_of_mul (ep2 ▸ h)
  have hpn' : (S.run inp).publicNum = (S.run inp).publicDen * G.target (Heap.omega B) (pubOf inp.scalars) inp.α inp.β
      inp.γ := hpn
  rw [e, ep2, hpn']
  field_simp

/-- **W's fold is `foldAt`.** -/
theorem run_fold (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) :
    (S.run inp).fold = foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ := by
  show foldW ((List.range S.logRow).map fun l ↦ sqIter inp.ρ l) S.logRow inp.a = _
  rw [hS.logRow]
  exact foldW_eq_foldAt inp.ρ _ G.logW inp.a fun l hl ↦ by
    simp [List.getD_eq_getElem?_getD, hl, sqIter_eq]

/-- **The verifier's check passes and its claims hold, at the true values, iff `t ∉ V_{m+2}`, `c_h + c_q ≠ 0` and
`RecPiop`'s state after `ρ` holds** (`PubOK`, `SumOK`, the setup's claim, `QClaim`, the fold). -/
theorem checks_claims_iff (hS : SpecOf S G B pairOf portOf nz pubOf) (hV : G.Valid) (inp : Inputs F)
    (ht qt sumH κt σt foldTrue : F) :
    ((S.run inp).all ≠ 0 ∧ (S.run inp).combination = (1 + (S.run inp).rhoQ) * ht + (S.run inp).rhoQ * qt ∧
        (S.run inp).target = sumH ∧ inp.ξ = κt + inp.β * σt ∧ (S.run inp).fold = foldTrue) ↔
      (QuotientSecurity.sq^[G.logN + 2] inp.t ≠ 0 ∧
        dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t *
            G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α
              inp.γ inp.t + (G.zV (Heap.omega B)).eval inp.t ≠ 0 ∧
        (∀ j < G.nP, G.dPub (Heap.omega B) (pubOf inp.scalars) inp.α inp.β inp.γ j ≠ 0) ∧
        sumH = G.target (Heap.omega B) (pubOf inp.scalars) inp.α inp.β inp.γ ∧
        inp.ξ = κt + inp.β * σt ∧
        G.QClaim (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α inp.β
          inp.γ inp.t ht qt ∧
        foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ = foldTrue) := by
  constructor
  · rintro ⟨h0, hc, htg, hξ, hf⟩
    obtain ⟨hT, hY, hP⟩ := (all_ne_zero_iff hS hV inp).mp h0
    refine ⟨hT, hY, hP, by rw [← htg, run_target hS hV inp h0], hξ, ?_, by rw [← hf, run_fold hS inp]⟩
    rw [Circuit.qClaim_iff_normalised _ _ _ _ _ _ _ _ hY, ← run_rhoQ hS hV inp h0, ← run_combination hS hV inp h0]
    exact hc.symm
  · rintro ⟨hT, hY, hP, hsum, hξ, hq, hf⟩
    have h0 : (S.run inp).all ≠ 0 := (all_ne_zero_iff hS hV inp).mpr ⟨hT, hY, hP⟩
    refine ⟨h0, ?_, by rw [hsum, run_target hS hV inp h0], hξ, by rw [← hf, run_fold hS inp]⟩
    rw [Circuit.qClaim_iff_normalised _ _ _ _ _ _ _ _ hY, ← run_rhoQ hS hV inp h0,
      ← run_combination hS hV inp h0] at hq
    exact hq.symm

/-- **The same with `RecPiop.Post2`**, for any tables' model `Mo` (its `h`, `q`, the setup's `σ`, `κ`, `W`'s true
fold values), the statement `s` with the public limbs `pubOf` of the public scalars, the fold values `a` (`2^r` of
them) and `ξ` the round's message. -/
theorem checks_claims_iff_post2 {St M : Type} (hS : SpecOf S G B pairOf portOf nz pubOf) (hV : G.Valid)
    (inp : Inputs F) (Mo : Model G (Heap.omega B) M) (pubOf' : St → ℕ → List F) (s : St)
    (hpub : pubOf' s = pubOf inp.scalars) (cW cQ : M) (ha : inp.a.length = 2 ^ G.logW) :
    ((S.run inp).all ≠ 0 ∧
        (S.run inp).combination = (1 + (S.run inp).rhoQ) * (Mo.hP cQ).eval inp.t +
          (S.run inp).rhoQ * (Mo.qP cQ).eval inp.t ∧
        (S.run inp).target = ∑ i ∈ range G.N, (Mo.hP cQ).eval (Heap.omega B i) ∧
        inp.ξ = Mo.setup.κP.eval inp.t + inp.β * Mo.setup.σP.eval inp.t ∧
        (S.run inp).fold = foldAt G.logW (Mo.fold cW inp.t) inp.ρ) ↔
      (QuotientSecurity.sq^[G.logN + 2] inp.t ≠ 0 ∧
        dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t *
            G.dPushAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.α
              inp.γ inp.t + (G.zV (Heap.omega B)).eval inp.t ≠ 0 ∧
        Post2 G (Heap.omega B) Mo pubOf' s cW [inp.α, inp.β, inp.γ] cQ [inp.t] (inp.a ++ [inp.ξ]) [inp.ρ]) := by
  rw [checks_claims_iff hS hV inp]
  have hfv : ∀ k < 2 ^ G.logW, foldVals (inp.a ++ [inp.ξ]) k = inp.a.getD k 0 := by
    intro k hk
    unfold foldVals
    rw [List.getD_append _ _ _ _ (by omega)]
  have hxi : xiOf G.logW (inp.a ++ [inp.ξ]) = inp.ξ := by
    unfold xiOf
    rw [List.getD_append_right _ _ _ _ (by omega), ha, Nat.sub_self]
    rfl
  have hcells : cellsOf G.logW (Heap.omega B) (foldVals (inp.a ++ [inp.ξ])) inp.t =
      cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t :=
    funext fun x ↦ cellsOf_congr G.logW (Heap.omega B) hfv inp.t x
  have hfold : foldAt G.logW (foldVals (inp.a ++ [inp.ξ])) inp.ρ = foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ :=
    Finset.sum_congr rfl fun k hk ↦ by rw [hfv k (Finset.mem_range.mp hk)]
  unfold Post2 PubOK SumOK abc
  simp only [List.getD_cons_zero, List.getD_cons_succ, hxi, hcells, hfold, hpub]

/-! ## The claims' points, for the tables' layer -/

/-- **The digits' inverses**, where `all ≠ 0`: `1/w_l` for `l ≤ m + 2`. -/
theorem run_wInvs (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) {l : ℕ}
    (hl : l ≤ G.logN + 2) : (S.run inp).wInvs.getD l 0 = (QuotientSecurity.sq^[l] inp.t)⁻¹ := by
  have ha := run_all hS inp
  have hT : QuotientSecurity.sq^[G.logN + 2] inp.t ≠ 0 := by
    rw [ha] at h; exact right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have htop : (S.run inp).invTop = ((S.run inp).digits.getD (S.logN + 2) 0)⁻¹ := by
    have e : (S.run inp).invTop = (S.run inp).all⁻¹ * (S.run inp).publicDen * (S.run inp).p1 := rfl
    have ep : (S.run inp).all = (S.run inp).p1 * (S.run inp).digits.getD (S.logN + 2) 0 * (S.run inp).publicDen := rfl
    rw [ep] at h
    rw [e, ep]
    have h1 : (S.run inp).p1 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h)
    have h2 : (S.run inp).publicDen ≠ 0 := right_ne_zero_of_mul h
    have h3 : (S.run inp).digits.getD (S.logN + 2) 0 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
    field_simp
  have e : (S.run inp).wInvs = wInvsList (S.run inp).digits (S.logN + 2) (S.run inp).invTop := rfl
  rw [e, htop, hS.logN,
    wInvsList_getD inp.t (S.run inp).digits (fun l hl ↦ run_digit hS inp hl) hT hl, run_digit hS inp hl]

/-- **`u_l = w_l/(1 + w_l)`** (`Q`'s point in the novel basis), where `all ≠ 0`. -/
theorem run_u (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) {l : ℕ}
    (hl : l < G.logN + 2) :
    (S.run inp).uList.getD l 0 = QuotientSecurity.sq^[l] inp.t / (1 + QuotientSecurity.sq^[l] inp.t) := by
  have ha := run_all hS inp
  have hT : QuotientSecurity.sq^[G.logN + 2] inp.t ≠ 0 := by
    rw [ha] at h; exact right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have e : (S.run inp).uList = (List.range (S.logN + 2)).map fun l ↦
      1 + (S.run inp).wInvs.getD l 0 + (S.run inp).wInvs.getD (l + 1) 0 := rfl
  have hl' : l < S.logN + 2 := by rw [hS.logN]; exact hl
  rw [e]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl', Option.map_some,
    Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, run_wInvs hS inp h hl.le,
    run_wInvs hS inp h (by omega : l + 1 ≤ G.logN + 2), Function.iterate_succ_apply', sq_eq_mul]
  have h0 : QuotientSecurity.sq^[l] inp.t ≠ 0 := digit_ne_zero_of_le (by omega) hT
  have h1 : 1 + QuotientSecurity.sq^[l] inp.t ≠ 0 := by
    have := digit_ne_zero_of_le (l := l + 1) (by omega) hT
    rw [Function.iterate_succ_apply', sq_eq_mul] at this
    exact right_ne_zero_of_mul this
  field_simp
  ring_nf
  rw [CharTwo.two_eq_zero]
  ring

/-- **`t/w_{m+2} = Π_{l<m+2} (1 + w_l)^{-1}`** (the scale of `Q`'s value), where `all ≠ 0`. -/
theorem run_digitsScale (hS : SpecOf S G B pairOf portOf nz pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).digitsScale = ∏ l ∈ range (G.logN + 2), (1 + QuotientSecurity.sq^[l] inp.t)⁻¹ := by
  have ha := run_all hS inp
  have hT : QuotientSecurity.sq^[G.logN + 2] inp.t ≠ 0 := by
    rw [ha] at h; exact right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have e : (S.run inp).digitsScale = inp.t * (S.run inp).wInvs.getD (S.logN + 2) 0 := rfl
  rw [e, hS.logN, run_wInvs hS inp h le_rfl]
  have key : ∀ L ≤ G.logN + 2, inp.t * (QuotientSecurity.sq^[L] inp.t)⁻¹ =
      ∏ l ∈ range L, (1 + QuotientSecurity.sq^[l] inp.t)⁻¹ := by
    intro L hL
    induction L with
    | zero =>
      have : inp.t ≠ 0 := digit_ne_zero_of_le (l := 0) (by omega) hT
      simp [this]
    | succ L ih =>
      rw [Finset.prod_range_succ, ← ih (by omega), Function.iterate_succ_apply', sq_eq_mul, mul_inv, ← mul_assoc]
  exact key _ le_rfl

end Main

end RecStatement
