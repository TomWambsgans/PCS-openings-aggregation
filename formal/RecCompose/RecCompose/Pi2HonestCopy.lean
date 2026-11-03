-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The polynomials are `formal/RecPiop`'s (`Identity.lean`:
-- `idPoly`, `idPoly_eval_omega`, `natDegree_idPoly_le`; `Ports.lean`: `push_port`).
import RecCompose.Pi2HonestBase

/-!
# π2's honest prover: the copy argument's sum and the identity

For a witness satisfying the circuit (`RecPiop.Circuit.Satisfies`) and the honest `h` on `V_m` (`hValues`):

* **`sum_hValues`** (`SumOK`): `Σ_V h` is the public target `Σ_j 1/(α + F_j + β ω_{N+j})`. The pulls of the non-holes
  and the pushes of the non-holes cancel (`σ` is a bijection of the non-holes, `w(σ_i) = P_i`, characteristic two); a
  hole's push is its port's public fingerprint to the tag `N + j` (`push_port`, `Satisfies.ports`). No denominator need be
  nonzero: a zero one is inverted to zero on both sides.
* **The identity**: with every pulled `d_pull` and every `d_push` on `V_m` nonzero, the identity without `q`
  (`numPoly`: `h d_pull d_push + (1 + 1_S) d_push + d_pull`) vanishes on `V_m` (`numPoly_eval_omega`), so
  `Z_V` divides it (`num_eq_zV_mul`) and **`q = numPoly /ₘ Z_V`** makes the identity zero (`idPoly_qHonest`), of degree
  below `4N` (`natDegree_qHonest_lt`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

variable {G : RecPiop.Circuit E}

/-! ## `h` on `V_m` -/

/-- **`h` at position `i`**: `[¬ hole]/d_pull(i) + 1/d_push(i)`. -/
theorem hValues_getD (w : ℕ → K) (α β γ : E) {i : ℕ} (hi : i < G.N) :
    (hValues G w α β γ).getD i 0 =
      (if G.IsHole i then 0 else (RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i)⁻¹) +
        (G.dPush pi2Omega (RecCircuit.emb w) α β γ i)⁻¹ := by
  unfold hValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, dite_true, Option.getD_some]
  unfold RecPiop.dPull RecPiop.Circuit.dPush RecPiop.den RecPiop.Circuit.IsHole
  rw [pi2Omega_eq, pi2Omega_eq]
  rfl

/-- **The copy argument's honest sum** (`SumOK`): `Σ_V h = T`. -/
theorem sum_hValues (hV : G.Valid) (w : ℕ → K) {pub : ℕ → List E} (hw : G.Satisfies pub (RecCircuit.emb w))
    (α β γ : E) : ∑ i ∈ range G.N, (hValues G w α β γ).getD i 0 = G.target pi2Omega pub α β γ := by
  set v := RecCircuit.emb w with hv
  rw [Finset.sum_congr rfl fun i hi ↦ hValues_getD w α β γ (mem_range.mp hi), sum_add_distrib]
  have hpull : ∑ i ∈ range G.N, (if G.IsHole i then 0 else (RecPiop.dPull pi2Omega v α β i)⁻¹) =
      ∑ i ∈ (range G.N).filter (fun i ↦ ¬ G.IsHole i), (RecPiop.dPull pi2Omega v α β i)⁻¹ := by
    rw [sum_filter]
    refine sum_congr rfl fun i _ ↦ ?_
    by_cases h : G.IsHole i <;> simp [h]
  have hsplit : ∑ i ∈ range G.N, (G.dPush pi2Omega v α β γ i)⁻¹ =
      ∑ i ∈ (range G.N).filter (fun i ↦ G.IsHole i), (G.dPush pi2Omega v α β γ i)⁻¹ +
        ∑ i ∈ (range G.N).filter (fun i ↦ ¬ G.IsHole i), (G.dPush pi2Omega v α β γ i)⁻¹ :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hNH : ∑ i ∈ (range G.N).filter (fun i ↦ ¬ G.IsHole i), (G.dPush pi2Omega v α β γ i)⁻¹ =
      ∑ j ∈ (range G.N).filter (fun i ↦ ¬ G.IsHole i), (RecPiop.dPull pi2Omega v α β j)⁻¹ := by
    refine Finset.sum_nbij G.sigma (fun a ha ↦ ?_) (fun a ha b hb hab ↦ ?_) (fun b hb ↦ ?_) (fun a ha ↦ ?_)
    · obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
      have := hV.sigma_inside a (mem_range.mp ha1) ha2
      exact mem_filter.mpr ⟨mem_range.mpr this.1, this.2⟩
    · exact hV.sigma_inj a (mem_range.mp (mem_filter.mp (Finset.mem_coe.mp ha)).1) b
        (mem_range.mp (mem_filter.mp (Finset.mem_coe.mp hb)).1) hab
    · obtain ⟨hb1, hb2⟩ := mem_filter.mp (Finset.mem_coe.mp hb)
      obtain ⟨i, hi, hσ⟩ := hV.sigma_onto b (mem_range.mp hb1) hb2
      refine ⟨i, Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr hi, fun hh ↦ ?_⟩), hσ⟩
      obtain ⟨j, hj, rfl⟩ := RecPiop.Circuit.exists_port_of_hole hV hi hh
      rw [hV.sigma_port j hj] at hσ
      have := mem_range.mp hb1
      omega
    · obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
      unfold RecPiop.Circuit.dPush RecPiop.dPull
      rw [hw.copy a (mem_range.mp ha1) ha2, G.push_gamma v ha2 γ 0]
  have hH : ∑ i ∈ (range G.N).filter (fun i ↦ G.IsHole i), (G.dPush pi2Omega v α β γ i)⁻¹ =
      G.target pi2Omega pub α β γ := by
    unfold RecPiop.Circuit.target
    symm
    refine Finset.sum_nbij G.port (fun j hj ↦ ?_) (fun a ha b hb hab ↦ ?_) (fun i hi ↦ ?_) (fun j hj ↦ ?_)
    · have := RecPiop.Circuit.port_lt hV (mem_range.mp hj)
      exact mem_filter.mpr ⟨mem_range.mpr this.1, this.2⟩
    · exact RecPiop.Circuit.port_inj hV (mem_range.mp (Finset.mem_coe.mp ha)) (mem_range.mp (Finset.mem_coe.mp hb))
        hab
    · obtain ⟨hi1, hi2⟩ := mem_filter.mp (Finset.mem_coe.mp hi)
      obtain ⟨j, hj, hji⟩ := RecPiop.Circuit.exists_port_of_hole hV (mem_range.mp hi1) hi2
      exact ⟨j, Finset.mem_coe.mpr (mem_range.mpr hj), hji⟩
    · have hj' := mem_range.mp hj
      unfold RecPiop.Circuit.dPub RecPiop.Circuit.dPush
      rw [hV.sigma_port j hj', RecPiop.Circuit.push_port hV hj', hw.ports j hj']
      rfl
  rw [hpull, hsplit, hH, hNH, add_comm, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-! ## The identity without `q` -/

/-- **The identity without `q`**: `h d_pull d_push + (1 + 1_S) d_push + d_pull`. -/
noncomputable def numPoly (S : RecPiop.SetupPolys G pi2Omega) (wP hP : E[X]) (α β γ : E) : E[X] :=
  G.idPoly pi2Omega S wP hP 0 α β γ

theorem idPoly_eq_num (S : RecPiop.SetupPolys G pi2Omega) (wP hP qP : E[X]) (α β γ : E) :
    G.idPoly pi2Omega S wP hP qP α β γ = numPoly S wP hP α β γ + qP * G.zV pi2Omega := by
  unfold numPoly RecPiop.Circuit.idPoly
  ring

section Char

variable {F : Type} [Field F] [CharP F 2]

theorem id_nonhole {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : (a⁻¹ + b⁻¹) * a * b + (1 + 0) * b + a = 0 := by
  have e : (a⁻¹ + b⁻¹) * a * b = b + a := by field_simp
  rw [e, add_zero, one_mul]
  calc b + a + b + a = (b + b) + (a + a) := by ring
    _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

theorem id_hole {a b : F} (hb : b ≠ 0) : (0 + b⁻¹) * a * b + (1 + 1) * b + a = 0 := by
  have e : (0 + b⁻¹) * a * b = a := by rw [zero_add, mul_comm b⁻¹ a, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  rw [e, CharTwo.add_self_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]

end Char

/-- **The identity without `q` vanishes on `V_m`**, the pulled `d_pull` and every `d_push` nonzero. -/
theorem numPoly_eval_omega (hV : G.Valid) (hn : G.logN ≤ 32) (S : RecPiop.SetupPolys G pi2Omega) {wP hP : E[X]}
    (w : ℕ → K) (hwP : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j) (α β γ : E)
    (hhP : ∀ i < G.N, hP.eval (pi2Omega i) = (hValues G w α β γ).getD i 0)
    (hpull : ∀ i < G.N, ¬ G.IsHole i → RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0)
    (hpush : ∀ i < G.N, G.dPush pi2Omega (RecCircuit.emb w) α β γ i ≠ 0) {i : ℕ} (hi : i < G.N) :
    (numPoly S wP hP α β γ).eval (pi2Omega i) = 0 := by
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  unfold numPoly
  rw [RecPiop.Circuit.idPoly_eval_omega hV hpts hn S wP hP 0 α β γ hi]
  have e1 : RecPiop.dPull pi2Omega (fun j ↦ wP.eval (pi2Omega j)) α β i =
      RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i := by
    simp only [RecPiop.dPull, RecPiop.den, hwP i hi]
  have e2 : G.dPush pi2Omega (fun j ↦ wP.eval (pi2Omega j)) α β γ i =
      G.dPush pi2Omega (RecCircuit.emb w) α β γ i := by
    have hpush' := G.push_congr_off_holes hV (w := fun j ↦ wP.eval (pi2Omega j)) (w' := RecCircuit.emb w)
      (fun j hj _ ↦ hwP j hj) γ hi
    simp only [RecPiop.Circuit.dPush, RecPiop.den, hpush']
  rw [e1, e2, hhP i hi, hValues_getD w α β γ hi]
  unfold RecPiop.Circuit.holeInd
  by_cases hh : G.IsHole i
  · simp only [hh, ite_true]
    exact id_hole (hpush i hi)
  · have ha := hpull i hi hh
    have hb := hpush i hi
    simp only [hh, ite_false]
    generalize RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i = a at ha ⊢
    generalize G.dPush pi2Omega (RecCircuit.emb w) α β γ i = b at hb ⊢
    have e : (a⁻¹ + b⁻¹) * a * b = b + a := by field_simp
    rw [e, add_zero, one_mul]
    calc b + a + b + a = (b + b) + (a + a) := by ring
      _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

theorem zV_monic : (G.zV pi2Omega).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

theorem natDegree_zV : (G.zV pi2Omega).natDegree = G.N := by
  unfold RecPiop.Circuit.zV
  rw [natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_add_C _]
  simp

theorem omega_injOn_N (hn : G.logN ≤ 32) : ∀ a < G.N, ∀ b < G.N, pi2Omega a = pi2Omega b → a = b := by
  have hN : G.N ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hn
  intro a ha b hb h
  exact (RecPiop.Points.ofCantor UniComplete.Domain.basisE).inj a (by omega) b (by omega) h

/-- **`Z_V` divides a polynomial vanishing on `V_m`.** -/
theorem num_eq_zV_mul (hn : G.logN ≤ 32) {p : E[X]} (hp : ∀ i < G.N, p.eval (pi2Omega i) = 0) :
    p = G.zV pi2Omega * (p /ₘ G.zV pi2Omega) := by
  have hmod : p %ₘ G.zV pi2Omega = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero ((range G.N).image pi2Omega) ?_ ?_
    · rw [card_image_of_injOn (fun a ha b hb hab ↦ omega_injOn_N hn a (mem_range.mp ha) b (mem_range.mp hb) hab),
        card_range]
      have := degree_modByMonic_lt p (zV_monic (G := G))
      rwa [degree_eq_natDegree (zV_monic (G := G)).ne_zero, natDegree_zV] at this
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      have e := congrArg (eval (pi2Omega i)) (modByMonic_add_div p (G.zV pi2Omega))
      rw [Polynomial.eval_add, Polynomial.eval_mul, RecPiop.Circuit.zV_eval (mem_range.mp hi), zero_mul, add_zero,
        hp i (mem_range.mp hi)] at e
      exact e
  have e := modByMonic_add_div p (G.zV pi2Omega)
  rw [hmod, zero_add] at e
  exact e.symm

/-- **The honest `q` makes the identity zero.** -/
theorem idPoly_qHonest (hV : G.Valid) (hn : G.logN ≤ 32) (S : RecPiop.SetupPolys G pi2Omega) {wP hP : E[X]}
    (w : ℕ → K) (hwP : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j) (α β γ : E)
    (hhP : ∀ i < G.N, hP.eval (pi2Omega i) = (hValues G w α β γ).getD i 0)
    (hpull : ∀ i < G.N, ¬ G.IsHole i → RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0)
    (hpush : ∀ i < G.N, G.dPush pi2Omega (RecCircuit.emb w) α β γ i ≠ 0) :
    G.idPoly pi2Omega S wP hP (numPoly S wP hP α β γ /ₘ G.zV pi2Omega) α β γ = 0 := by
  have h := num_eq_zV_mul hn fun i hi ↦ numPoly_eval_omega hV hn S w hwP α β γ hhP hpull hpush hi
  rw [idPoly_eq_num]
  set n := numPoly S wP hP α β γ
  nth_rewrite 1 [h]
  rw [mul_comm (n /ₘ G.zV pi2Omega)]
  exact CharTwo.add_self_eq_zero _

/-- **The honest `q` has degree below `4N`.** -/
theorem natDegree_qHonest_lt (hV : G.Valid) (S : RecPiop.SetupPolys G pi2Omega) {wP hP : E[X]}
    (hw : wP.natDegree < G.N) (hh : hP.natDegree < G.N) (α β γ : E) :
    (numPoly S wP hP α β γ /ₘ G.zV pi2Omega).natDegree < 4 * G.N := by
  rw [natDegree_divByMonic _ (zV_monic (G := G)), natDegree_zV]
  have h2 := RecPiop.Circuit.N_ge_two hV
  have := RecPiop.Circuit.natDegree_idPoly_le hV S hw hh (qP := 0) (by rw [natDegree_zero]; omega) α β γ
  unfold numPoly
  omega

end RecCompose

/-- info: 'RecCompose.sum_hValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.sum_hValues

/-- info: 'RecCompose.idPoly_qHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.idPoly_qHonest

/-- info: 'RecCompose.natDegree_qHonest_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.natDegree_qHonest_lt
