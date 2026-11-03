-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The counting follows `formal/RecPiop`'s (`Copy.lean`:
-- `card_dPull_eq_zero_le`; `Identity.lean`: `card_eval_eq_zero_le`, the degrees).
import RecCompose.Pi2HonestThm

/-!
# π2's honest prover: how many challenges are bad

* **`card_badCopy_le`**: at most `2N |E|²` triples `(α, β, γ)` are in `BadCopy`: each of the `N − n_P` pulled
  denominators, the `N` pushes' and the `n_P` public ones is `α + f(γ) + β g(γ)`, zero at `|E|²` triples (`α` determined by
  `β, γ`, `card_den_zero_le`).
* **`card_badT_le`**: for a triple off `BadCopy` (and a circuit with a non-hole position), at most `8N` points `t` are in
  `BadT`: `V_{m+2}` has `4N` points (`w_{m+2}`, monic of degree `4N`), and `d_pull d_push + Z_V` is a nonzero polynomial
  (at a non-hole `ω_i` it is `d_pull(i) d_push(i) ≠ 0`) of degree at most `4N`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

/-- **A denominator `α + f(γ) + β g(γ)` is zero at `|E|²` triples.** -/
theorem card_den_zero_le (f g : E → E) :
    (univ.filter fun v : E × E × E ↦ v.1 + f v.2.2 + v.2.1 * g v.2.2 = 0).card ≤ Fintype.card E ^ 2 := by
  classical
  refine (Finset.card_le_card (t := univ.image fun p : E × E ↦ (f p.2 + p.1 * g p.2, p.1, p.2))
    fun v hv ↦ ?_).trans (Finset.card_image_le.trans (by simp [sq]))
  rw [Finset.mem_filter] at hv
  refine Finset.mem_image.mpr ⟨(v.2.1, v.2.2), Finset.mem_univ _, ?_⟩
  have : v.1 = f v.2.2 + v.2.1 * g v.2.2 := CharTwo.add_eq_zero.mp (by rw [← hv.2]; ring)
  rw [← this]

open Classical in
/-- **At most `2N |E|²` triples are bad for the copy argument.** -/
theorem card_badCopy_le (G : RecPiop.Circuit E) (hV : G.Valid) (w : ℕ → K) (pub : ℕ → List E) :
    (univ.filter fun v : E × E × E ↦ BadCopy G w pub v.1 v.2.1 v.2.2).card ≤ 2 * G.N * Fintype.card E ^ 2 := by
  classical
  set NH := (range G.N).filter fun i ↦ ¬ G.IsHole i with hNH
  have hsub : (univ.filter fun v : E × E × E ↦ BadCopy G w pub v.1 v.2.1 v.2.2) ⊆
      (NH.biUnion fun i ↦ univ.filter fun v : E × E × E ↦
          RecPiop.dPull pi2Omega (RecCircuit.emb w) v.1 v.2.1 i = 0) ∪
        ((range G.N).biUnion fun i ↦ univ.filter fun v : E × E × E ↦
          G.dPush pi2Omega (RecCircuit.emb w) v.1 v.2.1 v.2.2 i = 0) ∪
        ((range G.nP).biUnion fun j ↦ univ.filter fun v : E × E × E ↦
          G.dPub pi2Omega pub v.1 v.2.1 v.2.2 j = 0) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    simp only [mem_union, mem_biUnion, mem_range, mem_filter, mem_univ, true_and, hNH]
    rcases hv with ⟨i, hi, hh, h⟩ | ⟨i, hi, h⟩ | ⟨j, hj, h⟩
    · exact Or.inl (Or.inl ⟨i, ⟨hi, hh⟩, h⟩)
    · exact Or.inl (Or.inr ⟨i, hi, h⟩)
    · exact Or.inr ⟨j, hj, h⟩
  have e1 : ∀ i, (univ.filter fun v : E × E × E ↦ RecPiop.dPull pi2Omega (RecCircuit.emb w) v.1 v.2.1 i = 0).card ≤
      Fintype.card E ^ 2 := fun i ↦ card_den_zero_le (fun _ ↦ RecCircuit.emb w i) (fun _ ↦ pi2Omega i)
  have e2 : ∀ i, (univ.filter fun v : E × E × E ↦ G.dPush pi2Omega (RecCircuit.emb w) v.1 v.2.1 v.2.2 i = 0).card ≤
      Fintype.card E ^ 2 := fun i ↦
    card_den_zero_le (fun γ ↦ G.push (RecCircuit.emb w) γ i) (fun _ ↦ pi2Omega (G.sigma i))
  have e3 : ∀ j, (univ.filter fun v : E × E × E ↦ G.dPub pi2Omega pub v.1 v.2.1 v.2.2 j = 0).card ≤
      Fintype.card E ^ 2 := fun j ↦
    card_den_zero_le (fun γ ↦ G.pubFp γ pub j) (fun _ ↦ pi2Omega (G.N + j))
  have hcNH : NH.card + G.nP = G.N := by
    have h := Finset.card_filter_add_card_filter_not (s := range G.N) (G.IsHole)
    rw [RecPiop.Circuit.card_holes hV, card_range] at h
    rw [hNH]
    omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ NH.card * Fintype.card E ^ 2 + G.N * Fintype.card E ^ 2 + G.nP * Fintype.card E ^ 2 := by
        refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · exact card_biUnion_le.trans ((Finset.sum_le_sum fun i _ ↦ e1 i).trans (by rw [sum_const, smul_eq_mul]))
        · exact card_biUnion_le.trans ((Finset.sum_le_sum fun i _ ↦ e2 i).trans
            (by rw [sum_const, card_range, smul_eq_mul]))
        · exact card_biUnion_le.trans ((Finset.sum_le_sum fun j _ ↦ e3 j).trans
            (by rw [sum_const, card_range, smul_eq_mul]))
    _ = 2 * G.N * Fintype.card E ^ 2 := by
        rw [← hcNH]
        ring

/-! ## The bad points `t` -/

/-- The honest setup's polynomials (`sigmaPoly`, `kappaPoly`). -/
noncomputable def setupOfG (G : RecPiop.Circuit E) (hm : G.logN ≤ 28) : RecPiop.SetupPolys G pi2Omega where
  σP := sigmaPoly G
  κP := kappaPoly G
  σ_deg := UniComplete.AlgC.novP_natDegree_lt _ _
  κ_deg := UniComplete.AlgC.novP_natDegree_lt _ _
  σ_eval _ hi := sigmaPoly_omega G hm hi
  κ_eval _ hi := kappaPoly_omega G hm hi

open Classical in
/-- **At most `8N` points `t` are bad**, for a triple off `BadCopy` and a circuit with a non-hole position. -/
theorem card_badT_le (G : RecPiop.Circuit E) (hV : G.Valid) (hm : G.logN ≤ 28) (w : ℕ → K) (pub : ℕ → List E)
    (α β γ : E) (hbad : ¬ BadCopy G w pub α β γ) (hnh : ∃ i < G.N, ¬ G.IsHole i) :
    (univ.filter fun t ↦ BadT G w α β γ t).card ≤ 8 * G.N := by
  classical
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  have hN2 := RecPiop.Circuit.N_ge_two hV
  set S := setupOfG G hm with hS
  set P := RecPiop.dPullP (witnessPoly G w) α β * G.dPushP pi2Omega S (witnessPoly G w) α β γ + G.zV pi2Omega with hP
  have hsub : (univ.filter fun t ↦ BadT G w α β γ t) ⊆
      (univ.filter fun t ↦ (UniComplete.Domain.wP (G.logN + 2)).eval t = 0) ∪ univ.filter fun t ↦ P.eval t = 0 := by
    intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    simp only [mem_union, mem_filter, mem_univ, true_and]
    rcases ht with h | h
    · exact Or.inl (by rw [wP_eval_sq]; exact h)
    · exact Or.inr h
  -- `V_{m+2}`
  have hA : (univ.filter fun t ↦ (UniComplete.Domain.wP (G.logN + 2)).eval t = 0).card ≤ 4 * G.N := by
    refine (RecPiop.Circuit.card_eval_eq_zero_le _ (UniComplete.Domain.wP_monic _).ne_zero).trans ?_
    rw [UniComplete.Domain.wP_natDegree, pow_add]
    unfold RecPiop.Circuit.N
    omega
  -- `d_pull d_push + Z_V`
  have hwdeg : (witnessPoly G w).natDegree ≤ G.N - 1 := by
    have := UniComplete.AlgC.novP_natDegree_lt G.logN fun j ↦
      (UniComplete.novelOfValuesK G.logN (wValues G w)).getD j 0
    unfold witnessPoly
    unfold RecPiop.Circuit.N
    omega
  have hPne : P ≠ 0 := by
    obtain ⟨i, hi, hh⟩ := hnh
    intro h0
    have e := congrArg (Polynomial.eval (pi2Omega i)) h0
    have hwv : ∀ j < G.N, (witnessPoly G w).eval (pi2Omega j) = RecCircuit.emb w j :=
      fun j hj ↦ witnessPoly_omega G w hm hj
    rw [hP, Polynomial.eval_add, Polynomial.eval_mul, RecPiop.Circuit.zV_eval hi, add_zero,
      RecPiop.Circuit.dPullP_eval, RecPiop.Circuit.dPushP_eval hV hpts (by omega) S _ α β γ hi,
      Polynomial.eval_zero] at e
    have e1 : RecPiop.dPull pi2Omega (fun j ↦ (witnessPoly G w).eval (pi2Omega j)) α β i =
        RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i := by
      simp only [RecPiop.dPull, RecPiop.den, hwv i hi]
    have hpush' := G.push_congr_off_holes hV (w := fun j ↦ (witnessPoly G w).eval (pi2Omega j))
      (w' := RecCircuit.emb w) (fun j hj _ ↦ hwv j hj) γ hi
    have e2 : G.dPush pi2Omega (fun j ↦ (witnessPoly G w).eval (pi2Omega j)) α β γ i =
        G.dPush pi2Omega (RecCircuit.emb w) α β γ i := by
      simp only [RecPiop.Circuit.dPush, RecPiop.den, hpush']
    rw [e1, e2] at e
    rcases mul_eq_zero.mp e with h | h
    · exact hbad (Or.inl ⟨i, hi, hh, h⟩)
    · exact hbad (Or.inr (Or.inl ⟨i, hi, h⟩))
  have hPdeg : P.natDegree ≤ 4 * G.N := by
    have h1 := RecPiop.Circuit.natDegree_dPullP_le (D := G.N - 1) hwdeg (by omega) α β
    have h2 := RecPiop.Circuit.natDegree_dPushP_le hV S (wP := witnessPoly G w) (by omega) α β γ
    have h3 := RecPiop.Circuit.natDegree_zV_le (G := G) (ω := pi2Omega)
    have h12 := natDegree_mul_le_of_le h1 h2
    rw [hP]
    refine (natDegree_add_le _ _).trans (max_le (h12.trans ?_) (h3.trans (by omega)))
    generalize G.N = N at *
    omega
  have hB : (univ.filter fun t ↦ P.eval t = 0).card ≤ 4 * G.N :=
    (RecPiop.Circuit.card_eval_eq_zero_le _ hPne).trans hPdeg
  calc _ ≤ _ := card_le_card hsub
    _ ≤ 4 * G.N + 4 * G.N := (card_union_le _ _).trans (add_le_add hA hB)
    _ = 8 * G.N := by ring

end RecCompose

/-- info: 'RecCompose.card_badCopy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.card_badCopy_le

/-- info: 'RecCompose.card_badT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.card_badT_le
