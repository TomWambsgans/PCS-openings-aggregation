-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The polynomials are `formal/RecPiop`'s (`Identity.lean`:
-- `pushPoly`, `holePoly`, `formulaPoly`, `cellPoly`, `Role.value_eval`; `Indicator.lean`: `ind`).
import RecCompose.Pi2HonestCopy

/-!
# π2's honest prover: `q` on the extension coset is the honest `q`

The prover computes `q` pointwise on the coset `β_{m+2} + V_{m+2}` (`qValues`) and interpolates it there (`qNovel`).
Here, at a circuit valid on `2^m` positions (`m + 2 < 28`):

* **the pairs** as a list (`pairsList`): `G.pairs`' elements once each (`sum_pairs`, `sum_pairs_filter`);
* **the indicators**: the prover's `indFrom` from a pair's data is `RecPiop.Circuit.ind` at a point off `V_m`
  (`ind_eval_eq`: `Z_V = Π_{j ∉ p} · Π_{j ∈ p}`);
* **the coset values**: `onCoset` is the novel polynomial at the coset's points (`onCoset_getD`); the prover's push and
  holes' indicator are `pushPoly`'s and `holePoly`'s values there (`pushAtCoset_eq`, `holeAtCoset_eq`), so its `q`
  values are the identity without `q` over `Z_V` (`qValues_eq`);
* **`qNovel`'s polynomial is the honest `q`** (`novP_qNovel`: both of degree below `4N`, agreeing on the coset's `4N`
  points), where the identity without `q` vanishes on `V_m` (`numPoly_eval_omega`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

variable {G : RecPiop.Circuit E}

/-! ## The pairs as a list -/

theorem mem_pairsList {q : RecPiop.Block × ℕ} : q ∈ pairsList G ↔ q ∈ G.pairs := by
  rcases q with ⟨b, k⟩
  unfold pairsList RecPiop.Circuit.pairs
  simp [List.mem_product, and_assoc]

theorem pairsList_nodup : (pairsList G).Nodup :=
  ((List.nodup_dedup _).product List.nodup_range).filter _

theorem pairs_eq_toFinset : G.pairs = (pairsList G).toFinset :=
  Finset.ext fun q ↦ by rw [List.mem_toFinset, mem_pairsList]

theorem sum_pairs (f : RecPiop.Block × ℕ → E) : ∑ q ∈ G.pairs, f q = ((pairsList G).map f).sum := by
  rw [pairs_eq_toFinset, List.sum_toFinset _ pairsList_nodup]

theorem sum_pairs_filter (P : RecPiop.Block × ℕ → Bool) (f : RecPiop.Block × ℕ → E) :
    ∑ q ∈ G.pairs.filter (fun q ↦ P q = true), f q = (((pairsList G).filter P).map f).sum := by
  have : G.pairs.filter (fun q ↦ P q = true) = ((pairsList G).filter P).toFinset := Finset.ext fun q ↦ by
    rw [List.mem_toFinset, List.mem_filter, Finset.mem_filter, mem_pairsList]
  rw [this, List.sum_toFinset _ (pairsList_nodup.filter _)]

/-! ## The indicators -/

theorem iterate_sq_eq (m : ℕ) (x : E) : (fun y : E ↦ y * y + y)^[m] x = QuotientSecurity.sq^[m] x := rfl

theorem prod_filter_range (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → E) :
    (((List.range N).filter fun j ↦ decide (P j)).map f).prod = ∏ j ∈ (range N).filter P, f j := by
  rw [← List.prod_toFinset _ (List.nodup_range.filter _), List.toFinset_filter, List.toFinset_range]
  simp

/-- **The prover's indicator is the polynomial's**, at a point off `V_m`. -/
theorem ind_eval_eq (hn : G.logN ≤ 32) (q : RecPiop.Block × ℕ) {x : E} (hx : ∀ j < G.N, x ≠ pi2Omega j) :
    (G.ind pi2Omega q).eval x =
      indFrom G.logN (∏ j ∈ G.compl q, (UniStatement.pointE (G.pairBase q) + UniStatement.pointE j))
        ((List.range G.N).filter fun j ↦ decide (G.InPair q j)) x := by
  have hz : zvAt G.logN x = ∏ j ∈ range G.N, (x + pi2Omega j) := by
    unfold zvAt
    rw [iterate_sq_eq, ← RecPiop.Circuit.zV_eval_eq G UniComplete.Domain.basisE hn x]
    unfold RecPiop.Circuit.zV
    rw [Polynomial.eval_prod]
    simp
  have hsplit := Finset.prod_filter_not_mul_prod_filter (range G.N) (G.InPair q) (fun j ↦ x + pi2Omega j)
  have hpos : (((List.range G.N).filter fun j ↦ decide (G.InPair q j)).map fun j ↦ x + UniStatement.pointE j).prod =
      ∏ j ∈ (range G.N).filter (G.InPair q), (x + pi2Omega j) := by
    rw [prod_filter_range]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [pi2Omega_eq]
  have hne : ∏ j ∈ (range G.N).filter (G.InPair q), (x + pi2Omega j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj ↦ fun h ↦
      hx j (mem_range.mp (mem_filter.mp hj).1) (CharTwo.add_eq_zero.mp h)
  have hc : ∏ j ∈ G.compl q, (UniStatement.pointE (G.pairBase q) + UniStatement.pointE j) =
      ∏ j ∈ G.compl q, (pi2Omega (G.pairBase q) + pi2Omega j) :=
    Finset.prod_congr rfl fun j _ ↦ by rw [pi2Omega_eq, pi2Omega_eq]
  unfold indFrom RecPiop.Circuit.ind
  rw [hz, hpos, hc, ← hsplit, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  unfold RecPiop.Circuit.compl
  field_simp

/-! ## The coset values -/

theorem size_wNov (w : ℕ → K) : (UniComplete.novelOfValuesK G.logN (wValues G w)).size = 2 ^ G.logN := by
  simp [UniComplete.novelOfValuesK, Bridge.Ntt.coefficients_size, wValues, RecPiop.Circuit.N]

theorem size_sigmaNov : (UniComplete.novelOfValuesE G.logN (sigmaValues G)).size = 2 ^ G.logN := by
  simp [ UniComplete.novelOfValuesE, Bridge.Ntt.coefficients_size, sigmaValues, RecPiop.Circuit.N]

theorem size_kappaNov : (UniComplete.novelOfValuesE G.logN (kappaValues G)).size = 2 ^ G.logN := by
  simp [ UniComplete.novelOfValuesE, Bridge.Ntt.coefficients_size, kappaValues, RecPiop.Circuit.N]

theorem size_hValues (w : ℕ → K) (α β γ : E) : (hValues G w α β γ).size = 2 ^ G.logN := by
  simp [hValues, RecPiop.Circuit.N]

theorem size_hNovel (w : ℕ → K) (α β γ : E) : (hNovel G w α β γ).size = 2 ^ G.logN := by
  simp [hNovel, UniComplete.novelOfValuesE, Bridge.Ntt.coefficients_size, size_hValues]

/-- **`onCoset` is the novel polynomial at the coset's points.** -/
theorem onCoset_getD {m : ℕ} (hm : m + 2 ≤ 28) (c : Array E) (hc : c.size = 2 ^ m) {p : ℕ}
    (hp : p < 2 ^ (m + 2)) :
    (onCoset m c).getD p 0 = (UniComplete.AlgC.novP m fun j ↦ c.getD j 0).eval (cosetPoint m p) := by
  unfold onCoset
  rw [values_getD_novP hm _ _ Array.size_ofFn hp]
  unfold cosetPoint
  congr 1
  have hle : 2 ^ m ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [UniComplete.AlgC.novP_of_zero_above (b := m) (m + 2) _ (by omega) fun k hk1 hk2 ↦ by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hk2, dite_true, Option.getD_some]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl]
  refine UniComplete.AlgC.novP_congr m fun k hk ↦ ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show k < 2 ^ (m + 2) by omega, dite_true, Option.getD_some]

theorem cosetPoint_ne' {m p : ℕ} (hm : m + 2 < 28) (hp : p < 2 ^ (m + 2)) :
    ∀ j < 2 ^ m, cosetPoint m p ≠ pi2Omega j := fun _ hj ↦ cosetPoint_ne hm hp hj

/-- **The prover's push at a coset point is the push polynomial's value.** -/
theorem pushAtCoset_eq (hV : G.Valid) (hm : G.logN + 2 < 28) (κP wP : E[X]) (κD wD : Array E) (γ : E) {p : ℕ}
    (hp : p < 2 ^ (G.logN + 2))
    (hw : ∀ p' < 2 ^ (G.logN + 2), wD.getD p' 0 = wP.eval (cosetPoint G.logN p'))
    (hκ : κD.getD p 0 = κP.eval (cosetPoint G.logN p)) :
    pushAtCoset G (pairData G) G.logN wD κD γ p = (G.pushPoly pi2Omega κP wP γ).eval (cosetPoint G.logN p) := by
  have hn : G.logN ≤ 32 := by omega
  have hW : G.W ≤ 2 ^ (G.logN + 2) :=
    Nat.pow_le_pow_right (by norm_num) (by have := hV.logW_lt; omega)
  unfold pushAtCoset RecPiop.Circuit.pushPoly pairData
  rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_finsetSum, sum_pairs, List.map_map, hw p hp, hκ]
  congr 2
  refine congrArg List.sum (List.map_congr_left fun q hq ↦ ?_)
  have hq' := mem_pairsList.mp hq
  simp only [Function.comp, Polynomial.eval_mul, Polynomial.eval_add]
  rw [ind_eval_eq hn q (cosetPoint_ne' hm hp)]
  congr 1
  unfold RecPiop.Circuit.formulaPoly
  rw [RecPiop.Role.value_eval]
  refine congrArg (fun z ↦ z + Polynomial.eval (cosetPoint G.logN p) wP) ?_
  refine RecPiop.Role.value_congr _ γ (fun _ ↦ rfl) fun c hc ↦ ?_
  have hc' := RecPiop.Circuit.regionRole_reads_lt hV hq' hc
  have hk : q.2 < G.W := (RecPiop.Circuit.mem_pairs.mp hq').2.1
  have hkc : q.2 ^^^ c < G.W := Nat.xor_lt_two_pow hk hc'
  unfold RecPiop.cellPoly
  have hkc' : q.2 ^^^ c < 2 ^ (G.logN + 2) := lt_of_lt_of_le hkc hW
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, ← cosetPoint_xor hm hp hkc',
    hw (p ^^^ (q.2 ^^^ c)) (xor_lt_pow hp hkc')]

/-- **The prover's holes' indicator at a coset point is the polynomial's.** -/
theorem holeAtCoset_eq (hm : G.logN + 2 < 28) {p : ℕ} (hp : p < 2 ^ (G.logN + 2)) :
    holeAtCoset G (pairData G) G.logN p = (G.holePoly pi2Omega).eval (cosetPoint G.logN p) := by
  have hn : G.logN ≤ 32 := by omega
  unfold holeAtCoset RecPiop.Circuit.holePoly pairData
  rw [Polynomial.eval_finsetSum, sum_pairs_filter (fun q ↦ (G.regionRole q.1 q.2).isPort)]
  simp only [List.filter_map, List.map_map, Function.comp_def]
  refine congrArg List.sum (List.map_congr_left fun q _ ↦ ?_)
  rw [ind_eval_eq hn q (cosetPoint_ne' hm hp)]

/-- **The prover's `q` values are the identity without `q` over `Z_V`**, at the polynomials of its novel
coefficients. -/
theorem qValues_eq (hV : G.Valid) (hm : G.logN + 2 < 28) (w : ℕ → K) (α β γ : E)
    (S : RecPiop.SetupPolys G pi2Omega) (wP hP : E[X])
    (hwP : wP = UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesK G.logN (wValues G w)).getD j 0)
    (hσ : S.σP = UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (sigmaValues G)).getD j 0)
    (hκ : S.κP = UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (kappaValues G)).getD j 0)
    (hhP : hP = UniComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β γ).getD j 0) {p : ℕ}
    (hp : p < 2 ^ (G.logN + 2)) :
    (qValues G w α β γ).getD p 0 =
      (numPoly S wP hP α β γ).eval (cosetPoint G.logN p) * (zvAt G.logN (cosetPoint G.logN p))⁻¹ := by
  have hm' : G.logN + 2 ≤ 28 := by omega
  have hwD : ∀ p' < 2 ^ (G.logN + 2), (onCoset G.logN (UniComplete.novelOfValuesK G.logN (wValues G w))).getD p' 0 = wP.eval (cosetPoint G.logN p') :=
    fun p' hp' ↦ by rw [onCoset_getD hm' _ (size_wNov w) hp', hwP]
  have hσD : (onCoset G.logN (UniComplete.novelOfValuesE G.logN (sigmaValues G))).getD p 0 = S.σP.eval (cosetPoint G.logN p) := by
    rw [onCoset_getD hm' _ size_sigmaNov hp, hσ]
  have hκD : (onCoset G.logN (UniComplete.novelOfValuesE G.logN (kappaValues G))).getD p 0 = S.κP.eval (cosetPoint G.logN p) := by
    rw [onCoset_getD hm' _ size_kappaNov hp, hκ]
  have hhD : (onCoset G.logN (hNovel G w α β γ)).getD p 0 = hP.eval (cosetPoint G.logN p) := by
    rw [onCoset_getD hm' _ (size_hNovel w α β γ) hp, hhP]
  unfold qValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  rw [hwD p hp, hσD, hhD, pushAtCoset_eq hV hm S.κP wP _ _ γ hp hwD hκD, holeAtCoset_eq hm hp]
  unfold numPoly RecPiop.Circuit.idPoly RecPiop.Circuit.dPushP RecPiop.dPullP
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, zero_mul, add_zero]

/-! ## `q`'s novel coefficients -/

theorem size_qValues (w : ℕ → K) (α β γ : E) : (qValues G w α β γ).size = 2 ^ (G.logN + 2) := by
  simp [qValues]

/-- **`qNovel`'s polynomial is the honest `q`** `numPoly /ₘ Z_V`, where every pulled `d_pull` and every `d_push` on
`V_m` is nonzero. -/
theorem novP_qNovel (hV : G.Valid) (hm : G.logN + 2 < 28) (w : ℕ → K) (α β γ : E)
    (S : RecPiop.SetupPolys G pi2Omega) (wP hP : E[X])
    (hwP : wP = UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesK G.logN (wValues G w)).getD j 0)
    (hσ : S.σP = UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (sigmaValues G)).getD j 0)
    (hκ : S.κP = UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (kappaValues G)).getD j 0)
    (hhP : hP = UniComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β γ).getD j 0)
    (hwv : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j)
    (hhv : ∀ i < G.N, hP.eval (pi2Omega i) = (hValues G w α β γ).getD i 0)
    (hpull : ∀ i < G.N, ¬ G.IsHole i → RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0)
    (hpush : ∀ i < G.N, G.dPush pi2Omega (RecCircuit.emb w) α β γ i ≠ 0) :
    (UniComplete.AlgC.novP (G.logN + 2) fun j ↦ (qNovel G w α β γ).getD j 0) =
      numPoly S wP hP α β γ /ₘ G.zV pi2Omega := by
  have hn : G.logN ≤ 32 := by omega
  have hnum := num_eq_zV_mul hn fun i hi ↦ numPoly_eval_omega hV hn S w hwv α β γ hhv hpull hpush hi
  have hwdeg : wP.natDegree < G.N := by rw [hwP]; exact UniComplete.AlgC.novP_natDegree_lt _ _
  have hhdeg : hP.natDegree < G.N := by rw [hhP]; exact UniComplete.AlgC.novP_natDegree_lt _ _
  refine poly_eq_of_eval_eq (n := 2 ^ (G.logN + 2)) (UniComplete.AlgC.novP_natDegree_lt _ _) ?_
    (cosetPoint G.logN) (fun a ha b hb h ↦ cosetPoint_inj hm ha hb h) fun p hp ↦ ?_
  · have := natDegree_qHonest_lt hV S hwdeg hhdeg α β γ
    calc _ < 4 * G.N := this
      _ = 2 ^ (G.logN + 2) := by unfold RecPiop.Circuit.N; ring
  · have hc : (UniComplete.AlgC.novP (G.logN + 2) fun j ↦ (qNovel G w α β γ).getD j 0).eval (cosetPoint G.logN p) =
        (qValues G w α β γ).getD p 0 :=
      novP_coefficients_eval (k := G.logN + 2) (by omega) (cosetOffset G.logN) (qValues G w α β γ)
        (size_qValues w α β γ) hp
    have hzne : (G.zV pi2Omega).eval (cosetPoint G.logN p) ≠ 0 := by
      unfold RecPiop.Circuit.zV
      rw [Polynomial.eval_prod]
      exact Finset.prod_ne_zero_iff.mpr fun j hj ↦ by
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        exact fun h ↦ cosetPoint_ne hm hp (mem_range.mp hj) (CharTwo.add_eq_zero.mp h)
    have hzv : zvAt G.logN (cosetPoint G.logN p) = (G.zV pi2Omega).eval (cosetPoint G.logN p) := by
      unfold zvAt
      rw [iterate_sq_eq, RecPiop.Circuit.zV_eval_eq G UniComplete.Domain.basisE hn]
    rw [hc, qValues_eq hV hm w α β γ S wP hP hwP hσ hκ hhP hp, hzv]
    conv_lhs => rw [hnum]
    rw [Polynomial.eval_mul]
    field_simp

end RecCompose

/-- info: 'RecCompose.novP_qNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.novP_qNovel
