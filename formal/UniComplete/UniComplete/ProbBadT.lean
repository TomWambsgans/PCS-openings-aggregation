-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.ProbHyp
import UniComplete.AlgCQuot
import UniComplete.DomainCoord18
import UniComplete.Reference

/-!
# The bad point challenges are few (`BadTCard`)

`BadT s fp t` (`ProbHyp.lean`): BLAKE2S's coordinate functionals at `t`, `y = coordinatesAt t (coordinateFunctionals r)`
(`r = h_B`), are a proper prefix of the memory's or the bytecode's point `w.take lm`, `w.take lb` (`w` the digits of
`t`), or of Flock's point `fp`. Each case fixes `y_0(t)`: to `w_0 = t` (the digits' first, `Domain.digits_getD`) or to
`fp_0`, a constant. `y_0 = Σ_m a_{0,m} X^(2^m)` is a polynomial (`coord0`, `Quotients.lean`'s `coordinateP`) of degree
at most `2^(r−1)` (`AlgC.coordinateP_natDegree`), and `y_0 − X`, `y_0 − c` are nonzero: `y_0(ω_1) = 1`, `y_0(ω_2) = 0`,
`y_0(0) = 0` (`Domain.coordinatesAt_pointE_of_basis`), while `ω_2 ≠ 0`. So the bad `t` are among the at most
`2 · 2^(r−1)` roots of the two (`badTCard_of_basis`), and at the reference shape (`h_B = 18`,
`Domain.coordinateFunctionalsBasis_18`) **`badTCard_reference : BadTCard reference (3 * 2 ^ 17)`** (the bound is
`2 · 2^17`).
-/

namespace UniComplete.Prob

open UniStatement LeanVM.Parameters Polynomial

/-- **The first coordinate functional** `y_0 = Σ_m a_{0,m} X^(2^m)`, as a polynomial. -/
noncomputable def coord0 (r : ℕ) : E[X] := (coordinateP (coordinateFunctionals r) 0).toPoly

theorem coordinatesAt_length (t : E) (r : ℕ) : (coordinatesAt t (coordinateFunctionals r)).length = r := by
  rw [AlgC.coordinatesAt_eq_map, List.length_map, List.length_range]

theorem coordinatesAt_getD_zero (t : E) {r : ℕ} (hr : 0 < r) :
    (coordinatesAt t (coordinateFunctionals r)).getD 0 0 = (coord0 r).eval t := by
  rw [AlgC.coordinatesAt_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr,
    Option.map_some, Option.getD_some, AlgC.pEval_eq]
  rfl

theorem coord0_eval_pointE {r : ℕ} (hC : Domain.CoordinateFunctionalsBasis r) (hr : 0 < r) {i : ℕ}
    (hi : i < 2 ^ r) : (coord0 r).eval (pointE i) = if i.testBit 0 then 1 else 0 := by
  rw [← coordinatesAt_getD_zero _ hr, Domain.coordinatesAt_pointE_of_basis hC hi, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hr]
  rfl

theorem getD_zero_of_take {y P : List E} (hy : 0 < y.length) (h : P.take y.length = y) :
    y.getD 0 0 = P.getD 0 0 := by
  rw [← h]
  simp [List.getD_eq_getElem?_getD, hy]

theorem take_getD_zero {w : List E} {n : ℕ} (hn : 0 < n) : (w.take n).getD 0 0 = w.getD 0 0 := by
  simp [List.getD_eq_getElem?_getD, hn]

/-- **The bad point challenges are among `2 · 2^(r−1)` values**, for a shape whose BLAKE2S height `r ≥ 2` has the
coordinate functionals' basis property. -/
theorem badTCard_of_basis (s : UniStatement.Shape) {r : ℕ} (hr : s.heights.getD opBlake2s 0 = r) (h2 : 2 ≤ r)
    (hC : Domain.CoordinateFunctionalsBasis r) : BadTCard s (2 * 2 ^ (r - 1)) := by
  intro fp
  have hr0 : 0 < r := by omega
  have hlt2 : 2 < 2 ^ r :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) h2 : 2 ^ 2 ≤ 2 ^ r)
  have hY1 : (coord0 r).eval (pointE 1) = 1 := by
    rw [coord0_eval_pointE hC hr0 (by omega)]
    rfl
  have hY2 : (coord0 r).eval (pointE 2) = 0 := by
    rw [coord0_eval_pointE hC hr0 hlt2]
    rfl
  have hY0 : (coord0 r).eval 0 = 0 := by
    rw [← Domain.pointE_zero, coord0_eval_pointE hC hr0 (Nat.two_pow_pos r)]
    rfl
  have hp2 : pointE 2 ≠ 0 := by
    intro h
    rw [← Domain.pointE_zero] at h
    exact absurd (Domain.pointE_injOn (by norm_num) (by norm_num) h) (by norm_num)
  have hne1 : coord0 r - X ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval (pointE 2)) h
    rw [Polynomial.eval_sub, Polynomial.eval_X, hY2, Polynomial.eval_zero, zero_sub, neg_eq_zero] at this
    exact hp2 this
  have hne2 : ∀ c : E, coord0 r - C c ≠ 0 := by
    intro c h
    have h0 := congrArg (Polynomial.eval 0) h
    have h1 := congrArg (Polynomial.eval (pointE 1)) h
    rw [Polynomial.eval_sub, Polynomial.eval_C, hY0, Polynomial.eval_zero, zero_sub, neg_eq_zero] at h0
    rw [Polynomial.eval_sub, Polynomial.eval_C, hY1, Polynomial.eval_zero, h0, sub_zero] at h1
    exact one_ne_zero h1
  have hdeg := AlgC.coordinateP_natDegree r hr0
  have hpow : 1 ≤ 2 ^ (r - 1) := Nat.one_le_two_pow
  have hd1 : (coord0 r - X).natDegree ≤ 2 ^ (r - 1) :=
    le_trans (natDegree_sub_le _ _) (max_le hdeg (by rw [natDegree_X]; exact hpow))
  have hd2 : (coord0 r - C (fp.getD 0 0)).natDegree ≤ 2 ^ (r - 1) :=
    le_trans (natDegree_sub_le _ _) (max_le hdeg (by rw [natDegree_C]; exact Nat.zero_le _))
  refine ⟨(coord0 r - X).roots.toFinset ∪ (coord0 r - C (fp.getD 0 0)).roots.toFinset, ?_, ?_⟩
  · refine le_trans (Finset.card_union_le _ _) ?_
    have c1 := le_trans (Multiset.toFinset_card_le _) (le_trans (card_roots' (coord0 r - X)) hd1)
    have c2 := le_trans (Multiset.toFinset_card_le _)
      (le_trans (card_roots' (coord0 r - C (fp.getD 0 0))) hd2)
    omega
  · intro t ht
    unfold BadT at ht
    dsimp only at ht
    obtain ⟨P, hP, hlt, htake⟩ := ht
    rw [hr] at hlt htake
    have hyl := coordinatesAt_length t r
    have hy0 := getD_zero_of_take (by rw [hyl]; exact hr0) htake
    rw [coordinatesAt_getD_zero t hr0] at hy0
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · -- the bytecode's point: `y_0(t) = w_0 = t`
      rw [hyl, List.length_take] at hlt
      rw [take_getD_zero (by omega), Domain.digits_getD t (by omega)] at hy0
      refine Finset.mem_union_left _ (Multiset.mem_toFinset.mpr ((mem_roots hne1).mpr ?_))
      rw [IsRoot, Polynomial.eval_sub, Polynomial.eval_X, hy0]
      exact sub_self t
    · -- the memory's point
      rw [hyl, List.length_take] at hlt
      rw [take_getD_zero (by omega), Domain.digits_getD t (by omega)] at hy0
      refine Finset.mem_union_left _ (Multiset.mem_toFinset.mpr ((mem_roots hne1).mpr ?_))
      rw [IsRoot, Polynomial.eval_sub, Polynomial.eval_X, hy0]
      exact sub_self t
    · -- Flock's point: `y_0(t) = fp_0`
      refine Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ((mem_roots (hne2 _)).mpr ?_))
      rw [IsRoot, Polynomial.eval_sub, Polynomial.eval_C, hy0]
      exact sub_self _

theorem reference_blake2sHeight : reference.heights.getD opBlake2s 0 = 18 := by
  rw [reference_heights]
  rfl

/-- **At most `3 · 2^17` bad point challenges at the reference shape** (in fact `2 · 2^17`), for every Flock point. -/
theorem badTCard_reference : BadTCard reference (3 * 2 ^ 17) := by
  intro fp
  obtain ⟨T, hT, hmem⟩ :=
    badTCard_of_basis reference reference_blake2sHeight (by norm_num) Domain.coordinateFunctionalsBasis_18 fp
  exact ⟨T, le_trans hT (by norm_num), hmem⟩

end UniComplete.Prob

/-- info: 'UniComplete.Prob.badTCard_of_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.badTCard_of_basis

/-- info: 'UniComplete.Prob.badTCard_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.badTCard_reference
