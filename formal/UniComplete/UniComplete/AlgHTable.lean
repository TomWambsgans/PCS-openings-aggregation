-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHLeaf

/-!
# A table's leaf quotient divides exactly and fits (milestone 4)

`(R P + P') Z_pad + (R + 1) Z_act`, `R` the polynomial of the table's leaves on `V_r` (`P'/P` on an active row, `1`
on a padding row), `P`, `P'` the products of the pull and push fingerprints at the columns' polynomials:

* `tableLeafNumerator_eval`: it vanishes on `V_r` (`Z_act` on the active rows, `Z_pad` on the others; `P ≠ 0` on
  an active row by `¬ BadFp`, every tuple having at most `16` forms, `tables_facts`);
* `natDegree_tableLeafNumerator_le`: degree `≤ max(M(n − 1) + (n − rows), (n − 1) + rows)`,
  `M = max(pullDegree, pushDegree)` (`tableDegrees`), and `≤ M(n − 1) + (n − leastRows r)` under `RowsFit`
  (`table_degree_arith`: every table has at least two flushes, so `M ≥ 3` and `leastRows r ≤ (M − 1)(n − 1)`).
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

set_option maxRecDepth 4000 in
/-- **The tables' flushes** (structural, by the kernel): every tuple has at most `16` forms, as many pulls as
pushes, at least two flushes. -/
theorem tables_facts : ∀ t < 6, (∀ tu ∈ (tables.getD t default).flushes.pull, tu.length ≤ 16) ∧
    (∀ tu ∈ (tables.getD t default).flushes.push, tu.length ≤ 16) ∧
    (tables.getD t default).flushes.pull.length = (tables.getD t default).flushes.push.length ∧
    2 ≤ (tables.getD t default).flushes.pull.length := by
  decide

theorem foldl_zip_degrees : ∀ (ps qs : List (List Form)) (a b : ℕ), ps.length = qs.length →
    (ps.zip qs).foldl (fun (acc : ℕ × ℕ) (x : List Form × List Form) ↦ (acc.1 + tupleDegree x.1, acc.2 + tupleDegree x.2))
      (a, b) = (a + (ps.map tupleDegree).sum, b + (qs.map tupleDegree).sum)
  | [], [], a, b, _ => by simp
  | p :: ps, q :: qs, a, b, h => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_degrees ps qs _ _ (by simpa using h)]
    simp only [List.map_cons, List.sum_cons, Prod.mk.injEq]
    constructor <;> ring
  | [], _ :: _, _, _, h => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)

theorem tableDegrees_eq {t : ℕ} (ht : t < 6) :
    tableDegrees (tables.getD t default) = (1 + ((tables.getD t default).flushes.pull.map tupleDegree).sum,
      ((tables.getD t default).flushes.push.map tupleDegree).sum) :=
  (foldl_zip_degrees _ _ 1 0 (tables_facts t ht).2.2.1).trans (by rw [Nat.zero_add])

theorem three_le_pullDegree {t : ℕ} (ht : t < 6) : 3 ≤ (tableDegrees (tables.getD t default)).1 := by
  rw [tableDegrees_eq ht]
  have h2 := (tables_facts t ht).2.2.2
  have : (tables.getD t default).flushes.pull.length ≤ ((tables.getD t default).flushes.pull.map tupleDegree).sum := by
    have := List.length_le_sum_of_one_le ((tables.getD t default).flushes.pull.map tupleDegree)
      (fun d hd ↦ by obtain ⟨tu, -, rfl⟩ := List.mem_map.mp hd; exact one_le_tupleDegree tu)
    simpa using this
  show 3 ≤ 1 + _
  omega

section Honest

variable {tr : Trace} (hon : TraceHonest tr) {alphas : List E} {beta : E} (hbad : ¬ BadFp tr alphas beta)
include hon

/-- A row's pull fingerprints' product. -/
def rowPull (tr : Trace) (weights : Array E) (beta : E) (t i : ℕ) : E :=
  (tables.getD t default).flushes.pull.foldl (fun acc tuple ↦ acc * fpE tuple weights beta (tr.cell t · i)) 1

/-- A row's push fingerprints' product. -/
def rowPush (tr : Trace) (weights : Array E) (beta : E) (t i : ℕ) : E :=
  (tables.getD t default).flushes.push.foldl (fun acc tuple ↦ acc * fpE tuple weights beta (tr.cell t · i)) 1

omit hon in
theorem tableLeaves_getD (weights : Array E) (beta : E) {t i : ℕ} (hi : i < 2 ^ tr.height t) :
    (tableLeaves tr weights beta t).getD i 0 = if isActive i (tr.rows.getD t 0) (tr.height t) then
      rowPush tr weights beta t i * (rowPull tr weights beta t i)⁻¹ else 1 := by
  unfold tableLeaves
  rw [getD_ofFn_lt _ _ hi]
  rfl

omit hon in
theorem tableLeaves_size (weights : Array E) (beta : E) (t : ℕ) :
    (tableLeaves tr weights beta t).size = 2 ^ tr.height t := Array.size_ofFn

/-- A table's column polynomial at `ω_i` is the row's value (`0` past the table's columns). -/
theorem ev_tableCol {t : ℕ} (ht : t < 6) (h28 : tr.height t ≤ 28) {i : ℕ} (hi : i < 2 ^ tr.height t) (c : ℕ) :
    ev (pointE i) ((tablePolys tr t).getD c 0) = tr.cell t c i := by
  unfold tablePolys Trace.cell
  by_cases hc : c < (tables.getD t default).width
  · rw [getD_ofFn_lt _ _ hc, ev_apply, eval_colPolyK h28 ((hon.tablesSize.2 t ht).2 c hc) hi]
  · rw [getD_ofFn_ge _ _ (by omega), map_zero, Trace.column, List.getD_eq_default _ _ (by
      rw [(hon.tablesSize.2 t ht).1]; omega)]
    simp [Array.getD_eq_getD_getElem?]

theorem ev_tableProd {t : ℕ} (ht : t < 6) (h28 : tr.height t ≤ 28) {i : ℕ} (hi : i < 2 ^ tr.height t)
    (weights : Array E) (beta : E) (l : List (List Form)) :
    ev (pointE i) (l.foldl (fun acc tuple ↦ acc * fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0) 1) =
      l.foldl (fun acc tuple ↦ acc * fpE tuple weights beta (tr.cell t · i)) 1 := by
  rw [ev_foldl_mul (pointE i) (fun tuple ↦ fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0), map_one]
  simp only [ev_fpP, ev_tableCol hon ht h28 hi]

omit hon in
include hbad in
theorem rowPull_ne_zero {t : ℕ} (ht : t < 6) {i : ℕ} (hi : i < 2 ^ tr.height t)
    (ha : isActive i (tr.rows.getD t 0) (tr.height t) = true) : rowPull tr (eqKernel alphas) beta t i ≠ 0 := by
  unfold rowPull
  rw [foldl_mul_eq, one_mul]
  refine List.prod_ne_zero fun h0 ↦ ?_
  obtain ⟨tuple, htu, h0⟩ := List.mem_map.mp h0
  apply hbad
  refine ⟨tupleAt tuple (tr.cell t · i), ?_, ?_⟩
  · unfold dividedTuples
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    refine List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, List.mem_flatMap.mpr ⟨tuple, htu, ?_⟩⟩
    refine List.mem_map.mpr ⟨i, ?_, rfl⟩
    unfold activeRows
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hi, ha⟩
  · rw [← fpE_eq_fpOf ((tables_facts t ht).1 tuple htu)]; exact h0

include hbad in
/-- **A table's leaf numerator vanishes on `V_r`** (`r ≤ 28`, `rows ≤ 2^r`). -/
theorem tableLeafNumerator_eval {t : ℕ} (ht : t < 6) (h28 : tr.height t ≤ 28)
    (hrows : tr.rows.getD t 0 ≤ 2 ^ tr.height t) {i : ℕ} (hi : i < 2 ^ tr.height t) :
    (tp (tableLeafNumerator tr (eqKernel alphas) beta t (ofNovel (tr.height t)
      (novelOfValuesE (tr.height t) (tableLeaves tr (eqKernel alphas) beta t))))).eval (pointE i) = 0 := by
  rw [← ev_apply]
  unfold tableLeafNumerator
  dsimp only
  simp only [map_add, map_mul, map_one]
  rw [ev_tableProd hon ht h28 hi, ev_tableProd hon ht h28 hi, ev_apply (pointE i) (ofNovel _ _),
    eval_ofNovel_novelOfValuesE h28 (tableLeaves_size _ _ _) hi, tableLeaves_getD _ _ hi,
    ev_apply (pointE i) (zPadP _ _), ev_apply (pointE i) (zActP _ _), tp_zPadP (by omega), tp_zActP]
  have hr31 : tr.height t ≤ 31 := by omega
  by_cases ha : isActive i (tr.rows.getD t 0) (tr.height t) = true
  · rw [ite_pos_of ha, (Domain.zActP_eval_pointE_eq_zero_iff hr31 hi).mpr ha, mul_zero, add_zero]
    have hne := rowPull_ne_zero hbad ht hi ha
    unfold rowPull rowPush at *
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, CharTwo.add_self_eq_zero, zero_mul]
  · rw [ite_neg_of ha, (Domain.zPadP_eval_pointE_eq_zero_iff hr31 hrows hi).mpr (by simpa using ha), mul_zero,
      zero_add, CharTwo.add_self_eq_zero, zero_mul]

omit hon in
theorem natDegree_foldl_mul_le' {α : Type*} (g : α → Poly) (dg : α → ℕ) :
    ∀ (l : List α), (∀ x ∈ l, (tp (g x)).natDegree ≤ dg x) → ∀ (a : Poly),
      (tp (l.foldl (fun acc x ↦ acc * g x) a)).natDegree ≤ (tp a).natDegree + (l.map dg).sum
  | [], _, a => by simp
  | x :: l, hg, a => by
    rw [List.foldl_cons]
    refine (natDegree_foldl_mul_le' g dg l (fun y hy ↦ hg y (List.mem_cons_of_mem _ hy)) _).trans ?_
    rw [tp_mul, List.map_cons, List.sum_cons]
    have := (natDegree_mul_le (p := tp a) (q := tp (g x))).trans
      (Nat.add_le_add_left (hg x (List.mem_cons_self ..)) _)
    omega

omit hon in
/-- **A table's leaf numerator's degree**: `≤ max(M(n − 1) + (n − rows), (n − 1) + rows)`. -/
theorem natDegree_tableLeafNumerator_le {t : ℕ} (ht : t < 6) (hr : tr.height t ≤ 31)
    (hrows : tr.rows.getD t 0 ≤ 2 ^ tr.height t) (weights : Array E) (beta : E) (rPoly : Poly)
    (hR : (tp rPoly).natDegree ≤ 2 ^ tr.height t - 1) :
    (tp (tableLeafNumerator tr weights beta t rPoly)).natDegree ≤
      max (max (tableDegrees (tables.getD t default)).1 (tableDegrees (tables.getD t default)).2 *
          (2 ^ tr.height t - 1) + (2 ^ tr.height t - tr.rows.getD t 0))
        (2 ^ tr.height t - 1 + tr.rows.getD t 0) := by
  unfold tableLeafNumerator
  dsimp only
  set n := 2 ^ tr.height t - 1
  set rows := tr.rows.getD t 0
  have hcol : ∀ c, (tp ((tablePolys tr t).getD c 0)).natDegree ≤ n := fun c ↦ by
    unfold tablePolys
    by_cases hc : c < (tables.getD t default).width
    · rw [getD_ofFn_lt _ _ hc]; exact Nat.le_sub_one_of_lt (natDegree_colPolyK_lt _ _)
    · rw [getD_ofFn_ge _ _ (by omega), tp_zero, natDegree_zero]; exact Nat.zero_le _
  have hP := natDegree_foldl_mul_le' (fun tuple ↦ fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0)
    (fun tuple ↦ tupleDegree tuple * n) (tables.getD t default).flushes.pull
    (fun tu _ ↦ natDegree_fpP_le tu weights beta _ n hcol) 1
  have hP' := natDegree_foldl_mul_le' (fun tuple ↦ fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0)
    (fun tuple ↦ tupleDegree tuple * n) (tables.getD t default).flushes.push
    (fun tu _ ↦ natDegree_fpP_le tu weights beta _ n hcol) 1
  rw [tp_one, natDegree_one, zero_add, List.sum_map_mul_right] at hP hP'
  rw [tableDegrees_eq ht]
  dsimp only
  set sp := ((tables.getD t default).flushes.pull.map tupleDegree).sum
  set sq := ((tables.getD t default).flushes.push.map tupleDegree).sum
  have hZp : (tp (zPadP rows (tr.height t))).natDegree = 2 ^ tr.height t - rows := by
    rw [tp_zPadP hr, Domain.zPadP_natDegree hr hrows]
  have hZa : (tp (zActP rows (tr.height t))).natDegree = rows := by
    rw [tp_zActP, Domain.zActP_natDegree hrows]
  have hRP : (tp (rPoly * (tables.getD t default).flushes.pull.foldl (fun acc tuple ↦ acc *
      fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0) 1)).natDegree ≤ (1 + sp) * n := by
    rw [tp_mul]; refine (natDegree_mul_le).trans ?_; rw [add_mul, one_mul]; omega
  have hsum : (tp (rPoly * (tables.getD t default).flushes.pull.foldl (fun acc tuple ↦ acc *
      fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0) 1 +
      (tables.getD t default).flushes.push.foldl (fun acc tuple ↦ acc *
      fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0) 1)).natDegree ≤ max (1 + sp) sq * n := by
    rw [tp_add]
    refine (natDegree_add_le _ _).trans (max_le (hRP.trans ?_) (hP'.trans ?_))
    · exact Nat.mul_le_mul_right n (le_max_left _ _)
    · exact Nat.mul_le_mul_right n (le_max_right _ _)
  rw [tp_add, tp_mul, tp_mul]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_mul_le).trans ?_
    rw [hZp]
    exact le_max_of_le_left (Nat.add_le_add_right hsum _)
  · refine (natDegree_mul_le).trans ?_
    rw [hZa]
    refine le_max_of_le_right (Nat.add_le_add_right ?_ _)
    rw [tp_add, tp_one]
    exact (natDegree_add_le _ _).trans (max_le hR (by rw [natDegree_one]; exact Nat.zero_le _))

end Honest

/-- **The arithmetic of the fit**: for `M ≥ 3` and `leastRows r ≤ rows ≤ 2^r`, both degrees are at most
`M(n − 1) + (n − leastRows r)`, `n = 2^r` (every height, `r = 0, 1, 2` included). -/
theorem table_degree_arith {M r rows : ℕ} (hM : 3 ≤ M) (hlo : Shape.leastRows r ≤ rows) (hhi : rows ≤ 2 ^ r) :
    max (M * (2 ^ r - 1) + (2 ^ r - rows)) (2 ^ r - 1 + rows) ≤ M * (2 ^ r - 1) + (2 ^ r - Shape.leastRows r) := by
  have hM' : 3 * (2 ^ r - 1) ≤ M * (2 ^ r - 1) := Nat.mul_le_mul_right _ hM
  have h1 := Nat.one_le_two_pow (n := r)
  unfold Shape.leastRows at hlo ⊢
  split_ifs at hlo ⊢ with h0
  · subst h0; simp at hhi ⊢; omega
  · have hn : 2 ^ r = 2 * 2 ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
    have h2 := Nat.one_le_two_pow (n := r - 1)
    refine max_le (by omega) (by omega)

end UniComplete.AlgH
