-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E` and `ofK`.
import E2ECompleteness.ProverDefs
import Completeness

/-!
# The prover's values at `t` are F1's honest ones

The Statement's prover sends, at `t`, the four row values `rowValuesAt` (each row polynomial in
the novel basis, `Domain.novelEval`, with its masks past `w_24(t)`) and the wiring polynomial's
value `nextAt`. Here:

* `novelEval_eq_sum`: `novelEval coeffs first step ds` is `Σ_i coeffs[first + step·i] · ∏_{bit k
  of i} ds_k` (its fold, one digit at a time from the lowest, `fold_novel`);
* `opened_eq_sum`: F1's honest value `Params.opened g t j` of a witness table's row polynomial is
  `Σ_{i < 2^23} c[j + 4i] · ∏_{bit k of i} w_{k+2}(t)`;
* **`rowValuesAt_eq`**: for a witness table whose entries are the Statement's (`witnessEntry`, the
  cells' coefficients then the sixteen mask entries), `rowValuesAt` is `Params.opened` of its row
  polynomials (the masks' entries `j + 4i`, `i < 4`, are the only ones past `2^24` that can be
  nonzero);
* **`nextAt_eq`**: for a wiring table whose entries are the Statement's, `nextAt` is its
  polynomial at `t`.

For any table of the right support, no evaluation at any size.
-/

open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain Finset Polynomial
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness

/-! ## Sums over a cube by numbers -/

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ N : ℕ, ∑ i ∈ range (2 * N), g i = ∑ j ∈ range N, (g (2 * j) + g (2 * j + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_two_mul g N, sum_range_succ, add_assoc]

/-- The digits' product of a number `2 j + b`: its low bit chooses `d`, the rest are `j`'s. -/
theorem prod_testBit_two_mul_add {M : Type*} [CommMonoid M] (d : M) (ds : ℕ → M) (j : ℕ)
    (b : Bool) (L : ℕ) :
    ∏ k ∈ range (L + 1), (if (2 * j + (if b then 1 else 0)).testBit k then
        (if k = 0 then d else ds (k - 1)) else 1) =
      (if b then d else 1) * ∏ k ∈ range L, (if j.testBit k then ds k else 1) := by
  rw [prod_range_succ']
  have h0 : (2 * j + (if b then 1 else 0)).testBit 0 = b := by
    cases b <;> simp [Nat.testBit_zero, Nat.mul_mod_right]
  have hs : ∀ k, (2 * j + (if b then 1 else 0)).testBit (k + 1) = j.testBit k := by
    intro k
    rw [Nat.testBit_succ]
    congr 1
    cases b <;> simp <;> omega
  simp only [h0, hs, if_true, show ∀ k : ℕ, k + 1 ≠ 0 from fun k ↦ by omega, if_false,
    Nat.add_sub_cancel]
  rw [mul_comm]

/-! ## `novelEval` -/

/-- One fold step of `novelEval`: pairs `(a, b)` become `a + d·b`. -/
def novelStep (cur : Array E) (d : E) : Array E :=
  Array.ofFn (n := cur.size / 2) fun j ↦ cur.getD (2 * j.val) 0 + d * cur.getD (2 * j.val + 1) 0

theorem novelStep_getD (cur : Array E) (d : E) (j : ℕ) (hj : j < cur.size / 2) :
    (novelStep cur d).getD j 0 = cur.getD (2 * j) 0 + d * cur.getD (2 * j + 1) 0 := by
  simp [novelStep, Array.getD_eq_getD_getElem?, hj]

/-- **The fold of `novelEval`**: from an array of `2^|ds|` entries, the entry left is
`Σ_i cur_i · ∏_{bit k of i} ds_k`. -/
theorem fold_novel : ∀ (ds : List E) (cur : Array E), cur.size = 2 ^ ds.length →
    (ds.foldl novelStep cur).getD 0 0 =
      ∑ i ∈ range (2 ^ ds.length),
        cur.getD i 0 * ∏ k ∈ range ds.length, (if i.testBit k then ds.getD k 0 else 1)
  | [], cur, h => by
    simp only [List.foldl_nil, List.length_nil, pow_zero, range_one, sum_singleton,
      range_zero, prod_empty, mul_one]
  | d :: ds, cur, h => by
    rw [List.foldl_cons, fold_novel ds (novelStep cur d) (by
      simp only [novelStep, Array.size_ofFn, h, List.length_cons, pow_succ]; omega)]
    rw [List.length_cons, pow_succ, mul_comm (2 ^ ds.length) 2, sum_range_two_mul]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j < cur.size / 2 := by
      rw [h, List.length_cons, pow_succ]; simp only [mem_range] at hj; omega
    rw [novelStep_getD cur d j hj']
    have e0 := prod_testBit_two_mul_add d (fun k ↦ ds.getD k 0) j false ds.length
    have e1 := prod_testBit_two_mul_add d (fun k ↦ ds.getD k 0) j true ds.length
    simp only [Bool.false_eq_true, if_false, add_zero, if_true] at e0 e1
    have hl : ∀ i : ℕ, ∏ k ∈ range (ds.length + 1),
        (if i.testBit k then (d :: ds).getD k 0 else 1) =
        ∏ k ∈ range (ds.length + 1),
          (if i.testBit k then (if k = 0 then d else ds.getD (k - 1) 0) else 1) := by
      intro i
      refine prod_congr rfl fun k _ ↦ ?_
      rcases k with _ | k <;> simp
    rw [hl, hl, e0, e1]
    ring

/-- **`novelEval` as a sum**: `Σ_i coeffs[first + step·i] · ∏_{bit k of i} ds_k`. -/
theorem novelEval_eq_sum (coeffs : Array K) (first step : ℕ) (ds : List E) :
    novelEval coeffs first step ds =
      ∑ i ∈ range (2 ^ ds.length), ofK (coeffs.getD (first + step * i) 0) *
        ∏ k ∈ range ds.length, (if i.testBit k then ds.getD k 0 else 1) := by
  unfold novelEval
  have h := fold_novel ds (Array.ofFn (n := 2 ^ ds.length) fun j ↦
    ofK (coeffs.getD (first + step * j.val) 0)) (by simp)
  refine (Eq.trans ?_ h).trans (sum_congr rfl fun i hi ↦ ?_)
  · rfl
  · simp [Array.getD_eq_getD_getElem?, mem_range.mp hi]

/-! ## `digitsOf` -/

theorem getLastD_append_one {α : Type} (a : α) :
    ∀ (l : List α) (d : α), (l ++ [a]).getLastD d = a
  | [], _ => rfl
  | b :: l, _ => by
    rw [List.cons_append, List.getLastD_cons, getLastD_append_one a l b]

theorem digitsOf_foldl (t : E) : ∀ n : ℕ,
    (List.range n).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t + ws.getLastD t]) [t] =
      (List.range (n + 1)).map fun k ↦ sq^[k] t
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ (n := n), List.foldl_append, digitsOf_foldl t n, List.foldl_cons,
      List.foldl_nil, List.range_succ (n := n + 1), List.map_append, List.map_singleton]
    have hl : ((List.range (n + 1)).map fun k ↦ sq^[k] t).getLastD t = sq^[n] t := by
      rw [List.range_succ (n := n), List.map_append, List.map_singleton, getLastD_append_one]
    rw [hl, Function.iterate_succ_apply']
    rfl

/-- **`digitsOf t count`** is `w_0(t), …, w_count(t)`. -/
theorem digitsOf_eq (t : E) (count : ℕ) :
    digitsOf t count = (List.range (count + 1)).map fun k ↦ sq^[k] t :=
  digitsOf_foldl t count

theorem digitsOf_getD (t : E) (count k : ℕ) (hk : k ≤ count) :
    (digitsOf t count).getD k 0 = sq^[k] t := by
  rw [digitsOf_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega)]
  rfl

/-! ## Sums over the cube by numbers -/

theorem sum_cube_eq_sum_range {M : Type*} [AddCommMonoid M] {m : ℕ} (f : (Fin m → Bool) → M) :
    ∑ b, f b = ∑ i ∈ range (2 ^ m), f (Completeness.bitsOf m i) := by
  refine Finset.sum_bij' (fun b _ ↦ Completeness.idx b) (fun i _ ↦ Completeness.bitsOf m i)
    (fun b _ ↦ mem_range.mpr (Completeness.idx_lt b)) (fun _ _ ↦ mem_univ _)
    (fun b _ ↦ Completeness.bitsOf_idx b)
    (fun i hi ↦ Completeness.idx_bitsOf m i (mem_range.mp hi)) (fun b _ ↦ ?_)
  rw [Completeness.bitsOf_idx]

/-- **A digit expansion by numbers.** -/
theorem digitsEval_eq_sum {F : Type*} [Field F] {m : ℕ} (c : (Fin m → Bool) → F)
    (w : Fin m → F) (wn : ℕ → F) (hw : ∀ k : Fin m, w k = wn k) :
    digitsEval c w =
      ∑ i ∈ range (2 ^ m), c (Completeness.bitsOf m i) *
        ∏ k ∈ range m, (if i.testBit k then wn k else 1) := by
  unfold digitsEval
  rw [sum_cube_eq_sum_range]
  refine sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun k ↦ if i.testBit k then wn k else 1)]
  refine prod_congr rfl fun k _ ↦ ?_
  rw [hw]
  rfl

/-! ## The witness table's row values -/

/-- The index of a table entry of role `j`: the role's two bits, then `i`. -/
theorem idx_role {k : ℕ} (j : Fin 4) (b : Fin k → Bool) :
    Completeness.idx (Fin.cons (roleBit0 j) (Fin.cons (roleBit1 j) b) : Fin (k + 1 + 1) → Bool) =
      j + 4 * Completeness.idx b := by
  rw [Completeness.idx_cons, Completeness.idx_cons]
  fin_cases j <;> simp [roleBit0, roleBit1] <;> ring

/-- **F1's honest value of a witness table's row polynomial `j`**, by numbers:
`Σ_{i < 2^23} c[j + 4i] · ∏_{bit k of i} w_{k+2}(t)`. -/
theorem opened_eq_sum (cW : (Fin (22 + 2 + 1) → Bool) → K) (t : E) (j : Fin 4) :
    Params.opened (witnessOfTable fun b ↦ algebraMap K E (cW b)) t j =
      ∑ i ∈ range (2 ^ (22 + 1)), ofK (Completeness.natTable cW (j + 4 * i)) *
        ∏ k ∈ range (22 + 1), (if i.testBit k then sq^[k + 2] t else 1) := by
  unfold Params.opened
  rw [Completeness.witnessOfTable_apply, eval_comp, rowPoly_eval, tablePoly_eval,
    digitsEval_eq_sum _ _ (fun n : ℕ ↦ sq^[n + 2] t) fun k ↦ by
      rw [← Function.iterate_add_apply]]
  refine sum_congr rfl fun i hi ↦ ?_
  congr 1
  have e := Completeness.natTable_idx cW
    (Fin.cons (roleBit0 j) (Fin.cons (roleBit1 j) (Completeness.bitsOf (22 + 1) i)))
  rw [idx_role, Completeness.idx_bitsOf _ _ (mem_range.mp hi)] at e
  rw [e]
  rfl

/-- The masks' part: past `2^24` the witness table's entries are the masks', zero from `16` on. -/
theorem natTable_mask_zero (cW : (Fin (22 + 2 + 1) → Bool) → K) (wHat mask : Array K)
    (hmask : mask.size = 16)
    (hW : ∀ i, witnessEntry (2 ^ 24) wHat mask i = Completeness.natTable cW i) (j : Fin 4)
    {i : ℕ} (hi : 4 ≤ i) : Completeness.natTable cW (j + 4 * (2 ^ 22 + i)) = 0 := by
  have hj := j.isLt
  rw [← hW (j + 4 * (2 ^ 22 + i))]
  unfold witnessEntry
  have h1 : ¬ (↑j + 4 * (2 ^ 22 + i) < 2 ^ 24) := by omega
  rw [if_neg h1]
  have h2 : mask.size ≤ ↑j + 4 * (2 ^ 22 + i) - 2 ^ 24 := by rw [hmask]; omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h2]
  rfl

/-- The product over `N + 1` digits of an index below `4` past `2^N`: the top digit and the two
low ones. -/
theorem prod_mask_digits (N : ℕ) (hN : 2 ≤ N) (f : ℕ → E) {i : ℕ} (hi : i < 4) :
    ∏ k ∈ range (N + 1), (if (2 ^ N + i).testBit k then f k else 1) =
      f N * ∏ k ∈ range 2, (if i.testBit k then f k else 1) := by
  rw [prod_range_succ, mul_comm]
  have htop : (2 ^ N + i).testBit N = true := by
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi
      (le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hN)))]; rfl
  rw [htop, if_pos rfl]
  congr 1
  rw [← prod_subset (range_mono hN) fun k hk hk2 ↦ ?_]
  · refine prod_congr rfl fun k hk ↦ ?_
    rw [Nat.testBit_two_pow_add_gt (by simp at hk; omega)]
  · rw [Nat.testBit_two_pow_add_gt (by simp at hk; omega),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (le_trans (by norm_num : 4 ≤ 2 ^ 2)
        (Nat.pow_le_pow_right (by norm_num) (show 2 ≤ k by simp at hk2; omega))))]
    rfl

/-- The cells' part: below `2^22`, the product over `23` digits is over the `22` low ones. -/
theorem prod_cell_digits (t : E) {i : ℕ} (hi : i < 2 ^ 22) :
    ∏ k ∈ range (22 + 1), (if i.testBit k then sq^[k + 2] t else 1) =
      ∏ k ∈ range 22, (if i.testBit k then sq^[k + 2] t else 1) := by
  rw [prod_range_succ, Nat.testBit_eq_false_of_lt hi]
  simp

/-- **The prover's row values are F1's honest ones**: for a witness table whose entries are the
Statement's (the cells' coefficients `wHat` below `2^24`, then the sixteen mask entries),
`rowValuesAt` at `t` is `Params.opened` of the table's row polynomials. -/
theorem rowValuesAt_eq (cW : (Fin (22 + 2 + 1) → Bool) → K) (wHat mask : Array K)
    (hmask : mask.size = 16)
    (hW : ∀ i, witnessEntry (2 ^ 24) wHat mask i = Completeness.natTable cW i) (t : E)
    (j : Fin 4) :
    (rowValuesAt 22 wHat mask t).get j =
      Params.opened (witnessOfTable fun b ↦ algebraMap K E (cW b)) t j := by
  rw [opened_eq_sum, show 2 ^ (22 + 1) = 2 ^ 22 + 2 ^ 22 by ring, sum_range_add]
  have hd : ∀ k ≤ 24, (digitsOf t (cellVars 22)).getD k 0 = sq^[k] t := fun k hk ↦
    digitsOf_getD t 24 k hk
  have hlow : ((digitsOf t (cellVars 22)).drop 2).take (cellVars 22 - 2) =
      (List.range 22).map fun k ↦ sq^[k + 2] t := by
    rw [digitsOf_eq]
    apply List.ext_getElem (by simp [cellVars])
    intro n h1 h2
    simp [cellVars] at h1 h2 ⊢
    try rw [add_comm]
  have hmk : ((digitsOf t (cellVars 22)).drop 2).take 2 = (List.range 2).map fun k ↦ sq^[k + 2] t := by
    rw [digitsOf_eq]
    apply List.ext_getElem (by simp [cellVars])
    intro n h1 h2
    simp [cellVars] at h1 h2 ⊢
    try rw [add_comm]
  simp only [rowValuesAt, Vector.get_ofFn]
  rw [hlow, hmk, hd (cellVars 22) le_rfl, show cellVars 22 = 24 from rfl, novelEval_eq_sum,
    novelEval_eq_sum, List.length_map, List.length_range, List.length_map, List.length_range]
  refine congrArg₂ (· + ·) ?_ ?_
  · -- The cells.
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    have hj := j.isLt
    rw [prod_cell_digits t hi', ← hW, witnessEntry, if_pos (by omega)]
    refine congrArg₂ (· * ·) rfl (prod_congr rfl fun k hk ↦ ?_)
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hk)]
    rfl
  · -- The masks.
    have hsplit : ∀ f : ℕ → E, ∑ x ∈ range (2 ^ 22), f x =
        ∑ x ∈ range 4, f x + ∑ x ∈ range (2 ^ 22 - 4), f (4 + x) := by
      intro f
      rw [← sum_range_add, show 4 + (2 ^ 22 - 4) = 2 ^ 22 by norm_num]
    rw [mul_sum, hsplit]
    have hz : ∑ x ∈ range (2 ^ 22 - 4), ofK (Completeness.natTable cW (j + 4 * (2 ^ 22 + (4 + x)))) *
        ∏ k ∈ range (22 + 1), (if (2 ^ 22 + (4 + x)).testBit k then sq^[k + 2] t else 1) = 0 :=
      sum_eq_zero fun x _ ↦ by
        rw [natTable_mask_zero cW wHat mask hmask hW j (by omega : 4 ≤ 4 + x)]
        simp
    rw [hz, add_zero, show (2 : ℕ) ^ 2 = 4 by norm_num]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    have hj := j.isLt
    rw [prod_mask_digits 22 (by norm_num) (fun k ↦ sq^[k + 2] t) hi',
      show (sq^[22 + 2] t : E) = sq^[24] t from rfl, ← hW, witnessEntry, if_neg (by omega),
      show j + 4 * (2 ^ 22 + i) - 2 ^ 24 = j + 4 * i by omega]
    have hp : ∏ k ∈ range 2, (if i.testBit k then ((List.range 2).map fun k ↦ sq^[k + 2] t).getD k 0
        else 1) = ∏ k ∈ range 2, (if i.testBit k then sq^[k + 2] t else 1) :=
      prod_congr rfl fun k hk ↦ by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hk)]
        rfl
    rw [hp]
    ring

/-! ## The wiring value -/

/-- **The prover's wiring value is the wiring table's polynomial at `t`**: for a table whose
entries are the Statement's `sigmaHat`. -/
theorem nextAt_eq (cσ : (Fin (22 + 2) → Bool) → K) (sigmaHat : Array K)
    (hσ : ∀ i, sigmaHat.getD i 0 = Completeness.natTable cσ i) (t : E) :
    nextAt 22 sigmaHat t = (tablePoly fun b ↦ algebraMap K E (cσ b)).eval t := by
  have hw : ((digitsOf t (cellVars 22)).take (cellVars 22)) =
      (List.range 24).map fun k ↦ sq^[k] t := by
    rw [digitsOf_eq]
    apply List.ext_getElem (by simp [cellVars])
    intro n h1 h2
    simp [cellVars] at h1 h2 ⊢
  rw [nextAt, hw, novelEval_eq_sum, tablePoly_eval,
    digitsEval_eq_sum _ _ (fun n : ℕ ↦ sq^[n] t) fun _ ↦ rfl]
  simp only [List.length_map, List.length_range]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [zero_add, one_mul, hσ, Completeness.natTable, if_pos (mem_range.mp hi)]
  congr 1

end E2ECompleteness

/-- info: 'E2ECompleteness.rowValuesAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.rowValuesAt_eq

/-- info: 'E2ECompleteness.nextAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.nextAt_eq
