-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.FlockProverRounds

/-!
# The pending sum's algebra: the weights and the extensions on the cube

The pieces `PendingSumHolds` is assembled from (`FlockProverSum.lean`), each a fact about the code's tables:

* `foldl_foldE_getD`: the zerocheck's folds (low variable first) leave the table's extension at the point;
* `lowW_getD`, `rowW_split`: the rows' weights the zerocheck's point gives the lincheck (`rowWeightsOf`:
  `e(row) = lowWeights[row mod 64] eq(chi_in, row / 64)`, `lowWeights = skip ⊗ eq(row_low)`) are, at
  `row = x + 2^k row'`, `skip[x] eq(row_low ++ chi_in, row')`;
* `cols_fst_getD`, `cols_snd_getD`: the backward walk is `Aᵀ e`;
* `eqEval_eq`: the verifier's `eqEval` (a fold over the zip) is mumbai's; `sum_eqB_mul_eqB`: `Σ_h eq(p, h) eq(q, h) =
  eq(p, q)`.
-/

namespace UniComplete.FlockP

open UniStatement UniStatement.Flock LeanVM.Parameters Finset
open LeanVM.Protocol.EndToEnd (boolPoint)

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The zerocheck's folds -/

/-- **The low folds are the extension**: `(p.foldl foldE a)[0] = Σ_b eq(p, b) a[b]` for `2^|p|` entries. -/
theorem foldl_foldE_getD : ∀ (p : List E) (a : Array E), a.size = 2 ^ p.length →
    (p.foldl foldE a).getD 0 0 = ∑ b ∈ range (2 ^ p.length), eqB p b * a.getD b 0
  | [], a, _ => by simp
  | r :: rs, a, h => by
    have hs : (foldE a r).size = 2 ^ rs.length := by
      rw [foldE_size', h, List.length_cons, pow_succ]; omega
    rw [List.foldl_cons, foldl_foldE_getD rs _ hs, List.length_cons, pow_succ', UniComplete.sum_range_two_mul]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i < (a.size + 1) / 2 := by rw [h, List.length_cons, pow_succ]; have := mem_range.mp hi; omega
    rw [foldE_getD' a r hi', eqB_cons_even, eqB_cons_odd]
    ring

/-! ## The rows' weights -/

/-- Entries of a `flatMap` of equal-length blocks. -/
theorem flatMap_getD (f : E → List E) (n : ℕ) (hf : ∀ a, (f a).length = n) :
    ∀ (L : List E), ∀ i < L.length, ∀ x < n, (L.flatMap f).getD (i * n + x) 0 = (f (L.getD i 0)).getD x 0
  | [], i, hi, _, _ => absurd hi (by simp)
  | a :: L, i, hi, x, hx => by
    rw [List.flatMap_cons]
    rcases i with _ | i
    · rw [zero_mul, zero_add, List.getD_append _ _ _ _ (by rw [hf]; exact hx)]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [hf]; nlinarith), hf,
        show (i + 1) * n + x - n = i * n + x by rw [Nat.add_mul, one_mul]; omega]
      exact flatMap_getD f n hf L i (by simpa using hi) x hx

/-- **The low weights**: `lowWeights[x + 2^k m] = skip[x] eq(row_low, m)` (`rowLowWeights`). -/
theorem lowW_getD (zSkip : Option E) (low : List E) {x m : ℕ}
    (hx : x < (rowLowWeights zSkip low).1.length) (hm : m < 2 ^ low.length) :
    (rowLowWeights zSkip low).2.getD (m * (rowLowWeights zSkip low).1.length + x) 0 =
      (rowLowWeights zSkip low).1.getD x 0 * eqB low m := by
  have hf : ∀ a : E, ((rowLowWeights zSkip low).1.map fun l ↦ l * a).length = (rowLowWeights zSkip low).1.length :=
    fun a ↦ List.length_map _
  have hlen : (eqKernel low).toList.length = 2 ^ low.length := by rw [Array.length_toList, eqKernel_size]
  have h := flatMap_getD (fun a ↦ (rowLowWeights zSkip low).1.map fun l ↦ l * a) _ hf (eqKernel low).toList m
    (by rw [hlen]; exact hm) x hx
  show ((eqKernel low).toList.flatMap fun a ↦ (rowLowWeights zSkip low).1.map fun l ↦ l * a).getD _ 0 = _
  rw [h, toList_getD (eqKernel low), eqKernel_getD _ hm]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hx, Option.map_some,
    Option.getD_some]

/-- `e(row) = lowWeights[row mod 64] · eq(chi_in, row / 64)` (`rowWeightsOf`'s entries). -/
def rowW (lowW chiIn : List E) (row : ℕ) : E := lowW.getD (row % 64) 0 * (eqKernel chiIn).getD (row / 64) 0

theorem rowWeightsOf_getD (lowW chiIn : List E) {row : ℕ} (h : row < 2 ^ 14) :
    (rowWeightsOf lowW chiIn).toArray.getD row 0 = rowW lowW chiIn row := by
  have h' : row < 2 ^ (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn) := h
  simp [rowWeightsOf, rowW, Array.getD_eq_getD_getElem?, h']

/-- **The rows' weights split**: at `row = x + 2^k row'`, `e(row) = skip[x] eq(row_low ++ chi_in, row')`. -/
theorem rowW_split (zSkip : Option E) (low chiIn : List E) (k : ℕ) (hk : k ≤ 6)
    (hskip : (rowLowWeights zSkip low).1.length = 2 ^ k) (hlow : low.length = 6 - k) (hin : chiIn.length = 8)
    {x row' : ℕ} (hx : x < 2 ^ k) (hrow' : row' < 2 ^ (14 - k)) :
    rowW (rowLowWeights zSkip low).2 chiIn (x + 2 ^ k * row') =
      (rowLowWeights zSkip low).1.getD x 0 * eqB (low ++ chiIn) row' := by
  have h6 : 2 ^ k * 2 ^ (6 - k) = 64 := by rw [← pow_add, show k + (6 - k) = 6 by omega]; rfl
  set m := row' % 2 ^ (6 - k)
  set bi := row' / 2 ^ (6 - k)
  have hrow : row' = m + 2 ^ (6 - k) * bi := (Nat.mod_add_div row' _).symm
  have hm : m < 2 ^ (6 - k) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbi : bi < 2 ^ 8 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, show 8 + (6 - k) = 14 - k by omega]; exact hrow'
  have hidx : x + 2 ^ k * row' = (x + 2 ^ k * m) + 64 * bi := by rw [hrow, ← h6]; ring
  have hlow64 : x + 2 ^ k * m < 64 := by
    calc x + 2 ^ k * m < 2 ^ k + 2 ^ k * m := by omega
      _ = 2 ^ k * (m + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ (6 - k) := Nat.mul_le_mul_left _ hm
      _ = 64 := h6
  have hmod : (x + 2 ^ k * row') % 64 = x + 2 ^ k * m := by
    rw [hidx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow64]
  have hdiv : (x + 2 ^ k * row') / 64 = bi := by
    rw [hidx, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hlow64, zero_add]
  unfold rowW
  rw [hmod, hdiv, show x + 2 ^ k * m = m * (rowLowWeights zSkip low).1.length + x by rw [hskip]; ring,
    lowW_getD zSkip low (by rw [hskip]; exact hx) (by rw [hlow]; exact hm), eqKernel_getD _ (by rw [hin]; exact hbi)]
  conv_rhs => rw [hrow, show 2 ^ (6 - k) = 2 ^ low.length by rw [hlow], eqB_append low chiIn (by rw [hlow]; exact hm)]
  ring

/-! ## The backward walks -/

/-- **The backward walk is `Aᵀ e`** (`cols_fst`), at a number. -/
theorem cols_fst_getD (e : CompPoly.CMlPolynomialEval E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn))
    {j : ℕ} (h : j < 2 ^ 14) :
    (flockR1cs.cols e).1.toArray.getD j 0 = ∑ row ∈ range (2 ^ 14), matE true row j * e.toArray.getD row 0 := by
  rw [vec_toArray_getD _ h]
  have hw := flockR1cs.cols_fst e ⟨j, h⟩
  rw [Fin.getElem_fin] at hw
  rw [hw, Finset.sum_range]
  refine Finset.sum_congr rfl fun row _ ↦ ?_
  have hr : row.val < 2 ^ 14 := row.isLt
  unfold matE
  rw [dite_cond_eq_true (eq_true ⟨hr, h⟩), vec_toArray_getD _ hr]
  simp only [ite_true, Fin.eta, Fin.getElem_fin]
  split <;> simp

/-- **The backward walk is `Bᵀ e`** (`cols_snd`), at a number. -/
theorem cols_snd_getD (e : CompPoly.CMlPolynomialEval E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn))
    {j : ℕ} (h : j < 2 ^ 14) :
    (flockR1cs.cols e).2.toArray.getD j 0 = ∑ row ∈ range (2 ^ 14), matE false row j * e.toArray.getD row 0 := by
  rw [vec_toArray_getD _ h]
  have hw := flockR1cs.cols_snd e ⟨j, h⟩
  rw [Fin.getElem_fin] at hw
  rw [hw, Finset.sum_range]
  refine Finset.sum_congr rfl fun row _ ↦ ?_
  have hr : row.val < 2 ^ 14 := row.isLt
  unfold matE
  rw [dite_cond_eq_true (eq_true ⟨hr, h⟩), vec_toArray_getD _ hr]
  simp only [Bool.false_eq_true, ite_false, Fin.eta, Fin.getElem_fin]
  split <;> simp

/-! ## `eq` -/

theorem ueq_gen : ∀ (L : List (E × E)) (c : E),
    L.foldl (fun acc (x, y) ↦ acc * (1 + x + y)) c = c * L.foldl (fun acc (x, y) ↦ acc * (1 + x + y)) 1
  | [], c => by simp
  | (u, v) :: L, c => by
    simp only [List.foldl_cons]
    rw [ueq_gen L (c * (1 + u + v)), ueq_gen L (1 * (1 + u + v))]
    ring

/-- **The verifier's `eqEval` is mumbai's.** -/
theorem eqEval_eq : ∀ (l r : List E), UniStatement.eqEval l r = LeanVM.Protocol.Verifier.eqEval l r
  | [], r => by cases r <;> simp [UniStatement.eqEval]
  | _ :: _, [] => by simp [UniStatement.eqEval]
  | x :: l, z :: r => by
    rw [LeanVM.Protocol.Whir.Complete.eqEval_cons, ← eqEval_eq l r]
    unfold UniStatement.eqEval
    rw [List.zip_cons_cons, List.foldl_cons, ueq_gen]
    simp only [one_mul]

/-- `Σ_h eq(p, h) eq(q, h) = eq(q, p)` for points of one length. -/
theorem sum_eqB_mul_eqB : ∀ (p q : List E), p.length = q.length →
    ∑ h ∈ range (2 ^ p.length), eqB p h * eqB q h = LeanVM.Protocol.Verifier.eqEval q p
  | [], [], _ => by simp
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | x :: p, z :: q, h => by
    have hl : p.length = q.length := by simpa using h
    rw [List.length_cons, pow_succ', UniComplete.sum_range_two_mul, LeanVM.Protocol.Whir.Complete.eqEval_cons,
      ← sum_eqB_mul_eqB p q hl, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [eqB_cons_even x p, eqB_cons_odd x p, eqB_cons_even z q, eqB_cons_odd z q]
    linear_combination (x * z * eqB p i * eqB q i) * two_eq_zero_E

end UniComplete.FlockP
