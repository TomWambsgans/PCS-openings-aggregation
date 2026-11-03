-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.FlockProverSumBasic

/-!
# The pending claim is the tables' product sum, given the lincheck's last claim

**`pendingSum_pure`**: if the lincheck's last claim `r_lc` is `Σ_y W'_y s_y` (the weights `W` and the witness folded
by its round challenges, `s` the slices), then `Pending.new`'s claim `r_lc + α² eq(chi_in, chi_in') Σ_y e_y s_y +
α³ eq(bits 8, chi_in') s_0` is `Σ_i G'_i L̂_i ŝ_i` over the prover's tables. In characteristic two the known terms
cancel the weights' `C = I` and pin parts (`W = Aᵀe + α Bᵀe + α² e + α³ [· = 512]`), and what is left is
`Σ_y s_y Σ_h eq(chi_in', h) Σ_row e(row) (A + α B)[row][y + 64 h]`, which is the tables' sum
(`sliced_getD`, `rowW_split`).
-/

namespace UniComplete.FlockP

open UniStatement UniStatement.Flock LeanVM.Parameters Finset
open LeanVM.Protocol.EndToEnd (boolPoint)

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The verifier's helpers -/

theorem udot_gen : ∀ (L : List (E × E)) (c : E),
    L.foldl (fun acc (x, y) ↦ acc + x * y) c = c + L.foldl (fun acc (x, y) ↦ acc + x * y) 0
  | [], c => by simp
  | (u, v) :: L, c => by
    simp only [List.foldl_cons]
    rw [udot_gen L (c + u * v), udot_gen L (0 + u * v)]
    ring

/-- **`dot` is the sum of products.** -/
theorem dot_eq : ∀ (l r : List E), l.length = r.length →
    UniStatement.dot l r = ∑ i ∈ range l.length, l.getD i 0 * r.getD i 0
  | [], _, _ => by simp [UniStatement.dot]
  | _ :: _, [], h => absurd h (by simp)
  | x :: l, z :: r, h => by
    have hl : l.length = r.length := by simpa using h
    unfold UniStatement.dot
    rw [List.zip_cons_cons, List.foldl_cons, udot_gen, List.length_cons, sum_range_succ']
    have ih := dot_eq l r hl
    unfold UniStatement.dot at ih
    rw [ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add]
    ring

/-- `Pending.new`'s claim with the slices sent. -/
theorem pending_claim (z : Option E) (low ci cip : List E) (α rLc : E) (s : List E) :
    (Pending.new z low ci cip α rLc (some s)).claim =
      rLc + (epow α 2 * UniStatement.eqEval ci cip * UniStatement.dot (rowLowWeights z low).2 s +
        epow α 3 * UniStatement.eqEval ((List.range lincheckRounds).map (bitE (constantColumn / kBits))) cip *
          s.getD (constantColumn % kBits) 0) := rfl

theorem constantBits_eq : (List.range lincheckRounds).map (bitE (constantColumn / kBits)) = boolPoint 8 8 := rfl

/-! ## The weights -/

/-- **The lincheck's weights** at a position: `(Aᵀe)_j + α (Bᵀe)_j + α² e_j + α³ [j = 512]`. -/
theorem W_getD (lowW chiIn : List E) (α : E) {j : ℕ} (hj : j < 2 ^ 14) :
    (lincheckWeights (rowWeightsOf lowW chiIn) α).getD j 0 =
      (∑ row ∈ range (2 ^ 14), matE true row j * rowW lowW chiIn row) +
        α * (∑ row ∈ range (2 ^ 14), matE false row j * rowW lowW chiIn row) +
        epow α 2 * rowW lowW chiIn j + (if j = 512 then epow α 3 else 0) := by
  have hj' : j < 2 ^ blake2sR1csLogSize := hj
  rw [lincheckWeights, E2ECompleteness.getD_ofFn' _ hj']
  simp only
  rw [cols_fst_getD _ hj, cols_snd_getD _ hj, rowWeightsOf_getD _ _ hj]
  have e1 : ∀ left, ∑ row ∈ range (2 ^ 14), matE left row j * (rowWeightsOf lowW chiIn).toArray.getD row 0 =
      ∑ row ∈ range (2 ^ 14), matE left row j * rowW lowW chiIn row := fun left ↦
    sum_congr rfl fun row hr ↦ by rw [rowWeightsOf_getD _ _ (mem_range.mp hr)]
  rw [e1 true, e1 false]
  rfl

/-- `e(y + 64 h) = lowW[y] eq(chi_in, h)`. -/
theorem rowW_high (lowW chiIn : List E) (hin : chiIn.length = 8) {y h : ℕ} (hy : y < 64) (hh : h < 2 ^ 8) :
    rowW lowW chiIn (y + 2 ^ 6 * h) = lowW.getD y 0 * eqB chiIn h := by
  unfold rowW
  have e1 : (y + 2 ^ 6 * h) % 64 = y := by
    rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simpa using hy)]
  have e2 : (y + 2 ^ 6 * h) / 64 = h := by
    rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by simpa using hy),
      zero_add]
  rw [e1, e2, eqKernel_getD _ (by rw [hin]; exact hh)]

/-- The pin's weights folded: `Σ_h eq(p, h) [y + 64 h = 512] = [y = 0] eq(p, 8)`. -/
theorem sum_pin (p : List E) (c : E) {y : ℕ} (hy : y < 64) :
    ∑ h ∈ range (2 ^ 8), eqB p h * (if y + 2 ^ 6 * h = 512 then c else 0) = if y = 0 then eqB p 8 * c else 0 := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [Finset.sum_eq_single 8]
    · simp
    · intro h _ hne
      rw [if_neg (by omega), mul_zero]
    · intro h; exact absurd (mem_range.mpr (by norm_num)) h
  · rw [if_neg hy0]
    refine sum_eq_zero fun h _ ↦ ?_
    rw [if_neg (by omega), mul_zero]

/-- The low weights have `64` entries. -/
theorem lowW_length (zSkip : Option E) (low : List E) (k : ℕ) (hk : k ≤ 6)
    (hskip : (rowLowWeights zSkip low).1.length = 2 ^ k) (hlow : low.length = 6 - k) :
    (rowLowWeights zSkip low).2.length = 64 := by
  show ((eqKernel low).toList.flatMap fun a ↦ (rowLowWeights zSkip low).1.map fun l ↦ l * a).length = 64
  rw [List.length_flatMap]
  simp only [List.length_map, hskip, List.map_const', List.sum_replicate, Array.length_toList, eqKernel_size,
    hlow, smul_eq_mul]
  rw [← pow_add, show 6 - k + k = 6 by omega]
  rfl

/-- `Mf(y) = Σ_h eq(chi_in', h) Σ_row (A + α B)[row][y + 64 h] e(row)`: what the pending claim weighs the slices
by. -/
def Mf (lowW chiIn cip : List E) (α : E) (y : ℕ) : E :=
  ∑ h ∈ range (2 ^ 8), eqB cip h * ∑ row ∈ range (2 ^ 14),
    (matE true row (y + 2 ^ 6 * h) + α * matE false row (y + 2 ^ 6 * h)) * rowW lowW chiIn row

/-- **The pending claim** is `Σ_y s_y Mf(y)`, given the lincheck's last claim. -/
theorem pending_claim_eq (k : ℕ) (hk : k ≤ 6) (zSkip : Option E) (low chiIn χs : List E) (α rLc : E) (s : List E)
    (hskip : (rowLowWeights zSkip low).1.length = 2 ^ k) (hlow : low.length = 6 - k) (hin : chiIn.length = 8)
    (hχ : χs.length = 8) (hs : s.length = 64)
    (hrLc : rLc = ∑ y ∈ range 64,
      (χs.foldl foldHigh (lincheckWeights (rowWeightsOf (rowLowWeights zSkip low).2 chiIn) α)).getD y 0 *
        s.getD y 0) :
    (Pending.new zSkip low chiIn χs.reverse α rLc (some s)).claim =
      ∑ y ∈ range 64, s.getD y 0 * Mf (rowLowWeights zSkip low).2 chiIn χs.reverse α y := by
  set lowW := (rowLowWeights zSkip low).2 with hlowW
  have hcip : χs.reverse.length = 8 := by rw [List.length_reverse, hχ]
  have hWsize : (lincheckWeights (rowWeightsOf lowW chiIn) α).size = 2 ^ (χs.length + 6) := by
    simp [lincheckWeights, hχ, blake2sR1csLogSize]
  -- The folded weights at `y`.
  have hWf : ∀ y < 64, (χs.foldl foldHigh (lincheckWeights (rowWeightsOf lowW chiIn) α)).getD y 0 =
      Mf lowW chiIn χs.reverse α y + epow α 2 * (lowW.getD y 0 * LeanVM.Protocol.Verifier.eqEval chiIn χs.reverse) +
        (if y = 0 then eqB χs.reverse 8 * epow α 3 else 0) := by
    intro y hy
    rw [foldl_foldHigh_getD χs 6 _ hWsize y (by simpa using hy), hχ, ← sum_eqB_mul_eqB χs.reverse chiIn
      (by rw [hcip, hin]), hcip, ← sum_pin χs.reverse (epow α 3) hy, Mf, mul_sum, mul_sum, ← sum_add_distrib,
      ← sum_add_distrib]
    refine sum_congr rfl fun h hh ↦ ?_
    have hh' := mem_range.mp hh
    have hj : y + 2 ^ 6 * h < 2 ^ 14 := by
      calc y + 2 ^ 6 * h < 2 ^ 6 + 2 ^ 6 * h := by omega
        _ = 2 ^ 6 * (h + 1) := by ring
        _ ≤ 2 ^ 6 * 2 ^ 8 := Nat.mul_le_mul_left _ hh'
        _ = 2 ^ 14 := by norm_num
    rw [W_getD lowW chiIn α hj, rowW_high lowW chiIn hin hy hh', sum_add_smul]
    have e3 : ∀ row ∈ range (2 ^ 14), (matE true row (y + 2 ^ 6 * h) * rowW lowW chiIn row +
        α * (matE false row (y + 2 ^ 6 * h) * rowW lowW chiIn row)) =
        (matE true row (y + 2 ^ 6 * h) + α * matE false row (y + 2 ^ 6 * h)) * rowW lowW chiIn row :=
      fun row _ ↦ by ring
    rw [sum_congr rfl e3]
    ring
  rw [pending_claim, hrLc, dot_eq lowW s (by rw [lowW_length zSkip low k hk hskip hlow, hs]),
    lowW_length zSkip low k hk hskip hlow, constantBits_eq, eqEval_eq, eqEval_eq,
    show constantColumn % kBits = 0 by rfl,
    sum_congr rfl fun y hy ↦ by rw [hWf y (mem_range.mp hy)]]
  have hpin : LeanVM.Protocol.Verifier.eqEval (boolPoint 8 8) χs.reverse = eqB χs.reverse 8 := by
    rw [eqB, hcip]
  rw [hpin]
  simp only [add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq', mem_range, show (0 : ℕ) < 64 by norm_num,
    ite_true]
  rw [show ∑ y ∈ range 64, epow α 2 * (lowW.getD y 0 * LeanVM.Protocol.Verifier.eqEval chiIn χs.reverse) *
      s.getD y 0 = epow α 2 * LeanVM.Protocol.Verifier.eqEval chiIn χs.reverse * ∑ y ∈ range 64, lowW.getD y 0 *
        s.getD y 0 by rw [mul_sum]; exact sum_congr rfl fun y _ ↦ by ring]
  have hcomm : ∑ y ∈ range 64, Mf lowW chiIn χs.reverse α y * s.getD y 0 =
      ∑ y ∈ range 64, s.getD y 0 * Mf lowW chiIn χs.reverse α y := sum_congr rfl fun y _ ↦ by ring
  rw [hcomm]
  linear_combination (epow α 2 * LeanVM.Protocol.Verifier.eqEval chiIn χs.reverse *
    ∑ y ∈ range 64, lowW.getD y 0 * s.getD y 0 + eqB χs.reverse 8 * epow α 3 * s.getD 0 0) * two_eq_zero_E

end UniComplete.FlockP
