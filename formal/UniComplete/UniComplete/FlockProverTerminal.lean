-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The matrices are `formal/Lv42`'s (`blake2sFlockSpec.r1cs`,
-- leanerVM `mumbai` f0393df4's, MIT OR Apache-2.0) through `formal/UniStatement`'s `flockMatrixStack`.
import UniComplete.FlockProverShape

/-!
# The pending terminal: the tables' extensions are `Pending.terminal`'s factors

**`pendingTerminalHolds`**: at every point `r` of the batch, with `a`, `b` the multilinear extensions of `A0`, `B0`
at the matrices' claim's point `(ρ, row_low, chi_in, σ, chi_in')` (`(ρ, σ)` the first `k + 6` coordinates of `r`),
`Pending.terminal`'s value `(a + α b) L̂(ρ) ŝ(σ)` is the product of the extensions of the three tables the prover
hands the batch, at `(ρ, σ)` (`PendingTerminalHolds`), for any challenges. Its three factors:

* `mle_sliced`: `Ĝ'(ρ, σ) = Â0(ρ, row_low, chi_in, σ, chi_in') + α B̂0(…)`: the table is `A0`, `B0` summed against
  `eq` on the coordinates bound before (`row_low`, `chi_in` on the rows, `chi_in'` on the columns), so its extension
  at the rest is theirs (`sum_eqB_split` twice; the walks are `A W` by `BlockR1CS.rows_fst`, `rows_fst_getD`; the
  stacks' words are the matrices' entries, `matrixStack_getD`);
* `mle_skipTable`: `L̂` is the skip's weights on the low `k` coordinates, constant on the high `6`;
* `mle_sliceTable`: `ŝ` is the slices on the high `6`, constant on the low `k`.

The matrices' entries are `matE` (`0`/`1` in `E`, the `2^14 × 2^14` block); nothing evaluates them.
-/

namespace UniComplete.FlockP

open UniStatement UniStatement.Flock LeanVM.Parameters Finset

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The matrices at numbers -/

/-- `A0`'s (`left`) or `B0`'s entry at row `row`, column `col`, in `E` (`0` outside the block). -/
def matE (left : Bool) (row col : ℕ) : E :=
  if h : row < 2 ^ 14 ∧ col < 2 ^ 14 then
    (if (if left then flockR1cs.A ⟨row, h.1⟩ ⟨col, h.2⟩ else flockR1cs.B ⟨row, h.1⟩ ⟨col, h.2⟩) then 1 else 0)
  else 0

theorem ofK_one' : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem ofK_zero' : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem ofK_ite (c : Prop) [Decidable c] : ofK (if c then (1 : K) else 0) = if c then 1 else 0 := by
  split
  · exact ofK_one'
  · exact ofK_zero'

theorem flockMatrixStack_size (left : Bool) : (flockMatrixStack left).size = 2 ^ 28 := by
  unfold flockMatrixStack matrixStack
  exact Array.size_ofFn

/-- `Σ a + α Σ b = Σ (a + α b)`. -/
theorem sum_add_smul (alpha : E) (s : Finset ℕ) (a b : ℕ → E) :
    (∑ h ∈ s, a h) + alpha * ∑ h ∈ s, b h = ∑ h ∈ s, (a h + alpha * b h) := by
  rw [mul_sum, ← sum_add_distrib]

theorem vec_toArray_getD {n : ℕ} (v : Vector E n) {i : ℕ} (h : i < n) : v.toArray.getD i 0 = v[i] := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- **The forward walk is `A W`** (`rows_fst`), at a number. -/
theorem rows_fst_getD (W : CompPoly.CMlPolynomialEval E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn))
    {row : ℕ} (h : row < 2 ^ 14) :
    (flockR1cs.rows W).1.toArray.getD row 0 = ∑ j ∈ range (2 ^ 14), matE true row j * W.toArray.getD j 0 := by
  rw [vec_toArray_getD _ h]
  have hw := flockR1cs.rows_fst W ⟨row, h⟩
  rw [Fin.getElem_fin] at hw
  rw [hw, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : j.val < 2 ^ 14 := j.isLt
  unfold matE
  rw [dite_cond_eq_true (eq_true ⟨h, hj⟩), vec_toArray_getD _ hj]
  simp only [ite_true, Fin.eta, Fin.getElem_fin]
  split <;> simp

/-- **The forward walk is `B W`** (`rows_snd`), at a number. -/
theorem rows_snd_getD (W : CompPoly.CMlPolynomialEval E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn))
    {row : ℕ} (h : row < 2 ^ 14) :
    (flockR1cs.rows W).2.toArray.getD row 0 = ∑ j ∈ range (2 ^ 14), matE false row j * W.toArray.getD j 0 := by
  rw [vec_toArray_getD _ h]
  have hw := flockR1cs.rows_snd W ⟨row, h⟩
  rw [Fin.getElem_fin] at hw
  rw [hw, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : j.val < 2 ^ 14 := j.isLt
  unfold matE
  rw [dite_cond_eq_true (eq_true ⟨h, hj⟩), vec_toArray_getD _ hj]
  simp only [Bool.false_eq_true, ite_false, Fin.eta, Fin.getElem_fin]
  split <;> simp

/-- **The stack's word `w`** is the matrix entry at row `w mod 2^14`, column `w / 2^14`. -/
theorem matrixStack_getD (left : Bool) {w : ℕ} (hw : w < 2 ^ 28) :
    ((flockMatrixStack left).toList.map ofK).getD w 0 = matE left (w % 2 ^ 14) (w / 2 ^ 14 % 2 ^ 14) := by
  have hl : w < (flockMatrixStack left).size := by rw [flockMatrixStack_size]; exact hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hl,
    Option.map_some, Option.getD_some]
  have h1 : w % 2 ^ 14 < 2 ^ 14 := Nat.mod_lt _ (by norm_num)
  have h2 : w / 2 ^ 14 % 2 ^ 14 < 2 ^ 14 := Nat.mod_lt _ (by norm_num)
  unfold matE
  rw [dite_cond_eq_true (eq_true ⟨h1, h2⟩)]
  simp only [flockMatrixStack, matrixStack, Array.getElem_ofFn]
  split <;> rw [ofK_ite]

/-- **A matrix's extension**: `M̂(R, C) = Σ_{row, col} M[row][col] eq(R, row) eq(C, col)`. -/
theorem mle_matrixStack (left : Bool) (R C : List E) (hR : R.length = 14) (hC : C.length = 14) :
    multilinearEval ((flockMatrixStack left).toList.map ofK) (R ++ C) =
      ∑ col ∈ range (2 ^ 14), ∑ row ∈ range (2 ^ 14), matE left row col * (eqB R row * eqB C col) := by
  have hlen : ((flockMatrixStack left).toList.map ofK).length = 2 ^ (R ++ C).length := by
    rw [List.length_map, Array.length_toList, flockMatrixStack_size, List.length_append, hR, hC]
  rw [mle_eq_sum _ _ hlen, List.length_append, hR, hC, sum_split 14 14]
  refine sum_congr rfl fun col hcol ↦ sum_congr rfl fun row hrow ↦ ?_
  have hrow' := mem_range.mp hrow
  have hcol' := mem_range.mp hcol
  have hw : row + 2 ^ 14 * col < 2 ^ 28 := by
    calc row + 2 ^ 14 * col < 2 ^ 14 + 2 ^ 14 * col := by omega
      _ = 2 ^ 14 * (col + 1) := by ring
      _ ≤ 2 ^ 14 * 2 ^ 14 := Nat.mul_le_mul_left _ hcol'
      _ = 2 ^ 28 := by norm_num
  have e1 : (row + 2 ^ 14 * col) % 2 ^ 14 = row := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow']
  have e2 : (row + 2 ^ 14 * col) / 2 ^ 14 % 2 ^ 14 = col := by
    rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hrow', zero_add, Nat.mod_eq_of_lt hcol']
  rw [matrixStack_getD left hw, e1, e2]
  have := eqB_append R C (x := row) (by rw [hR]; exact hrow') col
  rw [hR] at this
  rw [this]

/-! ## Collapsing `eq` sums -/

/-- **Two `eq` sums are one**: `Σ_x eq(ρ, x) Σ_t eq(τ, t) F(x + 2^|ρ| t) = Σ_i eq(ρ ++ τ, i) F(i)`. -/
theorem sum_eqB_split (ρ τ : List E) (F : ℕ → E) :
    ∑ x ∈ range (2 ^ ρ.length), eqB ρ x * ∑ t ∈ range (2 ^ τ.length), eqB τ t * F (x + 2 ^ ρ.length * t) =
      ∑ i ∈ range (2 ^ (ρ.length + τ.length)), eqB (ρ ++ τ) i * F i := by
  rw [sum_split, sum_comm]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [eqB_append _ _ (mem_range.mp hx)]
  ring

/-! ## The tables' entries -/

/-- **`G'`'s entry** at `x + 2^k y`: `Σ_{row'} eq((row_low, chi_in), row') Σ_h (A + α B)[x + 2^k row'][y + 64 h]
eq(chi_in', h)`. -/
theorem sliced_getD (k : ℕ) (hk : k ≤ 14) (low chiIn chiInPrime : List E) (alpha : E)
    (hlc : (low ++ chiIn).length = 14 - k) (hcp : chiInPrime.length = 8) {x y : ℕ} (hx : x < 2 ^ k)
    (hy : y < 64) :
    (sliced k low chiIn chiInPrime alpha).getD (x + 2 ^ k * y) 0 =
      ∑ row' ∈ range (2 ^ (14 - k)), eqB (low ++ chiIn) row' *
        ∑ h ∈ range (2 ^ 8), eqB chiInPrime h *
          (matE true (x + 2 ^ k * row') (y + 64 * h) + alpha * matE false (x + 2 ^ k * row') (y + 64 * h)) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hi : x + 2 ^ k * y < 2 ^ k * kBits := by
    unfold kBits
    calc x + 2 ^ k * y < 2 ^ k + 2 ^ k * y := by omega
      _ = 2 ^ k * (y + 1) := by ring
      _ ≤ 2 ^ k * 64 := Nat.mul_le_mul_left _ hy
  have hdiv : (x + 2 ^ k * y) / 2 ^ k = y := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hx, zero_add]
  have hmod : (x + 2 ^ k * y) % 2 ^ k = x := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  unfold sliced
  rw [E2ECompleteness.getD_ofFn' _ hi]
  simp only [hdiv, hmod]
  rw [E2ECompleteness.getD_ofFn' _ (by unfold kBits; exact hy), E2ECompleteness.getD_ofFn' _ hx, sumTo_eq]
  refine sum_congr rfl fun row' hrow' ↦ ?_
  have hrow'' : row' < 2 ^ (low ++ chiIn).length := by rw [hlc]; exact mem_range.mp hrow'
  have hrow : x + 2 ^ k * row' < 2 ^ 14 := by
    have := mem_range.mp hrow'
    calc x + 2 ^ k * row' < 2 ^ k + 2 ^ k * row' := by omega
      _ = 2 ^ k * (row' + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ (14 - k) := Nat.mul_le_mul_left _ this
      _ = 2 ^ 14 := by rw [← pow_add]; congr 1; omega
  rw [eqKernel_getD _ hrow'', rows_fst_getD _ hrow, rows_snd_getD _ hrow]
  -- The column weights: `w[j] = eq(chi_in', j / 64)` at `j ≡ y mod 64`.
  have hcol : ∀ (left : Bool), ∑ j ∈ range (2 ^ 14), matE left (x + 2 ^ k * row') j *
      (Vector.ofFn (n := 2 ^ (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn)) fun j : Fin _ ↦
        if j.val % kBits = y then (eqKernel chiInPrime).getD (j.val / kBits) 0 else 0).toArray.getD j 0 =
      ∑ h ∈ range (2 ^ 8), eqB chiInPrime h * matE left (x + 2 ^ k * row') (y + 64 * h) := by
    intro left
    rw [show (14 : ℕ) = 6 + 8 by rfl, sum_split 6 8]
    refine sum_congr rfl fun h hh ↦ ?_
    have hh' := mem_range.mp hh
    rw [Finset.sum_eq_single y]
    · have hj : y + 2 ^ 6 * h < 2 ^ (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn) := by
        show y + 2 ^ 6 * h < 2 ^ 14
        calc y + 2 ^ 6 * h < 2 ^ 6 + 2 ^ 6 * h := by omega
          _ = 2 ^ 6 * (h + 1) := by ring
          _ ≤ 2 ^ 6 * 2 ^ 8 := Nat.mul_le_mul_left _ hh'
          _ = 2 ^ 14 := by norm_num
      rw [vec_toArray_getD _ hj, Vector.getElem_ofFn]
      have e1 : (y + 2 ^ 6 * h) % kBits = y := by
        unfold kBits; rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_of_lt_of_eq hy (by norm_num))]
      have e2 : (y + 2 ^ 6 * h) / kBits = h := by
        unfold kBits
        rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (lt_of_lt_of_eq hy (by norm_num)), zero_add]
      simp only [e1, e2, ite_true]
      rw [eqKernel_getD _ (by rw [hcp]; exact hh'), show (2 : ℕ) ^ 6 = 64 by rfl]
      ring
    · intro y' hy' hne
      have hy'' := mem_range.mp hy'
      have hj : y' + 2 ^ 6 * h < 2 ^ (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn) := by
        show y' + 2 ^ 6 * h < 2 ^ 14
        calc y' + 2 ^ 6 * h < 2 ^ 6 + 2 ^ 6 * h := by omega
          _ = 2 ^ 6 * (h + 1) := by ring
          _ ≤ 2 ^ 6 * 2 ^ 8 := Nat.mul_le_mul_left _ hh'
          _ = 2 ^ 14 := by norm_num
      rw [vec_toArray_getD _ hj, Vector.getElem_ofFn]
      have e1 : (y' + 2 ^ 6 * h) % kBits = y' := by
        unfold kBits; rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_of_lt_of_eq hy'' (by norm_num))]
      simp only [e1, hne, ite_false, mul_zero]
    · intro hy'
      exact absurd (mem_range.mpr (by norm_num; omega)) hy'
  rw [hcol true, hcol false, sum_add_smul]
  refine congrArg (eqB (low ++ chiIn) row' * ·) (sum_congr rfl fun h _ ↦ ?_)
  ring

/-! ## The tables' extensions -/

/-- **`Ĝ'(ρ, σ) = Â0(ρ, row_low, chi_in, σ, chi_in') + α B̂0(…)`.** -/
theorem mle_sliced (k : ℕ) (hk : k ≤ 6) (ρ σ low chiIn chiInPrime : List E) (alpha : E) (hρ : ρ.length = k)
    (hσ : σ.length = 6) (hlow : low.length = 6 - k) (hin : chiIn.length = 8) (hcp : chiInPrime.length = 8) :
    multilinearEval (sliced k low chiIn chiInPrime alpha).toList (ρ ++ σ) =
      multilinearEval ((flockMatrixStack true).toList.map ofK) (ρ ++ low ++ chiIn ++ σ ++ chiInPrime) +
        alpha * multilinearEval ((flockMatrixStack false).toList.map ofK) (ρ ++ low ++ chiIn ++ σ ++ chiInPrime) := by
  subst hρ
  have hlc : (low ++ chiIn).length = 14 - ρ.length := by rw [List.length_append, hlow, hin]; omega
  have hR : (ρ ++ (low ++ chiIn)).length = 14 := by rw [List.length_append, hlc]; omega
  have hC : (σ ++ chiInPrime).length = 14 := by rw [List.length_append, hσ, hcp]
  have hpt : ρ ++ low ++ chiIn ++ σ ++ chiInPrime = (ρ ++ (low ++ chiIn)) ++ (σ ++ chiInPrime) := by
    simp only [List.append_assoc]
  have hlen : (sliced ρ.length low chiIn chiInPrime alpha).toList.length = 2 ^ (ρ ++ σ).length := by
    simp only [sliced, Array.length_toList, Array.size_ofFn, List.length_append, hσ, kBits, pow_add]
    rfl
  -- `M(row, col) = (A + α B)[row][col]`.
  set M : ℕ → ℕ → E := fun row col ↦ matE true row col + alpha * matE false row col with hM
  have h14 : 2 ^ 14 = 2 ^ (ρ.length + (low ++ chiIn).length) := by rw [hlc]; congr 1; omega
  have hC14 : 2 ^ 14 = 2 ^ (σ.length + chiInPrime.length) := by rw [hσ, hcp]
  -- The right side: `Σ_row eq(R, row) Σ_col eq(C, col) M(row, col)`.
  have hRHS : multilinearEval ((flockMatrixStack true).toList.map ofK) (ρ ++ low ++ chiIn ++ σ ++ chiInPrime) +
      alpha * multilinearEval ((flockMatrixStack false).toList.map ofK) (ρ ++ low ++ chiIn ++ σ ++ chiInPrime) =
      ∑ row ∈ range (2 ^ 14), eqB (ρ ++ (low ++ chiIn)) row *
        ∑ col ∈ range (2 ^ 14), eqB (σ ++ chiInPrime) col * M row col := by
    rw [hpt, mle_matrixStack true _ _ hR hC, mle_matrixStack false _ _ hR hC, sum_add_smul]
    simp only [sum_add_smul]
    rw [sum_comm]
    refine sum_congr rfl fun row _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun col _ ↦ ?_
    simp only [hM]
    ring
  -- The left side: `Σ_y eq(σ, y) Σ_row eq(R, row) Σ_h eq(chi_in', h) M(row, y + 64 h)`.
  have hL : ∀ y ∈ range (2 ^ 6), ∑ x ∈ range (2 ^ ρ.length),
      (sliced ρ.length low chiIn chiInPrime alpha).toList.getD (x + 2 ^ ρ.length * y) 0 *
        eqB (ρ ++ σ) (x + 2 ^ ρ.length * y) =
      eqB σ y * ∑ row ∈ range (2 ^ 14), eqB (ρ ++ (low ++ chiIn)) row *
        ∑ h ∈ range (2 ^ 8), eqB chiInPrime h * M row (y + 64 * h) := by
    intro y hy
    have hy' : y < 64 := by simpa using mem_range.mp hy
    rw [h14, ← sum_eqB_split, mul_sum]
    refine sum_congr rfl fun x hx ↦ ?_
    have hx' : x < 2 ^ ρ.length := mem_range.mp hx
    rw [toList_getD, sliced_getD ρ.length (by omega) low chiIn chiInPrime alpha hlc hcp hx' hy',
      eqB_append _ _ hx', hlc]
    ring
  -- The columns' sum, split: `Σ_col eq(C, col) M(row, col) = Σ_y eq(σ, y) Σ_h eq(chi_in', h) M(row, y + 64 h)`.
  have hcolr : ∀ row, ∑ col ∈ range (2 ^ 14), eqB (σ ++ chiInPrime) col * M row col =
      ∑ y ∈ range (2 ^ 6), eqB σ y * ∑ h ∈ range (2 ^ 8), eqB chiInPrime h * M row (y + 64 * h) := by
    intro row
    have := sum_eqB_split σ chiInPrime (M row)
    rw [hσ, hcp] at this
    rw [show (2 : ℕ) ^ 14 = 2 ^ (6 + 8) by rfl, ← this]
    rfl
  rw [hRHS, mle_eq_sum _ _ hlen, List.length_append, hσ, sum_split, sum_congr rfl hL]
  refine Eq.trans ?_ (sum_congr rfl fun row _ ↦ by rw [hcolr row])
  -- Reorder: `Σ_y Σ_row = Σ_row Σ_y`.
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun row _ ↦ sum_congr rfl fun y _ ↦ sum_congr rfl fun h _ ↦ ?_
  ring

/-- **`L̂(ρ, σ) = skip(ρ)`**: the skip's weights on the low `k` coordinates. -/
theorem mle_skipTable (k : ℕ) (skip ρ σ : List E) (hρ : ρ.length = k) (hσ : σ.length = 6)
    (hskip : skip.length = 2 ^ k) :
    multilinearEval (skipTable k skip).toList (ρ ++ σ) = multilinearEval skip ρ := by
  subst hρ
  have h := mle_tensor (skipTable ρ.length skip).toList skip (List.replicate (2 ^ σ.length) 1) ρ σ
    (by simp [skipTable, hσ, kBits, pow_add]) (by rw [hskip]) (by simp)
    (fun x hx y hy ↦ by
      have hy' : y < 64 := by rw [hσ] at hy; simpa using hy
      have hi : x + 2 ^ ρ.length * y < 2 ^ ρ.length * kBits := by
        unfold kBits
        calc x + 2 ^ ρ.length * y < 2 ^ ρ.length + 2 ^ ρ.length * y := by omega
          _ = 2 ^ ρ.length * (y + 1) := by ring
          _ ≤ 2 ^ ρ.length * 64 := Nat.mul_le_mul_left _ hy'
      rw [toList_getD, skipTable, E2ECompleteness.getD_ofFn' _ hi]
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      rw [List.getD_eq_getElem?_getD (l := List.replicate _ _), List.getElem?_replicate]
      simp [hy])
  rw [h, mle_ones, mul_one]

/-- **`ŝ(ρ, σ) = s(σ)`**: the slices on the high `6` coordinates. -/
theorem mle_sliceTable (k : ℕ) (s ρ σ : List E) (hρ : ρ.length = k) (hσ : σ.length = 6) (hs : s.length = 64) :
    multilinearEval (sliceTable k s).toList (ρ ++ σ) = multilinearEval s σ := by
  subst hρ
  have h := mle_tensor (sliceTable ρ.length s).toList (List.replicate (2 ^ ρ.length) 1) s ρ σ
    (by simp [sliceTable, hσ, kBits, pow_add]) (by simp) (by rw [hs, hσ]; rfl)
    (fun x hx y hy ↦ by
      have hy' : y < 64 := by rw [hσ] at hy; simpa using hy
      have hi : x + 2 ^ ρ.length * y < 2 ^ ρ.length * kBits := by
        unfold kBits
        calc x + 2 ^ ρ.length * y < 2 ^ ρ.length + 2 ^ ρ.length * y := by omega
          _ = 2 ^ ρ.length * (y + 1) := by ring
          _ ≤ 2 ^ ρ.length * 64 := Nat.mul_le_mul_left _ hy'
      rw [toList_getD, sliceTable, E2ECompleteness.getD_ofFn' _ hi]
      simp only [Nat.add_mul_div_left _ _ (Nat.two_pow_pos ρ.length), Nat.div_eq_of_lt hx, zero_add]
      rw [List.getD_eq_getElem?_getD (l := List.replicate _ _), List.getElem?_replicate]
      simp [hx])
  rw [h, mle_ones, one_mul]

/-! ## `Pending.new`'s fields -/

theorem pending_k (z : Option E) (low ci cip : List E) (α r : E) (sl : Option (List E)) :
    (Pending.new z low ci cip α r sl).k = packing - low.length := rfl

theorem pending_alpha (z : Option E) (low ci cip : List E) (α r : E) (sl : Option (List E)) :
    (Pending.new z low ci cip α r sl).alpha = α := rfl

theorem pending_slices (z : Option E) (low ci cip : List E) (α r : E) (sl : Option (List E)) :
    (Pending.new z low ci cip α r sl).slices = sl := rfl

theorem pending_skipWeights (z : Option E) (low ci cip : List E) (α r : E) (sl : Option (List E)) :
    (Pending.new z low ci cip α r sl).skipWeights = (rowLowWeights z low).1 := rfl

theorem pending_rowLow (z : Option E) (low ci cip : List E) (α r : E) (sl : Option (List E)) :
    (Pending.new z low ci cip α r sl).rowLow = low := rfl

theorem pending_chiIn (z : Option E) (low ci cip : List E) (α r : E) (sl : Option (List E)) :
    (Pending.new z low ci cip α r sl).chiIn = ci := rfl

theorem pending_chiInPrime (z : Option E) (low ci cip : List E) (α r : E) (sl : Option (List E)) :
    (Pending.new z low ci cip α r sl).chiInPrime = cip := rfl

/-! ## The terminal -/

/-- **The pending terminal of `assemble`**, for any front with the shapes of the prover's. -/
theorem assemble_terminal (fr : Front) (s : List E) (e : End) (k : ℕ) (hk : k ≤ 6)
    (hlow : fr.rowLow.length = 6 - k) (hin : fr.chiIn.length = 8) (hinp : fr.chiInPrime.length = 8)
    (hs : s.length = 64) (hsl : fr.slices = some s) (hskip : (rowLowWeights fr.zSkip fr.rowLow).1.length = 2 ^ k)
    (hskip0 : k = 0 → (rowLowWeights fr.zSkip fr.rowLow).1 = [1]) :
    PendingTerminalHolds (assemble fr s e) := by
  have hk' : packing - fr.rowLow.length = k := by rw [hlow]; unfold packing; omega
  intro r hr
  have hr' : k + packing ≤ r.length := by simpa [assemble, hk'] using hr
  simp only [assemble, hk', Pending.terminal, Pending.matrixClaim, Pending.skipAt, Pending.rounds, pending_k,
    pending_alpha, pending_slices, pending_skipWeights, pending_rowLow, pending_chiIn, pending_chiInPrime, hsl,
    Option.getD_some]
  set ρ := (r.take (k + packing)).take k with hρdef
  set σ := (r.take (k + packing)).drop k with hσdef
  have htake : r.take (k + packing) = ρ ++ σ := (List.take_append_drop _ _).symm
  have hρ : ρ.length = k := by simp only [hρdef, List.length_take]; omega
  have hσ : σ.length = 6 := by simp only [hσdef, List.length_drop, List.length_take]; unfold packing at hr' ⊢; omega
  rw [htake, mle_sliced k hk ρ σ fr.rowLow fr.chiIn fr.chiInPrime fr.alpha hρ hσ hlow hin hinp,
    mle_skipTable k _ ρ σ hρ hσ hskip, mle_sliceTable k s ρ σ hρ hσ hs]
  congr 2
  by_cases h0 : 0 < k
  · rw [if_pos h0]
  · have hk0 : k = 0 := by omega
    rw [if_neg h0, hskip0 hk0]
    have : ρ = [] := List.eq_nil_of_length_eq_zero (by rw [hρ, hk0])
    rw [this]
    rfl

/-- **`PendingTerminalHolds` of the honest prover**, at a pure Keccak-256, any skip `k ≤ 6`, `log_n ≥ 14`, the
slices sent, for every writer (any challenges). -/
theorem pendingTerminalHolds (H : List UInt8 → Id LeanVM.Protocol.Digest) (logN : ℕ) (variant : Variant)
    (q : Array K) (w : Wr) (hk : variant.skip ≤ 6) (hN : 14 ≤ logN) (hc : variant.slices ≠ .claim) :
    PendingTerminalHolds ((flockProve H logN variant q).run w).1 := by
  obtain ⟨frs, e, hfrs, hout⟩ := flockProve_eq H logN variant q w
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := frontW_shape H logN variant q w hk hN
  rw [← hfrs] at h1 h2 h3 h4 h5 h6 h7
  rw [hout]
  refine assemble_terminal frs.1 frs.2 e variant.skip hk h1 h2 h3 h4 (h5 hc) ?_ ?_
  · by_cases h0 : 0 < variant.skip
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (h7 h0)
      rw [hz, rowLowWeights, h1]
      simp [lagrangeWeights, packing]
      omega
    · rw [h6 (by omega)]
      simp [rowLowWeights, h0, show variant.skip = 0 by omega]
  · intro h0
    rw [h6 h0]
    rfl

end UniComplete.FlockP
