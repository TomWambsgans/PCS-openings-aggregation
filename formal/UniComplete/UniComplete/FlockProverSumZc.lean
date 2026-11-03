-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The relation is `formal/Lv42`'s (`BlockR1CS.BatchHolds`,
-- `batchBlock`, `bitTable`; leanerVM `mumbai` f0393df4's, MIT OR Apache-2.0).
import UniComplete.FlockProverSumPure

/-!
# The zerocheck's values and the lincheck's first claim

* `zc_fold_eq`: the zerocheck's tables at the skip's point (`T_z(b) = Σ_x skip[x] T(x + 2^k b)`), folded at its point
  `chi = row_low ++ chi_in ++ chi_rest`, are `Σ_t eq(chi_rest, t) Σ_row e(row) T(row + 2^14 t)` (`e` the rows'
  weights);
* `lincheck_init`: the lincheck's first claim is its weights against its witness:
  `Σ_j W_j Ẑ_j = v_A + α v_B + α² v_C + α³ Ẑ_512`, `v_A = Σ_t eq(chi_rest, t) Σ_row e(row) (A z_t)(row)`;
* `blocks_hold`: Lv42's `BatchHolds` on `q_flock`'s bits is the R1CS on the prover's blocks (`blockOf`) and the pin.
-/

namespace UniComplete.FlockP

open UniStatement UniStatement.Flock LeanVM.Parameters Finset

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## Sums, generically -/

theorem sum_swap3 {R : Type*} [AddCommMonoid R] (a b c : ℕ) (f : ℕ → ℕ → ℕ → R) :
    ∑ j ∈ range a, ∑ row ∈ range b, ∑ t ∈ range c, f j row t =
      ∑ t ∈ range c, ∑ row ∈ range b, ∑ j ∈ range a, f j row t :=
  calc _ = ∑ row ∈ range b, ∑ j ∈ range a, ∑ t ∈ range c, f j row t := sum_comm
    _ = ∑ row ∈ range b, ∑ t ∈ range c, ∑ j ∈ range a, f j row t := sum_congr rfl fun _ _ ↦ sum_comm
    _ = _ := sum_comm

/-- **The adjoint swap**: `Σ_j (Σ_row M(row, j) e(row)) (Σ_t ε(t) z(t, j)) = Σ_t ε(t) Σ_row e(row) Σ_j M(row, j)
z(t, j)`. -/
theorem bilin_swap {R : Type*} [CommRing R] (a b c : ℕ) (M : ℕ → ℕ → R) (e ε : ℕ → R) (z : ℕ → ℕ → R) :
    ∑ j ∈ range a, (∑ row ∈ range b, M row j * e row) * (∑ t ∈ range c, ε t * z t j) =
      ∑ t ∈ range c, ε t * ∑ row ∈ range b, e row * ∑ j ∈ range a, M row j * z t j := by
  simp only [sum_mul_sum]
  simp only [mul_sum]
  rw [sum_swap3]
  refine sum_congr rfl fun t _ ↦ sum_congr rfl fun row _ ↦ sum_congr rfl fun j _ ↦ ?_
  ring

/-- The diagonal: `Σ_j e(j) Σ_t ε(t) z(t, j) = Σ_t ε(t) Σ_j e(j) z(t, j)`. -/
theorem diag_swap {R : Type*} [CommRing R] (a c : ℕ) (e ε : ℕ → R) (z : ℕ → ℕ → R) :
    ∑ j ∈ range a, e j * (∑ t ∈ range c, ε t * z t j) = ∑ t ∈ range c, ε t * ∑ j ∈ range a, e j * z t j := by
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ ↦ sum_congr rfl fun j _ ↦ ?_
  ring

/-! ## The witness -/

/-- The lincheck's witness at a position: `Ẑ_j = Σ_t eq(chi_rest, t) z_t(j)`. -/
theorem lincheckWitness_getD' (q : Array K) (chiRest : List E) {j : ℕ} (hj : j < 2 ^ 14) :
    (lincheckWitness q chiRest).getD j 0 = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t * zAt q t j := by
  have hj' : j < 2 ^ blake2sR1csLogSize := hj
  rw [lincheckWitness, E2ECompleteness.getD_ofFn' _ hj']
  simp only
  rw [sumTo_eq, eqKernel_size]
  exact sum_congr rfl fun t ht ↦ by rw [eqKernel_getD _ (mem_range.mp ht)]

theorem blockOf_getD (q : Array K) (t : ℕ) {j : ℕ} (hj : j < 2 ^ 14) : (blockOf q t).toArray.getD j 0 = zAt q t j := by
  have hj' : j < 2 ^ (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn) := hj
  simp [blockOf, Array.getD_eq_getD_getElem?, hj']

/-- `(A z_t)(row)`, the forward walk of block `t`. -/
def aZ (q : Array K) (t row : ℕ) : E := (flockR1cs.rows (blockOf q t)).1.toArray.getD row 0

/-- `(B z_t)(row)`. -/
def bZ (q : Array K) (t row : ℕ) : E := (flockR1cs.rows (blockOf q t)).2.toArray.getD row 0

theorem aZ_eq (q : Array K) (t : ℕ) {row : ℕ} (h : row < 2 ^ 14) :
    aZ q t row = ∑ j ∈ range (2 ^ 14), matE true row j * zAt q t j := by
  rw [aZ, rows_fst_getD _ h]
  exact sum_congr rfl fun j hj ↦ by rw [blockOf_getD _ _ (mem_range.mp hj)]

theorem bZ_eq (q : Array K) (t : ℕ) {row : ℕ} (h : row < 2 ^ 14) :
    bZ q t row = ∑ j ∈ range (2 ^ 14), matE false row j * zAt q t j := by
  rw [bZ, rows_snd_getD _ h]
  exact sum_congr rfl fun j hj ↦ by rw [blockOf_getD _ _ (mem_range.mp hj)]

/-! ## The lincheck's first claim -/

/-- **The lincheck's weights against its witness** are `v_A + α v_B + α² v_C + α³ Ẑ_512`. -/
theorem lincheck_init (q : Array K) (lowW chiIn chiRest : List E) (α : E) :
    ∑ j ∈ range (2 ^ 14), (lincheckWeights (rowWeightsOf lowW chiIn) α).getD j 0 *
        (lincheckWitness q chiRest).getD j 0 =
      (∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t * ∑ row ∈ range (2 ^ 14), rowW lowW chiIn row * aZ q t row) +
        α * (∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
          ∑ row ∈ range (2 ^ 14), rowW lowW chiIn row * bZ q t row) +
        epow α 2 * (∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
          ∑ row ∈ range (2 ^ 14), rowW lowW chiIn row * zAt q t row) +
        epow α 3 * (lincheckWitness q chiRest).getD 512 0 := by
  have hW : ∀ j ∈ range (2 ^ 14), (lincheckWeights (rowWeightsOf lowW chiIn) α).getD j 0 *
      (lincheckWitness q chiRest).getD j 0 =
      (∑ row ∈ range (2 ^ 14), matE true row j * rowW lowW chiIn row) *
          (∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t * zAt q t j) +
        α * ((∑ row ∈ range (2 ^ 14), matE false row j * rowW lowW chiIn row) *
          (∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t * zAt q t j)) +
        epow α 2 * (rowW lowW chiIn j * (∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t * zAt q t j)) +
        (if j = 512 then epow α 3 * (lincheckWitness q chiRest).getD 512 0 else 0) := by
    intro j hj
    have hj' := mem_range.mp hj
    rw [W_getD lowW chiIn α hj', lincheckWitness_getD' q chiRest hj']
    by_cases h5 : j = 512
    · subst h5
      rw [if_pos rfl, if_pos rfl, lincheckWitness_getD' q chiRest (by norm_num)]
      ring
    · rw [if_neg h5, if_neg h5]
      ring
  have hA : ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t * ∑ row ∈ range (2 ^ 14),
      rowW lowW chiIn row * aZ q t row = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 14), rowW lowW chiIn row * ∑ j ∈ range (2 ^ 14), matE true row j * zAt q t j :=
    sum_congr rfl fun t _ ↦ congrArg (eqB chiRest t * ·) (sum_congr rfl fun row hr ↦ by
      rw [aZ_eq q t (mem_range.mp hr)])
  have hB : ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t * ∑ row ∈ range (2 ^ 14),
      rowW lowW chiIn row * bZ q t row = ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 14), rowW lowW chiIn row * ∑ j ∈ range (2 ^ 14), matE false row j * zAt q t j :=
    sum_congr rfl fun t _ ↦ congrArg (eqB chiRest t * ·) (sum_congr rfl fun row hr ↦ by
      rw [bZ_eq q t (mem_range.mp hr)])
  have h512 : (512 : ℕ) ∈ range (2 ^ 14) := by simp
  rw [hA, hB]
  have e1 := bilin_swap (2 ^ 14) (2 ^ 14) (2 ^ chiRest.length) (fun row j ↦ matE true row j) (rowW lowW chiIn)
    (eqB chiRest) (fun t j ↦ zAt q t j)
  have e2 := bilin_swap (2 ^ 14) (2 ^ 14) (2 ^ chiRest.length) (fun row j ↦ matE false row j) (rowW lowW chiIn)
    (eqB chiRest) (fun t j ↦ zAt q t j)
  have e3 := diag_swap (2 ^ 14) (2 ^ chiRest.length) (rowW lowW chiIn) (eqB chiRest) (fun t j ↦ zAt q t j)
  beta_reduce at e1 e2 e3
  conv_lhs => rw [sum_congr rfl hW, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_ite_eq' (range (2 ^ 14)) 512, if_pos h512]
  rw [e1, e2, e3]

/-! ## The zerocheck's values -/

/-- **The zerocheck's tables at its point**: a table at the skip's point (`T_z(b) = Σ_x skip[x] T(x + 2^k b)`),
folded at `chi = row_low ++ chi_in ++ chi_rest`, is `Σ_t eq(chi_rest, t) Σ_row e(row) T(row + 2^14 t)`. -/
theorem zc_fold_eq (zSkip : Option E) (low chiIn chiRest : List E) (k : ℕ) (hk : k ≤ 6)
    (hskip : (rowLowWeights zSkip low).1.length = 2 ^ k) (hlow : low.length = 6 - k) (hin : chiIn.length = 8)
    (T Tz : Array E) (hTz : Tz.size = 2 ^ (low ++ chiIn ++ chiRest).length)
    (hTzE : ∀ b < 2 ^ (low ++ chiIn ++ chiRest).length,
      Tz.getD b 0 = ∑ x ∈ range (2 ^ k), (rowLowWeights zSkip low).1.getD x 0 * T.getD (x + 2 ^ k * b) 0) :
    ((low ++ chiIn ++ chiRest).foldl foldE Tz).getD 0 0 =
      ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t *
        ∑ row ∈ range (2 ^ 14), rowW (rowLowWeights zSkip low).2 chiIn row * T.getD (row + 2 ^ 14 * t) 0 := by
  have hlc : (low ++ chiIn).length = 14 - k := by rw [List.length_append, hlow, hin]; omega
  have h14 : 2 ^ (k + (14 - k)) = 2 ^ 14 := by rw [show k + (14 - k) = 14 by omega]
  rw [foldl_foldE_getD _ _ hTz, List.length_append, sum_split (low ++ chiIn).length chiRest.length]
  refine sum_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  calc ∑ b ∈ range (2 ^ (low ++ chiIn).length), eqB (low ++ chiIn ++ chiRest) (b + 2 ^ (low ++ chiIn).length * t) *
        Tz.getD (b + 2 ^ (low ++ chiIn).length * t) 0
      = eqB chiRest t * ∑ b ∈ range (2 ^ (14 - k)), ∑ x ∈ range (2 ^ k),
          rowW (rowLowWeights zSkip low).2 chiIn (x + 2 ^ k * b) * T.getD ((x + 2 ^ k * b) + 2 ^ 14 * t) 0 := by
        rw [mul_sum, hlc]
        refine sum_congr rfl fun b hb ↦ ?_
        have hb' := mem_range.mp hb
        have hbt : b + 2 ^ (14 - k) * t < 2 ^ (low ++ chiIn ++ chiRest).length := by
          rw [List.length_append, hlc, pow_add]
          calc b + 2 ^ (14 - k) * t < 2 ^ (14 - k) + 2 ^ (14 - k) * t := by omega
            _ = 2 ^ (14 - k) * (t + 1) := by ring
            _ ≤ 2 ^ (14 - k) * 2 ^ chiRest.length := Nat.mul_le_mul_left _ ht'
        have hap := eqB_append (low ++ chiIn) chiRest (x := b) (by rw [hlc]; exact hb') t
        rw [hlc] at hap
        rw [hap, hTzE _ hbt, mul_sum, mul_sum]
        refine sum_congr rfl fun x hx ↦ ?_
        rw [rowW_split zSkip low chiIn k hk hskip hlow hin (mem_range.mp hx) hb',
          show x + 2 ^ k * (b + 2 ^ (14 - k) * t) = (x + 2 ^ k * b) + 2 ^ 14 * t by
            rw [← h14, pow_add]; ring]
        ring
    _ = eqB chiRest t * ∑ row ∈ range (2 ^ 14), rowW (rowLowWeights zSkip low).2 chiIn row *
          T.getD (row + 2 ^ 14 * t) 0 := by
        rw [← h14, sum_split k (14 - k)]

/-! ## The relation on the prover's blocks -/

/-- **Lv42's block is the prover's**: `batchBlock (bitTable q_flock) t = blockOf q t`. -/
theorem batchBlock_eq (κ : ℕ) (q : Array K) (t : Fin (2 ^ κ)) :
    Lv42.Protocol.BlockR1CS.batchBlock (s := Lv42.Parameters.Flock.kSkip) (m := Lv42.Parameters.Flock.kIn)
      (Lv42.Protocol.bitTable (colOf κ q)) t = blockOf q t.val := by
  apply Vector.ext
  intro j hj
  have hj' : j < 2 ^ 14 := hj
  have h64 : j % 64 < 2 ^ Lv42.Parameters.Flock.kSkip := Nat.mod_lt _ (by decide)
  have hd : j / 64 < 2 ^ Lv42.Parameters.Flock.kIn := by
    show j / 64 < 2 ^ 8
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hj' (by norm_num)
  have e : j % 64 + 2 ^ Lv42.Parameters.Flock.kSkip * (j / 64) = j := by
    show j % 64 + 2 ^ 6 * (j / 64) = j
    omega
  have h := Lv42.Protocol.BlockR1CS.batchBlock_cubeIndex (s := Lv42.Parameters.Flock.kSkip)
    (m := Lv42.Parameters.Flock.kIn) (Lv42.Protocol.bitTable (colOf κ q)) t ⟨j % 64, h64⟩ ⟨j / 64, hd⟩
  simp only [Fin.getElem_fin, LeanVM.Protocol.cubeIndex_val] at h
  simp only [e] at h
  rw [h]
  simp only [blockOf, Lv42.Protocol.bitTable, colOf, Vector.getElem_ofFn, Fin.getElem_fin, Vector.get_eq_getElem,
    LeanVM.Protocol.cubeIndex_val]
  rfl

/-- **The R1CS on the prover's blocks**: from `FlockHolds`, for every block `t < 2^κ`, `A z_t ∘ B z_t = z_t` and
the pin `z_t(512) = 1`. -/
theorem blocks_hold (κ : ℕ) (q : Array K) (hF : FlockHolds κ q) {t : ℕ} (ht : t < 2 ^ κ) :
    (∀ row < 2 ^ 14, aZ q t row * bZ q t row = zAt q t row) ∧ zAt q t 512 = 1 := by
  obtain ⟨hH, hP⟩ := hF ⟨t, ht⟩
  rw [batchBlock_eq] at hH hP
  refine ⟨fun row hrow ↦ ?_, ?_⟩
  · have := hH ⟨row, hrow⟩
    rw [aZ, bZ, vec_toArray_getD _ hrow, vec_toArray_getD _ hrow, ← blockOf_getD q t hrow,
      vec_toArray_getD _ hrow]
    simpa only [Fin.getElem_fin] using this
  · rw [← blockOf_getD q t (by norm_num), vec_toArray_getD _ (by norm_num)]
    simpa only [Lv42.Parameters.Flock.constPos, Fin.getElem_fin] using hP

/-- **The witness at the constant position** is `1`: `Ẑ_512 = Σ_t eq(chi_rest, t) = 1`. -/
theorem lincheckWitness_pin (κ : ℕ) (q : Array K) (hF : FlockHolds κ q) (chiRest : List E)
    (hcr : chiRest.length = κ) : (lincheckWitness q chiRest).getD 512 0 = 1 := by
  rw [lincheckWitness_getD' q chiRest (by norm_num), ← sum_eqB chiRest]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [(blocks_hold κ q hF (by rw [← hcr]; exact mem_range.mp ht)).2, mul_one]

end UniComplete.FlockP
