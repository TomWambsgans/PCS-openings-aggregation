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

end UniComplete.FlockP
