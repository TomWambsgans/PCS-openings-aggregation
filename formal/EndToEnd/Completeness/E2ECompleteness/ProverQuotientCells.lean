-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The quotient table's computations on the cells (`ProverDefs.lean`'s `hValues`) against
-- `formal/QuotientSecurity`'s honest second message. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the fields `K`, `E`.
import E2ECompleteness.ProverQuotientCoset

/-!
# The prover's sum on the cells is F1's `h₀`

`hValues` (`ProverDefs.lean`) computes, at cell `i`, `1/(α + w_i + β B(i)) + 1/(α + w_i + β B(σ(i)))`
plus the public weight `publicCellWeight i γ` times the cell on the public region. Here, for the
cells `f` given as an array and the deployed σ given as one:

* `pub_cell`: `publicCellWeight` is F1's public weight `pub γ` at the cell's point (zero off the
  region): the product of the weights of the cell's set bits is `bit_weight` of the bit it reads
  (`regionWeight_coordWeight`);
* `hValues_cell`: `hValues` at cell `idx x` is F1's `sumValue` at the cell `x`;
* **`hHat_table`**: the table `coefficients 24 0 hValues` holds F1's honest `h₀` (the
  interpolation of `sumValue` on the cells, `Lagrange.eq_interpolate_of_eval_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness

namespace ProverQuotient

open ProverTables

/-- **The honest first message** of the cells `f` and the masks (`formal/Completeness`'s
`honestG`): the row polynomials of `witnessTable deployedBasis f masks`. -/
noncomputable def gOf (f : (Fin (22 + 2) → Bool) → K) (masks : PcsQuotient.Masks) :
    Fin 4 → E[X] :=
  witnessOfTable fun b ↦ algebraMap K E (Completeness.witnessTable deployedBasis f masks b)

/-- The deployed instance's points in `E`. -/
theorem basis_point (hK : Constants) (x : Fin (22 + 2) → Bool) :
    Completeness.deployedInstanceE.basis.point x = ofK (point (Completeness.idx x)) := by
  rw [Completeness.point_map (algebraMap K E) deployedBasis _ (fun _ => rfl), ← point_idx hK]
  rfl

theorem pt_cellEquiv (hK : Constants) (x : Fin (22 + 2) → Bool) :
    Completeness.deployedInstanceE.params.pt (Completeness.deployedInstanceE.cellEquiv x) =
      ofK (point (Completeness.idx x)) := by
  rw [← basis_point hK]
  exact cantorCells_point (n := 22) _ le24 x

/-- **The honest cells** are the values the table was built from. -/
theorem cells_cellEquiv (f : (Fin (22 + 2) → Bool) → K) (masks : PcsQuotient.Masks)
    (x : Fin (22 + 2) → Bool) :
    Completeness.deployedInstanceE.params.cells (gOf f masks)
      (Completeness.deployedInstanceE.cellEquiv x) = ofK (f x) := by
  rw [← Completeness.deployedInstanceE.cellsOf_eq]
  exact Completeness.cellsOf_honest (algebraMap K E) Completeness.deployedInstanceE deployedBasis
    (fun _ => rfl) f masks x

/-! ## The public weight on the cells -/

theorem or_mul_two (a m : ℕ) (ha : a < 2) : a ||| (m * 2) = a + 2 * m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, show a + 2 * m = 2 ^ 1 * m + a by ring,
    Nat.testBit_two_pow_mul_add m (by simpa using ha), show m * 2 = 2 ^ 1 * m by ring,
    Nat.testBit_two_pow_mul]
  rcases i with _ | i
  · simp
  · have : a.testBit (i + 1) = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le ha (by calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this]

/-- The bit `publicCellWeight` reads. -/
theorem pcw_bit (n : ℕ) : ((n &&& 1) ||| (((n >>> 2) &&& 63) <<< 1)) = n % 2 + 2 * (n / 4 % 64) := by
  rw [Nat.and_one_is_mod, show (63 : ℕ) = 2 ^ 6 - 1 from rfl, Nat.shiftRight_eq_div_pow,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, pow_one,
    or_mul_two _ _ (Nat.mod_lt _ (by norm_num))]

/-- `bit_weight` (the Statement's) is `bitWeight F192.G F192.Y`. -/
theorem bitWeight_stmt {j : ℕ} (hj : j < 128) :
    PcsQuotient.bitWeight j = QuotientSecurity.bitWeight Primitives.F192.G Primitives.F192.Y j := by
  rw [bitWeight_eq', bitWeight_eq j hj, rustBitWeight_eq j hj]

/-- **F1's public weight at cell `n` is `publicCellWeight n`** on the public region, zero off it. -/
theorem pub_cell_nat (hK : Constants) (γ : E) {n : ℕ} (hn24 : n < 2 ^ (22 + 2)) :
    (Completeness.deployedInstanceE.params.pub γ).eval (ofK (point n)) =
      if n < 2 ^ PcsQuotient.region then PcsQuotient.publicCellWeight n γ else 0 := by
  have hidx : Completeness.idx (cellOf n) = n := Completeness.idx_bitsOf _ n hn24
  have e : ofK (point n) = Completeness.deployedInstanceE.basis.point (cellOf n) := by
    rw [basis_point hK, hidx]
  have hpub := pubProd_point Completeness.deployedInstanceE.basis
    (invSeq Completeness.deployedInstanceE.basis.β) (regionMu Completeness.deployedInstanceE.c) le24
    (by norm_num : 11 ≤ 22 + 2) (invSeq_zero _)
    (fun d hd _ => invSeq_sum Completeness.deployedInstanceE.basis.β
      Completeness.deployedInstanceE.basis.zero d hd) γ (cellOf n)
  rw [e, show Completeness.deployedInstanceE.params.pub γ =
      pubProd (invSeq Completeness.deployedInstanceE.basis.β)
        (regionMu Completeness.deployedInstanceE.c) 11 (22 + 2) γ from rfl, hpub, region_weights,
    Completeness.deployedInstanceE_c]
  simp only [regionWeight_cellOf _ _ n hn24]
  rw [show PcsQuotient.region = 11 from rfl]
  by_cases h11 : n < 2 ^ 11
  · rw [if_pos h11, Finset.sum_eq_single (⟨n / 256, by omega⟩ : Fin 8)
      (fun J _ hJ => by
        rw [if_neg (fun h => hJ (Fin.ext h.2.symm)), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), if_pos ⟨h11, rfl⟩]
    unfold PcsQuotient.publicCellWeight
    have hand2 : n &&& 2 = (n.testBit 1).toNat * 2 := by
      have := Nat.and_two_pow n 1
      rwa [pow_one] at this
    rw [hand2, pcw_bit, Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 8 = 256 from rfl]
    by_cases ht : n.testBit 1 = true
    · rw [ht, Finset.prod_eq_zero (i := 1) (by simp) (by rw [if_pos ht, coordWeight_one])]
      simp
    · have ht' : n.testBit 1 = false := by simpa using ht
      have h2 : n / 2 % 2 = 0 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at ht'
        simp only [pow_one, decide_eq_false_iff_not] at ht'
        omega
      rw [ht']
      simp only [Bool.toNat_false, zero_mul, ne_eq, not_true_eq_false, ↓reduceIte]
      have hj : n % 2 + 2 * (n / 4 % 64) < 128 := by omega
      have hcell : cellOf n = pubCell ⟨n / 256, by omega⟩ ⟨n % 2 + 2 * (n / 4 % 64), hj⟩ := by
        rw [pubCell_eq_cellOf]
        exact congrArg cellOf (by simp only; omega)
      have hrw := regionWeight_coordWeight Primitives.F192.G Primitives.F192.Y
        ⟨n / 256, by omega⟩ ⟨n % 2 + 2 * (n / 4 % 64), hj⟩
      rw [← hcell, regionWeight_cellOf _ _ n hn24, if_pos ⟨h11, rfl⟩] at hrw
      rw [bitWeight_stmt hj, hrw, mul_comm]
  · rw [if_neg h11]
    refine Finset.sum_eq_zero fun J _ => ?_
    rw [if_neg (fun h => h11 h.1), mul_zero]

/-! ## The sum's polynomial -/

section Sum

variable (hK : Constants) (f : (Fin (22 + 2) → Bool) → K) (cells : Array K)
  (hcells : ∀ b, cells.getD (Completeness.idx b) 0 = f b) (sigma : Array ℕ)
  (hsigma : ∀ b, point (sigma.getD (Completeness.idx b) 0) = deployedBasis.point (deployedSigma b))
  (masks : PcsQuotient.Masks)

include hK hcells hsigma in
/-- **`hValues` at cell `x` is F1's `sumValue`** there. -/
theorem hValues_cell (α β γ : E) (x : Fin (22 + 2) → Bool) :
    (hValues 22 cells sigma α β γ).getD (Completeness.idx x) 0 =
      Params.sumValue Completeness.deployedInstanceE.params (gOf f masks) α β γ
        (Completeness.deployedInstanceE.cellEquiv x) := by
  rw [hValues, getD_ofFn _ _ (by exact Completeness.idx_lt x)]
  simp only
  rw [Params.sumValue, cells_cellEquiv, pt_cellEquiv hK,
    Completeness.deployedInstanceE.sigma_cellEquiv, pt_cellEquiv hK,
    pub_cell_nat hK γ (Completeness.idx_lt x), hcells, Completeness.deployedInstanceE_wiring,
    hsigma, ← point_idx hK]
  split_ifs <;> ring

include hK hcells hsigma in
/-- **The table `coefficients 24 0 hValues` holds F1's honest `h₀`**: both take `sumValue` at the
`2^24` cells, below that degree. -/
theorem hHat_table (α β γ : E) :
    tablePoly (fun b : Fin 24 → Bool =>
        (coefficients 24 0 (hValues 22 cells sigma α β γ)).getD (Completeness.idx b) 0) =
      (Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ).h₀ := by
  have hsz : (hValues 22 cells sigma α β γ).size = 2 ^ 24 := Array.size_ofFn
  show _ = Lagrange.interpolate univ Completeness.deployedInstanceE.params.pt
    (Params.sumValue Completeness.deployedInstanceE.params (gOf f masks) α β γ)
  refine Lagrange.eq_interpolate_of_eval_eq
    (r := Params.sumValue Completeness.deployedInstanceE.params (gOf f masks) α β γ)
    Completeness.deployedInstanceE.params.pt_injective.injOn ?_ fun i _ => ?_
  · have hc : Fintype.card (Completeness.deployedInstanceE.params.T × Fin 4) = 2 ^ 24 :=
      Completeness.deployedInstanceE.nCells
    rw [Finset.card_univ, hc]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast natDegree_tablePoly_lt _)
  · obtain ⟨x, rfl⟩ := Completeness.deployedInstanceE.cellEquiv.surjective i
    have h := tablePoly_coefficients_E (m := 24) (cantorUpTo24 hK) (by unfold basisSize; norm_num)
      0 _ hsz (Completeness.idx_lt x)
    rw [zero_add] at h
    rw [pt_cellEquiv hK, h, hValues_cell hK f cells hcells sigma hsigma masks]

end Sum

end ProverQuotient

end E2ECompleteness

/-- info: 'E2ECompleteness.ProverQuotient.hHat_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.ProverQuotient.hHat_table

/-- info: 'E2ECompleteness.ProverQuotient.pub_cell_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.ProverQuotient.pub_cell_nat
