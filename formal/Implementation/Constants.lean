-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Claims

/-!
# The graph's constants are the model's

The constants `Graph.lean` carries from the Rust (`quotient::domain::beta`, `row_vanishing`,
`coordinates`, `protocol::extension`) are checked here by computation on numbers (`decide +kernel`)
and read in `F` through `IsF192`: `beta` is a Cantor basis (`basis`), `coords` inverts it on the
public region (`basis_hb`), `tau` gives the rows' vanishing polynomial, and `y0`, `y1`, `scale` are
`Y / (1 + Y)`, `Y^2 / (1 + Y^2)`, `1 / ((1 + Y) (1 + Y^2))` for `Y = y` (`consts`). Nothing about
the Rust's computation of them is trusted.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open Program Emitted QuotientSecurity

local notation "SQ" => QuotientSecurity.sq

/-! ## On numbers -/

theorem beta_succ : ∀ k < 23,
    mulE (beta.getD (k + 1) 0) (beta.getD (k + 1) 0) ^^^ beta.getD (k + 1) 0 = beta.getD k 0 := by
  decide +kernel

theorem coords_inverse : ∀ d < 11, 1 ≤ d →
    ((List.range (d + 1)).map fun e => mulE (coords.getD e 0) (beta.getD (d - e) 0)).foldl
      (· ^^^ ·) 0 = 0 := by
  decide +kernel

theorem tau_vanishes : ∀ j < 24, 2 ≤ j →
    ((List.range 23).map fun k => if k ≤ j then mulE (tau.getD k 0) (beta.getD (j - k) 0) else 0).foldl
      (· ^^^ ·) 0 = 0 := by
  decide +kernel

theorem consts_values : beta.getD 0 0 = 1 ∧ coords.getD 0 0 = 1 ∧ tau.getD 22 0 = 1 ∧
    mulE y0 (1 ^^^ B64) = B64 ∧ mulE y1 (1 ^^^ mulE B64 B64) = mulE B64 B64 ∧
    mulE scale (mulE (1 ^^^ B64) (1 ^^^ mulE B64 B64)) = 1 ∧
    (1 ^^^ B64) % B192 ≠ 0 ∧ (1 ^^^ mulE B64 B64) % B192 ≠ 0 := by
  decide +kernel

/-! ## In the field -/

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] {limbs : F ≃ QuotientRpm.Limbs}
variable (hF : IsF192 limbs)
include hF

theorem elem_xorFold : ∀ (l : List Nat) (acc : Nat),
    elem limbs (l.foldl (· ^^^ ·) acc) = elem limbs acc + (l.map (elem limbs)).sum
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, elem_xorFold l, elem_xor hF, List.map_cons, List.sum_cons, add_assoc]

theorem elem_ne_zero {x : Nat} (h : x % B192 ≠ 0) : elem limbs x ≠ 0 := by
  intro h0
  have hw := word_elem (limbs := limbs) x
  rw [h0] at hw
  have hz : word limbs (0 : F) = 0 := by
    have := word_elem (limbs := limbs) 0
    rwa [elem_zero hF] at this
  rw [hz] at hw
  exact h hw.symm

theorem elem_sq (x : Nat) : SQ (elem limbs x) = elem limbs (mulE x x ^^^ x) := by
  rw [elem_xor hF, elem_mulE hF]; rfl

/-- **`beta` is a Cantor basis** of 24 vectors. -/
noncomputable def basis : CantorBasis F (22 + 2) where
  β k := elem limbs (beta.getD k 0)
  zero := by rw [consts_values.1, elem_one hF]
  succ k hk := by rw [elem_sq hF, beta_succ k (by omega)]

variable (limbs) in
/-- The region's constants `b` (`coordinates(11)`). -/
noncomputable def bConst (k : ℕ) : F := elem limbs (coords.getD k 0)

variable (limbs) in
/-- The weights `c` of the region's coordinates (`coordinate_weight`). -/
noncomputable def cConst (k : ℕ) : F := elem limbs (slopeConst k ^^^ 1)

variable (limbs) in
/-- `Y = y`. -/
noncomputable def yConst : F := elem limbs B64

theorem basis_hb0 : bConst limbs 0 = 1 := by
  rw [bConst, consts_values.2.1, elem_one hF]

theorem sum_elem_mul (f g : ℕ → Nat) (n : ℕ) :
    ∑ e ∈ Finset.range n, elem limbs (f e) * elem limbs (g e) =
      elem limbs (((List.range n).map fun e => mulE (f e) (g e)).foldl (· ^^^ ·) 0) := by
  rw [elem_xorFold hF, elem_zero hF, zero_add, List.map_map, listSum_range]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [elem_mulE hF]

theorem basis_hb : ∀ d, 1 ≤ d → d < 11 →
    ∑ e ∈ Finset.range (d + 1), bConst limbs e * (basis hF).β (d - e) = 0 := by
  intro d hd1 hd
  have := sum_elem_mul hF (fun e => coords.getD e 0) (fun e => beta.getD (d - e) 0) (d + 1)
  rw [show (∑ e ∈ Finset.range (d + 1), bConst limbs e * (basis hF).β (d - e)) =
    ∑ e ∈ Finset.range (d + 1), elem limbs (coords.getD e 0) * elem limbs (beta.getD (d - e) 0)
    from rfl, this, coords_inverse d hd hd1, elem_zero hF]

theorem yConst_sq : yConst limbs ^ 2 = elem limbs (mulE B64 B64) := by
  rw [pow_two, yConst, elem_mulE hF]

/-- **The constants are the model's.** -/
theorem consts : Consts limbs (basis hF) (bConst limbs) (cConst limbs) (yConst limbs) := by
  obtain ⟨-, -, htau, hy0, hy1, hsc, hY, hY2⟩ := consts_values
  have e1 : (1 : F) + yConst limbs = elem limbs (1 ^^^ B64) := by rw [elem_xor hF, elem_one hF]; rfl
  have e2 : (1 : F) + yConst limbs ^ 2 = elem limbs (1 ^^^ mulE B64 B64) := by
    rw [elem_xor hF, elem_one hF, yConst_sq hF]
  have hY' : (1 : F) + yConst limbs ≠ 0 := by rw [e1]; exact elem_ne_zero hF hY
  have hY2' : (1 : F) + yConst limbs ^ 2 ≠ 0 := by rw [e2]; exact elem_ne_zero hF hY2
  refine
    { zero := elem_zero hF
      one := elem_one hF
      theta := rfl
      theta1 := by rw [elem_xor hF, elem_one hF]; rfl
      coords := fun e _ => rfl
      slopes := fun k _ => by
        rw [cConst, ← elem_one hF, ← elem_xor hF, ← Nat.xor_assoc, Nat.xor_comm 1, Nat.xor_assoc,
          Nat.xor_self, Nat.xor_zero]
      tauLast := by rw [htau, elem_one hF]
      tauSys := fun j hj => ?_
      y0 := by
        rw [eq_div_iff hY', e1, ← elem_mulE hF, hy0]; rfl
      y1 := by
        rw [eq_div_iff hY2', e2, ← elem_mulE hF, hy1, yConst_sq hF]
      scale := by
        apply eq_inv_of_mul_eq_one_left
        rw [e1, e2, ← elem_mulE hF, ← elem_mulE hF, hsc, elem_one hF]
      hY := hY'
      hY2 := hY2' }
  have hj24 : (j : ℕ) < 22 + 2 := j.2
  have hit : ∀ k : Fin (22 + 1), SQ^[(k : ℕ)] ((basis hF).β j) =
      if (k : ℕ) ≤ j then elem limbs (beta.getD (j - k) 0) else 0 := fun k =>
    (basis hF).iterate k j hj24
  simp only [hit, mul_ite, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ (j : ℕ) then elem limbs (tau.getD k 0) *
    elem limbs (beta.getD (j - k) 0) else 0) 23]
  have h2 := congrArg (elem limbs) (tau_vanishes j hj24 hj)
  rw [elem_xorFold hF, elem_zero hF, zero_add, List.map_map, listSum_range] at h2
  refine (Finset.sum_congr rfl fun k _ => ?_).trans h2
  simp only [Function.comp]
  split_ifs <;> simp [elem_mulE hF, elem_zero hF]

end Implementation
