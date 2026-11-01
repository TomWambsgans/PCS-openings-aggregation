-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Tables.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Cantor
import QuotientSecurity.Protocol

/-!
# The four claims, on tables

The verifier's claims are multilinear evaluations of committed tables. This file states each
claim on its table, at the point and with the value the verifier computes, and proves it
equivalent to the statement about polynomials that `Params.Accepts` makes. The tables' entries
are in the large field, which covers tables over the small one.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]

/-- The point of a claim, built from `t`: `w_k(t) / (1 + w_k(t))`, the digits from `first` on. -/
noncomputable def claimPoint (first m : ℕ) (t : F) : Fin m → F :=
  fun k => sq^[(k : ℕ) + first] t / (1 + sq^[(k : ℕ) + first] t)

/-- The scale of such a claim: the product of the `1 + w_k(t)`. -/
noncomputable def claimScale (first m : ℕ) (t : F) : F :=
  ∏ k : Fin m, (1 + sq^[(k : ℕ) + first] t)

/-- A first coordinate chooses between a table's two halves, like a last one. -/
theorem mle_cons {m : ℕ} (c : (Fin (m + 1) → Bool) → F) (e : F) (u : Fin m → F) :
    mle c (Fin.cons e u)
      = (1 + e) * mle (fun b => c (Fin.cons false b)) u
        + e * mle (fun b => c (Fin.cons true b)) u := by
  unfold mle
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => Bool), Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  rw [Finset.mul_sum, Finset.mul_sum, add_comm]
  congr 1 <;> exact Finset.sum_congr rfl fun b _ => by ring

/-- A table's polynomial, by its last digit. -/
theorem tablePoly_snoc {m : ℕ} (c : (Fin (m + 1) → Bool) → F) :
    tablePoly c = tablePoly (fun b => c (Fin.snoc b false))
      + digitPoly m * tablePoly (fun b => c (Fin.snoc b true)) := by
  have hterm : ∀ (b : Fin m → Bool) (x : Bool),
      (∏ k : Fin (m + 1), (if (Fin.snoc b x : Fin (m + 1) → Bool) k then
          (digitPoly (k : ℕ) : F[X]) else 1))
        = (∏ k : Fin m, (if b k then (digitPoly (k : ℕ) : F[X]) else 1))
          * (if x then digitPoly m else 1) := by
    intro b x
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
  unfold tablePoly
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 1) => Bool), Fintype.sum_prod_type,
    Fintype.sum_bool]
  have e : ∀ (x : Bool) (b : Fin m → Bool),
      (Fin.snocEquiv fun _ : Fin (m + 1) => Bool) (x, b) = Fin.snoc b x := fun _ _ => rfl
  simp only [e, hterm, Bool.false_eq_true, ite_false, ite_true, mul_one]
  rw [Finset.mul_sum, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The row of a point is its second digit. -/
theorem rowPoly_eval (t : F) : (rowPoly : F[X]).eval t = sq^[2] t := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  show (rowPoly : F[X]).eval t = sq (sq t)
  simp only [rowPoly, eval_add, eval_pow, eval_X]
  unfold sq
  linear_combination (-(t ^ 3) - t ^ 2) * two

/-- A claim at digits from the second on is an evaluation at the row. -/
theorem mle_claimPoint_two {m : ℕ} (c : (Fin m → Bool) → F) (t : F)
    (ht : ∀ k : Fin m, 1 + sq^[(k : ℕ) + 2] t ≠ 0) :
    mle c (claimPoint 2 m t) = ((tablePoly c).comp rowPoly).eval t / claimScale 2 m t := by
  refine (mle_eq_digitsEval_div c (fun k : Fin m => sq^[(k : ℕ) + 2] t) ht).trans ?_
  rw [eval_comp, tablePoly_eval, rowPoly_eval]
  unfold claimScale
  congr 2

/-- A claim at every digit is an evaluation. -/
theorem mle_claimPoint_zero {m : ℕ} (c : (Fin m → Bool) → F) (t : F)
    (ht : ∀ k : Fin m, 1 + sq^[(k : ℕ)] t ≠ 0) :
    mle c (claimPoint 0 m t) = (tablePoly c).eval t / claimScale 0 m t :=
  mle_eq_tablePoly_eval c t ht

/-- The two coordinates of the extension: with `y₀ = Y / (1 + Y)` and `y₁ = Y^2 / (1 + Y^2)`,
four values enter as `(1, Y, Y^2, Y^3)` over `(1 + Y)(1 + Y^2)`. -/
theorem limbs_combine {Y : F} (hY : 1 + Y ≠ 0) (hY2 : 1 + Y ^ 2 ≠ 0) (a b c d : F) :
    (1 + Y ^ 2 / (1 + Y ^ 2)) * ((1 + Y / (1 + Y)) * a + Y / (1 + Y) * b)
        + Y ^ 2 / (1 + Y ^ 2) * ((1 + Y / (1 + Y)) * c + Y / (1 + Y) * d)
      = (a + Y * b + Y ^ 2 * c + Y ^ 3 * d) / ((1 + Y) * (1 + Y ^ 2)) := by
  have h0 : 1 + Y / (1 + Y) = 1 / (1 + Y) := by
    rw [eq_div_iff hY, add_mul, one_mul, div_mul_cancel₀ _ hY, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have h1 : 1 + Y ^ 2 / (1 + Y ^ 2) = 1 / (1 + Y ^ 2) := by
    rw [eq_div_iff hY2, add_mul, one_mul, div_mul_cancel₀ _ hY2, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  rw [h0, h1]
  field_simp
  ring

theorem claimScale_ne_zero {first m : ℕ} {t : F}
    (ht : ∀ k : Fin m, 1 + sq^[(k : ℕ) + first] t ≠ 0) : claimScale first m t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => ht k

/-! ## The wiring claim -/

/-- **The claim on the wiring table** is that the wiring polynomial takes the value sent. -/
theorem wiring_claim {m : ℕ} (c : (Fin m → Bool) → F) (t s : F)
    (ht : ∀ k : Fin m, 1 + sq^[(k : ℕ) + 0] t ≠ 0) :
    mle c (claimPoint 0 m t) = s / claimScale 0 m t ↔ (tablePoly c).eval t = s := by
  rw [mle_claimPoint_zero c t ht, div_left_inj' (claimScale_ne_zero ht)]

/-! ## The witness claim -/

/-- The four row polynomials a witness table holds: its first two coordinates choose one. -/
noncomputable def witnessOfTable {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → F) : Params.Witness F :=
  ![tablePoly fun b => c (Fin.cons false (Fin.cons false b)),
    tablePoly fun b => c (Fin.cons true (Fin.cons false b)),
    tablePoly fun b => c (Fin.cons false (Fin.cons true b)),
    tablePoly fun b => c (Fin.cons true (Fin.cons true b))]

/-- The witness table's claim, as its polynomials' values at the row. -/
theorem witness_mle {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → F) (t ρ : F)
    (ht : ∀ i : Fin k, 1 + sq^[(i : ℕ) + 2] t ≠ 0) :
    mle c (Fin.cons ρ (Fin.cons (ρ ^ 2) (claimPoint 2 k t)))
      = (∑ j, Params.opening ρ j * ((witnessOfTable c j).comp rowPoly).eval t)
        / claimScale 2 k t := by
  rw [mle_cons, mle_cons, mle_cons]
  simp only [mle_claimPoint_two _ t ht, Fin.sum_univ_four, Params.opening, witnessOfTable,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- **The claim on the witness table** is the opening of its four polynomials at the row, under
the weights of `ρ`. -/
theorem witness_claim {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → F) (t ρ : F) (a : Fin 4 → F)
    (ht : ∀ i : Fin k, 1 + sq^[(i : ℕ) + 2] t ≠ 0) :
    mle c (Fin.cons ρ (Fin.cons (ρ ^ 2) (claimPoint 2 k t)))
        = (∑ j, Params.opening ρ j * a j) / claimScale 2 k t
      ↔ ∑ j, Params.opening ρ j * ((witnessOfTable c j).comp rowPoly).eval t
        = ∑ j, Params.opening ρ j * a j := by
  rw [witness_mle c t ρ ht, div_left_inj' (claimScale_ne_zero ht)]

/-! ## The quotient table -/

/-- One of the sixteen tables the last four coordinates of the quotient table choose from. -/
def subTable {k : ℕ} (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → F) (κ τ e₀ e₁ : Bool) :
    (Fin k → Bool) → F :=
  fun b => c (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc b κ) τ) e₀) e₁)

/-- The polynomial of a slot of the quotient table: its four limbs on `1, Y, Y^2, Y^3`. -/
noncomputable def slotPoly {k : ℕ} (Y : F) (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → F)
    (κ τ : Bool) : F[X] :=
  tablePoly (subTable c κ τ false false) + C Y * tablePoly (subTable c κ τ true false)
    + C (Y ^ 2) * tablePoly (subTable c κ τ false true)
    + C (Y ^ 3) * tablePoly (subTable c κ τ true true)

/-- The quotient table's claim at `t`, as its four slots' values. -/
theorem quotient_mle {k : ℕ} (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → F) (t e ρ Y : F)
    (hY : 1 + Y ≠ 0) (hY2 : 1 + Y ^ 2 ≠ 0) (ht : ∀ i : Fin k, 1 + sq^[(i : ℕ) + 0] t ≠ 0) :
    mle c (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 k t) e) ρ) (Y / (1 + Y)))
        (Y ^ 2 / (1 + Y ^ 2)))
      = ((1 + ρ) * ((1 + e) * (slotPoly Y c false false).eval t
            + e * (slotPoly Y c true false).eval t)
          + ρ * ((1 + e) * (slotPoly Y c false true).eval t
            + e * (slotPoly Y c true true).eval t))
        / ((1 + Y) * (1 + Y ^ 2)) / claimScale 0 k t := by
  have hS := claimScale_ne_zero ht
  have hsub : ∀ κ τ e₀ e₁, mle (subTable c κ τ e₀ e₁) (claimPoint 0 k t)
      = (tablePoly (subTable c κ τ e₀ e₁)).eval t / claimScale 0 k t := fun κ τ e₀ e₁ =>
    mle_claimPoint_zero _ t ht
  rw [mle_snoc, mle_snoc, mle_snoc, mle_snoc, mle_snoc, mle_snoc, mle_snoc]
  rw [mle_snoc, mle_snoc, mle_snoc, mle_snoc, mle_snoc, mle_snoc, mle_snoc, mle_snoc]
  change (1 + Y ^ 2 / (1 + Y ^ 2)) * ((1 + Y / (1 + Y)) *
        ((1 + ρ) * ((1 + e) * mle (subTable c false false false false) _
            + e * mle (subTable c true false false false) _)
          + ρ * ((1 + e) * mle (subTable c false true false false) _
            + e * mle (subTable c true true false false) _))
      + Y / (1 + Y) *
        ((1 + ρ) * ((1 + e) * mle (subTable c false false true false) _
            + e * mle (subTable c true false true false) _)
          + ρ * ((1 + e) * mle (subTable c false true true false) _
            + e * mle (subTable c true true true false) _)))
    + Y ^ 2 / (1 + Y ^ 2) * ((1 + Y / (1 + Y)) *
        ((1 + ρ) * ((1 + e) * mle (subTable c false false false true) _
            + e * mle (subTable c true false false true) _)
          + ρ * ((1 + e) * mle (subTable c false true false true) _
            + e * mle (subTable c true true false true) _))
      + Y / (1 + Y) *
        ((1 + ρ) * ((1 + e) * mle (subTable c false false true true) _
            + e * mle (subTable c true false true true) _)
          + ρ * ((1 + e) * mle (subTable c false true true true) _
            + e * mle (subTable c true true true true) _))) = _
  rw [limbs_combine hY hY2]
  simp only [hsub, slotPoly, eval_add, eval_mul, eval_C]
  field_simp
  ring

/-! ## The claim at the fixed point -/

/-- The first chunk of a table of two more digits. -/
def lowChunk {m : ℕ} (c : (Fin (m + 1 + 1) → Bool) → F) : (Fin m → Bool) → F :=
  fun b => c (Fin.snoc (Fin.snoc b false) false)

/-- What a table of two more digits holds beyond its first chunk, over the cells' vanishing
polynomial. -/
noncomputable def highPart {m : ℕ} (c : (Fin (m + 1 + 1) → Bool) → F) : F[X] :=
  tablePoly (fun b => c (Fin.snoc (Fin.snoc b true) false))
    + (digitPoly m + 1) * tablePoly (fun b => c (Fin.snoc b true))

/-- A table of two more digits holds its first chunk's polynomial, plus a multiple of the
cells' vanishing polynomial. -/
theorem tablePoly_low {m : ℕ} (c : (Fin (m + 1 + 1) → Bool) → F) :
    tablePoly c = tablePoly (lowChunk c) + digitPoly m * highPart c := by
  rw [tablePoly_snoc c, tablePoly_snoc fun b => c (Fin.snoc b false)]
  have hd : (digitPoly (m + 1) : F[X]) = digitPoly m * (digitPoly m + 1) := by
    show (X ^ 2 + X : F[X]).comp (digitPoly m) = _
    simp only [add_comp, pow_comp, X_comp]
    ring
  rw [hd]
  unfold lowChunk highPart
  ring

/-- The low part of the sum's polynomial: the first chunk of the first slot, over its limbs. -/
noncomputable def sumPolyLow {m : ℕ} (Y : F)
    (c : (Fin (m + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → F) : F[X] :=
  tablePoly (lowChunk (subTable c false false false false))
    + C Y * tablePoly (lowChunk (subTable c false false true false))
    + C (Y ^ 2) * tablePoly (lowChunk (subTable c false false false true))
    + C (Y ^ 3) * tablePoly (lowChunk (subTable c false false true true))

/-- The rest of the first slot, over the cells' vanishing polynomial. -/
noncomputable def sumPolyHigh {m : ℕ} (Y : F)
    (c : (Fin (m + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → F) : F[X] :=
  highPart (subTable c false false false false)
    + C Y * highPart (subTable c false false true false)
    + C (Y ^ 2) * highPart (subTable c false false false true)
    + C (Y ^ 3) * highPart (subTable c false false true true)

/-- The first slot is the low part plus a multiple of the cells' vanishing polynomial. -/
theorem slotPoly_low {m : ℕ} (Y : F) (c : (Fin (m + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → F) :
    slotPoly Y c false false = sumPolyLow Y c + digitPoly m * sumPolyHigh Y c := by
  unfold slotPoly sumPolyLow sumPolyHigh
  rw [tablePoly_low (subTable c false false false false),
    tablePoly_low (subTable c false false true false),
    tablePoly_low (subTable c false false false true),
    tablePoly_low (subTable c false false true true)]
  ring

/-- The fixed point of the second claim on the quotient table: ones on the cells' digits, zeros
on the next four coordinates, then the extension's two. -/
noncomputable def sumPoint (m : ℕ) (Y : F) : Fin (m + 1 + 1 + 1 + 1 + 1 + 1) → F :=
  Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (fun _ => 1) 0) 0) 0) 0)
    (Y / (1 + Y))) (Y ^ 2 / (1 + Y ^ 2))

/-- **The claim at the fixed point** is the sum of the low part over the cells. -/
theorem sum_mle {n m : ℕ} (B : CantorBasis F n) (hm : m ≤ n) (Y : F) (hY : 1 + Y ≠ 0)
    (hY2 : 1 + Y ^ 2 ≠ 0) (c : (Fin (m + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → F) :
    mle c (sumPoint m Y)
      = (∑ x : Fin m → Bool, (sumPolyLow Y c).eval (B.point x)) / ((1 + Y) * (1 + Y ^ 2)) := by
  unfold sumPoint
  simp only [mle_snoc, add_zero, zero_mul, one_mul]
  change (1 + Y ^ 2 / (1 + Y ^ 2)) * ((1 + Y / (1 + Y)) *
        mle (lowChunk (subTable c false false false false)) (fun _ => 1)
      + Y / (1 + Y) * mle (lowChunk (subTable c false false true false)) (fun _ => 1))
    + Y ^ 2 / (1 + Y ^ 2) * ((1 + Y / (1 + Y)) *
        mle (lowChunk (subTable c false false false true)) (fun _ => 1)
      + Y / (1 + Y) * mle (lowChunk (subTable c false false true true)) (fun _ => 1)) = _
  rw [limbs_combine hY hY2, ← sum_tablePoly B hm, ← sum_tablePoly B hm, ← sum_tablePoly B hm,
    ← sum_tablePoly B hm]
  unfold sumPolyLow
  simp only [eval_add, eval_mul, eval_C, Finset.sum_add_distrib, Finset.mul_sum]

/-! ## Degrees -/

theorem natDegree_digitPoly_le (k : ℕ) : (digitPoly k : F[X]).natDegree ≤ 2 ^ k := by
  induction k with
  | zero => simp [digitPoly]
  | succ k ih =>
    refine natDegree_comp_le.trans ?_
    have h2 : (X ^ 2 + X : F[X]).natDegree ≤ 2 := by compute_degree
    calc (X ^ 2 + X : F[X]).natDegree * (digitPoly k : F[X]).natDegree ≤ 2 * 2 ^ k :=
          Nat.mul_le_mul h2 ih
      _ = 2 ^ (k + 1) := by ring

theorem sum_two_pow_fin (m : ℕ) : ∑ k : Fin m, 2 ^ (k : ℕ) < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega

/-- A table of `m` variables holds a polynomial of degree at most `2^m`. -/
theorem natDegree_tablePoly_le {m : ℕ} (c : (Fin m → Bool) → F) :
    (tablePoly c).natDegree ≤ 2 ^ m := by
  unfold tablePoly
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_two_pow_fin m).le
  split_ifs
  · exact natDegree_digitPoly_le _
  · simp

/-- Strictly below `2^m`, in fact. -/
theorem natDegree_tablePoly_lt {m : ℕ} (c : (Fin m → Bool) → F) :
    (tablePoly c).natDegree < 2 ^ m := by
  have hpos : 0 < 2 ^ m := by positivity
  refine lt_of_le_of_lt (b := 2 ^ m - 1) ?_ (by omega)
  unfold tablePoly
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (Nat.le_sub_one_of_lt (sum_two_pow_fin m))
  split_ifs
  · exact natDegree_digitPoly_le _
  · simp

theorem tablePoly_sub {m : ℕ} (c c' : (Fin m → Bool) → F) :
    tablePoly (c - c') = tablePoly c - tablePoly c' := by
  unfold tablePoly
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [Pi.sub_apply, C_sub, sub_mul]

/-- A monic polynomial with as many distinct roots as its degree is the product over them. -/
theorem eq_prod_of_monic_of_roots {ι : Type*} [Fintype ι] {p : F[X]} (hmon : p.Monic)
    (hdeg : p.natDegree = Fintype.card ι) {f : ι → F} (hf : Function.Injective f)
    (hroot : ∀ i, p.eval (f i) = 0) : p = ∏ i, (X - C (f i)) := by
  have hqmon : (∏ i, (X - C (f i))).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hqdeg : (∏ i, (X - C (f i))).natDegree = Fintype.card ι := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  rw [← sub_eq_zero]
  by_contra hne
  have hlt : (p - ∏ i, (X - C (f i))).natDegree < Fintype.card ι := by
    have hdd : p.degree = (∏ i, (X - C (f i))).degree := by
      rw [degree_eq_natDegree hmon.ne_zero, degree_eq_natDegree hqmon.ne_zero, hdeg, hqdeg]
    have hlc : p.leadingCoeff = (∏ i, (X - C (f i))).leadingCoeff := by
      rw [hmon.leadingCoeff, hqmon.leadingCoeff]
    have := degree_sub_lt_left hdd hmon.ne_zero hlc
    rw [degree_eq_natDegree hmon.ne_zero, hdeg] at this
    exact (natDegree_lt_iff_degree_lt hne).mpr this
  refine hne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf (fun i => ?_) hlt)
  rw [eval_sub, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp), sub_zero]
  exact hroot i

end QuotientSecurity
