-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.R1CS

/-!
# The lincheck

The zerocheck leaves claims `v_a, v_b, v_c` on `Ã, B̃, C̃` at `(z, χ)`; the constant position's
claim is `1`. The verifier draws `α` and proves, by a sumcheck over the `m` slot bits of the
column (plain, degree `2`, the highest bit first: the Rust's `chi_in_prime` is the challenges
reversed), the batched claim `v_a + α v_b + α² v_c + α³` as

`linSum α = Σ_col M_α(col) ẑ(col, χ_rest)`,  `M_α(col) = Σ_row w(row)(A(row, col) + α B(row, col))
+ α² w(col) + α³ [col = cpos]`

(`linW`, `w` the row weight `rowW`). The rounds end on the 64 slices `ŝ(cy) = ẑ((cy, χ'), χ_rest)`
(`strue`): their terminal is `Σ_cy M̂_α(cy, χ') ŝ(cy)` (`linFun` at `χ'`).

* `lin_identity`: `linSum α = Ã + α B̃ + α² C̃ + α³ ẑ(cpos, χ_rest)`;
* `alphaBad`: the roots of the cubic in `α` the four claims' errors make, when one is nonzero (at
  most `3`); `alpha_escape`;
* **`lincheck_sound`**: a wrong terminal value or constant position leaves the lincheck's
  terminal wrong, unless `α` or a round's challenge is bad.

Nothing here transcribes a source.
-/

namespace FlockSound

open Polynomial Finset

variable {F : Type*} [Field F] {k l m κ : ℕ}

section Defs

variable (A B : Pos k l m → Pos k l m → Bool) (Z : Cube (k + l) → Cube m → Cube κ → F)
  (cpos : Pos k l m) (node : Bool × Cube k → F) (z : F) (rl : Fin l → F) (rh : Fin m → F)
  (rt : Fin κ → F)

/-- **The lincheck's column weight** `M_α(col)`. -/
noncomputable def linW (α : F) (col : Pos k l m) : F :=
  (∑ row, rowW node z rl rh row * (bit (A row col) + α * bit (B row col))) +
    α ^ 2 * rowW node z rl rh col + α ^ 3 * (if col = cpos then 1 else 0)

/-- `ẑ(col, χ_rest)`: the column's bit, extended over the blocks. -/
def zhat (col : Pos k l m) : F := mle (Z col.1 col.2) rt

/-- **The lincheck's true sum.** -/
noncomputable def linSum (α : F) : F :=
  ∑ col, linW A B cpos node z rl rh α col * zhat Z rt col

/-- **The lincheck's sumcheck function** of the column's slot bits. -/
noncomputable def linFun (α : F) (Y : Fin m → F) : F :=
  ∑ cy : Cube (k + l), mle (fun ch ↦ linW A B cpos node z rl rh α (cy, ch)) Y *
    mle (fun ch ↦ zhat Z rt (cy, ch)) Y

/-- **The true slices** at the lincheck's point `χ'`: `ŝ(cy) = ẑ((cy, χ'), χ_rest)`. -/
noncomputable def strue (χ' : Fin m → F) (cy : Cube (k + l)) : F :=
  mle (fun ch ↦ zhat Z rt (cy, ch)) χ'

end Defs

/-- The coordinates reversed: the lincheck binds its highest coordinate first. -/
def linRev {m : ℕ} (Φ : (Fin m → F) → F) (Y : Fin m → F) : F := Φ fun j ↦ Y (Fin.rev j)

theorem cubeSum_linRev {m : ℕ} (Φ : (Fin m → F) → F) :
    cubeSum (fun _ ↦ none) (linRev Φ) = cubeSum (fun _ ↦ none) Φ := by
  simp only [cubeSum, eqW_none, one_mul, linRev]
  rw [sum_cube_rev (fun b ↦ Φ (cube b))]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rfl

theorem IndDeg.linRev {m d : ℕ} {Φ : (Fin m → F) → F} (h : IndDeg Φ d) : IndDeg (linRev Φ) d :=
  h.comp Fin.rev Fin.rev_injective

theorem indDeg_linFun (A B : Pos k l m → Pos k l m → Bool) (Z : Cube (k + l) → Cube m → Cube κ → F)
    (cpos : Pos k l m) (node : Bool × Cube k → F) (z : F) (rl : Fin l → F) (rh : Fin m → F)
    (rt : Fin κ → F) (α : F) : IndDeg (linFun A B Z cpos node z rl rh rt α) 2 :=
  IndDeg.sum univ fun _ _ ↦ (indDeg_mle _).mul (indDeg_mle _)

theorem cubeSum_linFun (A B : Pos k l m → Pos k l m → Bool) (Z : Cube (k + l) → Cube m → Cube κ → F)
    (cpos : Pos k l m) (node : Bool × Cube k → F) (z : F) (rl : Fin l → F) (rh : Fin m → F)
    (rt : Fin κ → F) (α : F) :
    cubeSum (fun _ ↦ none) (linFun A B Z cpos node z rl rh rt α) =
      linSum A B Z cpos node z rl rh rt α := by
  simp only [cubeSum, eqW_none, one_mul, linFun, mle_cube, linSum, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- **The lincheck's identity**: its true sum batches the zerocheck's three true terminal values
and the constant position's. -/
theorem lin_identity (A B : Pos k l m → Pos k l m → Bool) (Z : Cube (k + l) → Cube m → Cube κ → F)
    (cpos : Pos k l m) (node : Bool × Cube k → F) (z : F) (rl : Fin l → F) (rh : Fin m → F)
    (rt : Fin κ → F) (α : F) :
    linSum A B Z cpos node z rl rh rt α =
      skipVal node (zcTab (rowProd A Z)) z (Fin.append (Fin.append rl rh) rt) +
        α * skipVal node (zcTab (rowProd B Z)) z (Fin.append (Fin.append rl rh) rt) +
        α ^ 2 * skipVal node (zcTab fun r t ↦ Z r.1 r.2 t) z (Fin.append (Fin.append rl rh) rt) +
        α ^ 3 * zhat Z rt cpos := by
  simp only [skipVal_eq_rowSum]
  -- A row product, summed against the row weight and `eq` on the blocks.
  have hM : ∀ M : Pos k l m → Pos k l m → Bool,
      ∑ row : Pos k l m, ∑ t : Cube κ, rowW node z rl rh row * eqP rt t * rowProd M Z row t =
        ∑ col, (∑ row, rowW node z rl rh row * bit (M row col)) * zhat Z rt col := by
    intro M
    have hrow : ∀ row : Pos k l m, ∑ t : Cube κ, rowW node z rl rh row * eqP rt t * rowProd M Z row t =
        ∑ col, rowW node z rl rh row * bit (M row col) * zhat Z rt col := by
      intro row
      simp only [rowProd, zhat, mle, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun col _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
      by_cases h : M row col <;> simp [h, bit] <;> ring
    rw [Finset.sum_congr rfl fun row _ ↦ hrow row, Finset.sum_comm]
    simp only [Finset.sum_mul]
  have hZ : ∑ row : Pos k l m, ∑ t : Cube κ, rowW node z rl rh row * eqP rt t * Z row.1 row.2 t =
      ∑ col, rowW node z rl rh col * zhat Z rt col := by
    simp only [zhat, mle, Finset.mul_sum]
    refine Finset.sum_congr rfl fun row _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
    ring
  rw [hM A, hM B, hZ]
  simp only [linSum, linW, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_add]
  have hpin : ∑ col : Pos k l m, α ^ 3 * (if col = cpos then 1 else 0) * zhat Z rt col =
      α ^ 3 * zhat Z rt cpos := by
    rw [Finset.sum_eq_single cpos]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hpin]
  congr 1
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun col _ ↦ Finset.sum_congr rfl fun row _ ↦ ?_
    ring
  · refine Finset.sum_congr rfl fun col _ ↦ ?_
    ring

/-! ## The batching challenge `α` -/

/-- The cubic in `α` the four claims' errors make. -/
noncomputable def alphaPoly (va vb vc TA TB TC TP : F) : F[X] :=
  C (va - TA) + C (vb - TB) * X ^ 1 + C (vc - TC) * X ^ 2 + C (1 - TP) * X ^ 3

theorem eval_alphaPoly (va vb vc TA TB TC TP α : F) :
    (alphaPoly va vb vc TA TB TC TP).eval α =
      (va + α * vb + α ^ 2 * vc + α ^ 3) - (TA + α * TB + α ^ 2 * TC + α ^ 3 * TP) := by
  simp only [alphaPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem alphaPoly_ne_zero {va vb vc TA TB TC TP : F}
    (h : ¬ (va = TA ∧ vb = TB ∧ vc = TC ∧ TP = 1)) : alphaPoly va vb vc TA TB TC TP ≠ 0 := by
  intro h0
  apply h
  have c0 := congrArg (·.coeff 0) h0
  have c1 := congrArg (·.coeff 1) h0
  have c2 := congrArg (·.coeff 2) h0
  have c3 := congrArg (·.coeff 3) h0
  simp only [alphaPoly, coeff_add, coeff_C_mul_X_pow, coeff_C, coeff_zero] at c0 c1 c2 c3
  norm_num at c0 c1 c2 c3
  exact ⟨sub_eq_zero.mp c0, sub_eq_zero.mp c1, sub_eq_zero.mp c2, (sub_eq_zero.mp c3).symm⟩

theorem natDegree_alphaPoly_le (va vb vc TA TB TC TP : F) :
    (alphaPoly va vb vc TA TB TC TP).natDegree ≤ 3 := by
  unfold alphaPoly
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le
    ((natDegree_add_le _ _).trans (max_le (by simp) ?_)) ?_)) ?_)
  · exact (natDegree_C_mul_X_pow_le _ _).trans (by norm_num)
  · exact (natDegree_C_mul_X_pow_le _ _).trans (by norm_num)
  · exact natDegree_C_mul_X_pow_le _ _

section Bad

variable [Fintype F] [DecidableEq F]

/-- **`α`'s bad values**: the roots of the cubic, when it is nonzero. -/
noncomputable def alphaBad (va vb vc TA TB TC TP : F) : Finset F :=
  if alphaPoly va vb vc TA TB TC TP ≠ 0 then (alphaPoly va vb vc TA TB TC TP).roots.toFinset else ∅

theorem card_alphaBad_le (va vb vc TA TB TC TP : F) : (alphaBad va vb vc TA TB TC TP).card ≤ 3 := by
  unfold alphaBad
  split_ifs
  · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_alphaPoly_le ..))
  · simp

theorem alpha_escape {va vb vc TA TB TC TP α : F} (h : ¬ (va = TA ∧ vb = TB ∧ vc = TC ∧ TP = 1))
    (hα : α ∉ alphaBad va vb vc TA TB TC TP) :
    va + α * vb + α ^ 2 * vc + α ^ 3 ≠ TA + α * TB + α ^ 2 * TC + α ^ 3 * TP := by
  intro heq
  apply hα
  have hne := alphaPoly_ne_zero h
  rw [alphaBad, if_pos hne, Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_alphaPoly, heq,
    sub_self]

/-- **The lincheck's soundness**: a wrong zerocheck terminal value or a wrong constant position
leaves the lincheck's terminal claim different from the true one at its point, unless `α` or a
round's challenge is bad. -/
theorem lincheck_sound (A B : Pos k l m → Pos k l m → Bool) (Z : Cube (k + l) → Cube m → Cube κ → F)
    (cpos : Pos k l m) (node : Bool × Cube k → F) (z : F) (rl : Fin l → F) (rh : Fin m → F)
    (rt : Fin κ → F) {va vb vc α : F}
    (hne : ¬ (va = skipVal node (zcTab (rowProd A Z)) z (Fin.append (Fin.append rl rh) rt) ∧
      vb = skipVal node (zcTab (rowProd B Z)) z (Fin.append (Fin.append rl rh) rt) ∧
      vc = skipVal node (zcTab fun r t ↦ Z r.1 r.2 t) z (Fin.append (Fin.append rl rh) rt) ∧
      zhat Z rt cpos = 1))
    (hα : α ∉ alphaBad va vb vc (skipVal node (zcTab (rowProd A Z)) z (Fin.append (Fin.append rl rh) rt))
      (skipVal node (zcTab (rowProd B Z)) z (Fin.append (Fin.append rl rh) rt))
      (skipVal node (zcTab fun r t ↦ Z r.1 r.2 t) z (Fin.append (Fin.append rl rh) rt))
      (zhat Z rt cpos))
    (q : Fin m → F[X]) (χ : Fin m → F)
    (hc : Consistent 2 (fun _ ↦ none) (va + α * vb + α ^ 2 * vc + α ^ 3) q χ)
    (hgood : ∀ j, χ j ∉ sumBad 2 m (fun _ ↦ none) (linRev (linFun A B Z cpos node z rl rh rt α)) q χ j) :
    claimAt (va + α * vb + α ^ 2 * vc + α ^ 3) q χ (Fin.last m) ≠
      linFun A B Z cpos node z rl rh rt α fun j ↦ χ (Fin.rev j) := by
  have h0 := alpha_escape hne hα
  rw [← lin_identity, ← cubeSum_linFun, ← cubeSum_linRev] at h0
  intro hlast
  obtain ⟨j, hj⟩ := sumcheck_sound ((indDeg_linFun A B Z cpos node z rl rh rt α).linRev) hc h0 hlast
  exact hgood j hj

end Bad

end FlockSound
