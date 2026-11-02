-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Zerocheck

/-!
# Flock's R1CS on the cube, and the zerocheck's tables

A batch of `2^κ` blocks, each of `2^(k + l + m)` bits: a position is `(y, c)`, `y` the `k + l`
packing bits (the skip's `k` low), `c` the `m` slot bits; `Z y c t` is the bit of block `t` there.
The R1CS has `C = I`: `(A z_t)_r · (B z_t)_r = (z_t)_r` at every position `r` of every block, and
the constant position holds `1` (`R1CSHolds`). The zerocheck reads it on the cube
`Cube (l + m + κ)` of its rounds, for each skip index `i : Cube k` (`zcRow`, `zcTab`): the row
products `A z`, `B z` and the bits themselves.

* `r1cs_doom`: if the R1CS fails, a residual table is nonzero or the constant position's table
  (`pinTab`) is;
* `zc_bool`: the residuals of a Boolean witness are Boolean (characteristic two);
* `skipVal_eq_rowSum`: the zerocheck's terminal values are row sums against the lincheck's row
  weight (`rowW`).

Nothing here transcribes a source.
-/

namespace FlockSound

open Polynomial Finset

variable {F : Type*} [Field F] {k l m κ : ℕ}

/-- A position of a block: the packing bits (the skip's `k` low, `l` others), the slot bits. -/
abbrev Pos (k l m : ℕ) : Type := Cube (k + l) × Cube m

/-- The row product `(M z_t)_r = Σ_c M(r, c) z_t(c)`. -/
def rowProd (M : Pos k l m → Pos k l m → Bool) (Z : Cube (k + l) → Cube m → Cube κ → F)
    (row : Pos k l m) (t : Cube κ) : F :=
  ∑ col, if M row col then Z col.1 col.2 t else 0

/-- **Flock's relation**: every block satisfies `(A z)(B z) = z` and holds `1` at `cpos`. -/
def R1CSHolds (A B : Pos k l m → Pos k l m → Bool) (Z : Cube (k + l) → Cube m → Cube κ → F)
    (cpos : Pos k l m) : Prop :=
  (∀ row t, rowProd A Z row t * rowProd B Z row t = Z row.1 row.2 t) ∧ ∀ t, Z cpos.1 cpos.2 t = 1

/-- The row of skip index `i` at a point `x` of the rounds' cube. -/
def zcRow (i : Cube k) (x : Cube (l + m + κ)) : Pos k l m :=
  (Fin.append i (lowPart (lowPart x)), highPart (lowPart x))

/-- A table of rows and blocks, read on the zerocheck's cube for each skip index. -/
def zcTab (G : Pos k l m → Cube κ → F) (i : Cube k) (x : Cube (l + m + κ)) : F :=
  G (zcRow i x) (highPart x)

/-- The constant position's table on the rounds' cube: its bit minus one, block by block. -/
def pinTab (Z : Cube (k + l) → Cube m → Cube κ → F) (cpos : Pos k l m) (x : Cube (l + m + κ)) : F :=
  Z cpos.1 cpos.2 (highPart x) - 1

theorem zcRow_surj (row : Pos k l m) (t : Cube κ) :
    ∃ i x, zcRow (l := l) (m := m) (κ := κ) i x = row ∧ highPart x = t := by
  refine ⟨lowPart row.1, Fin.append (Fin.append (highPart row.1) row.2) t, ?_, by simp⟩
  simp only [zcRow, lowPart_append, highPart_append, append_lowPart_highPart]

/-- A sum over the positions: the skip bits, the other packing bits, the slot bits. -/
theorem sum_pos {M : Type*} [AddCommMonoid M] (f : Pos k l m → M) :
    ∑ row : Pos k l m, f row = ∑ i : Cube k, ∑ bl : Cube l, ∑ bh : Cube m, f (Fin.append i bl, bh) := by
  rw [Fintype.sum_prod_type, sum_cube_append]

section Char2

variable [CharP F 2]

theorem add_eq_zero_iff_eq' {a b : F} : a + b = 0 ↔ a = b := by
  rw [← CharTwo.sub_eq_add, sub_eq_zero]

/-- **A failing R1CS shows in the zerocheck's tables**: some residual or the constant position's
table is nonzero. -/
theorem r1cs_doom {A B : Pos k l m → Pos k l m → Bool} {Z : Cube (k + l) → Cube m → Cube κ → F}
    {cpos : Pos k l m} (h : ¬ R1CSHolds A B Z cpos) :
    (∃ i x, zcTab (rowProd A Z) i x * zcTab (rowProd B Z) i x +
        zcTab (fun r t ↦ Z r.1 r.2 t) i x ≠ 0) ∨ pinTab Z cpos ≠ 0 := by
  unfold R1CSHolds at h
  rw [not_and_or] at h
  rcases h with h | h
  · push Not at h
    obtain ⟨row, t, ht⟩ := h
    obtain ⟨i, x, hr, hx⟩ := zcRow_surj (l := l) (m := m) row t
    refine Or.inl ⟨i, x, ?_⟩
    simp only [zcTab, hr, hx]
    rwa [Ne, add_eq_zero_iff_eq']
  · push Not at h
    obtain ⟨t, ht⟩ := h
    refine Or.inr fun h0 ↦ ht ?_
    have := congrFun h0 (Fin.append (Fin.append (fun _ ↦ false) (fun _ ↦ false)) t)
    simpa [pinTab, sub_eq_zero] using this

theorem isBool_add {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a + b = 0 ∨ a + b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [CharTwo.add_self_eq_zero]

theorem isBool_mul {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a * b = 0 ∨ a * b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem isBool_sum {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i = 0 ∨ f i = 1) :
    ∑ i ∈ s, f i = 0 ∨ ∑ i ∈ s, f i = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isBool_add (hf a (mem_insert_self a s)) (ih fun i hi ↦ hf i (mem_insert_of_mem hi))

theorem rowProd_bool (M : Pos k l m → Pos k l m → Bool) {Z : Cube (k + l) → Cube m → Cube κ → F}
    (hZ : ∀ y c t, Z y c t = 0 ∨ Z y c t = 1) (row : Pos k l m) (t : Cube κ) :
    rowProd M Z row t = 0 ∨ rowProd M Z row t = 1 :=
  isBool_sum _ _ fun col _ ↦ by split <;> [exact hZ _ _ _; exact Or.inl rfl]

/-- The residuals of a Boolean witness are Boolean. -/
theorem zc_bool (A B : Pos k l m → Pos k l m → Bool) {Z : Cube (k + l) → Cube m → Cube κ → F}
    (hZ : ∀ y c t, Z y c t = 0 ∨ Z y c t = 1) (i : Cube k) (x : Cube (l + m + κ)) :
    zcTab (rowProd A Z) i x * zcTab (rowProd B Z) i x + zcTab (fun r t ↦ Z r.1 r.2 t) i x = 0 ∨
      zcTab (rowProd A Z) i x * zcTab (rowProd B Z) i x + zcTab (fun r t ↦ Z r.1 r.2 t) i x = 1 :=
  isBool_add (isBool_mul (rowProd_bool A hZ _ _) (rowProd_bool B hZ _ _)) (hZ _ _ _)

end Char2

/-! ## The row weight -/

/-- **The lincheck's row weight** at the row point `(z, rl, rh)`: the skip's Lagrange weight at
`z` on the row's skip bits, `eq` on its other packing bits and its slot bits. -/
noncomputable def rowW (node : Bool × Cube k → F) (z : F) (rl : Fin l → F) (rh : Fin m → F)
    (row : Pos k l m) : F :=
  (lag node (lowPart row.1)).eval z * eqP rl (highPart row.1) * eqP rh row.2

/-- The zerocheck's terminal value of a table of rows is its row sum against the row weight and
`eq` on the blocks. -/
theorem skipVal_eq_rowSum (node : Bool × Cube k → F) (G : Pos k l m → Cube κ → F) (z : F)
    (rl : Fin l → F) (rh : Fin m → F) (rt : Fin κ → F) :
    skipVal node (zcTab G) z (Fin.append (Fin.append rl rh) rt) =
      ∑ row : Pos k l m, ∑ t : Cube κ, rowW node z rl rh row * eqP rt t * G row t := by
  have hrow : ∀ f : Pos k l m → F, ∑ row : Pos k l m, f row =
      ∑ i : Cube k, ∑ bl : Cube l, ∑ bh : Cube m, f (Fin.append i bl, bh) := by
    intro f
    rw [Fintype.sum_prod_type, sum_cube_append]
  have hx : ∀ f : Cube (l + m + κ) → F, ∑ x, f x =
      ∑ bl : Cube l, ∑ bh : Cube m, ∑ t : Cube κ, f (Fin.append (Fin.append bl bh) t) := by
    intro f
    rw [sum_cube_append, sum_cube_append (fun y ↦ ∑ t, f (Fin.append y t))]
  rw [hrow]
  simp only [skipVal, mle, hx, eqP_append, zcTab, zcRow, lowPart_append, highPart_append, rowW,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun bl _ ↦
    Finset.sum_congr rfl fun bh _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
  ring

end FlockSound
