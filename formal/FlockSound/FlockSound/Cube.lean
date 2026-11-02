-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Boolean cube, `eq` weights, multilinear extensions, individual degrees

The generic layer of `FlockSound`: everything a sumcheck over the Boolean cube reads, over any
commutative ring `F`, with points `Fin m → F` and cube points `Fin m → Bool` (`Cube m`), so that
binding the lowest coordinate is `Fin.cons`.

* `eq1 x b` is `x` at `b = true`, `1 - x` at `b = false`; `eqP x b = Π_i eq1 (x i) (b i)`.
* A sumcheck variable is **plain** (`none`, weight `1` on both halves) or **`eq`-weighted** at
  `τ` (`some τ`, the weight `eq1 τ`): `wt`, `eqW`. `cubeSum w Φ = Σ_b eqW w b · Φ(b)` is the sum
  a sumcheck with those variables proves (the zerocheck's `eq` factors split off, Gruen's form,
  are the `some` weights; the lincheck's and the matrices' rounds are plain).
* `mle t x = Σ_b t b · eqP x b`, the multilinear extension of a table.
* `IndDeg Φ d`: in every coordinate, at every point, `Φ` is a polynomial of degree at most `d`.
  Closed under sums, products (degrees add), constants, and reading a subset of the coordinates;
  `mle t` has individual degree `1`.

Nothing here transcribes a source.
-/

namespace FlockSound

open Polynomial Finset

/-- A point of the Boolean cube of dimension `m`. -/
abbrev Cube (m : ℕ) : Type := Fin m → Bool

section Ring

variable {F : Type*} [CommRing F]

/-- `0` or `1` in `F`. -/
def bit (b : Bool) : F := if b then 1 else 0

@[simp] theorem bit_true : (bit true : F) = 1 := rfl
@[simp] theorem bit_false : (bit false : F) = 0 := rfl

/-- A cube point as a point of `F^m`. -/
def cube {m : ℕ} (b : Cube m) : Fin m → F := fun i ↦ bit (b i)

/-- The `eq` weight of one coordinate: `x` at `true`, `1 - x` at `false`. -/
def eq1 (x : F) (b : Bool) : F := if b then x else 1 - x

@[simp] theorem eq1_true (x : F) : eq1 x true = x := rfl
@[simp] theorem eq1_false (x : F) : eq1 x false = 1 - x := rfl

/-- `eq(x, b) = Π_i eq1 (x i) (b i)`. -/
def eqP {m : ℕ} (x : Fin m → F) (b : Cube m) : F := ∏ i, eq1 (x i) (b i)

/-- A sumcheck variable's weight on its two halves: plain (`none`) or `eq` at `τ`. -/
def wt : Option F → Bool → F
  | none, _ => 1
  | some τ, b => eq1 τ b

/-- The weight of a cube point: the product of its variables' weights. -/
def eqW {m : ℕ} (w : Fin m → Option F) (b : Cube m) : F := ∏ i, wt (w i) (b i)

/-- **The weighted cube sum** a sumcheck proves: `Σ_b eqW w b · Φ(b)`. -/
def cubeSum {m : ℕ} (w : Fin m → Option F) (Φ : (Fin m → F) → F) : F :=
  ∑ b : Cube m, eqW w b * Φ (cube b)

/-- **The multilinear extension** of a table. -/
def mle {m : ℕ} (t : Cube m → F) (x : Fin m → F) : F := ∑ b, t b * eqP x b

/-! ## Splitting off the lowest coordinate -/

theorem sum_cube_succ {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Cube (m + 1) → M) :
    ∑ b, f b = ∑ b₀ : Bool, ∑ b : Cube m, f (Fin.cons b₀ b) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Bool) _ _ fun _ ↦ rfl).symm

theorem eqW_cons {m : ℕ} (w : Fin (m + 1) → Option F) (b₀ : Bool) (b : Cube m) :
    eqW w (Fin.cons b₀ b) = wt (w 0) b₀ * eqW (Fin.tail w) b := by
  simp only [eqW, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

theorem eqP_cons {m : ℕ} (x₀ : F) (x : Fin m → F) (b₀ : Bool) (b : Cube m) :
    eqP (Fin.cons x₀ x : Fin (m + 1) → F) (Fin.cons b₀ b) = eq1 x₀ b₀ * eqP x b := by
  simp only [eqP, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem cube_cons {m : ℕ} (b₀ : Bool) (b : Cube m) :
    (cube (Fin.cons b₀ b : Cube (m + 1)) : Fin (m + 1) → F) = Fin.cons (bit b₀) (cube b) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [cube]

/-- **One variable of the cube sum**: its two halves, each weighted. -/
theorem cubeSum_succ {m : ℕ} (w : Fin (m + 1) → Option F) (Φ : (Fin (m + 1) → F) → F) :
    cubeSum w Φ = wt (w 0) false * cubeSum (Fin.tail w) (fun r ↦ Φ (Fin.cons 0 r)) +
      wt (w 0) true * cubeSum (Fin.tail w) (fun r ↦ Φ (Fin.cons 1 r)) := by
  rw [cubeSum, sum_cube_succ, Fintype.sum_bool, add_comm]
  simp only [cubeSum, eqW_cons, cube_cons, bit_true, bit_false, Finset.mul_sum, mul_assoc]

theorem cubeSum_zero (w : Fin 0 → Option F) (Φ : (Fin 0 → F) → F) (x : Fin 0 → F) :
    cubeSum w Φ = Φ x := by
  have hx : ∀ y : Fin 0 → F, y = x := fun y ↦ funext fun i ↦ i.elim0
  simp [cubeSum, eqW, hx]

/-- The `eq` weights at a cube point are the indicator. -/
theorem eq1_bit (x y : Bool) : eq1 (bit x : F) y = if x = y then 1 else 0 := by
  cases x <;> cases y <;> simp [eq1, bit]

theorem eqP_cube {m : ℕ} (b' b : Cube m) : eqP (cube b' : Fin m → F) b = if b' = b then 1 else 0 := by
  simp only [eqP, cube, eq1_bit]
  rw [Finset.prod_boole]
  congr 1
  exact propext ⟨fun h ↦ funext fun i ↦ h i (Finset.mem_univ i), fun h i _ ↦ congrFun h i⟩

/-- A multilinear extension reads its table at a cube point. -/
@[simp] theorem mle_cube {m : ℕ} (t : Cube m → F) (b : Cube m) : mle t (cube b) = t b := by
  rw [mle, Finset.sum_eq_single b]
  · simp [eqP_cube]
  · intro b' _ hb'
    simp [eqP_cube, Ne.symm hb']
  · simp

/-- Binding the lowest coordinate of a multilinear extension. -/
theorem mle_cons {m : ℕ} (t : Cube (m + 1) → F) (x₀ : F) (x : Fin m → F) :
    mle t (Fin.cons x₀ x) = (1 - x₀) * mle (fun b ↦ t (Fin.cons false b)) x +
      x₀ * mle (fun b ↦ t (Fin.cons true b)) x := by
  rw [mle, sum_cube_succ, Fintype.sum_bool, add_comm]
  simp only [mle, eqP_cons, eq1_true, eq1_false, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun b _ ↦ ?_ <;> ring

/-- `eqW` at `eq` weights is `eqP`. -/
theorem eqW_some {m : ℕ} (τ : Fin m → F) (b : Cube m) : eqW (fun i ↦ some (τ i)) b = eqP τ b := rfl

/-- `eqW` at plain weights is `1`. -/
@[simp] theorem eqW_none {m : ℕ} (b : Cube m) : eqW (fun _ : Fin m ↦ (none : Option F)) b = 1 := by
  simp [eqW, wt]

/-- The partition of unity. -/
theorem sum_eqP {m : ℕ} (x : Fin m → F) : ∑ b : Cube m, eqP x b = 1 := by
  induction m with
  | zero => simp [eqP]
  | succ m ih =>
    rw [sum_cube_succ, Fintype.sum_bool]
    obtain ⟨x₀, y, rfl⟩ : ∃ x₀ y, x = Fin.cons x₀ y := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    simp only [eqP_cons, eq1_true, eq1_false, ← Finset.mul_sum, ih]
    ring

/-- A constant table extends to the constant. -/
theorem mle_const {m : ℕ} (a : F) (x : Fin m → F) : mle (fun _ : Cube m ↦ a) x = a := by
  rw [mle, ← Finset.mul_sum, sum_eqP, mul_one]

/-- The multilinear extension is linear in the table. -/
theorem mle_add {m : ℕ} (s t : Cube m → F) (x : Fin m → F) :
    mle (fun b ↦ s b + t b) x = mle s x + mle t x := by
  simp only [mle, add_mul, Finset.sum_add_distrib]

theorem mle_smul {m : ℕ} (a : F) (t : Cube m → F) (x : Fin m → F) :
    mle (fun b ↦ a * t b) x = a * mle t x := by
  simp only [mle, Finset.mul_sum, mul_assoc]

theorem mle_sum {m : ℕ} {ι : Type*} (s : Finset ι) (t : ι → Cube m → F) (x : Fin m → F) :
    mle (fun b ↦ ∑ i ∈ s, t i b) x = ∑ i ∈ s, mle (t i) x := by
  simp only [mle, Finset.sum_mul]
  exact Finset.sum_comm

theorem mle_sub {m : ℕ} (s t : Cube m → F) (x : Fin m → F) :
    mle (fun b ↦ s b - t b) x = mle s x - mle t x := by
  simp only [mle, sub_mul, Finset.sum_sub_distrib]

/-- A table zero on the cube extends to zero. -/
theorem mle_eq_zero {m : ℕ} {t : Cube m → F} (h : ∀ b, t b = 0) (x : Fin m → F) : mle t x = 0 := by
  simp [mle, h]

/-! ## Individual degrees -/

/-- **`Φ` has individual degree at most `d`**: in each coordinate, at every point, it is a
polynomial of degree at most `d`. -/
def IndDeg {m : ℕ} (Φ : (Fin m → F) → F) (d : ℕ) : Prop :=
  ∀ (r : Fin m → F) (i : Fin m), ∃ p : F[X], p.natDegree ≤ d ∧
    ∀ c, Φ (Function.update r i c) = p.eval c

theorem IndDeg.mono {m : ℕ} {Φ : (Fin m → F) → F} {d e : ℕ} (h : IndDeg Φ d) (hde : d ≤ e) :
    IndDeg Φ e := fun r i ↦
  let ⟨p, hp, he⟩ := h r i
  ⟨p, hp.trans hde, he⟩

theorem indDeg_const {m : ℕ} (a : F) (d : ℕ) : IndDeg (fun _ : Fin m → F ↦ a) d := fun _ _ ↦
  ⟨C a, by simp, fun _ ↦ by simp⟩

theorem IndDeg.add {m : ℕ} {Φ Ψ : (Fin m → F) → F} {d : ℕ} (hΦ : IndDeg Φ d) (hΨ : IndDeg Ψ d) :
    IndDeg (fun r ↦ Φ r + Ψ r) d := fun r i ↦ by
  obtain ⟨p, hp, hpe⟩ := hΦ r i
  obtain ⟨q, hq, hqe⟩ := hΨ r i
  exact ⟨p + q, (natDegree_add_le _ _).trans (max_le hp hq), fun c ↦ by simp [hpe, hqe]⟩

theorem IndDeg.mul {m : ℕ} {Φ Ψ : (Fin m → F) → F} {d e : ℕ} (hΦ : IndDeg Φ d)
    (hΨ : IndDeg Ψ e) : IndDeg (fun r ↦ Φ r * Ψ r) (d + e) := fun r i ↦ by
  obtain ⟨p, hp, hpe⟩ := hΦ r i
  obtain ⟨q, hq, hqe⟩ := hΨ r i
  exact ⟨p * q, (natDegree_mul_le).trans (add_le_add hp hq), fun c ↦ by simp [hpe, hqe]⟩

theorem IndDeg.const_mul {m : ℕ} {Φ : (Fin m → F) → F} {d : ℕ} (a : F) (hΦ : IndDeg Φ d) :
    IndDeg (fun r ↦ a * Φ r) d := by
  simpa using (indDeg_const (m := m) a 0).mul hΦ

theorem IndDeg.sum {m : ℕ} {ι : Type*} (s : Finset ι) {Φ : ι → (Fin m → F) → F} {d : ℕ}
    (h : ∀ i ∈ s, IndDeg (Φ i) d) : IndDeg (fun r ↦ ∑ i ∈ s, Φ i r) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using indDeg_const (m := m) (0 : F) d
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Reading a subset of the coordinates through an injection keeps the individual degree. -/
theorem IndDeg.comp {m m' : ℕ} {Φ : (Fin m → F) → F} {d : ℕ} (hΦ : IndDeg Φ d) (e : Fin m → Fin m')
    (he : Function.Injective e) : IndDeg (fun r : Fin m' → F ↦ Φ (r ∘ e)) d := fun r i ↦ by
  classical
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    obtain ⟨p, hp, hpe⟩ := hΦ (r ∘ e) j
    refine ⟨p, hp, fun c ↦ ?_⟩
    rw [← hpe c]
    show Φ (Function.update r (e j) c ∘ e) = _
    congr 1
    funext j'
    simp only [Function.comp, Function.update]
    by_cases hj : j' = j
    · subst hj; simp
    · rw [dif_neg (fun h ↦ hj (he h)), dif_neg hj]
  · have hi' : ∀ j, e j ≠ i := fun j h ↦ hi ⟨j, h⟩
    refine ⟨C (Φ (r ∘ e)), by simp, fun c ↦ ?_⟩
    simp only [eval_C]
    show Φ (Function.update r i c ∘ e) = _
    congr 1
    funext j'
    simp [Function.comp, Function.update, hi' j']

/-- Binding the lowest coordinate keeps the individual degree. -/
theorem IndDeg.cons {m : ℕ} {Φ : (Fin (m + 1) → F) → F} {d : ℕ} (hΦ : IndDeg Φ d) (x₀ : F) :
    IndDeg (fun r : Fin m → F ↦ Φ (Fin.cons x₀ r)) d := fun r i ↦ by
  obtain ⟨p, hp, hpe⟩ := hΦ (Fin.cons x₀ r) i.succ
  refine ⟨p, hp, fun c ↦ ?_⟩
  rw [← hpe c, ← Fin.cons_update]

/-- In the lowest coordinate. -/
theorem IndDeg.zero {m : ℕ} {Φ : (Fin (m + 1) → F) → F} {d : ℕ} (hΦ : IndDeg Φ d)
    (r : Fin m → F) : ∃ p : F[X], p.natDegree ≤ d ∧ ∀ c, Φ (Fin.cons c r) = p.eval c := by
  obtain ⟨p, hp, hpe⟩ := hΦ (Fin.cons 0 r) 0
  refine ⟨p, hp, fun c ↦ ?_⟩
  rw [← hpe c, Fin.update_cons_zero]

theorem indDeg_coord {m : ℕ} (j : Fin m) : IndDeg (fun r : Fin m → F ↦ r j) 1 := fun r i ↦ by
  by_cases h : i = j
  · subst h
    exact ⟨X, natDegree_X_le, fun c ↦ by simp⟩
  · exact ⟨C (r j), by simp, fun c ↦ by simp [Function.update, Ne.symm h]⟩

theorem indDeg_eq1 {m : ℕ} (j : Fin m) (b : Bool) : IndDeg (fun r : Fin m → F ↦ eq1 (r j) b) 1 := by
  cases b
  · have := (indDeg_const (m := m) (1 : F) 1).add ((indDeg_coord (F := F) j).const_mul (-1))
    simpa [sub_eq_add_neg] using this
  · simpa using indDeg_coord (F := F) j

/-- A product of functions of distinct coordinates, each of degree `1` in its own. -/
theorem indDeg_eqP {m : ℕ} (b : Cube m) : IndDeg (fun x : Fin m → F ↦ eqP x b) 1 := fun r i ↦ by
  classical
  refine ⟨C (∏ j ∈ Finset.univ.erase i, eq1 (r j) (b j)) * (if b i then X else 1 - X), ?_, ?_⟩
  · refine (natDegree_C_mul_le _ _).trans ?_
    split
    · exact natDegree_X_le
    · rw [sub_eq_add_neg, ← C_1]
      exact (natDegree_add_le _ _).trans
        (max_le (by simp) (by rw [natDegree_neg]; exact natDegree_X_le))
  · intro c
    show eqP (Function.update r i c) b = _
    rw [eqP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    rw [Finset.prod_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
    simp only [eval_mul, eval_C, eq1]
    split <;> simp [mul_comm]

theorem indDeg_mle {m : ℕ} (t : Cube m → F) : IndDeg (mle t) 1 := by
  have := IndDeg.sum (Finset.univ : Finset (Cube m)) (Φ := fun b x ↦ t b * eqP x b) (d := 1)
    fun b _ ↦ (indDeg_eqP b).const_mul (t b)
  exact this

end Ring

end FlockSound
