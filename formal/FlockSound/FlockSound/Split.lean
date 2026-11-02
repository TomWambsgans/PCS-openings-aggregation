-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Cube

/-!
# Splitting the cube into blocks of coordinates

`Fin.append` puts a point of `Fin a → F` in the low coordinates and one of `Fin b → F` in the high:
the cube sum, the `eq` weights and the multilinear extension split accordingly. Nothing here
transcribes a source.
-/

namespace FlockSound

open Finset

section Ring

variable {F : Type*} [CommRing F]

/-- The low block of a point. -/
def lowPart {a b : ℕ} {α : Type*} (x : Fin (a + b) → α) : Fin a → α := fun j ↦ x (Fin.castAdd b j)

/-- The high block of a point. -/
def highPart {a b : ℕ} {α : Type*} (x : Fin (a + b) → α) : Fin b → α := fun j ↦ x (Fin.natAdd a j)

theorem sum_cube_append {M : Type*} [AddCommMonoid M] {a b : ℕ} (f : Cube (a + b) → M) :
    ∑ x, f x = ∑ x : Cube a, ∑ y : Cube b, f (Fin.append x y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.appendEquiv a b) _ _ fun _ ↦ rfl).symm

theorem eqP_append {a b : ℕ} (x : Fin a → F) (y : Fin b → F) (bx : Cube a) (by' : Cube b) :
    eqP (Fin.append x y) (Fin.append bx by') = eqP x bx * eqP y by' := by
  simp only [eqP, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

theorem cube_append {a b : ℕ} (bx : Cube a) (by' : Cube b) :
    (cube (Fin.append bx by') : Fin (a + b) → F) = Fin.append (cube bx) (cube by') := by
  funext i
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;> simp [cube]

/-- The extension at a split point: the high block's extension of the low block's. -/
theorem mle_append {a b : ℕ} (t : Cube (a + b) → F) (x : Fin a → F) (y : Fin b → F) :
    mle t (Fin.append x y) = mle (fun by' ↦ mle (fun bx ↦ t (Fin.append bx by')) x) y := by
  simp only [mle, sum_cube_append, eqP_append, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun by' _ ↦ Finset.sum_congr rfl fun bx _ ↦ ?_
  ring

theorem append_lowPart_highPart {a b : ℕ} {α : Type*} (x : Fin (a + b) → α) :
    Fin.append (lowPart x) (highPart x) = x :=
  Fin.append_castAdd_natAdd

@[simp] theorem lowPart_append {a b : ℕ} {α : Type*} (x : Fin a → α) (y : Fin b → α) :
    lowPart (Fin.append x y) = x := funext fun j ↦ Fin.append_left x y j

@[simp] theorem highPart_append {a b : ℕ} {α : Type*} (x : Fin a → α) (y : Fin b → α) :
    highPart (Fin.append x y) = y := funext fun j ↦ Fin.append_right x y j

/-- A table of the high coordinates only extends to its own extension there. -/
theorem mle_high {a b : ℕ} (t : Cube b → F) (x : Fin a → F) (y : Fin b → F) :
    mle (fun c : Cube (a + b) ↦ t (highPart c)) (Fin.append x y) = mle t y := by
  rw [mle_append]
  simp only [highPart_append, mle_const]

/-- A table of the low coordinates only extends to its own extension there. -/
theorem mle_low {a b : ℕ} (t : Cube a → F) (x : Fin a → F) (y : Fin b → F) :
    mle (fun c : Cube (a + b) ↦ t (lowPart c)) (Fin.append x y) = mle t x := by
  rw [mle_append]
  simp only [lowPart_append, mle_const]

/-- Moving the outer of four sums innermost. -/
theorem sum_comm_in3 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.sum_comm]

theorem mle_split {a b : ℕ} (t : Cube (a + b) → F) (x : Fin (a + b) → F) :
    mle t x = mle (fun by' ↦ mle (fun bx ↦ t (Fin.append bx by')) (lowPart x)) (highPart x) := by
  conv_lhs => rw [← append_lowPart_highPart x]
  exact mle_append t _ _

/-- `Σ_b eq(x, b) eq(y, b) = Π_j (x_j y_j + (1 - x_j)(1 - y_j))`: the Rust's `eq_eval`. -/
def eqEval {m : ℕ} (x y : Fin m → F) : F := ∏ j, (x j * y j + (1 - x j) * (1 - y j))

theorem sum_eqP_mul_eqP {m : ℕ} (x y : Fin m → F) : ∑ b : Cube m, eqP x b * eqP y b = eqEval x y := by
  induction m with
  | zero => simp [eqP, eqEval]
  | succ m ih =>
    rw [sum_cube_succ, Fintype.sum_bool]
    obtain ⟨x₀, x', rfl⟩ : ∃ x₀ x', x = Fin.cons x₀ x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    obtain ⟨y₀, y', rfl⟩ : ∃ y₀ y', y = Fin.cons y₀ y' := ⟨y 0, Fin.tail y, (Fin.cons_self_tail y).symm⟩
    simp only [eqP_cons, eq1_true, eq1_false]
    have e1 : ∀ b : Cube m, x₀ * eqP x' b * (y₀ * eqP y' b) = x₀ * y₀ * (eqP x' b * eqP y' b) :=
      fun b ↦ by ring
    have e2 : ∀ b : Cube m, (1 - x₀) * eqP x' b * ((1 - y₀) * eqP y' b) =
        (1 - x₀) * (1 - y₀) * (eqP x' b * eqP y' b) := fun b ↦ by ring
    simp only [e1, e2, ← Finset.mul_sum, ih, eqEval, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring

/-- The extension of `eq(x, ·)` at `y` is `eqEval x y`. -/
theorem mle_eqP {m : ℕ} (x y : Fin m → F) : mle (fun b ↦ eqP x b) y = eqEval x y := by
  rw [mle, sum_eqP_mul_eqP]

/-- Reversing the coordinates keeps a cube sum. -/
theorem sum_cube_rev {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Cube m → M) :
    ∑ b, f b = ∑ b : Cube m, f (fun j ↦ b (Fin.rev j)) :=
  (Fintype.sum_equiv (Equiv.arrowCongr Fin.revPerm (Equiv.refl Bool)) _ _ fun b ↦ by
    congr 1
    funext j
    simp [Equiv.arrowCongr, Fin.revPerm]).trans rfl

end Ring

end FlockSound
