-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Cube
import Mathlib.Tactic.LinearCombination

/-!
# A nonzero table at a point drawn coordinate by coordinate

A family of tables `t i` on the cube, not all zero, is evaluated (`mle`) at a point whose
coordinates are drawn one at a time, lowest first. Binding a coordinate at `x` folds a table
(`fold t x = (1 - x) t(0, ·) + x t(1, ·)`); a nonzero table folds to zero for one `x` at most. So
the family stays nonzero, and its extensions at the point are not all zero, unless some coordinate
falls in its bad set (`pointBad`, at most one value, a function of the coordinates before it).

This is the zerocheck point's argument (`τ`, after the fixed coordinates) and the constant
position's (the batch coordinates of the zerocheck's challenges). Nothing here transcribes a
source.
-/

namespace FlockSound

open Finset

variable {F : Type*} [Field F]

/-- Bind the lowest coordinate of a table at `x`. -/
def fold {m : ℕ} (t : Cube (m + 1) → F) (x : F) : Cube m → F :=
  fun b ↦ (1 - x) * t (Fin.cons false b) + x * t (Fin.cons true b)

theorem mle_cons_fold {m : ℕ} (t : Cube (m + 1) → F) (x : F) (r : Fin m → F) :
    mle t (Fin.cons x r) = mle (fold t x) r := by
  rw [mle_cons]
  show _ = mle (fun b ↦ (1 - x) * t (Fin.cons false b) + x * t (Fin.cons true b)) r
  rw [mle_add, mle_smul, mle_smul]

section Bad

variable [Fintype F] [DecidableEq F] {ι : Type*}

/-- **The bad coordinates**: coordinate `0`'s, where every table of a family that is not all zero
folds to zero; coordinate `j + 1`'s, those of the family folded at coordinate `0`. -/
noncomputable def pointBad : (m : ℕ) → (ι → Cube m → F) → (Fin m → F) → Fin m → Finset F
  | 0, _, _, j => j.elim0
  | m + 1, t, χ, j => Fin.cases
      (by classical exact if ∃ i, t i ≠ 0 then univ.filter fun x ↦ ∀ i, fold (t i) x = 0 else ∅)
      (fun j ↦ pointBad m (fun i ↦ fold (t i) (χ 0)) (Fin.tail χ) j) j

/-- A nonzero table folds to zero at one point at most. -/
theorem card_fold_zero_le {m : ℕ} {t : Cube (m + 1) → F} (ht : t ≠ 0) :
    (univ.filter fun x ↦ fold t x = 0).card ≤ 1 := by
  obtain ⟨b, hb⟩ : ∃ b, t b ≠ 0 := by
    by_contra h
    push Not at h
    exact ht (funext h)
  obtain ⟨b₀, c, rfl⟩ : ∃ b₀ c, b = Fin.cons b₀ c := ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
  refine Finset.card_le_one.mpr fun x hx y hy ↦ ?_
  rw [Finset.mem_filter] at hx hy
  have hx' := congrFun hx.2 c
  have hy' := congrFun hy.2 c
  simp only [fold, Pi.zero_apply] at hx' hy'
  set a := t (Fin.cons false c)
  set a' := t (Fin.cons true c)
  -- `(1 - x) a + x a' = a + x (a' - a)`.
  have hxa : a + x * (a' - a) = 0 := by linear_combination hx'
  have hya : a + y * (a' - a) = 0 := by linear_combination hy'
  by_cases hd : a' - a = 0
  · exfalso
    have ha : a = 0 := by simpa [hd] using hxa
    have ha' : a' = 0 := by rw [sub_eq_zero] at hd; rw [hd, ha]
    cases b₀
    · exact hb ha
    · exact hb ha'
  · exact mul_right_cancel₀ hd (add_left_cancel (hxa.trans hya.symm))

theorem card_pointBad_le : ∀ (m : ℕ) (t : ι → Cube m → F) (χ : Fin m → F) (j : Fin m),
    (pointBad m t χ j).card ≤ 1
  | 0, _, _, j => j.elim0
  | m + 1, t, χ, j => by
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · classical
      simp only [pointBad, Fin.cases_zero]
      split_ifs with h
      · obtain ⟨i, hi⟩ := h
        refine (Finset.card_le_card fun x hx ↦ ?_).trans (card_fold_zero_le hi)
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_univ _, hx.2 i⟩
      · simp
    · simp only [pointBad, Fin.cases_succ]
      exact card_pointBad_le m _ _ j

/-- The bad coordinates depend on the coordinates before them only. -/
theorem pointBad_congr : ∀ (m : ℕ) (t : ι → Cube m → F) (χ χ' : Fin m → F) (j : Fin m),
    (∀ i : Fin m, i.val < j.val → χ i = χ' i) → pointBad m t χ j = pointBad m t χ' j
  | 0, _, _, _, j, _ => j.elim0
  | m + 1, t, χ, χ', j, h => by
    refine Fin.cases (fun _ ↦ ?_) (fun j h ↦ ?_) j h
    · simp only [pointBad, Fin.cases_zero]
    · simp only [pointBad, Fin.cases_succ]
      rw [h 0 (Nat.succ_pos _)]
      exact pointBad_congr m _ _ _ j fun i hi ↦ h i.succ (by simpa using hi)

/-- **A family not all zero stays so at the point** unless a coordinate is bad. -/
theorem point_escape : ∀ (m : ℕ) (t : ι → Cube m → F) (χ : Fin m → F), (∃ i, t i ≠ 0) →
    (∀ j, χ j ∉ pointBad m t χ j) → ∃ i, mle (t i) χ ≠ 0
  | 0, t, χ, ⟨i, hi⟩, _ => by
    refine ⟨i, fun h ↦ hi (funext fun b ↦ ?_)⟩
    have hb : b = fun j ↦ j.elim0 := funext fun j ↦ j.elim0
    have hχ : χ = cube b := funext fun j ↦ j.elim0
    rw [hχ, mle_cube] at h
    simpa using h
  | m + 1, t, χ, hne, hgood => by
    classical
    have h0 := hgood 0
    simp only [pointBad, Fin.cases_zero, if_pos hne, Finset.mem_filter, Finset.mem_univ,
      true_and] at h0
    push Not at h0
    obtain ⟨i, hi⟩ := h0
    obtain ⟨i', hi'⟩ := point_escape m (fun i ↦ fold (t i) (χ 0)) (Fin.tail χ) ⟨i, hi⟩
      fun j ↦ by
        have := hgood j.succ
        simp only [pointBad, Fin.cases_succ] at this
        exact this
    refine ⟨i', ?_⟩
    rw [← Fin.cons_self_tail χ, mle_cons_fold]
    exact hi'

end Bad

end FlockSound
