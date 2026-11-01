import QuotientSecurity

/-! Review experiment 2: the end theorems quantify over every `Instance`; at the identity wiring
and zero weights, `Relation` holds of every statement, so `Instance.soundness` there says nothing
about any statement being true. -/

open QuotientSecurity

namespace Review

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

/-- The cell of the region holding word `J`: bits 8, 9, 10 spell `J`, every other bit zero. -/
def xJ (J : Fin 8) : Fin (22 + 2) → Bool := fun j =>
  if (j : ℕ) = 8 then decide ((J : ℕ) % 2 = 1)
  else if (j : ℕ) = 9 then decide ((J : ℕ) / 2 % 2 = 1)
  else if (j : ℕ) = 10 then decide ((J : ℕ) / 4 % 2 = 1) else false

theorem wordOf_xJ (J : Fin 8) : wordOf (xJ J) = J := by
  fin_cases J <;> rfl

/-- Supported on the `X` and `V` cells of the eight rows `64 J`, where it is `stmt J`. -/
def wDeg (stmt : Fin 8 → F) (x : Fin (22 + 2) → Bool) : F :=
  if x 0 = x 1 ∧ ∀ j : Fin (22 + 2), (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 → (j : ℕ) ≠ 8 → (j : ℕ) ≠ 9 →
      (j : ℕ) ≠ 10 → x j = false
  then stmt (wordOf x) else 0

theorem eq_xJ (J : Fin 8) (x : Fin (22 + 2) → Bool) (h0 : x 0 = false) (h1 : x 1 = false)
    (hz : ∀ j : Fin (22 + 2), (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 → (j : ℕ) ≠ 8 → (j : ℕ) ≠ 9 →
      (j : ℕ) ≠ 10 → x j = false)
    (hw : wordOf x = J) : x = xJ J := by
  have hJ : (x 8).toNat + 2 * (x 9).toNat + 4 * (x 10).toNat = (J : ℕ) := by
    rw [← hw]; rfl
  funext j
  by_cases j0 : (j : ℕ) = 0
  · have : j = 0 := Fin.ext j0
    subst this; simp [h0, xJ]
  by_cases j1 : (j : ℕ) = 1
  · have : j = 1 := Fin.ext j1
    subst this; simp [h1, xJ]
  by_cases j8 : (j : ℕ) = 8
  · have : j = 8 := Fin.ext j8
    subst this
    simp only [xJ]
    cases h8 : x 8 <;> cases h9 : x 9 <;> cases h10 : x 10 <;> simp [h8, h9, h10] at hJ ⊢ <;> omega
  by_cases j9 : (j : ℕ) = 9
  · have : j = 9 := Fin.ext j9
    subst this
    simp only [xJ]
    cases h8 : x 8 <;> cases h9 : x 9 <;> cases h10 : x 10 <;> simp [h8, h9, h10] at hJ ⊢ <;> omega
  by_cases j10 : (j : ℕ) = 10
  · have : j = 10 := Fin.ext j10
    subst this
    simp only [xJ]
    cases h8 : x 8 <;> cases h9 : x 9 <;> cases h10 : x 10 <;> simp [h8, h9, h10] at hJ ⊢ <;> omega
  rw [hz j j0 j1 j8 j9 j10]
  simp [xJ, j8, j9, j10]

/-- **Every statement is in the language** of the instance with the identity wiring and zero
weights, over any Cantor basis. -/
theorem degenerate_relation (B : CantorBasis F (22 + 2)) (stmt : Fin 8 → F) :
    (⟨B, Equiv.refl _, fun _ => 0⟩ : Instance F).Relation stmt (wDeg stmt) := by
  refine ⟨fun y => ?_, fun x => rfl, fun J => ?_⟩
  · -- `X` and `V` of a row hold the same value, `Y` and `C` hold zero: `v + x = 0`.
    have hab : ∀ j : Fin (22 + 2), (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 →
        cellBits (y, 0) j = cellBits (y, 3) j := by
      intro j h0 h1
      obtain ⟨k, rfl⟩ : ∃ k : Fin 22, j = k.succ.succ := by
        refine ⟨⟨(j : ℕ) - 2, by omega⟩, Fin.ext ?_⟩
        simp only [Fin.val_succ]
        omega
      simp [cellBits]
    have hXV : wDeg stmt (cellBits (y, 0)) = wDeg stmt (cellBits (y, 3)) := by
      have h0 : cellBits (y, 0) 0 = cellBits (y, 0) 1 := by simp [cellBits, roleBit0, roleBit1]
      have h3 : cellBits (y, 3) 0 = cellBits (y, 3) 1 := by simp [cellBits, roleBit0, roleBit1]
      have hP : (∀ j : Fin (22 + 2), (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 → (j : ℕ) ≠ 8 → (j : ℕ) ≠ 9 →
            (j : ℕ) ≠ 10 → cellBits (y, 0) j = false) ↔
          (∀ j : Fin (22 + 2), (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 → (j : ℕ) ≠ 8 → (j : ℕ) ≠ 9 →
            (j : ℕ) ≠ 10 → cellBits (y, 3) j = false) :=
        forall_congr' fun j => by
          constructor
          · intro h a b c d e; rw [← hab j a b]; exact h a b c d e
          · intro h a b c d e; rw [hab j a b]; exact h a b c d e
      have hw : wordOf (cellBits (y, 0)) = wordOf (cellBits (y, 3)) := by
        apply Fin.ext
        show (cellBits (y, 0) 8).toNat + 2 * (cellBits (y, 0) 9).toNat
            + 4 * (cellBits (y, 0) 10).toNat
          = (cellBits (y, 3) 8).toNat + 2 * (cellBits (y, 3) 9).toNat
            + 4 * (cellBits (y, 3) 10).toNat
        rw [hab 8 (by decide) (by decide), hab 9 (by decide) (by decide),
          hab 10 (by decide) (by decide)]
      unfold wDeg
      rw [hw]
      by_cases hq : ∀ j : Fin (22 + 2), (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 → (j : ℕ) ≠ 8 →
          (j : ℕ) ≠ 9 → (j : ℕ) ≠ 10 → cellBits (y, 0) j = false
      · rw [if_pos ⟨h0, hq⟩, if_pos ⟨h3, hP.mp hq⟩]
      · rw [if_neg (fun h => hq h.2), if_neg (fun h => hq (hP.mpr h.2))]
    have hY : wDeg stmt (cellBits (y, 1)) = 0 := by simp [wDeg, cellBits, roleBit0, roleBit1]
    have hC : wDeg stmt (cellBits (y, 2)) = 0 := by simp [wDeg, cellBits, roleBit0, roleBit1]
    rw [gate, hY, hC, hXV, mul_zero, add_zero, add_zero, CharTwo.add_self_eq_zero]
  · show ∑ x, regionWeight (fun _ => (0 : F)) J x * wDeg stmt x = stmt J
    rw [Finset.sum_eq_single (xJ J)]
    · have hw : wDeg stmt (xJ J) = stmt J := by
        rw [wDeg, if_pos, wordOf_xJ]
        refine ⟨rfl, fun j a b c d e => ?_⟩
        simp [xJ, c, d, e]
      have hr : regionWeight (fun _ => (0 : F)) J (xJ J) = 1 := by
        rw [regionWeight, if_pos]
        · refine Finset.prod_eq_one fun k hk => ?_
          have hk8 := Finset.mem_range.mp hk
          have : bitAt (xJ J) k = false := by
            simp only [bitAt, xJ]
            split_ifs <;> first | rfl | omega
          simp [this]
        · refine ⟨fun j hj => ?_, wordOf_xJ J⟩
          simp only [xJ]
          split_ifs <;> first | rfl | omega
      rw [hr, hw, one_mul]
    · intro x _ hx
      by_cases hr : (∀ j : Fin (22 + 2), 11 ≤ (j : ℕ) → x j = false) ∧ wordOf x = J
      · by_cases hwx : x 0 = x 1 ∧ ∀ j : Fin (22 + 2), (j : ℕ) ≠ 0 → (j : ℕ) ≠ 1 →
            (j : ℕ) ≠ 8 → (j : ℕ) ≠ 9 → (j : ℕ) ≠ 10 → x j = false
        · cases h0 : x 0
          · exact absurd (eq_xJ J x h0 (hwx.1 ▸ h0) hwx.2 hr.2) hx
          · -- Bit 0 set: its weight has the factor `c 0 = 0`.
            have : regionWeight (fun _ => (0 : F)) J x = 0 := by
              rw [regionWeight, if_pos hr]
              refine Finset.prod_eq_zero (Finset.mem_range.mpr (show 0 < 8 by norm_num)) ?_
              simp [bitAt, h0]
            rw [this, zero_mul]
        · rw [wDeg, if_neg hwx, mul_zero]
      · rw [regionWeight, if_neg hr, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- So `Instance.soundness`, at that instance, bounds an event about a relation whose language
is everything: `∀ stmt, ∃ w, Relation stmt w`. -/
theorem degenerate_language (B : CantorBasis F (22 + 2)) :
    ∀ stmt : Fin 8 → F, ∃ w, (⟨B, Equiv.refl _, fun _ => 0⟩ : Instance F).Relation stmt w :=
  fun stmt => ⟨_, degenerate_relation B stmt⟩

end Review
