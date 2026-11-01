-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/RoundOne.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Cells
import QuotientSecurity.Counting

/-!
# The first challenge

If the cells of the first message do not satisfy the relation, few triples `(α, β, γ)` admit a
consistent second message: at most `(4 N + words) q^2`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] (P : Params F)

namespace Params

/-- The number of cells. -/
abbrev nCells : ℕ := Fintype.card (P.T × Fin 4)

open Classical in
/-- **The first challenge.** If the cells of the first message do not satisfy the relation, then
at most `(4 N + words) q^2` of the `q^3` triples admit a consistent second message.

If a gate fails while the copies and the words hold, a consistent triple makes a denominator
vanish on a cell: at most `2 N q^2`. If the copies hold and a word fails, add the `γ` at which a
nonzero polynomial of degree below `words` vanishes: `(2 N + words) q^2`. If a copy fails, a
consistent triple has, at every cell, both denominators zero or neither
(`consistent_denominators`), and where none vanishes a sum of logarithmic derivatives equal to a
target depending on `γ` (`consistent_on_cells`): at most `(4 N - 2) q^2` (`card_copy_triple_le`:
`2 N - 2` values of `β` cancel the pole of a failed copy, and otherwise at most `2 N` values of
`α`). -/
theorem card_consistent_le (stmt : Fin P.words → F) (g : Witness F)
    (hsat : ¬ P.Sat stmt (cells P g)) :
    (univ.filter fun p : F × F × F => ∃ R, P.Consistent stmt g R p.1 p.2.1 p.2.2).card
      ≤ (4 * P.nCells + P.words) * Fintype.card F ^ 2 := by
  set w := cells P g with hw
  set A := univ.filter fun p : F × F × F => ∃ R, P.Consistent stmt g R p.1 p.2.1 p.2.2 with hA
  set Z := univ.filter fun p : F × F × F =>
    ∃ i, p.1 + w i + p.2.1 * P.pt i = 0 ∨ p.1 + w i + p.2.1 * P.pt (P.σ i) = 0 with hZ
  have hZcard : Z.card ≤ 2 * P.nCells * Fintype.card F ^ 2 := card_zero_le P.pt P.σ w
  -- Outside `Z`, a consistent message forces the gates and the sum.
  have hout : ∀ p ∈ A, p ∉ Z →
      (∀ x : P.T, gate (w (x, 0)) (w (x, 1)) (w (x, 2)) (w (x, 3)) = 0) ∧
        logSum P.pt P.σ w p.1 p.2.1 + ∑ J : Fin P.words, p.2.2 ^ (J : ℕ) * P.wordSum J w
          = P.target stmt p.2.2 := by
    intro p hp hpZ
    rw [hA, Finset.mem_filter] at hp
    obtain ⟨-, R, hR⟩ := hp
    rw [hZ, Finset.mem_filter, not_and, not_exists] at hpZ
    have hz := hpZ (Finset.mem_univ _)
    exact P.consistent_on_cells stmt g R _ _ _ hR (fun i h => hz i (Or.inl h))
      (fun i h => hz i (Or.inr h))
  by_cases hcopy : ∀ i, w (P.σ i) = w i
  · by_cases hwords : ∀ J, P.wordSum J w = stmt J
    · -- Only a gate can fail, and then no triple outside `Z` is consistent.
      have hsub : A ⊆ Z := by
        intro p hp
        by_contra hpZ
        exact hsat ⟨(hout p hp hpZ).1, hcopy, hwords⟩
      calc A.card ≤ Z.card := Finset.card_le_card hsub
        _ ≤ 2 * P.nCells * Fintype.card F ^ 2 := hZcard
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · -- The copies hold, so the public words alone must meet the target.
      set e : Fin P.words → F := fun J => P.wordSum J w + stmt J with he
      have he0 : e ≠ 0 := by
        intro h
        apply hwords
        intro J
        have := congrFun h J
        exact CharTwo.add_eq_zero.mp this
      set G := univ.filter fun γ : F => ∑ J : Fin P.words, γ ^ (J : ℕ) * e J = 0 with hG
      have hGcard : G.card ≤ P.words := card_powers_le e he0
      have hsub : A ⊆ Z ∪ (univ ×ˢ (univ ×ˢ G)) := by
        intro p hp
        by_cases hpZ : p ∈ Z
        · exact Finset.mem_union_left _ hpZ
        · refine Finset.mem_union_right _ ?_
          have h := (hout p hp hpZ).2
          rw [logSum_eq_zero_of_copy P.pt P.σ w hcopy, zero_add] at h
          simp only [Finset.mem_product, Finset.mem_univ, true_and, hG, Finset.mem_filter]
          have : ∑ J : Fin P.words, p.2.2 ^ (J : ℕ) * e J
              = ∑ J : Fin P.words, p.2.2 ^ (J : ℕ) * P.wordSum J w + P.target stmt p.2.2 := by
            rw [target, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun J _ => by rw [he]; ring
          rw [this, h]
          exact CharTwo.add_self_eq_zero _
      calc A.card ≤ (Z ∪ (univ ×ˢ (univ ×ˢ G))).card := Finset.card_le_card hsub
        _ ≤ Z.card + (univ ×ˢ (univ ×ˢ G) : Finset (F × F × F)).card := Finset.card_union_le _ _
        _ ≤ 2 * P.nCells * Fintype.card F ^ 2 + Fintype.card F * (Fintype.card F * P.words) := by
            rw [Finset.card_product, Finset.card_product, Finset.card_univ]
            gcongr
        _ ≤ _ := by nlinarith [Nat.zero_le (P.nCells * Fintype.card F ^ 2)]
  · -- A copy fails: at each cell both denominators vanish or neither, and where none does, the
    -- sum is a nonzero rational function of `α` for all but `2 N - 2` values of `β`.
    set c : F → F := fun γ =>
      P.target stmt γ + ∑ J : Fin P.words, γ ^ (J : ℕ) * P.wordSum J w with hc
    set S := univ.filter fun p : F × F × F =>
      (∀ x, p.1 + w x + p.2.1 * P.pt x = 0 ↔ p.1 + w x + p.2.1 * P.pt (P.σ x) = 0) ∧
        ((∀ x, p.1 + w x + p.2.1 * P.pt x ≠ 0) → logSum P.pt P.σ w p.1 p.2.1 = c p.2.2) with hS
    have hScard : S.card ≤ (4 * P.nCells - 2) * Fintype.card F ^ 2 :=
      card_copy_triple_le P.pt P.pt_injective P.σ w hcopy c
    have hsub : A ⊆ S := by
      intro p hp
      rw [hA, Finset.mem_filter] at hp
      obtain ⟨-, R, hR⟩ := hp
      have hiff := P.consistent_denominators stmt g R _ _ _ hR
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hiff, fun hall => ?_⟩
      have h := (P.consistent_on_cells stmt g R _ _ _ hR hall
        fun i h => hall i ((hiff i).mpr h)).2
      show logSum P.pt P.σ w p.1 p.2.1
        = P.target stmt p.2.2 + ∑ J : Fin P.words, p.2.2 ^ (J : ℕ) * P.wordSum J w
      rw [← h, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    calc A.card ≤ S.card := Finset.card_le_card hsub
      _ ≤ (4 * P.nCells - 2) * Fintype.card F ^ 2 := hScard
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end Params

end QuotientSecurity
