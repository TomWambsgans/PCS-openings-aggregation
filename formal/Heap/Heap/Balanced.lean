-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Heap.Bus
import Lv42.Protocol.Spine.Instance

/-!
# `Balanced`, but with probability at most `4·N/|E|`

`Lv42.Protocol.M3Instance.Balanced q` is `(I.tuples q .push).Perm (I.tuples q .pull)`: the
executed rows' flushes and the boundary blocks' tuples, push against pull, as multisets. A heap
layout **realizes** the bus of a stack `q` (`Realizes`) when its push tuples (its blocks' and the
state boundary's push at the root) are a permutation of `I.tuples q .push`, and its pull tuples of
`I.tuples q .pull`; then `Balanced q` is the heap's own balance (`Realizes.balanced_iff`), and:

* **`prob_sat_not_balanced`**: for a well-formed layout that realizes the bus of `q`, the heap
  holds at a uniform `(α, β)` while `q` is not balanced with probability at most `busError N`
  (`= 4·N/|E|`), `N` bounding both sides' tuple counts (`busCount`, a function of the instance
  alone, `length_tuples`);
* **`prob_exists_candidate_le`**: the same union-bounded over a list `L` of candidate stacks (a
  WHIR root's level-0 Johnson list), each with its layout: at most `busError (L.length · N)`
  (`= L.length · busError N`, `busError_mul`). The challenges are drawn after the stacks are fixed.

The events are in the form the reduction's round errors take (a lost state, `¬ Balanced q`, and
a challenge that wins it, `Sat`), counted (`card_*`) and as `Pr` over `$ᵗ ((Fin 4 → E) × E)`.
-/

namespace Heap

open LeanVM.Parameters Lv42.Protocol Finset OracleComp
open scoped ENNReal

variable (I : M3Instance)

/-- **The tuple count of one side of the bus**: every executed row of every flush of that side,
and every row of every boundary block of that side. It depends on the instance alone. -/
def busCount (s : Side) : ℕ :=
  ((List.finRange I.ntab).map fun j ↦
      ((I.flushes j).filter fun f ↦ decide (f.1 = s)).length * I.rows j).sum +
    ((I.boundary.filter fun b ↦ decide (b.side = s)).map fun b ↦ 2 ^ b.κ).sum

theorem length_executed (j : Fin I.ntab) : (I.executed j).length = I.rows j := by
  rw [M3Instance.executed_eq, List.length_map, List.length_finRange]

/-- Every stack has `busCount` tuples on each side. -/
theorem length_tuples (q : LeanVM.Protocol.Column I.μ) (s : Side) :
    (I.tuples q s).length = busCount I s := by
  simp only [M3Instance.tuples, M3Instance.flushTuples, M3Instance.boundaryTuples, List.length_append,
    List.length_flatMap, List.length_map, length_executed, List.length_finRange, busCount,
    List.map_const', List.sum_replicate, smul_eq_mul]

variable {I}

/-- **A heap layout realizes the bus of the stack `q`**: its push tuples are a permutation of the
instance's push tuples, its pull tuples of the instance's pull tuples. -/
structure Realizes (q : LeanVM.Protocol.Column I.μ) (D : HeapData) : Prop where
  push : D.pushes.Perm (I.tuples q .push)
  pull : D.pulls.Perm (I.tuples q .pull)

/-- Where the layout realizes the bus, `Balanced` is the heap's own balance. -/
theorem Realizes.balanced_iff {q : LeanVM.Protocol.Column I.μ} {D : HeapData}
    (h : Realizes q D) : I.Balanced q ↔ D.pushes.Perm D.pulls :=
  ⟨fun hb ↦ h.push.trans (hb.trans h.pull.symm), fun hp ↦ h.push.symm.trans (hp.trans h.pull)⟩

/-- **`Balanced` through the fingerprints**: a stack whose bus is not balanced has equal push and
pull products at a uniform `(α, β)` with probability at most `busError N`. -/
theorem prob_products_eq_of_not_balanced {q : LeanVM.Protocol.Column I.μ} (hb : ¬ I.Balanced q)
    {N : ℕ} (hpush : busCount I .push ≤ N) (hpull : busCount I .pull ≤ N) :
    Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[fpProd (fp ab.1 ab.2) (I.tuples q .push) =
      fpProd (fp ab.1 ab.2) (I.tuples q .pull)] ≤ busError N :=
  prob_fpProd_eq_le hb (by rw [length_tuples]; exact hpush) (by rw [length_tuples]; exact hpull)

open Classical in
/-- **The bus's soundness, counting form.** For a well-formed layout realizing the bus of `q`, at
most `4·N·|E|⁴` challenges `(α, β)` make the heap hold while `q` is not balanced. -/
theorem card_sat_not_balanced_le {q : LeanVM.Protocol.Column I.μ} {D : HeapData}
    (hD : D.WellFormed) (hR : Realizes q D) {N : ℕ} (hpush : busCount I .push ≤ N)
    (hpull : busCount I .pull ≤ N) :
    (univ.filter fun ab : (Fin 4 → E) × E ↦ D.Sat ab.1 ab.2 ∧ ¬ I.Balanced q).card ≤
      4 * N * Fintype.card E ^ 4 := by
  by_cases hb : I.Balanced q
  · simp [hb]
  · refine (card_le_card fun ab hab ↦ ?_).trans (D.card_sat_le hD
      (fun hp ↦ hb (hR.balanced_iff.mpr hp))
      (by rw [hR.push.length_eq, length_tuples]; exact hpush)
      (by rw [hR.pull.length_eq, length_tuples]; exact hpull))
    rw [mem_filter] at hab ⊢
    exact ⟨hab.1, hab.2.1⟩

/-- **The bus's soundness.** For a well-formed heap layout realizing the bus of the stack `q`, a
uniform `(α, β)` makes the heap hold while `q` is not balanced with probability at most
`busError N = 4·N/|E|`, `N` bounding both sides' tuple counts. -/
theorem prob_sat_not_balanced {q : LeanVM.Protocol.Column I.μ} {D : HeapData}
    (hD : D.WellFormed) (hR : Realizes q D) {N : ℕ} (hpush : busCount I .push ≤ N)
    (hpull : busCount I .pull ≤ N) :
    Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[D.Sat ab.1 ab.2 ∧ ¬ I.Balanced q] ≤ busError N := by
  classical
  exact prob_le_busError_of_card_le _ (card_sat_not_balanced_le hD hR hpush hpull)

/-! ## Union-bounded over a list of candidates -/

/-- `busError (L·N) = L · busError N`. -/
theorem busError_mul (L N : ℕ) : busError (L * N) = (L : ℝ≥0∞) * busError N := by
  rw [busError, busError, ← mul_div_assoc]
  congr 1
  push_cast
  ring

open Classical in
/-- **Over a list of candidate stacks, counting form.** Every candidate `q ∈ L` with its own
well-formed layout `D q` realizing its bus: at most `L.length · 4·N·|E|⁴` challenges make some
candidate's heap hold while that candidate is not balanced. -/
theorem card_exists_candidate_le (L : List (LeanVM.Protocol.Column I.μ))
    (D : LeanVM.Protocol.Column I.μ → HeapData)
    (hD : ∀ q ∈ L, (D q).WellFormed ∧ Realizes q (D q)) {N : ℕ}
    (hpush : busCount I .push ≤ N) (hpull : busCount I .pull ≤ N) :
    (univ.filter fun ab : (Fin 4 → E) × E ↦ ∃ q ∈ L, (D q).Sat ab.1 ab.2 ∧ ¬ I.Balanced q).card ≤
      L.length * (4 * N * Fintype.card E ^ 4) := by
  induction L with
  | nil => simp
  | cons q L ih =>
    have hq := hD q (List.mem_cons_self ..)
    have ih' := ih fun q' hq' ↦ hD q' (List.mem_cons_of_mem _ hq')
    have hsub : (univ.filter fun ab : (Fin 4 → E) × E ↦
          ∃ q' ∈ q :: L, (D q').Sat ab.1 ab.2 ∧ ¬ I.Balanced q') ⊆
        (univ.filter fun ab : (Fin 4 → E) × E ↦ (D q).Sat ab.1 ab.2 ∧ ¬ I.Balanced q) ∪
          (univ.filter fun ab : (Fin 4 → E) × E ↦
            ∃ q' ∈ L, (D q').Sat ab.1 ab.2 ∧ ¬ I.Balanced q') := by
      intro ab hab
      simp only [mem_filter, mem_univ, true_and, mem_union, List.mem_cons] at hab ⊢
      obtain ⟨q', hq' | hq', h⟩ := hab
      · subst hq'
        exact Or.inl h
      · exact Or.inr ⟨q', hq', h⟩
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    rw [List.length_cons, add_mul, one_mul, add_comm]
    exact add_le_add ih' (card_sat_not_balanced_le hq.1 hq.2 hpush hpull)

/-- **Over a list of candidate stacks.** Every candidate `q ∈ L` with its own well-formed layout
`D q` realizing its bus: a uniform `(α, β)` makes some candidate's heap hold while that candidate
is not balanced with probability at most `busError (L.length · N) = L.length · busError N`. -/
theorem prob_exists_candidate_le (L : List (LeanVM.Protocol.Column I.μ))
    (D : LeanVM.Protocol.Column I.μ → HeapData)
    (hD : ∀ q ∈ L, (D q).WellFormed ∧ Realizes q (D q)) {N : ℕ}
    (hpush : busCount I .push ≤ N) (hpull : busCount I .pull ≤ N) :
    Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[∃ q ∈ L, (D q).Sat ab.1 ab.2 ∧ ¬ I.Balanced q] ≤
      busError (L.length * N) := by
  classical
  refine prob_le_busError_of_card_le _ ?_
  have := card_exists_candidate_le L D hD hpush hpull
  calc _ ≤ L.length * (4 * N * Fintype.card E ^ 4) := this
    _ = 4 * (L.length * N) * Fintype.card E ^ 4 := by ring

end Heap
