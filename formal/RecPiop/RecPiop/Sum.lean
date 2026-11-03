-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Cantor
import Heap.Cantor

/-!
# `Σ_V h` is `h`'s top coefficient

`PI2.md` §2: `Q`'s second claim is at `(1^m, 0, 0, 0, y₀, y₁)`, `h`'s top coefficient in the novel
basis, and it stands for `Σ_V h`, the copy argument's sum. For a table `c` on `m` variables and its
polynomial in the novel basis (`QuotientSecurity.tablePoly`, `Σ_b c_b Π_{b_k} w_k`), the sum over
the points `ω_i`, `i < 2^m`, of a Cantor basis is the table's entry at all ones
(`sum_tablePoly_omega`): this repository's `QuotientSecurity.sum_tablePoly` and `mle_ones`, on the
positions' points `Heap.omega` (`omega_eq_point`).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset QuotientSecurity

variable {F : Type} [Field F] [CharP F 2]

/-- A position below `2^m` is the point of its `m` bits. -/
theorem omega_eq_point {n m : ℕ} (B : CantorBasis F n) (hm : m ≤ n) {i : ℕ} (hi : i < 2 ^ m) :
    Heap.omega B i = B.point (fun k : Fin m => i.testBit k) := by
  unfold Heap.omega CantorBasis.point
  rw [← Finset.sum_range (fun k => if i.testBit k then B.β k else 0)]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hm) fun k _ hk => ?_
  have hk' : m ≤ k := by simpa using hk
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk'))]
  simp

/-- The bits of the positions below `2^m` are all the `m`-bit vectors, each once. -/
theorem image_bits (m : ℕ) :
    (range (2 ^ m)).image (fun i => fun k : Fin m => i.testBit k) = univ ∧
      Set.InjOn (fun i => fun k : Fin m => i.testBit k) (range (2 ^ m) : Set ℕ) := by
  have hinj : Set.InjOn (fun i => fun k : Fin m => i.testBit k) (range (2 ^ m) : Set ℕ) := by
    intro i hi j hj h
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    refine Nat.eq_of_testBit_eq fun k => ?_
    by_cases hk : k < m
    · exact congrFun h ⟨k, hk⟩
    · have hk' : m ≤ k := by omega
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk')),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hk'))]
  refine ⟨Finset.eq_univ_of_card _ ?_, hinj⟩
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  simp

/-- **`Σ_V h` is `h`'s top coefficient**: for a table `c` on `m ≤ n` variables, the sum of its
novel-basis polynomial over the points of the positions below `2^m` is its entry at all ones. -/
theorem sum_tablePoly_omega {n m : ℕ} (B : CantorBasis F n) (hm : m ≤ n)
    (c : (Fin m → Bool) → F) :
    ∑ i ∈ range (2 ^ m), (tablePoly c).eval (Heap.omega B i) = c (fun _ => true) := by
  rw [← mle_ones c, ← sum_tablePoly B hm c]
  obtain ⟨himg, hinj⟩ := image_bits m
  rw [← himg, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun i hi => by rw [omega_eq_point B hm (Finset.mem_range.mp hi)]

end RecPiop
