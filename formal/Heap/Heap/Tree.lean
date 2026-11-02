-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# The product heap's tree

The univariate PIOP's bus (`crates/leanvm_univariate/SPEC.md` §5.2, branch `leanvm-univariate`)
is a binary heap of depth `n`: position `i` holds node `i` for `1 ≤ i < 2^n`, the root at `1`,
the children of `p` at `2p` and `2p + 1`, the leaves at `[2^(n-1), 2^n)`. Position `0` is no
node. On positions, the **tree identity** says that every position `2 ≤ i < 2^n` is a child of
`i >>> 1`, and that its parent holds the product of `i` and of its sibling `i ^^^ 1`
(`TreeHolds`). Then the root holds the product of the leaves (`root_eq_prod_leaves`), level by
level: the product of level `k + 1` is the product of level `k` (`prod_children`).

Generic in the depth `n` and in the commutative monoid of the values. The positions `0` and `1`,
which are no child, are excluded from the identity: `TreeHolds` constrains neither `T 0` nor
anything at `i < 2`. `Heap.Cantor` reads the same identity on the points of a Cantor subspace.
-/

namespace Heap

open Finset

variable {M : Type*} [CommMonoid M]

/-- **The tree identity on positions**: for every position `2 ≤ i < 2^n`, the parent
`i >>> 1` holds the product of `i` and of its sibling `i ^^^ 1`. -/
def TreeHolds (n : ℕ) (T : ℕ → M) : Prop :=
  ∀ i, 2 ≤ i → i < 2 ^ n → T (i >>> 1) = T i * T (i ^^^ 1)

/-- The sibling of an even position is the next one. -/
theorem two_mul_xor_one (p : ℕ) : (2 * p) ^^^ 1 = 2 * p + 1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  have h1 := Nat.testBit_two_pow_mul_add p (show 1 < 2 ^ 1 by norm_num) j
  have h0 := Nat.testBit_two_pow_mul_add p (show 0 < 2 ^ 1 by norm_num) j
  simp only [pow_one, add_zero] at h1 h0
  rw [h1, h0]
  rcases j with _ | j
  · simp
  · have : Nat.testBit 1 (j + 1) = false := Nat.testBit_eq_false_of_lt (by
      have := Nat.one_lt_two_pow (n := j + 1) (by omega); omega)
    simp [this]

/-- The parent of an even position. -/
theorem two_mul_shiftRight_one (p : ℕ) : (2 * p) >>> 1 = p := by
  rw [Nat.shiftRight_one]
  omega

/-- A product over `[2a, 2b)` is a product over `[a, b)` of pairs of siblings. -/
theorem prod_Ico_two_mul (f : ℕ → M) {a b : ℕ} (h : a ≤ b) :
    ∏ i ∈ Ico (2 * a) (2 * b), f i = ∏ p ∈ Ico a b, f (2 * p) * f (2 * p + 1) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [prod_Ico_succ_top hab, ← ih, show 2 * (b + 1) = 2 * b + 1 + 1 by ring,
      prod_Ico_succ_top (by omega), prod_Ico_succ_top (by omega), mul_assoc]

/-- **One level up**: under the tree identity, the nodes `[2a, 2b)` multiply to the nodes
`[a, b)`, their parents, when `1 ≤ a` and `2b ≤ 2^n`. -/
theorem prod_children {n a b : ℕ} {T : ℕ → M} (h : TreeHolds n T) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : 2 * b ≤ 2 ^ n) :
    ∏ i ∈ Ico (2 * a) (2 * b), T i = ∏ p ∈ Ico a b, T p := by
  rw [prod_Ico_two_mul _ hab]
  refine prod_congr rfl fun p hp ↦ ?_
  rw [mem_Ico] at hp
  have := h (2 * p) (by omega) (by omega)
  rw [two_mul_shiftRight_one, two_mul_xor_one] at this
  exact this.symm

/-- Every level of a heap of depth `n` multiplies to the root. -/
theorem root_eq_prod_level {n : ℕ} {T : ℕ → M} (h : TreeHolds n T) :
    ∀ k, k + 1 ≤ n → T 1 = ∏ i ∈ Ico (2 ^ k) (2 ^ (k + 1)), T i
  | 0, _ => by simp
  | k + 1, hk => by
    rw [root_eq_prod_level h k (by omega), pow_succ' 2 (k + 1), pow_succ' 2 k,
      prod_children h (Nat.one_le_two_pow) (by omega)
        (by rw [← pow_succ', ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hk)]

/-- **The tree lemma.** If the tree identity holds at every position `2 ≤ i < 2^n`, the root
holds the product of the leaves `[2^(n-1), 2^n)`. -/
theorem root_eq_prod_leaves {n : ℕ} (hn : 1 ≤ n) {T : ℕ → M} (h : TreeHolds n T) :
    T 1 = ∏ i ∈ Ico (2 ^ (n - 1)) (2 ^ n), T i := by
  have := root_eq_prod_level h (n - 1) (by omega)
  rwa [Nat.sub_add_cancel hn] at this

end Heap
