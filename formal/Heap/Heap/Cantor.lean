-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Cantor
import Heap.Tree

/-!
# The heap on a Cantor subspace

SPEC §2: for a Cantor basis `β₀ = 1`, `s(β_{k+1}) = β_k` (`s(x) = x² + x`; this repository's
`QuotientSecurity.CantorBasis`, with `QuotientSecurity.sq` for `s`), position `i` is the point
`ω_i = Σ_{bit k of i} β_k` (`omega`) and `V_r = {ω_i : i < 2^r}` (`V`). The heap's tree identity
is stated on points, `T(s(x)) = T(x)·T(x + 1)` for `x ∈ V_n \ V_1`; it is the tree identity on
positions (`Heap.TreeHolds`) because of four facts of the basis, proved here for every `n`:

* `sq_omega`: `s(ω_i) = ω_{i >> 1}` for `i < 2^n` (and `sq_iterate_omega`: `w_l(ω_i) = ω_{i >> l}`);
* `omega_xor_one`: `ω_i + 1 = ω_{i xor 1}` (more generally `omega_xor`, additivity);
* `omega_one`: `ω_1 = 1`, the root;
* `omega_injOn`: `ω` is injective on `[0, 2^n)` (`omega_ne_zero`: `ω_i ≠ 0` for `0 < i < 2^n`),
  so that `ω_i ∉ V_1` exactly when `i ≥ 2` (`omega_mem_V_one_iff`).

Hence **`root_eq_prod_leaves_omega`**: the tree identity on `V_n \ V_1` gives
`T(1) = Π_{2^(n-1) ≤ i < 2^n} T(ω_i)`. **`tree_of_quotient`** reads the identity off the quotient
form the verifier checks, `w_1(x)·(T(s(x)) + T(x)·T(x + 1)) + w_n(x)·Q(x) = 0` on `V_n`
(`crates/leanvm_univariate/src/verifier.rs`, step 6): `w_n = s^n` vanishes on `V_n`, and
`w_1 = s` vanishes on `V_n` only on `V_1`. And for the leaf blocks: an aligned offset adds
(`omega_add_of_dvd`, so `o_b + ω_k = ω_{pos_b + k}` for the coset `o_b + V_{r_b}` of a block at
an aligned position), and the leaves are the coset `β_{n-1} + V_{n-1}` (`omega_two_pow_add`).

Everything is generic in the field (of characteristic two) and in `n`; nothing is evaluated.
-/

namespace Heap

open Finset
open QuotientSecurity (CantorBasis sq_iterate_sum sq_iterate_zero)

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ} (B : CantorBasis F n)

/-- **The point of position `i`**: `ω_i = Σ_{bit k of i, k < n} β_k`. -/
def omega (i : ℕ) : F := ∑ k ∈ range n, if i.testBit k then B.β k else 0

/-- **The subspace `V_r`**: the points of the positions `i < 2^r`. -/
def V (r : ℕ) : Set F := {x | ∃ i < 2 ^ r, omega B i = x}

/-- `omega` is this repository's `CantorBasis.point` of the bits of `i`. -/
theorem omega_eq_point (i : ℕ) : omega B i = B.point (fun k : Fin n ↦ i.testBit k) :=
  Finset.sum_range fun k ↦ if i.testBit k then B.β k else 0

theorem omega_zero : omega B 0 = 0 := by simp [omega]

/-- **The root**: `ω_1 = β_0 = 1`. -/
theorem omega_one (hn : 1 ≤ n) : omega B 1 = 1 := by
  unfold omega
  rw [Finset.sum_eq_single 0]
  · simp [B.zero]
  · intro k _ hk
    have : Nat.testBit 1 k = false := by
      rcases k with _ | k
      · exact absurd rfl hk
      · exact Nat.testBit_eq_false_of_lt (by
          have := Nat.one_lt_two_pow (n := k + 1) (by omega); omega)
    simp [this]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem ite_xor_eq (a b : Bool) (x : F) :
    (if (a ^^ b) then x else 0) = (if a then x else 0) + (if b then x else 0) := by
  cases a <;> cases b <;> simp [CharTwo.add_self_eq_zero]

/-- **Additivity**: `ω_{i xor j} = ω_i + ω_j`. -/
theorem omega_xor (i j : ℕ) : omega B (i ^^^ j) = omega B i + omega B j := by
  unfold omega
  rw [← Finset.sum_add_distrib]
  exact sum_congr rfl fun k _ ↦ by rw [Nat.testBit_xor, ite_xor_eq]

/-- **The sibling**: `ω_{i xor 1} = ω_i + 1`. -/
theorem omega_xor_one (hn : 1 ≤ n) (i : ℕ) : omega B (i ^^^ 1) = omega B i + 1 := by
  rw [omega_xor, omega_one B hn]

theorem sq_ite (b : Bool) (x : F) :
    QuotientSecurity.sq (if b then x else 0) = if b then QuotientSecurity.sq x else 0 := by
  cases b <;> simp [QuotientSecurity.sq_zero]

theorem sq_one' : QuotientSecurity.sq (1 : F) = 0 := by
  simp only [QuotientSecurity.sq, mul_one, CharTwo.add_self_eq_zero]

/-- **The parent**: `s(ω_i) = ω_{i >> 1}` for `i < 2^n`. -/
theorem sq_omega {i : ℕ} (hi : i < 2 ^ n) :
    QuotientSecurity.sq (omega B i) = omega B (i >>> 1) := by
  rcases n with _ | m
  · have : i = 0 := by simpa using hi
    subst this
    simp [omega, QuotientSecurity.sq_zero]
  · unfold omega
    rw [show QuotientSecurity.sq (∑ k ∈ range (m + 1), if i.testBit k then B.β k else 0) =
        ∑ k ∈ range (m + 1), QuotientSecurity.sq (if i.testBit k then B.β k else 0) from
        sq_iterate_sum _ _ 1,
      Finset.sum_range_succ', Finset.sum_range_succ]
    have h0 : QuotientSecurity.sq (if i.testBit 0 then B.β 0 else 0) = 0 := by
      rw [sq_ite, B.zero, sq_one']
      simp
    have htop : (i >>> 1).testBit m = false := by
      rw [Nat.shiftRight_one, Nat.testBit_div_two]
      exact Nat.testBit_eq_false_of_lt hi
    rw [h0, add_zero, htop]
    simp only [Bool.false_eq_true, ite_false, add_zero]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [sq_ite, B.succ k (by simp at hk; omega), Nat.shiftRight_one, Nat.testBit_div_two]

/-- **The digits**: `w_l(ω_i) = s^l(ω_i) = ω_{i >> l}` for `i < 2^n`. -/
theorem sq_iterate_omega (l : ℕ) :
    ∀ {i : ℕ}, i < 2 ^ n → QuotientSecurity.sq^[l] (omega B i) = omega B (i >>> l) := by
  induction l with
  | zero => intro i _; rfl
  | succ l ih =>
    intro i hi
    rw [Function.iterate_succ_apply, sq_omega B hi,
      ih (lt_of_le_of_lt (by rw [Nat.shiftRight_one]; omega) hi), ← Nat.shiftRight_add,
      Nat.add_comm]

/-- **No nonzero position is the point zero**: `ω_i ≠ 0` for `0 < i < 2^n`. The top digit
`w_l`, `l = ⌊log₂ i⌋`, sends `ω_i` to `ω_1 = 1`. -/
theorem omega_ne_zero {i : ℕ} (h0 : 0 < i) (hi : i < 2 ^ n) : omega B i ≠ 0 := by
  have hn : 1 ≤ n := by
    rcases n with _ | n
    · simp at hi; omega
    · omega
  set l := Nat.log 2 i
  have hl : i >>> l = 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_eq_of_lt_le (by rw [one_mul]; exact Nat.pow_log_le_self 2 h0.ne') ?_
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) i
    rw [pow_succ] at this
    linarith
  intro h
  have := sq_iterate_omega B l hi
  rw [h, sq_iterate_zero, hl, omega_one B hn] at this
  exact zero_ne_one this

/-- **`ω` is injective on `[0, 2^n)`.** -/
theorem omega_injOn {i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n) (h : omega B i = omega B j) :
    i = j := by
  by_contra hne
  have hx : 0 < i ^^^ j := by
    rcases Nat.eq_zero_or_pos (i ^^^ j) with h0 | h0
    · exact absurd (Nat.xor_eq_zero_iff.mp h0) hne
    · exact h0
  apply omega_ne_zero B hx (Nat.xor_lt_two_pow hi hj)
  rw [omega_xor, h, CharTwo.add_self_eq_zero]

/-- `V_1 = {0, 1}`. -/
theorem mem_V_one_iff (hn : 1 ≤ n) (x : F) : x ∈ V B 1 ↔ x = 0 ∨ x = 1 := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl (omega_zero B)
    · exact Or.inr (omega_one B hn)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, omega_zero B⟩
    · exact ⟨1, by norm_num, omega_one B hn⟩

/-- **A position is a child exactly when its point is off `V_1`**: for `i < 2^n`,
`ω_i ∈ V_1 ↔ i < 2`. -/
theorem omega_mem_V_one_iff (hn : 1 ≤ n) {i : ℕ} (hi : i < 2 ^ n) :
    omega B i ∈ V B 1 ↔ i < 2 := by
  constructor
  · rintro ⟨j, hj, hji⟩
    have hj' : j < 2 ^ n := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hn)
    have := omega_injOn B hj' hi hji
    omega
  · intro h
    exact ⟨i, by simpa using h, rfl⟩

/-- `V_r` is `ω` of the positions below `2^r`; for `r ≤ n` they are points of `V_n`. -/
theorem omega_mem_V {r i : ℕ} (hi : i < 2 ^ r) : omega B i ∈ V B r := ⟨i, hi, rfl⟩

/-! ## The tree identity on points -/

variable {M : Type*} [CommMonoid M]

/-- **The tree identity on `V_n \ V_1` is the tree identity on positions.** -/
theorem treeHolds_omega (hn : 1 ≤ n) {T : F → M}
    (h : ∀ x ∈ V B n, x ∉ V B 1 → T (QuotientSecurity.sq x) = T x * T (x + 1)) :
    TreeHolds n (fun i ↦ T (omega B i)) := by
  intro i hi2 hi
  have hx := h (omega B i) (omega_mem_V B hi)
    (fun hm ↦ absurd ((omega_mem_V_one_iff B hn hi).mp hm) (by omega))
  show T (omega B (i >>> 1)) = T (omega B i) * T (omega B (i ^^^ 1))
  rw [← sq_omega B hi, omega_xor_one B hn]
  exact hx

/-- **The tree lemma on a Cantor subspace.** If `T(s(x)) = T(x)·T(x + 1)` for every
`x ∈ V_n \ V_1`, then `T(1) = Π_{2^(n-1) ≤ i < 2^n} T(ω_i)`. -/
theorem root_eq_prod_leaves_omega (hn : 1 ≤ n) {T : F → M}
    (h : ∀ x ∈ V B n, x ∉ V B 1 → T (QuotientSecurity.sq x) = T x * T (x + 1)) :
    T 1 = ∏ i ∈ Ico (2 ^ (n - 1)) (2 ^ n), T (omega B i) := by
  have := root_eq_prod_leaves hn (treeHolds_omega B hn h)
  rwa [omega_one B hn] at this

/-- `s(x) = 0` only at `0` and `1`. -/
theorem sq_eq_zero_iff (x : F) : QuotientSecurity.sq x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have h' : x * (x + 1) = 0 := by rw [← h]; unfold QuotientSecurity.sq; ring
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (CharTwo.add_eq_zero.mp h1)
  · rintro (rfl | rfl)
    · exact QuotientSecurity.sq_zero
    · exact sq_one'

/-- `w_n = s^n` vanishes on `V_n`. -/
theorem sq_iterate_omega_eq_zero {i : ℕ} (hi : i < 2 ^ n) :
    QuotientSecurity.sq^[n] (omega B i) = 0 := by
  rw [sq_iterate_omega B n hi, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hi, omega_zero]

/-- **The tree identity from its quotient form.** The verifier checks
`w_1(t)·(T(s(t)) + T(t)·T(t + 1)) + w_n(t)·Q(t) = 0` (`w_1 = s`, `w_n = s^n`); where that
identity holds on `V_n`, the tree identity holds on `V_n \ V_1`, since `w_n` vanishes on `V_n`
and `w_1` does not on `V_n \ V_1`. -/
theorem tree_of_quotient {T Q : F → F}
    (h : ∀ x ∈ V B n, QuotientSecurity.sq x * (T (QuotientSecurity.sq x) + T x * T (x + 1)) +
      QuotientSecurity.sq^[n] x * Q x = 0) :
    ∀ x ∈ V B n, x ∉ V B 1 → T (QuotientSecurity.sq x) = T x * T (x + 1) := by
  rintro x ⟨i, hi, rfl⟩ hx
  have hn : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    exact hx ⟨i, by simp at hi; omega, rfl⟩
  have h1 := h (omega B i) ⟨i, hi, rfl⟩
  rw [sq_iterate_omega_eq_zero B hi, zero_mul, add_zero] at h1
  have hs : QuotientSecurity.sq (omega B i) ≠ 0 := fun h0 ↦
    hx ((mem_V_one_iff B hn _).mpr ((sq_eq_zero_iff _).mp h0))
  exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hs)

/-! ## Blocks of leaves on cosets -/

/-- Bits of `2^r·c + k`, `k < 2^r`, are those of `2^r·c` xor those of `k`. -/
theorem add_eq_xor_of_dvd {r a k : ℕ} (ha : 2 ^ r ∣ a) (hk : k < 2 ^ r) : a + k = a ^^^ k := by
  obtain ⟨c, rfl⟩ := ha
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add c hk]
  have h0 := Nat.testBit_two_pow_mul_add c (show 0 < 2 ^ r from Nat.two_pow_pos r) j
  rw [add_zero] at h0
  rw [h0]
  by_cases hj : j < r
  · simp [hj]
  · have : k.testBit j = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, this]

/-- **An aligned offset adds**: for `2^r ∣ a` and `k < 2^r`, `ω_{a + k} = ω_a + ω_k`; a block
of `2^r` leaves at an aligned position `a` is the coset `ω_a + V_r`. -/
theorem omega_add_of_dvd {r a k : ℕ} (ha : 2 ^ r ∣ a) (hk : k < 2 ^ r) :
    omega B (a + k) = omega B a + omega B k := by
  rw [add_eq_xor_of_dvd ha hk, omega_xor]

/-- `ω_{2^l} = β_l` for `l < n`. -/
theorem omega_two_pow {l : ℕ} (hl : l < n) : omega B (2 ^ l) = B.β l := by
  unfold omega
  rw [Finset.sum_eq_single l]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_range.mpr hl) h

/-- **The leaves are the coset `β_{n-1} + V_{n-1}`**: `ω_{2^(n-1) + k} = β_{n-1} + ω_k`. -/
theorem omega_two_pow_add (hn : 1 ≤ n) {k : ℕ} (hk : k < 2 ^ (n - 1)) :
    omega B (2 ^ (n - 1) + k) = B.β (n - 1) + omega B k := by
  rw [omega_add_of_dvd B (dvd_refl _) hk, omega_two_pow B (by omega)]

/-! ## Vanishing on executed and padding rows -/

/-- **The vanishing factor of an aligned block** `[a, a + 2^b)`: `w_b(x) + ω_{a >> b}`, the factor
`w[b] + point_e(start >> b)` of the crate's `prefix_vanishing` (`Z_act`, the executed rows
`[0, rows)`) and `suffix_vanishing` (`Z_pad`, the padding rows `[rows, 2^r)`). -/
def blockVanishing (b a : ℕ) (x : F) : F := QuotientSecurity.sq^[b] x + omega B (a >>> b)

/-- **The factor vanishes on its block and nowhere else in `V_n`**: for `2^b ∣ a` and
`k, a < 2^n`, `w_b(ω_k) + ω_{a >> b} = 0` exactly when `a ≤ k < a + 2^b`. -/
theorem blockVanishing_eq_zero_iff {b a k : ℕ} (hal : 2 ^ b ∣ a) (ha : a < 2 ^ n)
    (hk : k < 2 ^ n) : blockVanishing B b a (omega B k) = 0 ↔ a ≤ k ∧ k < a + 2 ^ b := by
  rw [blockVanishing, sq_iterate_omega B b hk, ← omega_xor]
  have hlt : ∀ m, m < 2 ^ n → m >>> b < 2 ^ n := fun m hm ↦
    lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hm
  have hiff : omega B ((k >>> b) ^^^ (a >>> b)) = 0 ↔ k >>> b = a >>> b := by
    constructor
    · intro h0
      by_contra hne
      have hx : 0 < (k >>> b) ^^^ (a >>> b) :=
        Nat.pos_of_ne_zero fun h ↦ hne (Nat.xor_eq_zero_iff.mp h)
      exact omega_ne_zero B hx (Nat.xor_lt_two_pow (hlt k hk) (hlt a ha)) h0
    · intro h
      rw [h, Nat.xor_self, omega_zero]
  rw [hiff, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  obtain ⟨c, rfl⟩ := hal
  have hp : 0 < 2 ^ b := Nat.two_pow_pos b
  rw [Nat.mul_div_cancel_left c hp]
  constructor
  · intro h
    have h1 := Nat.div_mul_le_self k (2 ^ b)
    have h2 := Nat.lt_div_mul_add (a := k) hp
    rw [h] at h1 h2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le (by linarith) (by linarith)

/-- **A product of aligned factors vanishes on the union of its blocks**: if the blocks
`[a, a + 2^b)` of `bl` are aligned and below `2^n`, the product of their factors vanishes at `ω_k`,
`k < 2^n`, exactly when `k` is in one of them. With `bl` covering `[0, rows)` it is `Z_act`, with
`bl` covering `[rows, 2^r)` it is `Z_pad`. -/
theorem prod_blockVanishing_eq_zero_iff (bl : List (ℕ × ℕ))
    (hbl : ∀ p ∈ bl, 2 ^ p.1 ∣ p.2 ∧ p.2 < 2 ^ n) {k : ℕ} (hk : k < 2 ^ n) :
    (bl.map fun p ↦ blockVanishing B p.1 p.2 (omega B k)).prod = 0 ↔
      ∃ p ∈ bl, p.2 ≤ k ∧ k < p.2 + 2 ^ p.1 := by
  rw [List.prod_eq_zero_iff, List.mem_map]
  constructor
  · rintro ⟨p, hp, h0⟩
    exact ⟨p, hp, (blockVanishing_eq_zero_iff B (hbl p hp).1 (hbl p hp).2 hk).mp h0⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, (blockVanishing_eq_zero_iff B (hbl p hp).1 (hbl p hp).2 hk).mpr h⟩

end Heap
