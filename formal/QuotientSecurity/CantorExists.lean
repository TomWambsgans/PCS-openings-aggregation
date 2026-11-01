-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/CantorExists.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Cantor
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# A Cantor basis exists

In a field of `2^64` elements, `S` applied 64 times is `x ↦ x^(2^64) + x`, which is zero. So the
kernels of the iterates of `S` grow by a factor of exactly two at each step, and an element of
the `n`-th kernel outside the one before gives a Cantor basis of `n` vectors, for every `n` up
to 64. A ring homomorphism carries it to any larger field, such as the cubic extension.
-/

set_option linter.unusedSectionVars false

open Finset

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]

/-- `S` applied `2^j` times is `x ↦ x^(2^(2^j)) + x`. -/
theorem sq_iterate_two_pow (j : ℕ) (x : F) : sq^[2 ^ j] x = x ^ (2 ^ (2 ^ j)) + x := by
  induction j generalizing x with
  | zero =>
    simp only [pow_zero, pow_one, Function.iterate_one, sq]
    ring
  | succ j ih =>
    have h2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
    have e1 : sq^[2 ^ j] x = x ^ 2 ^ 2 ^ j + x := ih x
    have e2 : sq^[2 ^ j] (x ^ 2 ^ 2 ^ j) = (x ^ 2 ^ 2 ^ j) ^ 2 ^ 2 ^ j + x ^ 2 ^ 2 ^ j := ih _
    have hpow : (x ^ 2 ^ 2 ^ j) ^ 2 ^ 2 ^ j = x ^ 2 ^ 2 ^ (j + 1) := by
      rw [← pow_mul, ← pow_add, ← h2]
    calc sq^[2 ^ (j + 1)] x = sq^[2 ^ j] (sq^[2 ^ j] x) := by
          rw [h2, Function.iterate_add_apply]
      _ = sq^[2 ^ j] (x ^ 2 ^ 2 ^ j) + sq^[2 ^ j] x := by rw [e1, sq_iterate_add, e1]
      _ = x ^ 2 ^ 2 ^ (j + 1) + x := by
          rw [e2, e1, hpow, add_assoc, ← add_assoc (x ^ 2 ^ 2 ^ j), CharTwo.add_self_eq_zero,
            zero_add]

/-- An element killed by `S` is zero or one. -/
theorem eq_zero_or_one_of_sq {x : F} (h : sq x = 0) : x = 0 ∨ x = 1 := by
  have h' : x * (x + 1) = 0 := by rw [← h]; unfold sq; ring
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (CharTwo.add_eq_zero.mp h1)

variable [Fintype F] [DecidableEq F]

/-- The kernel of `S` applied `k` times. -/
def sqKernel (F : Type*) [Field F] [Fintype F] [DecidableEq F] (k : ℕ) : Finset F :=
  univ.filter fun x => sq^[k] x = 0

/-- A kernel is at most twice the one before: `S` maps it there, two to one. -/
theorem card_sqKernel_succ_le (k : ℕ) :
    (sqKernel F (k + 1)).card ≤ 2 * (sqKernel F k).card := by
  have himage : (sqKernel F (k + 1)).image sq ⊆ sqKernel F k := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [sqKernel, Finset.mem_filter] at hx ⊢
    have h := hx.2
    rw [Function.iterate_succ_apply] at h
    exact ⟨Finset.mem_univ _, h⟩
  refine le_trans (Finset.card_le_mul_card_image (sqKernel F (k + 1)) 2 fun y _ => ?_)
    (Nat.mul_le_mul_left 2 (Finset.card_le_card himage))
  by_cases hne : ((sqKernel F (k + 1)).filter fun x => sq x = y).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    rw [Finset.mem_filter] at hx₀
    refine le_trans (Finset.card_le_card (t := {x₀, x₀ + 1}) fun x hx => ?_) Finset.card_le_two
    rw [Finset.mem_filter] at hx
    have hsum : sq (x + x₀) = 0 := by
      rw [sq_add, hx.2, hx₀.2, CharTwo.add_self_eq_zero]
    rcases eq_zero_or_one_of_sq hsum with h | h
    · rw [Finset.mem_insert]
      exact Or.inl (CharTwo.add_eq_zero.mp h)
    · rw [Finset.mem_insert, Finset.mem_singleton]
      refine Or.inr ?_
      have : x = x₀ + 1 := by
        have h' : x + x₀ + (x₀ + x₀) = 1 + (x₀ + x₀) := by rw [h]
        rw [CharTwo.add_self_eq_zero, add_zero, add_zero] at h'
        calc x = x + x₀ + x₀ := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
          _ = 1 + x₀ := by rw [h]
          _ = x₀ + 1 := add_comm _ _
      exact this
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

theorem card_sqKernel_le (k : ℕ) : (sqKernel F k).card ≤ 2 ^ k := by
  induction k with
  | zero =>
    have : sqKernel F 0 = {0} := by
      ext x
      rw [sqKernel, Finset.mem_filter, Finset.mem_singleton]
      simp
    rw [this]
    simp
  | succ k ih =>
    refine (card_sqKernel_succ_le k).trans ?_
    rw [pow_succ]
    omega

theorem card_sqKernel_add_le (k d : ℕ) :
    (sqKernel F (k + d)).card ≤ 2 ^ d * (sqKernel F k).card := by
  induction d with
  | zero => simp
  | succ d ih =>
    refine (card_sqKernel_succ_le (k + d)).trans ?_
    rw [pow_succ]
    nlinarith [ih]

/-- **A Cantor basis exists** in a field of `2^64` elements, of every length up to 64. -/
theorem exists_cantorBasis (hF : Fintype.card F = 2 ^ 64) (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 64) :
    Nonempty (CantorBasis F n) := by
  -- The 64th kernel is everything.
  have hall : sqKernel F 64 = univ := by
    ext x
    simp only [sqKernel, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have h := sq_iterate_two_pow 6 x
    have hpow : x ^ 2 ^ 64 = x := by rw [← hF]; exact FiniteField.pow_card x
    have e : (2 : ℕ) ^ 6 = 64 := by norm_num
    rw [e] at h
    rw [h, hpow, CharTwo.add_self_eq_zero]
  -- So the `n`-th kernel has at least `2^n` elements, more than the one before.
  have hbig : 2 ^ n ≤ (sqKernel F n).card := by
    have h := card_sqKernel_add_le (F := F) n (64 - n)
    rw [Nat.add_sub_cancel' hn, hall, Finset.card_univ, hF] at h
    have hsplit : (2 : ℕ) ^ 64 = 2 ^ (64 - n) * 2 ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hn]
    rw [hsplit] at h
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  have hsmall := card_sqKernel_le (F := F) (n - 1)
  have hlt : (sqKernel F (n - 1)).card < (sqKernel F n).card := by
    have : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨b, hb, hb'⟩ : ∃ b ∈ sqKernel F n, b ∉ sqKernel F (n - 1) := by
    by_contra h
    push_neg at h
    exact absurd (Finset.card_le_card fun x hx => h x hx) (not_le.mpr hlt)
  rw [sqKernel, Finset.mem_filter] at hb
  rw [sqKernel, Finset.mem_filter, not_and] at hb'
  have hb1 : sq^[n - 1] b ≠ 0 := hb' (Finset.mem_univ _)
  have hb0 : sq (sq^[n - 1] b) = 0 := by
    rw [(Function.iterate_succ_apply' sq (n - 1) b).symm]
    have e : (n - 1).succ = n := by omega
    rw [e]
    exact hb.2
  refine ⟨{ β := fun k => sq^[n - 1 - k] b, zero := ?_, succ := ?_ }⟩
  · exact (eq_zero_or_one_of_sq hb0).resolve_left hb1
  · intro k hk
    show sq (sq^[n - 1 - (k + 1)] b) = sq^[n - 1 - k] b
    rw [(Function.iterate_succ_apply' sq (n - 1 - (k + 1)) b).symm]
    have e : (n - 1 - (k + 1)).succ = n - 1 - k := by omega
    rw [e]

omit [Fintype F] [DecidableEq F] in
/-- A ring homomorphism carries a Cantor basis to the larger field. -/
def CantorBasis.map {E : Type*} [Field E] {n : ℕ} (B : CantorBasis F n) (f : F →+* E) :
    CantorBasis E n where
  β := fun k => f (B.β k)
  zero := by rw [B.zero, map_one]
  succ := fun k hk => by
    have := congrArg f (B.succ k hk)
    simpa [sq] using this

/-- **A Cantor basis exists in the protocol's field**: a field of `2^192` elements contains one
of `2^64`, whose basis it inherits. -/
theorem exists_cantorBasis_big {E : Type*} [Field E] [Fintype E] [CharP E 2]
    (hE : Fintype.card E = 2 ^ 192) (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 64) :
    Nonempty (CantorBasis E n) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) E := ZMod.algebra E 2
  have : Fintype (GaloisField 2 64) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card 2 64 (by norm_num)
  have hrE : Module.finrank (ZMod 2) E = 192 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [hE, ZMod.card] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hrK : Module.finrank (ZMod 2) (GaloisField 2 64) = 64 :=
    GaloisField.finrank 2 (by norm_num)
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (K := GaloisField 2 64) (L := E) (by rw [hrK, hrE]; norm_num)
  obtain ⟨B⟩ := exists_cantorBasis (F := GaloisField 2 64) hK n hn0 hn
  exact ⟨B.map f.toRingHom⟩

end QuotientSecurity
