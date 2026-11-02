-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniStatement.Basic

/-!
# The count checks of `countBits` (milestone 4, the domain facts)

`UniStatement.countBits` (step 0, iteration 2's F1) reads each table's count as `nextInteger 4`, requires
`intBits count (r + 1) 32 = 0` and `intBits count r 1 * intBits count 0 r = 0`, and returns the bits
`intBits count b 1`, `b ≤ r`. For an honest count `count ≤ 2^r`, `r ≤ 31`:

* `intBits_one`: a bit is the scalar `1` or `0` of `count.testBit b`;
* `intBits_high`, `intBits_range`: the two values `countBits` requires zero are zero;
* `byteFold_wire` (and `byteFold_wire_toArray`, the `Array` the channel's `takeBytes` returns): the big-endian
  byte fold of `nextInteger` returns `count` from the four bytes the prover writes,
  `(List.range 4).map fun k ↦ (count >>> (8 * (3 - k))).toUInt8` (`UniComplete.integerWire count 4`, by `rfl`;
  stated on the list itself so that this file does not import the prover's `Basic`), for `count < 2^32`.
-/

namespace UniComplete.Domain

open LeanVM.Parameters UniStatement

theorem eK_one : eK 1 = 1 := rfl

theorem eK_zero : eK 0 = 0 := rfl

/-- **A bit of the count, as a scalar**: `intBits n b 1` is `1` if bit `b` of `n` is set, else `0`. -/
theorem intBits_one (n b : ℕ) : intBits n b 1 = if n.testBit b then 1 else 0 := by
  unfold intBits
  rw [show min 1 64 = 1 from rfl, pow_one, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ b) with h | h <;> rw [h] <;> rfl

/-- **The count's high bits are zero**: `intBits count (r + 1) 32 = 0` for `count ≤ 2^r`. -/
theorem intBits_high {count r : ℕ} (hc : count ≤ 2 ^ r) : intBits count (r + 1) 32 = 0 := by
  unfold intBits
  rw [Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt (lt_of_le_of_lt hc (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self r))),
    Nat.zero_mod]
  rfl

/-- **A full count has no low bits**: `intBits count r 1 * intBits count 0 r = 0` for `count ≤ 2^r`,
`r ≤ 31`. -/
theorem intBits_range {count r : ℕ} (hc : count ≤ 2 ^ r) (hr : r ≤ 31) :
    intBits count r 1 * intBits count 0 r = 0 := by
  rcases hc.lt_or_eq with hlt | heq
  · rw [intBits_one, Nat.testBit_eq_false_of_lt hlt]
    simp
  · subst heq
    have h0 : intBits (2 ^ r) 0 r = 0 := by
      unfold intBits
      rw [Nat.shiftRight_zero, Nat.min_eq_left (by omega : r ≤ 64), Nat.mod_self]
      rfl
    rw [h0, mul_zero]

theorem toUInt8_toNat_shift (n k : ℕ) : (n >>> k).toUInt8.toNat = n / 2 ^ k % 256 := by
  rw [Nat.shiftRight_eq_div_pow]
  rfl

/-- **`nextInteger 4` reads back the count**: the big-endian fold of the four bytes `count >>> 24, …, count`
(mod `256`) is `count`, `count < 2^32`. -/
theorem byteFold_wire {count : ℕ} (hc : count < 2 ^ 32) :
    ((List.range 4).map fun k ↦ (count >>> (8 * (3 - k))).toUInt8).foldl
      (fun acc x ↦ acc * 256 + x.toNat) 0 = count := by
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, toUInt8_toNat_shift]
  norm_num
  omega

/-- `byteFold_wire` on the `Array` the channel reads (`takeBytes`). -/
theorem byteFold_wire_toArray {count : ℕ} (hc : count < 2 ^ 32) :
    ((List.range 4).map fun k ↦ (count >>> (8 * (3 - k))).toUInt8).toArray.foldl
      (fun acc x ↦ acc * 256 + x.toNat) 0 = count := by
  rw [List.foldl_toArray]
  exact byteFold_wire hc

end UniComplete.Domain

/-- info: 'UniComplete.Domain.intBits_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.intBits_one

/-- info: 'UniComplete.Domain.intBits_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.intBits_high

/-- info: 'UniComplete.Domain.intBits_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.intBits_range

/-- info: 'UniComplete.Domain.byteFold_wire' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.byteFold_wire

/-- info: 'UniComplete.Domain.byteFold_wire_toArray' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.byteFold_wire_toArray
