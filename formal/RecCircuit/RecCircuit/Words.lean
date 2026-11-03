-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Pack
import RecCircuit.Sponge
import Circuit.Bytes

/-!
# Words of bits

A packing whose bits are bit `e` of a number `M` is `M`'s word (`sum_bits_word`, through `F64.sum_testBit`); the bits
of big- and little-endian byte strings (`beNat_testBit`, `leNat_testBit`); the bits of a byte the decoders make from
free bits (`foldl_pow_testBit`).
-/

namespace RecCircuit

open Primitives PcsCircuit

theorem ofBool_mul_pow (b : Bool) (e : ℕ) : ofBool b * F64.G ^ e = if b then F64.G ^ e else 0 := by
  cases b <;> simp [ofBool]

/-- **A packing of the bits of `M` is `M`'s word.** -/
theorem sum_bits_word (B : ℕ → K) (M : ℕ) (hB : ∀ e < 64, B e = ofBool (M.testBit e)) :
    ∑ e ∈ Finset.range 64, B e * F64.G ^ e = F64.ofNat M := by
  rw [← F64.sum_testBit M, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hB i i.isLt, ofBool_mul_pow]

/-! ## Byte strings -/

/-- A little-endian number of bytes. -/
def leNat (bytes : List UInt8) : ℕ := bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

theorem beNat_append (bs : List UInt8) (b : UInt8) : beNat (bs ++ [b]) = beNat bs * 256 + b.toNat := by
  simp [beNat, List.foldl_append]

theorem testBit_byte (b : UInt8) (t : ℕ) (ht : 8 ≤ t) : b.toNat.testBit t = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by norm_num) ht))

theorem beNat_testBit : ∀ (bs : List UInt8) (e : ℕ),
    (beNat bs).testBit e = (decide (e < 8 * bs.length) && (bs.getD (bs.length - 1 - e / 8) 0).toNat.testBit (e % 8)) := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil => intro e; simp [beNat]
  | append_singleton bs b ih =>
    intro e
    rw [beNat_append, show beNat bs * 256 + b.toNat = 2 ^ 8 * beNat bs + b.toNat by ring,
      Nat.testBit_two_pow_mul_add _ (show b.toNat < 2 ^ 8 from b.toNat_lt)]
    simp only [List.length_append, List.length_singleton]
    by_cases h : e < 8
    · rw [ite_cond_eq_true _ _ (eq_true h)]
      have : bs.length + 1 - 1 - e / 8 = bs.length := by omega
      rw [decide_eq_true (show e < 8 * (bs.length + 1) by omega), Bool.true_and, this, Nat.mod_eq_of_lt h]
      simp [List.getD_eq_getElem?_getD]
    · rw [ite_cond_eq_false _ _ (eq_false h), ih (e - 8)]
      by_cases h2 : e - 8 < 8 * bs.length
      · have hi : bs.length + 1 - 1 - e / 8 < bs.length := by omega
        have e1 : bs.length + 1 - 1 - e / 8 = bs.length - 1 - (e - 8) / 8 := by omega
        rw [decide_eq_true h2, decide_eq_true (show e < 8 * (bs.length + 1) by omega), Bool.true_and, Bool.true_and,
          List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, e1,
          show (e - 8) % 8 = e % 8 by omega]
      · rw [decide_eq_false h2, decide_eq_false (show ¬ e < 8 * (bs.length + 1) by omega)]; rfl

theorem leNat_testBit : ∀ (bs : List UInt8) (e : ℕ),
    (leNat bs).testBit e = (decide (e < 8 * bs.length) && (bs.getD (e / 8) 0).toNat.testBit (e % 8))
  | [], e => by simp [leNat]
  | b :: bs, e => by
    have ih := leNat_testBit bs (e - 8)
    show (b.toNat + 256 * leNat bs).testBit e = _
    rw [show b.toNat + 256 * leNat bs = 2 ^ 8 * leNat bs + b.toNat by ring,
      Nat.testBit_two_pow_mul_add _ (show b.toNat < 2 ^ 8 from b.toNat_lt)]
    simp only [List.length_cons]
    by_cases h : e < 8
    · rw [ite_cond_eq_true _ _ (eq_true h)]
      simp [h, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, show e < 8 * (bs.length + 1) by omega]
    · rw [ite_cond_eq_false _ _ (eq_false h), ih]
      have e1 : e / 8 = (e - 8) / 8 + 1 := by omega
      rw [e1, show (e - 8) % 8 = e % 8 by omega]
      by_cases h2 : e - 8 < 8 * bs.length
      · simp [h2, show e < 8 * (bs.length + 1) by omega]
      · simp [h2, show ¬ e < 8 * (bs.length + 1) by omega]

theorem slice_length_le (bytes : List UInt8) (a n : ℕ) : (slice bytes a n).length ≤ n := by
  simp [slice]

theorem slice_length (bytes : List UInt8) (a n : ℕ) (h : a + n ≤ bytes.length) : (slice bytes a n).length = n := by
  simp [slice]; omega

theorem slice_getD (bytes : List UInt8) (a n i : ℕ) (hi : i < n) : (slice bytes a n).getD i 0 = bytes.getD (a + i) 0 := by
  simp [slice, List.getD_eq_getElem?_getD, List.getElem?_take, hi, List.getElem?_drop]

theorem slice_slice (bytes : List UInt8) (a n b m : ℕ) (h : b + m ≤ n) :
    slice (slice bytes a n) b m = slice bytes (a + b) m := by
  simp only [slice, List.drop_take, List.take_take, List.drop_drop]
  rw [min_eq_left (by omega)]

/-! ## The bits of a decoded byte -/

theorem foldl_pow_testBit (b : ℕ → ℕ) (hb : ∀ j, b j ≤ 1) :
    ∀ n, ((List.range n).foldl (fun acc j => acc + 2 ^ j * b j) 0) < 2 ^ n ∧
      ∀ t, ((List.range n).foldl (fun acc j => acc + 2 ^ j * b j) 0).testBit t = decide (t < n ∧ b t = 1)
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hlt, ht⟩ := foldl_pow_testBit b hb n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun acc j => acc + 2 ^ j * b j) 0 = S at hlt ht ⊢
    have hbn := hb n
    refine ⟨?_, ?_⟩
    · rw [pow_succ]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbn with h | h
      · rw [h, mul_zero, add_zero]; exact lt_of_lt_of_le hlt (Nat.le_mul_of_pos_right _ (by norm_num))
      · rw [h, mul_one, mul_two]; exact Nat.add_lt_add_right hlt _
    · intro t
      rw [show S + 2 ^ n * b n = 2 ^ n * b n + S by ring, Nat.testBit_two_pow_mul_add _ hlt]
      by_cases h : t < n
      · rw [ite_cond_eq_true _ _ (eq_true h), ht t]; simp [h, show t < n + 1 by omega]
      · rw [ite_cond_eq_false _ _ (eq_false h)]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbn with h1 | h1
        · rw [h1]
          by_cases h2 : t = n
          · subst h2; simp [h1]
          · simp [Nat.zero_testBit]; omega
        · rw [h1]
          by_cases h2 : t = n
          · subst h2; simp [h1]
          · have hf : (1 : ℕ).testBit (t - n) = false :=
              Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))
            rw [hf]; simp; omega

theorem bitOfWord_le (x : K) : Compiled.bitOfWord x ≤ 1 := by unfold Compiled.bitOfWord; split <;> omega

/-- A bit word is the bit `bitOfWord` reads. -/
theorem ofBool_bitOfWord {x : K} (h : x = 0 ∨ x = 1) : x = ofBool (decide (Compiled.bitOfWord x = 1)) := by
  rcases h with rfl | rfl
  · have : (0 : K) ≠ 1 := zero_ne_one
    simp [Compiled.bitOfWord, ofBool, this]
  · simp [Compiled.bitOfWord, ofBool]

/-- **A decoded byte's bits are its free bits.** -/
theorem decoded_byte_testBit (v : ℕ → K) (t : ℕ) (ht : t < 8) :
    ((List.range 8).foldl (fun acc j => acc + 2 ^ j * Compiled.bitOfWord (v j)) 0).toUInt8.toNat.testBit t =
      decide (Compiled.bitOfWord (v t) = 1) := by
  obtain ⟨hlt, htb⟩ := foldl_pow_testBit (fun j => Compiled.bitOfWord (v j)) (fun j => bitOfWord_le _) 8
  rw [Nat.toUInt8, UInt8.toNat_ofNat_of_lt' (by simpa [UInt8.size] using hlt), htb]
  simp [ht]

end RecCircuit
