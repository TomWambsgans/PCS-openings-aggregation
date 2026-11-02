/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-/
import Circuit.Keccak256Spec

/-!
# Bytes as bits, and the statement bit by bit

`bitOf bytes q` is bit `q % 8` of byte `q / 8`. `pair_bits`: the bits of `H(A ‖ B)` for two 32-byte
strings are `KeccakBits.hash` of the concatenated bits (`keccak256_bits`); `half_testBit`: bit `j` of a
public word (sixteen bytes read big-endian) is bit `j % 8` of byte `15 - j / 8`. `secretOfBits`
decodes the circuit's input bits into a `Secret` (`bitOf_bytesOfBits`, `bitsToNat_testBit`).
-/

set_option maxRecDepth 10000

namespace PcsCircuit

open LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## Numbers and bytes from bits -/

/-- A little-endian list of bits as a number. -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

theorem bitsToNat_testBit : ∀ (bs : List Bool) (t : Nat), (bitsToNat bs).testBit t = bs.getD t false
  | [], t => by simp [bitsToNat]
  | b :: bs, 0 => by cases b <;> simp [bitsToNat, Nat.add_mul_mod_self_left]
  | b :: bs, t + 1 => by
    rw [Nat.testBit_add_one]
    have : ((if b then 1 else 0) + 2 * bitsToNat bs) / 2 = bitsToNat bs := by cases b <;> simp <;> omega
    rw [bitsToNat, this, bitsToNat_testBit bs t]
    simp

theorem bitsToNat_lt : ∀ bs : List Bool, bitsToNat bs < 2 ^ bs.length
  | [] => by simp [bitsToNat]
  | b :: bs => by
    have := bitsToNat_lt bs
    simp only [bitsToNat, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

/-- The byte whose bit `t` is `f t`. -/
def byteOfBits (f : Nat → Bool) : UInt8 := (bitsToNat ((List.range 8).map f)).toUInt8

theorem byteOfBits_testBit (f : Nat → Bool) (t : Nat) (ht : t < 8) :
    (byteOfBits f).toNat.testBit t = f t := by
  have hlt := bitsToNat_lt ((List.range 8).map f)
  simp only [List.length_map, List.length_range] at hlt
  simp only [byteOfBits, Nat.toUInt8]
  rw [UInt8.toNat_ofNat_of_lt' (by simpa [UInt8.size] using hlt), bitsToNat_testBit]
  simp [ht]

/-- The `32` bytes whose bits are `f 0, f 1, …, f 255`, byte order, low bit first. -/
def bytesOfBits (f : Nat → Bool) : List UInt8 :=
  (List.range 32).map fun p => byteOfBits fun t => f (8 * p + t)

theorem bytesOfBits_length (f : Nat → Bool) : (bytesOfBits f).length = 32 := by simp [bytesOfBits]

theorem bitOf_bytesOfBits (f : Nat → Bool) (k : Nat) (hk : k < 256) : bitOf (bytesOfBits f) k = f k := by
  simp only [bitOf, bytesOfBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range
    (show k / 8 < 32 by omega), Option.map_some, Option.getD_some]
  rw [byteOfBits_testBit _ _ (Nat.mod_lt _ (by decide))]
  congr 1; omega

/-- The secret whose input bits (`Secret.inputs`) are `bits`: `x`, then each level's `256` sibling
bits and its direction bit. -/
def secretOfBits (bits : Nat → Bool) : Secret where
  x := bytesOfBits bits
  siblings := (List.range depth).map fun i => bytesOfBits fun j => bits (256 + 257 * i + j)
  directions := bitsToNat ((List.range depth).map fun i => bits (256 + 257 * i + 256))

/-! ## Hashes of pairs -/

theorem bitOf_append (A B : List UInt8) (hA : A.length = 32) (p : Nat) (hp : p < 512) :
    bitOf (A ++ B) p = if p < 256 then bitOf A p else bitOf B (p - 256) := by
  simp only [bitOf, List.getD_eq_getElem?_getD, List.getElem?_append, hA]
  by_cases h : p < 256
  · have : p / 8 < 32 := by omega
    simp [h, this]
  · have : ¬ p / 8 < 32 := by omega
    simp only [h, this, if_false]
    rw [show p / 8 - 32 = (p - 256) / 8 by omega, show p % 8 = (p - 256) % 8 by omega]

theorem hash_congr {m m' : Nat → Bool} (h : ∀ p < 512, m p = m' p) (k : Nat) (hk : k < 256) :
    KeccakBits.hash m k = KeccakBits.hash m' k := by
  have hI : BitsEq (KeccakBits.init m) (KeccakBits.init m') := by
    intro i hi z hz
    simp only [KeccakBits.init]
    split
    · exact h _ (by assumption)
    · rfl
  exact foldl_round_congr _ hI _ (by omega) _ (mod64_lt k)

/-- The bits of `H(A ‖ B)`, for two 32-byte strings. -/
theorem pair_bits (A B : List UInt8) (hA : A.length = 32) (hB : B.length = 32) (m : Nat → Bool)
    (hm : ∀ p < 512, m p = if p < 256 then bitOf A p else bitOf B (p - 256)) (k : Nat) (hk : k < 256) :
    KeccakBits.hash m k = bitOf (H (A ++ B)) k := by
  rw [keccak256_bits _ (by simp [hA, hB]) k hk]
  exact hash_congr (fun p hp => by rw [hm p hp, bitOf_append A B hA p hp]) k hk

theorem digestBytes_length (d : Digest) : (digestBytes d).length = 32 := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => simp [digestBytes, wordBytes]

theorem H_length (data : List UInt8) : (H data).length = 32 := digestBytes_length _

/-! ## The public words -/

/-- A big-endian number of bytes: bit `j` is bit `j % 8` of the byte `j / 8` from the end. -/
theorem foldl_bytes_testBit (g : Nat → Nat) (hg : ∀ k, g k < 256) :
    ∀ (n j : Nat), j < 8 * n →
      ((List.range n).foldl (fun acc k => acc * 256 + g k) 0).testBit j = (g (n - 1 - j / 8)).testBit (j % 8)
  | 0, j, hj => by omega
  | n + 1, j, hj => by
    have ih := foldl_bytes_testBit g hg n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun acc k => acc * 256 + g k) 0 = F at ih ⊢
    rw [show F * 256 + g n = 2 ^ 8 * F + g n by omega,
      Nat.testBit_two_pow_mul_add _ (show g n < 2 ^ 8 from hg n)]
    by_cases h : j < 8
    · rw [if_pos h, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp
    · rw [if_neg h, ih (j - 8) (by omega), show n - 1 - (j - 8) / 8 = n + 1 - 1 - j / 8 by omega,
        show (j - 8) % 8 = j % 8 by omega]

/-- Bit `j < 128` of `half bytes h` (`statement::halves`): bit `j % 8` of byte `16 h + 15 - j / 8`. -/
theorem half_testBit (bytes : List UInt8) (h j : Nat) (hj : j < 128) :
    (half bytes h).testBit j = (bytes.getD (16 * h + (15 - j / 8)) 0).toNat.testBit (j % 8) := by
  unfold half
  rw [foldl_bytes_testBit (fun k => (bytes.getD (16 * h + k) 0).toNat) (fun k => UInt8.toNat_lt _) 16 j
    (by omega)]

end PcsCircuit
