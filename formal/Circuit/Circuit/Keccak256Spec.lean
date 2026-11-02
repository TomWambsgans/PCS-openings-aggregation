/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
The specification is leanerVM's Keccak-256 (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
commit 6175f1a0, `Statement/Keccak.lean`, MIT OR Apache-2.0), imported.
-/
import Circuit.KeccakSpec

/-!
# Keccak-256 of a 64-byte message, bit by bit

`keccak256_bits`: bit `k` of `H data` (leanerVM's `keccak256`, its digest's bytes) for a 64-byte
`data` is bit `k` of Keccak-f[1600] on `KeccakBits.init` of the message's bits: one block, the
message, `0x01`, zeros, `0x80` (`padBlock`), the digest the first four lanes, little-endian
(`digestBytes`).
-/

set_option linter.deprecated false

namespace PcsCircuit

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash


/-- The state Keccak-256 of a short message (one block) applies Keccak-f[1600] to. -/
def absorbState (data : List UInt8) : KeccakState :=
  Vector.ofFn fun i => if i.val < 17 then Keccak.lane (Vector.replicate 25 0) i ^^^ leLane (padBlock data) i
    else Keccak.lane (Vector.replicate 25 0) i

theorem keccak256_eq (data : List UInt8) (h : data.length = 64) :
    keccak256 data = #v[Keccak.lane (keccakF1600 (absorbState data)) 0, Keccak.lane (keccakF1600 (absorbState data)) 1,
      Keccak.lane (keccakF1600 (absorbState data)) 2, Keccak.lane (keccakF1600 (absorbState data)) 3] := by
  simp only [keccak256, keccak256With, h, rate]
  rfl

theorem testBit_toNat8 (b : UInt8) (t : Nat) : b.toNat.testBit t = b.toBitVec.getLsbD t := by
  rw [← UInt8.toNat_toBitVec, BitVec.testBit_toNat]

theorem wordBytes_bit (w : UInt64) (j t : Nat) (hj : j < 8) (ht : t < 8) :
    ((wordBytes w).getD j 0).toNat.testBit t = w.toBitVec.getLsbD (8 * j + t) := by
  simp [wordBytes, hj]
  have h1 : 8 * j % 64 = 8 * j := Nat.mod_eq_of_lt (by omega)
  rw [h1, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    ← UInt64.toNat_toBitVec, BitVec.testBit_toNat]
  simp [ht]

theorem leLane_bit (bytes : List UInt8) (i z : Nat) (hz : z < 64) :
    (leLane bytes i).toBitVec.getLsbD z = (bytes.getD (8 * i + z / 8) 0).toNat.testBit (z % 8) := by
  rw [testBit_toNat8]
  simp only [leLane, List.range, List.range.loop, List.foldl]
  interval_cases z <;> simp [BitVec.getLsbD_or, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, testBit_toNat8]

theorem padBlock_getD (data : List UInt8) (h : data.length = 64) (q : Nat) :
    (padBlock data).getD q 0 = if q < 64 then data.getD q 0 else if q = 64 then 1 else if q = 135 then 0x80 else 0 := by
  simp only [padBlock, h, rate, padFirst, padLast, List.getD_eq_getElem?_getD, List.getElem?_modify,
    List.getElem?_append, List.getElem?_replicate]
  by_cases hq : q < 64
  · have h1 : ¬ 135 = q := by omega
    have h2 : ¬ 64 = q := by omega
    simp [hq, h1, h2]
  · by_cases hq2 : q - 64 < 136 - 64
    · by_cases h64 : q = 64
      · subst h64; simp
      · by_cases h135 : q = 135
        · subst h135; simp
        · have h1 : ¬ 135 = q := by omega
          have h2 : ¬ 64 = q := by omega
          simp [hq, hq2, h1, h2, h64, h135]
    · have h1 : ¬ 135 = q := by omega
      have h2 : ¬ 64 = q := by omega
      have h64 : ¬ q = 64 := by omega
      have h135 : ¬ q = 135 := by omega
      simp [hq, hq2, h1, h2, h64, h135]

/-- Bit `q` of a byte string: bit `q % 8` of byte `q / 8`. -/
def bitOf (bytes : List UInt8) (q : Nat) : Bool := (bytes.getD (q / 8) 0).toNat.testBit (q % 8)

/-- The state Keccak-256 of a 64-byte message starts Keccak-f[1600] from, as bits: the message's
`512` bits, low bit first, then the padding, bit `512` (`0x01` at byte `64`) and bit `1087` (`0x80` at
byte `135`); the circuit's `keccak256Block` state. -/
def KeccakBits.init (m : Nat → Bool) : Bits := fun i z =>
  if 64 * i + z < 512 then m (64 * i + z) else if 64 * i + z = 64 * 8 then true
  else if 64 * i + z = 64 * 16 + 63 then true else false

theorem absorb_bits (data : List UInt8) (h : data.length = 64) :
    BitsEq (laneBits (absorbState data)) (KeccakBits.init (bitOf data)) := by
  intro i hi z hz
  simp only [laneBits, absorbState, Keccak.lane]
  simp only [Vector.toArray_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, dite_true,
    Option.getD_some, Vector.toArray_replicate, Array.getElem?_replicate, ite_true, UInt64.zero_xor]
  unfold KeccakBits.init bitOf
  by_cases h17 : i < 17
  · rw [if_pos h17, leLane_bit _ _ _ hz, padBlock_getD _ h]
    by_cases h8 : i < 8
    · have e1 : 64 * i + z < 512 := by omega
      have e2 : 8 * i + z / 8 < 64 := by omega
      have e3 : (64 * i + z) / 8 = 8 * i + z / 8 := by omega
      have e4 : (64 * i + z) % 8 = z % 8 := by omega
      rw [if_pos e1, if_pos e2, e3, e4]
    · have e1 : ¬ 64 * i + z < 512 := by omega
      have e2 : ¬ 8 * i + z / 8 < 64 := by omega
      rw [if_neg e1, if_neg e2]
      obtain ⟨t, ht, hzt⟩ : ∃ t, t < 8 ∧ z % 8 = t := ⟨z % 8, Nat.mod_lt _ (by decide), rfl⟩
      rw [hzt]
      by_cases q64 : 8 * i + z / 8 = 64
      · rw [if_pos q64]
        have : 64 * i + z = 64 * 8 ↔ t = 0 := by omega
        have h1135 : ¬ 64 * i + z = 64 * 16 + 63 := by omega
        rw [if_neg h1135]
        by_cases t0 : t = 0
        · rw [if_pos (this.mpr t0), t0]; decide
        · rw [if_neg (fun h => t0 (this.mp h))]
          interval_cases t <;> first | decide | omega
      · rw [if_neg q64]
        have h512 : ¬ 64 * i + z = 64 * 8 := by omega
        rw [if_neg h512]
        by_cases q135 : 8 * i + z / 8 = 135
        · rw [if_pos q135]
          have : 64 * i + z = 64 * 16 + 63 ↔ t = 7 := by omega
          by_cases t7 : t = 7
          · rw [if_pos (this.mpr t7), t7]; decide
          · rw [if_neg (fun h => t7 (this.mp h))]
            interval_cases t <;> first | decide | omega
        · rw [if_neg q135]
          have h1087 : ¬ 64 * i + z = 64 * 16 + 63 := by omega
          rw [if_neg h1087]
          simp
  · rw [if_neg h17]
    have e1 : ¬ 64 * i + z < 512 := by omega
    have e2 : ¬ 64 * i + z = 64 * 8 := by omega
    have e3 : ¬ 64 * i + z = 64 * 16 + 63 := by omega
    rw [if_neg e1, if_neg e2, if_neg e3]
    simp

/-- Keccak-256 of a 64-byte message, as bits: bit `k` of the digest. -/
def KeccakBits.hash (m : Nat → Bool) (k : Nat) : Bool := KeccakBits.keccakF (KeccakBits.init m) (k / 64) (k % 64)

theorem digestBytes_getD (w0 w1 w2 w3 : UInt64) (p : Nat) (hp : p < 32) :
    (digestBytes #v[w0, w1, w2, w3]).getD p 0 = (wordBytes (#[w0, w1, w2, w3].getD (p / 8) 0)).getD (p % 8) 0 := by
  have hl : ∀ w, (wordBytes w).length = 8 := fun w => by simp [wordBytes]
  have e : digestBytes #v[w0, w1, w2, w3] = wordBytes w0 ++ (wordBytes w1 ++ (wordBytes w2 ++ wordBytes w3)) := by
    simp [digestBytes]
  rw [e]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
  interval_cases p <;> simp

/-- **Keccak-256 of a 64-byte message, bit by bit.** -/
theorem keccak256_bits (data : List UInt8) (h : data.length = 64) (k : Nat) (hk : k < 256) :
    bitOf (H data) k = KeccakBits.hash (bitOf data) k := by
  have hS := keccakF_bits (absorbState data) (k / 64) (by omega) (k % 64) (mod64_lt k)
  have hI := foldl_round_congr keccakRC (absorb_bits data h) (k / 64) (by omega) (k % 64) (mod64_lt k)
  simp only [KeccakBits.hash, KeccakBits.keccakF] at hS ⊢
  rw [← hI, ← hS]
  unfold H bitOf
  rw [keccak256_eq data h, digestBytes_getD _ _ _ _ _ (by omega), wordBytes_bit _ _ _ (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide))]
  have e : 8 * (k / 8 % 8) + k % 8 = k % 64 := by omega
  rw [e, show k / 8 / 8 = k / 64 by omega]
  have hj : k / 64 < 4 := by omega
  simp only [laneBits]
  generalize k / 64 = j at hj ⊢
  have g : ∀ (w0 w1 w2 w3 : UInt64) (j : Nat), j < 4 → #[w0, w1, w2, w3].getD j 0 = [w0, w1, w2, w3].getD j 0 :=
    fun _ _ _ _ _ _ => by simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [g _ _ _ _ _ hj]
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ]

end PcsCircuit
