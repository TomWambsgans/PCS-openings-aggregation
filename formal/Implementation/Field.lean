-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Arith
import QuotientRpm.Bytes
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finite.Basic

/-!
# A field held as limbs

The model (`QuotientRpm.Wire`) holds an element of its field `F` as three 64-bit limbs
(`Wire.limbs : F ≃ Limbs`); the graph holds it as the number `c0 + 2^64 c1 + 2^128 c2`. `IsF192`
says the limbs are `primitives::field::F192`'s: adding is `XOR` and multiplying is `mulE`
(`FIELD_MUL`), and one is `(1, 0, 0)`. That is, `limbs` is a ring isomorphism from `F` onto
`GF(2^192) = K[y] / (y^3 + y + 1)`, `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, in Rust's
representation. Such an `F` exists exactly because the two polynomials are irreducible; that, and
the computable field, are F0c's (`formal/Field`): here `F` is any field with such an isomorphism,
and `Field192.lean` proves that F0c's `Primitives.F192` is one (`isF192_primitives`).

From it: `elem x`, the element a number stands for (its low 192 bits), with `elem_xor`,
`elem_mulE`, `elem_one`; `F` has `2^192` elements (`card_eq`); and the Frobenius `frobE` is
`x ↦ x^(2^64)` (`elem_frobE`), which is proved here from the two operations: `K`'s elements are
fixed by it (a subfield of `2^64` elements) and `y^(2^64) = y^2` (computed).
-/

set_option linter.unusedSectionVars false

namespace Implementation

open QuotientRpm

/-- Limbs as a number: `c0 + 2^64 c1 + 2^128 c2`. -/
def limbsNat (l : Limbs) : Nat := ofLimbs l.1.toNat l.2.1.toNat l.2.2.toNat

/-- A number's low 192 bits as limbs. -/
def natLimbs (x : Nat) : Limbs := ((limb x 0).toUInt64, (limb x 1).toUInt64, (limb x 2).toUInt64)

theorem limb_lt (x i : Nat) : limb x i < B64 := Nat.mod_lt _ (by decide)

theorem limb_eq (x i : Nat) : limb x i = x / 2 ^ (64 * i) % B64 := by
  rw [limb, Nat.shiftRight_eq_div_pow]

theorem ofLimbs_lt {c0 c1 c2 : Nat} (h0 : c0 < B64) (h1 : c1 < B64) (h2 : c2 < B64) :
    ofLimbs c0 c1 c2 < B192 := by
  unfold ofLimbs B64 B192 at *
  omega

theorem limb_ofLimbs {c0 c1 c2 : Nat} (h0 : c0 < B64) (h1 : c1 < B64) (h2 : c2 < B64) :
    limb (ofLimbs c0 c1 c2) 0 = c0 ∧ limb (ofLimbs c0 c1 c2) 1 = c1 ∧
      limb (ofLimbs c0 c1 c2) 2 = c2 := by
  simp only [limb_eq, ofLimbs]
  norm_num
  unfold B64 at *
  omega

theorem ofLimbs_limb (x : Nat) : ofLimbs (limb x 0) (limb x 1) (limb x 2) = x % B192 := by
  simp only [limb_eq, ofLimbs]
  norm_num
  try unfold B64 B192
  omega

theorem limb_mod (x i : Nat) (hi : i < 3) : limb (x % B192) i = limb x i := by
  simp only [limb_eq]
  unfold B64 B192
  interval_cases i <;> norm_num <;> omega

theorem toNat_toUInt64 {n : Nat} (h : n < B64) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem limbsNat_lt (l : Limbs) : limbsNat l < B192 :=
  ofLimbs_lt l.1.toNat_lt l.2.1.toNat_lt l.2.2.toNat_lt

theorem limbsNat_natLimbs (x : Nat) : limbsNat (natLimbs x) = x % B192 := by
  simp only [limbsNat, natLimbs, toNat_toUInt64 (limb_lt _ _), ofLimbs_limb]

theorem natLimbs_limbsNat (l : Limbs) : natLimbs (limbsNat l) = l := by
  obtain ⟨c0, c1, c2⟩ := l
  obtain ⟨e0, e1, e2⟩ := limb_ofLimbs c0.toNat_lt c1.toNat_lt c2.toNat_lt
  simp only [natLimbs, limbsNat, e0, e1, e2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply UInt64.toNat_inj.mp <;>
    exact toNat_toUInt64 (UInt64.toNat_lt _)

theorem natLimbs_mod (x : Nat) : natLimbs (x % B192) = natLimbs x := by
  simp only [natLimbs, limb_mod x 0 (by decide), limb_mod x 1 (by decide), limb_mod x 2 (by decide)]

theorem limbsNat_injective : Function.Injective limbsNat := fun a b h => by
  rw [← natLimbs_limbsNat a, h, natLimbs_limbsNat]

theorem xor_mod_B192 (x y : Nat) : (x ^^^ y) % B192 = x % B192 ^^^ y % B192 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show B192 = 2 ^ 192 by rfl]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases h : i < 192 <;> simp [h]

theorem mulE_mod_left (x y : Nat) : mulE (x % B192) y = mulE x y := by
  simp only [mulE, limb_mod x 0 (by decide), limb_mod x 1 (by decide), limb_mod x 2 (by decide)]

theorem mulE_mod_right (x y : Nat) : mulE x (y % B192) = mulE x y := by
  simp only [mulE, limb_mod y 0 (by decide), limb_mod y 1 (by decide), limb_mod y 2 (by decide)]

theorem reduce64_lt (p : Nat) : reduce64 p < B64 := Nat.mod_lt _ (by decide)

theorem mulE_lt (x y : Nat) : mulE x y < B192 :=
  ofLimbs_lt (reduce64_lt _) (reduce64_lt _) (reduce64_lt _)

theorem frobE_lt (x : Nat) : frobE x < B192 := by
  refine ofLimbs_lt (limb_lt _ _) (limb_lt _ _) ?_
  exact Nat.xor_lt_two_pow (n := 64) (limb_lt _ _) (limb_lt _ _)

theorem frobE_mod (x : Nat) : frobE (x % B192) = frobE x := by
  simp only [frobE, limb_mod x 0 (by decide), limb_mod x 1 (by decide), limb_mod x 2 (by decide)]

variable {F : Type*} [Field F]

/-- **The limbs are `F192`'s**: `limbs` carries addition to `XOR` and multiplication to `mulE`
(`FIELD_MUL`), and one to `(1, 0, 0)`. -/
structure IsF192 (limbs : F ≃ Limbs) : Prop where
  add : ∀ a b : F, limbsNat (limbs (a + b)) = limbsNat (limbs a) ^^^ limbsNat (limbs b)
  mul : ∀ a b : F, limbsNat (limbs (a * b)) = mulE (limbsNat (limbs a)) (limbsNat (limbs b))
  one : limbs 1 = (1, 0, 0)

variable (limbs : F ≃ Limbs)

/-- The element a number stands for: its low 192 bits, as limbs. -/
def elem (x : Nat) : F := limbs.symm (natLimbs x)

/-- An element as a number. -/
def word (a : F) : Nat := limbsNat (limbs a)

variable {limbs}

theorem elem_word (a : F) : elem limbs (word limbs a) = a := by
  simp [elem, word, natLimbs_limbsNat]

theorem word_elem (x : Nat) : word limbs (elem limbs x) = x % B192 := by
  simp [elem, word, limbsNat_natLimbs]

theorem word_lt (a : F) : word limbs a < B192 := limbsNat_lt _

theorem elem_mod (x : Nat) : elem limbs (x % B192) = elem limbs x := by
  simp [elem, natLimbs_mod]

theorem word_injective : Function.Injective (word limbs) := fun a b h => by
  rw [← elem_word (limbs := limbs) a, h, elem_word]

theorem elem_eq_of_word {x : Nat} {a : F} (h : word limbs a = x % B192) : elem limbs x = a := by
  rw [← elem_mod, ← h, elem_word]

theorem elem_xor (hF : IsF192 limbs) (x y : Nat) :
    elem limbs (x ^^^ y) = elem limbs x + elem limbs y := by
  apply elem_eq_of_word
  rw [word, hF.add, ← word, ← word, word_elem, word_elem, xor_mod_B192]

theorem elem_mulE (hF : IsF192 limbs) (x y : Nat) :
    elem limbs (mulE x y) = elem limbs x * elem limbs y := by
  apply elem_eq_of_word
  rw [word, hF.mul, ← word, ← word, word_elem, word_elem, mulE_mod_left, mulE_mod_right,
    Nat.mod_eq_of_lt (mulE_lt _ _)]

theorem elem_one (hF : IsF192 limbs) : elem limbs 1 = (1 : F) := by
  apply elem_eq_of_word
  rw [word, hF.one]
  decide

theorem elem_zero (hF : IsF192 limbs) : elem limbs 0 = (0 : F) := by
  have h := elem_xor hF 0 0
  rw [Nat.xor_self] at h
  exact left_eq_add.mp h

/-- `F` has as many elements as `F192`. -/
theorem card_uint64 : Fintype.card UInt64 = 2 ^ 64 := by
  rw [Fintype.card_congr (⟨UInt64.toFin, UInt64.ofFin, fun w => by simp, fun i => by simp⟩ :
    UInt64 ≃ Fin (2 ^ 64)), Fintype.card_fin]

theorem card_eq [Fintype F] (limbs : F ≃ Limbs) : Fintype.card F = 2 ^ 192 := by
  rw [Fintype.card_congr limbs]
  simp only [Limbs, Fintype.card_prod, card_uint64]
  norm_num

end Implementation
