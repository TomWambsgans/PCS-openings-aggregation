-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The field is CompPoly's `BF64.Ext3` (https://github.com/Verified-zkEVM/CompPoly, commit
-- 572f997390aa4fc131ef30b1186fa1dcf292ca10, `CompPoly/Fields/Binary/BF64`, Apache-2.0): its carrier,
-- `Field` instance and the irreducibility of both moduli are CompPoly's. It is the carrier leanerVM's
-- `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a07f0dc33bd3d640de0063d1006143ee91,
-- `Statement/Field.lean`, MIT OR Apache-2.0) calls `LeanVM.Parameters.E`; `eq_sum_limbs` and
-- `ofLimbs_eq` follow mumbai's `lean_vm/LeanVM/Parameters/Field.lean`.
import CompPoly.Fields.Binary.BF64
import Mathlib.Tactic.LinearCombination

/-!
# `F192`, the field of `crates/primitives`

The fields of `crates/primitives/src/field` (vendored from leanVM):

```text
F64  = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)    gf2_64.rs     CompPoly's BF64
F192 = F64[y] / (y^3 + y + 1),  2^192 elements  gf2_64x3.rs   CompPoly's BF64.Ext3
```

An `F64` is a 64-bit word whose bit `i` is the coefficient of `x^i` (Rust's `F64(u64)`); `+` is
`xor` (`F64.toU64_add`) and `*` the carry-less product of the words reduced modulo the pentanomial
(`F64.mul_def`; as polynomials over `GF(2)`, `F64.toPolyBF64_mul`). An `F192` is three `F64` limbs
`c0, c1, c2`, the element `c0 + c1 y + c2 y^2` (Rust's `F192 { c0, c1, c2 }`); `+` is limbwise
`xor` (`new_add_new`) and `*` the nine limb products folded by `y^3 = y + 1`, `y^4 = y^2 + y`
(`ofLimbs_mul_ofLimbs`), the Rust's `software::mul` formula. Both moduli are irreducible
(`BF64.basePoly_irreducible`, Rabin's test with its chains checked by the kernel, no
`native_decide`; `BF64.ext3Poly_irreducible`), so both are fields (`inferInstance : Field F192`),
and `Fintype.card F192 = 2 ^ 192` (`card`).

The Rust's software product as `formal/Implementation` transcribes it (`mulE`: `software::clmul`,
its shift-fold `reduce` folding `x^64 = 0x1B`, the nine limb products folded by `y^3 = y + 1`) is
proved to be this field's `*`: `Implementation/Field192.lean` (`mul64_eq`, `isF192_primitives`).
That the Rust computes these operations (that transcription, its Karatsuba and PMULL paths) is
tested, not proved: `formal/Field/Test.lean` checks, in the kernel, products the Rust computes in
`crates/quotient/tests/lean_field_vectors.rs` (and the Python reference vectors of `gf2_64x3.rs`),
and inverses and a Frobenius by compiled evaluation.

## API

* `F64.ofU64 w` (`F64(w)`), `F64.toU64`, `F64.ofNat n` (`n as u64`), `F64.G` (`F64::G`, `x`);
* `F192.new c0 c1 c2` (`F192::new`), `x.c0`, `x.c1`, `x.c2` (the `u64` limbs), `F192.ofLimbs`,
  `x.limb i`, `F192.ofF64` (`From<F64>`, the `y^0` limb, a ring homomorphism), `F192.Y`
  (`F192::Y`), `F192.G` (`F192::new(2, 0, 0)`, `x`);
* `F192.ext`, `new_c0_c1_c2`, `new_add_new`, `ofLimbs_eq` (`c0 + c1 y + c2 y^2`),
  `ofLimbs_mul_ofLimbs` (the product, limb by limb), `Y_pow_three`;
* the bits: `F64.G_pow` (`x^j` is the word `1 << j` for `j < 64`), `F64.sum_testBit` (a word is
  the sum of its bits' powers of `x`), `F64.bits_eq_false` (the powers `x^j`, `j < 64`, are
  independent over `GF(2)`).

The type is CompPoly's, so its `Field`, `DecidableEq` and `CharP _ 2` instances are; this file adds
`Fintype F64` (hence `Fintype F192`), defined as mumbai's `instFintypeK` is (`Fintype.ofFinite`, so
the two agree by unfolding), and `Field/Sampleable.lean` the samplers, mumbai's. Ground terms
evaluate in the kernel (`decide +kernel`, about a second a product) except inverses (an
exponentiation to `2^192 - 2`); `#eval` and `#guard` run them all.
-/

open CompPoly.Extension Polynomial BinaryField

namespace Primitives

/-- **`F64`**, `GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)` (`crates/primitives/src/field/gf2_64.rs`),
CompPoly's `BF64`: a 64-bit word, bit `i` the coefficient of `x^i`. -/
abbrev F64 : Type := BF64

/-- **`F192`**, `F64[y] / (y^3 + y + 1)` (`crates/primitives/src/field/gf2_64x3.rs`), CompPoly's
`BF64.Ext3`: three limbs, limb `i` the coefficient of `y^i`. -/
abbrev F192 : Type := BF64.Ext3

/-- A proof-only enumeration of `F64`, as mumbai's `LeanVM.Parameters.instFintypeK`. -/
noncomputable instance instFintypeF64 : Fintype F64 := Fintype.ofFinite F64

/-! ## `F64` -/

namespace F64

/-- `F64(w)`: the element whose bit `i` is bit `i` of `w`. -/
def ofU64 (w : UInt64) : F64 := BF64.ofBitVec w.toBitVec

/-- The word of an element (`F64.0`). -/
def toU64 (a : F64) : UInt64 := UInt64.ofBitVec a.toBitVec

/-- `F64(n as u64)`: the word `n mod 2^64`. -/
def ofNat (n : ℕ) : F64 := BF64.ofBitVec (BitVec.ofNat 64 n)

/-- **`F64::G = F64(2)`**: the element `x`. -/
def G : F64 := ofU64 2

@[simp] theorem toU64_ofU64 (w : UInt64) : (ofU64 w).toU64 = w := rfl

@[simp] theorem ofU64_toU64 (a : F64) : ofU64 a.toU64 = a := rfl

theorem toU64_injective : Function.Injective toU64 := fun a b h => by
  rw [← ofU64_toU64 a, h, ofU64_toU64]

theorem ofU64_eq_ofNat (w : UInt64) : ofU64 w = ofNat w.toNat := by
  unfold ofU64 ofNat
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt w.toBitVec.isLt).symm

theorem ofU64_ofNat (n : ℕ) : ofU64 (UInt64.ofNat n) = ofNat n := rfl

/-- `n as u64` keeps the low 64 bits. -/
theorem ofNat_mod (n : ℕ) : ofNat (n % 2 ^ 64) = ofNat n := by
  unfold ofNat
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]

@[simp] theorem ofU64_zero : ofU64 0 = 0 := rfl

@[simp] theorem ofU64_one : ofU64 1 = 1 := rfl

@[simp] theorem ofNat_zero : ofNat 0 = 0 := rfl

/-- `+` is `xor` of the words. -/
theorem ofU64_xor (u v : UInt64) : ofU64 (u ^^^ v) = ofU64 u + ofU64 v := rfl

theorem toU64_add (a b : F64) : (a + b).toU64 = a.toU64 ^^^ b.toU64 := rfl

/-- `*` is the carry-less product of the words, reduced modulo `x^64 + x^4 + x^3 + x + 1`. -/
theorem mul_def (a b : F64) :
    a * b = BF64.ofBitVec (BF64.reduce (carryLessMul (w := 128) a.toBitVec b.toBitVec)) := rfl

/-- The polynomial of an element determines it. -/
theorem toPolyBF64_injective : Function.Injective BF64.toPolyBF64 := fun _ _ h =>
  BF64.toQuot_injective (congrArg (AdjoinRoot.mk BF64.basePoly) h)

/-- **`*` is the product of the polynomials modulo `x^64 + x^4 + x^3 + x + 1`** (CompPoly's
`toPoly_reduce`, `toPoly_carryLessMul`). -/
theorem toPolyBF64_mul (a b : F64) :
    BF64.toPolyBF64 (a * b) = BF64.toPolyBF64 a * BF64.toPolyBF64 b % BF64.basePoly := by
  show toPoly (BF64.reduce (carryLessMul (w := 128) a.toBitVec b.toBitVec)) = _
  rw [BF64.toPoly_reduce, toPoly_carryLessMul _ _ (by omega)]
  rfl

/-- `+` is the sum of the polynomials. -/
theorem toPolyBF64_add (a b : F64) :
    BF64.toPolyBF64 (a + b) = BF64.toPolyBF64 a + BF64.toPolyBF64 b := BF64.toPolyBF64_add a b

/-- The polynomial of an element, as an additive map. -/
noncomputable def toPolyHom : F64 →+ (ZMod 2)[X] where
  toFun := BF64.toPolyBF64
  map_zero' := BF64.toPolyBF64_zero
  map_add' := BF64.toPolyBF64_add

theorem toPolyHom_apply (a : F64) : toPolyHom a = BF64.toPolyBF64 a := rfl

theorem toPolyBF64_ofNat (n : ℕ) :
    BF64.toPolyBF64 (ofNat n) = ∑ i : Fin 64, if n.testBit i then X ^ (i : ℕ) else 0 := by
  show toPoly (BitVec.ofNat 64 n) = _
  unfold toPoly
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat]
  rw [Nat.testBit_mod_two_pow]
  simp [i.isLt]

/-- **`x^j` is the word `1 << j`** for `j < 64`. -/
theorem G_pow (j : ℕ) (hj : j < 64) : G ^ j = ofNat (1 <<< j) := by
  apply BF64.toQuot_injective
  rw [BF64.toQuot_npow]
  have hG : BF64.toPolyBF64 G = X := by
    show toPoly ((1 <<< 1 : ℕ) : BitVec 64) = X
    rw [toPoly_one_shiftLeft 1 (by norm_num), pow_one]
  have hj' : BF64.toPolyBF64 (ofNat (1 <<< j)) = X ^ j := toPoly_one_shiftLeft j hj
  simp only [BF64.toQuot, hG, hj', map_pow]

theorem toPolyBF64_G_pow (j : ℕ) (hj : j < 64) : BF64.toPolyBF64 (G ^ j) = X ^ j := by
  rw [G_pow j hj]
  exact toPoly_one_shiftLeft j hj

/-- The polynomial of a sum of powers `x^i`, `i < 64`. -/
theorem toPolyBF64_sum (b : Fin 64 → Bool) :
    BF64.toPolyBF64 (∑ i : Fin 64, if b i then G ^ (i : ℕ) else 0)
      = ∑ i : Fin 64, if b i then X ^ (i : ℕ) else 0 := by
  rw [← toPolyHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_ite toPolyHom, map_zero, toPolyHom_apply, toPolyBF64_G_pow _ i.isLt]

/-- **A word is the sum of its bits' powers of `x`.** -/
theorem sum_testBit (n : ℕ) :
    (∑ i : Fin 64, if n.testBit i then G ^ (i : ℕ) else 0) = ofNat n := by
  apply toPolyBF64_injective
  rw [toPolyBF64_sum fun i => n.testBit i, toPolyBF64_ofNat]

/-- **The powers `x^i`, `i < 64`, are independent over `GF(2)`.** -/
theorem bits_eq_false (b : Fin 64 → Bool)
    (h : (∑ i : Fin 64, if b i then G ^ (i : ℕ) else 0) = 0) (i : Fin 64) : b i = false := by
  have hp := congrArg (fun p => Polynomial.coeff p i) (congrArg BF64.toPolyBF64 h)
  simp only [toPolyBF64_sum, BF64.toPolyBF64_zero, coeff_zero, finsetSum_coeff] at hp
  rw [Finset.sum_eq_single i (fun k _ hk => by
      have hik : (i : ℕ) ≠ k := fun e => hk (Fin.ext e.symm)
      split_ifs <;> simp [coeff_X_pow, hik])
    (fun hi => absurd (Finset.mem_univ i) hi)] at hp
  cases hb : b i
  · rfl
  · simp [hb] at hp

end F64

/-! ## `F192` -/

namespace F192

/-- The element `c0 + c1 y + c2 y^2`. -/
def ofLimbs (c0 c1 c2 : F64) : F192 := Ext.ofVector #v[c0, c1, c2]

/-- Limb `i`: the coefficient of `y^i`. -/
def limb (x : F192) (i : Fin 3) : F64 := Ext.coeff x i

/-- **`F192::new(c0, c1, c2)`**: the element `c0 + c1 y + c2 y^2`, the limbs as words. -/
def new (c0 c1 c2 : UInt64) : F192 := ofLimbs (F64.ofU64 c0) (F64.ofU64 c1) (F64.ofU64 c2)

/-- The limb `c0`, the coefficient of `y^0`, as a word. -/
def c0 (x : F192) : UInt64 := (x.limb 0).toU64

/-- The limb `c1`, the coefficient of `y`, as a word. -/
def c1 (x : F192) : UInt64 := (x.limb 1).toU64

/-- The limb `c2`, the coefficient of `y^2`, as a word. -/
def c2 (x : F192) : UInt64 := (x.limb 2).toU64

/-- `From<F64> for F192`: the `y^0` limb. It is `algebraMap F64 F192` (`ofF64_eq_algebraMap`). -/
def ofF64 (a : F64) : F192 := Ext.ofBase a

/-- **`F192::Y`**, the root `y` of `y^3 + y + 1`. -/
def Y : F192 := new 0 1 0

/-- **`F192::new(2, 0, 0)`**, the element `x` of the base field (`F64::G`). -/
def G : F192 := new 2 0 0

/-- The limbs as hexadecimal words, `F192::new(0x…, 0x…, 0x…)`, for `#eval`. -/
def hex (x : F192) : String :=
  s!"F192::new(0x{x.c0.toBitVec.toHex}, 0x{x.c1.toBitVec.toHex}, 0x{x.c2.toBitVec.toHex})"

@[simp] theorem limb_ofLimbs (a b c : F64) (i : Fin 3) :
    (ofLimbs a b c).limb i = ![a, b, c] i := by
  fin_cases i <;> rfl

@[simp] theorem limb_ofLimbs_zero (a b c : F64) : (ofLimbs a b c).limb 0 = a := rfl
@[simp] theorem limb_ofLimbs_one (a b c : F64) : (ofLimbs a b c).limb 1 = b := rfl
@[simp] theorem limb_ofLimbs_two (a b c : F64) : (ofLimbs a b c).limb 2 = c := rfl

@[simp] theorem c0_new (a b c : UInt64) : (new a b c).c0 = a := rfl
@[simp] theorem c1_new (a b c : UInt64) : (new a b c).c1 = b := rfl
@[simp] theorem c2_new (a b c : UInt64) : (new a b c).c2 = c := rfl

/-- Elements with the same limbs are equal. -/
@[ext] theorem ext {x z : F192} (h : ∀ i, x.limb i = z.limb i) : x = z := Ext.ext h

theorem ext_iff' {x z : F192} : x = z ↔ ∀ i, x.limb i = z.limb i :=
  ⟨fun h _ => h ▸ rfl, ext⟩

theorem ofLimbs_limb (x : F192) : ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) = x :=
  ext fun i => by fin_cases i <;> rfl

/-- An element is `F192::new` of its words. -/
@[simp] theorem new_c0_c1_c2 (x : F192) : new x.c0 x.c1 x.c2 = x := ofLimbs_limb x

theorem new_injective {a b c a' b' c' : UInt64} (h : new a b c = new a' b' c') :
    a = a' ∧ b = b' ∧ c = c' :=
  ⟨congrArg c0 h, congrArg c1 h, congrArg c2 h⟩

theorem ofLimbs_injective {a b c a' b' c' : F64} (h : ofLimbs a b c = ofLimbs a' b' c') :
    a = a' ∧ b = b' ∧ c = c' :=
  ⟨congrArg (limb · 0) h, congrArg (limb · 1) h, congrArg (limb · 2) h⟩

@[simp] theorem limb_add (x z : F192) (i : Fin 3) : (x + z).limb i = x.limb i + z.limb i :=
  Ext.coeff_add x z i

@[simp] theorem limb_zero (i : Fin 3) : (0 : F192).limb i = 0 :=
  Ext.coeff_zero (P := BF64.ext3Params) i

theorem zero_eq : (0 : F192) = ofLimbs 0 0 0 := ext fun i => by fin_cases i <;> rfl

theorem one_eq : (1 : F192) = ofLimbs 1 0 0 := ext fun i => by fin_cases i <;> rfl

theorem zero_eq_new : (0 : F192) = new 0 0 0 := zero_eq

theorem one_eq_new : (1 : F192) = new 1 0 0 := one_eq

theorem ofLimbs_add_ofLimbs (a b c a' b' c' : F64) :
    ofLimbs a b c + ofLimbs a' b' c' = ofLimbs (a + a') (b + b') (c + c') :=
  ext fun i => by fin_cases i <;> simp

/-- **`+` is limbwise `xor`** (`impl Add for F192`). -/
theorem new_add_new (a b c a' b' c' : UInt64) :
    new a b c + new a' b' c' = new (a ^^^ a') (b ^^^ b') (c ^^^ c') := by
  rw [new, new, ofLimbs_add_ofLimbs, new, F64.ofU64_xor, F64.ofU64_xor, F64.ofU64_xor]

/-! ### The base field in `F192` -/

theorem ofF64_eq_algebraMap (a : F64) : ofF64 a = algebraMap F64 F192 a := rfl

theorem ofF64_eq (a : F64) : ofF64 a = ofLimbs a 0 0 :=
  ext fun i => by fin_cases i <;> rfl

theorem ofF64_ofU64 (w : UInt64) : ofF64 (F64.ofU64 w) = new w 0 0 := ofF64_eq _

@[simp] theorem ofF64_zero : ofF64 0 = 0 := map_zero (algebraMap F64 F192)
@[simp] theorem ofF64_one : ofF64 1 = 1 := map_one (algebraMap F64 F192)
@[simp] theorem ofF64_add (a b : F64) : ofF64 (a + b) = ofF64 a + ofF64 b :=
  map_add (algebraMap F64 F192) a b
@[simp] theorem ofF64_mul (a b : F64) : ofF64 (a * b) = ofF64 a * ofF64 b :=
  map_mul (algebraMap F64 F192) a b
@[simp] theorem ofF64_pow (a : F64) (n : ℕ) : ofF64 (a ^ n) = ofF64 a ^ n :=
  map_pow (algebraMap F64 F192) a n

theorem ofF64_sum {ι : Type*} (s : Finset ι) (f : ι → F64) :
    ofF64 (∑ i ∈ s, f i) = ∑ i ∈ s, ofF64 (f i) :=
  map_sum (algebraMap F64 F192) f s

theorem ofF64_injective : Function.Injective ofF64 := fun a b h => by
  rw [ofF64_eq, ofF64_eq] at h
  exact (ofLimbs_injective h).1

theorem G_eq : G = ofF64 F64.G := (ofF64_eq _).symm

/-! ### `y` -/

theorem Y_eq_gen : Y = BF64.ext3Gen := ext fun i => by fin_cases i <;> rfl

/-- **The defining relation** `y^3 = y + 1`. -/
theorem Y_pow_three : Y ^ 3 = Y + 1 := by rw [Y_eq_gen]; exact BF64.ext3Gen_pow_three

/-- Every element is its limbs in the basis `1, y, y^2`. -/
theorem eq_sum_limbs (x : F192) :
    x = ofF64 (x.limb 0) + ofF64 (x.limb 1) * Y + ofF64 (x.limb 2) * Y ^ 2 := by
  apply Ext.toQuot_injective
  have hx : Ext.toQuot x = ∑ i : Fin 3,
      algebraMap F64 (AdjoinRoot BF64.ext3Params.poly) (x.limb i) *
        Ext.rt BF64.ext3Params ^ (i : ℕ) := rfl
  rw [hx, Fin.sum_univ_three, Y_eq_gen]
  simp [ofF64]

/-- **`ofLimbs c0 c1 c2 = c0 + c1 y + c2 y^2`.** -/
theorem ofLimbs_eq (a b c : F64) : ofLimbs a b c = ofF64 a + ofF64 b * Y + ofF64 c * Y ^ 2 := by
  conv_lhs => rw [eq_sum_limbs (ofLimbs a b c)]
  rfl

theorem new_eq (a b c : UInt64) :
    new a b c = ofF64 (F64.ofU64 a) + ofF64 (F64.ofU64 b) * Y + ofF64 (F64.ofU64 c) * Y ^ 2 :=
  ofLimbs_eq _ _ _

/-- **The product, limb by limb** (`F192Unreduced::reduce` after the `y`-fold): the nine limb
products, `y^3 = y + 1` and `y^4 = y^2 + y` folding the top two. -/
theorem ofLimbs_mul_ofLimbs (a0 a1 a2 b0 b1 b2 : F64) :
    ofLimbs a0 a1 a2 * ofLimbs b0 b1 b2 =
      ofLimbs (a0 * b0 + a1 * b2 + a2 * b1)
        (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) := by
  rw [ofLimbs_eq, ofLimbs_eq, ofLimbs_eq]
  simp only [ofF64_add, ofF64_mul]
  linear_combination
    (ofF64 a1 * ofF64 b2 + ofF64 a2 * ofF64 b1 + ofF64 a2 * ofF64 b2 * Y) * Y_pow_three

/-- `y` times a base-field element is that element in the `y` limb. -/
theorem Y_mul_ofF64 (a : F64) : Y * ofF64 a = ofLimbs 0 a 0 := by
  rw [ofLimbs_eq, ofF64_zero, zero_add, zero_mul, add_zero, mul_comm]

/-! ### The count -/

/-- **`F192` has `2^192` elements.** -/
theorem card : Fintype.card F192 = 2 ^ 192 := BF64.card_ext3

end F192

end Primitives
