-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Model
import Field.F192
import Field.Sampleable

/-!
# `mulE` is `F192`'s product: F5 on the concrete field

F5's end theorems (`graph_is_verifier`, `graph_words`, `graph_reaches_iff`) hold for any field `F`
with limbs `IsF192`: `XOR` is `+`, `mulE` (`FIELD_MUL`, the Lean transcription of
`crates/primitives`' `software::clmul` and `reduce`) is `*`, one is `(1, 0, 0)`. Here the field is
F0c's `Primitives.F192` (CompPoly's `BF64.Ext3`, leanerVM mumbai's `E`) with its Rust limbs
`(c0, c1, c2)` (`limbsEquiv`), and `isF192_primitives` proves those three facts, so the end
theorems hold of it with no field hypothesis (`graph_is_verifier_F192`, `graph_words_F192`,
`graph_reaches_iff_F192`).

The core is the 64-bit product. A number is read as the polynomial over `GF(2)` of its bits
(`natPoly`; CompPoly's `toPoly` of a bit vector is `natPoly` of its value, `toPoly_eq_natPoly`).
Then:

* `natPoly_clmul`: `clmul` (`software::clmul`, shifted copies of `b` added for the bits of `a`) is
  the product of the polynomials, so it is CompPoly's `carryLessMul` (`clmul_eq_carryLessMul`);
* `natPoly_reduce64`: Rust's shift-fold `reduce` (the high half `hi`, its spill
  `hi >> 63 ^ hi >> 61 ^ hi >> 60` above `x^64` after multiplying by `x^4 + x^3 + x + 1`,
  `v = hi ^ spill`, then `lo ^ v ^ v << 1 ^ v << 3 ^ v << 4`) differs from its input by `v` times
  the modulus `x^64 + x^4 + x^3 + x + 1`, and has degree below 64: it is the remainder, as
  CompPoly's `reduce` (two folds by `0x1B`) is (`reduce64_eq_reduce`);
* so `mul64 a b` is CompPoly's `BF64` product, `reduce (carryLessMul a b)`, for all 64-bit `a`,
  `b` (`mul64_eq`, `ofNat_mul64`); no evaluation over inputs, and no `bv_decide`.

`mulE`'s three limbs are then the nine limb products folded by `y^3 = y + 1`, `y^4 = y^2 + y`,
each reduced, which is F0c's `ofLimbs_mul_ofLimbs` (`isF192_primitives`).

What stays tested: that the Rust computes `mulE` (its Karatsuba and PMULL paths, the opcode of
`crates/evm`), by `crates/quotient/tests/lean_field_vectors.rs` and `Implementation/Diff.lean`.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open Polynomial BinaryField QuotientRpm QuotientSecurity Program Emitted

local notation "SQ" => QuotientSecurity.sq

/-! ## Numbers as polynomials over `GF(2)` -/

/-- **The polynomial of a number**: the coefficient of `X^i` is bit `i`. -/
noncomputable def natPoly (n : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, if n.testBit i then X ^ i else 0

theorem coeff_bitSum (k : ℕ) (f : ℕ → Bool) (j : ℕ) :
    (∑ i ∈ Finset.range k, if f i then (X : (ZMod 2)[X]) ^ i else 0).coeff j =
      if j < k ∧ f j = true then 1 else 0 := by
  rw [finsetSum_coeff]
  by_cases hj : j < k
  · rw [Finset.sum_eq_single j]
    · by_cases hf : f j <;> simp [hj, hf]
    · intro i _ hij
      split_ifs <;> simp [coeff_X_pow, Ne.symm hij]
    · intro h
      exact absurd (Finset.mem_range.mpr hj) h
  · simp only [hj, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hji : j ≠ i := fun e => hj (e ▸ Finset.mem_range.mp hi)
    split_ifs <;> simp [coeff_X_pow, hji]

theorem coeff_natPoly (n j : ℕ) : (natPoly n).coeff j = if n.testBit j then 1 else 0 := by
  rw [natPoly, coeff_bitSum]
  by_cases hb : n.testBit j
  · have hj : j < n := by
      by_contra h
      rw [Nat.testBit_lt_two_pow (lt_of_le_of_lt (not_lt.mp h) Nat.lt_two_pow_self)] at hb
      exact absurd hb Bool.false_ne_true
    simp [hb, hj]
  · simp [hb]

theorem natPoly_injective : Function.Injective natPoly := fun a b h =>
  Nat.eq_of_testBit_eq fun j => by
    have hj := congrArg (coeff · j) h
    simp only [coeff_natPoly] at hj
    cases ha : a.testBit j <;> cases hb : b.testBit j <;> simp [ha, hb] at hj ⊢

@[simp] theorem natPoly_zero : natPoly 0 = 0 := by simp [natPoly]

/-- `XOR` is `+`. -/
theorem natPoly_xor (a b : ℕ) : natPoly (a ^^^ b) = natPoly a + natPoly b := by
  ext j
  simp only [coeff_add, coeff_natPoly, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

/-- `<<< k` is multiplying by `X^k`. -/
theorem natPoly_shiftLeft (a k : ℕ) : natPoly (a <<< k) = X ^ k * natPoly a := by
  ext j
  rw [coeff_X_pow_mul', coeff_natPoly, Nat.testBit_shiftLeft]
  by_cases h : k ≤ j
  · simp [h, coeff_natPoly]
  · simp [h]

/-- A number is its low `k` bits plus `X^k` times the rest. -/
theorem natPoly_split (a k : ℕ) :
    natPoly a = natPoly (a % 2 ^ k) + X ^ k * natPoly (a >>> k) := by
  ext j
  rw [coeff_add, coeff_X_pow_mul', coeff_natPoly, coeff_natPoly, Nat.testBit_mod_two_pow]
  by_cases h : j < k
  · simp [h, show ¬ k ≤ j by omega]
  · rw [coeff_natPoly, Nat.testBit_shiftRight, Nat.add_sub_of_le (by omega : k ≤ j)]
    simp [h, show k ≤ j by omega]

theorem natPoly_mod_succ (a m : ℕ) :
    natPoly (a % 2 ^ (m + 1)) = natPoly (a % 2 ^ m) + if a.testBit m then X ^ m else 0 := by
  ext j
  rw [coeff_add, coeff_natPoly, coeff_natPoly, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hm : a.testBit m
  · simp only [hm, ↓reduceIte, coeff_X_pow]
    rcases lt_trichotomy j m with h | rfl | h
    · simp [h, show j < m + 1 by omega, show j ≠ m by omega]
    · simp [hm]
    · simp [show ¬ j < m + 1 by omega, show ¬ j < m by omega, show j ≠ m by omega]
  · simp only [hm, Bool.false_eq_true, ↓reduceIte, coeff_zero, add_zero]
    rcases lt_trichotomy j m with h | rfl | h
    · simp [h, show j < m + 1 by omega]
    · simp [hm]
    · simp [show ¬ j < m + 1 by omega, show ¬ j < m by omega]

theorem natPoly_coeff_eq_zero {n k j : ℕ} (hn : n < 2 ^ k) (hj : k ≤ j) :
    (natPoly n).coeff j = 0 := by
  rw [coeff_natPoly,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hj))]
  simp

theorem lt_of_coeff_natPoly {n k : ℕ} (h : ∀ j, k ≤ j → (natPoly n).coeff j = 0) : n < 2 ^ k :=
  Nat.lt_pow_two_of_testBit n fun j hj => by
    have hc := h j hj
    rw [coeff_natPoly] at hc
    cases hb : n.testBit j
    · rfl
    · rw [hb] at hc
      simp at hc

theorem degree_natPoly_lt {n k : ℕ} (hn : n < 2 ^ k) : (natPoly n).degree < k :=
  (degree_lt_iff_coeff_zero _ _).mpr fun _ hj => natPoly_coeff_eq_zero hn hj

/-- CompPoly's `toPoly` of a bit vector is the polynomial of its value. -/
theorem toPoly_eq_natPoly {w : ℕ} (v : BitVec w) : toPoly v = natPoly v.toNat := by
  ext j
  rw [toPoly_eq_range, coeff_bitSum, coeff_natPoly]
  by_cases h : j < w
  · simp [h]
  · rw [Nat.testBit_lt_two_pow
      (lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)))]
    simp [h]

/-! ## The carry-less product -/

theorem natPoly_clmul_foldl (a b m acc : ℕ) :
    natPoly ((List.range m).foldl
        (fun acc i => if a.testBit i then acc ^^^ (b <<< i) else acc) acc)
      = natPoly acc + natPoly (a % 2 ^ m) * natPoly b := by
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, natPoly_mod_succ]
    split_ifs with h
    · rw [natPoly_xor, ih, natPoly_shiftLeft]
      ring
    · rw [ih]
      ring

/-- **`clmul` is the product of the polynomials** (of `a`'s low 64 bits and `b`). -/
theorem natPoly_clmul (a b : ℕ) : natPoly (clmul a b) = natPoly (a % 2 ^ 64) * natPoly b := by
  rw [clmul, natPoly_clmul_foldl, natPoly_zero, zero_add]

theorem clmul_lt (a b : ℕ) (hb : b < 2 ^ 64) : clmul a b < 2 ^ 128 := by
  refine lt_of_coeff_natPoly fun j hj => ?_
  rw [natPoly_clmul, coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rcases le_or_gt 64 x.1 with h | h
  · rw [natPoly_coeff_eq_zero (Nat.mod_lt _ (by norm_num)) h, zero_mul]
  · rw [natPoly_coeff_eq_zero hb (by omega), mul_zero]

/-- **`clmul` is CompPoly's `carryLessMul`** on 64-bit inputs. -/
theorem clmul_eq_carryLessMul (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    clmul a b = (carryLessMul (w := 128) (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)).toNat := by
  apply natPoly_injective
  rw [← toPoly_eq_natPoly, toPoly_carryLessMul _ _ (by norm_num), toPoly_eq_natPoly,
    toPoly_eq_natPoly, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, natPoly_clmul, Nat.mod_eq_of_lt ha]

/-! ## The reduction -/

theorem shiftLeft_shiftRight (v j k m : ℕ) (h : j + m = k) : (v <<< j) >>> k = v >>> m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  rw [show k + i - j = m + i by omega]
  simp [show j ≤ k + i by omega]

/-- **Rust's `reduce` is the input less a multiple of the modulus**: `v = hi ^ spill` times
`x^64 + x^4 + x^3 + x + 1`. -/
theorem natPoly_reduce64 (p : ℕ) (hp : p < 2 ^ 128) :
    ∃ v, natPoly p = natPoly (reduce64 p) + BF64.basePoly * natPoly v := by
  have hhi : p >>> 64 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hp)
  have eP := natPoly_split p 64
  unfold reduce64
  dsimp only
  rw [show (B64 : ℕ) = 2 ^ 64 by norm_num, Nat.mod_eq_of_lt hhi]
  set hi := p >>> 64 with hhi_def
  set spill := hi >>> 63 ^^^ hi >>> 61 ^^^ hi >>> 60 with hspill
  set v := hi ^^^ spill with hv
  refine ⟨v, ?_⟩
  have hsp : spill < 2 ^ 4 := by
    have h : ∀ k, 60 ≤ k → hi >>> k < 2 ^ 4 := fun k hk => by
      rw [Nat.shiftRight_eq_div_pow]
      refine Nat.div_lt_of_lt_mul (lt_of_lt_of_le hhi ?_)
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (h 63 (by norm_num)) (h 61 (by norm_num)))
      (h 60 (by norm_num))
  have hv_lt : v < 2 ^ 64 := Nat.xor_lt_two_pow hhi (lt_of_lt_of_le hsp (by norm_num))
  have hvk : ∀ k, 60 ≤ k → v >>> k = hi >>> k := fun k hk => by
    rw [hv, Nat.shiftRight_xor_distrib,
      Nat.shiftRight_eq_zero spill k (lt_of_lt_of_le hsp (Nat.pow_le_pow_right (by norm_num)
        (by omega))), Nat.xor_zero]
  have eV : natPoly v = natPoly hi + natPoly spill := natPoly_xor _ _
  have eS : natPoly spill = natPoly (hi >>> 63) + natPoly (hi >>> 61) + natPoly (hi >>> 60) := by
    rw [hspill, natPoly_xor, natPoly_xor]
  have ej : ∀ j m, j + m = 64 → 60 ≤ m →
      X ^ j * natPoly v = natPoly ((v <<< j) % 2 ^ 64) + X ^ 64 * natPoly (hi >>> m) :=
    fun j m h hm => by
      rw [← natPoly_shiftLeft, ← hvk m hm, ← shiftLeft_shiftRight v j 64 m h]
      exact natPoly_split _ 64
  have e1 := ej 1 63 rfl (by norm_num)
  have e3 := ej 3 61 rfl (by norm_num)
  have e4 := ej 4 60 rfl (by norm_num)
  have hm : ∀ x : ℕ, x % 2 ^ 64 < 2 ^ 64 := fun x => Nat.mod_lt _ (by norm_num)
  have hlt : p % 2 ^ 64 ^^^ v ^^^ (v <<< 1) % 2 ^ 64 ^^^ (v <<< 3) % 2 ^ 64 ^^^
      (v <<< 4) % 2 ^ 64 < 2 ^ 64 :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hm _) hv_lt)
      (hm _)) (hm _)) (hm _)
  rw [Nat.mod_eq_of_lt hlt, natPoly_xor, natPoly_xor, natPoly_xor, natPoly_xor, BF64.basePoly_eq]
  have h2 : (2 : (ZMod 2)[X]) = 0 := ZMod2Poly.two_eq_zero
  linear_combination eP + e1 + e3 + e4 - X ^ 64 * eS - X ^ 64 * eV -
    (1 + X + X ^ 3 + X ^ 4) * natPoly v * h2

/-- **`reduce64` is CompPoly's `reduce`**: both are the remainder modulo
`x^64 + x^4 + x^3 + x + 1`. -/
theorem reduce64_eq_reduce (p : ℕ) (hp : p < 2 ^ 128) :
    reduce64 p = (BF64.reduce (BitVec.ofNat 128 p)).toNat := by
  apply natPoly_injective
  rw [← toPoly_eq_natPoly, BF64.toPoly_reduce, toPoly_eq_natPoly, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp]
  obtain ⟨v, hv⟩ := natPoly_reduce64 p hp
  rw [hv, Polynomial.add_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_right _ _), add_zero]
  refine ((Polynomial.mod_eq_self_iff BF64.basePoly_ne_zero).mpr ?_).symm
  rw [BF64.basePoly_degree]
  exact degree_natPoly_lt (reduce64_lt p)

/-! ## The product in `F64` -/

theorem toQuot_eq (e : Primitives.F64) :
    BF64.toQuot e = AdjoinRoot.mk BF64.basePoly (natPoly e.toBitVec.toNat) := by
  rw [BF64.toQuot, BF64.toPolyBF64, toPoly_eq_natPoly]

theorem toQuot_ofNat {n : ℕ} (hn : n < 2 ^ 64) :
    BF64.toQuot (Primitives.F64.ofNat n) = AdjoinRoot.mk BF64.basePoly (natPoly n) := by
  rw [toQuot_eq]
  show AdjoinRoot.mk _ (natPoly (BitVec.ofNat 64 n).toNat) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem toQuot_reduce64 (p : ℕ) (hp : p < 2 ^ 128) :
    BF64.toQuot (Primitives.F64.ofNat (reduce64 p)) = AdjoinRoot.mk BF64.basePoly (natPoly p) := by
  obtain ⟨v, hv⟩ := natPoly_reduce64 p hp
  rw [toQuot_ofNat (reduce64_lt p), hv, map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]

theorem mk_natPoly_clmul {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    AdjoinRoot.mk BF64.basePoly (natPoly (clmul a b)) =
      BF64.toQuot (Primitives.F64.ofNat a) * BF64.toQuot (Primitives.F64.ofNat b) := by
  rw [natPoly_clmul, Nat.mod_eq_of_lt ha, map_mul, toQuot_ofNat ha, toQuot_ofNat hb]

/-- **The 64-bit product (`mul64`, Rust's `reduce ∘ clmul`) is `F64`'s** (CompPoly's `BF64`). -/
theorem ofNat_mul64 {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Primitives.F64.ofNat (mul64 a b) = Primitives.F64.ofNat a * Primitives.F64.ofNat b :=
  BF64.toQuot_injective (by
    rw [mul64, toQuot_reduce64 _ (clmul_lt a b hb), mk_natPoly_clmul ha hb, BF64.toQuot_mul])

/-- **The same, as CompPoly computes it**: `reduce (carryLessMul a b)`, for all 64-bit `a`, `b`. -/
theorem mul64_eq {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    mul64 a b =
      (BF64.reduce (carryLessMul (w := 128) (BitVec.ofNat 64 a) (BitVec.ofNat 64 b))).toNat := by
  calc mul64 a b = (Primitives.F64.ofNat (mul64 a b)).toBitVec.toNat := by
        show _ = (BitVec.ofNat 64 _).toNat
        rw [BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt (reduce64_lt (clmul a b) : mul64 a b < 2 ^ 64)).symm
    _ = (Primitives.F64.ofNat a * Primitives.F64.ofNat b).toBitVec.toNat := by
        rw [ofNat_mul64 ha hb]
    _ = _ := rfl

/-- A limb's word reads back as the limb. -/
theorem ofNat_toU64 (e : Primitives.F64) : Primitives.F64.ofNat e.toU64.toNat = e := by
  rw [← Primitives.F64.ofU64_eq_ofNat, Primitives.F64.ofU64_toU64]

theorem mk_clmul_toU64 (u w : Primitives.F64) :
    AdjoinRoot.mk BF64.basePoly (natPoly (clmul u.toU64.toNat w.toU64.toNat)) =
      BF64.toQuot (u * w) := by
  rw [mk_natPoly_clmul (UInt64.toNat_lt _) (UInt64.toNat_lt _), ofNat_toU64, ofNat_toU64,
    BF64.toQuot_mul]

/-- An element of `F64` whose class is that of `d < 2^128` has the word `reduce64 d`. -/
theorem toNat_toU64_eq {e : Primitives.F64} {d : ℕ} (hd : d < 2 ^ 128)
    (h : AdjoinRoot.mk BF64.basePoly (natPoly d) = BF64.toQuot e) :
    e.toU64.toNat = reduce64 d := by
  have he : e = Primitives.F64.ofNat (reduce64 d) :=
    BF64.toQuot_injective (by rw [toQuot_reduce64 d hd, h])
  rw [he]
  show (BitVec.ofNat 64 (reduce64 d)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (reduce64_lt _)]

/-! ## `F192` -/

/-- **`F192`'s limbs as words**, `x ↦ (x.c0, x.c1, x.c2)`, back by `F192::new`. (Not mumbai's
`Primitives.limbsEquiv : Vector F64 3 ≃ F192`.) -/
def limbsEquiv : Primitives.F192 ≃ Limbs where
  toFun x := (x.c0, x.c1, x.c2)
  invFun l := Primitives.F192.new l.1 l.2.1 l.2.2
  left_inv x := Primitives.F192.new_c0_c1_c2 x
  right_inv _ := rfl

theorem limbsNat_limbsEquiv (x : Primitives.F192) :
    limbsNat (limbsEquiv x) = ofLimbs x.c0.toNat x.c1.toNat x.c2.toNat := rfl

theorem limb_xor (x y i : ℕ) : limb (x ^^^ y) i = limb x i ^^^ limb y i := by
  unfold limb
  rw [show (B64 : ℕ) = 2 ^ 64 by norm_num, Nat.shiftRight_xor_distrib]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (j < 64) <;> simp

theorem ofLimbs_xor_ofLimbs {x0 x1 x2 y0 y1 y2 : ℕ} (hx0 : x0 < B64) (hx1 : x1 < B64) (hx2 : x2 < B64)
    (hy0 : y0 < B64) (hy1 : y1 < B64) (hy2 : y2 < B64) :
    ofLimbs (x0 ^^^ y0) (x1 ^^^ y1) (x2 ^^^ y2) = ofLimbs x0 x1 x2 ^^^ ofLimbs y0 y1 y2 := by
  have hlt : ofLimbs x0 x1 x2 ^^^ ofLimbs y0 y1 y2 < B192 :=
    Nat.xor_lt_two_pow (n := 192) (ofLimbs_lt hx0 hx1 hx2) (ofLimbs_lt hy0 hy1 hy2)
  obtain ⟨a0, a1, a2⟩ := limb_ofLimbs hx0 hx1 hx2
  obtain ⟨b0, b1, b2⟩ := limb_ofLimbs hy0 hy1 hy2
  rw [← Nat.mod_eq_of_lt hlt, ← ofLimbs_limb, limb_xor, limb_xor, limb_xor, a0, a1, a2, b0, b1,
    b2]

/-- **`Primitives.F192`'s limbs are `F192`'s**: `+` is `XOR`, `*` is `mulE`, one is `(1, 0, 0)`. -/
theorem isF192_primitives : IsF192 limbsEquiv where
  add a b := by
    have h : ∀ i, ((a + b).limb i).toU64 = (a.limb i).toU64 ^^^ (b.limb i).toU64 := fun i => by
      rw [Primitives.F192.limb_add, Primitives.F64.toU64_add]
    rw [limbsNat_limbsEquiv, limbsNat_limbsEquiv, limbsNat_limbsEquiv]
    simp only [Primitives.F192.c0, Primitives.F192.c1, Primitives.F192.c2, h, UInt64.toNat_xor]
    exact ofLimbs_xor_ofLimbs (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
      (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  mul a b := by
    have hab : a * b = Primitives.F192.ofLimbs
        (a.limb 0 * b.limb 0 + a.limb 1 * b.limb 2 + a.limb 2 * b.limb 1)
        (a.limb 0 * b.limb 1 + a.limb 1 * b.limb 0 + a.limb 1 * b.limb 2 + a.limb 2 * b.limb 1 +
          a.limb 2 * b.limb 2)
        (a.limb 0 * b.limb 2 + a.limb 1 * b.limb 1 + a.limb 2 * b.limb 0 +
          a.limb 2 * b.limb 2) := by
      conv_lhs => rw [← Primitives.F192.ofLimbs_limb a, ← Primitives.F192.ofLimbs_limb b]
      exact Primitives.F192.ofLimbs_mul_ofLimbs _ _ _ _ _ _
    obtain ⟨ea0, ea1, ea2⟩ :=
      limb_ofLimbs (UInt64.toNat_lt a.c0) (UInt64.toNat_lt a.c1) (UInt64.toNat_lt a.c2)
    obtain ⟨eb0, eb1, eb2⟩ :=
      limb_ofLimbs (UInt64.toNat_lt b.c0) (UInt64.toNat_lt b.c1) (UInt64.toNat_lt b.c2)
    rw [limbsNat_limbsEquiv, limbsNat_limbsEquiv, limbsNat_limbsEquiv]
    simp only [mulE, ea0, ea1, ea2, eb0, eb1, eb2]
    simp only [Primitives.F192.c0, Primitives.F192.c1, Primitives.F192.c2]
    have hc : ∀ u w : Primitives.F64, clmul u.toU64.toNat w.toU64.toNat < 2 ^ 128 :=
      fun u w => clmul_lt _ _ (UInt64.toNat_lt _)
    congr 1 <;> refine toNat_toU64_eq ?_ ?_ <;>
      first
      | (repeat' apply Nat.xor_lt_two_pow) <;> exact hc _ _
      | (rw [hab]
         simp only [Primitives.F192.limb_ofLimbs_zero, Primitives.F192.limb_ofLimbs_one,
           Primitives.F192.limb_ofLimbs_two, natPoly_xor, map_add, mk_clmul_toU64,
           BF64.toQuot_add] <;>
         ring)
  one := by
    show ((1 : Primitives.F192).c0, (1 : Primitives.F192).c1, (1 : Primitives.F192).c2) = (1, 0, 0)
    rw [Primitives.F192.one_eq_new, Primitives.F192.c0_new, Primitives.F192.c1_new,
      Primitives.F192.c2_new]

/-! ## F5 on `Primitives.F192` -/

variable (σ : Equiv.Perm (Fin (22 + 2) → Bool)) (H : List UInt8 → Vector UInt8 32) (idx : Bytes32)

/-- **F5 on `Primitives.F192`**: `graph_is_verifier` with the field of `crates/primitives`
(CompPoly's `BF64.Ext3`) and its Rust limbs, no field hypothesis left. On the calldata of a model
proof `π`, with tables `cW`, `cQ` whose polynomials are `π`'s messages and a wiring table `cF` of
`σ`: the contract reaches its calls of `PCS_OPEN` with claims that hold of `cW`, `cF`, `cQ` exactly
when no `1 + w_k(t)` vanishes and the model's verifier with the deployed `Wire` accepts `π`. -/
theorem graph_is_verifier_F192
    (π : ChainProof (params isF192_primitives σ) (bounds isF192_primitives σ))
    (cW : (Fin (22 + 1 + 1 + 1) → Bool) → Primitives.F192)
    (cF : (Fin (22 + 2) → Bool) → Primitives.F192)
    (hcF : ∀ x, (tablePoly cF).eval ((basis isF192_primitives).point x) =
      (basis isF192_primitives).point (σ x))
    (cQ : (Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → Primitives.F192)
    (hg : π.g.1 = witnessOfTable cW) (hR : π.R.1 = quotientsOfTable (yConst limbsEquiv) cQ) :
    let I := proofVals isF192_primitives σ H idx π
    ((run H idx (calldataOf limbsEquiv π.stmt (H (encW isF192_primitives σ π.g))
        (H (encQ isF192_primitives σ π.R)) [π.v.1 0, π.v.1 1, π.v.1 2, π.v.1 3, π.v.2])).isSome ∧
      (mle cW (Fin.cons I.ρ (Fin.cons (I.ρ ^ 2) (claimPoint 2 (22 + 1) I.t)))
          = (∑ j, Params.opening I.ρ j * I.a j) / claimScale 2 (22 + 1) I.t ∧
        mle cF (claimPoint 0 (22 + 2) I.t) = I.next / claimScale 0 (22 + 2) I.t ∧
        mle cQ (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) I.t)
            ((params isF192_primitives σ).vCells.eval I.t /
              (params isF192_primitives σ).claimDen I.α I.β I.t I.a I.next)) I.ρ)
              (yConst limbsEquiv / (1 + yConst limbsEquiv)))
              (yConst limbsEquiv ^ 2 / (1 + yConst limbsEquiv ^ 2)))
          = (params isF192_primitives σ).claimValue I.α I.β I.γ I.t I.ρ I.a I.next /
              ((1 + yConst limbsEquiv) * (1 + yConst limbsEquiv ^ 2)) /
            claimScale 0 (22 + 2 + 1 + 1) I.t ∧
        mle cQ (sumPoint (22 + 2) (yConst limbsEquiv)) =
          (params isF192_primitives σ).target ![I.s 0, I.s 1, I.s 2, I.s 3, 1, 0, 0, 0] I.γ /
            ((1 + yConst limbsEquiv) * (1 + yConst limbsEquiv ^ 2)))) ↔
      ((∀ i : Fin (22 + 2 + 1 + 1), 1 + SQ^[(i : ℕ)] I.t ≠ 0) ∧
        (wire isF192_primitives σ idx).verifyWith (m := Id) H π = true) :=
  graph_is_verifier isF192_primitives σ H idx π cW cF hcF cQ hg hR

/-- **F5 on `Primitives.F192`, the words**: when the contract reaches its calls, it hands
`PCS_OPEN` the model's claims (`graph_words`, no field hypothesis left). -/
theorem graph_words_F192 (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)
    (x0 x1 x2 x3 x4 : Primitives.F192) (ws : List Nat)
    (h : run H idx (calldataOf limbsEquiv sb r₁ r₂ [x0, x1, x2, x3, x4]) = some ws) :
    let I := modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4
    ∃ wW wF wQ s, ws = [rootWord r₁.toList, 256 * 1 + 22, 1] ++ wW ++
        [rootWord idx.toList, 256 * 2 + 22, 1] ++ wF ++
        [rootWord r₂.toList, 256 * 3 + 22, 2] ++ wQ ++ sumPointWords ++ [s] ∧
      wW.map (elem limbsEquiv) = modelWitness I.t I.ρ I.a ∧
      wF.map (elem limbsEquiv) = modelWiring I.t I.next ∧
      wQ.map (elem limbsEquiv) = modelQuotient (params isF192_primitives σ) I.α I.β I.γ I.t I.ρ
        I.next (yConst limbsEquiv) I.a ∧
      sumPointWords.map (elem limbsEquiv) = List.ofFn (sumPoint (22 + 2) (yConst limbsEquiv)) ∧
      elem limbsEquiv s =
        (params isF192_primitives σ).target ![I.s 0, I.s 1, I.s 2, I.s 3, 1, 0, 0, 0] I.γ /
          ((1 + yConst limbsEquiv) * (1 + yConst limbsEquiv ^ 2)) :=
  graph_words isF192_primitives σ H idx sb r₁ r₂ x0 x1 x2 x3 x4 ws h

/-- **F5 on `Primitives.F192`, reaching the calls**: exactly when the product of the denominators
is not zero (`graph_reaches_iff`, no field hypothesis left). -/
theorem graph_reaches_iff_F192 (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)
    (x0 x1 x2 x3 x4 : Primitives.F192) :
    (run H idx (calldataOf limbsEquiv sb r₁ r₂ [x0, x1, x2, x3, x4])).isSome ↔
      Formula.check limbsEquiv (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4) ≠ 0 :=
  graph_reaches_iff isF192_primitives H idx sb r₁ r₂ x0 x1 x2 x3 x4

end Implementation
