-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Field.F192

/-!
# `F192` against the Rust

The vectors of `crates/quotient/tests/lean_field_vectors.rs`, which asserts them of
`primitives::field::F192`: the products are checked by the kernel (`decide +kernel` evaluates
CompPoly's carry-less products and reductions), the inverses and the Frobenius (exponentiations
to `2^192 - 2` and `2^64`) by compiled evaluation (`#guard`).
-/

namespace Primitives.F192

/-! ## Products, in the kernel -/

/-- All-ones times all-ones: every reduction spill. -/
theorem mul_ones_ones :
    new 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff *
        new 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff =
      new 0x5555555555555513 0x5555555555555513 0 := by decide +kernel

theorem mul_tops_tops :
    new 0x8000000000000000 0x8000000000000000 0x8000000000000000 *
        new 0x8000000000000000 0x8000000000000000 0x8000000000000000 =
      new 0xc00000000000005a 0xc00000000000005a 0 := by decide +kernel

theorem mul_ones_tops :
    new 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff *
        new 0x8000000000000000 0x8000000000000000 0x8000000000000000 = new 0x65 0x65 0 := by
  decide +kernel

theorem mul_a_ones :
    new 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923 *
        new 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff =
      new 0xf732f696ccf14373 0x4e7f3bdaf2bc8b22 0xe537c4a915aa5ba0 := by decide +kernel

/-- `y * y = y^2`. -/
theorem mul_Y_Y : Y * Y = new 0 0 1 := by decide +kernel

/-- `y^2 * y = y + 1`. -/
theorem mul_Y2_Y : new 0 0 1 * Y = new 1 1 0 := by decide +kernel

/-- `x^63 * x = x^64 = x^4 + x^3 + x + 1 = 0x1B`. -/
theorem mul_x63_x : new 0x8000000000000000 0 0 * G = new 0x1b 0 0 := by decide +kernel

theorem mul_x63_x63 :
    new 0x8000000000000000 0 0 * new 0x8000000000000000 0 0 = new 0xc00000000000005a 0 0 := by
  decide +kernel

/-- The Rust's `x^{-1}`. -/
theorem mul_xinv_x : new 0x800000000000000d 0 0 * G = 1 := by decide +kernel

/-! The Python reference vectors of `gf2_64x3.rs`'s tests. -/

theorem mul_python_0 :
    new 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923 *
        new 0x6dbca290a9eab706 0x4c10a4fe30cffdda 0xf26fff4cc4fd394d =
      new 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabe := by decide +kernel

theorem mul_python_1 :
    new 0x6814a2bc786a6d2d 0xa26b351e6c8042c5 0x54760e7fbc051c6c *
        new 0xd4c08880a5a4666d 0x29610ae0eed8f1e7 0xc34bd8e2fe5213e5 =
      new 0x2ad322ebf2f9043b 0x8ac800aa67154c80 0x6d0f76651d3c4d0c := by decide +kernel

theorem mul_python_2 :
    new 0x6c50afb6e9fb123d 0x6f28d015a2aa0b9d 0x4e385994ebac94af *
        new 0x194f9545adba52ce 0xc675ce05588f882f 0x57de8c051d4b7ef2 =
      new 0xea6b9f9d23d4a1ff 0xd82aa6058c431457 0x5fd4d8fda2f1e74a := by decide +kernel

theorem mul_python_3 :
    new 0xd998efd82733e933 0x6df216c33f8f3201 0x11dc6f3fcb57d5d8 *
        new 0x8860a84722025e05 0x33176469aa6ef630 0x607507ebc5b864d7 =
      new 0xfa3a0d66cdfbc1b3 0xbd47bd3343aad307 0xdaf50186477f6a77 := by decide +kernel

/-! ## Inverses and the Frobenius, compiled -/

#guard (new 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923)⁻¹ =
  new 0x54585269244a53bf 0xe61abf3f20ceabe4 0x8eb77d6b827e0877
#guard G⁻¹ = new 0x800000000000000d 0 0
#guard Y⁻¹ = new 1 0 1
#guard (0 : F192)⁻¹ = 0
-- `F192::frobenius`, `a^(2^64)`.
#guard new 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923 ^ (2 ^ 64) =
  new 0x950e87d7f5606615 0x1f00bca0042db923 0x33619bfc9a46d5db
#guard (new 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923 *
  new 0x6dbca290a9eab706 0x4c10a4fe30cffdda 0xf26fff4cc4fd394d).hex =
  "F192::new(0x888a0fc35abaf5f6, 0x68a84cbc132b0649, 0x9fdeaf613003cabe)"

/-- info: 'Primitives.F192.mul_python_0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_python_0

end Primitives.F192
