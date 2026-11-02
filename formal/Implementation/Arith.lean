-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribes crates/primitives/src/field/gf2_64.rs (`software::clmul`, `reduce`) and gf2_64x3.rs (the product's
-- three stages, `frobenius`), vendored there from leanVM (https://github.com/leanEthereum/leanVM, commit c445e3d5,
-- MIT OR Apache-2.0; `reduce` credited there to binius64, Apache-2.0).

/-!
# `FIELD_MUL`, on numbers

The arithmetic of `GF(2^192) = K[y] / (y^3 + y + 1)`, `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, on
the numbers the EVM holds: an element is `c0 + 2^64 c1 + 2^128 c2`, `c_i` the coefficient of `y^i`, bit
`j` of `c_i` its coefficient of `x^j` (`primitives::field::F192`). Addition is `XOR`; the product
(`mulE`, the opcode `FIELD_MUL` of `crates/evm/src/machine.rs`) is the schoolbook of
`gf2_64x3.rs`: nine carry-less products (`clmul`, `software::clmul`), the fold `y^3 = y + 1`,
`y^4 = y^2 + y`, then each coefficient reduced by `x^64 = x^4 + x^3 + x + 1` (`reduce64`,
`gf2_64.rs`'s `reduce`). `frobE` is `F192::frobenius`, `x^(2^64)`.

Natural numbers rather than `UInt64`: the kernel computes on them directly (`decide +kernel`).
-/

namespace Implementation

/-- `2^64`. -/
abbrev B64 : Nat := 18446744073709551616

/-- `2^192`. -/
abbrev B192 : Nat := 6277101735386680763835789423207666416102355444464034512896

/-- Limb `i` of a number: its bits `64 i .. 64 i + 64`. -/
def limb (x i : Nat) : Nat := (x >>> (64 * i)) % B64

/-- The number of three limbs. -/
def ofLimbs (c0 c1 c2 : Nat) : Nat := c0 + B64 * c1 + B64 * B64 * c2

/-- The carry-less product of `a < 2^64` and `b` (`software::clmul`): `b x^i` for each set bit `i`
of `a`, added. -/
def clmul (a b : Nat) : Nat :=
  (List.range 64).foldl (fun acc i => if a.testBit i then acc ^^^ (b <<< i) else acc) 0

/-- A product of degree below `128` reduced modulo `x^64 + x^4 + x^3 + x + 1` (`gf2_64.rs`'s
`reduce`, its shifts truncated to 64 bits as `u64`'s are). -/
def reduce64 (p : Nat) : Nat :=
  let lo := p % B64
  let hi := (p >>> 64) % B64
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  (lo ^^^ v ^^^ ((v <<< 1) % B64) ^^^ ((v <<< 3) % B64) ^^^ ((v <<< 4) % B64)) % B64

/-- The product in `K`. -/
def mul64 (a b : Nat) : Nat := reduce64 (clmul a b)

/-- **The product in `GF(2^192)`** (`FIELD_MUL`): the coefficients of `y^0 .. y^4`, folded by
`y^3 = y + 1` and `y^4 = y^2 + y`, each reduced. Only the low 192 bits of each factor count. -/
def mulE (x y : Nat) : Nat :=
  let a0 := limb x 0
  let a1 := limb x 1
  let a2 := limb x 2
  let b0 := limb y 0
  let b1 := limb y 1
  let b2 := limb y 2
  let d0 := clmul a0 b0
  let d1 := clmul a0 b1 ^^^ clmul a1 b0
  let d2 := clmul a0 b2 ^^^ clmul a1 b1 ^^^ clmul a2 b0
  let d3 := clmul a1 b2 ^^^ clmul a2 b1
  let d4 := clmul a2 b2
  ofLimbs (reduce64 (d0 ^^^ d3)) (reduce64 (d1 ^^^ d3 ^^^ d4)) (reduce64 (d2 ^^^ d4))

/-- **The Frobenius** `x^(2^64)` (`F192::frobenius`): `c0 + c1 y + c2 y^2 ↦ c0 + c2 y + (c1 + c2) y^2`. -/
def frobE (x : Nat) : Nat := ofLimbs (limb x 0) (limb x 2) (limb x 1 ^^^ limb x 2)

-- `y^3 = y + 1`, `y · (1 + y + y^2) = 1 + y^3 + ... `: spot checks against the definition.
example : mulE (ofLimbs 0 1 0) (ofLimbs 0 0 1) = ofLimbs 1 1 0 := by decide +kernel
example : mulE (ofLimbs 0 0 1) (ofLimbs 0 0 1) = ofLimbs 0 1 1 := by decide +kernel
-- `x^63 · x = x^64 = x^4 + x^3 + x + 1` in `K`.
example : mul64 (2 ^ 63) 2 = 0x1b := by decide +kernel

end Implementation
