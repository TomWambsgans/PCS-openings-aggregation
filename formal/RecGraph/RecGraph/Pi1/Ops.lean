-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed, in the Rust's operation order, from
-- `crates/leanvm_flock_gas/src/{scalar,multilinear,transcript}.rs` (`Scalar::pow`, `Scalar::sum`, `eq_kernel`,
-- `multilinear_eval`, `eq_eval`, `dot`, `poly_eval`, `squares`, `FsShape::draw`, `sumcheck_round_poly`,
-- `sumcheck_drawn`, `pair_point`, `pair_round_poly`, `sumcheck_pairs_drawn`, adapted there from leanVM
-- (https://github.com/leanEthereum/leanVM), commit 42422001) and `crates/leanvm_univariate/src/domain.rs` (`digits`,
-- `coordinates_at`, `active_vanishing_from_bits`, `vanishing_ratio`).
import RecGraph.Record
import UniStatement.Rec

/-!
# π1-rec3's verifier as a program: the generic helpers

The Rust verifier is generic over its scalar (`Scalar`), and recorded on `record::Sym`. Here, the same functions as
programs over the recorder (`Prog`, scalars node indices), **operation for operation in the Rust's order**, so that
recording them gives the Rust's graph node for node (`RecGraphTest/Pi1Check.lean` checks it). Each `S::zero()`,
`S::one()`, `S::constant(c)` is an operation too (a constant node, hash-consed), and so is every eager step of an
iterator (`successors` computes one item past those taken).
-/

namespace RecGraph.Pi1

open LeanVM.Parameters UniStatement

/-- A scalar: a node's index. -/
abbrev Sym := Nat

/-- One operation. -/
def op (o : Op) : Prog Sym := .op o .pure

/-- `S::constant(x)`. -/
def const (x : E) : Prog Sym := op (.constant x)
/-- `S::zero()`. -/
def zero : Prog Sym := const 0
/-- `S::one()`. -/
def one : Prog Sym := const 1
def add (a b : Sym) : Prog Sym := op (.add a b)
def mul (a b : Sym) : Prog Sym := op (.mul a b)
/-- `Scalar::square` (the default: `self * self`). -/
def square (a : Sym) : Prog Sym := mul a a
/-- `Channel::next_scalar`: 24 bytes. -/
def nextScalar : Prog Sym := op (.input 24)
/-- `Channel::next_integer(bytes)`. -/
def nextInteger (bytes : Nat) : Prog Sym := op (.input bytes)
/-- `Channel::next_root`: two 16-byte halves. -/
def nextRoot : Prog (Sym × Sym) := do
  let a ← op (.input 16)
  let b ← op (.input 16)
  pure (a, b)
/-- `Channel::sample`. -/
def sample : Prog Sym := op (.sample false)
/-- `Channel::sample_narrow`. -/
def sampleNarrow : Prog Sym := op (.sample true)
/-- `Scalar::bits(shift, width)`. -/
def bits (v shift width : Nat) : Prog Sym := op (.bits v shift width)
/-- `Scalar::ring_weight(point, 1 + r, map)`. -/
def ringWeight (point onePlusR map : List Sym) : Prog Sym := op (.ringWeight point onePlusR map)
/-- `Recorder::statement`'s word `k`. -/
def statement (k : Nat) : Prog Sym := op (.statement k)
/-- `Channel::require_zero`. -/
def requireZero (v : Sym) : Prog Unit := .zero v (.pure ())

/-- `Channel::next_scalars(count)`. -/
def nextScalars (count : Nat) : Prog (List Sym) := do
  let mut out : Array Sym := #[]
  for _ in [0:count] do
    out := out.push (← nextScalar)
  return out.toList

/-- `Channel::samples(count)`. -/
def samples (count : Nat) : Prog (List Sym) := do
  let mut out : Array Sym := #[]
  for _ in [0:count] do
    out := out.push (← sample)
  return out.toList

/-- A challenge, narrow or not. -/
def sampleDrawn (narrow : Bool) : Prog Sym := if narrow then sampleNarrow else sample

/-- `Scalar::sum(values)`: from `S::zero()`. -/
def sum (values : List Sym) : Prog Sym := do
  let mut acc ← zero
  for v in values do
    acc ← add acc v
  return acc

/-- **`Scalar::pow(exponent)`** (the default, square and multiply, low bit first: a square past the last bit). -/
def pow (x : Sym) (exponent : Nat) : Prog Sym := do
  let mut base := x
  let mut out ← one
  let mut n := exponent
  for _ in [0:65] do
    if n = 0 then break
    if n % 2 = 1 then
      out ← mul out base
    base ← square base
    n := n / 2
  return out

/-- `eq_kernel(point)`: `out[i + 2^k] = out[i] r_k`, `out[i] += out[i + 2^k]`. -/
def eqKernel (point : List Sym) : Prog (Array Sym) := do
  let z ← zero
  let mut out : Array Sym := Array.replicate (2 ^ point.length) z
  out := out.set! 0 (← one)
  for (r, k) in point.zip (List.range point.length) do
    for i in [0:2 ^ k] do
      let v := out.getD i 0
      let h ← mul v r
      out := out.set! (i + 2 ^ k) h
      out := out.set! i (← add v h)
  return out

/-- `multilinear_eval(mle, point)`: `cur[i] = cur[2i] + r (cur[2i] + cur[2i+1])`. -/
def multilinearEval (mle : List Sym) (point : List Sym) : Prog Sym := do
  let mut cur : Array Sym := mle.toArray
  for r in point do
    for i in [0:cur.size / 2] do
      let a := cur.getD (2 * i) 0
      let b := cur.getD (2 * i + 1) 0
      let s ← add a b
      let p ← mul r s
      cur := cur.set! i (← add a p)
    cur := cur.extract 0 (cur.size / 2)
  return cur.getD 0 0

/-- `eq_eval(left, right) = Π (1 + x + y)`. -/
def eqEval (left right : List Sym) : Prog Sym := do
  let mut result ← one
  for (x, y) in left.zip right do
    let o ← one
    let a ← add o x
    let b ← add a y
    result ← mul result b
  return result

/-- `dot(left, right)`. -/
def dot (left right : List Sym) : Prog Sym := do
  let mut result ← zero
  for (x, y) in left.zip right do
    let p ← mul x y
    result ← add result p
  return result

/-- `poly_eval(coefficients, x)`: Horner from `S::zero()`, the highest coefficient first. -/
def polyEval (coefficients : List Sym) (x : Sym) : Prog Sym := do
  let mut acc ← zero
  for c in coefficients.reverse do
    let p ← mul acc x
    acc ← add p c
  return acc

/-- `squares(first, count)`: `first, first², …`, no square past the last. -/
def squares (first : Sym) (count : Nat) : Prog (List Sym) := do
  if count = 0 then return []
  let mut out : Array Sym := #[first]
  let mut last := first
  for _ in [1:count] do
    last ← square last
    out := out.push last
  return out.toList

/-- **`FsShape::draw(channel, count)`**. -/
def drawRun (fs : FsShape) (count : Nat) : Prog (List Sym) :=
  match fs with
  | .main => samples count
  | .rec1 | .rec2 | .rec3 => if count = 0 then pure [] else do
      let c ← sample
      squares c count

/-! ### Sumchecks (`transcript.rs`) -/

/-- **`sumcheck_round_poly(count, claim, eq_factor)`**. -/
def roundPoly (count : Nat) (claim : Sym) (eqFactor : Option Sym) : Prog (List Sym) := do
  match eqFactor with
  | none =>
    let constant ← nextScalar
    let tail ← nextScalars (count - 2)
    let s ← sum tail
    let c1 ← add claim s
    return [constant, c1] ++ tail
  | some r =>
    let tail ← nextScalars (count - 1)
    let s ← sum tail
    let p ← mul r s
    let c0 ← add claim p
    return [c0] ++ tail

/-- **`sumcheck_drawn(claim, count, equalities, narrow)`**. -/
def sumcheckDrawn (claim : Sym) (count : Nat) (equalities : List (Option Sym)) (narrow : Bool) :
    Prog (List Sym × Sym) := do
  let mut point : Array Sym := #[]
  let mut claim := claim
  for equality in equalities do
    let message ← roundPoly count claim equality
    let challenge ← sampleDrawn narrow
    point := point.push challenge
    claim ← polyEval message challenge
  return (point.toList, claim)

/-- **`pair_point(z)`**: `y_1 = z² + z`, `y_0 = z + β_1 y_1`. -/
def pairPoint (z : Sym) : Prog (List Sym) := do
  let zz ← square z
  let y1 ← add zz z
  let b ← const cantorBeta1
  let p ← mul b y1
  let y0 ← add z p
  return [y0, y1]

/-- **`pair_round_poly(degree, claim)`**: `c_0, c_1, c_2` read, then `c_4 …`; `c_3` from the claim. -/
def pairRoundPoly (degree : Nat) (claim : Sym) : Prog (List Sym) := do
  let top := 4 * degree
  let low ← nextScalars 3
  let high ← nextScalars (top - 3)
  let mut c3 := claim
  for (c, k) in high.zip (List.range high.length) do
    if (k + 4) % 3 = 0 then
      c3 ← add c3 c
  return low ++ [c3] ++ high

/-- **`sumcheck_pairs_drawn(claim, degree, vars, narrow)`**: the point, the challenges, the last claim. -/
def sumcheckPairsDrawn (claim : Sym) (degree vars : Nat) (narrow : Bool) : Prog (List Sym × List Sym × Sym) := do
  let mut point : Array Sym := #[]
  let mut challenges : Array Sym := #[]
  let mut claim := claim
  for _ in [0:vars / 2] do
    let message ← pairRoundPoly degree claim
    let z ← sampleDrawn narrow
    point := point ++ (← pairPoint z).toArray
    challenges := challenges.push z
    claim ← polyEval message z
  if vars % 2 = 1 then
    let (last, end_) ← sumcheckDrawn claim (degree + 1) [none] narrow
    challenges := challenges ++ last.toArray
    point := point ++ last.toArray
    claim := end_
  return (point.toList, challenges.toList, claim)

/-! ### The domain (`domain.rs`) -/

/-- **`digits(t, count)`**: `w_0 = t`, `w_(l+1) = w_l² + w_l`; `successors` computes one past the last taken. -/
def digits (t : Sym) (count : Nat) : Prog (List Sym) := do
  let mut out : Array Sym := #[]
  let mut w := t
  for _ in [0:count] do
    out := out.push w
    let ww ← mul w w
    w ← add ww w
  return out.toList

/-- **`coordinates_at(t, functionals)`**: `t`'s Frobenius powers (one past the last), then each functional's sum
of its nonzero coefficients times them. -/
def coordinatesAt (t : Sym) (functionals : Array (Array K)) : Prog (List Sym) := do
  let r := functionals.size
  let mut frobenius : Array Sym := #[]
  let mut x := t
  for _ in [0:r] do
    frobenius := frobenius.push x
    x ← square x
  let mut out : Array Sym := #[]
  for row in functionals.toList do
    let mut acc ← zero
    for (a, f) in row.toList.zip frobenius.toList do
      if a ≠ 0 then
        let c ← const (ofK a)
        let p ← mul c f
        acc ← add acc p
    out := out.push acc
  return out.toList

/-- **`vanishing_ratio(w, r, m)`**: `Π_(r ≤ j < m) (w_j + 1)`. -/
def vanishingRatio (w : List Sym) (r m : Nat) : Prog Sym := do
  let mut acc ← one
  for j in [r:m] do
    let o ← one
    let s ← add (w.getD j 0) o
    acc ← mul acc s
  return acc

/-- **`active_vanishing_from_bits(w, bits, r)`**. -/
def activeVanishingFromBits (w bits : List Sym) (r : Nat) : Prog Sym := do
  let o ← one
  let s ← add (w.getD r 0) o
  let p ← mul (bits.getD r 0) s
  let mut product ← add o p
  for (bit, b) in (bits.take r).zip (List.range r) do
    let c ← const (cosetOffset r b + 1)
    let s ← add (w.getD b 0) c
    let p ← mul bit s
    let f ← add o p
    product ← mul product f
  return product

end RecGraph.Pi1
