-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/leanvm_flock_gas/src/{field,multilinear,scalar}.rs` (adapted there from leanVM
-- (https://github.com/leanEthereum/leanVM), commit 42422001, `crates/verifier/src/{field,multilinear}.rs`).
-- The fields are leanerVM's (`Statement/Field.lean`, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0).
module

public import Statement.Field

/-!
# Field helpers

The verifier computes on `E = GF(2^192)` (leanerVM's `LeanVM.Parameters.E`, CompPoly's `BF64.Ext3`,
compiled on machine words by `Statement/Fast`). This file holds the few helpers of
`leanvm_flock_gas` the verifier calls, each on `E` (the Rust is generic over a `Scalar`, which on the
native verifier is `E`; constants are elements of `E`):

* `eNew c0 c1 c2` is the Rust's `E::new`, limb `i` the coefficient of `y^i`;
* `epow` is `E::pow` (square and multiply, low bit first) and `sqn x k` is `k` squarings;
* `eqKernel`, `eqEval`, `multilinearEval`, `polyEval`, `dot` (`multilinear.rs`);
* `log2Ceil` (`multilinear.rs`) and `trailingZeros` (`u64::trailing_zeros`, `64` at zero).

A `List` stands for a `Vec`; an out-of-range index reads `0` (`getD`), where the Rust would panic.
The verifier reads in range everywhere (the test exercises every path).
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters

/-- `E::new(c0, c1, c2)`: the element `c0 + c1·y + c2·y²` of three 64-bit words. -/
def eNew (c0 c1 c2 : UInt64) : E := E.ofLimbs (K.ofLane c0) (K.ofLane c1) (K.ofLane c2)

/-- `E::new(c0, 0, 0)`: a 64-bit word in limb `0`. -/
def eK (c0 : UInt64) : E := eNew c0 0 0

/-- `GEN = E(2)`, the generator `x`. -/
def gen : E := eK 2

/-- `E::pow` (`field.rs`): square and multiply, low bit first. `fuel` bounds the loop by the exponent's
bits. -/
def epowAux : ℕ → E → E → ℕ → E
  | 0, _, out, _ => out
  | fuel + 1, base, out, n =>
    if n = 0 then out else epowAux fuel (base * base) (if n % 2 = 1 then out * base else out) (n / 2)

/-- `x^n` by square and multiply (`E::pow`, `Scalar::pow`). -/
def epow (x : E) (n : ℕ) : E := epowAux (Nat.log2 n + 1) x 1 n

/-- `x` squared `k` times: `x^(2^k)`. -/
def sqn (x : E) : ℕ → E
  | 0 => x
  | k + 1 => sqn (x * x) k

/-- `gpow(i) = GEN^i` (`layout.rs`). -/
def gpow (i : ℕ) : E := epow gen i

/-- `Σ values` (`Scalar::sum`). -/
def esum (values : List E) : E := values.foldl (· + ·) 0

/-- `Π values`. -/
def eprod (values : List E) : E := values.foldl (· * ·) 1

/-- `dot(left, right)` (`multilinear.rs`). -/
def dot (left right : List E) : E := (left.zip right).foldl (fun acc (x, y) ↦ acc + x * y) 0

/-- `eq_eval(left, right) = Π (1 + x + y)` (`multilinear.rs`). -/
def eqEval (left right : List E) : E := (left.zip right).foldl (fun acc (x, y) ↦ acc * (1 + x + y)) 1

/-- `eq_kernel(point)` (`multilinear.rs`): `eq(i, point)` for every index `i < 2^len`, LSB first. -/
def eqKernel (point : List E) : Array E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) #[1]

/-- One fold of `multilinear_eval`: `cur[i] = cur[2i] + r (cur[2i] + cur[2i+1])`. -/
def foldOnce (cur : Array E) (r : E) : Array E :=
  Array.ofFn (n := cur.size / 2) fun i ↦
    let a := cur.getD (2 * i.val) 0
    let b := cur.getD (2 * i.val + 1) 0
    a + r * (a + b)

/-- `multilinear_eval(mle, point)` (`multilinear.rs`): the multilinear extension of `mle` at `point`,
low coordinate first. The Rust's size check (`MultilinearSize`) holds at every call of this verifier. -/
def multilinearEval (mle : List E) (point : List E) : E :=
  (point.foldl foldOnce mle.toArray).getD 0 0

/-- `poly_eval(coefficients, x)` (`multilinear.rs`): Horner, constant first. -/
def polyEval (coefficients : List E) (x : E) : E := coefficients.foldr (fun c acc ↦ acc * x + c) 0

/-- `log2_ceil(v) = 64 − clz(v − 1)` (`multilinear.rs`), `0` at `0` and `1`. -/
def log2Ceil (v : ℕ) : ℕ := if v ≤ 1 then 0 else Nat.log2 (v - 1) + 1

/-- `u64::trailing_zeros`: `64` at zero. -/
def trailingZeros (n : ℕ) : ℕ :=
  if n = 0 then 64 else ((List.range 64).find? fun k ↦ n.testBit k).getD 64

/-- Bit `k` of `n` as an element of `E`: `E::new(n >> k & 1, 0, 0)`. -/
def bitE (n k : ℕ) : E := if n.testBit k then 1 else 0

end UniStatement

end
