-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/domain.rs` (the Cantor basis computed
-- as in `crates/quotient/src/domain.rs`, adapted there from leanVM (https://github.com/leanEthereum/leanVM), branch
-- PCS-openings-aggregation, commit 651453c6, `crates/flock/src/quotient/domain.rs`), for leanVM 42422001's `K`.
-- MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Basic

/-!
# The domain: the Cantor basis of `K` and the encodings (SPEC.md §2)

* **The Cantor basis** `β₀ = 1`, `s(β_{k+1}) = β_k`, `s(x) = x² + x`, each `β_{k+1}` the solution of
  `s(x) = β_k` with its low bit clear (`beta`, computed as the Rust computes it: `s` is `GF(2)`-linear on
  the 64 bits, its matrix reduced once). `ω_i = Σ_k i_k β_k` (`point`), `V_r = {ω_i : i < 2^r}`.
* **The digits** `w_0(t) = t`, `w_{k+1} = s(w_k)` (`digits`): `w_r` is `V_r`'s subspace polynomial,
  `w_l(ω_i) = ω_{i >> l}`. A column of `2^r` rows is committed as its coefficients in the basis
  `B_k = Π_l (w_l if k_l else 1 + w_l)`, so that its value at `t` is the multilinear extension of the
  coefficients at `(w_0(t), …, w_{r−1}(t))`.
* **The coordinate functionals** `y_l(x) = Σ_{m<r} a_{l,m} x^(2^m)` with `y_l(ω_i) = i_l` on `V_r`
  (`coordinateFunctionals`: the inverse of the transposed Moore matrix by Gauss–Jordan over `K`, as the
  Rust), read at `t` by `coordinatesAt`.
* **The vanishing polynomials** of the first `rows` points of `V_r` (`prefixVanishing`) and of the rest
  (`suffixVanishing`), products over aligned cosets; `w_m / w_r = Π_{j=r}^{m−1} (w_j + 1)`
  (`vanishingRatio`).

Each is checked against the Rust through the verifier's outputs (the differential test); the defining
properties (`s(β_{k+1}) = β_k`, `y_l(ω_i) = i_l`, the vanishing) are the Rust's unit tests
(`domain.rs`), not restated here.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters

/-- `BASIS` (`domain.rs`): basis vectors computed. -/
def basisSize : ℕ := 32

/-- `s(x) = x² + x` on `K`. -/
def sK (x : K) : K := x * x + x

/-- The index of the top set bit of a nonzero word (`63 − leading_zeros`). -/
def topBit (w : UInt64) : ℕ := Nat.log2 w.toNat

/-- Reduce `(image, source)` against the pivots, inserting it where its top bit has no pivot
(`beta`'s first loop, `domain.rs:33-44`). -/
def insertPivot (pivots : Array (UInt64 × UInt64)) (image source : UInt64) : Array (UInt64 × UInt64) :=
  Id.run do
    let mut image := image
    let mut source := source
    let mut pivots := pivots
    for _ in [0:65] do
      if image ≠ 0 then
        let top := topBit image
        let (pi, ps) := pivots.getD top (0, 0)
        if pi = 0 then
          pivots := pivots.set! top (image, source)
          image := 0
        else
          image := image ^^^ pi
          source := source ^^^ ps
    return pivots

/-- The reduced matrix of `s` over `GF(2)`: each pivot's image and what it was made of. -/
def sPivots : Array (UInt64 × UInt64) :=
  (List.range 64).foldl (fun piv j ↦
    let x : UInt64 := (1 : UInt64) <<< j.toUInt64
    insertPivot piv (sK (K.ofLane x)).lane x) (Array.replicate 64 (0, 0))

/-- `solve(target)` (`domain.rs:45-54`): the preimage of `target` under `s` with its low bit clear. -/
def solveS (target : K) : K := Id.run do
  let mut image := target.lane
  let mut source : UInt64 := 0
  for _ in [0:65] do
    if image ≠ 0 then
      let (pi, ps) := sPivots.getD (topBit image) (0, 0)
      image := image ^^^ pi
      source := source ^^^ ps
  return K.ofLane (source &&& ~~~1)

/-- **The Cantor basis** `β_0 … β_31` (`beta`, `domain.rs`): `β_0 = 1`, `β_{k+1} = solve(β_k)`. -/
def beta : Array K :=
  (List.range (basisSize - 1)).foldl (fun b _ ↦ b.push (solveS (b.back?.getD 1))) #[K.ofLane 1]

/-- `ω_i = Σ_{k : bit k of i} β_k` (`point`). -/
def point (index : ℕ) : K :=
  (List.range basisSize).foldl (fun acc k ↦ if index.testBit k then acc + beta.getD k 0 else acc) 0

/-- `ω_i` in `E` (`point_e`). -/
def pointE (index : ℕ) : E := ofK (point index)

/-- **The digits** `w_0(t), …, w_{count−1}(t)` (`digits`): `w_{k+1} = w_k² + w_k`. -/
def digits (t : E) (count : ℕ) : List E :=
  ((List.range (count - 1)).foldl (fun (ws : Array E) _ ↦
    let w := ws.back?.getD t
    ws.push (w * w + w)) #[t]).toList.take count

/-- `x` squared `m` times, in `K`. -/
def frobK (x : K) : ℕ → K
  | 0 => x
  | m + 1 => frobK (x * x) m

/-- **The coordinate functionals** `a[l][m]` (`coordinate_functionals`, `domain.rs`):
`y_l(x) = Σ_{m<r} a[l][m] x^(2^m)` with `y_l(ω_i) = i_l` for `i < 2^r`, by Gauss–Jordan on `[M | I]`,
`M[j][m] = β_j^(2^m)`, as the Rust (pivot: the first nonzero entry at or below the diagonal; rows
eliminated in order). -/
def coordinateFunctionals (r : ℕ) : Array (Array K) := Id.run do
  let mut rows : Array (Array K) := Array.ofFn (n := r) fun j ↦
    (Array.ofFn (n := r) fun mm ↦ frobK (beta.getD j.val 0) mm.val) ++
      Array.ofFn (n := r) fun c ↦ if c.val = j.val then (1 : K) else 0
  for col in [0:r] do
    let pivot := ((List.range' col (r - col)).find? fun i ↦
      (rows.getD i #[]).getD col 0 ≠ 0).getD col
    let rowCol := rows.getD col #[]
    let rowPivot := rows.getD pivot #[]
    rows := (rows.set! col rowPivot).set! pivot rowCol
    let inverse := ((rows.getD col #[]).getD col 0)⁻¹
    rows := rows.set! col ((rows.getD col #[]).map (· * inverse))
    for i in [0:r] do
      let factor := (rows.getD i #[]).getD col 0
      if i ≠ col ∧ factor ≠ 0 then
        let pivotRow := rows.getD col #[]
        rows := rows.set! i ((rows.getD i #[]).zipWith (fun x p ↦ x + factor * p) pivotRow)
  return Array.ofFn (n := r) fun l ↦ Array.ofFn (n := r) fun mm ↦
    (rows.getD mm.val #[]).getD (r + l.val) 0

/-- **`y_0(t), …, y_{r−1}(t)`** (`coordinates_at`): the successive squares of `t`, then each functional's
combination of them. -/
def coordinatesAt (t : E) (functionals : Array (Array K)) : List E :=
  let r := functionals.size
  let frobenius : List E := (List.range r).map fun mm ↦ sqn t mm
  functionals.toList.map fun row ↦
    (row.toList.zip frobenius).foldl (fun acc (a, x) ↦ if a ≠ 0 then acc + ofK a * x else acc) 0

/-- **The vanishing polynomial of the first `rows` points** of `V_r` at the point whose digits are `w`
(`prefix_vanishing`): over the aligned cosets `ω_a + V_b` of `[0, rows)`'s binary decomposition, the
product of `w_b + ω_{a >> b}`. -/
def prefixVanishing (w : List E) (rows : ℕ) : E := Id.run do
  let mut product : E := 1
  let mut start := 0
  for i in [0:64] do
    let b := 63 - i
    if rows.testBit b then
      product := product * (w.getD b 0 + pointE (start >>> b))
      start := start + 2 ^ b
  return product

/-- **The vanishing polynomial of `[rows, 2^r)`** in `V_r` (`suffix_vanishing`): aligned cosets from
`rows` up, each the largest that is aligned and fits. -/
def suffixVanishing (w : List E) (rows r : ℕ) : E := Id.run do
  let mut product : E := 1
  let mut start := rows
  for _ in [0:2 * r + 2] do
    if start < 2 ^ r then
      let mut b := min (trailingZeros start) r
      for _ in [0:r + 1] do
        if start + 2 ^ b > 2 ^ r then b := b - 1
      product := product * (w.getD b 0 + pointE (start >>> b))
      start := start + 2 ^ b
  return product

/-- `w_m / w_r = Π_{j=r}^{m−1} (w_j + 1)` (`vanishing_ratio`). -/
def vanishingRatio (w : List E) (r m : ℕ) : E :=
  (List.range' r (m - r)).foldl (fun acc j ↦ acc * (w.getD j 0 + 1)) 1

end UniStatement

end
