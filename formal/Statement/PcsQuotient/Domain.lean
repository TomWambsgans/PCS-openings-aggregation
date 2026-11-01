-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/domain.rs` (copied from leanVM, branch
-- PCS-openings-aggregation, commit 651453c6, `crates/flock/src/quotient/domain.rs`). The fields are
-- leanerVM's (`Statement/Field.lean`, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0).
module

public import Statement.Field

/-!
# The domain: a Cantor basis of `K = GF(2^64)`

The cells of the circuit are the points of the span of a **Cantor basis** of `K`
(`domain.rs:14-53`): `β₀ = 1` and `S(β_{k+1}) = β_k` for `S(x) = x² + x`, each `β_{k+1}` the
solution with its low bit clear. Cell `i` is the point `B(i) = Σ_{bit k of i} β_k` (`point`).
`w_k = S^k` is the subspace polynomial of the span of `β₀ … β_{k−1}` normalised at `β_k`
(`chain`), and a polynomial is held by its coefficients in the novel basis
`X_j = ∏_{bit k of j} w_k` (`novelEval`, `values`, `coefficients`).

The constants the verifier reads (`coordinates`, `rowVanishing`) are computed here as the Rust
computes them, by the same elimination; the differential test checks the verifier's outputs, hence
these constants, against the Rust's.

`values` and `coefficients` are the additive transform between the novel-basis coefficients of a
polynomial and its values on a coset `offset + span(β₀ … β_{m−1})` (`domain.rs:118-265`), one
butterfly stage per basis vector: the honest prover and the extractor use them; the verifier does
not.
-/

@[expose] public section

namespace PcsQuotient.Domain

open LeanVM.Parameters

/-- `S(x) = x² + x`, additive on `K` (`domain.rs:15`). -/
def S (x : K) : K := x * x + x

/-- `BASIS` (`domain.rs:12`): the basis vectors computed, enough for `2^28` points. -/
def basisSize : ℕ := 28

/-! ### The Cantor basis (`beta`, `domain.rs:20-53`)

`S` is `GF(2)`-linear on the 64 bit coordinates of `K`. Its matrix is reduced once, each pivot (by
its top bit) keeping the combination of unit vectors it is the image of; `solve` reads a target
off the pivots and clears the low bit of the preimage (the kernel of `S` is `{0, 1}`). -/

/-- A pivot: an image under `S` and the unit vectors it is the image of. -/
abbrev Pivot : Type := UInt64 × UInt64

/-- The top bit of a nonzero word. -/
def topBit (w : UInt64) : ℕ := Nat.log2 w.toNat

/-- Insert `(image, source)` into the pivots: reduce by the pivot of its top bit while there is
one; store it where there is none. Each step clears the top bit, so `64` steps suffice. -/
def insertPivot : ℕ → Array Pivot → UInt64 → UInt64 → Array Pivot
  | 0, pivots, _, _ => pivots
  | fuel + 1, pivots, image, source =>
    if image = 0 then pivots
    else
      let p := pivots.getD (topBit image) (0, 0)
      if p.1 = 0 then pivots.setIfInBounds (topBit image) (image, source)
      else insertPivot fuel pivots (image ^^^ p.1) (source ^^^ p.2)

/-- The reduced matrix of `S`: the images of the unit vectors `x^j`, `j < 64`. -/
def pivots : Array Pivot :=
  (List.range 64).foldl
    (fun ps j ↦ insertPivot 64 ps (S (K.ofBits (2 ^ j))).lane ((1 : UInt64) <<< j.toUInt64))
    (Array.replicate 64 (0, 0))

/-- The preimage of `image` under `S` read off the pivots (`solve`, `domain.rs:37-46`), the low bit
cleared. The Rust panics on a target outside the image of `S`; no basis vector is one (the
differential test reads the basis through the verifier's outputs). -/
def solveLoop : ℕ → UInt64 → UInt64 → UInt64
  | 0, _, source => source
  | fuel + 1, image, source =>
    if image = 0 then source
    else
      let p := pivots.getD (topBit image) (0, 0)
      solveLoop fuel (image ^^^ p.1) (source ^^^ p.2)

/-- `S⁻¹(target)` with its low bit clear. -/
def solve (target : K) : K := K.ofLane (solveLoop 64 target.lane 0 &&& ~~~(1 : UInt64))

/-- **The Cantor basis** `β₀ … β₂₇` (`beta`, `domain.rs:20-53`): `β₀ = 1`,
`β_{k+1} = S⁻¹(β_k)` with its low bit clear. -/
def beta : Array K :=
  (List.range (basisSize - 1)).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1))) #[1]

/-- `β_k`, `0` past the computed ones. -/
def betaAt (k : ℕ) : K := beta.getD k 0

/-- **The point of index `i`** (`point`, `domain.rs:56-73`): `B(i) = Σ_{bit k of i} β_k`. -/
def point (i : ℕ) : K :=
  (List.range basisSize).foldl (fun acc k ↦ if i.testBit k then acc + betaAt k else acc) 0

/-- `w_k(x)` for `k < count`: `w₀ = x`, `w_{k+1} = S(w_k)` (`chain`, `domain.rs:76-78`). -/
def chain (x : K) (count : ℕ) : List K :=
  (List.range count).foldl (fun ws _ ↦ ws ++ [S (ws.getLastD x)]) [x] |>.take count

/-- **The coordinates' constants** (`coordinates`, `domain.rs:82-88`): `b` with
`x_k = Σ_{j ≥ k} b[j − k] · w_j(x)` the `k`-th coordinate of a point `x` of the span of the first
`count` basis vectors; `b[0] = 1`, `b[d] = Σ_{e = 1}^{d} β_e · b[d − e]`. -/
def coordinates (count : ℕ) : List K :=
  ((List.range count).foldl
    (fun (b : Array K) d ↦
      if d = 0 then b.push 1
      else b.push ((List.range d).foldl (fun acc e ↦ acc + betaAt (e + 1) * b.getD (d - 1 - e) 0) 0))
    #[]).toList

/-- One Gauss–Jordan step on column `col` (`row_vanishing`, `domain.rs:102-114`): bring the first
row at or below `col` with a nonzero entry there to row `col`, scale it to `1`, and clear the column
in every other row. A column without a pivot is left (the Rust panics; the system is regular). -/
def eliminate (n : ℕ) (rows : Array (Array K)) (col : ℕ) : Array (Array K) :=
  let at_ (r c : ℕ) : K := (rows.getD r #[]).getD c 0
  match (List.range (n - col)).find? (fun d ↦ at_ (col + d) col ≠ 0) with
  | none => rows
  | some d =>
    let p := col + d
    let swapped : Array (Array K) := Array.ofFn (n := rows.size) fun r ↦
      if r.val = col then rows.getD p #[] else if r.val = p then rows.getD col #[] else rows.getD r #[]
    let pivotRow := (swapped.getD col #[]).map (· * ((swapped.getD col #[]).getD col 0)⁻¹)
    Array.ofFn (n := swapped.size) fun r ↦
      if r.val = col then pivotRow
      else
        let row := swapped.getD r #[]
        let factor := row.getD col 0
        if factor = 0 then row else Array.zipWith (fun x q ↦ x + factor * q) row pivotRow

/-- **The rows' vanishing polynomial** (`row_vanishing`, `domain.rs:92-116`): `τ` with
`Σ_{k < m−1} τ_k · w_k` the additive polynomial of degree `2^(m−2)` vanishing on the span of
`β₂ … β_{m−1}` (the cells of role `X`), `τ_{m−2} = 1`. One equation per `β_j`, `2 ≤ j < m`, as
`w_k(β_j) = β_{j−k}` for `k ≤ j` and `0` above, solved by Gauss–Jordan elimination. -/
def rowVanishing (m : ℕ) : List K :=
  let n := m - 2
  let rows : Array (Array K) := Array.ofFn (n := n) fun r ↦
    Array.ofFn (n := n + 1) fun k ↦ if k.val ≤ r.val + 2 then betaAt (r.val + 2 - k.val) else 0
  let reduced := (List.range n).foldl (eliminate n) rows
  (List.range n).map (fun k ↦ (reduced.getD k #[]).getD n 0) ++ [1]

/-! ### The constants' defining properties

The constants above are computed; what makes them the protocol's constants is stated here, each property
decidable and kernel-checked by `PcsQuotientTest/Constants.lean` (`decide`) at the sizes the protocol uses.
`S`, hence every `w_k`, is additive (`GF(2)`-linear) in characteristic two, so the properties on basis
vectors give the ones on every point of the span (`domain.rs`'s `transform_matches_the_basis` tests those). -/

/-- **The Cantor basis property** (`formal/`'s `CantorBasis`): `β₀ = 1` and `S(β_{k+1}) = β_k`, `k < 27`. -/
def IsCantorBasis : Prop :=
  betaAt 0 = 1 ∧ ∀ k : Fin (basisSize - 1), S (betaAt (k.val + 1)) = betaAt k.val

instance : Decidable IsCantorBasis := inferInstanceAs (Decidable (_ ∧ _))

/-- The `k`-th coordinate of `x` as the constants `b` read it: `Σ_{j ≥ k} b[j − k] · w_j(x)`. -/
def coordinateOf (count k : ℕ) (x : K) : K :=
  (List.range' k (count - k)).foldl
    (fun acc j ↦ acc + (coordinates count).getD (j - k) 0 * (chain x count).getD j 0) 0

/-- **The coordinates' property**: on the span of `β₀ … β_{count−1}`, coordinate `k` of `β_j` is `[j = k]`;
by additivity, coordinate `k` of `B(i)` is bit `k` of `i`. -/
def CoordinatesRead (count : ℕ) : Prop :=
  ∀ k j : Fin count, coordinateOf count k.val (betaAt j.val) = if j = k then 1 else 0

instance (count : ℕ) : Decidable (CoordinatesRead count) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- The rows' polynomial at `x`: `Σ_{k < m−1} τ_k · w_k(x)` (`row_poly` of `prove`). -/
def rowPolyAt (m : ℕ) (x : K) : K :=
  ((chain x (m - 1)).zip (rowVanishing m)).foldl (fun acc (w, t) ↦ acc + t * w) 0

/-- **The rows' polynomial's property**: monic in `w_{m−2}` (`τ_{m−2} = 1`: degree `2^(m−2)`), zero at
`β₂ … β_{m−1}`, and not zero at `1`, `β₁`, `1 + β₁`; by additivity, on the span of `β₀ … β_{m−1}` it vanishes
exactly at the points `B(i)` with `i ≡ 0 mod 4`, the cells of role `X`. -/
def RowVanishingProperty (m : ℕ) : Prop :=
  (rowVanishing m).getLast? = some 1 ∧ (∀ j : Fin m, 2 ≤ j.val → rowPolyAt m (betaAt j.val) = 0) ∧
    rowPolyAt m 1 ≠ 0 ∧ rowPolyAt m (betaAt 1) ≠ 0 ∧ rowPolyAt m (1 + betaAt 1) ≠ 0

instance (m : ℕ) : Decidable (RowVanishingProperty m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ### The novel basis and the additive transform (`domain.rs:118-283`) -/

/-- **A polynomial in the novel basis at a point** given by its digits `w_k(x)` (`evaluate`,
`domain.rs:267-283`): `Σ_j c_j · ∏_{bit k of j} digits_k`, the coefficients
`coeffs[first + step · j]` for `j < 2^|digits|`, folded from the lowest digit. -/
def novelEval (coeffs : Array K) (first step : ℕ) (digits : List E) : E :=
  let start : Array E := Array.ofFn (n := 2 ^ digits.length) fun j ↦
    ofK (coeffs.getD (first + step * j.val) 0)
  (digits.foldl
    (fun (cur : Array E) d ↦
      Array.ofFn (n := cur.size / 2) fun j ↦ cur.getD (2 * j.val) 0 + d * cur.getD (2 * j.val + 1) 0)
    start).getD 0 0

/-- A module the transform moves: `K` itself, or `E` scaled by `K`. -/
class Scalable (M : Type) extends Add M, Inhabited M where
  /-- `λ · v`. -/
  scale : K → M → M

instance : Scalable K where
  scale l v := l * v

instance : Scalable E where
  scale l v := ofK l * v

/-- Stage `k` of the transform on `2^m` entries at the coset `offset + span(β₀ … β_{m−1})`, in
either direction (`layers`, `forward_layer`, `inverse_layer`, `domain.rs:138-167`). In the block
`j` of `2^(k+1)` entries, `λ = w_k(offset) + B(2j)` (`w_k` is constant on the block's low half), and
the pair `(a, b)` at positions `p` and `p + 2^k` becomes `(a + λ·b, a + λ·b + b)` forward and
`(a + λ·(a + b), a + b)` backward. -/
def stage {M : Type} [Scalable M] (forward : Bool) (offsetDigits : List K) (k : ℕ)
    (a : Array M) : Array M :=
  let half := 2 ^ k
  let lams : Array K := Array.ofFn (n := a.size / (2 * half) + 1) fun j ↦
    offsetDigits.getD k 0 + point (2 * j.val)
  Array.ofFn (n := a.size) fun p ↦
    let r := p.val % (2 * half)
    let base := p.val - r + r % half
    let lo := a.getD base default
    let hi := a.getD (base + half) default
    let lam := lams.getD (p.val / (2 * half)) 0
    if forward then
      if r < half then lo + Scalable.scale lam hi else lo + Scalable.scale lam hi + hi
    else
      if r < half then lo + Scalable.scale lam (lo + hi) else lo + hi

/-- **Coefficients to values** (`values`, `domain.rs:257-260`): entry `i` of the `2^m`
novel-basis coefficients becomes the polynomial at `offset + B(i)`; the stages `m − 1, …, 0`. -/
def values {M : Type} [Scalable M] (m : ℕ) (offset : K) (coeffs : Array M) : Array M :=
  (List.range m).foldr (fun k a ↦ stage true (chain offset m) k a) coeffs

/-- **Values to coefficients** (`coefficients`, `domain.rs:262-265`): the inverse of `values`, the
stages `0, …, m − 1`. -/
def coefficients {M : Type} [Scalable M] (m : ℕ) (offset : K) (vals : Array M) : Array M :=
  (List.range m).foldl (fun a k ↦ stage false (chain offset m) k a) vals

end PcsQuotient.Domain

end
