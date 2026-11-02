-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The unique decoder is Gao's (S. Gao, *A new algorithm for decoding Reed–Solomon codes*, in
-- Communications, Information and Network Security, V. Bhargava et al. (eds.), Kluwer, 2003,
-- pp. 55–68): the partial extended Euclidean algorithm on the points' vanishing polynomial and the
-- received word's interpolant. It runs on leanerVM's novel-basis transforms, lanes and prefix pruning
-- (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Extractor.lean`'s `novelInv`,
-- `novelFwd`, `laneSymbol`, `pruneStep`, `stackOf`, `johnsonThreshold`, used unchanged, and the shape
-- of its `fastStacks`); the novel basis is Lin, Chung and Han's (FOCS 2014). The basis changes
-- between the novel and the monomial basis are the recursive splitting `X_{j + 2^ℓ} = Ŵ_ℓ · X_j` of
-- that basis, written here.
module

public import Statement.Extractor

/-!
# The unique decoder

The extractor's second stage (`Extractor.lean`'s `extractFrom`): between mumbai's fast path
(`fastStacks`, interpolation from each lane's first `2^κ` columns, which one wrong symbol there
defeats) and its Guruswami–Sudan list decoder (`decodeStacks`), **each lane is uniquely decoded**:
Gao's decoder recovers the polynomial of degree `< k = 2^κ` whose evaluations on the `n = 2^(κ+R)`
points `x_v = K.ofBits v` differ from the lane in at most `⌊(n − k)/2⌋` columns (for the witness
table, `κ = 19`, `R = 1`: up to `2^18` wrong columns of `2^20`). The lanes' polynomials, in the novel
basis, are then pruned as the fast path's (`pruneStep` at the Johnson threshold) into at most one
stack (`uniqueStacks`).

**Gao's decoder** (`gao`): `g₀ = ∏_v (X − x_v)` (here the subspace polynomial `W_{κ+R}`, `κ + R + 2`
terms, `subspaceCoeffs`), `g₁` the lane's interpolant (`novelInv` then `toMono`); the extended
Euclidean algorithm on `(g₀, g₁)`, stopped at the first remainder `g` of degree `< (n + k)/2`, with
`v` its cofactor of `g₁`; the message is `g / v` if `v` divides `g` and the quotient has degree `< k`.
If the lane is within `⌊(n − k)/2⌋` of a codeword, `v` is the error locator (up to a constant) and
`g / v` the codeword's polynomial (Gao, Theorem 1).

**Cost** of one lane, in operations of `K` (`m = κ + R`, `e` the lane's wrong columns when it is within
the radius):

| Step | Cost |
| --- | --- |
| interpolant: `novelInv m`, `toMono m` | `m·2^m` butterflies (and `m·2^(m−1)` for the twiddles); `2^m·m(m+1)/2` |
| Euclid, stopped at degree `< (n + k)/2` | at most `deg v` divisions, `2·deg v·(n + 1)` multiplications in all, `deg v ≤ e` (and `≤ (n − k)/2` always); `2·(deg v)²` for the cofactors |
| `g / v`, `fromMono κ`, `novelFwd κ R` | `((n + k)/2)·(deg v + 1)`; `2^(κ−1)·κ(κ+1)/2`; `κ·2^m` |

At the witness table (`κ = 19`, `m = 20`): about `2^28` per lane without errors, plus about `2^21`
per wrong column; for the `64` lanes about `2^34`, and at most about `2^45` (`e = 2^18`). Every loop is
a `for` over an explicit range or a fold over an explicit list: no recursion without fuel.
-/

@[expose] public section

namespace PcsQuotient.UniqueDecoding

open LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction

/-! ### Polynomials over `K` as coefficient arrays, lowest first -/

/-- A polynomial's coefficients without trailing zeros (the zero polynomial is `#[]`), so that
`p.size − 1` is its degree: one scan from the top. -/
def trim (p : Array K) : Array K := Id.run do
  let mut q := p
  for _ in [0:p.size] do
    match q.back? with
    | some c => if c == 0 then q := q.pop else break
    | none => break
  return q

/-- The difference (the sum: characteristic two), trimmed. -/
def sub (a b : Array K) : Array K :=
  trim (Array.ofFn fun i : Fin (max a.size b.size) ↦ a.getD i.val 0 - b.getD i.val 0)

/-- The product, schoolbook: `|a|·|b|` multiplications. -/
def mul (a b : Array K) : Array K := Id.run do
  if a.size = 0 ∨ b.size = 0 then return #[]
  let mut c := Array.replicate (a.size + b.size - 1) (0 : K)
  for i in [0:a.size] do
    let ai := a.getD i 0
    if ai != 0 then
      for j in [0:b.size] do
        c := c.set! (i + j) (c.getD (i + j) 0 + ai * b.getD j 0)
  return trim c

/-- **Division with remainder** by a trimmed nonzero `b`: `(q, r)` with `a = q·b + r` and
`deg r < deg b`, both trimmed: `(|a| − |b| + 1)·|b|` multiplications and one inverse. -/
def divMod (a b : Array K) : Array K × Array K := Id.run do
  if a.size < b.size then return (#[], trim a)
  let db := b.size - 1
  let inv := (b.getD db 1)⁻¹
  let mut r := a
  let mut q := Array.replicate (a.size - db) (0 : K)
  for j in [0:a.size - db] do
    let d := a.size - 1 - j
    let c := r.getD d 0 * inv
    q := q.set! (d - db) c
    if c != 0 then
      for t in [0:b.size] do
        r := r.set! (d - db + t) (r.getD (d - db + t) 0 - c * b.getD t 0)
  return (trim q, trim (r.extract 0 db))

/-! ### Gao's decoder -/

/-- **Gao's decoder** for messages of degree `< k` on `n` points, `g₀` the points' vanishing
polynomial and `g₁` the received word's interpolant (degree `< n`): the remainders `r₀, r₁` of the
extended Euclidean algorithm on `(g₀, g₁)` and the cofactors `v₀, v₁` of `g₁` (`rᵢ ≡ vᵢ·g₁ mod g₀`),
until `deg r₁ < (n + k)/2` (at most `n + 1` divisions, each lowering `deg r₁`); then `r₁ / v₁` if `v₁`
divides `r₁` and the quotient has degree `< k`, `none` otherwise. -/
def gao (n k : ℕ) (g₀ g₁ : Array K) : Option (Array K) := Id.run do
  let mut r₀ := trim g₀
  let mut r₁ := trim g₁
  let mut v₀ : Array K := #[]
  let mut v₁ : Array K := #[1]
  for _ in [0:n + 1] do
    -- `deg r₁ < (n + k)/2`, `deg r₁ = r₁.size − 1` (the zero polynomial stops too)
    if 2 * r₁.size < n + k + 2 then break
    let (q, r) := divMod r₀ r₁
    r₀ := r₁
    r₁ := r
    let v := sub v₀ (mul q v₁)
    v₀ := v₁
    v₁ := v
  let (f, rem) := divMod r₁ v₁
  if rem.size = 0 ∧ f.size ≤ k then some f else none

/-! ### The subspace polynomials and the basis changes -/

/-- The value at `a` of the linearized polynomial `Σ_t c_t·X^(2^t)`: `|c|` squarings. -/
def linearizedEval (c : Array K) (a : K) : K :=
  (c.foldl (fun (acc : K × K) ct ↦ (acc.1 + ct * acc.2, acc.2 * acc.2)) (0, a)).1

/-- **The subspace polynomial** `W_i(X) = ∏_{v < 2^i} (X + x_v)` (mumbai's `subspacePoly`) as a
linearized polynomial: entry `t ≤ i` is its coefficient of `X^(2^t)`. `W_0 = X`, and
`W_{i+1}(X) = W_i(X)·W_i(X + x_{2^i}) = W_i(X)² + W_i(x_{2^i})·W_i(X)` (`W_i` is additive, its roots
`x_v`, `v < 2^i`, a subspace; squaring doubles the exponents in characteristic two). -/
def subspaceCoeffs : ℕ → Array K
  | 0 => #[1]
  | i + 1 =>
    let c := subspaceCoeffs i
    let a := linearizedEval c (K.ofBits (2 ^ i))
    Array.ofFn fun t : Fin (i + 2) ↦
      (if t.val = 0 then 0 else c.getD (t.val - 1) 0 ^ 2) + a * c.getD t.val 0

/-- The coefficients of the normalized subspace polynomial `Ŵ_i = W_i / W_i(x_{2^i})`, the factor of
the novel basis `X_j = ∏_{bit i of j} Ŵ_i` (mumbai's `novelTwiddles` normalizes alike). -/
def normalizedCoeffs (i : ℕ) : Array K :=
  let c := subspaceCoeffs i
  let s := (linearizedEval c (K.ofBits (2 ^ i)))⁻¹
  c.map (· * s)

/-- Stage `ℓ` of the novel-to-monomial change over a buffer of `2^m`, `w` the coefficients of `Ŵ_ℓ`:
each block of `2^(ℓ+1)`, its halves `lo` and `hi` already in the monomial basis, becomes
`lo + Ŵ_ℓ·hi` (`X_{j + 2^ℓ} = Ŵ_ℓ·X_j` for `j < 2^ℓ`): `(ℓ + 1)·2^m` multiplications. -/
def monoStage (m ℓ : ℕ) (w : Array K) (b : Array K) : Array K :=
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let r := p.val % 2 ^ (ℓ + 1)
    let hi := p.val - r + 2 ^ ℓ
    Nat.fold (ℓ + 1)
      (fun t _ acc ↦
        if 2 ^ t ≤ r ∧ r - 2 ^ t < 2 ^ ℓ then acc + w.getD t 0 * b.getD (hi + (r - 2 ^ t)) 0
        else acc)
      (if r < 2 ^ ℓ then b.getD p.val 0 else 0)

/-- **Novel to monomial basis**: the coefficients of `Σ_{j < 2^m} c_j·X_j` in the monomial basis,
stages `0, …, m − 1`: `2^m·m(m+1)/2` multiplications. -/
def toMono (m : ℕ) (c : Array K) : Array K :=
  (List.range m).foldl (fun b ℓ ↦ monoStage m ℓ (normalizedCoeffs ℓ) b) c

/-- Stage `ℓ` of the monomial-to-novel change over a buffer of `2^m`: each block of `2^(ℓ+1)`, a
polynomial in the monomial basis, divided by `Ŵ_ℓ` (its `ℓ + 1` terms): the remainder in the lower
half, the quotient in the upper. -/
def novelStage (m ℓ : ℕ) (w : Array K) (b : Array K) : Array K := Id.run do
  let lead := (w.getD ℓ 1)⁻¹
  let half := 2 ^ ℓ
  let mut a := b
  for blk in [0:2 ^ m / (2 * half)] do
    for j in [0:half] do
      let d := blk * (2 * half) + 2 * half - 1 - j
      let q := a.getD d 0 * lead
      if q != 0 then
        for t in [0:ℓ] do
          let pos := d - half + 2 ^ t
          a := a.set! pos (a.getD pos 0 - q * w.getD t 0)
      a := a.set! d q
  return a

/-- **Monomial to novel basis** (the inverse of `toMono`): stages `m − 1, …, 0`, about
`2^(m−1)·m(m+1)/2` multiplications. -/
def fromMono (m : ℕ) (p : Array K) : Array K :=
  (List.range m).foldr (fun ℓ b ↦ novelStage m ℓ (normalizedCoeffs ℓ) b) p

/-- The vanishing polynomial `W_m` of the `2^m` points `x_v`, `v < 2^m`, densely: its `m + 1` terms
`X^(2^t)` (monic). -/
def vanishing (m : ℕ) : Array K :=
  let w := subspaceCoeffs m
  (List.range (m + 1)).foldl (fun g t ↦ g.set! (2 ^ t) (w.getD t 0))
    (Array.replicate (2 ^ m + 1) 0)

/-! ### The lanes -/

/-- **The unique decoder of lane `u`** of the word `W`, for messages of `2^κ` coefficients on
`2^(κ+R)` columns: Gao's decoder on the lane's symbols (`laneSymbol`) at the points `x_v`, the message
returned in the novel basis (`2^κ` coefficients), `none` if it fails. -/
def laneDecode (κ R : ℕ) (W : ℕ → List K) (u : ℕ) : Option (Array K) :=
  let m := κ + R
  let g₁ := toMono m (novelInv m (Array.ofFn fun v : Fin (2 ^ m) ↦ laneSymbol W u v.val))
  (gao (2 ^ m) (2 ^ κ) (vanishing m) g₁).map fun f ↦
    fromMono κ (Array.ofFn fun i : Fin (2 ^ κ) ↦ f.getD i.val 0)

/-- **The unique-decoding stage**, for a word with errors: the fast path's pruning (`pruneStep` at the
Johnson threshold), with lane `u`'s list the unique decoder's message, if it finds one (`laneDecode`);
a lane is decoded only while survivors remain. At most one stack: the stack whose encoding agrees with
the word on at least `(n + k)/2` columns, when there is one (each lane then has at most `⌊(n − k)/2⌋`
wrong columns). -/
def uniqueStacks (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  let κ := μ - initialFold
  let st := (List.range (2 ^ initialFold)).foldl
    (fun st u ↦
      if st.isEmpty then [] else
        match laneDecode κ R W u with
        | some c => pruneStep (johnsonThreshold μ R) (laneSymbol W u) [(c, novelFwd κ R c)] st
        | none => [])
    [([], List.range (2 ^ (κ + R)))]
  st.map fun s ↦ stackOf μ s.1

end PcsQuotient.UniqueDecoding

end
