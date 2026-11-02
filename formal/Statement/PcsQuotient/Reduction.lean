-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/protocol.rs` (`reduce`, `verify`, `label`, `sum_point`,
-- `bit_weight`, `coordinate_weight`, `extension`), adapted from leanVM's `flock::quotient` (branch
-- PCS-openings-aggregation, commit 651453c6). Fields and Keccak-256 are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0).
module

public import PcsQuotient.Relation
public import PcsQuotient.Domain
public import PcsQuotient.Transcript

/-!
# The reduction: five field elements to four claims

The verifier of the reduction (`reduce` and `verify`, `protocol.rs`): from the statement and
the reduction's proof (two commitments and five elements of `E`), the two commitments it names and
**four claims**, each a multilinear evaluation claim on a committed table: one on the witness table,
one on the circuit's wiring table, two on the quotient table (`Claims`). It rejects only a size the layouts do
not take (`Supported`: `2^17` to `2^22` rows), a malformed
commitment (a root's halves with a top limb) or a challenge at which a denominator vanishes; the
claims carry the rest, and the openings (`Opening.lean`) check them.

**The protocol** (`doc/quotient/main.tex` of leanVM's branch). The circuit has `2^m` cells,
`m = logRows + 2`, cell `i` at the point `B(i)` of the Cantor basis (`Domain.lean`), four a row
(`X, Y, C, V`), its gate `V = X + C + Y·C`. The prover commits the witness table (the cells'
polynomial in the novel basis, and masks), receives `α, β, γ`, commits the quotient table (the sum's
polynomial `h` and the two quotients), receives `t`, and sends the four values `a_j` of the row
polynomials at `t` and `next`, the wiring polynomial at `t`; `ρ` batches. Since a multilinear claim at
the point `(w_k(t))_k` is a univariate evaluation, each identity is one claim.

**Transcription.** The Rust is generic in its scalar (so that the same code is the EVM contract);
here the scalar is `E`. Two forms differ without changing a value: the proof is a structure
(`ReductionProof`, nine scalars in the stream's order) rather than a stream (a stream of another
length, which the Rust rejects as exhausted or trailing, is no `ReductionProof`); and the inverses are
taken one by one (`x⁻¹`) where the Rust inverts one product (by the norm to `K`, `protocol.rs`)
and unwinds it, after the same check that no denominator is zero.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Domain PcsQuotient.Transcript

/-! ### Constants -/

/-- `REGION` (`protocol.rs`): the public bits are the cells of the span of `11` basis vectors,
the `X` and `Y` cells of the `512` public rows. -/
def region : ℕ := 11

/-- `cell_vars` (`protocol.rs`): the cells' variables, `m = logRows + 2` (four cells a row).
-/
def cellVars (logRows : ℕ) : ℕ := logRows + 2

/-- `LOG_ROWS` (`circuit.rs:22`): the membership circuit has `2^22` rows, so `2^24` cells. -/
def logRows : ℕ := 22

/-- `MIN_LOG_ROWS` (`protocol.rs`): below `2^17` rows the witness table's hidden layout does not fit. -/
def minLogRows : ℕ := 17

/-- `MAX_LOG_ROWS` (`protocol.rs`): above `2^22` rows the quotient table's stack exceeds WHIR's `2^28` words.
-/
def maxLogRows : ℕ := 22

/-- `supported` (`protocol.rs`): the sizes the layouts take; the verifier rejects any other
(`VerifyError::Shape`). -/
def Supported (logRows : ℕ) : Prop := minLogRows ≤ logRows ∧ logRows ≤ maxLogRows

instance (logRows : ℕ) : Decidable (Supported logRows) := inferInstanceAs (Decidable (_ ∧ _))

/-- `bit_weight` (`protocol.rs`): the weight of bit `j < 128` of a public word, `x^j` in limb
`0` below `64` and `x^(j−64)` in limb `1` above: the weighted bits of a word sum to the element it is
read as. -/
def bitWeight (j : ℕ) : E :=
  if j < 64 then E.ofLimbs (K.ofBits (2 ^ j)) 0 0 else E.ofLimbs 0 (K.ofBits (2 ^ (j - 64))) 0

/-- `coordinate_weight` (`protocol.rs`): `m_k` for coordinate `k` of the public region, the
region's weight being `∏_k (1 + x_k (1 + m_k))`; `none` for `k ≥ 8`, where it is a power of `γ`. -/
def coordinateWeight (k : ℕ) : Option E :=
  if k = 0 then some (bitWeight 1)
  else if k = 1 then some 0
  else if k < 8 then some (bitWeight (2 ^ (k - 1)))
  else none

/-- `F192::Y`: the element `y`, limb `1`. -/
def ey : E := E.ofLimbs 0 1 0

/-- `extension` (`protocol.rs`): the two coordinates `(y/(1+y), y²/(1+y²))` of the extension
over the base field, and the scale `1/((1+y)(1+y²))` of the weights `(1, y, y², y³)` they give. -/
def extension : (E × E) × E :=
  let d0 := 1 + ey
  let d1 := 1 + ey * ey
  ((ey * d0⁻¹, ey * ey * d1⁻¹), (d0 * d1)⁻¹)

/-- `sum_point` (`protocol.rs`): the fixed point of the second claim on the quotient table,
the top coefficient of its first chunk: `m` ones, four zeros, the extension's coordinates. -/
def sumPoint (logRows : ℕ) : List E :=
  List.replicate (cellVars logRows) 1 ++ List.replicate 4 0 ++ [extension.1.1, extension.1.2]

/-- `label` (`protocol.rs`): the transcript's seed, `"pcs-quotient-kc1"`, the circuit's
commitment and the statement (`112` bytes). -/
def label (indexRoot : Digest) (stmt : Statement) : List UInt8 :=
  "pcs-quotient-kc1".toUTF8.toList ++ digestBytes indexRoot ++ stmt.y.toList ++ stmt.root.toList

/-- `halves` (`statement.rs:62-67`): a 32-byte value as two elements of `E`, sixteen bytes each read
as a big-endian number in limbs `0` (low) and `1` (high). -/
def halves (b : Bytes32) : E × E :=
  let half (h : ℕ) : E :=
    E.ofLimbs (K.ofLane (beWord b.toList (16 * h + 8))) (K.ofLane (beWord b.toList (16 * h))) 0
  (half 0, half 1)

/-- `Statement::halves` (`statement.rs:33-37`): `y` then `root`, each as its two halves. -/
def Statement.halves (stmt : Statement) : List E :=
  [(PcsQuotient.halves stmt.y).1, (PcsQuotient.halves stmt.y).2,
    (PcsQuotient.halves stmt.root).1, (PcsQuotient.halves stmt.root).2]

/-- **The statement embedding**: the eight public words `J < 8` the circuit's public rows hold (`finish`,
`circuit.rs`; `Circuit.lean`), each a 128-bit word in the low two limbs of `E`: `y` and `root` as their
halves, big-endian (`halves`), then word `4`, the constant one (bit `0` set: the row that pins `1`), and
words `5 … 7`, zero (the rows that pin `0`). The public bits must sum to `Σ_J γ^J · word_J`. -/
def statementWords (stmt : Statement) : List E := stmt.halves ++ [1, 0, 0, 0]

/-! ### The proof and the claims -/

/-- **The reduction's proof**: two commitments, each as the two scalars it rides the stream as
(`root_scalars`, `transcript.rs:16-18`: its 128-bit halves, two little-endian words each), and five
elements of `E`: the four row values `a_j` at `t` and `next`, the wiring polynomial at `t`. The Rust
stream is `witnessRoot, quotientRoot, values, next`, in this order (`prove`, `protocol.rs`).
-/
structure ReductionProof where
  witnessRoot : E × E
  quotientRoot : E × E
  values : Vector E 4
  next : E

/-- The stream of nine scalars, in the order sent. -/
def ReductionProof.stream (p : ReductionProof) : List E :=
  [p.witnessRoot.1, p.witnessRoot.2, p.quotientRoot.1, p.quotientRoot.2] ++ p.values.toList ++
    [p.next]

/-- The proof a stream of exactly nine scalars is; `none` for any other length (which the Rust
rejects: `Exhausted`, `Trailing`). -/
def ReductionProof.ofStream : List E → Option ReductionProof
  | [w0, w1, q0, q1, a0, a1, a2, a3, n] => some ⟨(w0, w1), (q0, q1), #v[a0, a1, a2, a3], n⟩
  | _ => none

/-- **A claim** (`opening::Claim`): the table's multilinear extension at `point` is `value`. -/
structure Claim where
  point : List E
  value : E
  deriving DecidableEq

/-- **The four claims** (`Claims`, `protocol.rs`): on the witness table, on the circuit's
wiring table, on the quotient table, and on the quotient table at the fixed point `sumPoint`. -/
structure Claims where
  witness : Claim
  wiring : Claim
  quotient : Claim
  sum : Claim
  deriving DecidableEq

/-- What the reduction leaves: the two commitments it names and the four claims. -/
structure Reduced where
  witnessRoot : Digest
  quotientRoot : Digest
  claims : Claims

/-! ### The claims at given challenges (`protocol.rs`) -/

/-- **The claims of a proof at the challenges** `α, β, γ, t, ρ`, or `none` if a denominator
vanishes (`VerifyError::Degenerate`). Line by line `reduce` after its transcript reads. -/
def claimsAt (logRows : ℕ) (stmt : Statement) (α β γ t ρ : E) (a : Vector E 4) (next : E) :
    Option Claims :=
  let m := cellVars logRows
  -- `w_k(t)`, `k ≤ m + 1`: up to the two digits past the cells.
  let w : List E := (List.range (m + 1)).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t +
    ws.getLastD t]) [t]
  let wAt (k : ℕ) : E := w.getD k 0
  -- The four cells of the row of `t`, and its gate `V + X + C + Y·C`.
  let theta := betaAt 1
  let cell (shift : K) (second : Bool) : E :=
    let first := t + ofK shift
    let second := if second then wAt 1 + 1 else wAt 1
    a[0] + first * a[1] + second * (a[2] + first * a[3])
  let x := cell 0 false
  let y := cell 1 false
  let c := cell theta true
  let v := cell (theta + 1) true
  let gate := v + x + c + y * c
  -- The public weight at `t`, and what the weighted public bits must sum to.
  let b := coordinates region
  let gamma2 := γ * γ
  let gammas : List E := [γ, gamma2, gamma2 * gamma2]
  let outside := (List.range' region (m - region)).foldl (fun acc k ↦ acc * (1 + wAt k)) 1
  let publicWeight := (List.range region).foldl
    (fun acc k ↦
      let coordinate := (List.range' (k + 1) (region - (k + 1))).foldl
        (fun s j ↦ s + ofK (b.getD (j - k) 0) * wAt j) (wAt k)
      let slope := match coordinateWeight k with
        | some weight => 1 + weight
        | none => 1 + gammas.getD (k - 8) 0
      acc * (1 + coordinate * slope))
    outside
  -- `Σ_J γ^J · word_J` by Horner's rule; the Rust writes it `s₀ + γ s₁ + γ²(s₂ + γ s₃) + γ⁴`, the same value.
  let target := (statementWords stmt).foldr (fun word acc ↦ word + γ * acc) 0
  -- The rows' polynomial at `t`, the copy identity's denominator.
  let tau := rowVanishing m
  let rows := (List.range (m - 1)).foldl (fun acc k ↦ acc + ofK (tau.getD k 0) * wAt k) 0
  let d := α + x + β * t
  let dNext := α + x + β * next
  let product := d * dNext
  let copies := d + dNext + publicWeight * x * product
  -- Every `1 + w_k`, the copy identity's denominator and the rows' polynomial, inverted.
  let denominators := w.map (1 + ·) ++ [product + wAt m, rows]
  if denominators.any (· = 0) then none
  else
    let inv (k : ℕ) : E := (denominators.getD k 1)⁻¹
    let u : List E := (List.range (m + 2)).map fun k ↦ wAt k * inv k
    let copyInverse := inv (m + 2)
    let rowsInverse := inv (m + 3)
    let middle := (List.range' 3 (m - 3)).foldl (fun acc k ↦ acc * inv k) (inv 2)
    let wiringScale := middle * inv 0 * inv 1
    let quotientScale := wiringScale * inv m * inv (m + 1)
    let rho2 := ρ * ρ
    let opened := (1 + rho2) * (a[0] + ρ * (a[0] + a[1])) + rho2 * (a[2] + ρ * (a[2] + a[3]))
    let identities := (1 + ρ) * copies * rows + ρ * product * gate
    some
      { witness := ⟨[ρ, rho2] ++ (u.drop 2).take (m - 1), opened * middle * inv m⟩
        wiring := ⟨u.take m, next * wiringScale⟩
        quotient := ⟨u ++ [wAt m * copyInverse, ρ, extension.1.1, extension.1.2],
          extension.2 * quotientScale * copyInverse * rowsInverse * identities⟩
        sum := ⟨sumPoint logRows, extension.2 * target⟩ }

/-! ### The reduction's verifier, over a permutation -/

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The reduction's verifier** over the permutation `F` (`verify` and `reduce`,
`protocol.rs`): read the witness table's root, draw `α, β, γ`; read the quotient table's
root, draw `t`; read the four values and `next`, draw `ρ`; then the claims. `none` on a size the layouts do
not take (`Shape`), a root whose
halves have a top limb (`NotARoot`) or a vanishing denominator (`Degenerate`). -/
def reduceWith (logRows : ℕ) (indexRoot : Digest) (stmt : Statement) (p : ReductionProof) :
    m (Option Reduced) := do
  if ¬ Supported logRows then return none
  let c ← Chain.startWith F (label indexRoot stmt)
  let c := (c.absorb p.witnessRoot.1).absorb p.witnessRoot.2
  match digestOfScalars p.witnessRoot with
  | none => return none
  | some witnessRoot =>
    let (α, c) ← c.squeezeWith F
    let (β, c) ← c.squeezeWith F
    let (γ, c) ← c.squeezeWith F
    let c := (c.absorb p.quotientRoot.1).absorb p.quotientRoot.2
    match digestOfScalars p.quotientRoot with
    | none => return none
    | some quotientRoot =>
      let (t, c) ← c.squeezeWith F
      let c := (p.values.toList.foldl Chain.absorb c).absorb p.next
      let (ρ, _) ← c.squeezeWith F
      return (claimsAt logRows stmt α β γ t ρ p.values p.next).map
        fun claims ↦ ⟨witnessRoot, quotientRoot, claims⟩

end With

end PcsQuotient

end
