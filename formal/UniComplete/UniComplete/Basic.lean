-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The writer is `leanvm_flock_gas::transcript::KeccakWriter`
-- (crates/leanvm_flock_gas, the prover's side of `KeccakChannel`); the polynomials are CompPoly's computable
-- `CPolynomial` (the `lean_vm` package set's).
import UniStatement.Security
import CompPoly.Univariate.Basic

/-!
# The honest prover's channel and its polynomials

* **The writer** (`Wr`, `KeccakWriter`): the stream written so far, how much of it the state has absorbed, the
  state, the challenges drawn. Sending appends bytes exactly as the verifier's `KeccakChannel` reads them
  (`sendScalar`: 24 bytes, limbs `2, 1, 0` big-endian; `sendRoot`: two 16-byte halves; `sendInteger`: a
  big-endian count); `sample` is the verifier's `sample` on the bytes since the last challenge.
* **Polynomials** (`Poly`, CompPoly's `CPolynomial E`, computable, with Mathlib's `Polynomial E` behind it): the
  digits' polynomials `w_l` (`wPoly`, `w_{l+1} = w_l² + w_l`), the novel basis `X_k = Π_{l ∈ k} w_l` (`ofNovel`,
  `toNovel`), a column's polynomial from its basis-`B` or novel coefficients, the subset-sum transform on `E`.

Nothing here is an FFT: the prover is mathematical (`toNovel` divides by `w_l`, the quotients are exact divisions),
fast enough only at the review's tiny shapes.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ### The writer -/

/-- **The prover's channel** (`KeccakWriter`): the stream so far, the bytes the state has absorbed, the state,
every challenge drawn. -/
structure Wr where
  stream : Array UInt8
  absorbed : ℕ
  state : Digest
  challenges : Array E

/-- The writer from the seed. -/
def Wr.start (seed : Digest) : Wr := ⟨#[], 0, seed, #[]⟩

/-- The prover's monad over `m`. -/
abbrev WrM (m : Type → Type) := StateT Wr m

/-- A scalar's 24 bytes as `next_scalar` reads them: limbs `2, 1, 0`, each big-endian. -/
def scalarWire (x : E) : List UInt8 := be64 (x.limb 2).lane ++ be64 (x.limb 1).lane ++ be64 (x.limb 0).lane

/-- A count's bytes as `next_integer(bytes)` reads it: big-endian. -/
def integerWire (n bytes : ℕ) : List UInt8 := (List.range bytes).map fun k ↦ (n >>> (8 * (bytes - 1 - k))).toUInt8

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- Append bytes to the stream. -/
def sendBytes (b : List UInt8) : WrM m Unit := modify fun c ↦ { c with stream := c.stream ++ b.toArray }

/-- `send(x)`: a scalar. -/
def sendScalar (x : E) : WrM m Unit := sendBytes (scalarWire x)

/-- Scalars, in order. -/
def sendScalars (xs : List E) : WrM m Unit := sendBytes (xs.flatMap scalarWire)

/-- `send_integer(n, bytes)`. -/
def sendInteger (n bytes : ℕ) : WrM m Unit := sendBytes (integerWire n bytes)

/-- `send_root(halves)`: the two halves, as `next_root` reads them (`rootWord`). -/
def sendRoot (halves : E × E) : WrM m Unit := sendBytes (rootWord halves)

/-- **`sample`**: Keccak-256 (`H`; over the permutation, `keccak256With F`) of the state and of the bytes written
since the last challenge; its low 192 bits the challenge (the verifier's `sample`, on the prover's side). -/
def sampleW : WrM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList
  let state ← (StateT.lift (H input) : WrM m Digest)
  let x := PcsQuotient.Transcript.challengeOf state
  set { c with absorbed := c.stream.size, state := state, challenges := c.challenges.push x }
  return x

/-- `count` challenges. -/
def samplesW : ℕ → WrM m (List E)
  | 0 => pure []
  | n + 1 => do
    let x ← sampleW H
    let rest ← samplesW n
    return x :: rest

end With

/-! ### Polynomials -/

/-- A computable polynomial over `E` (CompPoly's). -/
abbrev Poly : Type := CompPoly.CPolynomial E

/-- The constant polynomial. -/
abbrev pC (x : E) : Poly := CompPoly.CPolynomial.C x

/-- The variable. -/
abbrev pX : Poly := CompPoly.CPolynomial.X

/-- Evaluation. -/
abbrev pEval (x : E) (p : Poly) : E := CompPoly.CPolynomial.eval x p

/-- The digits' polynomials `w_0, …, w_{n−1}`: `w_0 = X`, `w_{l+1} = w_l² + w_l` (`w_l` is `V_l`'s subspace
polynomial, monic of degree `2^l`). -/
def wPolys (n : ℕ) : Array Poly :=
  (List.range n).foldl (fun (ws : Array Poly) _ ↦
    match ws.back? with
    | some w => ws.push (w * w + w)
    | none => ws.push pX) #[]

/-- `w_l`. -/
def wPoly (l : ℕ) : Poly := (wPolys (l + 1)).getD l 0

/-- **The polynomial of novel coefficients** `d` over `ws.size` variables: `Σ_k d_k X_k`, `X_k = Π_{l ∈ k} w_l`,
split on the top variable (`X_{2^(m−1) + k} = w_{m−1} X_k`). -/
def ofNovelWith (ws : Array Poly) : ℕ → Array E → Poly
  | 0, d => pC (d.getD 0 0)
  | m + 1, d =>
    let half := 2 ^ m
    ofNovelWith ws m (d.extract 0 half) + ws.getD m 0 * ofNovelWith ws m (d.extract half (2 * half))

/-- `Σ_k d_k X_k` for `2^m` novel coefficients. -/
def ofNovel (m : ℕ) (d : Array E) : Poly := ofNovelWith (wPolys m) m d

/-- **The novel coefficients** of a polynomial of degree `< 2^m`: the remainder and the quotient by `w_{m−1}`, each
recursively. -/
def toNovelWith (ws : Array Poly) : ℕ → Poly → Array E
  | 0, p => #[p.coeff 0]
  | m + 1, p =>
    let w := ws.getD m 0
    toNovelWith ws m (CompPoly.CPolynomial.modByMonic p w) ++ toNovelWith ws m (CompPoly.CPolynomial.divByMonic p w)

/-- The `2^m` novel coefficients of `p`. -/
def toNovel (m : ℕ) (p : Poly) : Array E := toNovelWith (wPolys m) m p

/-- The subset-sum transform on `2^r` entries of `E` (`subset_sums`): `c_k = Σ_{S ⊆ k} d_S`, its own inverse. -/
def subsetSumsE (r : ℕ) (d : Array E) : Array E :=
  (List.range r).foldl (fun a l ↦ Array.ofFn (n := a.size) fun k ↦
    if k.val.testBit l then a.getD k.val 0 + a.getD (k.val - 2 ^ l) 0 else a.getD k.val 0) d

/-- A `K`-column of `2^r` values (rows `ω_0 … ω_{2^r − 1}`): its novel coefficients, in `E`. -/
def novelOfValuesK (r : ℕ) (v : Array K) : Array E := (PcsQuotient.Domain.coefficients r 0 v).map ofK

/-- An `E`-column of `2^r` values: its novel coefficients. -/
def novelOfValuesE (r : ℕ) (v : Array E) : Array E := PcsQuotient.Domain.coefficients r 0 v

/-- An `E`-column's basis-`B` coefficients from its novel ones. -/
def bOfNovelE (r : ℕ) (d : Array E) : Array E := subsetSumsE r d

/-- The value of a column of basis-`B` coefficients `b` (`2^r`, in `E`) at the digits `w`: `b̂(w_0, …, w_{r−1})`
(SPEC.md §2; the verifier's `multilinearEval`, the Rust's `eval_e`). -/
def evalB (b : Array E) (r : ℕ) (w : List E) : E := multilinearEval b.toList (w.take r)

end UniComplete
