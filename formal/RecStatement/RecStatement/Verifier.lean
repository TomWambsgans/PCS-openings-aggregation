-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/pi2/verifier.rs`
-- (`NAME`, `frobenius`, `inverse`, `extension`, `reduce`'s transcript, `statement_words`, `verify`) and
-- `crates/leanvm_rec/src/pi2/prover.rs` (`layouts`, `quotient_chunks`, `layout_word`, `layout_words`, `iv`), branch
-- `leanvm-rec` @ 2b22581. The channel is `formal/UniStatement`'s (`KeccakChannel`); the layouts are
-- `formal/Statement`'s (`PcsQuotient.Layout.ofChunks`, `Layout::new`).
import RecStatement.Spec
import RecStatement.Core

/-!
# π2's verifier on calldata

**The transcript** (`KeccakChannel`, `PI2.md` §2): the seed `keccak(NAME ‖ IV ‖ public input)`,
`NAME = "leanvm-rec-pi2v1"`; the stream holds the public data (`Read`s: π1's roots `C1`, `C2` as `PCS_OPEN`'s
root words, π1's claims' elements: the pair challenges and the values), `W`'s root, then `α, β, γ` are drawn;
`Q`'s root, then `t`; the `2^r` fold values and `ξ = κ(t) + βσ(t)`, then `ρ`. The first challenge hashes the state
and everything read before it: the public data is bound there. Then the arithmetic (`CoreSpec.run`, over `E`, its
constants `Spec.of`'s: `Spec.core`), which requires one value nonzero (`Out.all`, the contract's one nonzero check).

**The IV** (`prover::iv`): `keccak("leanvm-rec-iv-v2" ‖ π1's contract IV ‖ the setup's root ‖ the circuit's digest ‖
W's, Q's and the setup's layout words)`; each layout word (`layout_word`) is the tag `"pi2"`, `log_n`, the table's
code (`0x5601` `W`, `0x5602` `Q`, `0x5603` the setup), its variables and the words its lanes fill.

**The tables' layouts** (`prover::layouts`, public layouts of `quotient::opening`): `W` (`m` variables, one chunk of
`N`), `Q` (`m + 5`: `h` and `q`'s four chunks, three limbs each, 15 chunks of `N`), the setup (`m + 1`: `κ` then
`κ + σ`), on stacks of at least `2^24` words (`2^15` below `2^20` positions).

**The inverse**: the arithmetic takes the field's; the Rust's is the norm's (`normInverse`: two Frobenius maps
from the limbs' shifts, Itoh–Tsujii on the norm in `K`), the same value for a nonzero element (the runner checks it on
every vector's `Out.all`).
-/

namespace RecStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## `E`'s helpers -/

/-- `Y`, the extension's generator (`F192::Y`). -/
def yE : E := UniStatement.eNew 0 1 0

/-- `x >> 64 = c_1 + c_2 Y` and `x >> 128 = c_2` (`Limbs::shifted`). -/
def shifted (x : E) : E × E :=
  (UniStatement.eNew (x.limb 1).lane (x.limb 2).lane 0, UniStatement.eNew (x.limb 2).lane 0 0)

/-- **`frobenius(x)`** `= x^(2^64)`: `x + (Y + Y²)(x >> 64) + (1 + Y²)(x >> 128)`. -/
def frobenius (x : E) : E :=
  let (u, v) := shifted x
  x + (yE + yE * yE) * u + (1 + yE * yE) * v

/-- **`inverse(x)`**, by the norm: `m = x^(2^64) x^(2^128)`, `N = x m` in `K`, `N^-1 = N^(2^64 − 2)` by the chain
`1, 2, 3, 6, 7, …, 62, 63`, then `x^-1 = m N^-1`. -/
def normInverse (x : E) : E := Id.run do
  let f := frobenius x
  let m := f * frobenius f
  let norm := x * m
  let mut t := norm
  let mut k := 1
  for bit in (List.range 5).reverse do
    let mut s := t
    for _ in [0:k] do
      s := s * s
    t := s * t
    k := 2 * k
    if (63 >>> bit) % 2 = 1 then
      t := t * t * norm
      k := k + 1
  return m * (t * t)

/-- **`extension()`**: the extension's coordinates `(Y/(1 + Y), Y²/(1 + Y²))` and the scale `1/((1 + Y)(1 + Y²))`
(`quotient::protocol::extension`). -/
def extension : (E × E) × E :=
  let y2 := yE * yE
  let d0 := 1 + yE
  let d1 := 1 + y2
  ((yE * d0⁻¹, y2 * d1⁻¹), (d0 * d1)⁻¹)

/-- `base::<S>(x)`: an element of `K` in `E`. -/
def kE (x : K) : E := ofK x

/-! ## The constants over `E` -/

def Coeff.toF (c : Coeff) : CoeffF E := ⟨c.field, c.gamma⟩

def Lin.toF (l : Lin) : LinF E := ⟨l.terms.map fun t ↦ (t.1.toF, t.2), l.constant.map Coeff.toF⟩

def Formula.toF (f : Formula) : FormulaF E :=
  ⟨f.lin.toF, f.products.map fun p ↦ (p.1.toF, p.2.1.toF, p.2.2.toF)⟩

/-- **The arithmetic's constants over `E`**: `Spec.of`'s, the walk `tagWalk`'s, the extension's, the points
`ω_i = point_e(i)`. -/
def Spec.core (s : Spec) : CoreSpec E :=
  { logN := s.logN
    logRow := s.logRow
    pairs := s.pairs.map fun p ↦ (p.logRows, kE p.z)
    groups := s.groups.map fun g ↦ ⟨g.role, g.formula.toF, g.pulls, g.pairs⟩
    c := s.c.map kE
    publicTerms := s.publicTerms.map fun t ↦ (t.tag, t.value.toF)
    walk := tagWalk (s.publicTerms.map (·.tag))
    zeroCoset := s.zeroCoset.map fun z ↦ (z.1, z.2.1, z.2.2.map kE)
    maxGamma := s.maxGamma
    y0 := extension.1.1
    y1 := extension.1.2
    scale := extension.2
    ω := UniStatement.pointE }

/-! ## The layouts, the layout words, the IV -/

/-- `MIN_LOG_STACK`, `MIN_CERTIFIED_STACK`, `CERTIFIED_FROM` (`prover.rs`). -/
def minLogStack : ℕ := 15
def minCertifiedStack : ℕ := 24
def certifiedFrom : ℕ := 20

/-- **`quotient_chunks(m)`**: chunk `8 limb + 4 kind + digit`, `h` (kind 0, digit 0) and `q`'s four chunks. -/
def quotientChunks (m : ℕ) : List (ℕ × ℕ) :=
  (List.range 3).flatMap fun limb ↦ (8 * limb, 2 ^ m) :: (List.range 4).map fun d ↦ (8 * limb + 4 + d, 2 ^ m)

/-- **`layouts(m)`**: `W`, `Q`, the setup (`Layout::new(vars, m, stack, chunks)`). -/
def layoutsOf (m : ℕ) : PcsQuotient.Layout × PcsQuotient.Layout × PcsQuotient.Layout :=
  let least := if certifiedFrom ≤ m then minCertifiedStack else minLogStack
  let stack (v : ℕ) : ℕ := max v least
  (PcsQuotient.Layout.ofChunks m m (stack m) [(0, 2 ^ m)],
    PcsQuotient.Layout.ofChunks (m + 5) m (stack (m + 4)) (quotientChunks m),
    PcsQuotient.Layout.ofChunks (m + 1) m (stack (m + 1)) [(0, 2 ^ m), (1, 2 ^ m)])

/-- `Layout::placed`: the words the lanes fill. -/
def placed (L : PcsQuotient.Layout) : ℕ := L.lanes.length * 2 ^ L.logLane

/-- The tables' codes (`WITNESS_CODE`, `QUOTIENT_CODE`, `SETUP_CODE`). -/
def witnessCode : ℕ := 0x5601
def quotientCode : ℕ := 0x5602
def setupCode : ℕ := 0x5603

/-- **`layout_word(code, m, layout)`**: `"pi2\0"`, `m` (byte 4), the code (bytes 22..24, big-endian), the variables
(byte 24), the words placed (bytes 25..32, big-endian). -/
def layoutWord (code m : ℕ) (L : PcsQuotient.Layout) : List UInt8 :=
  "pi2".toUTF8.toList ++ [0, m.toUInt8] ++ List.replicate 17 (0 : UInt8) ++ [(code >>> 8).toUInt8, code.toUInt8,
    L.vars.toUInt8] ++ (List.range 7).map fun k ↦ (placed L >>> (8 * (6 - k))).toUInt8

/-- **`layout_words(m)`**: `W`'s, `Q`'s, the setup's. -/
def layoutWords (m : ℕ) : List UInt8 × List UInt8 × List UInt8 :=
  let (w, q, s) := layoutsOf m
  (layoutWord witnessCode m w, layoutWord quotientCode m q, layoutWord setupCode m s)

/-- The IV's tag. -/
def ivTag : List UInt8 := "leanvm-rec-iv-v2".toUTF8.toList

/-- The transcript's name (`NAME`). -/
def name : List UInt8 := "leanvm-rec-pi2v1".toUTF8.toList

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`iv(pi1_iv, digest, setup_root, m)`** over `F`. -/
def ivWith (pi1Iv digest setupRoot : List UInt8) (logN : ℕ) : m (List UInt8) := do
  let (w, q, s) := layoutWords logN
  let d ← keccak256With F (ivTag ++ pi1Iv ++ setupRoot ++ digest ++ w ++ q ++ s)
  return digestBytes d

end With

/-- The IV over Keccak-f[1600]: the deployed contract's constant. -/
def iv (pi1Iv digest setupRoot : List UInt8) (logN : ℕ) : List UInt8 :=
  Id.run (ivWith (m := Id) (fun x ↦ pure (keccakF1600 x)) pi1Iv digest setupRoot logN)

/-! ## The run -/

/-- `cantor_beta1()`: `x^((2^64 − 1)/3)`, or it plus one, the one with its low bit clear (`β_1² + β_1 = 1`;
`UniStatement.cantorBeta1`, π1-rec3's). -/
def cantorBeta1 : E := UniStatement.cantorBeta1

/-- **`pair_point(z)`**: `(z + β_1 (z² + z), z² + z)`. -/
def pairPoint (z : E) : E × E :=
  let y1 := z * z + z
  (z + cantorBeta1 * y1, y1)

/-- **What the verifier leaves** (`Reduced`): the public scalars, their pair points, `W`'s and `Q`'s roots (each
two halves), what the transcript gave the arithmetic, and every value the arithmetic computes. -/
structure Reduced where
  scalars : List E
  pairPoints : List (E × E)
  roots : (E × E) × (E × E)
  inputs : Inputs E
  out : Out E

/-- `W`'s claim: `(ρ, ρ², …, ρ^(2^(r−1)), w_r, …, w_{m−1})`, value `Σ_k eq(ρ⃗, k) a_k`. -/
def Reduced.witness (r : Reduced) : List E × E := (r.out.witnessPoint, r.out.fold)

/-- `Q`'s claim at `(u_0, …, u_{m+1}, ρ', y_0, y_1)`, value `s (t/w_{m+2}) X/(S_d Y)`. -/
def Reduced.quotient (r : Reduced) : List E × E := (r.out.quotientPoint, r.out.quotientValue)

/-- `Q`'s claim at `h`'s top coefficient, value `s T`. -/
def Reduced.sum (r : Reduced) : List E × E := (r.out.sumPoint, r.out.sumValue)

/-- The setup's claim at `(w_0, …, w_{m−1}, β)`, value `ξ`. -/
def Reduced.setup (r : Reduced) : List E × E := (r.out.setupPoint, r.inputs.ξ)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`reduce`**: the public data, `W`'s root, `α, β, γ`, `Q`'s root, `t`, the fold values and `ξ`, `ρ`; then the
arithmetic. -/
def reduceWith (s : Spec) (statement : List E) : UniStatement.ChanM m Reduced := do
  let mut pubs := statement
  for rd in s.reads do
    match rd with
    | .integer b => pubs := pubs ++ [UniStatement.eK (UInt64.ofNat (← UniStatement.nextInteger (m := m) b))]
    | .root =>
      let (lo, hi) ← UniStatement.nextRoot (m := m)
      pubs := pubs ++ [lo, hi]
    | .scalar => pubs := pubs ++ [← UniStatement.nextScalar (m := m)]
  let wRoot ← UniStatement.nextRoot (m := m)
  let α ← UniStatement.sample F
  let β ← UniStatement.sample F
  let γ ← UniStatement.sample F
  let qRoot ← UniStatement.nextRoot (m := m)
  let t ← UniStatement.sample F
  let a ← UniStatement.nextScalars (m := m) (2 ^ s.logRow)
  let ξ ← UniStatement.nextScalar (m := m)
  let ρ ← UniStatement.sample F
  let inp : Inputs E := ⟨pubs, α, β, γ, t, a, ξ, ρ⟩
  return ⟨pubs, pubs.map pairPoint, (wRoot, qRoot), inp, s.core.run inp⟩

/-- **A run's outcome**: the result (the reduction, or the stream's error) and the channel at the end. -/
structure Outcome where
  result : Except UniStatement.UniError Reduced
  chan : UniStatement.Chan

/-- **The verdict**: no error, and the value the verifier requires nonzero is (the inversion's). -/
def Outcome.accepts (o : Outcome) : Bool :=
  match o.result with
  | .ok r => r.out.all != 0
  | .error _ => false

/-- **π2's verifier on calldata** over `F` (`verify`): the seed of the IV and the public input, the reduction, nothing
of the stream left. -/
def runWith (s : Spec) (iv publicInput : List UInt8) (stream : Array UInt8) : m Outcome := do
  let seed ← keccak256With F (name ++ iv ++ publicInput)
  let walk : UniStatement.ChanM m Reduced := do
    let r ← reduceWith F s (UniStatement.publicWordsOf publicInput)
    UniStatement.finish (m := m)
    return r
  let (result, chan) ← (walk.run).run (UniStatement.Chan.start seed stream)
  return ⟨result, chan⟩

end With

/-- The run over Keccak-f[1600]: the deployed contract's computation. -/
def run (s : Spec) (iv publicInput : List UInt8) (stream : Array UInt8) : Outcome :=
  Id.run (runWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s iv publicInput stream)

end RecStatement
