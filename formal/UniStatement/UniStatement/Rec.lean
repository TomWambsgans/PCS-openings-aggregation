-- Part of this repository. Transcribed from `crates/leanvm_flock_gas/src/transcript.rs` (`FsShape`, `squares`,
-- `NARROW_BITS`, `narrow`, `Channel::sample_narrow`, `sumcheck_drawn`, `cantor_beta1`, `pair_point`,
-- `pair_round_poly`, `sumcheck_pairs_drawn`), `flock_min.rs` (`zerocheck`'s draw, `Slices::TowerWalk`,
-- `verify_walked`, `walked_terminal`), `flock.rs` (`blake2s_row_values`, `RowValues`, adapted there from leanVM
-- (https://github.com/leanEthereum/leanVM), commit 42422001), `hash.rs` (`BLAKE2S_IV`, `BLAKE2S_SIGMA`,
-- `BLAKE2S_G_LANES`, leanVM's), `crates/leanvm_univariate/src/verifier.rs` (`reduce`'s `α` draw and walked Flock,
-- `batch`'s rounds) and `contract.rs` (`variant_bytes`, `contract_iv_for`), at `leanvm-rec` 4247e37. MIT OR
-- Apache-2.0; see NOTICE.md.
module

public import UniStatement.Opening

/-!
# π1's Fiat–Shamir shapes for the recursion: π1-rec, π1-rec2, π1-rec3

`crates/leanvm_rec/SPEC-REC.md` §1.4 and §12 (items 4, 6–8), `SPEC-POINTS.md`. The recursion's inner proof π1 is the
main line with its Fiat–Shamir shape changed (`FsShape`, a parameter here, **`main` by default**) and, from π1-rec2
on, Flock's lincheck terminal checked by π1's verifier itself (`walk`, `Slices::TowerWalk`):

| Rust | `Blake2s` | `fs` | `walk` |
|---|---|---|---|
| `FLOCK_MAIN` (the main line) | `.flock flockMain` | `.main` | `false` |
| `FLOCK_REC` (π1-rec) | `.flock flockMain` | `.rec1` | `false` |
| `FLOCK_REC2` (π1-rec2) | `.flock flockMain` | `.rec2` | `true` |
| `FLOCK_REC3` (π1-rec3, the recursion's) | `.flock flockMain` | `.rec3` | `true` |

* **Squares** (`.rec1`, `.rec2`, `.rec3`; `FsShape::draw`): the bus's `α = (c, c², c⁴, c⁸)` of one challenge `c`, and
  Flock's zerocheck eq coordinates after the seven fixed ones `c', c'², c'⁴, …` of one challenge `c'` (`drawRun`).
* **The walked terminal** (`walk`, `Slices::TowerWalk`: the main line's `tower` slices, and the terminal walked):
  Flock's lincheck terminal `r_lc` is checked against `walkedTerminal`, leanVM's forward walk of the BLAKE2s circuit
  on the sent slices (`blake2sRowValues`: `A0 w`, `B0 w`), collected as a zero (`FlockMatrixTerminal`). No matrices'
  reduction, no `a`, `b`, no claims on `A0`, `B0`: three calls, `C1`, `C2`, the setup, all at the batch's point.
* **Narrow challenges** (`.rec2`, `.rec3`): the batching sumcheck's challenges are the hash's low 160 bits
  (`sampleNarrow`: limb 2 cut to 32 bits, `narrowE`).
* **Paired rounds** (`.rec3`): the batch two variables a round (`sumcheckPairsDrawn`): pair `j`'s round polynomial
  `G_j` of degree `4 · 2` sent but `c_3` (`pairRoundPoly`: `Σ_(x ∈ V_2) G_j(x) = Σ_(e > 0, 3 | e) c_e`), one narrow
  challenge `z_j`, the point's two coordinates `pairPoint z_j = (z + β_1 (z² + z), z² + z)` (`cantorBeta1`); with
  the variables odd, a last plain round.
* **The IV binds the variant** (`variantBytes`, `contractIvForWith`; REVIEW-REC.md N2): with a shape other than
  `main`, the tag `fs-rec`, `fs-rec2` or `fs-rec3`, the skip and the slices' code are appended to the IV's preimage.

**The existing definitions are unchanged**: every function that changes has a parameterised copy here, named with
`Fs` (`Flock.zerocheckFs`, `Flock.frontFs`, `Flock.verifyFs`, `Flock.verifyDeferredFs`, `batchFs`, `reduceWithFs`,
`runWithFs`, `runFs`, `verifyWithFs`; and the new `Flock.verifyWalkedFs`), its body the original's but for the
draws, the walk and the batch's rounds. At `fs = .main`, `walk = false` each is the original (`…_main`, by `rfl`
after a case split on the configuration), so the proofs about the main line (`UniSound`, `UniComplete`) keep their
meaning and are not rebuilt. The verifier the recursion's π2 proves is `runFs reference iv publicInput stream
(.flock flockMain) .point .rec3 true`, and with its three openings `verifyWithFs … .rec3 true`.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **The verifier's Fiat–Shamir shape** (`transcript::FsShape`): which runs of challenges are derived, how wide the
batch's challenges are, and how many variables a batch round takes. -/
inductive FsShape where
  /-- Every challenge drawn, one Keccak-256 each: the main line's. -/
  | main
  /-- π1-rec (the Rust's `Rec`; `rec` is the recursor's name here): `α` and Flock's zerocheck eq point after its
  seven fixed coordinates as successive squares. -/
  | rec1
  /-- π1-rec2: `rec`, and the batching sumcheck's challenges narrow (160 bits). -/
  | rec2
  /-- π1-rec3: `rec2` with the batching sumcheck two variables a round. -/
  | rec3
  deriving DecidableEq, Repr, Inhabited

/-- Whether the batch's challenges are narrow (`.rec2`, `.rec3`). -/
def FsShape.narrow : FsShape → Bool
  | .rec2 | .rec3 => true
  | .main | .rec1 => false

/-- **`NARROW_BITS`**: a narrow challenge's bits, its top limb's low 32. -/
def narrowBits : ℕ := 160

/-- **`narrow(x)`**: the narrow challenge of a hash's challenge, its limb 2 cut to 32 bits. -/
def narrowE (x : E) : E := eNew (x.limb 0).lane (x.limb 1).lane ((x.limb 2).lane &&& 0xFFFFFFFF)

/-- **`squares(first, count)`**: `first, first², first⁴, …`, `count` terms, each the square of the one before. -/
def squares : E → ℕ → List E
  | _, 0 => []
  | x, n + 1 => x :: squares (x * x) n

/-- **`cantor_beta1()`**: `β_1` of the Cantor basis (`β_1² + β_1 = 1`, its low bit clear): `x^((2^64 − 1)/3)`, an
element of order 3, or it plus one, the one whose low bit is clear. -/
def cantorBeta1 : E :=
  let g := epow gen ((2 ^ 64 - 1) / 3)
  if (g.limb 0).lane &&& 1 = 0 then g else g + 1

/-- **`pair_point(z)`**: a pair's two coordinates at its challenge, `(y_0, y_1) = (z + β_1 y_1, z² + z)`, the
coordinate functionals of `V_2 = {0, 1, β_1, 1 + β_1}`. -/
def pairPoint (z : E) : List E :=
  let y1 := z * z + z
  [z + cantorBeta1 * y1, y1]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`Channel::sample_narrow`** (`KeccakChannel`: `narrow(self.sample())`): a challenge, cut to 160 bits. The channel
keeps the narrow one among its challenges. -/
def sampleNarrow : ChanM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList
  let state ← (keccak256With F input : m Digest)
  let x := narrowE (PcsQuotient.Transcript.challengeOf state)
  set { c with absorbed := c.cursor, state := state, challenges := c.challenges.push x }
  return x

/-- A challenge, narrow or not. -/
def sampleDrawn (narrow : Bool) : ChanM m E :=
  match narrow with
  | true => sampleNarrow F
  | false => sample F

/-- **`FsShape::draw(channel, count)`**: a run of `count` challenges, drawn one by one (`main`), or the first drawn and
each next the square of the one before (the others). -/
def drawRun (fs : FsShape) (count : ℕ) : ChanM m (List E) :=
  match fs with
  | .main => samples F count
  | .rec1 | .rec2 | .rec3 =>
    if count = 0 then pure [] else do
      let c ← sample F
      pure (squares c count)

/-- **`sumcheck_drawn(claim, count, equalities, narrow)`**: `sumcheck`, its challenges narrow when `narrow`. -/
def sumcheckDrawn (claim : E) (count : ℕ) (equalities : List (Option E)) (narrow : Bool) :
    ChanM m (List E × E) := do
  let mut point : Array E := #[]
  let mut claim := claim
  for equality in equalities do
    let message ← roundPoly (m := m) count claim equality
    let challenge ← sampleDrawn F narrow
    point := point.push challenge
    claim := polyEval message challenge
  return (point.toList, claim)

/-- **`pair_round_poly(degree, claim)`**: a pair's round polynomial `G` of degree `4 · degree`, its monomial
coefficients but `c_3` read (`c_0, c_1, c_2`, then `c_4 …`); `c_3` is the claim plus every read `c_e` with `e > 0`,
`3 | e` (over `V_2 = GF(4)`, `Σ_x x^e` is `1` exactly then). -/
def pairRoundPoly (degree : ℕ) (claim : E) : ChanM m (List E) := do
  let top := 4 * degree
  let low ← nextScalars (m := m) 3
  let high ← nextScalars (m := m) (top - 3)
  let c3 := (high.zip (List.range high.length)).foldl
    (fun acc (c, k) ↦ if (k + 4) % 3 = 0 then acc + c else acc) claim
  return low ++ [c3] ++ high

/-- **`sumcheck_pairs_drawn(claim, degree, vars, narrow)`** (π1-rec3, `SPEC-POINTS.md`): `vars` variables two at a
time, low first: pair `j`'s round polynomial, one challenge `z_j` (narrow when `narrow`), its two coordinates
`pairPoint z_j`; with `vars` odd a last plain round (`sumcheckDrawn` of `degree + 1` coefficients). The point, the
challenges, the last claim. -/
def sumcheckPairsDrawn (claim : E) (degree vars : ℕ) (narrow : Bool) : ChanM m (List E × List E × E) := do
  let mut point : Array E := #[]
  let mut challenges : Array E := #[]
  let mut claim := claim
  for _ in [0:vars / 2] do
    let message ← pairRoundPoly (m := m) degree claim
    let z ← sampleDrawn F narrow
    point := point ++ (pairPoint z).toArray
    challenges := challenges.push z
    claim := polyEval message z
  if vars % 2 = 1 then
    let (last, end_) ← sumcheckDrawn F claim (degree + 1) [none] narrow
    challenges := challenges ++ last.toArray
    point := point ++ last.toArray
    claim := end_
  return (point.toList, challenges.toList, claim)

end With

/-! ### The BLAKE2s circuit's walk (`flock.rs`'s `blake2s_row_values`, π1-rec2's terminal) -/

namespace Flock

/-- `BLAKE2S_IV`. -/
def blake2sIv : List ℕ :=
  [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

/-- `BLAKE2S_SIGMA`: the message schedule of the ten rounds. -/
def blake2sSigma : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- `BLAKE2S_G_LANES`: the four lanes of each of a round's eight gates. -/
def blake2sGLanes : List (List ℕ) :=
  [[0, 4, 8, 12], [1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15],
    [0, 5, 10, 15], [1, 6, 11, 12], [2, 7, 8, 13], [3, 4, 9, 14]]

/-- A 32-bit word of the walk: its bits' values. -/
abbrev WalkWord := Array E

/-- `RowValues::slots(base)`: the column weights at `base .. base + 32`. -/
def walkSlots (cw : Array E) (base : ℕ) : WalkWord := Array.ofFn (n := 32) fun b ↦ cw.getD (base + b.val) 0

/-- `RowValues::literal(value)`: the constant column's weight at each set bit of `value`. -/
def walkLiteral (cw : Array E) (value : ℕ) : WalkWord :=
  Array.ofFn (n := 32) fun b ↦ if value.testBit b.val then cw.getD constantColumn 0 else 0

/-- `xor(x, y)`. -/
def walkXor (x y : WalkWord) : WalkWord := Array.ofFn (n := 32) fun b ↦ x.getD b.val 0 + y.getD b.val 0

/-- `rotate_right(word, amount)`. -/
def walkRotr (w : WalkWord) (amount : ℕ) : WalkWord := Array.ofFn (n := 32) fun b ↦ w.getD ((b.val + amount) % 32) 0

/-- **`RowValues::add(x, y, carry_base)`**: the 31 carry rows of `x + y` (left `x_i + c`, right `y_i + c`, the carry
`c` the sum of the carry slots below `i`), and the sum's bits. -/
def walkAdd (cw left right : Array E) (x y : WalkWord) (carryBase : ℕ) : Array E × Array E × WalkWord := Id.run do
  let mut left := left
  let mut right := right
  let mut carry : E := 0
  let mut output : Array E := Array.replicate 32 0
  for bit in [0:32] do
    if bit < 31 then
      left := left.set! (carryBase + bit) (x.getD bit 0 + carry)
      right := right.set! (carryBase + bit) (y.getD bit 0 + carry)
    output := output.set! bit (x.getD bit 0 + y.getD bit 0 + carry)
    if bit < 31 then
      carry := carry + cw.getD (carryBase + bit) 0
  return (left, right, output)

/-- **`RowValues::add3(x, y, z, base)`**: the fused three-operand add, 31 majority rows then 30 ripple rows. -/
def walkAdd3 (cw left right : Array E) (x y z : WalkWord) (base : ℕ) : Array E × Array E × WalkWord := Id.run do
  let mut left := left
  let mut right := right
  let mut majority : Array E := Array.replicate 31 0
  for bit in [0:31] do
    left := left.set! (base + bit) (x.getD bit 0 + z.getD bit 0)
    right := right.set! (base + bit) (y.getD bit 0 + z.getD bit 0)
    majority := majority.set! bit (cw.getD (base + bit) 0 + z.getD bit 0)
  let rippleBase := base + 31
  let mut carry : E := 0
  let mut output : Array E := Array.replicate 32 0
  for bit in [0:32] do
    let q : E := if bit = 0 then 0 else majority.getD (bit - 1) 0
    let l := x.getD bit 0 + y.getD bit 0 + z.getD bit 0 + carry
    output := output.set! bit (l + q)
    if 1 ≤ bit ∧ bit ≤ 30 then
      left := left.set! (rippleBase + bit - 1) l
      right := right.set! (rippleBase + bit - 1) (q + carry)
      carry := carry + cw.getD (rippleBase + bit - 1) 0
  return (left, right, output)

/-- **`blake2s_row_values(column_weights)`**: `A0 w` and `B0 w`, by one forward walk of the BLAKE2s circuit (leanVM's
encoding: the chaining value, the message and the counters' linear rows, ten rounds of eight gates, each two
three-operand and two two-operand adds, the output's linear rows, the constant position). -/
def blake2sRowValues (cw : Array E) : Array E × Array E := Id.run do
  let size := 2 ^ blake2sR1csLogSize
  let constant := constantColumn
  let messageBase := 640
  let counterLow := 1152
  let counterHigh := 1184
  let finalFlag := 1216
  let lastNodeFlag := 1248
  let gatesBase := 1280
  let gateStride := 184
  let mut left : Array E := Array.replicate size 0
  let mut right : Array E := Array.replicate size 0
  for (base, length) in [(0, 256), (messageBase, 512), (counterLow, 128)] do
    for row in [base:base + length] do
      left := left.set! row (cw.getD row 0)
      right := right.set! row (cw.getD constant 0)
  -- v[0..8] = h, v[8..12] = IV[0..4], v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1).
  let mut state : Array WalkWord := Array.replicate 16 (Array.replicate 32 0)
  for word in [0:8] do
    state := state.set! word (walkSlots cw (32 * word))
  for word in [0:4] do
    state := state.set! (8 + word) (walkLiteral cw (blake2sIv.getD word 0))
  for (base, word) in [counterLow, counterHigh, finalFlag, lastNodeFlag].zip (List.range 4) do
    state := state.set! (12 + word) (walkXor (walkLiteral cw (blake2sIv.getD (4 + word) 0)) (walkSlots cw base))
  for (sigma, roundIndex) in blake2sSigma.zip (List.range blake2sSigma.length) do
    for (lanes, gateIndex) in blake2sGLanes.zip (List.range blake2sGLanes.length) do
      let gate := roundIndex * 8 + gateIndex
      let gateBase := gatesBase + gateStride * gate
      let la := lanes.getD 0 0
      let lb := lanes.getD 1 0
      let lc := lanes.getD 2 0
      let ld := lanes.getD 3 0
      let a := state.getD la #[]
      let b := state.getD lb #[]
      let c := state.getD lc #[]
      let d := state.getD ld #[]
      let mx := walkSlots cw (messageBase + 32 * sigma.getD (2 * gateIndex) 0)
      let my := walkSlots cw (messageBase + 32 * sigma.getD (2 * gateIndex + 1) 0)
      let (l1, r1, a1) := walkAdd3 cw left right a b mx gateBase
      let d1 := walkRotr (walkXor d a1) 16
      let (l2, r2, c1) := walkAdd cw l1 r1 c d1 (gateBase + 61)
      let b1 := walkRotr (walkXor b c1) 12
      let (l3, r3, a2) := walkAdd3 cw l2 r2 a1 b1 my (gateBase + 92)
      let d2 := walkRotr (walkXor d1 a2) 8
      let (l4, r4, c2) := walkAdd cw l3 r3 c1 d2 (gateBase + 153)
      let b2 := walkRotr (walkXor b1 c2) 7
      left := l4
      right := r4
      state := (((state.set! la a2).set! lb b2).set! lc c2).set! ld d2
  -- out[w] = h[w] ^ v[w] ^ v[w+8], the only materialised words.
  for word in [0:8] do
    let out := walkXor (walkXor (state.getD word #[]) (state.getD (word + 8) #[])) (walkSlots cw (32 * word))
    for bit in [0:32] do
      left := left.set! (256 + 32 * word + bit) (out.getD bit 0)
      right := right.set! (256 + 32 * word + bit) (cw.getD constant 0)
  left := left.set! constant (cw.getD constant 0)
  right := right.set! constant (cw.getD constant 0)
  return (left, right)

/-- **`walked_terminal(z_skip, row_low, chi_in, chi_in', s, α)`**: the lincheck's terminal as leanVM's verifier
computes it: the column weights `w = s ⊗ eq(chi_in')`, the walk's `A0 w` and `B0 w`, weighed by
`e = (L(z_skip) ⊗ eq(row_low)) ⊗ eq(chi_in)` and `α`, plus the `C = I` claim's term and the constant position's pin
(`knownWeights`). -/
def walkedTerminal (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) : E := Id.run do
  let (_, lowWeightsL) := rowLowWeights zSkip rowLow
  let lowWeights := lowWeightsL.toArray
  let slices := s.toArray
  let high := eqKernel chiInPrime
  let mut w : Array E := Array.replicate (2 ^ blake2sR1csLogSize) 0
  for h in [0:high.size] do
    for l in [0:slices.size] do
      w := w.set! (h * kBits + l) (slices.getD l 0 * high.getD h 0)
  let (left, right) := blake2sRowValues w
  let rows := eqKernel chiIn
  let mut matrix : E := 0
  for h in [0:rows.size] do
    let mut lSum : E := 0
    let mut rSum : E := 0
    for low in [0:lowWeights.size] do
      lSum := lSum + lowWeights.getD low 0 * left.getD (h * kBits + low) 0
      rSum := rSum + lowWeights.getD low 0 * right.getD (h * kBits + low) 0
    matrix := matrix + rows.getD h 0 * (lSum + alpha * rSum)
  let (cWeight, pinWeight) := knownWeights alpha chiIn chiInPrime
  return matrix + cWeight * dot lowWeightsL s + pinWeight * s.getD (constantColumn % kBits) 0

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`zerocheck(log_n, k, fs)`**: `zerocheck`, the coordinates after the seven fixed ones drawn as `fs` has it. -/
def zerocheckFs (logN k : ℕ) (fs : FsShape := .main) : ChanM m (Option E × List E × E × E × E) := do
  let sampled ← drawRun F fs (logN - k - nFixed)
  let r : List (Option E) := (fixedChallenges ++ sampled).map some
  let (zSkip, claim) ← if k > 0 then do
      let coset ← nextScalars (m := m) (2 ^ k)
      let z ← sample F
      pure (some z, lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ coset) z)
    else pure (none, 0)
  let (chi, running) ← sumcheck F claim 3 r
  let vA ← nextScalar (m := m)
  let vB ← nextScalar (m := m)
  return (zSkip, chi, vA, vB, running + vA * vB)

/-- `front`, its zerocheck drawn as `fs` has it. -/
def frontFs (logN : ℕ) (variant : Variant) (fs : FsShape := .main) : ChanM m Front := do
  let k := variant.skip
  let (zSkip, chi, vA, vB, vC) ← zerocheckFs F logN k fs
  let rowLow := chi.take (packing - k)
  let rest := chi.drop (packing - k)
  let chiIn := rest.take lincheckRounds
  let chiRest := rest.drop lincheckRounds
  let alpha ← sample F
  let claim := vA + alpha * vB + epow alpha 2 * vC + epow alpha 3
  let (roundChallenges, rLc) ← sumcheck F claim 3 (List.replicate lincheckRounds none)
  let chiInPrime := roundChallenges.reverse
  let s ← if variant.slices = .claim then pure none else some <$> nextScalars (m := m) kBits
  return ⟨zSkip, chi, rowLow, chiIn, chiInPrime, alpha, rLc, s, chiInPrime ++ chiRest⟩

/-- `verify`, its zerocheck drawn as `fs` has it. -/
def verifyFs (logN : ℕ) (variant : Variant) (fs : FsShape := .main) : ChanM m Reduced := do
  let fr ← frontFs F logN variant fs
  let (matrices, combination) ←
    reduceTerminal F fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices
  match fr.slices, combination with
  | some s, _ => return ⟨fr.point, matrices, ← ringEnd F variant s⟩
  | none, some (weights, value) => return ⟨fr.point, matrices, .combination weights value⟩
  | none, none => return ⟨fr.point, matrices, .combination [] 0⟩

/-- `verify_deferred`, its zerocheck drawn as `fs` has it. -/
def verifyDeferredFs (logN : ℕ) (variant : Variant) (fs : FsShape := .main) :
    ChanM m (List E × Option End × Pending) := do
  let fr ← frontFs F logN variant fs
  let pending := Pending.new fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices
  let end_ ← match fr.slices with
    | some s => some <$> ringEnd F variant s
    | none => pure none
  return (fr.point, end_, pending)

/-- **`verify_walked(log_n, variant)`** (`Slices::TowerWalk`, π1-rec2): the front (the slices sent), the lincheck's
terminal `r_lc` against the circuit's walk (`walkedTerminal`, collected: `FlockMatrixTerminal`), then the ring
switch's map and target. The slices' point and the ring switch's end; no claims on `A0`, `B0`. -/
def verifyWalkedFs (logN : ℕ) (variant : Variant) (fs : FsShape := .main) : ChanM m (List E × End) := do
  let fr ← frontFs F logN variant fs
  let s := fr.slices.getD []
  let terminal := walkedTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime s fr.alpha
  requireZero (m := m) (terminal + fr.rLc)
  let end_ ← ringEnd F variant s
  return (fr.point, end_)

theorem zerocheckFs_main (logN k : ℕ) : zerocheckFs F logN k .main = zerocheck F logN k := rfl

theorem frontFs_main (logN : ℕ) (variant : Variant) : frontFs F logN variant .main = front F logN variant := rfl

theorem verifyFs_main (logN : ℕ) (variant : Variant) : verifyFs F logN variant .main = verify F logN variant := rfl

theorem verifyDeferredFs_main (logN : ℕ) (variant : Variant) :
    verifyDeferredFs F logN variant .main = verifyDeferred F logN variant := rfl

end With

end Flock

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem sumcheckDrawn_false (claim : E) (count : ℕ) (equalities : List (Option E)) :
    sumcheckDrawn F claim count equalities false = sumcheck F claim count equalities := rfl

/-- **`batch(fs, …)`**: `batch`, its rounds as `fs` has them: plain (`main`, `rec1`), plain and narrow (`rec2`), paired
and narrow (`rec3`: degree 2 a variable, no pending matrices). -/
def batchFs (fs : FsShape) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E) := none)
    (pending : Option (Flock.Pending × List E) := none) :
    ChanM m (List (Commitment × Opening) × Option Flock.MatrixClaim) := do
  let lambda ← sample F
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, scale) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let target := match pending with
    | some (p, _) => target + scale * p.claim
    | none => target
  let (r, last) ← match fs with
    | .rec3 => do
      let (r, _, last) ← sumcheckPairsDrawn F target 2 vars true
      pure (r, last)
    | .main | .rec1 | .rec2 => sumcheckDrawn F target 3 (List.replicate vars none) fs.narrow
  let values ← nextScalars (m := m) combined.length
  let matrices ← match pending with
    | some _ => do
      let a ← nextScalar (m := m)
      let b ← nextScalar (m := m)
      pure (some (a, b))
    | none => pure none
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  let (sum, scale, openings, _) := (combined.zip values).foldl
    (fun (acc : E × E × Array (Commitment × Opening) × Option Combined) ((commitment, claim), value) ↦
      let (sum, scale, openings, bitSlice) := acc
      let layout := layoutOf commitment
      let weight := weightAt claim layout r ringMap
      let extension := (List.range' layout.vars (vars - layout.vars)).foldl
        (fun e j ↦ e * (1 + r.getD j 0)) 1
      let (mine, rest) := if commitment == .c1 then (bitSlice, none) else (none, bitSlice)
      (sum + scale * weight * extension * value, scale * lambda,
        openings.push (commitment, .point (r.take layout.vars) value mine), rest))
    (0, 1, #[], bitSlice)
  match pending, matrices with
  | some (p, flockPoint), some (a, b) =>
    let extension := (List.range' p.rounds (vars - p.rounds)).foldl (fun e j ↦ e * (1 + r.getD j 0)) 1
    if p.hasSlices then
      let (value, claim) := p.terminal r a b
      requireZero (m := m) (sum + scale * value * extension + last)
      return (openings.toList, some claim)
    else
      let (weights, claim) := p.combination r a b extension scale
      let relation : Relation := ⟨(weights.zip (List.range weights.length)).map
        (fun (c, i) ↦ ⟨.qflockBits, flockPoint, i, c⟩), sum + last⟩
      let combination := combine [relation] .c1 1
      let openings := openings.map fun (c, o) ↦ match c, o with
        | .c1, .point pt v _ => (c, .point pt v combination)
        | _, _ => (c, o)
      return (openings.toList, some claim)
  | _, _ =>
    requireZero (m := m) (sum + last)
    return (openings.toList, none)

theorem batchFs_main (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    batchFs F .main combined layouts bitSlice ringMap pending = batch F combined layouts bitSlice ringMap pending :=
  rfl

/-- **The verifier at a Fiat–Shamir shape** (`reduce`): `reduceWith`, but `α` drawn as `fs` has it (`drawRun`), Flock's
zerocheck likewise, the batch's rounds as `batchFs`, and with `walk` (`Slices::TowerWalk`) Flock's lincheck terminal
walked (`Flock.verifyWalkedFs`, in either mode: no matrices' reduction, no claims on `A0`, `B0`). Without Flock the
shape is the main line's (`Blake2s::fs`). -/
def reduceWithFs (shape : Shape) (publicWords : List E) (blake2s : Blake2s) (mode : ClaimsMode)
    (fs : FsShape := .main) (walk : Bool := false) : ChanM m Reduced := do
  if !shape.validate (blake2s != .omitted) then throw .invalidShape
  let fs := match blake2s with
    | .flock _ => fs
    | .omitted => .main
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  -- 0. The tables' row counts (F1): six 32-bit integers, absorbed with C1's root.
  let counts ← countBits (m := m) heights
  -- 1. C1, then the bus's and the constraints' challenges; α drawn as the shape has it.
  let root1 ← nextRoot (m := m)
  let alphas ← drawRun F fs 4
  let beta ← sample F
  let gamma ← sample F
  let weights := eqKernel alphas
  -- 2. Flock, on C1's q_flock: walked (π1-rec2), or with the point-claim ABI its matrices' reduction left pending.
  let logN := blake2sR1csLogSize + heights.getD opBlake2s 0
  let (flock, pending) : Option (List E × Option Flock.End × Option Flock.MatrixClaim) ×
      Option (Flock.Pending × List E) ← match blake2s, mode, walk with
    | .flock variant, _, true => do
      let (point, end_) ← Flock.verifyWalkedFs F logN variant fs
      pure (some (point, some end_, (none : Option Flock.MatrixClaim)), none)
    | .flock variant, .point, false => do
      let (point, end_, left) ← Flock.verifyDeferredFs F logN variant fs
      pure (some (point, end_, (none : Option Flock.MatrixClaim)), some (left, point))
    | .flock variant, .weighted, false => do
      let reduced ← Flock.verifyFs F logN variant fs
      pure (some (reduced.point, some reduced.end_, some reduced.matrices), none)
    | .omitted, _, _ => pure (none, none)
  -- 3. C2, then the point; the active rows' vanishing polynomials from the counts' bits (F1b).
  let root2 ← nextRoot (m := m)
  let t ← sample F
  let w := digits t (max h (rW + 4) + 2)
  let active := (counts.zip heights).map fun (bits, r) ↦ activeVanishingFromBits w bits r
  -- 4. The values at t, with the relations they take part in.
  let mut relations : Array Relation := #[]
  let mut parts : Array TablePart := #[]
  for table in tables do
    let (part, rels) ← tablePart (m := m) table (heights.getD table.opcode 0) weights beta w
    parts := parts.push part
    relations := relations ++ rels.toArray
  -- The memory: pull (SEP_MEM, g^i, final count, limbs) of every cell, push the same with count 1.
  let lm := shape.logMemory
  let memoryFinalCount ← nextScalar (m := m)
  let address ← nextScalar (m := m)
  let memoryPull ← nextScalar (m := m)
  relations := relations.push (Relation.equal (.memory 3) (w.take lm) memoryFinalCount)
  relations := relations.push (Relation.equal .address (w.take lm) address)
  relations := relations.push ⟨(List.range 3).map (fun k ↦ term (.memory k) (w.take lm) (weights.getD (3 + k) 0)),
    memoryPull + beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * address +
      weights.getD 2 0 * memoryFinalCount⟩
  let memoryPush := memoryPull + weights.getD 2 0 * (1 + memoryFinalCount)
  -- The bytecode: pull (SEP_BYTECODE, g^i, final count, instruction), push the same with count 1.
  let lb := shape.logBytecode
  let bytecodeFinalCount ← nextScalar (m := m)
  let bytecodePull ← nextScalar (m := m)
  relations := relations.push (Relation.equal .bytecodeFinal (w.take lb) bytecodeFinalCount)
  relations := relations.push (Relation.equal .bytecodeTuple (alphas ++ w.take lb)
    (bytecodePull + beta + weights.getD 2 0 * bytecodeFinalCount))
  let bytecodePush := bytecodePull + weights.getD 2 0 * (1 + bytecodeFinalCount)
  let heapValue ← nextScalar (m := m)
  let constraintValue ← nextScalar (m := m)
  -- 5. The constraint quotient's identity, on C1 but for Q_W(t), which is sent.
  let (constraint, quotientDegree) :=
    constraintRelation shape parts.toList publicWords gamma t constraintValue w
  relations := relations.push constraint
  let constraintChunks := chunks (quotientDegree + 1)
  let c2Columns : List (Column × ℕ × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (constraintChunks.zip (List.range constraintChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  -- 6. C2: the heap's tree, root and leaves, and Q_W's value.
  let (heapRels, leafColumns) := heapRelations shape active parts.toList weights beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush w constraintChunks
  relations := relations ++ heapRels.toArray
  let c2Columns := c2Columns ++ leafColumns
  -- 7. Flock's claim on q_flock: the ring switch's weight (one term, or 64), or one bit-slice combination.
  let tower := match blake2s with
    | .flock variant => variant.slices == .tower
    | .omitted => false
  let mut bitSliceRelations : List Relation := []
  let mut matrices : Option Flock.MatrixClaim := none
  let mut ringMap : Option (List E) := none
  match flock with
  | some (flockPoint, some flockEnd, flockMatrices) =>
    match flockEnd with
    | .ring map target =>
      if tower && mode == .point then
        relations := relations.push ⟨[⟨.qflock, flockPoint, ringTwist, 1⟩], target⟩
        ringMap := some map
      else
        let coefficients := if tower then Flock.towerCoefficients map else Flock.ringSwitchCoefficients map
        relations := relations.push ⟨(coefficients.zip (List.range coefficients.length)).map
          (fun (c, k) ↦ ⟨.qflock, flockPoint, k, c⟩), target⟩
    | .combination ws value =>
      bitSliceRelations := [⟨(ws.zip (List.range ws.length)).map
        (fun (c, i) ↦ ⟨.qflockBits, flockPoint, i, c⟩), value⟩]
    matrices := flockMatrices
  | _ => pure ()
  -- 8. One claim per commitment.
  let rho ← sample F
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine relations.toList c rho).map (c, ·)
  let bitSlice := combine bitSliceRelations .c1 1
  let stackLayouts := layouts shape c2Columns
  let stackVars := stackLayouts.map fun (c, l) ↦ (c, l.vars)
  let mut openings : List (Commitment × Opening) := []
  match mode with
  | .weighted =>
    openings := combined.map fun (c, claim) ↦ (c, .weighted claim)
    match bitSlice, openings with
    | some claim, (c, .weighted c1) :: rest =>
      let fresh := epow rho c1.relations
      let base := c1.points.length
      let merged : Combined := { c1 with
        points := c1.points ++ claim.points
        terms := c1.terms ++ claim.terms.map fun (column, p, twist, k) ↦ (column, p + base, twist, fresh * k)
        value := c1.value + fresh * claim.value }
      openings := (c, .weighted merged) :: rest
    | _, _ => pure ()
  | .point =>
    let (batched, deferred) ← batchFs F fs combined stackLayouts bitSlice ringMap pending
    openings := batched
    if deferred.isSome then matrices := deferred
  return ⟨(root1, root2), openings, matrices, relations.size, stackVars, stackLayouts⟩

set_option maxHeartbeats 4000000 in
/-- At the main line's shape and without the walk, `reduceWithFs` is `reduceWith` (by unfolding, case by case). -/
theorem reduceWithFs_main (shape : Shape) (publicWords : List E) (blake2s : Blake2s) (mode : ClaimsMode) :
    reduceWithFs F shape publicWords blake2s mode .main false = reduceWith F shape publicWords blake2s mode := by
  cases blake2s <;> cases mode <;> rfl

/-- **The verifier on calldata at a Fiat–Shamir shape** (`rust_verifier`): `runWith` with `reduceWithFs`. The IV is the
contract's (for a shape other than `main`, `contractIvForWith`'s). -/
def runWithFs (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) (fs : FsShape := .main) (walk : Bool := false) : m Outcome := do
  let seed ← seedWith F iv publicInput
  let walkM : ChanM m Reduced := do
    let r ← reduceWithFs F shape (publicWordsOf publicInput) blake2s mode fs walk
    finish (m := m)
    return r
  let (result, chan) ← (walkM.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

theorem runWithFs_main (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) :
    runWithFs F shape iv publicInput stream blake2s mode .main false =
      runWith F shape iv publicInput stream blake2s mode := by
  unfold runWithFs runWith
  rw [reduceWithFs_main]

end With

/-- The run over Keccak-f[1600] at a Fiat–Shamir shape: the deployed contract's computation. -/
def runFs (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) (fs : FsShape := .main) (walk : Bool := false) : Outcome :=
  Id.run (runWithFs (m := Id) (fun s ↦ pure (keccakF1600 s)) shape iv publicInput stream blake2s mode fs walk)

theorem runFs_main (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) : runFs shape iv publicInput stream blake2s mode .main false =
      run shape iv publicInput stream blake2s mode := by
  simp only [runFs, run, runWithFs_main]

/-! ### The contract's IV binds the variant (`variant_bytes`, `contract_iv_for`) -/

/-- **`variant_bytes(blake2s)`** (REVIEW-REC.md N2): nothing at the main line's shape (or without Flock); else the tag
`fs-rec`, `fs-rec2` or `fs-rec3`, then the skip and the slices' code (`InContract` 0, `Weighted` 1, `Claim` 2, `Tower`
3, `TowerWalk` 4: `tower` with `walk`). -/
def variantBytes (blake2s : Blake2s) (fs : FsShape) (walk : Bool) : List UInt8 :=
  match blake2s with
  | .omitted => []
  | .flock v =>
    if fs = .main then [] else
    let slices : ℕ := match walk, v.slices with
      | true, _ => 4
      | false, .inContract => 0
      | false, .weighted => 1
      | false, .claim => 2
      | false, .tower => 3
    let tag := match fs with
      | .rec2 => "fs-rec2"
      | .rec3 => "fs-rec3"
      | _ => "fs-rec"
    tag.toUTF8.toList ++ [v.skip.toUInt8, slices.toUInt8]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`contract_iv_for(shape, blake2s, program_iv, roots)`** over `F`: `contractIvWith`, with `variantBytes` appended to
its preimage when there are any. -/
def contractIvForWith (s : Shape) (blake2s : Blake2s) (fs : FsShape) (walk : Bool) (programIv : List UInt8)
    (roots : SetupRoots) : m (List UInt8) := do
  let extra := variantBytes blake2s fs walk
  if extra.isEmpty then contractIvWith F s programIv roots else
  let d ← keccak256With F (ivTag ++ programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes s ++ (layoutWords s).flatten ++ extra)
  return digestBytes d

end With

/-- The contract's IV over Keccak-f[1600] for a variant: the deployed contract's constant. -/
def contractIvFor (s : Shape) (blake2s : Blake2s) (fs : FsShape) (walk : Bool) (programIv : List UInt8)
    (roots : SetupRoots) : List UInt8 :=
  Id.run (contractIvForWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s blake2s fs walk programIv roots)

/-! ### The whole verifier at a Fiat–Shamir shape -/

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The verifier** over `F` at a Fiat–Shamir shape (`verifyWith`, the main line's Flock `flockMain`): the run, its
verdict, then the calls: `C1`, `C2`, the setup (one point claim each), then without the walk Flock's `A0` and `B0`
(with it there are none: π1-rec2, π1-rec3 make three calls). -/
def verifyWithFs (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) (fs : FsShape := .main) (walk : Bool := false) : m Bool := do
  let o ← runWithFs F shape iv publicInput.toList proof.stream (.flock flockMain) .point fs walk
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := layoutWords shape
    let callOf : Commitment → Digest × List UInt8 × Compile.Proof
      | .c1 => (rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    -- C1, C2, the setup: one point claim each.
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← pcsOpenWith F (layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    -- Flock's matrices: none with the walk, else A0 and B0.
    match r.matrices, walk with
    | some mc, false =>
      ok := ok && (← pcsOpenWith F (layoutWordVars (words.getD 3 [])) roots.a0 [⟨mc.point, mc.a⟩] proof.a0)
      ok := ok && (← pcsOpenWith F (layoutWordVars (words.getD 4 [])) roots.b0 [⟨mc.point, mc.b⟩] proof.b0)
    | none, true => pure ()
    | _, _ => ok := false
    return ok

end With

end UniStatement

end
