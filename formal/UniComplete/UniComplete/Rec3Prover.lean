-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `crates/leanvm_univariate/src/prover/prove.rs`
-- and `batch.rs` (`prove_pairs`) at `FLOCK_REC3` (`leanvm-rec` 4247e37), `crates/lv42_flock`'s zerocheck draw
-- (`EqPoint::Squares`), and `crates/leanvm_flock_gas/src/transcript.rs` (`FsShape::draw`, `Channel::sample_narrow`);
-- the verifier it writes for is `formal/UniStatement/UniStatement/Rec.lean`'s `reduceWithFs … .rec3 true`.
import UniComplete.Rec3Pairs
import UniComplete.ProverSim
import UniComplete.FlockProver
import UniStatement.RecSecurity

/-!
# π1-rec3's honest prover

The main line's prover (`Prover.lean`, `Witness.lean`, `Batch.lean`, `FlockProver.lean`) with π1-rec3's changes, in
the verifier's order (`reduceWithFs … (.flock flockMain) .point .rec3 true`):

1. **`α = squares c 4`** of one challenge `c` (`drawRunW`, the verifier's `drawRun .rec3 4`), then `β`, `γ` drawn;
2. **Flock** (`flockProve3`): the main line's honest Flock prover (`FlockP`) but the zerocheck's eq coordinates after
   the seven fixed ones `squares c' (log_n − k − 7)` of one challenge `c'` (`zerocheckW3`); the lincheck's slices are
   sent; no matrices' reduction is run (the verifier walks the lincheck's terminal, `Flock.verifyWalkedFs`), so the
   output's `pending` and `tables` are not used;
3. `C2`, `t`, the values at `t`, `ρ`, the combined claims: the main line's (`c2DataOf`, `atTOf`, `combine`);
4. **the batch two variables a round** (`batchRounds3`): `λ`, then `vars / 2` pair rounds (`pairRound3`: the eight
   scalars `msg8 cs` of the pair polynomial `G(X) = Σ_k λ^k Σ_u W_k C_k (r, pairPoint X, u)`, `pairMsgOf`; one narrow
   challenge `z`, `sampleNarrowW`; every table folded at `pairPoint z`'s two coordinates), with `vars` odd a last plain
   narrow round (`plainRound3`); the stacks' values at the point; **no pending `λ^n` term, no `a`, `b`**;
5. the IV binds the variant (`contractIvRec3Of`, `contractIvForWith`'s preimage with `variantBytes`); **three WHIR
   openings** (`C1`, `C2`, the setup); the proof's `a0`, `b0` are empty (`noProof`, the verifier reads neither).

**A pair's polynomial, computed** (`prove_pairs` computes it by interpolation at `0, 1, β_1`; here directly): each
table's quadruple `i`, folded low coordinate first at `(y_0(X), y_1(X)) = pairPoint X`, is
`f₀ + y₀ (f₀ + f₁) + y₁ (f₀ + f₂) + y₀ y₁ (f₀ + f₁ + f₂ + f₃)`, a polynomial of degree `4` (`quadCoeffs`, with
`y₀ = (1 + β_1) X + β_1 X²`, `y₁ = X + X²`, `y₀ y₁ = (1 + β_1) X² + X³ + β_1 X⁴` in characteristic two); a weight's
and its stack's multiply (`mul5`, degree `8`); the products are summed over the `2^(vars − 2j − 2)` quadruples
(`pairPolyOf`) and weighed by `λ^k` (`pairMsgOf`).

Decisions (recorded):
* The Flock prover is a parameter (`FlockProver m`, `FlockProverH`) as in the main line; π1-rec3's honest one is
  `flockProve3H`. The blake2s configuration is fixed at `.flock flockMain` (π1-rec3 has no other).
* The batch's state is the main line's `BatchState` with no matrices (`matrices = none`, `matrixValue = 0`).
* The sums run over the batch's uniform counts (`2^(vars − 2j − 2)` quadruples a pair round, one pair in the last
  plain round), every table read with `getD` (zero past its size: a stack shorter than the batch is zero-extended, as
  the Rust's `extend`), so the algebra needs no size bookkeeping (`Rec3Batch.lean`).
-/

namespace UniComplete.Rec3

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## The writer's draws -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **`sample_narrow`** on the prover's side: a challenge, cut to 160 bits (`narrowE`); the writer keeps the narrow one
among its challenges, as the verifier's `sampleNarrow` does. -/
def sampleNarrowW : WrM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList
  let state ← (StateT.lift (H input) : WrM m Digest)
  let x := narrowE (PcsQuotient.Transcript.challengeOf state)
  set { c with absorbed := c.stream.size, state := state, challenges := c.challenges.push x }
  return x

/-- **`FsShape::draw` at π1-rec3**: a run of `count` challenges, the first drawn and each next the square of the one
before (none drawn for an empty run; the verifier's `drawRun .rec3`). -/
def drawRunW (count : ℕ) : WrM m (List E) :=
  if count = 0 then pure [] else do
    let c ← sampleW H
    pure (squares c count)

end With

/-! ## Flock's honest prover at π1-rec3 -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **The zerocheck at π1-rec3** (`zerocheckFs … .rec3`): the main line's `FlockP.zerocheckW`, its eq coordinates after
the seven fixed ones the squares of one challenge. -/
def zerocheckW3 (logN k : ℕ) (wit : FlockP.Wit) : WrM m (Option E × List E × E × E × E) := do
  let sampled ← drawRunW H (logN - k - nFixed)
  let st ← FlockP.skipW H k (fixedChallenges ++ sampled) wit
  let zc ← FlockP.zcRounds H (fixedChallenges ++ sampled) st.claim st.a st.b st.c
  sendScalar zc.va
  sendScalar zc.vb
  return (st.zSkip, zc.chi, zc.va, zc.vb, zc.running + zc.va * zc.vb)

/-- **Flock's front at π1-rec3** (`frontFs … .rec3`): `FlockP.frontW` with `zerocheckW3`. -/
def frontW3 (logN : ℕ) (variant : Variant) (q : Array K) : WrM m (Front × List E) := do
  let zc ← zerocheckW3 H logN variant.skip (FlockP.witOf logN q)
  let alpha ← sampleW H
  let lc ← FlockP.lcRounds H lincheckRounds (FlockP.lcClaim zc alpha) (FlockP.lcWeightsOf variant.skip zc alpha)
    (FlockP.lcWitnessOf variant.skip q zc)
  let slices ← FlockP.sendSlices (m := m) variant lc.z.toList
  return FlockP.frontOf variant zc alpha lc slices

/-- **Flock's honest prover at π1-rec3** (`Flock.verifyWalkedFs … .rec3`: the front, the walk checked by the verifier
alone, the ring switch's map): `FlockP.flockProve` with `frontW3`. -/
def flockProve3 : FlockProver m := fun logN variant q ↦ do
  let frs ← frontW3 H logN variant q
  let end_ ← FlockP.endW H variant frs.1.slices
  return FlockP.assemble frs.1 frs.2 end_

end With

/-- **π1-rec3's honest Flock prover**, generic in the monad and the hash. -/
def flockProve3H : FlockProverH := fun H ↦ flockProve3 H

/-! ## The paired batch -/

/-- **A quadruple folded at `pairPoint X`**: the five coefficients of `f₀ + y₀ (f₀ + f₁) + y₁ (f₀ + f₂) +
y₀ y₁ (f₀ + f₁ + f₂ + f₃)`, `y₀ = (1 + b) X + b X²`, `y₁ = X + X²`. -/
def quadCoeffs (b : E) (f : Array E) (i : ℕ) : List E :=
  let f0 := f.getD (4 * i) 0
  let f1 := f.getD (4 * i + 1) 0
  let f2 := f.getD (4 * i + 2) 0
  let f3 := f.getD (4 * i + 3) 0
  let B := f0 + f1
  let C := f0 + f2
  let D := f0 + f1 + f2 + f3
  [f0, B * (1 + b) + C, B * b + C + D * (1 + b), D, D * b]

/-- The product of two polynomials of five coefficients: nine. -/
def mul5 (p q : List E) : List E :=
  let a0 := p.getD 0 0
  let a1 := p.getD 1 0
  let a2 := p.getD 2 0
  let a3 := p.getD 3 0
  let a4 := p.getD 4 0
  let b0 := q.getD 0 0
  let b1 := q.getD 1 0
  let b2 := q.getD 2 0
  let b3 := q.getD 3 0
  let b4 := q.getD 4 0
  [a0 * b0, a0 * b1 + a1 * b0, a0 * b2 + a1 * b1 + a2 * b0, a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0,
    a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0, a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1,
    a2 * b4 + a3 * b3 + a4 * b2, a3 * b4 + a4 * b3, a4 * b4]

/-- The sum of two polynomials of nine coefficients. -/
def add9 (p q : List E) : List E :=
  [p.getD 0 0 + q.getD 0 0, p.getD 1 0 + q.getD 1 0, p.getD 2 0 + q.getD 2 0, p.getD 3 0 + q.getD 3 0,
    p.getD 4 0 + q.getD 4 0, p.getD 5 0 + q.getD 5 0, p.getD 6 0 + q.getD 6 0, p.getD 7 0 + q.getD 7 0,
    p.getD 8 0 + q.getD 8 0]

/-- A polynomial of nine coefficients scaled. -/
def smul9 (s : E) (p : List E) : List E :=
  [s * p.getD 0 0, s * p.getD 1 0, s * p.getD 2 0, s * p.getD 3 0, s * p.getD 4 0, s * p.getD 5 0,
    s * p.getD 6 0, s * p.getD 7 0, s * p.getD 8 0]

/-- The zero polynomial, nine coefficients. -/
def zero9 : List E := [0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **A weight's and a stack's pair polynomial** over the `nq` quadruples: `Σ_i W_i(pairPoint X) C_i(pairPoint X)`. -/
def pairPolyOf (b : E) (nq : ℕ) (w c : Array E) : List E :=
  (List.range nq).foldl (fun acc i ↦ add9 acc (mul5 (quadCoeffs b w i) (quadCoeffs b c i))) zero9

/-- **The pair polynomial of the batch** (`prove_pairs`' `c`): `Σ_k λ^k` of each claim's pair polynomial. -/
def pairMsgOf (b lambda : E) (nq : ℕ) (weights tabs : List (Array E)) : List E :=
  ((weights.zip tabs).foldl (fun (acc : List E × E) wc ↦
    (add9 acc.1 (smul9 acc.2 (pairPolyOf b nq wc.1 wc.2)), acc.2 * lambda)) (zero9, 1)).1

/-- **A plain round's sums** over `nh` pairs: `Σ w₀ c₀` and `Σ (w₀ + w₁)(c₀ + c₁)` (`round_sums`, its count the
batch's). -/
def halfSums (nh : ℕ) (w c : Array E) : E × E :=
  (List.range nh).foldl (fun (acc : E × E) i ↦
    let w0 := w.getD (2 * i) 0
    let w1 := w.getD (2 * i + 1) 0
    let c0 := c.getD (2 * i) 0
    let c1 := c.getD (2 * i + 1) 0
    (acc.1 + w0 * c0, acc.2 + (w0 + w1) * (c0 + c1))) (0, 0)

/-- **A plain round's message** (`q(0)`, `q`'s `X²` coefficient), weighed by `λ^k`. -/
def plainMsgOf (lambda : E) (nh : ℕ) (weights tabs : List (Array E)) : E × E :=
  let t := (weights.zip tabs).foldl (fun (acc : E × E × E) wc ↦
    let s := halfSums nh wc.1 wc.2
    (acc.1 + acc.2.2 * s.1, acc.2.1 + acc.2.2 * s.2, acc.2.2 * lambda)) (0, 0, 1)
  (t.1, t.2.1)

/-- Every table folded at `x`. -/
def foldAt (st : BatchState) (x : E) : BatchState :=
  ⟨st.weights.map (foldE · x), st.tabs.map (foldE · x), none, 0, st.point ++ [x]⟩

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **A pair round** (`prove_pairs`' loop): the eight scalars of the pair polynomial, the narrow challenge `z`, every
table folded at `pairPoint z`'s two coordinates (`nq` quadruples left). -/
def pairRound3 (lambda : E) (nq : ℕ) (st : BatchState) : WrM m BatchState := do
  let cs := pairMsgOf cantorBeta1 lambda nq st.weights st.tabs
  sendScalars (msg8 cs)
  let z ← sampleNarrowW H
  let y := pairPoint z
  return foldAt (foldAt st (y.getD 0 0)) (y.getD 1 0)

/-- **The last plain round** (narrow): `q(0)`, `q`'s `X²` coefficient, the narrow challenge, the tables folded. -/
def plainRound3 (lambda : E) (nh : ℕ) (st : BatchState) : WrM m BatchState := do
  let msg := plainMsgOf lambda nh st.weights st.tabs
  sendScalar msg.1
  sendScalar msg.2
  let r ← sampleNarrowW H
  return foldAt st r

/-- **π1-rec3's batching sumcheck's rounds** (`sumcheck_pairs_drawn`'s prover): `vars / 2` pair rounds (pair `j` over
`2^(vars − 2j − 2)` quadruples), with `vars` odd a last plain round over one pair; the point. -/
def batchRounds3 (lambda : E) (vars : ℕ) (st : BatchState) : WrM m (List E) := do
  let mut st := st
  for j in List.range (vars / 2) do
    st ← pairRound3 H lambda (2 ^ (vars - 2 * j - 2)) st
  if vars % 2 = 1 then
    st ← plainRound3 H lambda 1 st
  return st.point

end With

/-! ## The stream and the proof -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **π1-rec3's stream** (`prove`, steps 0–9 at `FLOCK_REC3`), from the seed: the main line's `proveStreamWith` with
`α = squares c 4`, Flock's prover at π1-rec3, the paired batch, no matrices. -/
def proveStreamRec3With (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m) (tr : Trace) :
    WrM m CoreOut := do
  let shape := tr.shape
  -- 0. The six row counts.
  for rows in tr.rows do
    sendInteger rows 4
  -- 1. C1, then α = squares c 4, β, γ.
  let stack1 := c1Stack tr
  let committed1 ← (StateT.lift (commit .c1 (c1Layout shape).vars stack1) : WrM m Committed)
  sendRoot committed1.halves
  let alphas ← drawRunW H 4
  let beta ← sampleW H
  let gamma ← sampleW H
  -- 2. Flock (π1-rec3's: the zerocheck's squares, the walked terminal).
  let logN := blake2sR1csLogSize + shape.heights.getD opBlake2s 0
  let flockOut : Option FlockOut ← some <$> flock logN flockMain tr.qflock
  -- 3. The heap, the quotients, C2.
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 ← (StateT.lift (commit .c2 (((layoutsOf shape).lookup .c2).getD default).vars c2.stack) :
    WrM m Committed)
  sendRoot committed2.halves
  -- 4.–7. The values at t.
  let t ← sampleW H
  let a := atTOf tr c2 alphas beta gamma t flockOut
  sendScalars a.values
  -- 8. ρ, the combined claims.
  let rho ← sampleW H
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layouts shape a.c2Columns
  let stack3 := setupStackOf tr
  let stackOf : Commitment → Array K
    | .c1 => stack1
    | .c2 => c2.stack
    | .setup => stack3
  -- 9. The batching sumcheck, two variables a round, no pending matrices.
  let lambda ← sampleW H
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) a.ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩
  let r ← batchRounds3 H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let c ← get
  return ⟨c.stream, (stack1, committed1), (c2.stack, committed2), stack3, claims, none, combined, c2.heapVals⟩

/-- **π1-rec3's contract IV** with Keccak-256 `H` (`contract_iv_for` at `FLOCK_REC3`: the main line's preimage, then
`variantBytes (.flock flockMain) .rec3 true`). -/
def contractIvRec3Of (shape : UniStatement.Shape) (programIv : List UInt8) (roots : SetupRoots) : m (List UInt8) := do
  let d ← H (ivTag ++ programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes shape ++ (layoutWords shape).flatten ++
    variantBytes (.flock flockMain) .rec3 true)
  return digestBytes d

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π1-rec3's honest prover** over `H`, `F`: the setup's trees, π1-rec3's IV, the seed, the stream, then the three
WHIR openings (`C1`, `C2`, the setup); `none` if a proof of work fails. `A0`, `B0` are not opened. -/
def proveRec3With (fuel : ℕ) (flock : FlockProver m) (programIv : List UInt8) (tr : Trace) :
    m (Option UniProof) := do
  let trees ← setupTreesOf H tr
  let iv ← contractIvRec3Of H tr.shape programIv trees.roots
  let seed ← seedOf H iv tr.publicInput
  let (out, _) ← (proveStreamRec3With H (commitReal H) flock tr).run (Wr.start seed)
  let words := layoutWords tr.shape
  let openOne (c : Commitment) (pt : List E) (value : E) : m (Option Compile.Proof) :=
    let (stack, tree, word) : Array K × LeanVM.Prover.Tree × List UInt8 := match c with
      | .c1 => (out.c1.1, out.c1.2.tree, words.getD 0 [])
      | .c2 => (out.c2.1, out.c2.2.tree, words.getD 1 [])
      | .setup => (out.setup, trees.bytecode, words.getD 2 [])
    E2ECompleteness.proveOpeningWithH H F fuel (plainLayout (layoutWordVars word)) tree stack [⟨pt, value⟩]
  let p1 ← match out.claims.find? (·.1 == .c1) with
    | some (_, pt, v) => openOne .c1 pt v
    | none => pure none
  let p2 ← match out.claims.find? (·.1 == .c2) with
    | some (_, pt, v) => openOne .c2 pt v
    | none => pure none
  let p3 ← match out.claims.find? (·.1 == .setup) with
    | some (_, pt, v) => openOne .setup pt v
    | none => pure none
  return do
    let c1 ← p1
    let c2 ← p2
    let s ← p3
    pure ⟨out.stream, c1, c2, s, noProof, noProof⟩

/-- **π1-rec3's honest prover on a witness**: `proveRec3With` on the placed trace (`honestTrace`), `nonceFuel` nonces a
proof of work. -/
def uniProverRec3With (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : m (Option UniProof) :=
  proveRec3With H F PcsQuotient.nonceFuel flock D.programIv (honestTrace D input rows q)

end With

/-- **π1-rec3's honest prover in the random-permutation model**: `uniProverRec3With` over `π`, Keccak-256 the sponge
over `π`, Flock's prover at the same Keccak-256. -/
def uniProverRec3RP (flock : FlockProverH) (D : Deployment) : UniProver D :=
  uniProverRec3With (keccak256With Common.queryPermutation) Common.queryPermutation
    (flock (keccak256With Common.queryPermutation)) D

end UniComplete.Rec3
