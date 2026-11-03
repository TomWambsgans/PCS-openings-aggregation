-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `formal/UniStatement` (`Transcript.lean`, `Flock.lean`, `Batch.lean`, `Verifier.lean`, `Run.lean`,
-- `Opening.lean`, `Security.lean`), with Keccak-256 an explicit call, as `formal/EndToEnd/Completeness/
-- E2ECompleteness/WithHash.lean` rewrites `formal/Statement`; the openings and the commitments are WithHash's
-- (`openingWithH`, `commitWithH`, after leanerVM `mumbai` 6175f1a0's `runWithHash`, `buildTreeWithHash`, MIT OR
-- Apache-2.0).
import UniStatement.Security
import E2ECompleteness.WithHash

/-!
# The univariate verifier and setup with Keccak-256 an explicit call

`formal/UniStatement`'s verifier and setup are written over a permutation `F`, every Keccak-256 the sponge over
it (`keccak256With F`). Here each function that hashes is rewritten with Keccak-256 a separate function `H`
(`…H`), the code text the Statement's, only the hash changed:

* the transcript: `seedWithH`, `sampleH`, `samplesH`, `sumcheckH`;
* Flock: `Flock.zerocheckH`, `Flock.reduceTerminalH`, `Flock.frontH`, `Flock.ringEndH`, `Flock.verifyH`,
  `Flock.verifyDeferredH`;
* the batching sumcheck `batchH`, the walk `reduceWithH`, the run on calldata `runWithH`;
* the contract's IV `contractIvWithH`, `Deployment.ivWithH`; `PCS_OPEN` `pcsOpenWithH` (WithHash's
  `openingWithH`), the verifier `verifyWithH`, the deployed verifier `Deployment.verifierWithH`;
* the setup `setupTreesWithH` (WithHash's `commitWithH`).

**At `H = keccak256With F`** each is the Statement's (`…_eqH`): by `rfl` but where an opening or a commitment
is involved (WithHash's `openingWith_eqH`, `commitWith_eqH`). In particular
`Deployment.verifierWith F = Deployment.verifierWithH (keccak256With F) F` (`verifierWith_eqH`) and
`setupTreesWith F D = setupTreesWithH (keccak256With F) F D` (`setupTreesWith_eqH`).

Decisions:

* A function takes `H` alone where the Statement's used `F` only for Keccak-256 (the transcript, Flock, the
  batch, the walk, the run, the IV), and `H F` where it also runs the permutation (`pcsOpenWithH`,
  `verifyWithH`, `Deployment.verifierWithH`), as WithHash's `reduceWithH H`, `openingWithH H F`.
  `setupTreesWithH` takes `H F` as the end statements use it, its `F` unused: the setup only hashes.
* The non-hashing helpers (`nextScalar`, `nextScalars`, `nextRoot`, `nextInteger`, `takeBytes`, `requireZero`,
  `finish`, `roundPoly`, `tablePart`, `countBits`) are the Statement's own, at the same monad.
* Names in namespace `UniComplete` (Flock's in `UniComplete.Flock`); identifiers the Statement's files resolved
  by their own namespace are qualified where they would be ambiguous here (`Flock.Reduced`, `Flock.End`), which
  changes no term (the `_eqH` lemmas are `rfl`).
* Not a Lean `module`: E2ECompleteness is not one, and a module cannot import it.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

namespace UniComplete

/-! ## The transcript (`Transcript.lean`) -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `seedWith` with Keccak-256 `H`. -/
def seedWithH (iv publicInput : List UInt8) : m Digest := H (name ++ iv ++ publicInput)

/-- `sample` with Keccak-256 `H`. -/
def sampleH : ChanM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList
  let state ← (H input : m Digest)
  let x := PcsQuotient.Transcript.challengeOf state
  set { c with absorbed := c.cursor, state := state, challenges := c.challenges.push x }
  return x

/-- `samples` with Keccak-256 `H`. -/
def samplesH (count : ℕ) : ChanM m (List E) := do
  let mut out : Array E := #[]
  for _ in [0:count] do
    out := out.push (← sampleH H)
  return out.toList

/-- `sumcheck` with Keccak-256 `H`. -/
def sumcheckH (claim : E) (count : ℕ) (equalities : List (Option E)) : ChanM m (List E × E) := do
  let mut point : Array E := #[]
  let mut claim := claim
  for equality in equalities do
    let message ← roundPoly (m := m) count claim equality
    let challenge ← sampleH H
    point := point.push challenge
    claim := polyEval message challenge
  return (point.toList, claim)

end With

/-! ## Flock (`Flock.lean`) -/

namespace Flock

open UniStatement.Flock

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `Flock.zerocheck` with Keccak-256 `H`. -/
def zerocheckH (logN k : ℕ) : ChanM m (Option E × List E × E × E × E) := do
  let sampled ← samplesH H (logN - k - nFixed)
  let r : List (Option E) := (fixedChallenges ++ sampled).map some
  let (zSkip, claim) ← if k > 0 then do
      let coset ← nextScalars (m := m) (2 ^ k)
      let z ← sampleH H
      pure (some z, lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ coset) z)
    else pure (none, 0)
  let (chi, running) ← sumcheckH H claim 3 r
  let vA ← nextScalar (m := m)
  let vB ← nextScalar (m := m)
  return (zSkip, chi, vA, vB, running + vA * vB)

/-- `Flock.reduceTerminal` with Keccak-256 `H`. -/
def reduceTerminalH (zSkip : Option E) (rowLow chiIn chiInPrime : List E) (alpha rLc : E)
    (s : Option (List E)) : ChanM m (MatrixClaim × Option (List E × E)) := do
  let k := packing - rowLow.length
  let (skipWeights, lowWeights) := rowLowWeights zSkip rowLow
  let (cWeight, pinWeight) := knownWeights alpha chiIn chiInPrime
  let pin := constantColumn % kBits
  let known := s.map fun s ↦ cWeight * dot lowWeights s + pinWeight * s.getD pin 0
  let (challenges, running) ← sumcheckH H (rLc + known.getD 0) 3 (List.replicate (k + packing) none)
  let rho := challenges.take k
  let sigma := challenges.drop k
  let a ← nextScalar (m := m)
  let b ← nextScalar (m := m)
  let skipAtRho := if k > 0 then multilinearEval skipWeights rho else 1
  let factor := (a + alpha * b) * skipAtRho
  let matrices : MatrixClaim := ⟨rho ++ rowLow ++ chiIn ++ sigma ++ chiInPrime, a, b⟩
  match s with
  | some s =>
    requireZero (m := m) (factor * multilinearEval s sigma + running)
    return (matrices, none)
  | none =>
    let lambda := eprod challenges
    let lambdaC := lambda * cWeight
    let lambdaPin := lambda * pinWeight
    let weights := ((eqKernel sigma).toList.zip (lowWeights ++ List.replicate kBits 0)).map
      fun (e, low) ↦ factor * e + lambdaC * low
    let weights := weights.modify pin (· + lambdaPin)
    return (matrices, some (weights, running))

/-- `Flock.front` with Keccak-256 `H`. -/
def frontH (logN : ℕ) (variant : Variant) : ChanM m Front := do
  let k := variant.skip
  let (zSkip, chi, vA, vB, vC) ← zerocheckH H logN k
  let rowLow := chi.take (packing - k)
  let rest := chi.drop (packing - k)
  let chiIn := rest.take lincheckRounds
  let chiRest := rest.drop lincheckRounds
  let alpha ← sampleH H
  let claim := vA + alpha * vB + epow alpha 2 * vC + epow alpha 3
  let (roundChallenges, rLc) ← sumcheckH H claim 3 (List.replicate lincheckRounds none)
  let chiInPrime := roundChallenges.reverse
  let s ← if variant.slices = .claim then pure none else some <$> nextScalars (m := m) kBits
  return ⟨zSkip, chi, rowLow, chiIn, chiInPrime, alpha, rLc, s, chiInPrime ++ chiRest⟩

/-- `Flock.ringEnd` with Keccak-256 `H`. -/
def ringEndH (variant : Variant) (s : List E) : ChanM m Flock.End := do
  let map ← samplesH H ringMapShifts.length
  let target := if variant.slices = .tower then towerTarget s map
    else polyEval (s.map fun value ↦ ringMap value map) gen
  return .ring map target

/-- `Flock.verify` with Keccak-256 `H`. -/
def verifyH (logN : ℕ) (variant : Variant) : ChanM m Flock.Reduced := do
  let fr ← frontH H logN variant
  let (matrices, combination) ←
    reduceTerminalH H fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices
  match fr.slices, combination with
  | some s, _ => return ⟨fr.point, matrices, ← ringEndH H variant s⟩
  | none, some (weights, value) => return ⟨fr.point, matrices, .combination weights value⟩
  | none, none => return ⟨fr.point, matrices, .combination [] 0⟩

/-- `Flock.verifyDeferred` with Keccak-256 `H`. -/
def verifyDeferredH (logN : ℕ) (variant : Variant) : ChanM m (List E × Option Flock.End × Pending) := do
  let fr ← frontH H logN variant
  let pending := Pending.new fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices
  let end_ ← match fr.slices with
    | some s => some <$> ringEndH H variant s
    | none => pure none
  return (fr.point, end_, pending)

end With

end Flock

/-! ## The batching sumcheck (`Batch.lean`) and the walk (`Verifier.lean`) -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `batch` with Keccak-256 `H`. -/
def batchH (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E) := none)
    (pending : Option (Flock.Pending × List E) := none) :
    ChanM m (List (Commitment × Opening) × Option Flock.MatrixClaim) := do
  let lambda ← sampleH H
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, scale) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let target := match pending with
    | some (p, _) => target + scale * p.claim
    | none => target
  let (r, last) ← sumcheckH H target 3 (List.replicate vars none)
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
      -- Flock (a): the terminal leaves `Σ_i μ_i ẑ(i, p) = sum + last`, a bit-slice claim joining C1's call.
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

/-- `reduceWith` with Keccak-256 `H`. -/
def reduceWithH (shape : Shape) (publicWords : List E) (blake2s : Blake2s) (mode : ClaimsMode) :
    ChanM m Reduced := do
  if !shape.validate (blake2s != .omitted) then throw .invalidShape
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  -- 0. The tables' row counts (F1): six 32-bit integers, absorbed with C1's root.
  let counts ← countBits (m := m) heights
  -- 1. C1, then the bus's and the constraints' challenges.
  let root1 ← nextRoot (m := m)
  let alphas ← samplesH H 4
  let beta ← sampleH H
  let gamma ← sampleH H
  let weights := eqKernel alphas
  -- 2. Flock, on C1's q_flock; with the point-claim ABI, its matrices' reduction left pending (lever 4a).
  let logN := blake2sR1csLogSize + heights.getD opBlake2s 0
  let (flock, pending) : Option (List E × Option Flock.End × Option Flock.MatrixClaim) ×
      Option (Flock.Pending × List E) ← match blake2s, mode with
    | .flock variant, .point => do
      let (point, end_, left) ← Flock.verifyDeferredH H logN variant
      pure (some (point, end_, (none : Option Flock.MatrixClaim)), some (left, point))
    | .flock variant, .weighted => do
      let reduced ← Flock.verifyH H logN variant
      pure (some (reduced.point, some reduced.end_, some reduced.matrices), none)
    | .omitted, _ => pure (none, none)
  -- 3. C2, then the point; the active rows' vanishing polynomials from the counts' bits (F1b).
  let root2 ← nextRoot (m := m)
  let t ← sampleH H
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
        -- One term for the whole weight, evaluated at the batch's point (lever 1a).
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
  let rho ← sampleH H
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
      -- Without the point ABI, the bit-slice terms join C1's weighted claim, at a fresh power of ρ.
      let fresh := epow rho c1.relations
      let base := c1.points.length
      let merged : Combined := { c1 with
        points := c1.points ++ claim.points
        terms := c1.terms ++ claim.terms.map fun (column, p, twist, k) ↦ (column, p + base, twist, fresh * k)
        value := c1.value + fresh * claim.value }
      openings := (c, .weighted merged) :: rest
    | _, _ => pure ()
  | .point =>
    let (batched, deferred) ← batchH H combined stackLayouts bitSlice ringMap pending
    openings := batched
    if deferred.isSome then matrices := deferred
  return ⟨(root1, root2), openings, matrices, relations.size, stackVars, stackLayouts⟩

/-! ## The run (`Run.lean`) and the contract's IV (`Opening.lean`) -/

/-- `runWith` with Keccak-256 `H`. -/
def runWithH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) : m Outcome := do
  let seed ← seedWithH H iv publicInput
  let walk : ChanM m Reduced := do
    let r ← reduceWithH H shape (publicWordsOf publicInput) blake2s mode
    finish (m := m)
    return r
  let (result, chan) ← (walk.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

/-- `contractIvWith` with Keccak-256 `H`. -/
def contractIvWithH (s : Shape) (programIv : List UInt8) (roots : SetupRoots) : m (List UInt8) := do
  let d ← H (ivTag ++ programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes s ++ (layoutWords s).flatten)
  return digestBytes d

/-- `Deployment.ivWith` with Keccak-256 `H`. -/
def Deployment.ivWithH (D : Deployment) (roots : SetupRoots) : m (List UInt8) :=
  contractIvWithH H D.shape D.programIv roots

end With

/-! ## `PCS_OPEN`, the verifier and the setup (`Opening.lean`, `Security.lean`) -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- `pcsOpenWith` with Keccak-256 `H`: WithHash's `openingWithH` on the plain layout. -/
def pcsOpenWithH (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : LeanVM.Protocol.Compile.Proof) : m Bool :=
  E2ECompleteness.openingWithH H F (plainLayout vars) root claims proof

/-- `verifyWith` with Keccak-256 `H`. -/
def verifyWithH (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) : m Bool := do
  let o ← runWithH H shape iv publicInput.toList proof.stream (.flock flockMain) .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := layoutWords shape
    let callOf : Commitment → Digest × List UInt8 × LeanVM.Protocol.Compile.Proof
      | .c1 => (rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    -- C1, C2, the setup: one point claim each.
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← pcsOpenWithH H F (layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    -- Flock's matrices.
    match r.matrices with
    | some mc =>
      ok := ok && (← pcsOpenWithH H F (layoutWordVars (words.getD 3 [])) roots.a0 [⟨mc.point, mc.a⟩] proof.a0)
      ok := ok && (← pcsOpenWithH H F (layoutWordVars (words.getD 4 [])) roots.b0 [⟨mc.point, mc.b⟩] proof.b0)
    | none => ok := false
    return ok

/-- `Deployment.verifierWith` with Keccak-256 `H`. -/
def Deployment.verifierWithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) : m Bool := do
  verifyWithH H F D.shape (← Deployment.ivWithH H D roots) roots input proof

/-- `setupTreesWith` with Keccak-256 `H` (WithHash's `commitWithH`). The setup only hashes: `_F` is unused, there
for the two-call signature the end statements use. -/
def setupTreesWithH (_F : KeccakState → m KeccakState) (D : Deployment) : m SetupTrees := do
  let f ← E2ECompleteness.commitWithH H (setupLayout D.shape).vars (setupStack D.prog D.shape)
  let a ← E2ECompleteness.commitWithH H matrixVars (flockMatrixStack true)
  let b ← E2ECompleteness.commitWithH H matrixVars (flockMatrixStack false)
  return ⟨f, a, b⟩

end With

/-! ## At `H = keccak256With F` -/

section Eq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem seedWith_eqH (iv publicInput : List UInt8) :
    seedWith F iv publicInput = seedWithH (keccak256With F) iv publicInput := rfl

theorem sample_eqH : sample F = sampleH (keccak256With F) := rfl

theorem samples_eqH (count : ℕ) : samples F count = samplesH (keccak256With F) count := rfl

theorem sumcheck_eqH (claim : E) (count : ℕ) (equalities : List (Option E)) :
    sumcheck F claim count equalities = sumcheckH (keccak256With F) claim count equalities := rfl

theorem zerocheck_eqH (logN k : ℕ) :
    UniStatement.Flock.zerocheck F logN k = Flock.zerocheckH (keccak256With F) logN k := rfl

theorem reduceTerminal_eqH (zSkip : Option E) (rowLow chiIn chiInPrime : List E) (alpha rLc : E)
    (s : Option (List E)) :
    UniStatement.Flock.reduceTerminal F zSkip rowLow chiIn chiInPrime alpha rLc s =
      Flock.reduceTerminalH (keccak256With F) zSkip rowLow chiIn chiInPrime alpha rLc s := rfl

theorem front_eqH (logN : ℕ) (variant : UniStatement.Flock.Variant) :
    UniStatement.Flock.front F logN variant = Flock.frontH (keccak256With F) logN variant := rfl

theorem ringEnd_eqH (variant : UniStatement.Flock.Variant) (s : List E) :
    UniStatement.Flock.ringEnd F variant s = Flock.ringEndH (keccak256With F) variant s := rfl

theorem flockVerify_eqH (logN : ℕ) (variant : UniStatement.Flock.Variant) :
    UniStatement.Flock.verify F logN variant = Flock.verifyH (keccak256With F) logN variant := rfl

theorem verifyDeferred_eqH (logN : ℕ) (variant : UniStatement.Flock.Variant) :
    UniStatement.Flock.verifyDeferred F logN variant = Flock.verifyDeferredH (keccak256With F) logN variant :=
  rfl

theorem batch_eqH (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    batch F combined layouts bitSlice ringMap pending =
      batchH (keccak256With F) combined layouts bitSlice ringMap pending := rfl

/-- The walk at `H = keccak256With F`: its parts rewritten, the rest the same code (a plain `rfl` from the two
names times out in the elaborator, which unfolds them in a bad order). -/
theorem reduceWith_eqH (shape : Shape) (publicWords : List E) (blake2s : Blake2s) (mode : ClaimsMode) :
    reduceWith F shape publicWords blake2s mode = reduceWithH (keccak256With F) shape publicWords blake2s mode := by
  unfold reduceWith reduceWithH
  simp only [samples_eqH, sample_eqH, verifyDeferred_eqH, flockVerify_eqH, batch_eqH]
  rfl

theorem runWith_eqH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) :
    runWith F shape iv publicInput stream blake2s mode =
      runWithH (keccak256With F) shape iv publicInput stream blake2s mode := by
  unfold runWith runWithH
  simp only [seedWith_eqH, reduceWith_eqH]

theorem contractIvWith_eqH (s : Shape) (programIv : List UInt8) (roots : SetupRoots) :
    contractIvWith F s programIv roots = contractIvWithH (keccak256With F) s programIv roots := rfl

theorem ivWith_eqH (D : Deployment) (roots : SetupRoots) :
    D.ivWith F roots = Deployment.ivWithH (keccak256With F) D roots := rfl

theorem pcsOpenWith_eqH (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : LeanVM.Protocol.Compile.Proof) :
    pcsOpenWith F vars root claims proof = pcsOpenWithH (keccak256With F) F vars root claims proof :=
  E2ECompleteness.openingWith_eqH F _ _ _ _

theorem verifyWith_eqH (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) :
    verifyWith F shape iv roots publicInput proof =
      verifyWithH (keccak256With F) F shape iv roots publicInput proof := by
  unfold verifyWith verifyWithH
  simp only [runWith_eqH, pcsOpenWith_eqH]
  rfl

/-- **The deployed verifier at `H = keccak256With F`** is the Statement's. -/
theorem verifierWith_eqH :
    Deployment.verifierWith F = Deployment.verifierWithH (keccak256With F) F := by
  funext D roots input proof
  simp only [Deployment.verifierWith, Deployment.verifierWithH, ivWith_eqH, verifyWith_eqH]

/-- **The setup at `H = keccak256With F`** is the Statement's. -/
theorem setupTreesWith_eqH (D : Deployment) :
    setupTreesWith F D = setupTreesWithH (keccak256With F) F D := by
  simp only [setupTreesWith, setupTreesWithH, E2ECompleteness.commitWith_eqH]

end Eq

end UniComplete

/-- info: 'UniComplete.verifierWith_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.verifierWith_eqH

/-- info: 'UniComplete.setupTreesWith_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.setupTreesWith_eqH
