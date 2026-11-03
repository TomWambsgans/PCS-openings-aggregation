-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `formal/UniStatement/UniStatement/Rec.lean`
-- and `RecSecurity.lean` with Keccak-256 an explicit call, as `VerifierH.lean` does for the main line.
import UniComplete.VerifierH
import UniStatement.RecSecurity

/-!
# π1-rec3's verifier with Keccak-256 an explicit call

`Rec.lean`'s functions that hash, each rewritten with Keccak-256 a separate function `H` (`…H`), the code text
`Rec.lean`'s, only the hash changed (`VerifierH.lean`'s discipline): the narrow challenge `sampleNarrowH`, the draws
`sampleDrawnH`, `drawRunH`, the sumchecks `sumcheckDrawnH`, `sumcheckPairsDrawnH`; Flock's `zerocheckFsH`, `frontFsH`,
`verifyFsH`, `verifyDeferredFsH`, `verifyWalkedFsH`; the batch `batchFsH`; the walk `reduceWithFsH`, the run
`runWithFsH`; the IV `contractIvForWithH`, `Deployment.ivRec3WithH`; the verifier `verifyWithFsH`, the deployed one
`Deployment.verifierRec3WithH`.

**At `H = keccak256With F`** each is `Rec.lean`'s (`…_eqH`), by `rfl` but where an opening is involved
(`pcsOpenWith_eqH`): in particular `Deployment.verifierRec3With F = Deployment.verifierRec3WithH (keccak256With F) F`
(`verifierRec3With_eqH`).

Decisions: the non-hashing helpers (`pairRoundPoly`, `nextScalars`, `requireZero`, `tablePart`, `walkedTerminal`, …)
are `Rec.lean`'s and the Statement's own, at the same monad; the configurations other than π1-rec3's (`fs`, `walk`,
the modes) are kept, so that `reduceWithFsH` is `reduceWithFs`'s text and `_eqH` is a rewrite.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

namespace UniComplete.Rec3

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `sampleNarrow` with Keccak-256 `H`. -/
def sampleNarrowH : ChanM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList
  let state ← (H input : m Digest)
  let x := narrowE (PcsQuotient.Transcript.challengeOf state)
  set { c with absorbed := c.cursor, state := state, challenges := c.challenges.push x }
  return x

/-- `sampleDrawn` with Keccak-256 `H`. -/
def sampleDrawnH (narrow : Bool) : ChanM m E :=
  match narrow with
  | true => sampleNarrowH H
  | false => sampleH H

/-- `drawRun` with Keccak-256 `H`. -/
def drawRunH (fs : FsShape) (count : ℕ) : ChanM m (List E) :=
  match fs with
  | .main => samplesH H count
  | .rec1 | .rec2 | .rec3 =>
    if count = 0 then pure [] else do
      let c ← sampleH H
      pure (squares c count)

/-- `sumcheckDrawn` with Keccak-256 `H`. -/
def sumcheckDrawnH (claim : E) (count : ℕ) (equalities : List (Option E)) (narrow : Bool) :
    ChanM m (List E × E) := do
  let mut point : Array E := #[]
  let mut claim := claim
  for equality in equalities do
    let message ← roundPoly (m := m) count claim equality
    let challenge ← sampleDrawnH H narrow
    point := point.push challenge
    claim := polyEval message challenge
  return (point.toList, claim)

/-- `sumcheckPairsDrawn` with Keccak-256 `H`. -/
def sumcheckPairsDrawnH (claim : E) (degree vars : ℕ) (narrow : Bool) : ChanM m (List E × List E × E) := do
  let mut point : Array E := #[]
  let mut challenges : Array E := #[]
  let mut claim := claim
  for _ in [0:vars / 2] do
    let message ← pairRoundPoly (m := m) degree claim
    let z ← sampleDrawnH H narrow
    point := point ++ (pairPoint z).toArray
    challenges := challenges.push z
    claim := polyEval message z
  if vars % 2 = 1 then
    let (last, end_) ← sumcheckDrawnH H claim (degree + 1) [none] narrow
    challenges := challenges ++ last.toArray
    point := point ++ last.toArray
    claim := end_
  return (point.toList, challenges.toList, claim)

end With

/-! ## Flock at a Fiat–Shamir shape -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

open UniStatement.Flock

/-- `Flock.zerocheckFs` with Keccak-256 `H`. -/
def zerocheckFsH (logN k : ℕ) (fs : FsShape := .main) : ChanM m (Option E × List E × E × E × E) := do
  let sampled ← drawRunH H fs (logN - k - nFixed)
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

/-- `Flock.frontFs` with Keccak-256 `H`. -/
def frontFsH (logN : ℕ) (variant : Variant) (fs : FsShape := .main) : ChanM m Front := do
  let k := variant.skip
  let (zSkip, chi, vA, vB, vC) ← zerocheckFsH H logN k fs
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

/-- `Flock.verifyFs` with Keccak-256 `H`. -/
def verifyFsH (logN : ℕ) (variant : Variant) (fs : FsShape := .main) : ChanM m Flock.Reduced := do
  let fr ← frontFsH H logN variant fs
  let (matrices, combination) ←
    Flock.reduceTerminalH H fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices
  match fr.slices, combination with
  | some s, _ => return ⟨fr.point, matrices, ← Flock.ringEndH H variant s⟩
  | none, some (weights, value) => return ⟨fr.point, matrices, .combination weights value⟩
  | none, none => return ⟨fr.point, matrices, .combination [] 0⟩

/-- `Flock.verifyDeferredFs` with Keccak-256 `H`. -/
def verifyDeferredFsH (logN : ℕ) (variant : Variant) (fs : FsShape := .main) :
    ChanM m (List E × Option Flock.End × Pending) := do
  let fr ← frontFsH H logN variant fs
  let pending := Pending.new fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices
  let end_ ← match fr.slices with
    | some s => some <$> Flock.ringEndH H variant s
    | none => pure none
  return (fr.point, end_, pending)

/-- `Flock.verifyWalkedFs` with Keccak-256 `H`. -/
def verifyWalkedFsH (logN : ℕ) (variant : Variant) (fs : FsShape := .main) : ChanM m (List E × Flock.End) := do
  let fr ← frontFsH H logN variant fs
  let s := fr.slices.getD []
  let terminal := walkedTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime s fr.alpha
  requireZero (m := m) (terminal + fr.rLc)
  let end_ ← Flock.ringEndH H variant s
  return (fr.point, end_)

end With

/-! ## The batch and the walk at a Fiat–Shamir shape -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `batchFs` with Keccak-256 `H`. -/
def batchFsH (fs : FsShape) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
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
  let (r, last) ← match fs with
    | .rec3 => do
      let (r, _, last) ← sumcheckPairsDrawnH H target 2 vars true
      pure (r, last)
    | .main | .rec1 | .rec2 => sumcheckDrawnH H target 3 (List.replicate vars none) fs.narrow
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

/-- `reduceWithFs` with Keccak-256 `H`. -/
def reduceWithFsH (shape : UniStatement.Shape) (publicWords : List E) (blake2s : Blake2s) (mode : ClaimsMode)
    (fs : FsShape := .main) (walk : Bool := false) : ChanM m Reduced := do
  if !shape.validate (blake2s != .omitted) then throw .invalidShape
  let fs := match blake2s with
    | .flock _ => fs
    | .omitted => .main
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  let counts ← countBits (m := m) heights
  let root1 ← nextRoot (m := m)
  let alphas ← drawRunH H fs 4
  let beta ← sampleH H
  let gamma ← sampleH H
  let weights := eqKernel alphas
  let logN := blake2sR1csLogSize + heights.getD opBlake2s 0
  let (flock, pending) : Option (List E × Option Flock.End × Option Flock.MatrixClaim) ×
      Option (Flock.Pending × List E) ← match blake2s, mode, walk with
    | .flock variant, _, true => do
      let (point, end_) ← verifyWalkedFsH H logN variant fs
      pure (some (point, some end_, (none : Option Flock.MatrixClaim)), none)
    | .flock variant, .point, false => do
      let (point, end_, left) ← verifyDeferredFsH H logN variant fs
      pure (some (point, end_, (none : Option Flock.MatrixClaim)), some (left, point))
    | .flock variant, .weighted, false => do
      let reduced ← verifyFsH H logN variant fs
      pure (some (reduced.point, some reduced.end_, some reduced.matrices), none)
    | .omitted, _, _ => pure (none, none)
  let root2 ← nextRoot (m := m)
  let t ← sampleH H
  let w := digits t (max h (rW + 4) + 2)
  let active := (counts.zip heights).map fun (bits, r) ↦ activeVanishingFromBits w bits r
  let mut relations : Array Relation := #[]
  let mut parts : Array TablePart := #[]
  for table in tables do
    let (part, rels) ← tablePart (m := m) table (heights.getD table.opcode 0) weights beta w
    parts := parts.push part
    relations := relations ++ rels.toArray
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
  let lb := shape.logBytecode
  let bytecodeFinalCount ← nextScalar (m := m)
  let bytecodePull ← nextScalar (m := m)
  relations := relations.push (Relation.equal .bytecodeFinal (w.take lb) bytecodeFinalCount)
  relations := relations.push (Relation.equal .bytecodeTuple (alphas ++ w.take lb)
    (bytecodePull + beta + weights.getD 2 0 * bytecodeFinalCount))
  let bytecodePush := bytecodePull + weights.getD 2 0 * (1 + bytecodeFinalCount)
  let heapValue ← nextScalar (m := m)
  let constraintValue ← nextScalar (m := m)
  let (constraint, quotientDegree) :=
    constraintRelation shape parts.toList publicWords gamma t constraintValue w
  relations := relations.push constraint
  let constraintChunks := chunks (quotientDegree + 1)
  let c2Columns : List (Column × ℕ × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (constraintChunks.zip (List.range constraintChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  let (heapRels, leafColumns) := heapRelations shape active parts.toList weights beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush w constraintChunks
  relations := relations ++ heapRels.toArray
  let c2Columns := c2Columns ++ leafColumns
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
      let fresh := epow rho c1.relations
      let base := c1.points.length
      let merged : Combined := { c1 with
        points := c1.points ++ claim.points
        terms := c1.terms ++ claim.terms.map fun (column, p, twist, k) ↦ (column, p + base, twist, fresh * k)
        value := c1.value + fresh * claim.value }
      openings := (c, .weighted merged) :: rest
    | _, _ => pure ()
  | .point =>
    let (batched, deferred) ← batchFsH H fs combined stackLayouts bitSlice ringMap pending
    openings := batched
    if deferred.isSome then matrices := deferred
  return ⟨(root1, root2), openings, matrices, relations.size, stackVars, stackLayouts⟩

/-- `runWithFs` with Keccak-256 `H`. -/
def runWithFsH (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) (fs : FsShape := .main) (walk : Bool := false) : m Outcome := do
  let seed ← seedWithH H iv publicInput
  let walkM : ChanM m Reduced := do
    let r ← reduceWithFsH H shape (publicWordsOf publicInput) blake2s mode fs walk
    finish (m := m)
    return r
  let (result, chan) ← (walkM.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

/-- `contractIvForWith` with Keccak-256 `H`. -/
def contractIvForWithH (s : UniStatement.Shape) (blake2s : Blake2s) (fs : FsShape) (walk : Bool)
    (programIv : List UInt8) (roots : SetupRoots) : m (List UInt8) := do
  let extra := variantBytes blake2s fs walk
  if extra.isEmpty then contractIvWithH H s programIv roots else
  let d ← H (ivTag ++ programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes s ++ (layoutWords s).flatten ++ extra)
  return digestBytes d

/-- `Deployment.ivRec3With` with Keccak-256 `H`. -/
def Deployment.ivRec3WithH (D : Deployment) (roots : SetupRoots) : m (List UInt8) :=
  contractIvForWithH H D.shape (.flock flockMain) .rec3 true D.programIv roots

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- `verifyWithFs` with Keccak-256 `H`. -/
def verifyWithFsH (shape : UniStatement.Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) (fs : FsShape := .main) (walk : Bool := false) : m Bool := do
  let o ← runWithFsH H shape iv publicInput.toList proof.stream (.flock flockMain) .point fs walk
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := layoutWords shape
    let callOf : Commitment → Digest × List UInt8 × LeanVM.Protocol.Compile.Proof
      | .c1 => (rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← pcsOpenWithH H F (layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    match r.matrices, walk with
    | some mc, false =>
      ok := ok && (← pcsOpenWithH H F (layoutWordVars (words.getD 3 [])) roots.a0 [⟨mc.point, mc.a⟩] proof.a0)
      ok := ok && (← pcsOpenWithH H F (layoutWordVars (words.getD 4 [])) roots.b0 [⟨mc.point, mc.b⟩] proof.b0)
    | none, true => pure ()
    | _, _ => ok := false
    return ok

/-- **π1-rec3's deployed verifier** with Keccak-256 `H` (`Deployment.verifierRec3With`). -/
def Deployment.verifierRec3WithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) : m Bool := do
  verifyWithFsH H F D.shape (← Deployment.ivRec3WithH H D roots) roots input proof .rec3 true

end With

/-! ## At `H = keccak256With F` -/

section Eq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem sampleNarrow_eqH : sampleNarrow F = sampleNarrowH (keccak256With F) := rfl

theorem sampleDrawn_eqH (narrow : Bool) : sampleDrawn F narrow = sampleDrawnH (keccak256With F) narrow := rfl

theorem drawRun_eqH (fs : FsShape) (count : ℕ) : drawRun F fs count = drawRunH (keccak256With F) fs count := rfl

theorem sumcheckDrawn_eqH (claim : E) (count : ℕ) (equalities : List (Option E)) (narrow : Bool) :
    sumcheckDrawn F claim count equalities narrow = sumcheckDrawnH (keccak256With F) claim count equalities narrow :=
  rfl

theorem sumcheckPairsDrawn_eqH (claim : E) (degree vars : ℕ) (narrow : Bool) :
    sumcheckPairsDrawn F claim degree vars narrow = sumcheckPairsDrawnH (keccak256With F) claim degree vars narrow :=
  rfl

theorem zerocheckFs_eqH (logN k : ℕ) (fs : FsShape) :
    UniStatement.Flock.zerocheckFs F logN k fs = zerocheckFsH (keccak256With F) logN k fs := rfl

theorem frontFs_eqH (logN : ℕ) (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    UniStatement.Flock.frontFs F logN variant fs = frontFsH (keccak256With F) logN variant fs := rfl

theorem verifyFs_eqH (logN : ℕ) (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    UniStatement.Flock.verifyFs F logN variant fs = verifyFsH (keccak256With F) logN variant fs := rfl

theorem verifyDeferredFs_eqH (logN : ℕ) (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    UniStatement.Flock.verifyDeferredFs F logN variant fs = verifyDeferredFsH (keccak256With F) logN variant fs :=
  rfl

theorem verifyWalkedFs_eqH (logN : ℕ) (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    UniStatement.Flock.verifyWalkedFs F logN variant fs = verifyWalkedFsH (keccak256With F) logN variant fs := rfl

theorem batchFs_eqH (fs : FsShape) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (bitSlice : Option Combined) (ringMap : Option (List E))
    (pending : Option (Flock.Pending × List E)) :
    batchFs F fs combined layouts bitSlice ringMap pending =
      batchFsH (keccak256With F) fs combined layouts bitSlice ringMap pending := rfl

/-- The walk at `H = keccak256With F`: its parts rewritten, the rest the same code. -/
theorem reduceWithFs_eqH (shape : UniStatement.Shape) (publicWords : List E) (blake2s : Blake2s)
    (mode : ClaimsMode) (fs : FsShape) (walk : Bool) :
    reduceWithFs F shape publicWords blake2s mode fs walk =
      reduceWithFsH (keccak256With F) shape publicWords blake2s mode fs walk := by
  unfold reduceWithFs reduceWithFsH
  simp only [drawRun_eqH, sample_eqH, verifyWalkedFs_eqH, verifyDeferredFs_eqH, verifyFs_eqH, batchFs_eqH]
  rfl

theorem runWithFs_eqH (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (blake2s : Blake2s) (mode : ClaimsMode) (fs : FsShape) (walk : Bool) :
    runWithFs F shape iv publicInput stream blake2s mode fs walk =
      runWithFsH (keccak256With F) shape iv publicInput stream blake2s mode fs walk := by
  unfold runWithFs runWithFsH
  simp only [seedWith_eqH, reduceWithFs_eqH]

theorem contractIvForWith_eqH (s : UniStatement.Shape) (blake2s : Blake2s) (fs : FsShape) (walk : Bool)
    (programIv : List UInt8) (roots : SetupRoots) :
    contractIvForWith F s blake2s fs walk programIv roots =
      contractIvForWithH (keccak256With F) s blake2s fs walk programIv roots := rfl

theorem ivRec3With_eqH (D : Deployment) (roots : SetupRoots) :
    D.ivRec3With F roots = Deployment.ivRec3WithH (keccak256With F) D roots := rfl

theorem verifyWithFs_eqH (shape : UniStatement.Shape) (iv : List UInt8) (roots : SetupRoots)
    (publicInput : Vector UInt8 32) (proof : UniProof) (fs : FsShape) (walk : Bool) :
    verifyWithFs F shape iv roots publicInput proof fs walk =
      verifyWithFsH (keccak256With F) F shape iv roots publicInput proof fs walk := by
  unfold verifyWithFs verifyWithFsH
  simp only [runWithFs_eqH, pcsOpenWith_eqH]
  rfl

/-- **π1-rec3's deployed verifier at `H = keccak256With F`** is `RecSecurity.lean`'s. -/
theorem verifierRec3With_eqH :
    Deployment.verifierRec3With F = Deployment.verifierRec3WithH (keccak256With F) F := by
  funext D roots input proof
  simp only [Deployment.verifierRec3With, Deployment.verifierRec3WithH, ivRec3With_eqH, verifyWithFs_eqH]

end Eq

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.verifierRec3With_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.verifierRec3With_eqH
