-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `crates/leanvm_univariate/src/prover/prove.rs`
-- (branch `leanvm-univariate-prover2`): the prover phase by phase, its messages in the verifier's order
-- (`formal/UniStatement/UniStatement/Verifier.lean`'s `reduceWith`).
import UniComplete.Quotients
import UniComplete.Batch
import E2ECompleteness.WithHash

/-!
# The honest prover (`prove.rs`), on a placed trace

`proveStreamWith`, phase by phase, writing the stream `reduceWith` reads:

0. the six row counts (4-byte big-endian);
1. `C1` (every column in basis `B`, `z_T`, the memory, the bytecode's final counts, `q_flock` as values), committed,
   its root's halves; then `α ∈ E^4`, `β`, `γ`;
2. Flock (a prover given as a function, `FlockProver`: its messages, the ring map, what its matrices' reduction
   leaves to the batching sumcheck);
3. the heap's values, its novel and basis-`B` coefficients; the quotients (exact divisions); `C2`, committed, its
   root's halves; then `t`;
4. the values at `t`, in `reduceWith`'s order;
5. `ρ`; the relations exactly as `reduceWith` states them (its own `tablePart` run on the values each table sends,
   and its pure `constraintRelation`, `heapRelations`, `combine`); the combined claims;
6. `λ`, the batching sumcheck's rounds (`batchRounds`, the dense weights of the combined claims), the three stacks'
   values at its point, Flock's `a`, `b`.

`proveWith` adds the setup (the three trees, as the experiment's `setupTreesWith`, recomputed), the contract's IV,
the seed, and the five WHIR openings (`proveOpeningWithH`, the Statement's honest opening): `none` if a proof of
work fails. The commitments go through a function (`commit`), the real one `commitWithH`; the differential test
passes the review's stand-in roots.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A commitment: the tree the opening needs, and the root's halves the stream carries. -/
structure Committed where
  tree : LeanVM.Prover.Tree
  halves : E × E

/-- What Flock's prover leaves: `q_flock`'s point, its end on `q_flock` (the ring switch's map and target), what
the verifier's `verifyDeferred` returns as pending, and the matrices' product sum's tables for the batch. -/
structure FlockOut where
  point : List E
  end_ : Flock.End
  pending : Flock.Pending
  tables : PendingTables
  deriving Inhabited

/-- **Flock's prover** (`FlockProver`): at `log_n` variables and a variant, on `q_flock`'s words, its messages
written and its challenges drawn as `Flock.verifyDeferred` reads them. -/
abbrev FlockProver (m : Type → Type) : Type := ℕ → Flock.Variant → Array K → WrM m FlockOut

/-- Run a channel program that only reads, on given bytes: the verifier's own code on the values it reads. -/
def runReader {α : Type} [Inhabited α] (x : ChanM Id α) (bytes : List UInt8) : α :=
  match (x.run.run (Chan.start default bytes.toArray) : Id (Except UniError α × Chan)) with
  | (.ok a, _) => a
  | (.error _, _) => default

/-- **What table `t` sends at `t`** (`tablePart`'s reads): its sent columns' values, then each flush's pull
fingerprint when its tuple reads an unsent column, and its push fingerprint when their difference does. -/
def tableValues (table : Table) (at_ : ℕ → E) (weights : Array E) (beta : E) : List E := Id.run do
  let mut sent : Array (Option E) := Array.replicate table.width none
  let mut out : Array E := #[]
  for column in sentColumns table do
    sent := sent.set! column (some (at_ column))
    out := out.push (at_ column)
  for (pulled, pushed) in table.flushes.pull.zip table.flushes.push do
    if !(linearise pulled weights sent).2.isEmpty then
      out := out.push (fpE pulled weights beta at_)
    if !(linearise (difference pushed pulled) weights sent).2.isEmpty then
      out := out.push (fpE pushed weights beta at_)
  return out.toList

/-- The stream so far, and what the openings need. -/
structure CoreOut where
  stream : Array UInt8
  c1 : Array K × Committed
  c2 : Array K × Committed
  setup : Array K
  /-- One point claim per commitment, in the combined claims' order. -/
  claims : List (Commitment × List E × E)
  /-- Flock's claims on `A0`, `B0`. -/
  matrices : Option Flock.MatrixClaim
  /-- For the tests: the combined claims, the heap's values. -/
  combined : List (Commitment × Combined)
  heap : Array E

instance : Inhabited Committed := ⟨⟨⟨0, fun _ ↦ [], #[]⟩, (0, 0)⟩⟩

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **`C2`'s columns** after the bus's and the constraints' challenges (`prove`, steps 4–6): the heap's values, its
novel and basis-`B` coefficients; the tree quotient's, the constraint quotient's and every used block's leaf
quotient's chunks (in basis `B`); the stack. -/
structure C2Data where
  heapVals : Array E
  heapNovel : Array E
  heapB : Array E
  treeChunks : List (Array E)
  constraintSizes : List ℕ
  constraintChunks : List (Array E)
  leafChunks : List (ℕ × List ℕ × List (Array E))
  stack : Array K

/-- **`C2`** at `α` (through its `eq` weights), `β`, `γ`. -/
def c2DataOf (tr : Trace) (weights : Array E) (beta gamma : E) : C2Data :=
  let shape := tr.shape
  let heap := shape.heap
  let h := heap.h
  let heapVals := heapValues tr weights beta
  let heapNovel := novelOfValuesE h heapVals
  let heapB := bOfNovelE h heapNovel
  let treeChunks := chunksB (treeQuotient h heapNovel) [h, 0]
  let constraintSizes := chunks (shape.constraintDegree + 1)
  let constraintQ := chunksB (constraintQuotient tr gamma (publicWordsOf tr.publicInput)) constraintSizes
  let leafChunks : List (ℕ × List ℕ × List (Array E)) :=
    (heap.blocks.zip (List.range heap.blocks.length)).filterMap fun (block, index) ↦
      match Shape.leafDegree block, leafNumerator tr weights beta block
          (ofNovel block.r (novelOfValuesE block.r (blockLeaves tr weights beta block.leaves))) with
      | some d, some numerator =>
        let sizes := chunks (d + 1)
        some (index, sizes, chunksB (divM numerator (wPoly block.r)) sizes)
      | _, _ => none
  let c2Layout := ((layoutsOf shape).lookup .c2).getD default
  let c2Words : Column → ℕ → Array K := fun column limb ↦
    match column with
    | .heap => limbWords heapB limb
    | .treeQuotient c => limbWords (treeChunks.getD c #[]) limb
    | .constraintQuotient c => limbWords (constraintQ.getD c #[]) limb
    | .leafQuotient b c => match leafChunks.find? (·.1 == b) with
      | some (_, _, parts) => limbWords (parts.getD c #[]) limb
      | none => #[]
    | _ => #[]
  ⟨heapVals, heapNovel, heapB, treeChunks, constraintSizes, constraintQ, leafChunks, placeStack c2Layout c2Words⟩

/-- **What the prover sends at `t` and what the verifier states then** (`prove`, step 7; `reduceWith`, steps 4–7):
every value in the verifier's order (per table `tableValues`, then the memory's three, the bytecode's two, `T(t)`
and `Q_W(t)`), every relation (each table's by the verifier's own `tablePart` on the values it reads; the rest by
its pure `constraintRelation`, `heapRelations`; Flock's ring term), `C2`'s columns as the verifier lists them, the
ring map, the pending matrices with `q_flock`'s point. -/
structure AtT where
  values : List E
  relations : List Relation
  c2Columns : List (Column × ℕ × Bool)
  ringMap : Option (List E)
  pending : Option (Flock.Pending × List E)

/-- **The values and the relations at `t`**, from the trace, `C2`, the challenges and Flock's output. -/
def atTOf (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (flockOut : Option FlockOut) :
    AtT := Id.run do
  let shape := tr.shape
  let heights := shape.heights
  let h := shape.heap.h
  let rW := shape.constraintVars
  let lm := shape.logMemory
  let lb := shape.logBytecode
  let weights := eqKernel alphas
  let w := digits t (max h (rW + 4) + 2)
  let active := ((tr.rows.zip heights).map fun (rows, r) ↦
    activeVanishingFromBits w ((List.range (r + 1)).map fun b ↦ intBits rows b 1) r)
  let mut sent : Array E := #[]
  let mut relations : Array Relation := #[]
  let mut parts : Array TablePart := #[]
  for table in tables do
    let r := heights.getD table.opcode 0
    let at_ : ℕ → E := fun c ↦ evalB ((bCoefficients r (tr.column table.opcode c)).map ofK) r w
    let values := tableValues table at_ weights beta
    sent := sent ++ values.toArray
    let (part, rels) := runReader (tablePart (m := Id) table r weights beta w) (values.flatMap scalarWire)
    parts := parts.push part
    relations := relations ++ rels.toArray
  let memAt (k : ℕ) : E := evalB ((bCoefficients lm (tr.memory.getD k #[])).map ofK) lm w
  let memoryFinalCount := memAt 3
  let address := evalB ((bCoefficients lm (addressColumn lm)).map ofK) lm w
  let memoryPull := memoryFp weights beta address memoryFinalCount ((List.range 3).map memAt)
  sent := sent ++ #[memoryFinalCount, address, memoryPull]
  relations := relations.push (Relation.equal (.memory 3) (w.take lm) memoryFinalCount)
  relations := relations.push (Relation.equal .address (w.take lm) address)
  relations := relations.push ⟨(List.range 3).map (fun k ↦ term (.memory k) (w.take lm) (weights.getD (3 + k) 0)),
    memoryPull + beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * address +
      weights.getD 2 0 * memoryFinalCount⟩
  let memoryPush := memoryPull + weights.getD 2 0 * (1 + memoryFinalCount)
  let bytecodeFinalCount := evalB ((bCoefficients lb tr.bytecodeFinal).map ofK) lb w
  let slotAt (s : ℕ) : E := evalB ((bCoefficients lb (tr.slots.getD s #[])).map ofK) lb w
  let bytecodePull := bytecodeFp weights beta fun s ↦ if s = 2 then bytecodeFinalCount else slotAt s
  sent := sent ++ #[bytecodeFinalCount, bytecodePull]
  relations := relations.push (Relation.equal .bytecodeFinal (w.take lb) bytecodeFinalCount)
  relations := relations.push (Relation.equal .bytecodeTuple (alphas ++ w.take lb)
    (bytecodePull + beta + weights.getD 2 0 * bytecodeFinalCount))
  let bytecodePush := bytecodePull + weights.getD 2 0 * (1 + bytecodeFinalCount)
  let heapValue := evalB c2.heapB h w
  let constraintValue := ((c2.constraintChunks.zip c2.constraintSizes).foldl (fun (acc : E × E) (chunk, e) ↦
    (acc.1 + acc.2 * evalB chunk e w, acc.2 * w.getD e 0)) (0, 1)).1
  sent := sent ++ #[heapValue, constraintValue]
  -- The constraint quotient's identity; the heap's.
  let (constraint, quotientDegree) :=
    constraintRelation shape parts.toList (publicWordsOf tr.publicInput) gamma t constraintValue w
  relations := relations.push constraint
  let verifierChunks := chunks (quotientDegree + 1)
  let c2Columns : List (Column × ℕ × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (verifierChunks.zip (List.range verifierChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  let (heapRels, leafColumns) := heapRelations shape active parts.toList weights beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush w verifierChunks
  relations := relations ++ heapRels.toArray
  -- Flock's claim on q_flock: one term for the ring switch's weight (the main line).
  let mut ringMap : Option (List E) := none
  let mut pending : Option (Flock.Pending × List E) := none
  match flockOut with
  | some out =>
    match out.end_ with
    | .ring map target =>
      relations := relations.push ⟨[⟨.qflock, out.point, ringTwist, 1⟩], target⟩
      ringMap := some map
    | .combination _ _ => pure ()
    pending := some (out.pending, out.point)
  | none => pure ()
  return ⟨sent.toList, relations.toList, c2Columns ++ leafColumns, ringMap, pending⟩

/-- The stacks' layouts the verifier states (`layouts shape c2Columns`), and one of them. -/
def layoutIn (stackLayouts : List (Commitment × StackLayout)) (c : Commitment) : StackLayout :=
  ((stackLayouts.find? (·.1 == c)).map (·.2)).getD default

/-- **The prover's stream** (`prove`, steps 0–9), from the seed. -/
def proveStreamWith (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m)
    (blake2s : Blake2s) (tr : Trace) : WrM m CoreOut := do
  let shape := tr.shape
  -- 0. The six row counts.
  for rows in tr.rows do
    sendInteger rows 4
  -- 1. C1.
  let stack1 := c1Stack tr
  let committed1 ← (StateT.lift (commit .c1 (c1Layout shape).vars stack1) : WrM m Committed)
  sendRoot committed1.halves
  let alphas ← samplesW H 4
  let beta ← sampleW H
  let gamma ← sampleW H
  -- 2. Flock.
  let logN := blake2sR1csLogSize + shape.heights.getD opBlake2s 0
  let flockOut : Option FlockOut ← match blake2s with
    | .flock variant => some <$> flock logN variant tr.qflock
    | .omitted => pure none
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
  -- 9. The batching sumcheck.
  let lambda ← sampleW H
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) a.ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), flockOut.map (·.tables), 0, []⟩
  let r ← batchRounds H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let matrices ← match a.pending with
    | some (p, _) => do
      let mc := p.matrixClaim r 0 0
      let ma := multilinearEval ((flockMatrixStack true).toList.map ofK) mc.point
      let mb := multilinearEval ((flockMatrixStack false).toList.map ofK) mc.point
      sendScalars [ma, mb]
      pure (some (p.matrixClaim r ma mb))
    | none => pure none
  let c ← get
  return ⟨c.stream, (stack1, committed1), (c2.stack, committed2), stack3, claims, matrices, combined,
    c2.heapVals⟩

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- The real commitment: the WHIR tree of the stack (`commitWithH`), its root's halves. -/
def commitReal (_ : Commitment) (vars : ℕ) (stack : Array K) : m Committed := do
  let tree ← E2ECompleteness.commitWithH H vars stack
  return ⟨tree, digestScalars tree.root⟩

/-- The setup's trees, as the experiment computes them (`setupTreesWith`), from the trace's setup stack. -/
def setupTreesOf (tr : Trace) : m SetupTrees := do
  let f ← E2ECompleteness.commitWithH H (setupLayout tr.shape).vars (setupStackOf tr)
  let a ← E2ECompleteness.commitWithH H matrixVars (flockMatrixStack true)
  let b ← E2ECompleteness.commitWithH H matrixVars (flockMatrixStack false)
  return ⟨f, a, b⟩

/-- The seed of the contract's IV (`keccak(name ‖ IV ‖ public input)`). -/
def seedOf (iv publicInput : List UInt8) : m Digest := H (name ++ iv ++ publicInput)

/-- The contract's IV with Keccak-256 `H` (`contract_iv`). -/
def contractIvOf (shape : Shape) (programIv : List UInt8) (roots : SetupRoots) : m (List UInt8) := do
  let d ← H (ivTag ++ programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes shape ++ (layoutWords shape).flatten)
  return digestBytes d

/-- The empty opening proof (no call). -/
def noProof : Compile.Proof := ⟨[], []⟩

/-- **The honest prover** over `H`, `F` (`prove`): the setup's trees, the contract's IV, the seed, the stream, then
the five WHIR openings (`C1`, `C2`, the setup, `A0`, `B0`); `none` if a proof of work fails. -/
def proveWith (fuel : ℕ) (flock : FlockProver m) (blake2s : Blake2s) (programIv : List UInt8) (tr : Trace) :
    m (Option UniProof) := do
  let trees ← setupTreesOf H tr
  let iv ← contractIvOf H tr.shape programIv trees.roots
  let seed ← seedOf H iv tr.publicInput
  let (out, _) ← (proveStreamWith H (commitReal H) flock blake2s tr).run (Wr.start seed)
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
  let (pa, pb) ← match out.matrices with
    | some mc => do
      let pa ← E2ECompleteness.proveOpeningWithH H F fuel (plainLayout (layoutWordVars (words.getD 3 [])))
        trees.a0 (flockMatrixStack true) [⟨mc.point, mc.a⟩]
      let pb ← E2ECompleteness.proveOpeningWithH H F fuel (plainLayout (layoutWordVars (words.getD 4 [])))
        trees.b0 (flockMatrixStack false) [⟨mc.point, mc.b⟩]
      pure (pa, pb)
    | none => pure (some noProof, some noProof)
  return do
    let c1 ← p1
    let c2 ← p2
    let s ← p3
    let a ← pa
    let b ← pb
    pure ⟨out.stream, c1, c2, s, a, b⟩

end With

end UniComplete
