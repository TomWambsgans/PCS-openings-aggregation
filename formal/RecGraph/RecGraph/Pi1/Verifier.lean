-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed, in the Rust's operation order, from
-- `crates/leanvm_univariate/src/verifier.rs` (`reduce`, `linearise`, `table_part`, `quotient_terms`, `weight_at`,
-- `batch`), `claims.rs` (`Relations::{push, equal, combine}`), `stacks.rs` (`EqCache`, `limb_basis`) and
-- `contract.rs` (`record_verifier`, `calls`), at `leanvm-rec` 4247e37.
import RecGraph.Pi1.Flock

/-!
# π1-rec3's verifier as a program

`reduce` at the reference shape with `Blake2s::Flock(FLOCK_REC3)` and `Claims::Point`, on the recorder: `pi1Rec3`.
Its terms and relations carry node indices (`TermS`, `RelationS`, `CombinedS`), and `combine` compares points as
the recorder does, by their nodes. `weightAt` is the Rust's (`EqCache`, a column's limbs summed into its part, the
terms grouped by row, `q_flock`'s slots by point); its caches are left out, since an operation done twice is the
node already recorded (hash-consing), so the graph is the same. `pi1Graph` is the recorded graph with its calls'
words (`calls`).
-/

namespace RecGraph.Pi1

open LeanVM.Parameters UniStatement UniStatement.Flock

/-- A term (`claims::Term` on the recorder). -/
structure TermS where
  column : Column
  point : List Sym
  twist : Nat
  coefficient : Sym

/-- A relation `Σ terms = value`. -/
structure RelationS where
  terms : List TermS
  value : Sym

def RelationS.commitment (r : RelationS) : Commitment :=
  match r.terms with
  | t :: _ => t.column.commitment
  | [] => .c1

/-- A combined claim: points, terms (column, point, twist, coefficient), value, relations. -/
structure CombinedS where
  points : List (List Sym)
  terms : List (Column × Nat × Nat × Sym)
  value : Sym
  relations : Nat

/-- `term(column, point, coefficient)`. -/
def termS (column : Column) (point : List Sym) (coefficient : Sym) : TermS := ⟨column, point, 0, coefficient⟩

/-- **`Relations::equal(column, point, value)`**: one term, coefficient `S::one()`. -/
def equalS (column : Column) (point : List Sym) (value : Sym) : Prog RelationS := do
  let o ← one
  return ⟨[termS column point o], value⟩

/-- `linearise`'s `add`: add to the column's coefficient, or append it. -/
def addTermS (terms : Array (Nat × Sym)) (column : Nat) (c : Sym) : Prog (Array (Nat × Sym)) := do
  match terms.findIdx? (·.1 == column) with
  | some i => return terms.set! i (column, ← add (terms.getD i (0, 0)).2 c)
  | none => return terms.push (column, c)

/-- **`linearise(tuple, weights, sent)`**. -/
def linearise (tuple : List Form) (weights : Array Sym) (sent : Array (Option Sym)) :
    Prog (Sym × List (Nat × Sym)) := do
  let mut known ← zero
  let mut terms : Array (Nat × Sym) := #[]
  for (form, s) in tuple.zip (List.range tuple.length) do
    if s < weights.size then
      let weight := weights.getD s 0
      for (monomial, coefficient) in form do
        if coefficient = 0 then continue
        let cc ← const coefficient
        let c ← mul weight cc
        match monomial with
        | [] => known ← add known c
        | [i] =>
          match sent.getD i none with
          | some v =>
            let cv ← mul c v
            known ← add known cv
          | none => terms ← addTermS terms i c
        | [i, j] =>
          match sent.getD i none, sent.getD j none with
          | some a, some b =>
            let ca ← mul c a
            let cab ← mul ca b
            known ← add known cab
          | some a, none =>
            let ca ← mul c a
            terms ← addTermS terms j ca
          | none, some b =>
            let cb ← mul c b
            terms ← addTermS terms i cb
          | none, none => pure ()
        | _ => pure ()
  return (known, terms.toList)

/-- One table's part (`TablePart`). -/
structure TablePartS where
  pull : Sym
  push : Sym
  pullDegree : Nat
  pushDegree : Nat
  sent : Array (Option Sym)

/-- **`table_part(table, log_height, weights, β, point)`**: the sent values and their relations, then the flushes'
fingerprints; the relations it states, in order. -/
def tablePart (t : Table) (logHeight : Nat) (weights : Array Sym) (beta : Sym) (point : List Sym) :
    Prog (TablePartS × List RelationS) := do
  let at_ (c : Nat) : Column := .table t.opcode c
  let pt := point.take logHeight
  let mut sent : Array (Option Sym) := Array.replicate t.width none
  let mut relations : Array RelationS := #[]
  for column in sentColumns t do
    let value ← nextScalar
    sent := sent.set! column (some value)
    relations := relations.push (← equalS (at_ column) pt value)
  let mut pull ← one
  let mut push ← one
  let mut pullDegree := 1
  let mut pushDegree := 0
  for (pulled, pushed) in t.flushes.pull.zip t.flushes.push do
    let (known, terms) ← linearise pulled weights sent
    let mut dPull := 0
    if terms.isEmpty then
      dPull ← add beta known
    else
      let value ← nextScalar
      let vb ← add value beta
      let vbk ← add vb known
      relations := relations.push ⟨terms.map (fun (c, k) ↦ termS (at_ c) pt k), vbk⟩
      dPull := value
    let (knownDifference, differenceTerms) ← linearise (difference pushed pulled) weights sent
    let mut dPush := 0
    if differenceTerms.isEmpty then
      dPush ← add dPull knownDifference
    else
      let (knownPush, termsPush) ← linearise pushed weights sent
      let value ← nextScalar
      let vb ← add value beta
      let vbk ← add vb knownPush
      relations := relations.push ⟨termsPush.map (fun (c, k) ↦ termS (at_ c) pt k), vbk⟩
      dPush := value
    pull ← mul pull dPull
    push ← mul push dPush
    pullDegree := pullDegree + tupleDegree pulled
    pushDegree := pushDegree + tupleDegree pushed
  return (⟨pull, push, pullDegree, pushDegree, sent⟩, relations.toList)

/-- **`quotient_terms(column, sizes, w, scale)`**. -/
def quotientTerms (column : Nat → Column) (sizes : List Nat) (w : List Sym) (scale : Sym) : Prog (List TermS) := do
  let mut factor := scale
  let mut out : Array TermS := #[]
  for (e, chunk) in sizes.zip (List.range sizes.length) do
    out := out.push (termS (column chunk) (w.take e) factor)
    factor ← mul factor (w.getD e 0)
  return out.toList

/-- The longest point having point `p` as a prefix (itself included), the first among equals. -/
def longestOfS (points : Array (List Sym)) (p : Nat) : Nat :=
  let pp := points.getD p []
  (List.range points.size).foldl (fun best q ↦
    let pq := points.getD q []
    if pq.length ≥ pp.length ∧ pq.take pp.length == pp ∧ pq.length > (points.getD best []).length then q
    else best) p

/-- Add `coefficient` to the term `(column, p, twist)`, or append it. -/
def mergeTermS (terms : Array (Column × Nat × Nat × Sym)) (column : Column) (p twist : Nat) (coefficient : Sym) :
    Prog (Array (Column × Nat × Nat × Sym)) := do
  match terms.findIdx? (fun (c, q, k, _) ↦ c == column && q == p && k == twist) with
  | some i =>
    let (c, q, k, v) := terms.getD i (column, p, twist, 0)
    return terms.set! i (c, q, k, ← add v coefficient)
  | none => return terms.push (column, p, twist, coefficient)

/-- **`Relations::combine(commitment, ρ)`**, its points compared by their nodes. -/
def combine (relations : List RelationS) (commitment : Commitment) (rho : Sym) : Prog (Option CombinedS) := do
  let mine := relations.filter (·.commitment == commitment)
  if mine.isEmpty then return none
  let mut points : Array (List Sym) := #[]
  let mut terms : Array (Column × Nat × Nat × Sym) := #[]
  let mut value ← zero
  let mut scale ← one
  for relation in mine do
    let sv ← mul scale relation.value
    value ← add value sv
    for t in relation.terms do
      let p := (points.findIdx? (· == t.point)).getD points.size
      if p = points.size then
        points := points.push t.point
      let coefficient ← mul scale t.coefficient
      terms ← mergeTermS terms t.column p t.twist coefficient
    scale ← mul scale rho
  let longest := (List.range points.size).map (longestOfS points)
  let kept := (List.range points.size).filter fun p ↦ longest.getD p p == p
  let renumber (p : Nat) : Nat := kept.idxOf (longest.getD p p)
  let mut merged : Array (Column × Nat × Nat × Sym) := #[]
  for (column, p, twist, coefficient) in terms do
    merged ← mergeTermS merged column (renumber p) twist coefficient
  return some ⟨kept.map (points.getD · []), merged.toList, value, mine.length⟩

/-! ### The batch's weights (`weight_at`, `EqCache`) -/

/-- **`EqCache::selector(from, offset)`**: `Π_(k ≥ from) eq(bit_k(offset), r_k)`, from the top down. -/
def selectorS (r : List Sym) : Nat → Nat → Nat → Prog Sym
  | 0, _, _ => one
  | fuel + 1, fromVar, offset =>
    if fromVar ≥ r.length then one else do
      let rest ← selectorS r fuel (fromVar + 1) offset
      let rf := r.getD fromVar 0
      let factor ← if offset.testBit fromVar then pure rf else do add (← one) rf
      mul factor rest

/-- A column's part: `Σ_limbs basis[limb] · selector(vars, offset)`, and its variables. -/
def partS (r : List Sym) (basis : List Sym) (layout : StackLayout) (column : Column) : Prog (Nat × Sym) := do
  let limbs := layout.limbs column
  let vars := (limbs.headD (0, 0, 0)).2.1
  let mut sum ← zero
  for (limb, _, offset) in limbs do
    let selector ← selectorS r (r.length + 1) vars offset
    let term ← if limb = 0 then pure selector else mul (basis.getD limb 0) selector
    sum ← add sum term
  return (vars, sum)

/-- **`weight_at(claim, layout, r, ring_map)`** (the Rust's, `EqCache`'s caches left out). -/
def weightAt (claim : CombinedS) (layout : StackLayout) (r : List Sym) (ringMap : Option (List Sym)) :
    Prog Sym := do
  let mut onePlusR : Array Sym := #[]
  for x in r do
    let o ← one
    onePlusR := onePlusR.push (← add o x)
  let b0 ← const (eNew 1 0 0)
  let b1 ← const (eNew 0 1 0)
  let b2 ← const (eNew 0 0 1)
  let basis := [b0, b1, b2]
  let mut rows : Array ((Nat × Nat × Nat) × Sym) := #[]
  let mut slots : Array (Nat × Sym) := #[]
  for (column, p, twist, coefficient) in claim.terms do
    match column with
    | .qflockSlot j =>
      let mut acc ← one
      for b in [0:8] do
        acc ← mul acc (if j.testBit b then r.getD b 0 else onePlusR.getD b 0)
      let c ← mul coefficient acc
      match slots.findIdx? (·.1 == p) with
      | some i => slots := slots.set! i (p, ← add (slots.getD i (0, 0)).2 c)
      | none => slots := slots.push (p, c)
    | _ =>
      let (vars, sum) ← partS r basis layout column
      let c ← mul coefficient sum
      match rows.findIdx? (·.1 == (p, vars, twist)) with
      | some i => rows := rows.set! i ((p, vars, twist), ← add (rows.getD i ((0, 0, 0), 0)).2 c)
      | none => rows := rows.push ((p, vars, twist), c)
  let mut total ← zero
  for ((p, len, twist), sum) in rows do
    let point := claim.points.getD p []
    let row ← if twist = ringTwist then
        ringWeight (point.take len) (onePlusR.toList.take len) (ringMap.getD [])
      else do
        let mut product ← one
        for k in [0:len] do
          let s ← add (onePlusR.getD k 0) (point.getD k 0)
          product ← mul product s
        pure product
    let rs ← mul row sum
    total ← add total rs
  for (p, sum) in slots do
    let point := claim.points.getD p []
    let (_, qflock) ← partS r basis layout .qflock
    let mut inst ← one
    for (x, a) in point.zip (onePlusR.toList.drop 8) do
      let s ← add a x
      inst ← mul inst s
    let si ← mul sum inst
    let siq ← mul si qflock
    total ← add total siq
  return total

/-- **`batch`** at π1-rec3 (`FsShape::Rec3`: paired and narrow rounds; no pending matrices, no bit-slice claim): the
point claims, in `combined`'s order (commitment, point, value). -/
def batch (combined : List (Commitment × CombinedS)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List Sym)) : Prog (List (Commitment × List Sym × Sym)) := do
  let lambda ← sample
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let mut target ← zero
  let mut scale ← one
  for (_, claim) in combined do
    let sv ← mul scale claim.value
    target ← add target sv
    scale ← mul scale lambda
  let (r, _, last) ← sumcheckPairsDrawn target 2 vars true
  let values ← nextScalars combined.length
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  let mut sum ← zero
  let mut scale2 ← one
  let mut openings : Array (Commitment × List Sym × Sym) := #[]
  for ((commitment, claim), value) in combined.zip values do
    let layout := layoutOf commitment
    let weight ← weightAt claim layout r ringMap
    let mut extension ← one
    for j in [layout.vars:vars] do
      let o ← one
      let s ← add o (r.getD j 0)
      extension ← mul extension s
    let sw ← mul scale2 weight
    let swe ← mul sw extension
    let swev ← mul swe value
    sum ← add sum swev
    scale2 ← mul scale2 lambda
    openings := openings.push (commitment, r.take layout.vars, value)
  requireZero (← add sum last)
  return openings.toList

/-! ### `reduce` -/

/-- What π1-rec3's verifier leaves: the roots' halves, the point claims (commitment, point, value). -/
structure ReducedS where
  root1 : Sym × Sym
  root2 : Sym × Sym
  openings : List (Commitment × List Sym × Sym)

/-- **The row counts** (step 0): each count's range required zero, its bits `0..=r`. -/
def countBits (heights : List Nat) : Prog (List (List Sym)) := do
  let mut out : Array (List Sym) := #[]
  for r in heights do
    let count ← nextInteger 4
    requireZero (← bits count (r + 1) 32)
    let hi ← bits count r 1
    let lo ← bits count 0 r
    requireZero (← mul hi lo)
    let mut bs : Array Sym := #[]
    for b in [0:r + 1] do
      bs := bs.push (← bits count b 1)
    out := out.push bs.toList
  return out.toList

/-- **The constraint quotient's identity** (step 5). -/
def constraintRelation (shape : Shape) (parts : List TablePartS) (publicWords : List Sym) (gamma t constraintValue : Sym)
    (w : List Sym) : Prog RelationS := do
  let heights := shape.heights
  let rW := shape.constraintVars
  let mut known ← zero
  let mut terms : Array TermS := #[]
  let mut power ← one
  let o ← one
  for (table, part) in tables.zip parts do
    let r := heights.getD table.opcode 0
    let lift ← vanishingRatio w r rW
    let at_ (c : Nat) : Column := .table table.opcode c
    if table.opcode = opJump then
      let cond := (part.sent.getD (colIdx table.columns "v_cond") none).getD 0
      let flag := (part.sent.getD (colIdx table.columns "b") none).getD 0
      let cur1 := power
      power ← mul power gamma
      let g1 ← mul cur1 lift
      known ← add known (← mul g1 flag)
      terms := terms.push (termS (at_ (colIdx table.columns "w")) (w.take r) (← mul g1 cond))
      let cur2 := power
      power ← mul power gamma
      let g2 ← mul cur2 lift
      let g2c ← mul g2 cond
      let f1 ← add flag o
      known ← add known (← mul g2c f1)
    let mut counters := o
    for column in table.countColumns do
      counters ← mul counters ((part.sent.getD column none).getD 0)
    let cur := power
    power ← mul power gamma
    let g ← mul cur lift
    terms := terms.push (termS (.inverse table.opcode) (w.take r) (← mul g counters))
    known ← add known g
    if table.opcode = opBlake2s then
      let y ← coordinatesAt t (coordinateFunctionals r)
      for (name, column) in table.columns.zip (List.range table.width) do
        if let some slot := qflockSlot name then
          let cur := power
          power ← mul power gamma
          let g ← mul cur lift
          terms := terms.push (termS (at_ column) (w.take r) g)
          terms := terms.push (termS (.qflockSlot slot) y g)
  let lm := shape.logMemory
  let z1 ← zero
  let z2 ← zero
  let lines : List (Sym × Sym) :=
    [(publicWords.getD 0 0, publicWords.getD 2 0), (publicWords.getD 1 0, publicWords.getD 3 0), (z1, z2)]
  let lift ← vanishingRatio w 1 rW
  for ((low, high), k) in lines.zip (List.range 3) do
    let cur := power
    power ← mul power gamma
    let g ← mul cur lift
    terms := terms.push (termS (.memory k) (w.take lm) g)
    let lh ← add low high
    let tlh ← mul t lh
    let l2 ← add low tlh
    known ← add known (← mul g l2)
  let cw ← mul constraintValue (w.getD rW 0)
  return ⟨terms.toList, ← add cw known⟩

/-- **The heap's relations** (step 6) and the leaf quotients' columns. -/
def heapRelations (shape : Shape) (active : List Sym) (parts : List TablePartS) (weights : Array Sym)
    (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : Sym) (w : List Sym)
    (constraintChunks : List Nat) : Prog (List RelationS × List (Column × Nat × Bool)) := do
  let heap := shape.heap
  let h := heap.h
  let lb := shape.logBytecode
  let o ← one
  let atT := w.take h
  let mut relations : Array RelationS := #[← equalS .heap atT heapValue]
  let mut columns : Array (Column × Nat × Bool) := #[]
  let atS := (w.drop 1).take h
  let n0 ← add (atT.getD 0 0) o
  let atNext := atT.set 0 n0
  let w1 := w.getD 1 0
  let wh := w.getD h 0
  let w1v ← mul w1 heapValue
  let whh ← mul wh wh
  let z ← zero
  relations := relations.push ⟨[termS .heap atS w1, termS .heap atNext w1v, termS (.treeQuotient 0) atT wh,
    termS (.treeQuotient 1) [] whh], z⟩
  let mut atOne : Array Sym := #[]
  for l in [0:h] do
    atOne := atOne.push (← if l = 0 then pure o else zero)
  let c1 ← const sepState
  let w0s ← mul (weights.getD 0 0) c1
  let i1 ← add beta w0s
  let i2 ← add i1 (weights.getD 1 0)
  let init ← add i2 (weights.getD 2 0)
  let last ← const (gpow (2 ^ lb - 1))
  let c2 ← const sepState
  let w0s' ← mul (weights.getD 0 0) c2
  let f1 ← add beta w0s'
  let w1l ← mul (weights.getD 1 0) last
  let f2 ← add f1 w1l
  let fin ← add f2 (weights.getD 2 0)
  relations := relations.push ⟨[termS .heap atOne.toList init], fin⟩
  for (block, index) in heap.blocks.zip (List.range heap.blocks.length) do
    let mut mixed : Array Sym := #[]
    for l in [0:h] do
      let constant ← const (pointE (block.position >>> l))
      mixed := mixed.push (← if l < block.r then add (w.getD l 0) constant else pure constant)
    let n := 2 ^ block.r
    let wr := w.getD block.r 0
    match block.leaves with
    | .unused =>
      relations := relations.push ⟨[termS .heap mixed.toList o], o⟩
    | leaves =>
      let (pull, push, d, scale) ← match leaves with
        | .memory => pure (memoryPull, memoryPush, degree (2 * (n - 1)) n, wr)
        | .bytecode => pure (bytecodePull, bytecodePush, degree (2 * (n - 1)) n, wr)
        | .table t => do
          let part := parts.getD t ⟨0, 0, 0, 0, #[]⟩
          let zz := active.getD t 0
          let square ← mul zz zz
          let rows := Shape.leastRows block.r
          let d := degree (max part.pullDegree part.pushDegree * (n - 1) + (n - rows)) n
          let pw ← mul part.pull wr
          let pl ← add pw square
          let qw ← mul part.push wr
          let ps ← add qw square
          let sc ← mul wr zz
          pure (pl, ps, d, sc)
        | .unused => pure (0, 0, 0, 0)
      let sizes := chunks (d + 1)
      columns := columns ++ (sizes.zip (List.range sizes.length)).toArray.map fun (e, chunk) ↦
        (Column.leafQuotient index chunk, e, true)
      let qt ← quotientTerms (Column.leafQuotient index) sizes w scale
      relations := relations.push ⟨[termS .heap mixed.toList pull] ++ qt, push⟩
  let qt ← quotientTerms .constraintQuotient constraintChunks w o
  relations := relations.push ⟨qt, constraintValue⟩
  return (relations.toList, columns.toList)

/-- **π1-rec3's verifier** (`reduce` with `FLOCK_REC3`, `Claims::Point`), on the recorder, from the public input's
words. -/
def reduce (shape : Shape) (publicWords : List Sym) : Prog ReducedS := do
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  let variant := flockMain
  let fs := FsShape.rec3
  -- 0. The row counts.
  let counts ← countBits heights
  -- 1. C1, α (squares), β, γ.
  let root1 ← nextRoot
  let alphas ← drawRun fs 4
  let beta ← sample
  let gamma ← sample
  let weights ← eqKernel alphas
  -- 2. Flock, its lincheck's terminal walked.
  let logN := blake2sR1csLogSize + heights.getD opBlake2s 0
  let (flockPoint, map, target) ← verifyWalked logN variant fs
  -- 3. C2, t, the digits, Z_act.
  let root2 ← nextRoot
  let t ← sample
  let w ← digits t (max h (rW + 4) + 2)
  let mut active : Array Sym := #[]
  for (bs, r) in counts.zip heights do
    active := active.push (← activeVanishingFromBits w bs r)
  -- 4. The values at t.
  let mut relations : Array RelationS := #[]
  let mut parts : Array TablePartS := #[]
  for table in tables do
    let (part, rels) ← tablePart table (heights.getD table.opcode 0) weights beta w
    parts := parts.push part
    relations := relations ++ rels.toArray
  let o ← one
  let lm := shape.logMemory
  let memoryFinalCount ← nextScalar
  let address ← nextScalar
  let memoryPull ← nextScalar
  relations := relations.push (← equalS (.memory 3) (w.take lm) memoryFinalCount)
  relations := relations.push (← equalS .address (w.take lm) address)
  let mp1 ← add memoryPull beta
  let cm ← const sepMem
  let w0m ← mul (weights.getD 0 0) cm
  let mp2 ← add mp1 w0m
  let w1a ← mul (weights.getD 1 0) address
  let mp3 ← add mp2 w1a
  let w2m ← mul (weights.getD 2 0) memoryFinalCount
  let mp4 ← add mp3 w2m
  relations := relations.push ⟨(List.range 3).map (fun k ↦ termS (.memory k) (w.take lm) (weights.getD (3 + k) 0)), mp4⟩
  let om ← add o memoryFinalCount
  let w2om ← mul (weights.getD 2 0) om
  let memoryPush ← add memoryPull w2om
  let lb := shape.logBytecode
  let bytecodeFinalCount ← nextScalar
  let bytecodePull ← nextScalar
  relations := relations.push (← equalS .bytecodeFinal (w.take lb) bytecodeFinalCount)
  let bp1 ← add bytecodePull beta
  let w2b ← mul (weights.getD 2 0) bytecodeFinalCount
  let bp2 ← add bp1 w2b
  relations := relations.push (← equalS .bytecodeTuple (alphas ++ w.take lb) bp2)
  let ob ← add o bytecodeFinalCount
  let w2ob ← mul (weights.getD 2 0) ob
  let bytecodePush ← add bytecodePull w2ob
  let heapValue ← nextScalar
  let constraintValue ← nextScalar
  -- 5. The constraint quotient's identity.
  let constraint ← constraintRelation shape parts.toList publicWords gamma t constraintValue w
  relations := relations.push constraint
  let constraintChunks := chunks (shape.constraintDegree + 1)
  let c2Base : List (Column × Nat × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (constraintChunks.zip (List.range constraintChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  -- 6. C2: the heap.
  let (heapRels, leafColumns) ← heapRelations shape active.toList parts.toList weights beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush w constraintChunks
  relations := relations ++ heapRels.toArray
  let c2Columns := c2Base ++ leafColumns
  -- 7. Flock's claim on q_flock: one term for the whole ring-switch weight.
  relations := relations.push ⟨[⟨.qflock, flockPoint, ringTwist, ← one⟩], target⟩
  -- 8. ρ, one claim per commitment, the batch.
  let rho ← sample
  let mut combined : Array (Commitment × CombinedS) := #[]
  for c in commitments do
    if let some claim ← combine relations.toList c rho then
      combined := combined.push (c, claim)
  let _ ← one
  let stackLayouts := layouts shape c2Columns
  let openings ← batch combined.toList stackLayouts (some map)
  return ⟨root1, root2, openings⟩

/-- **The recorded verifier** (`record_verifier_with`): the recorder's start (the seed), the public input's four words,
then `reduce`. -/
def pi1Rec3 : Prog ReducedS := do
  let mut words : Array Sym := #[]
  for k in [0:4] do
    words := words.push (← statement k)
  reduce reference words.toList

/-- The big-endian number of some bytes. -/
def beNat (l : List UInt8) : Nat := l.foldl (fun acc b ↦ acc * 256 + b.toNat) 0

/-- **`contract::calls`**: each point claim's words (its root, its layout word, one claim, its point, its value); a
root in the stream is the word at its first half's offset. -/
def callsOf (st : RecState) (red : ReducedS) : List (List Word) :=
  let words := layoutWords reference
  let streamAt (half : Sym) : Word :=
    match st.nodes[half]? with
    | some (.input off _) => .stream off
    | _ => .stream 0
  red.openings.map fun (c, point, value) ↦
    let (root, layout) : Word × List UInt8 := match c with
      | .c1 => (streamAt red.root1.1, words.getD 0 [])
      | .c2 => (streamAt red.root2.1, words.getD 1 [])
      | .setup => (.const (beNat (LeanVM.Protocol.KeccakHash.digestBytes referenceRoots.bytecode)), words.getD 2 [])
    [root, .const (beNat layout), .const 1] ++ point.map Word.node ++ [.node value]

/-- **π1-rec3's graph, recorded in Lean**: `pi1Rec3` on the recorder from its start, with its calls' words and its
stream's length. -/
def pi1Graph : Graph :=
  let (red, st) := pi1Rec3.record RecState.start
  st.graph (callsOf st red) st.cursor

end RecGraph.Pi1
