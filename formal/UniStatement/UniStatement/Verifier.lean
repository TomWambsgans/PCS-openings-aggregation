-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/verifier.rs` (`reduce`, `table_part`,
-- `linearise`, `tuple_degree`, `chunks`, `quotient_terms`, `sent_columns`, `layouts`, `Shape`). The tables,
-- flushes, fingerprints, public lines and Flock are leanVM 42422001's (https://github.com/leanEthereum/leanVM),
-- read through `crates/leanvm_flock_gas`. MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Domain
public import UniStatement.Heap
public import UniStatement.Flock
public import UniStatement.Batch

/-!
# The verifier (`verifier.rs`, SPEC.md §4–§8): from the stream to one claim per commitment

`reduceWith F shape publicWords blake2s mode`, line by line `reduce`:

1. **`C1`**, then `α ∈ E^4` (the tuple weights, `eq(α, ·)` over 16 slots), `β` (the fingerprint shift),
   `γ` (the constraints' batching).
2. **Flock** (`Flock.verify`, a module of its own), on `q_flock`.
3. **`C2`**, then `t`, and its digits `w_l(t)`.
4. **The values at `t`** (`tablePart`, then the memory, the bytecode, `T(t)`, `Q_W(t)`): each table's
   counters and factor columns, then each flush's pull fingerprint (computed when every column of its tuple
   is sent, else sent and bound by a relation on `C1`), and its push fingerprint (the pull's plus their
   difference when the sent values give it, else sent and bound).
5. **The constraint quotient's identity** on `C1`: JUMP's two constraints, every table's counters
   (`(z Π c + 1) Z_pad`), BLAKE2S's limb copies against `q_flock`'s slots (read through `y(t)`), the public
   lines; batched by the powers of `γ`, each lifted to `V_{r_W}`; `= Q_W(t) w_{r_W}(t)`.
6. **`C2`**: `T(t)`, the tree, the root, each heap block's leaf identity, the constraint quotient's chunks.
7. **Flock's end** on `q_flock`: the ring switch's 64 twisted terms, or the bit-slice combination.
8. **`ρ`** combines each commitment's relations (`combine`); then one claim per commitment: weighted
   (extension W) or by the batching sumcheck (`batch`, a module of its own) to point claims (the ABI).

The verdict is `reduce`'s: no stream error, every collected value zero, the stream consumed
(`run`, `Accepts`). What `PCS_OPEN` then checks of the claims is `Opening.lean`'s.

Rust `u64` arithmetic on degrees is `ℕ` here; the Rust's differences never underflow at a shape whose
tables are nonempty (the test's shapes).
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol

/-- **The sizes a contract is built for** (`Shape`, the setup's part): the memory's and the bytecode's
log-sizes, each table's log-height (XOR, MUL, SET, DEREF, JUMP, BLAKE2S), and the row counts each quotient is
sized for (`capacityRows`). The heap, the stacks and every quotient's size depend on these only.

**The row counts are the proof's** (`Rows`, REVIEW-M1 F1): `Z_act` and `Z_pad` are computed from them. At
`cee6363`/`b948bfc` the contract fixes them too (`Shape::table_rows`, the `capacityRows` here and the rows a
run is given are the same constants, `shapeOf`); REVIEW-M1's F1 announces them in calldata, absorbed in the
seed, the quotients sized for the smallest count of each height (`capacityRows = 2^(h−1) + 1`). -/
structure Shape where
  logMemory : ℕ
  logBytecode : ℕ
  heights : List ℕ
  capacityRows : List ℕ
  deriving Inhabited, Repr

/-- **A valid shape** (REVIEW-M1 F5: smaller sizes make the Rust's `u64` degrees wrap and `reduce` panic):
six tables, the memory and the bytecode of at least `4` cells, and each table either empty (height `0`, no
row; XOR, MUL, SET or DEREF only: JUMP's and BLAKE2S's degrees wrap at height `0`) or of height at least `2`
with its capacity a row count of its height (`2^(h−1) < capacity ≤ 2^h`). -/
def Shape.Valid (s : Shape) : Prop :=
  s.heights.length = 6 ∧ s.capacityRows.length = 6 ∧ 2 ≤ s.logMemory ∧ 2 ≤ s.logBytecode ∧
    ∀ t < 6, (s.heights.getD t 0 = 0 ∧ s.capacityRows.getD t 0 = 0 ∧ t < 4) ∨
      (2 ≤ s.heights.getD t 0 ∧ 2 ^ (s.heights.getD t 0 - 1) < s.capacityRows.getD t 0 ∧
        s.capacityRows.getD t 0 ≤ 2 ^ s.heights.getD t 0)

instance (s : Shape) : Decidable s.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- **The row counts a proof is for** fit the shape: six, each at least its table's capacity and at most
its height (so `⌈log₂ rows⌉` is the height, and every honest quotient fits its chunks). -/
def Shape.RowsFit (s : Shape) (rows : List ℕ) : Prop :=
  rows.length = 6 ∧ ∀ t < 6, s.capacityRows.getD t 0 ≤ rows.getD t 0 ∧ rows.getD t 0 ≤ 2 ^ s.heights.getD t 0

instance (s : Shape) (rows : List ℕ) : Decidable (s.RowsFit rows) := inferInstanceAs (Decidable (_ ∧ _))

/-- `Shape::constraint_vars`: the domain of the constraint quotient, the largest table or the memory. -/
def Shape.constraintVars (s : Shape) : ℕ := (s.heights ++ [s.logMemory]).foldl max 0

/-- `Shape::heap`. -/
def Shape.heap (s : Shape) : HeapLayout := HeapLayout.new s.logMemory s.logBytecode s.heights

/-- `factor_columns(opcode)`: the columns a table sends at `t` besides its counters, every factor of a
product in its flushes and constraints. -/
def factorColumns (opcode : ℕ) : List String :=
  if opcode = opMul then ["fp", "pc", "va_0", "va_1", "va_2"]
  else if opcode = opDeref then ["fp", "pc", "ptr", "f_pc", "f_fp"]
  else if opcode = opJump then ["fp", "b", "v_cond"]
  else ["fp", "pc"]

/-- **`sent_columns(table)`**: the counters, then the factor columns, in the order they are sent. -/
def sentColumns (t : Table) : List ℕ :=
  t.countColumns ++ (factorColumns t.opcode).map (colIdx t.columns)

/-- Add `c` to `column`'s coefficient, or append it (`linearise`'s `add`). -/
def addTerm (terms : List (ℕ × E)) (column : ℕ) (c : E) : List (ℕ × E) :=
  match terms.findIdx? (·.1 == column) with
  | some i => terms.modify i fun (k, v) ↦ (k, v + c)
  | none => terms ++ [(column, c)]

/-- **`linearise(tuple, weights, sent)`**: `Σ_s weights[s] · tuple[s]` split into what the sent values give
and the terms in the other columns (a product of a sent and an unsent column is a term in the unsent one;
the tables have no product of two unsent columns). -/
def linearise (tuple : List Form) (weights : Array E) (sent : Array (Option E)) : E × List (ℕ × E) :=
  ((tuple.zip (List.range tuple.length)).foldl (fun (acc : E × List (ℕ × E)) (form, s) ↦
    let weight := weights.getD s 0
    form.foldl (fun (acc : E × List (ℕ × E)) (monomial, coefficient) ↦
      let (known, terms) := acc
      if coefficient = 0 then acc else
      let c := weight * coefficient
      match monomial with
      | [] => (known + c, terms)
      | [i] => match sent.getD i none with
        | some v => (known + c * v, terms)
        | none => (known, addTerm terms i c)
      | [i, j] => match sent.getD i none, sent.getD j none with
        | some a, some b => (known + c * a * b, terms)
        | some a, none => (known, addTerm terms j (c * a))
        | none, some b => (known, addTerm terms i (c * b))
        | none, none => (known, terms)
      | _ => acc) acc) (0, []))

/-- `tuple_degree(tuple)`: the largest degree of a nonzero monomial, at least `1`. -/
def tupleDegree (tuple : List Form) : ℕ :=
  max 1 (tuple.foldl (fun d form ↦
    form.foldl (fun d (monomial, c) ↦ if c = 0 then d else max d monomial.length) d) 0)

/-- **`chunks(count)`**: `Σ_k 2^(e_k)`, at most three powers of two, covering `count` coefficients (a
quotient's chunks: the largest powers of two, the third rounded up). -/
def chunks (count : ℕ) : List ℕ := Id.run do
  let mut sizes : Array ℕ := #[]
  let mut left := count
  for _ in [0:4] do
    if left > 0 then
      let top := Nat.log2 left
      if sizes.size = 2 ∧ left ≠ 2 ^ top then
        sizes := sizes.push (top + 1)
        left := 0
      else
        sizes := sizes.push top
        left := left - 2 ^ top
  return sizes.toList

/-- **`quotient_terms(column, sizes, w, scale)`**: `Q(t) = Q_0 + w_{e_0}(Q_1 + w_{e_1}(Q_2 …))` times `scale`,
as terms on the chunks, chunk `c` at `w[..e_c]`. -/
def quotientTerms (column : ℕ → Column) (sizes : List ℕ) (w : List E) (scale : E) : List Term :=
  ((sizes.zip (List.range sizes.length)).foldl (fun (acc : Array Term × E) (e, chunk) ↦
    (acc.1.push (term (column chunk) (w.take e) acc.2), acc.2 * w.getD e 0)) (#[], scale)).1.toList

/-- One table's part of the check (`TablePart`): its leaf's two products, their degrees over `n − 1`, its
sent values. -/
structure TablePart where
  pull : E
  push : E
  pullDegree : ℕ
  pushDegree : ℕ
  sent : Array (Option E)
  deriving Inhabited

/-- The push tuple's difference from the pull tuple, slot by slot (`pushed + pulled`). -/
def difference (pushed pulled : List Form) : List Form :=
  (pushed.zip pulled).map fun (a, b) ↦ a.addScaled b 1

/-- **How the BLAKE2s argument runs** (`Blake2s`). -/
inductive Blake2s where
  | flock (variant : Flock.Variant)
  | omitted
  deriving DecidableEq, Repr, Inhabited

/-- **How the relations reach `PCS_OPEN`** (`Claims`). -/
inductive ClaimsMode where
  /-- `PCS_OPEN`'s ABI: point claims, by the batching sumcheck. -/
  | point
  /-- Extension W: one weighted claim per commitment. -/
  | weighted
  deriving DecidableEq, Repr, Inhabited

/-- `FLOCK_MAIN`: the main line, (a′), skip 3, the slices sent. -/
def flockMain : Flock.Variant := ⟨3, .weighted⟩
/-- `FLOCK_BIT_SLICE`: extension B, skip 4, the slices left to a bit-slice claim. -/
def flockBitSlice : Flock.Variant := ⟨4, .claim⟩
/-- `FLOCK_LEANVM_SKIP`: leanVM's skip 6 with (a′)'s weighted claim. -/
def flockLeanvmSkip : Flock.Variant := ⟨6, .weighted⟩

/-- **What the verifier leaves** (`Reduced`): the two roots (each its halves), one opening per commitment,
Flock's claims on `A0`, `B0`, the number of relations combined, each stack's variables. -/
structure Reduced where
  roots : (E × E) × (E × E)
  openings : List (Commitment × Opening)
  matrices : Option Flock.MatrixClaim
  relations : ℕ
  stackVars : List (Commitment × ℕ)
  deriving Inhabited

/-- **The three stacks' layouts** (`layouts`, SPEC.md §3). `C1`: `q_flock` (values, `h_B + 8`), every
table's columns and its `z_T`, the memory's four columns, the bytecode's final counts; `C2`: the heap, the
quotients (`E`-valued, as the walk lists them); setup: the bytecode's tuples (`lb + 4`), the addresses. -/
def layouts (shape : Shape) (c2Columns : List (Column × ℕ × Bool)) : List (Commitment × StackLayout) :=
  let heights := shape.heights
  let c1 : List (Column × ℕ × Bool) :=
    [(.qflock, heights.getD opBlake2s 0 + 8, false)] ++
      tables.flatMap (fun t ↦
        let h := heights.getD t.opcode 0
        (List.range t.width).map (fun c ↦ (Column.table t.opcode c, h, false)) ++
          [(.inverse t.opcode, h, false)]) ++
      (List.range 4).map (fun k ↦ (Column.memory k, shape.logMemory, false)) ++
      [(.bytecodeFinal, shape.logBytecode, false)]
  let setup : List (Column × ℕ × Bool) :=
    [(.bytecodeTuple, shape.logBytecode + 4, false), (.address, shape.logMemory, false)]
  [(.c1, StackLayout.new c1), (.c2, StackLayout.new c2Columns), (.setup, StackLayout.new setup)]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`table_part`**: a table's sent values (each bound on `C1` at `w[..r]`), then its flushes'
fingerprints and its leaf's products; the relations it states, in order. -/
def tablePart (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E) :
    ChanM m (TablePart × List Relation) := do
  let at_ (c : ℕ) : Column := .table t.opcode c
  let pt := w.take logHeight
  let mut sent : Array (Option E) := Array.replicate t.width none
  let mut relations : Array Relation := #[]
  for column in sentColumns t do
    let value ← nextScalar (m := m)
    sent := sent.set! column (some value)
    relations := relations.push (Relation.equal (at_ column) pt value)
  let mut pull : E := 1
  let mut push : E := 1
  let mut pullDegree := 1
  let mut pushDegree := 0
  for (pulled, pushed) in t.flushes.pull.zip t.flushes.push do
    -- The pull fingerprint: computed if every column is sent, else sent and bound.
    let (known, terms) := linearise pulled weights sent
    let mut dPull := beta + known
    if !terms.isEmpty then
      let value ← nextScalar (m := m)
      relations := relations.push ⟨terms.map (fun (c, k) ↦ term (at_ c) pt k), value + beta + known⟩
      dPull := value
    -- The push fingerprint: the pull's plus their difference, when the sent values give it; else sent.
    let (knownDifference, differenceTerms) := linearise (difference pushed pulled) weights sent
    let mut dPush := dPull + knownDifference
    if !differenceTerms.isEmpty then
      let (knownPush, termsPush) := linearise pushed weights sent
      let value ← nextScalar (m := m)
      relations := relations.push ⟨termsPush.map (fun (c, k) ↦ term (at_ c) pt k), value + beta + knownPush⟩
      dPush := value
    pull := pull * dPull
    push := push * dPush
    pullDegree := pullDegree + tupleDegree pulled
    pushDegree := pushDegree + tupleDegree pushed
  return (⟨pull, push, pullDegree, pushDegree, sent⟩, relations.toList)

/-- **The constraint quotient's identity** (step 5): its relation on `C1` (but for `Q_W(t)`, sent) and the
quotient's degree. -/
def constraintRelation (shape : Shape) (rowCounts : List ℕ) (parts : List TablePart) (publicWords : List E)
    (gamma t constraintValue : E) (w : List E) : Relation × ℕ := Id.run do
  let heights := shape.heights
  let rW := shape.constraintVars
  let mut known : E := 0
  let mut terms : Array Term := #[]
  let mut power : E := 1
  let mut degree : ℕ := 0
  for (table, part) in tables.zip parts do
    let r := heights.getD table.opcode 0
    let n := 2 ^ r
    let rows := rowCounts.getD table.opcode 0
    let capacity := shape.capacityRows.getD table.opcode 0
    let lift := vanishingRatio w r rW
    let padding := suffixVanishing w rows r
    -- JUMP: b + v_cond w, v_cond (b + 1).
    if table.opcode = opJump then
      let cond := (part.sent.getD (colIdx table.columns "v_cond") none).getD 0
      let flag := (part.sent.getD (colIdx table.columns "b") none).getD 0
      let g1 := power * lift
      power := power * gamma
      known := known + g1 * flag
      terms := terms.push (term (.table table.opcode (colIdx table.columns "w")) (w.take r) (g1 * cond))
      let g2 := power * lift
      power := power * gamma
      known := known + g2 * cond * (flag + 1)
      degree := max degree (n - 2)
    -- Counters nonzero on the active rows: (z Π c + 1) Z_pad.
    let counters := table.countColumns.foldl (fun acc c ↦ acc * (part.sent.getD c none).getD 0) 1
    let g := power * lift * padding
    power := power * gamma
    terms := terms.push (term (.inverse table.opcode) (w.take r) (g * counters))
    known := known + g
    let counts := table.countColumns.length
    degree := max degree ((n - 1) * (1 + counts) + (n - capacity) - n)
    -- BLAKE2S's limb copies equal q_flock's limbs: copy_j − ℓ_j, ℓ_j read through y(t).
    if table.opcode = opBlake2s then
      let y := coordinatesAt t (coordinateFunctionals r)
      for c in List.range table.width do
        if let some slot := qflockSlot (table.columns.getD c "") then
          let g := power * lift
          power := power * gamma
          terms := terms.push (term (.table table.opcode c) (w.take r) g)
          terms := terms.push (term (.qflockSlot slot) y g)
      degree := max degree (r * (n / 2) - n)
  -- The public input: the memory's limbs at cells 0 and 1 are the public lines.
  let lm := shape.logMemory
  let lines : List (E × E) :=
    [(publicWords.getD 0 0, publicWords.getD 2 0), (publicWords.getD 1 0, publicWords.getD 3 0), (0, 0)]
  let lift := vanishingRatio w 1 rW
  for ((low, high), k) in lines.zip (List.range 3) do
    let g := power * lift
    power := power * gamma
    terms := terms.push (term (.memory k) (w.take lm) g)
    known := known + g * (low + t * (low + high))
  degree := max degree (2 ^ lm - 3)
  return (⟨terms.toList, constraintValue * w.getD rW 0 + known⟩, degree)

/-- **The heap's relations** (step 6) on `C2`, and the leaf quotients' columns: `T(t)`, the tree, the root,
each block's leaf identity (`R_b(o_b + t) P_pull + w_r(t) Q_b(t) = P_push`, `R_u(o_u + t) = 1` on an unused
block), the constraint quotient's chunks. -/
def heapRelations (shape : Shape) (rowCounts : List ℕ) (parts : List TablePart) (weights : Array E) (beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush : E) (w : List E)
    (constraintChunks : List ℕ) : List Relation × List (Column × ℕ × Bool) := Id.run do
  let heap := shape.heap
  let h := heap.h
  let lb := shape.logBytecode
  let atT := w.take h
  let mut relations : Array Relation := #[Relation.equal .heap atT heapValue]
  let mut columns : Array (Column × ℕ × Bool) := #[]
  -- The tree: w_1 (T(s(t)) + T(t) T(t+1)) + w_h Q_tree(t) = 0, Q_tree = Q_0 + w_h q_1.
  let atS := (w.drop 1).take h
  let atNext := atT.modify 0 (· + 1)
  let w1 := w.getD 1 0
  let wh := w.getD h 0
  relations := relations.push ⟨[term .heap atS w1, term .heap atNext (w1 * heapValue),
    term (.treeQuotient 0) atT wh, term (.treeQuotient 1) [] (wh * wh)], 0⟩
  -- The root: T(1) (β + fp(SEP_STATE, 1, 1)) = β + fp(SEP_STATE, g^(2^lb − 1), 1).
  let atOne := (List.range h).map fun l ↦ if l = 0 then (1 : E) else 0
  let init := beta + weights.getD 0 0 * sepState + weights.getD 1 0 + weights.getD 2 0
  let last := gpow (2 ^ lb - 1)
  let fin := beta + weights.getD 0 0 * sepState + weights.getD 1 0 * last + weights.getD 2 0
  relations := relations.push ⟨[term .heap atOne init], fin⟩
  -- Each block's leaves.
  for (block, index) in heap.blocks.zip (List.range heap.blocks.length) do
    let mixed := (List.range h).map fun l ↦
      let c := pointE (block.position >>> l)
      if l < block.r then w.getD l 0 + c else c
    let n := 2 ^ block.r
    let leaf : Option (E × E × ℕ) := match block.leaves with
      | .unused => none
      | .memory => some (memoryPull, memoryPush, 2 * (n - 1) - n)
      | .bytecode => some (bytecodePull, bytecodePush, 2 * (n - 1) - n)
      | .table t =>
        -- Padding rows' leaves are 1, whatever they hold: (R P_pull + P_push) Z_pad + (R + 1) Z_act.
        let part := parts.getD t default
        let rows := rowCounts.getD t 0
        let capacity := shape.capacityRows.getD t 0
        let active := prefixVanishing w rows
        let padding := suffixVanishing w rows block.r
        let d := (max part.pullDegree part.pushDegree) * (n - 1) + (n - capacity) - n
        some (part.pull * padding + active, part.push * padding + active, d)
    match leaf with
    | none => relations := relations.push ⟨[term .heap mixed 1], 1⟩
    | some (pull, push, degree) =>
      let sizes := chunks (degree + 1)
      columns := columns ++ (sizes.zip (List.range sizes.length)).toArray.map fun (e, chunk) ↦
        (Column.leafQuotient index chunk, e, true)
      relations := relations.push ⟨[term .heap mixed pull] ++
        quotientTerms (Column.leafQuotient index) sizes w (w.getD block.r 0), push⟩
  relations := relations.push ⟨quotientTerms .constraintQuotient constraintChunks w 1, constraintValue⟩
  return (relations.toList, columns.toList)

/-- **The verifier** over the permutation `F` (`reduce`, SPEC.md §4–§8), at the shape `shape` and the row
counts `rows`: `publicWords` are the public input's four 64-bit words, low first. -/
def reduceWith (shape : Shape) (rows : List ℕ) (publicWords : List E) (blake2s : Blake2s)
    (mode : ClaimsMode) : ChanM m Reduced := do
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  -- 1. C1, then the bus's and the constraints' challenges.
  let root1 ← nextRoot (m := m)
  let alphas ← samples F 4
  let beta ← sample F
  let gamma ← sample F
  let weights := eqKernel alphas
  -- 2. Flock, on C1's q_flock.
  let flock ← match blake2s with
    | .flock variant => some <$> Flock.verify F (blake2sR1csLogSize + heights.getD opBlake2s 0) variant
    | .omitted => pure none
  -- 3. C2, then the point.
  let root2 ← nextRoot (m := m)
  let t ← sample F
  let w := digits t (max h (rW + 4) + 2)
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
    constraintRelation shape rows parts.toList publicWords gamma t constraintValue w
  relations := relations.push constraint
  let constraintChunks := chunks (quotientDegree + 1)
  let c2Columns : List (Column × ℕ × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (constraintChunks.zip (List.range constraintChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  -- 6. C2: the heap's tree, root and leaves, and Q_W's value.
  let (heapRels, leafColumns) := heapRelations shape rows parts.toList weights beta heapValue constraintValue
    memoryPull memoryPush bytecodePull bytecodePush w constraintChunks
  relations := relations ++ heapRels.toArray
  let c2Columns := c2Columns ++ leafColumns
  -- 7. Flock's claim on q_flock: the ring switch's 64 twisted terms, or one bit-slice combination.
  let mut bitSliceRelations : List Relation := []
  let mut matrices : Option Flock.MatrixClaim := none
  match flock with
  | some fl =>
    match fl.end_ with
    | .ring map target =>
      let coefficients := Flock.ringSwitchCoefficients map
      relations := relations.push ⟨(coefficients.zip (List.range coefficients.length)).map
        (fun (c, k) ↦ ⟨.qflock, fl.point, k, c⟩), target⟩
    | .combination ws value =>
      bitSliceRelations := [⟨(ws.zip (List.range ws.length)).map (fun (c, i) ↦ ⟨.qflockBits, fl.point, i, c⟩),
        value⟩]
    matrices := some fl.matrices
  | none => pure ()
  -- 8. One claim per commitment.
  let rho ← sample F
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine relations.toList c rho).map (c, ·)
  let bitSlice := combine bitSliceRelations .c1 1
  let stackLayouts := layouts shape c2Columns
  let stackVars := stackLayouts.map fun (c, l) ↦ (c, l.vars)
  let openings ← match mode with
    | .weighted =>
      let openings : List (Commitment × Opening) := combined.map fun (c, claim) ↦ (c, .weighted claim)
      match bitSlice, openings with
      | some claim, (c, .weighted c1) :: rest =>
        -- Without the point ABI, the bit-slice terms join C1's weighted claim, at a fresh power of ρ.
        let fresh := epow rho c1.relations
        let base := c1.points.length
        let merged : Combined := { c1 with
          points := c1.points ++ claim.points
          terms := c1.terms ++ claim.terms.map fun (column, p, twist, k) ↦ (column, p + base, twist, fresh * k)
          value := c1.value + fresh * claim.value }
        pure ((c, .weighted merged) :: rest)
      | _, _ => pure openings
    | .point => batch F combined stackLayouts bitSlice
  return ⟨(root1, root2), openings, matrices, relations.size, stackVars⟩

end With

end UniStatement

end
