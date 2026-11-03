-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from
-- `formal/UniStatement/UniStatement/Verifier.lean` (`tablePart`, `reduceWith` steps 3–7), itself
-- `crates/leanvm_univariate/src/verifier.rs`.
import UniSound.Ids.Poly

/-!
# The verifier's relations at `t`, read off the values

`reduceWith` (steps 3–7) states its relations from the challenges, Flock's result, `t` and the values
the stream sends at `t`, in a fixed order (`tablePart` for every table, then the memory's, the
bytecode's, `T(t)`, `Q_W(t)`). **`relsOf`** is that computation as a pure function of the values
(`RelInput.vals`, in stream order; a missing value reads `0`): `tablePartOf` is `tablePart` with
`nextScalar` replaced by the next value of the list, and the rest calls the verifier's own pure
functions (`linearise`, `constraintRelation`, `heapRelations`, `activeVanishingFromBits`). It is the
main line's (Flock in tower order, point claims): Flock's end, if a ring end, adds the one ring-switch
term (`ringTwist`).

That `reduceWith` states exactly these relations (`tablePart`'s reads are `tablePartOf`'s values) is
part of the code-level link; nothing here is proved about the monadic code.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement

/-! ## A table's part -/

/-- `tablePart`'s state through its flushes: the leaf's products, their degrees, the relations, the
values not yet read. -/
structure TPState where
  pull : E
  push : E
  pullDegree : ℕ
  pushDegree : ℕ
  rels : List Relation
  vals : List E

/-- **One flush of `tablePart`** (its loop body): the pull fingerprint computed from the sent values, or
sent and bound by a relation; the push fingerprint the pull's plus the difference, or sent and bound. -/
def flushStep (at_ : ℕ → Column) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) (st : TPState) (fl : List Form × List Form) : TPState :=
  let lPull := linearise fl.1 weights sent
  let pullSent := !lPull.2.isEmpty
  let dPull := if pullSent then st.vals.headD 0 else beta + lPull.1
  let rels1 := if pullSent then
      st.rels ++ [⟨lPull.2.map (fun ck ↦ term (at_ ck.1) pt ck.2), st.vals.headD 0 + beta + lPull.1⟩]
    else st.rels
  let vals1 := if pullSent then st.vals.tail else st.vals
  let lDiff := linearise (difference fl.2 fl.1) weights sent
  let pushSent := !lDiff.2.isEmpty
  let lPush := linearise fl.2 weights sent
  let dPush := if pushSent then vals1.headD 0 else dPull + lDiff.1
  let rels2 := if pushSent then
      rels1 ++ [⟨lPush.2.map (fun ck ↦ term (at_ ck.1) pt ck.2), vals1.headD 0 + beta + lPush.1⟩]
    else rels1
  let vals2 := if pushSent then vals1.tail else vals1
  ⟨st.pull * dPull, st.push * dPush, st.pullDegree + tupleDegree fl.1,
    st.pushDegree + tupleDegree fl.2, rels2, vals2⟩

/-- The sent values' array (`tablePart`'s first loop): column `sentColumns[i]` holds value `i`. -/
def sentOf (t : Table) (vals : List E) : Array (Option E) :=
  ((sentColumns t).zip (List.range (sentColumns t).length)).foldl
    (fun (sent : Array (Option E)) p ↦ sent.set! p.1 (some (vals.getD p.2 0)))
    (Array.replicate t.width none)

/-- **`tablePart`, read off a list of values**: its part, its relations, the values left. -/
def tablePartOf (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E)
    (vals : List E) : TablePart × List Relation × List E :=
  let pt := w.take logHeight
  let sc := sentColumns t
  let sent := sentOf t vals
  let rels0 : List Relation := (sc.zip (List.range sc.length)).map fun p ↦
    Relation.equal (.table t.opcode p.1) pt (vals.getD p.2 0)
  let st := (t.flushes.pull.zip t.flushes.push).foldl
    (flushStep (fun c ↦ .table t.opcode c) pt weights beta sent) ⟨1, 1, 1, 0, rels0, vals.drop sc.length⟩
  (⟨st.pull, st.push, st.pullDegree, st.pushDegree, sent⟩, st.rels, st.vals)

/-- Every table's part, in order, each reading the values the one before left. -/
def tablesPart (shape : Shape) (weights : Array E) (beta : E) (w : List E) :
    List Table → List E → List TablePart × List Relation × List E
  | [], vals => ([], [], vals)
  | t :: ts, vals =>
    let r := tablePartOf t (shape.heights.getD t.opcode 0) weights beta w vals
    let rest := tablesPart shape weights beta w ts r.2.2
    (r.1 :: rest.1, r.2.1 ++ rest.2.1, rest.2.2)

/-! ## All the relations -/

/-- **What the verifier states its relations from** (steps 3–7): the shape, the public words, each
table's count bits, the bus challenges, Flock's point and end, `t`, the values at `t`. -/
structure RelInput where
  shape : Shape
  publicWords : List E
  counts : List (List E)
  alphas : List E
  beta : E
  gamma : E
  flockPoint : List E
  flockEnd : Option Flock.End
  t : E
  vals : List E

namespace RelInput

variable (inp : RelInput)

/-- The digits the verifier reads `t` through. -/
def w : List E := digits inp.t (max inp.shape.heap.h (inp.shape.constraintVars + 4) + 2)

/-- The tuple weights `eq(α, ·)`. -/
def weights : Array E := eqKernel inp.alphas

/-- Each table's `Z_act(t)` (F1b). -/
def active : List E :=
  (inp.counts.zip inp.shape.heights).map fun p ↦ activeVanishingFromBits inp.w p.1 p.2

/-- The tables' parts. -/
def tp : List TablePart × List Relation × List E :=
  tablesPart inp.shape inp.weights inp.beta inp.w tables inp.vals

/-- The values after the tables'. -/
def rest : List E := inp.tp.2.2

def memoryFinalCount : E := inp.rest.getD 0 0
def address : E := inp.rest.getD 1 0
def memoryPull : E := inp.rest.getD 2 0
def memoryPush : E := inp.memoryPull + inp.weights.getD 2 0 * (1 + inp.memoryFinalCount)
def bytecodeFinalCount : E := inp.rest.getD 3 0
def bytecodePull : E := inp.rest.getD 4 0
def bytecodePush : E := inp.bytecodePull + inp.weights.getD 2 0 * (1 + inp.bytecodeFinalCount)
def heapValue : E := inp.rest.getD 5 0
def constraintValue : E := inp.rest.getD 6 0

/-- The memory's three relations. -/
def memRels : List Relation :=
  [Relation.equal (.memory 3) (inp.w.take inp.shape.logMemory) inp.memoryFinalCount,
    Relation.equal .address (inp.w.take inp.shape.logMemory) inp.address,
    ⟨(List.range 3).map (fun k ↦ term (.memory k) (inp.w.take inp.shape.logMemory)
        (inp.weights.getD (3 + k) 0)),
      inp.memoryPull + inp.beta + inp.weights.getD 0 0 * sepMem + inp.weights.getD 1 0 * inp.address +
        inp.weights.getD 2 0 * inp.memoryFinalCount⟩]

/-- The bytecode's two relations. -/
def bcRels : List Relation :=
  [Relation.equal .bytecodeFinal (inp.w.take inp.shape.logBytecode) inp.bytecodeFinalCount,
    Relation.equal .bytecodeTuple (inp.alphas ++ inp.w.take inp.shape.logBytecode)
      (inp.bytecodePull + inp.beta + inp.weights.getD 2 0 * inp.bytecodeFinalCount)]

/-- The constraint quotient's relation and degree (step 5). -/
def constraint : Relation × ℕ :=
  constraintRelation inp.shape inp.tp.1 inp.publicWords inp.gamma inp.t inp.constraintValue inp.w

/-- The heap's relations (step 6). -/
def heap : List Relation × List (Column × ℕ × Bool) :=
  heapRelations inp.shape inp.active inp.tp.1 inp.weights inp.beta inp.heapValue inp.constraintValue
    inp.memoryPull inp.memoryPush inp.bytecodePull inp.bytecodePush inp.w (chunks (inp.constraint.2 + 1))

/-- Flock's ring end (step 7, the main line: one term for the whole ring-switch weight). -/
def ringRels : List Relation :=
  match inp.flockEnd with
  | some (.ring _ target) => [⟨[⟨.qflock, inp.flockPoint, ringTwist, 1⟩], target⟩]
  | _ => []

/-- The ring map the batch's weight reads the ring-switch term by. -/
def ringMap : Option (List E) :=
  match inp.flockEnd with
  | some (.ring mp _) => some mp
  | _ => none

end RelInput

/-- **The verifier's relations at `t`**, in its order (steps 4–7 of `reduceWith`, main line). -/
def relsOf (inp : RelInput) : List Relation :=
  inp.tp.2.1 ++ inp.memRels ++ inp.bcRels ++ [inp.constraint.1] ++ inp.heap.1 ++ inp.ringRels

/-- The relations on one commitment, in order (`combine`'s `mine`). -/
def mine (rels : List Relation) (c : Commitment) : List Relation :=
  rels.filter (·.commitment == c)

end UniSound.Ids
