-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Prover
import UniComplete.Claims
import UniComplete.Honest
import UniStatement.Run

/-! Phase timings of the honest prover on the first honest vector (a diagnostic for `Runner.lean`), logged to
`$UNI_PROFILE_LOG` as it goes. -/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement UniComplete

namespace UniCompleteProfile

def pushTuplesP := @pushTuples
def pullTuplesP := @pullTuples

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexNat (s : String) : ℕ := s.toList.foldl (fun acc c ↦ 16 * acc + (hexDigit c).getD 0) 0

def hexBytes (s : String) : Array UInt8 :=
  let cs := s.toList.toArray
  (Array.range (cs.size / 2)).map fun i ↦
    UInt8.ofNat (16 * (hexDigit (cs.getD (2 * i) '0')).getD 0 + (hexDigit (cs.getD (2 * i + 1) '0')).getD 0)

def rest (l : String) : List String := ((l.splitOn " ").drop 1).filter (· ≠ "")

def tagged (ls : List String) (tag : String) : List String :=
  match ls.find? (·.startsWith (tag ++ " ")) with
  | some l => rest l
  | none => []

def traceOf (shape : Shape) (rows : List ℕ) (c1 : Array K) (bytecode : Array K) (pub : List UInt8) : Trace :=
  let layout := c1Layout shape
  let stack : ℕ → K := fun i ↦ c1.getD i 0
  let valuesOf (column : Column) (r : ℕ) : Array K :=
    let coeffs := c1Block layout stack column
    Array.ofFn (n := 2 ^ r) fun x ↦ basisValue coeffs r x.val
  let tablesV : List (List (Array K)) := UniStatement.tables.map fun table ↦
    let r := shape.heights.getD table.opcode 0
    (List.range table.width).map fun c ↦ valuesOf (.table table.opcode c) r
  let memory := (List.range 4).map fun k ↦ valuesOf (.memory k) shape.logMemory
  let lb := shape.logBytecode
  let slots := (List.range 16).map fun s ↦
    Array.ofFn (n := 2 ^ lb) fun i ↦ bytecode.getD (16 * i.val + s) 0
  ⟨shape, rows, tablesV, memory, valuesOf .bytecodeFinal lb, c1Block layout stack .qflock, slots, pub⟩

def main : IO Unit := do
  let some path ← IO.getEnv "UNI_HONEST" | throw (IO.userError "UNI_HONEST")
  let some logPath ← IO.getEnv "UNI_PROFILE_LOG" | throw (IO.userError "UNI_PROFILE_LOG")
  let h ← IO.FS.Handle.mk logPath .write
  let say (s : String) : IO Unit := do h.putStrLn s; h.flush
  let ls := (← IO.FS.lines path).toList
  let body := (ls.dropWhile (fun l ↦ !(l.startsWith "VECTOR" && l.endsWith "omitted point honest"))).takeWhile (· != "END")
  let sh := (tagged body "SHAPE").map String.toNat!
  let shape : Shape := shapeWith (sh.getD 0 0) (sh.getD 1 0) (sh.drop 2)
  let rows := ((tagged body "COUNTS").drop 1).map String.toNat!
  let pub := (hexBytes ((tagged body "PUBLIC").headD "")).toList
  let c1 : Array K := match body.find? (·.startsWith "STACK C1 ") with
    | some l => (((rest l).drop 2).map fun w ↦ K.ofLane (UInt64.ofNat (hexNat w))).toArray
    | none => #[]
  let bytecode := (((tagged body "BYTECODE").drop 1).map fun w ↦ K.ofLane (UInt64.ofNat (hexNat w))).toArray
  say s!"{body.headD ""}: shape {sh}"
  let tr := traceOf shape rows c1 bytecode pub
  say s!"  c1 parsed: {c1.size} words, {(c1.toList.filter (· != 0)).length} nonzero; layout vars {(c1Layout shape).vars}, blocks {(c1Layout shape).blocks.length}; table 0 col 0 at {(c1Layout shape).limbs (.table 0 0)}; coeffs {(c1Block (c1Layout shape) (fun i ↦ c1.getD i 0) (.table 0 0)).toList.map (·.lane)}; values {(tr.column 0 0).toList.map (·.lane)}"
  let time {α : Type} (name : String) (f : Unit → α) (show_ : α → String) : IO α := do
    let t0 ← IO.monoMsNow
    let a := f ()
    say s!"  {name}: {show_ a} ({(← IO.monoMsNow) - t0} ms)"
    return a
  let _ ← time "trace (a column)" (fun _ ↦ tr.column 0 0) (fun a ↦ s!"{a.size}")
  let s1 ← time "C1 stack" (fun _ ↦ c1Stack tr) (fun a ↦ s!"{a.size} words, same {a == c1}")
  let _ ← time "setup stack" (fun _ ↦ setupStackOf tr) (fun a ↦ s!"{a.size}")
  let alphas : List E := [eK 3, eK 5, eK 7, eK 11]
  let weights := eqKernel alphas
  let beta := eK 13
  let gamma := eK 17
  let hv ← time "heap values" (fun _ ↦ heapValues tr weights beta) (fun a ↦ s!"{a.size}")
  let h := shape.heap.h
  let hn ← time "heap novel" (fun _ ↦ novelOfValuesE h hv) (fun a ↦ s!"{a.size}")
  let tn ← time "tree numerator" (fun _ ↦ treeNumerator h hn) (fun a ↦ s!"degree {a.natDegree}")
  let tq ← time "tree quotient" (fun _ ↦ divM tn (wPoly h)) (fun a ↦ s!"degree {a.natDegree}")
  let _ ← time "tree remainder" (fun _ ↦ modM tn (wPoly h)) (fun a ↦ s!"degree {a.natDegree} zero {a == 0}")
  let _ ← time "tree chunks" (fun _ ↦ chunksB tq [h, 0]) (fun a ↦ s!"{a.length}")
  let cn ← time "constraint numerator" (fun _ ↦ constraintNumerator tr gamma (publicWordsOf pub))
    (fun a ↦ s!"degree {a.natDegree}")
  let _ ← time "constraint remainder" (fun _ ↦ modM cn (wPoly shape.constraintVars)) (fun a ↦ s!"zero {a == 0}")
  for (block, index) in shape.heap.blocks.zip (List.range shape.heap.blocks.length) do
    let leaves ← time s!"block {index} leaves" (fun _ ↦ blockLeaves tr weights beta block.leaves) (fun a ↦ s!"{a.size}")
    let rp ← time s!"block {index} R" (fun _ ↦ ofNovel block.r (novelOfValuesE block.r leaves)) (fun a ↦ s!"degree {a.natDegree}")
    match leafNumerator tr weights beta block rp with
    | some n =>
      let _ ← time s!"block {index} numerator degree" (fun _ ↦ n.natDegree) (fun a ↦ s!"{a}")
      let _ ← time s!"block {index} remainder" (fun _ ↦ modM n (wPoly block.r)) (fun a ↦ s!"zero {a == 0}")
    | none => pure ()
  -- interpolation: the column polynomials at the rows
  for t in List.range 6 do
    let r := tr.height t
    let polys := tablePolys tr t
    let ok := (List.range (UniStatement.tables.getD t default).width).all fun c ↦
      (List.range (2 ^ r)).all fun i ↦ pEval (pointE i) (polys.getD c 0) == ofK ((tr.column t c).getD i 0)
    let nz := (List.range (UniStatement.tables.getD t default).width).any fun c ↦ (tr.column t c).any (· != 0)
    say s!"  table {t}: polynomials interpolate the rows {ok}; some nonzero cell {nz}; poly 0 degree {(polys.getD 0 0).natDegree}"
  let memOk := (List.range 4).all fun k ↦ (List.range (2 ^ shape.logMemory)).all fun i ↦
    pEval (pointE i) (colPolyK shape.logMemory (tr.memory.getD k #[])) == ofK ((tr.memory.getD k #[]).getD i 0)
  say s!"  memory polynomials interpolate {memOk}; cells 0,1 limb 0: {(tr.memory.getD 0 #[]).getD 0 0 |>.lane} {(tr.memory.getD 0 #[]).getD 1 0 |>.lane}; public words {(publicWordsOf pub).map fun x ↦ (x.limb 0).lane}"
  -- the bus: products at the test challenges
  let pushP := (pushTuplesP tr).foldl (fun acc τ ↦ acc * fpOf weights beta τ) 1
  let pullP := (pullTuplesP tr).foldl (fun acc τ ↦ acc * fpOf weights beta τ) 1
  say s!"  bus: {(pushTuplesP tr).length} pushes, {(pullTuplesP tr).length} pulls, products equal {pushP == pullP}"
  -- each constraint's divisibility
  let rW := shape.constraintVars
  for table in UniStatement.tables do
    let t := table.opcode
    let r := tr.height t
    let polys := tablePolys tr t
    let col := fun (name : String) ↦ polys.getD (colIdx table.columns name) 0
    let wr := wPoly r
    let check (name : String) (p : Poly) : IO Unit := say s!"  table {t} r {r} {name}: remainder zero {modM p wr == 0}"
    if t = opJump then
      check "jump1" (col "b" + col "v_cond" * col "w")
      check "jump2" (col "v_cond" * (col "b" + 1))
    let counters := table.countColumns.foldl (fun p c ↦ p * polys.getD c 0) (colPolyK r (inverseColumn tr t))
    check "counters" (counters + 1)
    if t = opBlake2s then
      let functionals := coordinateFunctionals r
      let y := (List.range r).map (coordinateP functionals)
      for c in List.range table.width do
        if let some slot := qflockSlot (table.columns.getD c "") then
          let slotValues : Array Poly := Array.ofFn (n := 2 ^ r) fun u ↦
            pC (ofK (tr.qflock.getD (slot + 256 * u.val) 0))
          check s!"copy {c} slot {slot}" (polys.getD c 0 + mleP slotValues y)
  let lm := shape.logMemory
  let pw := publicWordsOf pub
  let lines : List (E × E) := [(pw.getD 0 0, pw.getD 2 0), (pw.getD 1 0, pw.getD 3 0), (0, 0)]
  for ((low, high), k) in lines.zip (List.range 3) do
    let mem := colPolyK lm (tr.memory.getD k #[])
    say s!"  public line {k}: remainder zero {modM (mem + pC low + pX * pC (low + high)) (wPoly 1) == 0}"
  let c2 ← time "c2DataOf" (fun _ ↦ c2DataOf tr weights beta gamma) (fun a ↦ s!"{a.stack.size}")
  let a ← time "atTOf" (fun _ ↦ atTOf tr c2 alphas beta gamma (eK 19) none) (fun a ↦ s!"{a.values.length} values, {a.relations.length} relations")
  let combined ← time "combine" (fun _ ↦ commitments.filterMap fun c ↦ (combine a.relations c (eK 23)).map (c, ·))
    (fun a ↦ s!"{a.length}")
  let stackLayouts := layouts shape a.c2Columns
  for (c, claim) in combined do
    let wt ← time s!"dense weight {c.name}" (fun _ ↦ denseWeight claim (layoutIn stackLayouts c) none) (fun a ↦ s!"{a.size}")
    let stack := match c with | .c1 => s1 | .c2 => c2.stack | .setup => setupStackOf tr
    let _ ← time s!"pairing {c.name}" (fun _ ↦ (List.range wt.size).foldl (fun acc u ↦ acc + wt.getD u 0 * ofK (stack.getD u 0)) 0)
      (fun v ↦ s!"holds {v == claim.value}")
  let stackOf : Commitment → Array K := fun c ↦ match c with | .c1 => s1 | .c2 => c2.stack | .setup => setupStackOf tr
  let lay := layoutIn stackLayouts
  let mut i := 0
  for rel in a.relations do
    let lhs := (rel.terms.map fun t ↦ termEval (lay t.column.commitment) (stackOf t.column.commitment) a.ringMap t).sum
    if !(lhs == rel.value) then
      say s!"  relation {i} FAILS: {rel.terms.length} terms, first column id {(rel.terms.head?.map (·.column.id)).getD 0}"
    i := i + 1
  say "done"

end UniCompleteProfile

#eval UniCompleteProfile.main
