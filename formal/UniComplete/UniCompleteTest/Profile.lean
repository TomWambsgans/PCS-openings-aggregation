-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Prover
import UniStatement.Run

/-! Phase timings of the honest prover on the first honest vector (a diagnostic for `Runner.lean`), logged to
`$UNI_PROFILE_LOG` as it goes. -/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement UniComplete

namespace UniCompleteProfile

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
  let shape : Shape := ⟨sh.getD 0 0, sh.getD 1 0, sh.drop 2⟩
  let rows := ((tagged body "COUNTS").drop 1).map String.toNat!
  let pub := (hexBytes ((tagged body "PUBLIC").headD "")).toList
  let c1 : Array K := match body.find? (·.startsWith "STACK C1 ") with
    | some l => (((rest l).drop 2).map fun w ↦ K.ofLane (UInt64.ofNat (hexNat w))).toArray
    | none => #[]
  let bytecode := (((tagged body "BYTECODE").drop 1).map fun w ↦ K.ofLane (UInt64.ofNat (hexNat w))).toArray
  say s!"{body.headD ""}: shape {sh}"
  let tr := traceOf shape rows c1 bytecode pub
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
  say "done"

end UniCompleteProfile

#eval UniCompleteProfile.main
