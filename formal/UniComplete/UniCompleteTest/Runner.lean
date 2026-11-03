-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Prover
import UniStatement.Run

/-!
# The differential test of the honest prover

`UNI_HONEST=<vectors> lake env lean ../UniComplete/UniCompleteTest/Runner.lean` (from `formal/EndToEnd`), on the
review's honest proofs (`crates/leanvm_univariate/tests/review_honest.rs`, `lean_honest_vectors`: the vectors
`honest-lm* omitted point honest`, which carry their committed stacks `STACK C1/C2/Setup` and the bytecode's
slots `BYTECODE`). For each: the placed trace is read back from the vector's `C1` stack (each column's basis-`B`
coefficients at its block, evaluated at every row: `basisValue`) and its bytecode; the Lean prover
(`proveStreamWith`, interpreted, with the review's stand-in roots for `C1` and `C2`, as the Rust's `prove_tiny`
cross-check does) writes its stream and its stacks; the test compares **the stream byte for byte** and **the three
stacks word for word** with the vector's, and runs the Lean verifier (`UniStatement.run`) on the Lean stream.
It throws (so `lean` exits with an error) on any disagreement.

The vectors: `UNI_HONEST_OUT=$PWD/uni_honest.txt cargo test --release -p leanvm_univariate --test review_honest --
--ignored --nocapture lean_honest_vectors` (the four `… omitted point honest` records of the 20 are the ones
read). The review's prover writes the same streams as the Rust prover's `prove_tiny` with stand-in roots (that
test's own cross-check, `leanvm-univariate-prover2`), so the Lean prover agrees with both. A vector's `SHAPE`
line carries the row counts; the heights are `⌈log₂ rows⌉` (`shapeWith`).

**Result** (h1, `lean-uni-complete`): 4/4 vectors (memory and bytecode `2^4`, `2^5`; 15 to 31 cycles over all six
tables, DEREF's gated store; Flock omitted, point claims): the stream the same byte for byte (2,896 bytes each),
`C1`, `C2` and the setup stack the same word for word (`2^15` words each), the Lean verifier accepts; about
6.5 minutes interpreted (the exact divisions are `Div.lean`'s quadratic long division).
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement UniComplete

namespace UniCompleteTest

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexNat (s : String) : ℕ := s.toList.foldl (fun acc c ↦ 16 * acc + (hexDigit c).getD 0) 0

def hexBytes (s : String) : Array UInt8 :=
  let cs := s.toList.toArray
  (Array.range (cs.size / 2)).map fun i ↦
    UInt8.ofNat (16 * (hexDigit (cs.getD (2 * i) '0')).getD 0 + (hexDigit (cs.getD (2 * i + 1) '0')).getD 0)

/-- The tokens after a line's tag. -/
def rest (l : String) : List String := ((l.splitOn " ").drop 1).filter (· ≠ "")

/-- A vector's lines. -/
structure Vec where
  name : String
  lines : List String

def vectors (ls : List String) : List Vec := Id.run do
  let mut out : Array Vec := #[]
  let mut cur : Option Vec := none
  for l in ls do
    if l.startsWith "VECTOR " then
      cur := some ⟨l, []⟩
    else if l == "END" then
      if let some v := cur then out := out.push ⟨v.name, v.lines.reverse⟩
      cur := none
    else
      cur := cur.map fun v ↦ ⟨v.name, l :: v.lines⟩
  return out.toList

def Vec.tagged (v : Vec) (tag : String) : List String :=
  match v.lines.find? (·.startsWith (tag ++ " ")) with
  | some l => rest l
  | none => []

/-- The trace read back from a `C1` stack and the bytecode's slots. -/
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

/-- The review's stand-in roots (`prove_tiny`): `C1`'s `(0x1111, 0x2222), (0x3333, 0x4444)`, `C2`'s
`(0x5555, 0x6666), (0x7777, 0x8888)`. -/
def standIn : Commitment → ℕ → Array K → Id Committed
  | .c1, _, _ => pure ⟨(default : Committed).tree, (eNew 0x1111 0x2222 0, eNew 0x3333 0x4444 0)⟩
  | _, _, _ => pure ⟨(default : Committed).tree, (eNew 0x5555 0x6666 0, eNew 0x7777 0x8888 0)⟩

def firstDiff {α : Type} [BEq α] (a b : Array α) : ℕ :=
  ((List.range (max a.size b.size)).find? fun i ↦ !(a[i]? == b[i]?)).getD 0

def checkVector (v : Vec) : IO Bool := do
  let sh := (v.tagged "SHAPE").map String.toNat!
  let shape : Shape := shapeWith (sh.getD 0 0) (sh.getD 1 0) (sh.drop 2)
  let rows := ((v.tagged "COUNTS").drop 1).map String.toNat!
  let iv := (hexBytes ((v.tagged "IV").headD "")).toList
  let pub := (hexBytes ((v.tagged "PUBLIC").headD "")).toList
  let stream := hexBytes ((v.tagged "STREAM").getD 1 "")
  let stackLine (c : String) : Array K :=
    match v.lines.find? (·.startsWith s!"STACK {c} ") with
    | some l => (((rest l).drop 2).map fun w ↦ K.ofLane (UInt64.ofNat (hexNat w))).toArray
    | none => #[]
  let c1 := stackLine "C1"
  let c2 := stackLine "C2"
  let setup := stackLine "Setup"
  let bytecode := (((v.tagged "BYTECODE").drop 1).map fun w ↦ K.ofLane (UInt64.ofNat (hexNat w))).toArray
  let tr := traceOf shape rows c1 bytecode pub
  IO.println s!"{v.name}"
  let t0 ← IO.monoMsNow
  let myC1 := c1Stack tr
  IO.println s!"  C1 stack {myC1.size} words: {if myC1 == c1 then "same" else s!"DIFFER at {firstDiff myC1 c1}"} ({(← IO.monoMsNow) - t0} ms)"
  let t0 ← IO.monoMsNow
  let mySetup := setupStackOf tr
  IO.println s!"  setup stack: {if mySetup == setup then "same" else s!"DIFFER at {firstDiff mySetup setup}"} ({(← IO.monoMsNow) - t0} ms)"
  let t0 ← IO.monoMsNow
  let hv := heapValues tr (eqKernel [1, 2, 3, 4]) 5
  IO.println s!"  heap values at test challenges: {hv.size} ({(← IO.monoMsNow) - t0} ms)"
  let t0 ← IO.monoMsNow
  let hn := novelOfValuesE tr.shape.heap.h hv
  let tq := treeQuotient tr.shape.heap.h hn
  IO.println s!"  tree quotient: degree {tq.natDegree} ({(← IO.monoMsNow) - t0} ms)"
  let t0 ← IO.monoMsNow
  let cq := constraintQuotient tr 7 (publicWordsOf pub)
  IO.println s!"  constraint quotient: degree {cq.natDegree} ({(← IO.monoMsNow) - t0} ms)"
  (← IO.getStdout).flush
  let H : List UInt8 → Id Digest := fun b ↦ pure (keccak256 b)
  let seed := keccak256 (name ++ iv ++ pub)
  let flock : FlockProver Id := fun _ _ _ ↦ pure default
  let (out, _) := (proveStreamWith (m := Id) H standIn flock .omitted tr).run (Wr.start seed)
  let streamOk := out.stream == stream
  let c1Ok := out.c1.1 == c1
  let c2Ok := out.c2.1 == c2
  let setupOk := out.setup == setup
  let o := run shape iv pub out.stream .omitted .point
  IO.println s!"{v.name}: stream {out.stream.size}/{stream.size} bytes {if streamOk then "same" else s!"DIFFER at {firstDiff out.stream stream}"}; C1 {if c1Ok then "same" else s!"DIFFER at {firstDiff out.c1.1 c1}"}; C2 {if c2Ok then "same" else s!"DIFFER at {firstDiff out.c2.1 c2}"}; setup {if setupOk then "same" else s!"DIFFER at {firstDiff out.setup setup}"}; the Lean verifier on it: accepts {o.accepts}"
  return streamOk && c1Ok && c2Ok && setupOk && o.accepts

def main : IO Unit := do
  let path ← IO.getEnv "UNI_HONEST"
  let some path := path | throw (IO.userError "UNI_HONEST: the vectors file")
  let ls := (← IO.FS.lines path).toList
  let vs := (vectors ls).filter fun v ↦ v.name.endsWith "omitted point honest"
  IO.println s!"{vs.length} honest point-claim vectors"
  let mut ok := true
  for v in vs do
    ok := (← checkVector v) && ok
  if ok then IO.println "all agree" else throw (IO.userError "a disagreement")

end UniCompleteTest

#eval UniCompleteTest.main
