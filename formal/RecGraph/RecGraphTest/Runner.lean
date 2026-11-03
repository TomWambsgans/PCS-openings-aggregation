-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The hex and element parsers follow
-- `formal/UniStatement/UniStatementTest/Runner.lean`'s.
import RecGraph.Emitted
import RecGraph.Semantics

/-!
# The differential runner

`lake env lean ../RecGraph/RecGraphTest/Runner.lean` (from `formal/EndToEnd`), with the vectors of
`crates/leanvm_rec/tests/lean_graph.rs` (`lean_vectors`) at `$REC_VECTORS` and, optionally, the committed real vector
`crates/leanvm_univariate/tests/vectors/main_line_rec3.txt` at `$REC_REAL`. Compiled evaluation (`#eval`), not the
kernel. For every vector, three runs on the same calldata, compared on every output (each `PCS_OPEN` call's bytes, the
values required zero, the values required nonzero):

1. **the graph, by Lean**: `evalGraph` of π1-rec3's emitted graph (`Emitted.graph`), against
2. **the graph, by Rust**: `leanvm_rec::eval` (`EVALCALL`, `EVALZEROS`, `EVALNONZEROS`): the semantics agree;
3. **the verifier, by Lean**: `UniStatement`'s at π1-rec3 (`verifierOutputsDeployed reference referenceRoots … .rec3
   true`), against (1), and against **the verifier, by Rust** (`rust_verifier_with` at `FLOCK_REC3`: `NATIVECALL`,
   `NATIVEZEROS`, `NATIVENONZEROS`).

Then: the contract's IV the Lean derives for π1-rec3 (`contractIvFor`) is the vectors'; on the real proof, the Lean
verifier's calls are the contract's (`REC_REAL`'s `pcs_open` lines) and every zero holds; streams one byte short or
long have no outputs, by the graph and by the verifier. Last, **an oracle under which the graph and the verifier
differ** (`programmedGap`, see there). It prints one line per test and per vector, a summary, and throws (so `lean`
exits with an error) on any unexpected disagreement.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph

namespace RecGraphTest

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexNat (s : String) : Except String ℕ :=
  s.toList.foldlM (fun acc c ↦ match hexDigit c with
    | some d => pure (16 * acc + d)
    | none => throw s!"not hex: {s}") 0

/-- Bytes from hex. -/
def hexBytes (s : String) : Except String (Array UInt8) := do
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then throw "odd hex"
  let mut out : Array UInt8 := Array.mkEmpty (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexDigit (cs.getD (2 * i) '0'), hexDigit (cs.getD (2 * i + 1) '0') with
    | some a, some b => out := out.push (UInt8.ofNat (16 * a + b))
    | _, _ => throw "not hex"
  return out

/-- Lowercase hex of bytes. -/
def hexOf (b : List UInt8) : String :=
  String.join (b.map fun x ↦
    let d (n : ℕ) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList [d (x.toNat / 16), d (x.toNat % 16)])

def eHex (x : E) : String :=
  s!"{String.ofList (Nat.toDigits 16 (x.limb 0).lane.toNat)}:{String.ofList (Nat.toDigits 16 (x.limb 1).lane.toNat)}:{String.ofList (Nat.toDigits 16 (x.limb 2).lane.toNat)}"

/-- An element as the Rust writes it, `c0:c1:c2` in hex. -/
def eElem (t : String) : Except String E :=
  match t.splitOn ":" with
  | [a, b, c] => do
    let limb (s : String) : Except String UInt64 := UInt64.ofNat <$> hexNat s
    pure (eNew (← limb a) (← limb b) (← limb c))
  | _ => throw s!"not an element of E: {t}"

/-- A count, then that many elements. -/
def elems (ts : List String) : Except String (List E) := do
  match ts with
  | n :: rest =>
    let some k := n.toNat? | throw s!"not a count: {n}"
    if rest.length ≠ k then throw "an element list's length"
    rest.mapM eElem
  | [] => throw "an empty element list"

/-- The tokens of a line. -/
def tokens (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

/-- A vector: the calldata, and the outputs of the Rust graph evaluator and of the Rust verifier. -/
structure Vector' where
  id : String
  iv : Array UInt8
  publicInput : Array UInt8
  stream : Array UInt8
  eval : Outputs
  native : Option Outputs

def parseVector (lines : List (List String)) : Except String Vector' := do
  let byKey (k : String) : Option (List String) := (lines.find? (·.head? == some k)).map (·.drop 1)
  let req (k : String) : Except String (List String) :=
    match byKey k with
    | some ts => pure ts
    | none => throw s!"no {k} line"
  let all (k : String) : Except String (List (List UInt8)) :=
    ((lines.filter (·.head? == some k)).mapM fun ts ↦ (·.toList) <$> hexBytes ((ts.drop 1).headD ""))
  let id := (← req "VECTOR").headD "?"
  let iv ← hexBytes ((← req "IV").headD "")
  let publicInput ← hexBytes ((← req "PUBLIC").headD "")
  let stream ← hexBytes ((← req "STREAM").headD "")
  let eval : Outputs := ⟨← all "EVALCALL", ← elems (← req "EVALZEROS"), ← elems (← req "EVALNONZEROS")⟩
  let native ← match byKey "NATIVE" with
    | some ["ok"] => do
      pure (some ⟨← all "NATIVECALL", ← elems (← req "NATIVEZEROS"), ← elems (← req "NATIVENONZEROS")⟩)
    | _ => pure none
  pure ⟨id, iv, publicInput, stream, eval, native⟩

/-- The vectors of a file: the lines from each `VECTOR` to its `END`. -/
def parseVectors (text : String) : Except String (List Vector') := do
  let lines := (text.splitOn "\n").map tokens |>.filter fun ts ↦ !ts.isEmpty && ts.head? != some "#"
  let mut out : Array Vector' := #[]
  let mut cur : Array (List String) := #[]
  for ts in lines do
    if ts.head? == some "END" then
      out := out.push (← parseVector cur.toList)
      cur := #[]
    else cur := cur.push ts
  return out.toList

/-- The first difference of two outputs, if any. -/
def diff (what : String) (a b : Outputs) : Option String :=
  if a.calls.length != b.calls.length then some s!"{what}: {a.calls.length} calls against {b.calls.length}"
  else match ((a.calls.zip b.calls).zip (List.range a.calls.length)).find? (fun ((x, y), _) ↦ x != y) with
  | some ((x, y), i) => some s!"{what}: call {i} differs:\n  {hexOf x}\n  {hexOf y}"
  | none =>
    if a.zeros != b.zeros then some s!"{what}: zeros {a.zeros.map eHex} against {b.zeros.map eHex}"
    else if a.nonzeros != b.nonzeros then some s!"{what}: nonzeros {a.nonzeros.map eHex} against {b.nonzeros.map eHex}"
    else none

def g : Graph := Emitted.graph

/-- The π1-rec3 verifier's outputs over Keccak-f[1600]. -/
def verifierOut (iv publicInput : List UInt8) (stream : Array UInt8) : Option Outputs :=
  verifierOutputsDeployed reference referenceRoots iv publicInput stream .rec3 true

/-- One vector's three comparisons. -/
def check (v : Vector') : Except String String := do
  let iv := v.iv.toList
  let pub := v.publicInput.toList
  let some lean := evalGraphDeployed g iv pub v.stream | throw s!"{v.id}: the graph has no outputs"
  if let some d := diff s!"{v.id}: Lean graph vs Rust graph" lean v.eval then throw d
  let some ver := verifierOut iv pub v.stream | throw s!"{v.id}: the Lean verifier rejects the stream"
  if let some d := diff s!"{v.id}: Lean graph vs Lean verifier" lean ver then throw d
  let some native := v.native | throw s!"{v.id}: the Rust verifier rejects the stream"
  if let some d := diff s!"{v.id}: Lean verifier vs Rust verifier" ver native then throw d
  let holds := lean.zeros.all (· == 0)
  return s!"{v.id}: {lean.calls.length} calls ({(lean.calls.map List.length)} bytes), {lean.zeros.length} zeros \
    ({if holds then "all hold" else "some fail"}), {lean.nonzeros.length} nonzeros: the four agree"

/-! ### An oracle under which the graph and the verifier differ

`combine` (`Relations::combine`) merges a relation's points that are equal, and a point into a longer one it is a
prefix of. The verifier on `E` (the Rust's `rust_verifier`, and `UniStatement`) compares the points' **values**; the
recorder compares its symbols, so the graph (the contract, π2's circuit) merges by **identity**. They differ when two
of the verifier's points are related by value but not as symbols. On `C1`, the BLAKE2S table's `q_flock` slot terms
are at `y = coordinatesAt t (coordinateFunctionals 18)` (18 coordinates), and the ring switch's term at Flock's point
(26: the lincheck's 8 challenges reversed, then the zerocheck's last 18). A slot term reads as many coordinates as its
point has (`weightAt`'s `rowLen`), so if Flock's point starts with `y` the verifier reads the slot terms at Flock's
26 coordinates, the graph at `y`'s 18: `C1`'s weight differs, and so does the batch's terminal.

`programmed` answers Keccak-f[1600] but at chosen calls, where it sets the digest's challenge: `t` to a fixed `t*`,
and Flock's point's first 18 coordinates to `y(t*)`. Every query is distinct (checked), so a permutation answers the
same: `GraphIsVerifier` fails for π1-rec3's graph at that permutation. A control sets `t` alone: they agree. -/

/-- Byte-reverse a word. -/
def bswap (w : UInt64) : UInt64 :=
  (List.range 8).foldl (fun acc k ↦ (acc <<< 8) ||| ((w >>> (8 * k).toUInt64) &&& 0xff)) 0

/-- A state whose digest's challenge is `c`: the digest's bytes `8 .. 32` are limbs `2, 1, 0` big-endian, lanes `1, 2,
3` little-endian. -/
def withChallenge (s : KeccakState) (c : E) : KeccakState :=
  ((s.set 1 (bswap (c.limb 2).lane)).set 2 (bswap (c.limb 1).lane)).set 3 (bswap (c.limb 0).lane)

/-- The oracle's state: the calls made, and the states queried. -/
abbrev OracleM := StateM (ℕ × Array KeccakState × Array KeccakState)

/-- Keccak-f[1600], but at the calls `overrides` names, whose answers carry the given challenge. -/
def programmed (overrides : List (ℕ × E)) (s : KeccakState) : OracleM KeccakState := do
  let (n, ins, outs) ← get
  let out := match overrides.lookup n with
    | some c => withChallenge (keccakF1600 s) c
    | none => keccakF1600 s
  set (n + 1, ins.push s, outs.push out)
  return out

/-- Each challenge's last permutation call, in drawing order: the seed is call `0` (80 bytes, one block), then each
hash of the graph takes `(32 + to − from) / 136 + 1`. -/
def challengeCalls : List ℕ :=
  let lens := g.nodes.toList.filterMap fun n ↦ match n with
    | .hash _ fr upto => some (32 + upto - fr)
    | _ => none
  (lens.foldl (fun (acc : ℕ × Array ℕ) len ↦ (acc.1 + len / 136 + 1, acc.2.push (acc.1 + len / 136))) (1, #[])).2.toList

/-- `t*`, and the overrides: `t` (challenge 49) is `t*`; the lincheck's rounds (challenges 35..42, Flock's point's
first 8 coordinates reversed) and the zerocheck's rounds 11..20 (challenges 16..25, its next 10) are `y(t*)`. -/
def tStar : E := eNew 0x1234 0x5678 0x9abc

def yStar : List E := coordinatesAt tStar (coordinateFunctionals 18)

def gapOverrides (withFlock : Bool) : List (ℕ × E) :=
  let at_ (i : ℕ) : ℕ := challengeCalls.getD i 0
  (if withFlock then
    (List.range 8).map (fun j ↦ (at_ (42 - j), yStar.getD j 0)) ++
      (List.range 10).map fun i ↦ (at_ (16 + i), yStar.getD (8 + i) 0)
  else []) ++ [(at_ 49, tStar)]

/-- The graph's and the verifier's outputs under the programmed oracle, whether they queried the same distinct states,
and the verifier's challenges at the programmed places. -/
def gapRun (withFlock : Bool) (iv pub : List UInt8) (stream : Array UInt8) :
    Option Outputs × Option Outputs × Bool × Bool × List E := Id.run do
  let F := programmed (gapOverrides withFlock)
  let (graphOut, (n1, ins1, outs1)) := (evalGraph (m := OracleM) F g iv pub stream).run (0, #[], #[])
  let (verOut, (n2, ins2, _)) :=
    (verifierOutputsWith (m := OracleM) F reference referenceRoots iv pub stream .rec3 true).run (0, #[], #[])
  let (o, _) := (runWithFs (m := OracleM) F reference iv pub stream (.flock flockMain) .point .rec3 true).run
    (0, #[], #[])
  let distinct (a : Array KeccakState) : Bool :=
    (List.range a.size).all fun i ↦ (List.range i).all fun j ↦ a.getD i default != a.getD j default
  let same := n1 == n2 && ins1 == ins2
  let ch := o.chan.challenges
  let point := (List.range 8).map (fun j ↦ ch.getD (42 - j) 0) ++ (List.range 10).map (fun i ↦ ch.getD (16 + i) 0)
  return (graphOut, verOut, same, distinct ins1 && distinct outs1, point ++ [ch.getD 49 0])

end RecGraphTest

open RecGraphTest in
#eval show IO Unit from do
  let path ← IO.getEnv "REC_VECTORS"
  let some path := path | throw (IO.userError "REC_VECTORS unset")
  let text ← IO.FS.readFile path
  let vectors ← IO.ofExcept (parseVectors text)
  IO.println s!"π1-rec3's graph: {g.nodes.size} nodes, {g.zero.length} zeros, {g.nonzero.length} nonzeros, \
    {g.calls.length} calls, a stream of {g.streamLen} bytes; {vectors.length} vectors"
  -- The contract's IV for π1-rec3, by the Lean (`contractIvFor`), is the vectors'.
  let iv := contractIvFor reference (.flock flockMain) .rec3 true programIv referenceRoots
  let mut failures : Array String := #[]
  match vectors.head? with
  | some v =>
    if iv.toArray == v.iv then IO.println s!"the contract's IV for π1-rec3 (contractIvFor): {hexOf iv}, the vectors'"
    else failures := failures.push s!"IV: Lean {hexOf iv}, Rust {hexOf v.iv.toList}"
  | none => failures := failures.push "no vectors"
  for v in vectors do
    match check v with
    | .ok line => IO.println line
    | .error e => IO.println s!"FAIL {e}"; failures := failures.push e
  -- The real proof: the Lean verifier's calls are the contract's, and it accepts.
  if let some real ← IO.getEnv "REC_REAL" then
    let text ← IO.FS.readFile real
    let lines := (text.splitOn "\n").map tokens
    let get (k : String) : List String := ((lines.find? (·.head? == some k)).map (·.drop 1)).getD []
    let calldata ← IO.ofExcept (hexBytes ((get "calldata").headD ""))
    let calls ← IO.ofExcept ((lines.filter (·.head? == some "pcs_open")).mapM fun ts ↦
      (·.toList) <$> hexBytes ((ts.drop 1).headD ""))
    let pub := (calldata.extract 4 36).toList
    let stream := calldata.extract 36 calldata.size
    match verifierOut iv pub stream, evalGraphDeployed g iv pub stream with
    | some ver, some lean =>
      let accepts := ver.zeros.all (· == 0)
      if ver.calls == calls && lean.calls == calls && accepts then
        IO.println s!"the real proof (REC_REAL): the Lean verifier's and the graph's {calls.length} calls are the \
          contract's, every zero holds"
      else failures := failures.push s!"the real proof: calls agree {ver.calls == calls}, {lean.calls == calls}; \
        accepts {accepts}"
      -- Streams one byte short or long: no outputs, by the graph and by the verifier.
      let short := stream.extract 0 (stream.size - 1)
      let long := stream.push 0
      let none_ (o : Option Outputs) : Bool := o.isNone
      if none_ (evalGraphDeployed g iv pub short) && none_ (verifierOut iv pub short) &&
          none_ (evalGraphDeployed g iv pub long) && none_ (verifierOut iv pub long) then
        IO.println "a stream one byte short or long: no outputs, by the graph and by the verifier"
      else failures := failures.push "a stream of another length has outputs"
    | _, _ => failures := failures.push "the real proof: no outputs"
  -- The programmed oracle: the graph and the verifier differ; the control (t alone) agrees.
  match vectors.head? with
  | some v =>
    let (gc, vc, sameC, distinctC, _) := gapRun false v.iv.toList v.publicInput.toList v.stream
    let (gg, vg, sameG, distinctG, programmedAt) := gapRun true v.iv.toList v.publicInput.toList v.stream
    let hit := programmedAt == yStar ++ [tStar]
    match gc, vc, gg, vg with
    | some a, some b, some c, some d =>
      if diff "" a b == none && sameC && distinctC then
        IO.println "programmed oracle, control (t = t* alone): the graph and the verifier agree"
      else failures := failures.push "programmed oracle: the control disagrees"
      match diff "programmed oracle (Flock's point starting with y(t*)): graph vs verifier" c d with
      | some d' =>
        if sameG && distinctG && hit then
          IO.println s!"EXPECTED GAP, {d'}\n  (the same {(gapOverrides true).length} programmed answers, every query \
            distinct: a permutation's; the zeros: graph {c.zeros.map eHex}, verifier {d.zeros.map eHex})"
        else failures := failures.push s!"programmed oracle: queries same {sameG}, distinct {distinctG}, hit {hit}"
      | none => IO.println "programmed oracle: the graph and the verifier agree (no gap found)"
    | _, _, _, _ => failures := failures.push "programmed oracle: no outputs"
  | none => pure ()
  if failures.isEmpty then IO.println s!"all {vectors.length} vectors agree"
  else throw (IO.userError s!"{failures.size} failures")
