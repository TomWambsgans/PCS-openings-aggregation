-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Compile

/-!
# The differential runner: the Lean compiler against the Rust's

`rec-circuit-diff GRAPH`: reads a recorded graph written by `crates/leanvm_rec/tests/lean_circuit.rs`, compiles it
with `RecCircuit.compileRaw` (compiled code, not the kernel), and prints the circuit's summary in the Rust test's
format (the shape, the regions and their formula tables, the blocks, the ports, the calls, `κ`, `σ`'s FNV-1a hash);
`diff` it against the Rust's `.circuit` file.
-/

open RecCircuit Primitives

namespace RecCircuitTest

def hexNat (n : ℕ) : String := String.ofList (Nat.toDigits 16 n)

def hexK (k : K) : String := hexNat (F64.toU64 k).toNat

def parseHexChar (c : Char) : ℕ :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseHex (s : String) : ℕ := s.foldl (fun acc c => 16 * acc + parseHexChar c) 0

def parseBytes (s : String) : List UInt8 :=
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i => (16 * parseHexChar (cs.getD (2 * i) '0') + parseHexChar (cs.getD (2 * i + 1) '0')).toUInt8

def nat (s : String) : ℕ := s.toNat!

def words (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

def parseNode (line : String) : Except String Node :=
  match words line with
  | ["C", a, b, c] => pure (.const (nat a).toUInt64 (nat b).toUInt64 (nat c).toUInt64)
  | ["S", k] => pure (.statement (nat k))
  | ["I", o, l] => pure (.input (nat o) (nat l))
  | ["A", a, b] => pure (.add (nat a) (nat b))
  | ["M", a, b] => pure (.mul (nat a) (nat b))
  | ["D"] => pure .seed
  | ["H", s, f, t] => pure (.hash (nat s) (nat f) (nat t))
  | ["L", h] => pure (.low (nat h))
  | ["N", h] => pure (.narrow (nat h))
  | ["B", v, s, w] => pure (.bits (nat v) (nat s) (nat w))
  | ["W", k, n] => pure (.ringWeight (nat k) (nat n))
  | _ => throw s!"bad node line {line}"

def parseWord (w : String) : Except String Word :=
  match w.toList with
  | 'n' :: rest => pure (.node (String.ofList rest).toNat!)
  | 'c' :: rest => pure (.const (parseHex (String.ofList rest)))
  | 't' :: rest => pure (.stream (String.ofList rest).toNat!)
  | _ => throw s!"bad word {w}"

/-- The graph file. -/
def parseGraph (text : String) : Except String Recorded := do
  let lines := (text.splitOn "\n").toArray
  let mut i := 0
  let next := fun (i : ℕ) => lines.getD i ""
  if next i != "graph" then throw "not a graph"
  i := i + 1
  let iv := match words (next i) with
    | ["iv", h] => parseBytes h
    | _ => []
  i := i + 1
  let streamLen := match words (next i) with
    | ["stream_len", n] => nat n
    | _ => 0
  i := i + 1
  let rootsAt := match words (next i) with
    | "roots_at" :: rs => rs.map nat
    | _ => []
  i := i + 1
  let n := match words (next i) with
    | ["nodes", n] => nat n
    | _ => 0
  i := i + 1
  let mut nodes : Array Node := #[]
  for _ in [0:n] do
    nodes := nodes.push (← parseNode (next i))
    i := i + 1
  let zero := match words (next i) with
    | "zero" :: _ :: ids => ids.map nat
    | _ => []
  i := i + 1
  let nonzero := match words (next i) with
    | "nonzero" :: _ :: ids => ids.map nat
    | _ => []
  i := i + 1
  let nk := match words (next i) with
    | ["kernels", n] => nat n
    | _ => 0
  i := i + 1
  let mut kernels : Array (List ℕ) := #[]
  for _ in [0:nk] do
    kernels := kernels.push (match words (next i) with
      | "kernel" :: _ :: ids => ids.map nat
      | _ => [])
    i := i + 1
  let nc := match words (next i) with
    | ["calls", n] => nat n
    | _ => 0
  i := i + 1
  let mut calls : List (List Word) := []
  for _ in [0:nc] do
    match words (next i) with
    | "call" :: _ :: ws => calls := calls ++ [← ws.mapM parseWord]
    | _ => throw "bad call"
    i := i + 1
  return { graph := { nodes, zero, nonzero, kernels, calls, streamLen }, rootsAt, iv }

def polyText (p : Poly) : String :=
  let lin := p.linear.foldl (fun s t => s ++ s!" {t.1}:{hexK t.2}") ""
  let quad := p.quadratic.foldl (fun s t => s ++ s!" {t.1}:{t.2.1}:{hexK t.2.2}") ""
  s!"E {p.linear.length}{lin} {p.quadratic.length}{quad}"

def formulaText : Formula → String
  | .forward => "F"
  | .expr p => polyText p
  | .port limbs => s!"P {limbs.length}" ++ limbs.foldl (fun s l => s ++ s!" {l}") ""

def sourceText : Source → String
  | .statement => "S"
  | .root i => s!"R {i}"
  | .element i => s!"E {i}"
  | .zero => "Z"
  | .pad => "P"

def callWordText : CallWord → String
  | .const w => s!" C{hexNat w}"
  | .root i => s!" R{i}"
  | .element i => s!" E{i}"
  | .pair e c => s!" Q{e}:{c}"

def fnv (xs : Array ℕ) : UInt64 :=
  xs.foldl (fun h x => (h ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

def circuitText (c : Circuit) : String := Id.run do
  let mut out : Array String := #["circuit", s!"log_n {c.logN} log_width {c.logWidth}", s!"regions {c.regions.size}"]
  for r in c.regions do
    out := out.push s!"region {r.name}"
    for f in r.roles do out := out.push s!" {formulaText f}"
  out := out.push s!"blocks {c.blocks.size}"
  for b in c.blocks do out := out.push s!"block {b.row} {b.logRows} {b.region}"
  out := out.push s!"ports {c.ports.size}"
  for p in c.ports do out := out.push s!"port {p.position} {sourceText p.source}"
  out := out.push s!"calls {c.calls.length}"
  for call in c.calls do
    out := out.push (s!"call {call.length}" ++ call.foldl (fun s w => s ++ callWordText w) "")
  out := out.push s!"kappa {c.kappa.size}"
  for (i, k) in c.kappa do out := out.push s!"k {i} {hexK k}"
  out := out.push s!"sigma {c.sigma.size} {hexNat (fnv c.sigma).toNat}"
  out := out.push "end"
  return "\n".intercalate out.toList ++ "\n"

end RecCircuitTest

open RecCircuitTest in
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match parseGraph text with
    | .error e => IO.eprintln s!"parse: {e}"; return 2
    | .ok r =>
      let t0 ← IO.monoMsNow
      match compileRaw r with
      | .error e => IO.eprintln s!"the compiler rejects the graph: {e}"; return 1
      | .ok c =>
        let t1 ← IO.monoMsNow
        IO.eprintln s!"compiled in {t1 - t0} ms: {c.nodes.size} expanded nodes, {c.view.producerF.size} values"
        IO.print (circuitText c.circuit)
        return 0
  | _ => IO.eprintln "usage: rec-circuit-diff GRAPH"; return 2
