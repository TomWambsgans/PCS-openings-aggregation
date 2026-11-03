-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuitTest.Parse

/-!
# The differential runner: the Lean compiler against the Rust's

`rec-circuit-diff GRAPH`: reads a recorded graph written by `crates/leanvm_rec/tests/lean_circuit.rs`, compiles it
with `RecCircuit.compile` (compiled code, not the kernel; the checker included), and prints the circuit's summary in
the Rust test's format (the shape, the regions and their formula tables, the blocks, the ports, the calls, `κ`, `σ`'s
FNV-1a hash); `diff` it against the Rust's `.circuit` file.
-/

open RecCircuit Primitives

open RecCircuitTest in
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match parseGraph text with
    | .error e => IO.eprintln s!"parse: {e}"; return 2
    | .ok r =>
      let t0 ← IO.monoMsNow
      match compile r with
      | .error e => IO.eprintln s!"the compiler rejects the graph: {e}"; return 1
      | .ok c =>
        let t1 ← IO.monoMsNow
        IO.eprintln s!"compiled in {t1 - t0} ms: {c.nodes.size} expanded nodes, {c.view.producerF.size} values"
        IO.print (circuitText c.circuit)
        return 0
  | _ => IO.eprintln "usage: rec-circuit-diff GRAPH"; return 2
