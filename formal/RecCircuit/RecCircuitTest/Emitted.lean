-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuitTest.Parse
import RecCircuit.Sound
import RecGraph.Emitted

/-!
# The compiler on `RecGraph.Emitted.graph`, the very term `pi1rec3_end` is about

`rec-circuit-emitted GRAPH`: reads π1-rec3's graph as `crates/leanvm_rec/tests/lean_circuit.rs` writes it (for its IV),
checks that it is `RecGraph.Emitted.graph` with `RecGraph.Emitted.rootsAt` field by field, then runs
`RecCircuit.compile (ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv)` (compiled code) and prints the
circuit's summary, to `diff` against the Rust's `.circuit` file.
-/

open RecCircuit Primitives RecCircuitTest

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match parseGraph text with
    | .error e => IO.eprintln s!"parse: {e}"; return 2
    | .ok r =>
      let e := ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt r.iv
      let same := r.graph.nodes == e.graph.nodes && r.graph.zero == e.graph.zero &&
        r.graph.nonzero == e.graph.nonzero && r.graph.kernels == e.graph.kernels && r.graph.calls == e.graph.calls &&
        r.graph.streamLen == e.graph.streamLen && r.rootsAt == e.rootsAt
      if !same then IO.eprintln "the graph file is not RecGraph.Emitted.graph"; return 3
      IO.eprintln "the graph file is RecGraph.Emitted.graph"
      let t0 ← IO.monoMsNow
      match compile e with
      | .error m => IO.eprintln s!"the compiler rejects RecGraph.Emitted.graph: {m}"; return 1
      | .ok c =>
        let t1 ← IO.monoMsNow
        IO.eprintln s!"compiled RecGraph.Emitted.graph in {t1 - t0} ms: {c.nodes.size} expanded nodes"
        IO.print (circuitText c.circuit)
        return 0
  | _ => IO.eprintln "usage: rec-circuit-emitted GRAPH"; return 2
