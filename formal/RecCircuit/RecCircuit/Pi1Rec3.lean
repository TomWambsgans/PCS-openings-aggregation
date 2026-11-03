-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.End
import RecGraph.Emitted

/-!
# π2's circuit for π1-rec3

The end theorem at π1-rec3's recorded graph (`RecGraph.Emitted.graph`, its roots at `RecGraph.Emitted.rootsAt`) and
any π1 contract IV: if the compiler accepts it, every witness satisfying π2's PIOP has ports and rebuilt `PCS_OPEN`
inputs equal to π1-rec3's graph's outputs over Keccak-f[1600] (`EndStatement`). That the compiler accepts it is a
run, not a proof: `rec-circuit-diff` compiles the graph the Rust emits (`crates/leanvm_rec/tests/lean_circuit.rs`,
`pi1_rec3`) and prints a circuit identical to the Rust's.
-/

namespace RecCircuit

open Primitives

/-- **π2's circuit for π1-rec3 carries π1-rec3's outputs.** -/
theorem pi1rec3_end {iv : List UInt8} {c : Compiled}
    (hc : compile (ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) = .ok c) {pub : ℕ → List F192}
    {w : ℕ → K} (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    Compiled.EndStatement RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv c w :=
  Compiled.compile_sound_end hc hw

end RecCircuit
