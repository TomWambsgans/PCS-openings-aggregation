-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Node
import RecGraph.Semantics
import RecGraph.Record
import RecGraph.Commute
import RecGraph.Values
import RecGraph.Hazard

/-!
# RecGraph: π1-rec3's recorded verifier graph, its meaning, and the recorder

The recursion's outer proof π2 proves a circuit compiled from the **recorded operation graph** of the inner proof π1's
verifier (`crates/leanvm_rec`, π1-rec3: `FLOCK_REC3`, `FsShape::Rec3`). This library is the design-independent half of
"compiler correctness" (`README.md` here): the graph (`Node`, `Graph`; π1-rec3's is `Emitted.lean`, written by the
Rust, data only), its meaning over any permutation (`evalGraph`), the target statement "graph = verifier"
(`GraphIsVerifier`, against `UniStatement`'s π1-rec3: `UniStatement/Rec.lean`), and the Lean recorder (`Record.lean`)
with "recording commutes with evaluation" (`Commute.lean`, `Values.lean`).

The build fails if a definition or theorem below uses an axiom beyond Lean's three standard ones.
-/

/-- info: 'RecGraph.evalGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.evalGraph

/-- info: 'RecGraph.GraphIsVerifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.GraphIsVerifier

/-- info: 'UniStatement.runFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.runFs

/-- info: 'UniStatement.verifyWithFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.verifyWithFs

/-- info: 'UniStatement.reduceWithFs_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.reduceWithFs_main

/-- info: 'UniStatement.runFs_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.runFs_main

/-- info: 'RecGraph.run_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.run_vals

/-- info: 'RecGraph.record_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.record_eval

/-- info: 'RecGraph.new_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.new_val

/-- info: 'RecGraph.constant_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.constant_val

/-- info: 'RecGraph.add_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.add_val

/-- info: 'RecGraph.mul_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.mul_val

/-- info: 'RecGraph.new_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.new_inv

/-- info: 'RecGraph.add_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.add_inv

/-- info: 'RecGraph.mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.mul_inv

/-- info: 'RecGraph.start_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.start_inv

/-- info: 'RecGraph.op_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.op_val

/-- info: 'RecGraph.op_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.op_inv

/-- info: 'RecGraph.op_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.op_lt

/-- info: 'RecGraph.record_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.record_inv

/-- info: 'RecGraph.sample_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.sample_val

/-- info: 'RecGraph.input_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.input_val

/-- info: 'RecGraph.ringWeight_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.ringWeight_val

/-- info: 'RecGraph.bits_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.bits_val

/-- info: 'RecGraph.hazard_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.hazard_card

/-- info: 'RecGraph.hazard_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.hazard_prob
