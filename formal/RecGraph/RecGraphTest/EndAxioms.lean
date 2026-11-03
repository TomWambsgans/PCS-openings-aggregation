-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.End

/-!
# Graph = verifier for π1-rec3 uses Lean's three standard axioms only

`Sim/End.lean` (`pi1Sim`, `pi1GraphIsVerifier`) and its composition (`Sim/Compose.lean`, `Sim/Top.lean`,
`Sim/Calls.lean`): run from `formal/EndToEnd` with `lake env lean ../RecGraph/RecGraphTest/EndAxioms.lean`; it prints
nothing when every guard holds.
-/

/-- info: 'RecGraph.Pi1.pi1GraphIsVerifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Pi1.pi1GraphIsVerifier

/-- info: 'RecGraph.Pi1.pi1Sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Pi1.pi1Sim

/-- info: 'RecGraph.Sim.reduce_simQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.reduce_simQ

/-- info: 'RecGraph.Sim.pi1Sim_of_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.pi1Sim_of_reduce

/-- info: 'RecGraph.Sim.calls_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.calls_eq

/-- info: 'RecGraph.Sim.degreeSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.degreeSpec
