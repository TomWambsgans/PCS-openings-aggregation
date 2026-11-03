-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Top
import RecGraph.Sim.Compose
import RecGraph.Sim.Flock
import RecGraph.Sim.TablePart
import RecGraph.Sim.Batch
import RecGraph.Sim.Shape

/-!
# `Pi1Sim`, and graph = verifier for π1-rec3

The parts: Flock (`flockSpec`, `Sim/Flock.lean`), the tables (`tableSpec`, `Sim/TablePart.lean`), the constraint
quotient's and the heap's relations (`constraintSpec`, `heapSpec`, `Sim/Relations.lean`), the degree
(`degreeSpec`, `Sim/Compose.lean`), the tail (`tailSpec`, `Sim/Batch.lean`), the shapes (`shapeSpec`,
`Sim/Shape.lean`); composed by `reduce_simQ` (`Sim/Compose.lean`) and `pi1Sim_of_reduce` (`Sim/Top.lean`).
-/

namespace RecGraph.Pi1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph.Sim

/-- **The simulation**: π1-rec3's program computes `UniStatement`'s π1-rec3 verifier's outputs, off the merge
hazard. -/
theorem pi1Sim : Pi1Sim :=
  pi1Sim_of_reduce fun _ _ _ _ st words wordsE hg hseed hcur hch hw hwl ↦
    reduce_simQ partR partR_grows flockSpec tableSpec constraintSpec degreeSpec heapSpec tailSpec shapeSpec
      st words wordsE hg hseed hcur hch hw hwl

/-- **Graph = verifier for π1-rec3, off the merge hazard.** -/
theorem pi1GraphIsVerifier : Pi1GraphIsVerifier := pi1GraphIsVerifier_of_sim pi1Sim

end RecGraph.Pi1
