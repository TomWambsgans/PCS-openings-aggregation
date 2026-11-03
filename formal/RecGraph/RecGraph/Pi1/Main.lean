-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Pi1.Verifier
import RecGraph.Commute
import RecGraph.Hazard

/-!
# Graph = verifier for π1-rec3, off the merge hazard: the statement, and its reduction

* `Pi1GraphIsVerifier`: **the target**. For every permutation `π`, IV, public input and stream off the merge hazard
  (`MergeHazard`, `Hazard.lean`), π1-rec3's recorded graph (`Pi1.pi1Graph`, the Lean recording of the program
  `Pi1.pi1Rec3`, equal node for node to the Rust's `Emitted.graph`: `RecGraphTest/Pi1Check.lean`) evaluates to
  `UniStatement`'s π1-rec3 verifier's outputs (`verifierOutputsWith … .rec3 true`).
* `evalGraph_recordedGraph` (proved): the graph's evaluation is the program's run on `E` (`record_eval`), so the target
  is `Pi1Sim`, a statement about the program alone: its run (each operation worth its meaning, `op_val`) computes
  `UniStatement`'s outputs.
* `pi1GraphIsVerifier_of_sim` (proved): `Pi1Sim → Pi1GraphIsVerifier`.

`Pi1Sim` is the simulation of `UniStatement`'s π1-rec3 verifier by the program, function by function; it is proved in
`Sim/End.lean` (`pi1Sim`, and `pi1GraphIsVerifier : Pi1GraphIsVerifier`, on the three standard axioms:
`RecGraphTest/EndAxioms.lean`). It is also checked by the differential runner on the real proof and 24 mutated and
random streams (`RecGraphTest/Runner.lean`, with `Pi1Check.lean`'s equality of the graphs).
-/

namespace RecGraph.Pi1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement

/-- The program's values on `E`: `Prog.run` of π1-rec3's verifier from the recorder's start. -/
abbrev runVals (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) : Array Value :=
  (pi1Rec3.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2

/-- **Graph = verifier for π1-rec3, off the merge hazard.** -/
def Pi1GraphIsVerifier : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
    ¬ MergeHazard π iv publicInput.toList stream →
      evalGraph (m := Id) (fun s ↦ pure (π s)) (recordedGraph pi1Rec3) iv publicInput.toList stream =
        verifierOutputsWith (m := Id) (fun s ↦ pure (π s)) reference referenceRoots iv publicInput.toList stream .rec3
          true

/-- **A recorded graph's evaluation is its program's run on `E`** (`record_eval`), for any program: on a stream of
the graph's length, the outputs read off the run's values; on another, none. -/
theorem evalGraph_recorded {α : Type} (π : KeccakState → KeccakState) (iv publicInput : List UInt8)
    (stream : Array UInt8) (p : Prog α) (g : Graph) (hn : g.nodes = (p.record RecState.start).2.nodes)
    (hk : g.kernels = (p.record RecState.start).2.kernels) :
    evalGraph (m := Id) (fun s ↦ pure (π s)) g iv publicInput stream =
      if stream.size = g.streamLen then
        some (outputsOf g stream
          (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2)
      else none := by
  have h : Id.run (evalNodes (m := Id) (fun s ↦ pure (π s)) g iv publicInput stream) =
      (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2 := by
    have he := record_eval π iv publicInput stream p g.calls g.streamLen
    rw [← he]
    unfold evalNodes RecState.graph
    rw [hn, hk]
  unfold evalGraph
  split
  · rw [← h]
    rfl
  · rfl

/-- `evalGraph_recorded` for `recordedGraph`. -/
theorem evalGraph_recordedGraph (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)
    (p : Prog ReducedS) :
    evalGraph (m := Id) (fun s ↦ pure (π s)) (recordedGraph p) iv publicInput stream =
      if stream.size = (recordedGraph p).streamLen then
        some (outputsOf (recordedGraph p) stream
          (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2)
      else none :=
  evalGraph_recorded π iv publicInput stream p (recordedGraph p) rfl rfl

/-- **What is left**: the program's run on `E` computes `UniStatement`'s π1-rec3 outputs, off the merge hazard. -/
def Pi1Sim : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
    ¬ MergeHazard π iv publicInput.toList stream →
      (if stream.size = (recordedGraph pi1Rec3).streamLen then
          some (outputsOf (recordedGraph pi1Rec3) stream
            (pi1Rec3.run π iv publicInput.toList stream
              (RecState.start, evalAll π iv publicInput.toList stream RecState.start)).2.2)
        else none) =
        verifierOutputsWith (m := Id) (fun s ↦ pure (π s)) reference referenceRoots iv publicInput.toList stream .rec3
          true

/-- **The simulation gives graph = verifier.** -/
theorem pi1GraphIsVerifier_of_sim (h : Pi1Sim) : Pi1GraphIsVerifier := by
  intro π iv publicInput stream hz
  rw [evalGraph_recordedGraph]
  exact h π iv publicInput stream hz

end RecGraph.Pi1
