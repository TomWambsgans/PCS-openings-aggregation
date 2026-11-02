-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoreMain
import ZK.Computable

/-!
# The closed zero-knowledge theorem with the compiled simulator

`zeroKnowledge_closed` (`ZK/CoreMain.lean`) proves `ZeroKnowledgeWith` with no hypothesis for the
simulator `zkSimulator (fun _ ↦ deployedPub deployedRep) (fun stmt ↦ deployedSimV deployedRep P₀D
(stmtWD stmt) F192.Y (Render.whirRenderer deployedRep stmt) inKD sigmaAtD) (fun stmt ↦ skelSetup
(stmtBytesD stmt) idWD idσD idQD rowsWD) fmt`, its samplers of `K` and `E` `formal/Field`'s
`instSampleableTypeF64`, `instSampleableTypeF192` (uniform words, the limbs of three uniform words;
`ZK/CoreDefs.lean` selects them, as here). Of its parts `deployedSimV`, `sigmaAtD`,
`Render.whirRenderer` and the wiring codeword's rows `rowsWD` are `noncomputable`. Here:

* **`rowsWDc`**: `rowsWD`, compiled (`rowsWDc_eq`): the `2^19` rows of the wiring table's WHIR word,
  each `64` words little-endian;
* **`zkSimulatorClosed`**: `zkSimulatorC` (`ZK/Computable.lean`: the compiled view simulator
  `deployedSimVc`, the compiled renderer `whirRendererC`) at the deployed skeleton, **equal to
  `zeroKnowledge_closed`'s simulator** (`zkSimulatorClosed_eq`, an equality of functions);
* **`zeroKnowledge_closed_computable`**: `zeroKnowledge_closed` for it, no hypothesis.

The audit: `zkSimulatorClosed` reaches no axiom outside proofs and types and no non-core
`noncomputable`, `implemented_by`, `extern` or `opaque` constant (`#computational_axioms`), and it is
a `def`, so it is compiled. Its cost: `ZK/Computable.lean`, "The simulator and its cost"; `rowsWDc`
adds the wiring word (`2^25` words by the additive transform) and its bytes, once.
-/

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open Primitives
open scoped ENNReal

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

namespace PcsQuotient.EndToEnd

/-- **The wiring codeword's rows, compiled** (`rowsWD`). -/
def rowsWDc : List (List UInt8) :=
  (List.range (2 ^ 19)).map fun i ↦
    (stackWordFast (cellVars logRows) 1 (membership logRows).wiringTable i).flatMap kBytes

theorem rowsWDc_eq : rowsWDc = rowsWD :=
  (rfl : rowsWDc = (List.range (2 ^ 19)).map fun i ↦
    (stackWordFast (cellVars logRows) 1 (membership logRows).wiringTable i).flatMap kBytes).trans
    rowsWD_eq.symm

attribute [irreducible] rowsWDc

/-- **The closed theorem's simulator, compiled**: `zkSimulatorC` at the deployed skeleton. -/
def zkSimulatorClosed : Statement → StateT RpmSimState ProbComp (Option Proof) :=
  zkSimulatorC stmtBytesD idWD idσD idQD rowsWDc

/-- **`zkSimulatorClosed` is `zeroKnowledge_closed`'s simulator.** -/
theorem zkSimulatorClosed_eq :
    zkSimulatorClosed =
      zkSimulator (fun _ ↦ deployedPub deployedRep)
        (fun stmt ↦ deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y
          (Render.whirRenderer deployedRep stmt) inKD sigmaAtD)
        (fun stmt ↦ skelSetup (stmtBytesD stmt) idWD idσD idQD rowsWD) fmt := by
  rw [zkSimulatorClosed.eq_1, zkSimulatorC_eq, rowsWDc_eq]

/-- **Zero knowledge of the membership proof with the compiled simulator**: `zeroKnowledge_closed`
with its simulator replaced by `zkSimulatorClosed` (`zkSimulatorClosed_eq`), no hypothesis:
`ZeroKnowledgeWith` at `zkBoundEnd ((2^24 + 2^70)·12) fmtBudget (· ↦ deltaNone)`. -/
theorem zeroKnowledge_closed_computable (s₀ : RpmSimState) :
    ZeroKnowledgeWith s₀ zkSimulatorClosed rpmSimOracle
      (zkBoundEnd ((2 ^ 24 + 2 ^ 70) * 12) fmtBudget fun _ ↦ E2ECompleteness.deltaNone) := by
  rw [zkSimulatorClosed_eq]
  exact zeroKnowledge_closed s₀

end PcsQuotient.EndToEnd

/-! ## Axioms and the audit -/

/--
info: 'PcsQuotient.EndToEnd.zeroKnowledge_closed_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_closed_computable

/--
info: 'PcsQuotient.EndToEnd.zkSimulatorClosed_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.zkSimulatorClosed_eq

/--
info: PcsQuotient.EndToEnd.zkSimulatorClosed: computational axioms [], non-core implemented_by/extern/opaque [], non-core noncomputable []
-/
#guard_msgs in
#computational_axioms PcsQuotient.EndToEnd.zkSimulatorClosed
