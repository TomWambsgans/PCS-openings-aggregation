-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoreFinal
import ZK.CoreBad
import ZK.Budget

/-!
# Zero knowledge, the prover's budget and its failures discharged

**`zeroKnowledge_final`**: `zeroKnowledge_whirD` (`ZK/CoreFinal.lean`) with the prover's permutation
budget `Qp = (2^24 + 2^70)·12` (`hprover_whir`, `ZK/Budget.lean`; the wiring rows are `512` bytes) and
the probability that the statement's prover fails or meets degenerate `α, β` at most
`deltaNone < 2^-162` (`hbad_deployed`, `ZK/CoreBad.lean`). What remains is the deterministic core
`CoreD` (`ZK/CoreDefs.lean`): the formatted skeleton's proof is the statement's prover's, for every
permutation off the degenerate challenges.
-/

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open LeanVM.Parameters LeanVM.Protocol.KeccakHash LeanVM.Prover
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open Primitives
open scoped ENNReal

namespace PcsQuotient.EndToEnd

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

theorem length_stackWordFast (μ R : ℕ) (stack : Array K) (p : ℕ) :
    (stackWordFast μ R stack p).length = 64 := by
  simp only [stackWordFast, stackWordFast.stackWordOf]
  split_ifs <;> simp

/-- **The wiring rows are `512` bytes.** -/
theorem rowsWD_length : ∀ r ∈ rowsWD, r.length ≤ 1564 := by
  intro r hr
  rw [rowsWD_eq, List.mem_map] at hr
  obtain ⟨i, -, rfl⟩ := hr
  have h : ∀ l : List K, (l.flatMap kBytes).length = 8 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, kBytes, LeanVM.Rpm.wordBytes_len, ih]; ring
  rw [h, length_stackWordFast]
  norm_num

/-- **Zero knowledge of the membership proof**, the renderer WHIR's honest prover, the prover's
budget and failures discharged: `ZeroKnowledgeWith` at
`zkBoundEnd ((2^24 + 2^70)·12) fmtBudget (· ↦ deltaNone)`, from the deterministic core `CoreD`. -/
theorem zeroKnowledge_final (s₀ : RpmSimState) (hcore : ∀ stmt w, Relation stmt w → CoreD stmt w) :
    ZeroKnowledgeWith s₀
      (zkSimulator (fun _ ↦ deployedPub deployedRep)
        (fun stmt ↦ deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y
          (Render.whirRenderer deployedRep stmt) inKD sigmaAtD)
        (fun stmt ↦ skelSetup (stmtBytesD stmt) idWD idσD idQD rowsWD) fmt)
      rpmSimOracle (zkBoundEnd ((2 ^ 24 + 2 ^ 70) * 12) fmtBudget fun _ ↦ E2ECompleteness.deltaNone) :=
  zeroKnowledge_whirD _ _ s₀
    (hprover_whir stmtBytesD idWD idσD idQD rowsWD length_rowsWD rowsWD_length) hcore
    (fun stmt w hw _ ↦ hbad_deployed stmt w hw _)

end PcsQuotient.EndToEnd

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_final
