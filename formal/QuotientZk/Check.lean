-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Rom.Main
import VCVio.OracleComp.RunIO

/-!
# The simulator runs

`sim` is a computable definition (not `noncomputable`): Lean compiles it. Here it is run, with
VCVio's `OracleComp.runIO` (the uniform draws from the system's randomness), on a toy protocol: two
Fiat–Shamir steps, a message, an opened and an unopened leaf, a public query. The skeleton returns
what it saw of the challenges' count and the leaves' digests' equality, which do not depend on the
draws, so the output is fixed.

`#print axioms sim` lists `Classical.choice`: it enters only through the proof field of VCVio's
`SampleableType` (the statement that `$ᵗ` is uniform, `SampleableType.mk`'s second argument), not
through anything the simulator computes; a `ProbComp` built from `pure` and `bind` alone uses no
axiom (`QuotientZk.Check.noAxioms`).
-/

open OracleComp OracleSpec

namespace QuotientZk.Check

/-- A toy protocol: inputs `Bool`, answers `Fin 4`, one table with two positions. -/
def toyP : Proto Unit Bool (Fin 4) ℕ Unit Bool where
  n := 2
  msgFn _ h := h.length
  cK _ := 1
  rowFn _ _ _ x := x
  opened _ _ x := x

/-- Its skeleton: a challenge, a message, the two leaves, a public query, a challenge. -/
def toySkel : OracleComp (OpSpec Bool (Fin 4) ℕ Unit Bool) (ℕ × Bool) := do
  let _ ← liftM ((OpSpec Bool (Fin 4) ℕ Unit Bool).query (.chal true))
  let m ← liftM ((OpSpec Bool (Fin 4) ℕ Unit Bool).query .msg)
  let a ← liftM ((OpSpec Bool (Fin 4) ℕ Unit Bool).query (.leaf () true))
  let b ← liftM ((OpSpec Bool (Fin 4) ℕ Unit Bool).query (.pub true))
  let _ ← liftM ((OpSpec Bool (Fin 4) ℕ Unit Bool).query (.chal false))
  return (m, decide (a = b))

/-- The simulated view: the message is the number of challenges, as the honest one. -/
def toySimV (_ : List (Fin 4)) : ProbComp (View ℕ Bool Unit Bool) :=
  pure ⟨fun c => c, fun _ x => x⟩

/-- The opened leaf `true` hashes the row `true` and the public query asks `true`: the same digest.
The message after one challenge is `1`. -/
def runSim : IO (ℕ × Bool) := do
  let z ← OracleComp.runIO (sim toyP toySimV toySkel [])
  return z.1

/-- info: (1, true) -/
#guard_msgs in
#eval runSim

def noAxioms : ProbComp ℕ := pure 3 >>= fun n => pure (n + 1)

/-- info: 'QuotientZk.Check.noAxioms' does not depend on any axioms -/
#guard_msgs in
#print axioms noAxioms

end QuotientZk.Check
