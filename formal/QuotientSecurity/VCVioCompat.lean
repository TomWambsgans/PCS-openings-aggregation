-- Not from leanVM: written for the move of these proofs to VCVio afa6593f, whose measure-based
-- probability API retired some lemmas they used. MIT OR Apache-2.0; see NOTICE.md.
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Sum
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Event lemmas retired from VCVio

VCVio states probabilities as `Pr{let x ← mx}[p x]`, the mass of an event under the computation's
output measure. A few lemmas of its earlier discrete API have no counterpart there; they are
proved here from the current ones.
-/

open OracleComp

namespace QuotientSecurity

/-- Split an event, on the possible outputs, into a main event and an exceptional one. -/
theorem prEvent_le_add_of_imp_or {α : Type} {mx : ProbComp α} {p q r : α → Prop}
    (h : ∀ x ∈ support mx, p x → q x ∨ r x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] + Pr{let x ← mx}[r x] :=
  (prEvent_mono_of_support mx p (fun x => q x ∨ r x) h).trans (prEvent_or_le mx q r)

end QuotientSecurity
