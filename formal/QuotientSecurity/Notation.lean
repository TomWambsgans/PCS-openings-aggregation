-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Notation.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Distance

/-!
# One notation for probabilities

VCVio states probabilities as `Pr{let x ← mx}[p x]`, the mass that the computation's output
measure puts on the event. These files were first written on its retired `Pr[p | mx]`, the mass of
the set `{x | p x}`: this is the bridge between the two readings.
-/

open OracleComp

namespace QuotientSecurity

/-- The two readings are the same number: the probability of the event is the mass of its set
under the output measure, on the discrete σ-algebra. -/
theorem prEvent_eq_probEvent {α : Type} (mx : ProbComp α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = (letI : MeasurableSpace α := ⊤; 𝒟[mx] {x | p x}) := by
  let _ : MeasurableSpace α := ⊤
  exact prEvent_eq_evalDist_of_discrete mx p

end QuotientSecurity
