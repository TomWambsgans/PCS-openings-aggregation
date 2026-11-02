-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Claims.Reduce
import Bridge.Claims.Constants
import Implementation.Graph

/-!
# The statement's claims are the composition's

The reduction's claims of the statement (`PcsQuotient.claimsAt`, `formal/Statement/PcsQuotient/
Reduction.lean`) against `Compose.Reduce.reduce` (`formal/Compose/Compose/Reduce.lean`), the
transcription the composed soundness (`Compose/Claims.lean`, `Soundness.VerifierBridge`) reads:

* **`claimsAt_eq_reduce`** (`Claims/Reduce.lean`): `claimsAt 22 stmt α β γ t ρ a next` is
  `(reduce statementConsts 24 (stmtHalves (stmt.y ++ stmt.root)) α β γ t (a.get ·) next ρ).map
  reducedTr`, for every statement, challenges and values, without evaluating any constant;
* **`isCantor_statementConsts`**, **`rowVanishing_statementConsts`** (`Claims/Constants.lean`): the
  statement's constants meet `reduce`'s two hypotheses (`Compose.IsCantor`,
  `Compose.Reduce.RowVanishing`), by kernel evaluation (`Claims/Tau.lean`: `rowVanishing 24` in
  `22` elimination steps);
* `betaWords_eq_emitted`, `tauWords_eq_emitted`: the words are those F5's graph carries
  (`Implementation.Emitted.beta`, `tau`).
-/

namespace Bridge

/-- The statement's basis words are F5's graph's. -/
theorem betaWords_eq_emitted :
    QuotientSecurity.betaWords ++
        [0xf89578714bd28f96, 0x564dda59237a3352, 0xad33bc6cc75aed38, 0x57a3104fcd0e5f34] =
      Implementation.Emitted.beta.map Nat.toUInt64 := by
  decide

/-- The statement's `τ` words are F5's graph's. -/
theorem tauWords_eq_emitted : tauWords = Implementation.Emitted.tau.map Nat.toUInt64 := by
  decide

end Bridge

/-- info: 'Bridge.claimsAt_eq_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.claimsAt_eq_reduce

/-- info: 'Bridge.isCantor_statementConsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.isCantor_statementConsts

/-- info: 'Bridge.rowVanishing_statementConsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.rowVanishing_statementConsts

/-- info: 'Bridge.betaAt_eq_deployedBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.betaAt_eq_deployedBasis

/-- info: 'Bridge.statementTau_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.statementTau_eq

/-- info: 'Bridge.tauWords_eq_emitted' does not depend on any axioms -/
#guard_msgs in
#print axioms Bridge.tauWords_eq_emitted
