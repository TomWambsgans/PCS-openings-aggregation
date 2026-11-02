-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.ProverAccept
import E2ECompleteness.ProverTables
import E2ECompleteness.ProverQuotient
import E2ECompleteness.ProverFacts

/-!
# The prover's tables are Completeness's, discharged

`TablesMatch` (`ProverAccept.lean`), from the tables helper's theorems (`ProverTables.lean`:
`witness_table`, `wiring_table`; `ProverQuotient.lean`: `quotient_table`) at the Statement's
constants (`constants`, `ProverFacts.lean`).
-/

set_option autoImplicit false

namespace E2ECompleteness

/-- **The prover's NTT tables are Completeness's.** -/
theorem tablesMatch : TablesMatch where
  witness f cells hcs hcells masks i :=
    ProverTables.witness_table constants f cells hcs hcells masks i
  wiring sigma hss hsig i := (ProverTables.wiring_table constants sigma hss hsig).2 i
  quotient f cells hcs hcells sigma hss hsig masks hgate α β γ hab i hi :=
    ProverQuotient.quotient_table constants f cells hcs hcells sigma hss hsig masks hgate α β γ hab
      i hi

end E2ECompleteness

/-- info: 'E2ECompleteness.tablesMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.tablesMatch
