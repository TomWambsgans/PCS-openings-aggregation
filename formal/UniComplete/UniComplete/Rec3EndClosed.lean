-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `formal/UniStatement`'s
-- `UniCompletenessRec3` (`RecSecurity.lean`).
import UniComplete.Rec3EndRows
import FlockSoundUni.Walk

/-!
# Completeness of π1-rec3, closed: no hypothesis beyond the statement's

**`uniCompletenessRec3_end_closed`**: for every deployment at the reference shape whose program IV has at most
`2^16` bytes, π1-rec3's honest prover `uniProverRec3RP flockProve3H D` (`Rec3Prover.lean`: `α` as squares, Flock's
zerocheck squares, no matrices' reduction, the paired narrow batch, three WHIR openings) is complete with error
`deltaRec3 < 2^-167` (`deltaRec3_lt`). It is `uniCompletenessRec3_end_of_rows` with the circuit walk's
specification `rowValues_spec` (`FlockSoundUni/Walk.lean`).
-/

namespace UniComplete.Rec3

open UniStatement

/-- **Completeness of π1-rec3, closed.** -/
theorem uniCompletenessRec3_end_closed (D : Deployment) (hD : D.shape = reference)
    (hiv : D.programIv.length ≤ 2 ^ 16) : UniCompletenessRec3 D (uniProverRec3RP flockProve3H D) deltaRec3 :=
  uniCompletenessRec3_end_of_rows D hD hiv fun cw hcw j ↦ FlockSound.Uni.rowValues_spec cw hcw j

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.uniCompletenessRec3_end_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.uniCompletenessRec3_end_closed
