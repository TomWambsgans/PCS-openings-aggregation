-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's completeness from the BLAKE2s walk's rows
-- (`formal/FlockSound/FlockSoundUni/WalkAlg.lean`'s `RowsSpec`, `walkLemmaConverse_of_rows`), the hypothesis
-- π1-rec3's knowledge soundness takes too (`UniSound.Rec3`'s closed theorem).
import UniComplete.Rec3End
import FlockSoundUni.WalkAlg

/-!
# π1-rec3's completeness from the walk's rows

**`uniCompletenessRec3_end_of_rows`**: `Rec3End.lean`'s `uniCompletenessRec3_end` with its one hypothesis, the walk
lemma's converse (`WalkLemmaConverse`), discharged from **`FlockSound.Uni.RowsSpec`** (the BLAKE2s walk
`blake2sRowValues` computes the R1CS's `A0 w`, `B0 w`) by the soundness side's `walkLemmaConverse_of_rows`: the same
single fact about the walk that π1-rec3's knowledge soundness assumes.
-/

open UniStatement LeanVM LeanVM.Parameters
open scoped ENNReal

namespace UniComplete.Rec3

/-- **The walk lemma's converse from the walk's rows.** -/
theorem walkLemmaConverse_of_rowsSpec (hR : FlockSound.Uni.RowsSpec) : WalkLemmaConverse :=
  FlockSound.Uni.walkLemmaConverse_of_rows hR

/-- **End-to-end completeness of π1-rec3 at the reference deployment**, from the walk's rows. -/
theorem uniCompletenessRec3_end_of_rows (D : Deployment) (hD : D.shape = reference)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hR : FlockSound.Uni.RowsSpec) :
    UniCompletenessRec3 D (uniProverRec3RP flockProve3H D) deltaRec3 :=
  uniCompletenessRec3_end D hD hiv (walkLemmaConverse_of_rowsSpec hR)

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.uniCompletenessRec3_end_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.uniCompletenessRec3_end_of_rows
