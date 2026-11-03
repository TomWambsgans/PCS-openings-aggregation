-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.Walk
import FlockSoundUni.WalkAlg

/-!
# π1-rec3's walk lemma, closed

The TowerWalk terminal (π1-rec3, `Slices::TowerWalk`): the verifier checks `walked_terminal … + r_lc = 0` in place
of the matrices' reduction. Two halves give the walk's lemma:

* **the rows** (`Walk.lean`, `rowValues_spec`): `blake2sRowValues` computes `A0 w` and `B0 w` of the BLAKE2s R1CS,
  by simulating Lv42's circuit builder; hence **`rowsSpec : RowsSpec`**;
* **the algebra** (`WalkAlg.lean`, `walkLemma_of_rows`, `walkLemmaConverse_of_rows`): from the rows, the walked
  terminal is the pending reduction's sum plus its known terms.

**`walkLemma : WalkLemma`** is the hypothesis π1-rec3's closed theorem takes (`Rec3Walk.lean`), and
**`walk_zero_iff`** the equivalence at the main line's shape (`zSkip = some z`, `k = 3`: `rowLow` of 3, `chiIn`,
`chiInPrime` of 8, 64 slices).
-/

namespace FlockSound.Uni

open UniStatement UniStatement.Flock UniSound LeanVM.Parameters

/-- **The rows' specification holds**: the walk computes the matrices' products at every row. -/
theorem rowsSpec : RowsSpec := fun cw hcw j ↦ rowValues_spec cw hcw j

/-- **The walk's lemma**: the walked terminal's zero gives the pending reduction's claim. -/
theorem walkLemma : WalkLemma := walkLemma_of_rows rowsSpec

/-- **The walked terminal vanishes exactly when the pending reduction's claim is its sum** (main line, `k = 3`). -/
theorem walk_zero_iff (z : E) (rowLow chiIn chiInPrime s : List E) (alpha rLc : E) (hl : rowLow.length = 3)
    (h8 : chiIn.length = 8) (h8' : chiInPrime.length = 8) (hs : s.length = 64) :
    Flock.walkedTerminal (some z) rowLow chiIn chiInPrime s alpha + rLc = 0 ↔
      PendingHolds (Flock.Pending.new (some z) rowLow chiIn chiInPrime alpha rLc (some s)) :=
  ⟨walkLemma z rowLow chiIn chiInPrime s alpha rLc hl h8 h8' hs,
    walkLemmaConverse_of_rows rowsSpec z rowLow chiIn chiInPrime s alpha rLc hl h8 h8' hs⟩

end FlockSound.Uni

/-- info: 'FlockSound.Uni.rowsSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.rowsSpec

/-- info: 'FlockSound.Uni.walkLemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.walkLemma

/-- info: 'FlockSound.Uni.walk_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.walk_zero_iff
