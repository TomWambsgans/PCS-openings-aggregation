-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `FsFinal3.lean`'s `fsLayer3_holds` with
-- `FsGame128_3.lean`'s `fsLayer128_3_of_gameV'` (kept apart from `FsGame128_3.lean`, which must not import
-- `FsFinal3.lean`'s bridges: they bring `Completeness`'s instance of `SampleableType E`), as the main line's
-- `FsFinal128.lean`.
import UniSound.Rec3.FsGame128_3
import UniSound.Rec3.FsFinal3

namespace UniSound

open UniStatement

/-- **π1-rec3's Fiat–Shamir layer at `≥ 128` bits, proved**, for every code-level link naming the stream's roots,
from the deployment's numbers (`fsLayer3_holds` with `FsLayer128_3`). -/
theorem fsLayer128_3_holds (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
    (hs : UniShapes D) (hsmall : LayoutVarsSmall D) (hI : UniIv3 D)
    (hnQ : (uniSpec (rec3Rounds F3.prog.rounds nV np)).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ rec3Rounds F3.prog.rounds nV np, r.nv ≤ 2 ^ 30) (hO : UniOutRoots3 D F3 nV np C) :
    FsLayer128_3 D F3 nV np C :=
  fsLayer128_3_of_gameV' D F3 nV np C hs hnQ hnv hI (uniGameLeV3_holds D F3 nV np C hs hsmall hO)

end UniSound

/-- info: 'UniSound.fsLayer128_3_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer128_3_holds
