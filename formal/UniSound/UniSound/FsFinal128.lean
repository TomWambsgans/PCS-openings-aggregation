-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `FsFinal.lean`'s `fsLayer_holds` with
-- `FsGame128.lean`'s `fsLayer128_of_gameV'` (kept apart from `FsGame128.lean`, which must not import
-- `FsFinal.lean`'s bridges: they bring `Completeness`'s instance of `SampleableType E`).
import UniSound.FsGame128
import UniSound.FsFinal

namespace UniSound

open UniStatement

/-- **The Fiat–Shamir layer at `≥ 128` bits, proved** at the main line's code-level link, from the
deployment's numbers (`fsLayer_holds` with `FsLayer128`). -/
theorem fsLayer128_holds (D : Deployment) {κ : ℕ} (Fl : FlockSound κ)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV V : ℕ) (hnV : nV = valsCount)
    (hV : V = varsOf (layoutsOf D.shape)) (hs : UniShapes D) (hsmall : LayoutVarsSmall D)
    (hI : UniIv D) (hnQ : (uSpec Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds Fl nV V, r.nv ≤ 2 ^ 30) :
    FsLayer128 D Fl nV V (uniCodeAt D Fl hκ nV V hnV hV) :=
  fsLayer128_of_gameV' D Fl nV V _ hs hnQ hnv hI
    (uniGameLeV_holds D Fl nV V _ hs hsmall (uniOutRoots_uniCodeAt D Fl hκ nV V hnV hV))

end UniSound

/-- info: 'UniSound.fsLayer128_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer128_holds
