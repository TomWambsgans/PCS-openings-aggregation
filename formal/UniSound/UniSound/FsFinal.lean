-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.FsSetup
import UniSound.FsExtract
import UniSound.FsVerifier
import UniSound.FsWalkProof

/-!
# The Fiat–Shamir layer, proved

**`uniGameLeV_holds`**: the coupling `UniGameLeV` (`FsGame.lean`) for every deployment whose stacks'
variables fit a layout word's byte (`LayoutVarsSmall`) and every code-level link whose result names
the stream's roots (`UniOutRoots`), from its three bridge facts, each proved: the setup's
(`uniSetupBridge_of_small`), the verifier's (`uniVerifierBridge_of_walk` with `uniWalk`,
`uniWalkReject`) and the extractor's (`uniExtractBridge`).

**`fsLayer_holds`**: `FsLayer` at the main line's code-level link (`uniCodeAt`), from the
deployment's numbers only: `UniShapes`, `LayoutVarsSmall`, `UniIv`, the chain's `< 2^10` queries and
rounds of `≤ 2^30` scalars.
-/

namespace UniSound

open UniStatement

/-- **The coupling, proved**, from `LayoutVarsSmall` and `UniOutRoots`. -/
theorem uniGameLeV_holds (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ)
    (C : UniCode D Fl nV V) (hs : UniShapes D) (hsmall : LayoutVarsSmall D)
    (hO : UniOutRoots D Fl nV V C) : UniGameLeV D Fl nV V C hs :=
  uniGameLeV_of D Fl nV V C hs (uniSetupBridge_of_small D hs hsmall)
    (uniVerifierBridge_of_walk D Fl nV V C hs (uniWalk D Fl nV V C) (uniWalkReject D Fl nV V C) hO)
    (uniExtractBridge D Fl nV V hs hsmall)

/-- **The Fiat–Shamir layer, proved** at the main line's code-level link, from the deployment's
numbers. -/
theorem fsLayer_holds (D : Deployment) {κ : ℕ} (Fl : FlockSound κ)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV V : ℕ) (hnV : nV = valsCount)
    (hV : V = varsOf (layoutsOf D.shape)) (hs : UniShapes D) (hsmall : LayoutVarsSmall D)
    (hI : UniIv D) (hnQ : (uSpec Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds Fl nV V, r.nv ≤ 2 ^ 30) :
    FsLayer D Fl nV V (uniCodeAt D Fl hκ nV V hnV hV) :=
  fsLayer_of_gameV' D Fl nV V _ hs hnQ hnv hI
    (uniGameLeV_holds D Fl nV V _ hs hsmall (uniOutRoots_uniCodeAt D Fl hκ nV V hnV hV))

end UniSound

/-- info: 'UniSound.uniGameLeV_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniGameLeV_holds

/-- info: 'UniSound.fsLayer_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer_holds
