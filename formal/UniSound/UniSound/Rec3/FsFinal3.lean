-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsFinal.lean` for π1-rec3.
import UniSound.Rec3.FsExtract3
import UniSound.Rec3.FsVerifier3
import UniSound.Rec3.FsWalkProof3
import UniSound.FsSetup

/-!
# π1-rec3's Fiat–Shamir layer, proved

**`uniGameLeV3_holds`**: the coupling `UniGameLeV3` (`FsGame3.lean`) for every deployment whose stacks' variables
fit a layout word's byte (`LayoutVarsSmall`) and every code-level link whose result names the stream's roots
(`UniOutRoots3`), from its three bridge facts, each proved: the setup's (`uniSetupBridge_of_small`, the main line's:
the setup is unchanged), the verifier's (`uniVerifierBridge3_of_walk` with `uniWalk3`, `uniWalkReject3`) and the
extractor's (`uniExtractBridge3`).

**`fsLayer3_holds`**: `FsLayer3` (`Fs3.lean`) for every code-level link `C : UniCode3 D F3 nV np` whose result names
the stream's two roots (`UniOutRoots3`, the one hypothesis about `C`; it follows from the link's `out` naming the
transcript's roots, `uniOutRoots3_of`), from the deployment's numbers: `UniShapes`, `LayoutVarsSmall`, `UniIv3` (the
IV's input, `9` bytes longer than the main line's), the chain's `≤ 2^10` queries and rounds of `≤ 2^30` scalars.
The bound is `uniBound3` as `Fs3.lean` defines it (three openings' doom terms; no other constant changed).
-/

namespace UniSound

open UniStatement

/-- **π1-rec3's coupling, proved**, from `LayoutVarsSmall` and `UniOutRoots3`. -/
theorem uniGameLeV3_holds (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ)
    (C : UniCode3 D F3 nV np) (hs : UniShapes D) (hsmall : LayoutVarsSmall D)
    (hO : UniOutRoots3 D F3 nV np C) : UniGameLeV3 D F3 nV np C hs :=
  uniGameLeV3_of D F3 nV np C hs (uniSetupBridge_of_small D hs hsmall)
    (uniVerifierBridge3_of_walk D F3 nV np C hs (uniWalk3 D F3 nV np C) (uniWalkReject3 D F3 nV np C) hO)
    (uniExtractBridge3 D F3 nV np hs hsmall)

/-- **π1-rec3's Fiat–Shamir layer, proved**, for every code-level link naming the stream's roots, from the
deployment's numbers. -/
theorem fsLayer3_holds (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
    (hs : UniShapes D) (hsmall : LayoutVarsSmall D) (hI : UniIv3 D)
    (hnQ : (uniSpec (rec3Rounds F3.prog.rounds nV np)).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ rec3Rounds F3.prog.rounds nV np, r.nv ≤ 2 ^ 30) (hO : UniOutRoots3 D F3 nV np C) :
    FsLayer3 D F3 nV np C :=
  fsLayer3_of_gameV' D F3 nV np C hs hnQ hnv hI (uniGameLeV3_holds D F3 nV np C hs hsmall hO)

end UniSound

/-- info: 'UniSound.uniGameLeV3_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniGameLeV3_holds

/-- info: 'UniSound.fsLayer3_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer3_holds

/-- info: 'UniSound.uniVerifierBridge3_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniVerifierBridge3_of_walk

/-- info: 'UniSound.uniWalk3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniWalk3

/-- info: 'UniSound.uniWalkReject3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniWalkReject3

/-- info: 'UniSound.uniExtractBridge3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniExtractBridge3

/-- info: 'UniSound.fsLayer3_of_gameV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer3_of_gameV
