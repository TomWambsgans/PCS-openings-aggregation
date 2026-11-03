-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Final
import UniSound.FsProof

/-!
# The end theorem with the Fiat–Shamir layer proved from the game bridge

**`uniKnowledgeSoundness_game`**: `Final.lean`'s `uniKnowledgeSoundness_bus` with its hypothesis
`hFs : FsLayer …` replaced by what `FsProof.lean`'s `fsLayer_of_game` proves it from: the
deployment's five layout words of `24 … 28` variables (`UniShapes`; the reference shape's are
`27, 27, 24, 28, 28`), its numbers (`UniNumbers`) and the game bridge (`UniGameLe`).
-/

namespace UniSound

open LeanVM.Parameters UniStatement
open scoped ENNReal

/-- **Knowledge soundness of the univariate verifier for leanVM 42422001** (main line), at most
`2^-61` for `Q ≤ 2^64`, **under the Flock hypothesis**, the bus model and the identity model, the
code-level links, and, for the Fiat–Shamir layer, the stacks' sizes, the numbers and the game
bridge. -/
theorem uniKnowledgeSoundness_game {D : Deployment} {κ : ℕ} (hFlock : FlockSound κ)
    (B : BusModel D κ) (J : UniIdsRest D hFlock B) (C : UniCode D hFlock J.nV J.V)
    (hFin : UniFinal D hFlock (UniIds.ofBus hFlock B J) C) (hs : UniShapes D)
    (hN : UniNumbers D hFlock J.nV J.V C hs) (hG : UniGameLe D hFlock J.nV J.V C hs)
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32)
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : J.degSum ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_bus hFlock B J C hFin (fsLayer_of_game D hFlock J.nV J.V C hs hN hG) hB hFl
    hdeg hrel

/-- info: 'UniSound.uniKnowledgeSoundness_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness_game

end UniSound
