-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's Flock step: the verifier's
-- `Flock.verifyWalkedFs … .rec3` (`Rec.lean`, `Rec3VerifierH.lean`'s `verifyWalkedFsH`) against `Rec3Prover.lean`'s
-- `flockProve3`; the walk's lemma is `formal/FlockSound/FlockSoundUni/Rec3Walk.lean`'s `WalkLemma`.
import UniComplete.Rec3Prover
import UniComplete.Rec3VerifierH
import UniComplete.SyncBasic
import UniSound.FlockInterface

/-!
# π1-rec3's Flock step: the statements

* **`walkZero3 H logN variant q w`**: the value the verifier's walk collects (`requireZero (walkedTerminal … + r_lc)`)
  on the honest front `frontW3` from the writer `w`.
* **`FlockSyncs3 H flock logN variant q zero`** (`SyncBasic.FlockSyncs` for the walked verifier): from any writer,
  `verifyWalkedFsH (pure ∘ H) logN variant .rec3` reads Flock's messages, draws its challenges, returns `q_flock`'s
  point and the ring switch's end as the prover's output carries them, and collects one value, `zero w`.
* **`WalkLemmaConverse`**: the converse of the walk's lemma (`FlockSound.Uni.WalkLemma`, `Rec3Walk.lean`) at the
  main line's front shape: if the pending reduction's claim is its sum (`UniSound.PendingHolds (Pending.new …)`), the
  walk's zero vanishes (`walkedTerminal … + r_lc = 0`). It is the `←` direction of the walk's identity
  `walkedTerminal … + r_lc = 0 ↔ PendingHolds (Pending.new …)` (`walk_zero_iff`, being proved on the soundness
  side); until that lands it is a named hypothesis of π1-rec3's completeness.
-/

namespace UniComplete.Rec3

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Protocol

/-- **The walk's zero on the honest front** from the writer `w`. -/
def walkZero3 (H : List UInt8 → Digest) (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) : E :=
  let fr := ((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1
  walkedTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime (fr.slices.getD []) fr.alpha + fr.rLc

/-- **Flock's prover synchronises with π1-rec3's walked verifier** `verifyWalkedFsH … .rec3`, collecting `zero w`. -/
def FlockSyncs3 (H : List UInt8 → Digest) (flock : FlockProver Id) (logN : ℕ) (variant : Variant) (q : Array K)
    (zero : Wr → E) : Prop :=
  ∀ w : Wr, Syncs (verifyWalkedFsH (m := Id) (Pure.pure ∘ H) logN variant .rec3) (flock logN variant q) w
    (((flock logN variant q).run w).1.point, ((flock logN variant q).run w).1.end_) [zero w]

/-- **The converse of the walk's lemma** at the main line's front shape (a skip point, a row point of `3`
coordinates, lincheck points of `8`, `64` slices): the pending claim's identity makes the walk's zero vanish. -/
def WalkLemmaConverse : Prop :=
  ∀ (z : E) (rowLow chiIn chiInPrime s : List E) (alpha rLc : E), rowLow.length = 3 → chiIn.length = 8 →
    chiInPrime.length = 8 → s.length = 64 →
    UniSound.PendingHolds (Pending.new (some z) rowLow chiIn chiInPrime alpha rLc (some s)) →
      walkedTerminal (some z) rowLow chiIn chiInPrime s alpha + rLc = 0

end UniComplete.Rec3
