-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls` and their simulation lemmas (`implH`, `implF`, `simulateQ_queryH`), and
-- `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean`'s `simulateQ_openingWithH`.
import UniComplete.Rec3Hyp
import UniComplete.VerifierHSim

/-!
# π1-rec3's verifier commutes with simulation

π1-rec3's deployed verifier over the two calls (`Rec3VerifierH.lean`'s `Deployment.verifierRec3WithH` at
`H := callKeccak256`, `F := callKeccakF1600`) commutes with any simulation `impl`: **`simulateQ_verifierRec3WithH`**,
that is **`verifierCommutes3 : VerifierCommutes3`** (`Rec3Hyp.lean`).

As `VerifierHSim.lean` does for the main line, the commutation is proved once for **any monad morphism**
(`UniComplete.Morph`, `VerifierHSim.lean`'s: its lift to the channel's monad `Morph.chan` and its lemmas `chan_…`,
`app_…` are reused unchanged), of which `simulateQ impl` is one (`Morph.sim`):

* every function of π1-rec3's verifier that hashes commutes with the morphism, the hash `H` becoming `φ ∘ H`: the
  narrow challenge and the draws (`chan_sampleNarrowH`, `chan_sampleDrawnH`, `chan_drawRunH`), the sumchecks
  (`chan_sumcheckDrawnH`, `chan_sumcheckPairsDrawnH`; the pair's round polynomial `pairRoundPoly` reads only,
  `chan_pairRoundPoly`), Flock (`chan_zerocheckFsH`, `chan_frontFsH`, `chan_verifyFsH`, `chan_verifyDeferredFsH`,
  `chan_verifyWalkedFsH`), the batch (`chan_batchFsH`), the walk (**`chan_reduceWithFsH`**, every configuration);
* at the monad's level, the run, the IV and, given that the opening commutes (`hopen`, WithHash's
  `simulateQ_openingWithH` for `simulateQ`), the verifier (`app_runWithFsH`, `app_contractIvForWithH`,
  `app_verifyWithFsH`, **`app_verifierRec3WithH`**).

Decisions: the lemmas are in `UniComplete.Rec3.Morph`, next to the functions they are about, with the main line's
`UniComplete.Morph` opened; they are stated for every configuration (`fs`, `walk`, `blake2s`, `mode`), as
`Rec3VerifierH.lean` keeps them, though π1-rec3's verifier runs only `(.flock flockMain) .point .rec3 true`. The walk's
proof is one tactic for the eight configurations (`chan_close`: push the morphism through the binds, strip the
common prefix, split the matches the pushing stops at).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.Compile.Rom (implH implF)
open UniStatement

namespace UniComplete.Rec3.Morph

open UniComplete.Morph

/-! ## The verifier's functions -/

section Verifier

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : UniComplete.Morph m n)
  (H : List UInt8 → m Digest)

theorem chan_sampleNarrowH : φ.chan (sampleNarrowH H) = sampleNarrowH fun x ↦ φ.app (H x) := by
  simp only [sampleNarrowH, chan_bind, chan_get, chan_lift, chan_set, chan_pure]

theorem chan_sampleDrawnH (narrow : Bool) :
    φ.chan (sampleDrawnH H narrow) = sampleDrawnH (fun x ↦ φ.app (H x)) narrow := by
  cases narrow
  · exact chan_sampleH φ H
  · exact chan_sampleNarrowH φ H

theorem chan_drawRunH (fs : FsShape) (count : ℕ) :
    φ.chan (drawRunH H fs count) = drawRunH (fun x ↦ φ.app (H x)) fs count := by
  cases fs <;> simp only [drawRunH, chan_samplesH, chan_ite, chan_pure, chan_bind, chan_sampleH]

theorem chan_sumcheckDrawnH (claim : E) (count : ℕ) (equalities : List (Option E)) (narrow : Bool) :
    φ.chan (sumcheckDrawnH H claim count equalities narrow) =
      sumcheckDrawnH (fun x ↦ φ.app (H x)) claim count equalities narrow := by
  simp only [sumcheckDrawnH, chan_bind, chan_forIn_list, chan_roundPoly, chan_sampleDrawnH, chan_pure]

/-- The pair's round polynomial only reads. -/
theorem chan_pairRoundPoly (degree : ℕ) (claim : E) :
    φ.chan (pairRoundPoly (m := m) degree claim) = pairRoundPoly degree claim := by
  simp only [pairRoundPoly, chan_bind, chan_nextScalars, chan_pure]

theorem chan_sumcheckPairsDrawnH (claim : E) (degree vars : ℕ) (narrow : Bool) :
    φ.chan (sumcheckPairsDrawnH H claim degree vars narrow) =
      sumcheckPairsDrawnH (fun x ↦ φ.app (H x)) claim degree vars narrow := by
  simp only [sumcheckPairsDrawnH, chan_bind, chan_forIn_range, chan_pairRoundPoly, chan_sampleDrawnH, chan_pure,
    chan_ite, chan_sumcheckDrawnH]

theorem chan_zerocheckFsH (logN k : ℕ) (fs : FsShape) :
    φ.chan (zerocheckFsH H logN k fs) = zerocheckFsH (fun x ↦ φ.app (H x)) logN k fs := by
  simp only [zerocheckFsH, chan_bind, chan_drawRunH, chan_ite, chan_nextScalars, chan_sampleH, chan_pure,
    chan_sumcheckH, chan_nextScalar]

theorem chan_frontFsH (logN : ℕ) (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    φ.chan (frontFsH H logN variant fs) = frontFsH (fun x ↦ φ.app (H x)) logN variant fs := by
  simp only [frontFsH, chan_bind, chan_zerocheckFsH, chan_sampleH, chan_sumcheckH, chan_ite, chan_pure,
    chan_map, chan_nextScalars]

theorem chan_verifyFsH (logN : ℕ) (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    φ.chan (verifyFsH H logN variant fs) = verifyFsH (fun x ↦ φ.app (H x)) logN variant fs := by
  simp only [verifyFsH, chan_bind, chan_frontFsH, chan_reduceTerminalH]
  congr 1; funext fr; congr 1; funext x
  split <;> simp only [chan_bind, chan_ringEndH, chan_pure]

theorem chan_verifyDeferredFsH (logN : ℕ) (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    φ.chan (verifyDeferredFsH H logN variant fs) = verifyDeferredFsH (fun x ↦ φ.app (H x)) logN variant fs := by
  simp only [verifyDeferredFsH, chan_bind, chan_frontFsH]
  congr 1; funext fr
  split <;> simp only [chan_bind, chan_map, chan_ringEndH, chan_pure]

theorem chan_verifyWalkedFsH (logN : ℕ) (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    φ.chan (verifyWalkedFsH H logN variant fs) = verifyWalkedFsH (fun x ↦ φ.app (H x)) logN variant fs := by
  simp only [verifyWalkedFsH, chan_bind, chan_frontFsH, chan_requireZero, chan_ringEndH, chan_pure]

theorem chan_batchFsH (fs : FsShape) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (bitSlice : Option Combined) (ringMap : Option (List E))
    (pending : Option (Flock.Pending × List E)) :
    φ.chan (batchFsH H fs combined layouts bitSlice ringMap pending) =
      batchFsH (fun x ↦ φ.app (H x)) fs combined layouts bitSlice ringMap pending := by
  rcases pending with _ | ⟨p, flockPoint⟩ <;> cases fs <;>
    simp only [batchFsH, chan_bind, chan_sampleH, chan_sumcheckPairsDrawnH, chan_sumcheckDrawnH,
      chan_nextScalars, chan_nextScalar, chan_pure, pure_bind, chan_ite, chan_requireZero]

/-- Push the morphism through the walk's binds (the lemmas above). -/
macro "chan_push" : tactic => `(tactic| simp only [chan_bind, chan_ite, chan_throw, chan_pure, chan_countBits,
  chan_nextRoot, chan_drawRunH, chan_sampleH, chan_verifyWalkedFsH, chan_verifyDeferredFsH, chan_verifyFsH,
  chan_forIn_list, chan_tablePart, chan_nextScalar, chan_batchFsH, pure_bind])

/-- The walk's closing tactic: push the morphism through the binds, then strip the common prefix of binds and split
the matches the pushing stopped at (on the results of earlier steps), pushing again inside, until both sides
agree. -/
macro "chan_close" : tactic => `(tactic| (chan_push; repeat (first
  | with_reducible rfl
  | (with_reducible refine bind_congr fun _ ↦ ?_)
  | split
  | chan_push)))

/-- The walk, Flock walked, point claims (π1-rec2's and π1-rec3's). -/
theorem chan_reduceWithFsH_walkedPoint (shape : Shape) (publicWords : List E) (variant : UniStatement.Flock.Variant)
    (fs : FsShape) :
    φ.chan (reduceWithFsH H shape publicWords (.flock variant) .point fs true) =
      reduceWithFsH (fun x ↦ φ.app (H x)) shape publicWords (.flock variant) .point fs true := by
  unfold reduceWithFsH
  chan_close

/-- The walk, Flock walked, weighted claims. -/
theorem chan_reduceWithFsH_walkedWeighted (shape : Shape) (publicWords : List E)
    (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    φ.chan (reduceWithFsH H shape publicWords (.flock variant) .weighted fs true) =
      reduceWithFsH (fun x ↦ φ.app (H x)) shape publicWords (.flock variant) .weighted fs true := by
  unfold reduceWithFsH
  chan_close

/-- The walk, Flock deferred, point claims (the main line's and π1-rec's). -/
theorem chan_reduceWithFsH_flockPoint (shape : Shape) (publicWords : List E) (variant : UniStatement.Flock.Variant)
    (fs : FsShape) :
    φ.chan (reduceWithFsH H shape publicWords (.flock variant) .point fs false) =
      reduceWithFsH (fun x ↦ φ.app (H x)) shape publicWords (.flock variant) .point fs false := by
  unfold reduceWithFsH
  chan_close

/-- The walk, Flock and weighted claims. -/
theorem chan_reduceWithFsH_flockWeighted (shape : Shape) (publicWords : List E)
    (variant : UniStatement.Flock.Variant) (fs : FsShape) :
    φ.chan (reduceWithFsH H shape publicWords (.flock variant) .weighted fs false) =
      reduceWithFsH (fun x ↦ φ.app (H x)) shape publicWords (.flock variant) .weighted fs false := by
  unfold reduceWithFsH
  chan_close

/-- The walk without Flock, point claims. -/
theorem chan_reduceWithFsH_omittedPoint (shape : Shape) (publicWords : List E) (fs : FsShape) (walk : Bool) :
    φ.chan (reduceWithFsH H shape publicWords .omitted .point fs walk) =
      reduceWithFsH (fun x ↦ φ.app (H x)) shape publicWords .omitted .point fs walk := by
  unfold reduceWithFsH
  chan_close

/-- The walk without Flock, weighted claims. -/
theorem chan_reduceWithFsH_omittedWeighted (shape : Shape) (publicWords : List E) (fs : FsShape) (walk : Bool) :
    φ.chan (reduceWithFsH H shape publicWords .omitted .weighted fs walk) =
      reduceWithFsH (fun x ↦ φ.app (H x)) shape publicWords .omitted .weighted fs walk := by
  unfold reduceWithFsH
  chan_close

/-- **The walk commutes with the morphism**, at every configuration. -/
theorem chan_reduceWithFsH (shape : Shape) (publicWords : List E) (blake2s : Blake2s) (mode : ClaimsMode)
    (fs : FsShape) (walk : Bool) :
    φ.chan (reduceWithFsH H shape publicWords blake2s mode fs walk) =
      reduceWithFsH (fun x ↦ φ.app (H x)) shape publicWords blake2s mode fs walk := by
  rcases blake2s with variant | _ <;> cases mode
  · cases walk
    · exact chan_reduceWithFsH_flockPoint φ H shape publicWords variant fs
    · exact chan_reduceWithFsH_walkedPoint φ H shape publicWords variant fs
  · cases walk
    · exact chan_reduceWithFsH_flockWeighted φ H shape publicWords variant fs
    · exact chan_reduceWithFsH_walkedWeighted φ H shape publicWords variant fs
  · exact chan_reduceWithFsH_omittedPoint φ H shape publicWords fs walk
  · exact chan_reduceWithFsH_omittedWeighted φ H shape publicWords fs walk

/-! ### The run, the IV, the verifier -/

theorem app_runWithFsH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) (fs : FsShape) (walk : Bool) :
    φ.app (runWithFsH H shape iv publicInput stream blake2s mode fs walk) =
      runWithFsH (fun x ↦ φ.app (H x)) shape iv publicInput stream blake2s mode fs walk := by
  simp only [runWithFsH, φ.app_bind, app_seedWithH, φ.app_pure, ← chan_run φ, chan_bind, chan_reduceWithFsH,
    chan_finish, chan_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_contractIvForWithH (s : Shape) (blake2s : Blake2s) (fs : FsShape) (walk : Bool)
    (programIv : List UInt8) (roots : SetupRoots) :
    φ.app (contractIvForWithH H s blake2s fs walk programIv roots) =
      contractIvForWithH (fun x ↦ φ.app (H x)) s blake2s fs walk programIv roots := by
  simp only [contractIvForWithH, app_ite, app_contractIvWithH, φ.app_bind, φ.app_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_ivRec3WithH (D : Deployment) (roots : SetupRoots) :
    φ.app (Deployment.ivRec3WithH H D roots) = Deployment.ivRec3WithH (fun x ↦ φ.app (H x)) D roots :=
  app_contractIvForWithH φ H _ _ _ _ _ _

variable (F : KeccakState → m KeccakState)

/-- **π1-rec3's verifier commutes with a monad morphism that commutes with the opening** (`hopen`, WithHash's
`simulateQ_openingWithH` for `simulateQ`). -/
theorem app_verifyWithFsH
    (hopen : ∀ (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (E2ECompleteness.openingWithH H F L root claims proof) =
        E2ECompleteness.openingWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) L root claims proof)
    (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32) (proof : UniProof)
    (fs : FsShape) (walk : Bool) :
    φ.app (verifyWithFsH H F shape iv roots publicInput proof fs walk) =
      verifyWithFsH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) shape iv roots publicInput proof fs walk := by
  simp only [verifyWithFsH, φ.app_bind, app_runWithFsH]
  congr 1; funext o
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · simp only [φ.app_bind, app_forIn_list]
      congr 1
      · congr 1; funext x s
        split
        · simp only [φ.app_bind, φ.app_pure, pcsOpenWithH, hopen]
        · exact φ.app_pure _
      · funext s
        split
        · simp only [φ.app_bind, φ.app_pure, pcsOpenWithH, hopen]
        · exact φ.app_pure _
        · exact φ.app_pure _

/-- **π1-rec3's deployed verifier commutes with a monad morphism that commutes with the opening.** -/
theorem app_verifierRec3WithH
    (hopen : ∀ (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (E2ECompleteness.openingWithH H F L root claims proof) =
        E2ECompleteness.openingWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) L root claims proof)
    (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof) :
    φ.app (Deployment.verifierRec3WithH H F D roots input proof) =
      Deployment.verifierRec3WithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D roots input proof := by
  simp only [Deployment.verifierRec3WithH, φ.app_bind, app_ivRec3WithH, app_verifyWithFsH φ H F hopen]

end Verifier

end UniComplete.Rec3.Morph

/-! ## Over the two calls: `simulateQ` -/

namespace UniComplete.Rec3

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- **π1-rec3's deployed verifier over the two calls commutes with any simulation.** -/
theorem simulateQ_verifierRec3WithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) :
    simulateQ impl (Deployment.verifierRec3WithH callKeccak256 callKeccakF1600 D roots input proof) =
      Deployment.verifierRec3WithH (implH impl) (implF impl) D roots input proof := by
  have h := Morph.app_verifierRec3WithH (UniComplete.Morph.sim impl) callKeccak256 callKeccakF1600
    (fun L root claims proof ↦ by
      rw [UniComplete.Morph.sim_H, UniComplete.Morph.sim_F]
      exact E2ECompleteness.simulateQ_openingWithH impl L root claims proof) D roots input proof
  rw [UniComplete.Morph.sim_H, UniComplete.Morph.sim_F] at h
  exact h

end Commute

/-- **`VerifierCommutes3`**: π1-rec3's deployed verifier commutes with every simulation. -/
theorem verifierCommutes3 : VerifierCommutes3 :=
  fun impl D roots input proof ↦ simulateQ_verifierRec3WithH impl D roots input proof

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.verifierCommutes3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.verifierCommutes3

/-- info: 'UniComplete.Rec3.Morph.app_verifierRec3WithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.Morph.app_verifierRec3WithH
