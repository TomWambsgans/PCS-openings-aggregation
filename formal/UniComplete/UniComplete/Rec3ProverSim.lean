-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls` and their simulation lemmas (`implH`, `implF`); and
-- `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean`'s `simulateQ_proveOpeningWithH`.
import UniComplete.Rec3Hyp
import UniComplete.FlockCost

/-!
# π1-rec3's honest prover commutes with simulation

The port of `ProverSim.lean` (and of `FlockCost.lean`'s commutation) to π1-rec3's prover (`Rec3Prover.lean`):

1. **`flockCommutes_flockProve3H : FlockCommutes flockProve3H`**: π1-rec3's honest Flock prover commutes with every
   monad morphism, the hash becoming `φ ∘ H`. Its new pieces are the run of squares (`wr_drawRunW`) and the zerocheck
   and the front that draw it (`wr_zerocheckW3`, `wr_frontW3`); the rest is the main line's (`FlockP.wr_skipW`,
   `wr_zcRounds`, `wr_lcRounds`, `wr_sendSlices`, `wr_endW`, `FlockCost.lean`).
2. **`proverCommutes3_of_flock : FlockCommutes flock → ProverCommutes3 flock D`** (`Rec3Hyp.lean`), through
   `Morph.wr` (`ProverSim.lean`): the narrow draw (`wr_sampleNarrowW`), the paired batch's rounds (`wr_pairRound3`,
   `wr_plainRound3`, `wr_batchRounds3`), the stream (`wr_proveStreamRec3With`), π1-rec3's IV
   (`app_contractIvRec3Of`), the prover with its three openings (`app_proveRec3With`, `app_uniProverRec3With`), and
   over the two calls `simulateQ_uniProverRec3With` (`Morph.sim impl`, the opening by WithHash's
   `simulateQ_proveOpeningWithH`).

Decisions (recorded): as in `ProverSim.lean`, the lemmas are stated for any monad morphism, lawfulness asked only
where `<$>` is used (the stream's `some <$> flock …`); the main line's `Morph.wr_…`, `Morph.app_setupTreesOf`,
`app_seedOf`, `app_commitReal` are reused as they are. `proverCommutes3_flockProve3H` and
`flockSimCommutes_flockProve3H` (`Prob.FlockSimCommutes`, which π1-rec3's probability layer takes of Flock's prover)
are the corollaries at π1-rec3's honest Flock prover.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.Compile.Rom (implH implF)
open UniStatement

set_option autoImplicit false

namespace UniComplete.Rec3

/-! ## The writer's draws and Flock's prover commute with every monad morphism -/

section Draws

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Morph m n) (H : List UInt8 → m Digest)

/-- **The narrow draw commutes.** -/
theorem wr_sampleNarrowW : φ.wr (sampleNarrowW H) = sampleNarrowW fun x ↦ φ.app (H x) := by
  simp only [sampleNarrowW, Morph.wr_bind, Morph.wr_get, Morph.wr_lift, Morph.wr_set, Morph.wr_pure]

/-- **A run of squares commutes.** -/
theorem wr_drawRunW (count : ℕ) : φ.wr (drawRunW H count) = drawRunW (fun x ↦ φ.app (H x)) count := by
  simp only [drawRunW, Morph.wr_ite, Morph.wr_bind, Morph.wr_sampleW, Morph.wr_pure]

/-- **The zerocheck at π1-rec3 commutes.** -/
theorem wr_zerocheckW3 (logN k : ℕ) (wit : FlockP.Wit) :
    φ.wr (zerocheckW3 H logN k wit) = zerocheckW3 (fun x ↦ φ.app (H x)) logN k wit := by
  simp only [zerocheckW3, Morph.wr_bind, wr_drawRunW, FlockP.wr_skipW, FlockP.wr_zcRounds, Morph.wr_sendScalar,
    Morph.wr_pure]

/-- **Flock's front at π1-rec3 commutes.** -/
theorem wr_frontW3 (logN : ℕ) (variant : Flock.Variant) (q : Array K) :
    φ.wr (frontW3 H logN variant q) = frontW3 (fun x ↦ φ.app (H x)) logN variant q := by
  simp only [frontW3, Morph.wr_bind, wr_zerocheckW3, Morph.wr_sampleW, FlockP.wr_lcRounds, FlockP.wr_sendSlices,
    Morph.wr_pure]

/-- **π1-rec3's honest Flock prover commutes with every monad morphism**, the hash becoming `φ ∘ H`. -/
theorem wr_flockProve3 (logN : ℕ) (variant : Flock.Variant) (q : Array K) :
    φ.wr (flockProve3 H logN variant q) = flockProve3 (fun x ↦ φ.app (H x)) logN variant q := by
  simp only [flockProve3, Morph.wr_bind, wr_frontW3, FlockP.wr_endW, Morph.wr_pure]

end Draws

/-- **π1-rec3's honest Flock prover commutes with every monad morphism** (`ProverSim.lean`'s `FlockCommutes`). -/
theorem flockCommutes_flockProve3H : FlockCommutes flockProve3H := by
  intro m n _ _ _ _ φ H logN variant words
  exact wr_flockProve3 φ H logN variant words

/-! ## The paired batch and the stream -/

section Stream

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Morph m n) (H : List UInt8 → m Digest)

/-- **A pair round commutes.** -/
theorem wr_pairRound3 (lambda : E) (nq : ℕ) (st : BatchState) :
    φ.wr (pairRound3 H lambda nq st) = pairRound3 (fun x ↦ φ.app (H x)) lambda nq st := by
  simp only [pairRound3, Morph.wr_bind, Morph.wr_sendScalars, wr_sampleNarrowW, Morph.wr_pure]

/-- **The last plain round commutes.** -/
theorem wr_plainRound3 (lambda : E) (nh : ℕ) (st : BatchState) :
    φ.wr (plainRound3 H lambda nh st) = plainRound3 (fun x ↦ φ.app (H x)) lambda nh st := by
  simp only [plainRound3, Morph.wr_bind, Morph.wr_sendScalar, wr_sampleNarrowW, Morph.wr_pure]

/-- **π1-rec3's batching sumcheck's rounds commute.** -/
theorem wr_batchRounds3 (lambda : E) (vars : ℕ) (st : BatchState) :
    φ.wr (batchRounds3 H lambda vars st) = batchRounds3 (fun x ↦ φ.app (H x)) lambda vars st := by
  simp only [batchRounds3, Morph.wr_bind, Morph.wr_forIn_list, wr_pairRound3, Morph.wr_ite, wr_plainRound3,
    Morph.wr_pure]

/-- **π1-rec3's stream commutes with a morphism** that commutes with the commitment and with Flock's prover. -/
theorem wr_proveStreamRec3With [LawfulMonad m] [LawfulMonad n] (commit : Commitment → ℕ → Array K → m Committed)
    (commit' : Commitment → ℕ → Array K → n Committed) (hcommit : ∀ c v s, φ.app (commit c v s) = commit' c v s)
    (flock : FlockProver m) (flock' : FlockProver n) (hflock : ∀ logN v q, φ.wr (flock logN v q) = flock' logN v q)
    (tr : Trace) :
    φ.wr (proveStreamRec3With H commit flock tr) =
      proveStreamRec3With (fun x ↦ φ.app (H x)) commit' flock' tr := by
  simp only [proveStreamRec3With, Morph.wr_bind, Morph.wr_forIn_list, Morph.wr_sendInteger, Morph.wr_pure,
    Morph.wr_lift, hcommit, Morph.wr_sendRoot, wr_drawRunW, Morph.wr_sampleW, Morph.wr_map, hflock,
    Morph.wr_sendScalars, wr_batchRounds3, Morph.wr_get]

end Stream

/-! ## The IV, the prover -/

section Top

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

omit [LawfulMonad m] [LawfulMonad n] in
/-- **π1-rec3's IV commutes.** -/
theorem app_contractIvRec3Of (shape : Shape) (programIv : List UInt8) (roots : SetupRoots) :
    φ.app (contractIvRec3Of H shape programIv roots) =
      contractIvRec3Of (fun x ↦ φ.app (H x)) shape programIv roots := by
  simp only [contractIvRec3Of, φ.app_bind, φ.app_pure]

/-- **π1-rec3's honest prover commutes with a monad morphism** that commutes with Flock's prover and with the opening
(`hopen`, WithHash's `simulateQ_proveOpeningWithH` for `simulateQ`). -/
theorem app_proveRec3With
    (hopen : ∀ (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
      (claims : List PcsQuotient.Claim),
      φ.app (E2ECompleteness.proveOpeningWithH H F fuel L tree stack claims) =
        E2ECompleteness.proveOpeningWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel L tree stack claims)
    (flock : FlockProver m) (flock' : FlockProver n) (hflock : ∀ logN v q, φ.wr (flock logN v q) = flock' logN v q)
    (fuel : ℕ) (programIv : List UInt8) (tr : Trace) :
    φ.app (proveRec3With H F fuel flock programIv tr) =
      proveRec3With (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel flock' programIv tr := by
  have hs : ∀ seed, φ.app ((proveStreamRec3With H (commitReal H) flock tr).run (Wr.start seed)) =
      (proveStreamRec3With (fun x ↦ φ.app (H x)) (commitReal fun x ↦ φ.app (H x)) flock' tr).run
        (Wr.start seed) := fun seed ↦ by
    rw [← Morph.wr_run, wr_proveStreamRec3With φ H _ _ (Morph.app_commitReal φ H) flock flock' hflock]
  simp only [proveRec3With, φ.app_bind, Morph.app_setupTreesOf, app_contractIvRec3Of, Morph.app_seedOf, hs]
  refine bind_congr fun trees ↦ bind_congr fun iv ↦ bind_congr fun seed ↦ bind_congr fun x ↦ ?_
  obtain ⟨out, _⟩ := x
  dsimp only
  generalize List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    simp only [φ.app_bind, φ.app_pure, hopen]

/-- **π1-rec3's deployed honest prover commutes with a monad morphism** that commutes with Flock's prover and with
the opening. -/
theorem app_uniProverRec3With
    (hopen : ∀ (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
      (claims : List PcsQuotient.Claim),
      φ.app (E2ECompleteness.proveOpeningWithH H F fuel L tree stack claims) =
        E2ECompleteness.proveOpeningWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel L tree stack claims)
    (flock : FlockProver m) (flock' : FlockProver n) (hflock : ∀ logN v q, φ.wr (flock logN v q) = flock' logN v q)
    (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    φ.app (uniProverRec3With H F flock D input rows q) =
      uniProverRec3With (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) flock' D input rows q :=
  app_proveRec3With φ H F hopen flock flock' hflock _ _ _

end Top

/-! ## Over the two calls: `simulateQ` -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- **π1-rec3's honest prover over the two calls commutes with any simulation**, at any fuel. -/
theorem simulateQ_proveRec3With (flock : FlockProverH) (hflock : FlockCommutes flock) (fuel : ℕ)
    (programIv : List UInt8) (tr : Trace) :
    simulateQ impl (proveRec3With callKeccak256 callKeccakF1600 fuel (flock callKeccak256) programIv tr) =
      proveRec3With (implH impl) (implF impl) fuel (flock (implH impl)) programIv tr := by
  have h := app_proveRec3With (Morph.sim impl) callKeccak256 callKeccakF1600
    (fun fuel L tree stack claims ↦ by
      rw [Morph.sim_H, Morph.sim_F]
      exact E2ECompleteness.simulateQ_proveOpeningWithH impl fuel L tree stack claims)
    (flock callKeccak256) (flock (implH impl)) (fun logN v q ↦ by rw [hflock, Morph.sim_H]) fuel programIv tr
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

/-- **π1-rec3's deployed honest prover over the two calls commutes with any simulation**: simulated by `impl`, it is
the honest prover over `impl`'s two calls, Flock's prover at `impl`'s hash. -/
theorem simulateQ_uniProverRec3With (flock : FlockProverH) (hflock : FlockCommutes flock) (D : Deployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) =
      uniProverRec3With (implH impl) (implF impl) (flock (implH impl)) D input rows q :=
  simulateQ_proveRec3With impl flock hflock _ _ _

end Commute

/-- **`ProverCommutes3` from `FlockCommutes`** (`simulateQ_uniProverRec3With`). -/
theorem proverCommutes3_of_flock {flock : FlockProverH} (h : FlockCommutes flock) (D : Deployment) :
    ProverCommutes3 flock D :=
  fun impl input rows q ↦ simulateQ_uniProverRec3With impl flock h D input rows q

/-- **π1-rec3's prover with its honest Flock prover commutes with simulation.** -/
theorem proverCommutes3_flockProve3H (D : Deployment) : ProverCommutes3 flockProve3H D :=
  proverCommutes3_of_flock flockCommutes_flockProve3H D

/-- **π1-rec3's honest Flock prover commutes with simulation** (`Prob.FlockSimCommutes`). -/
theorem flockSimCommutes_flockProve3H : Prob.FlockSimCommutes flockProve3H :=
  Prob.flockSimCommutes_of_commutes flockCommutes_flockProve3H

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.flockCommutes_flockProve3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.flockCommutes_flockProve3H

/-- info: 'UniComplete.Rec3.app_uniProverRec3With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.app_uniProverRec3With

/-- info: 'UniComplete.Rec3.simulateQ_uniProverRec3With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.simulateQ_uniProverRec3With

/-- info: 'UniComplete.Rec3.proverCommutes3_of_flock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.proverCommutes3_of_flock

/-- info: 'UniComplete.Rec3.proverCommutes3_flockProve3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.proverCommutes3_flockProve3H

/-- info: 'UniComplete.Rec3.flockSimCommutes_flockProve3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.flockSimCommutes_flockProve3H
