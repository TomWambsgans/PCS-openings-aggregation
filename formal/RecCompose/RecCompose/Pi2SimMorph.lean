-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `formal/UniComplete/UniComplete/VerifierHSim.lean`
-- and `ProverSim.lean` (`UniComplete.Morph`, its channel and writer liftings) for π2's code (`Pi2CompleteH`'s contract,
-- setup and graph verifier with Keccak-256 explicit, `Pi2Prover`'s honest prover, `Pi2ProbStaged`'s stages), over
-- leanerVM's two calls (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0: `implH`, `implF`, `simulateQ_queryH`) and `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean`'s
-- `simulateQ_openingWithH`, `simulateQ_proveOpeningWithH`.
import RecCompose.Pi2P1

/-!
# π2's code commutes with simulation

Every function of π2's completeness experiment is written over any monad, Keccak-256 `H` and the permutation `F`
explicit. Read through a monad morphism `φ` (`UniComplete.Morph`) that commutes with WHIR's opening and its prover
(`hopen`, `hprove`), each is the same function over `φ ∘ H`, `φ ∘ F` (`app_…`, `chan_…`, `wr_…`): the setup
(`app_setupTreesWithH2`), the IV (`app_ivOfH`), π1-rec3's graph with its openings (`app_pi1GraphVerifierWithH`), π2's
run and contract (`chan_reduceWithH2`, `app_runWithH2`, `app_contractWithH`, `app_verifierWithH2`), π2's honest prover
(`wr_pi2ProveStreamWith`, `app_pi2ProveWith`, `app_pi2ProverWith`), the experiment `expW2` and its stages
(`app_expW2`, `wr_pre2`, `wr_mid2`, `wr_post2`, `app_stageA`, `app_stageB`, `app_stageC`).

**`sim_…`**: over the two calls, with `φ = Morph.sim impl` (`simulateQ impl`), the two hypotheses WithHash's.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open UniStatement (Chan ChanM)
open UniComplete (Morph)
open Pi2S Pi2K Pi2P Pi2E Pi2G

section Morph

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-! ## The setup, the IV -/

theorem app_setupTreesWithH2 (D : RecDeployment) :
    φ.app (Pi2H.setupTreesWithH H F D) =
      Pi2H.setupTreesWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D := by
  simp only [Pi2H.setupTreesWithH, Pi2H.setupTreeWithH, UniComplete.setupTreesWithH, φ.app_bind, φ.app_pure,
    Morph.app_commitWithH]

theorem app_digestWithH (c : Pi2Circuit) :
    φ.app (Pi2H.digestWithH H c) = Pi2H.digestWithH (fun x ↦ φ.app (H x)) c := by
  simp only [Pi2H.digestWithH, φ.app_bind, φ.app_pure]

theorem app_ivWithH2 (pi1Iv digest setupRoot : List UInt8) (logN : ℕ) :
    φ.app (Pi2H.ivWithH H pi1Iv digest setupRoot logN) =
      Pi2H.ivWithH (fun x ↦ φ.app (H x)) pi1Iv digest setupRoot logN := by
  simp only [Pi2H.ivWithH, φ.app_bind, φ.app_pure]

theorem app_ivOfH (D : RecDeployment) (roots : RecSetupRoots) :
    φ.app (Pi2H.ivOfH H D roots) = Pi2H.ivOfH (fun x ↦ φ.app (H x)) D roots := by
  simp only [Pi2H.ivOfH, φ.app_bind, app_digestWithH, app_ivWithH2]

/-! ## The openings -/

variable (hopen : ∀ (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : LeanVM.Protocol.Compile.Proof),
    φ.app (E2ECompleteness.openingWithH H F L root claims proof) =
      E2ECompleteness.openingWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) L root claims proof)

include hopen in
theorem app_pcsOpenWithH (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : LeanVM.Protocol.Compile.Proof) :
    φ.app (UniComplete.pcsOpenWithH H F vars root claims proof) =
      UniComplete.pcsOpenWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) vars root claims proof :=
  hopen _ _ _ _

include hopen in
/-- **π1-rec3's graph with its three openings.** -/
theorem app_pi1GraphVerifierWithH (D : RecDeployment) (roots : UniStatement.SetupRoots) (input : Vector UInt8 32)
    (proof : UniStatement.UniProof) :
    φ.app (Pi2H.pi1GraphVerifierWithH H F D roots input proof) =
      Pi2H.pi1GraphVerifierWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D roots input proof := by
  unfold Pi2H.pi1GraphVerifierWithH
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · split
        · exact φ.app_pure _
        · simp only [φ.app_bind, Morph.app_forIn_list, φ.app_pure, app_pcsOpenWithH φ H F hopen]

include hopen in
theorem app_pcsOpenAtH (registry : List (List UInt8 × Opener)) (words : List (List UInt8))
    (proof : LeanVM.Protocol.Compile.Proof) :
    φ.app (Pi2H.pcsOpenAtH H F registry words proof) =
      Pi2H.pcsOpenAtH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) registry words proof := by
  unfold Pi2H.pcsOpenAtH
  split
  · exact φ.app_pure _
  · exact app_pcsOpenWithH φ H F hopen _ _ _ _
  · exact hopen _ _ _ _

/-! ## π2's run and the contract -/

theorem chan_reduceWithH2 (s : Spec) (statement : List E) :
    φ.chan (Pi2H.reduceWithH H s statement) = Pi2H.reduceWithH (fun x ↦ φ.app (H x)) s statement := by
  simp only [Pi2H.reduceWithH, Morph.chan_bind, Morph.chan_forIn_list, Morph.chan_pure, Morph.chan_nextRoot,
    Morph.chan_sampleH, Morph.chan_nextScalars, Morph.chan_nextScalar]
  congr 1
  congr 1
  funext rd pubs
  split <;> simp only [Morph.chan_bind, Morph.chan_pure, Morph.chan_nextInteger, Morph.chan_nextRoot,
    Morph.chan_nextScalar]

theorem app_runWithH2 (s : Spec) (iv publicInput : List UInt8) (stream : Array UInt8) :
    φ.app (Pi2H.runWithH H s iv publicInput stream) =
      Pi2H.runWithH (fun x ↦ φ.app (H x)) s iv publicInput stream := by
  simp only [Pi2H.runWithH, φ.app_bind, φ.app_pure, ← Morph.chan_run φ, Morph.chan_bind, chan_reduceWithH2,
    Morph.chan_finish, Morph.chan_pure]

include hopen in
/-- **The contract.** -/
theorem app_contractWithH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    φ.app (Pi2H.contractWithH H F D roots input proof) =
      Pi2H.contractWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D roots input proof := by
  simp only [Pi2H.contractWithH, φ.app_bind, app_ivOfH, app_runWithH2]
  refine bind_congr fun iv ↦ bind_congr fun o ↦ ?_
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · simp only [φ.app_bind, Morph.app_forIn_list, φ.app_pure, app_pcsOpenAtH φ H F hopen]

include hopen in
theorem app_verifierWithH2 (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    φ.app (Pi2H.verifierWithH H F D roots input proof) =
      Pi2H.verifierWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D roots input proof := by
  simp only [Pi2H.verifierWithH, φ.app_bind, φ.app_pure, app_contractWithH φ H F hopen]

/-! ## π2's honest prover -/

theorem wr_sendPublic : ∀ l : List (Read × PublicValue), φ.wr (sendPublic (m := m) l) = sendPublic l
  | [] => φ.wr_pure _
  | (.integer b, .integer x) :: rest => by
    simp only [sendPublic, Morph.wr_bind, Morph.wr_sendInteger, wr_sendPublic rest]
  | (.root, .root bytes) :: rest => by
    simp only [sendPublic, Morph.wr_bind, Morph.wr_sendRoot, wr_sendPublic rest]
  | (.scalar, .scalar x) :: rest => by
    simp only [sendPublic, Morph.wr_bind, Morph.wr_sendScalar, wr_sendPublic rest]
  | (.integer _, .root _) :: rest => wr_sendPublic rest
  | (.integer _, .scalar _) :: rest => wr_sendPublic rest
  | (.root, .integer _) :: rest => wr_sendPublic rest
  | (.root, .scalar _) :: rest => wr_sendPublic rest
  | (.scalar, .integer _) :: rest => wr_sendPublic rest
  | (.scalar, .root _) :: rest => wr_sendPublic rest

theorem wr_pi2ProveStreamWith (G : RecPiop.Circuit E) (reads : List Read) (setupStack : Array K)
    (input : List UInt8) (values : List PublicValue) (w : ℕ → K) :
    φ.wr (pi2ProveStreamWith H G reads setupStack input values w) =
      pi2ProveStreamWith (fun x ↦ φ.app (H x)) G reads setupStack input values w := by
  simp only [pi2ProveStreamWith, Morph.wr_bind, wr_sendPublic, Morph.wr_lift, Morph.app_commitWithH,
    Morph.wr_sendRoot, Morph.wr_sampleW, Morph.wr_sendScalars, Morph.wr_get, Morph.wr_pure]

variable (hprove : ∀ (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim),
    φ.app (E2ECompleteness.proveOpeningWithH H F fuel L tree stack claims) =
      E2ECompleteness.proveOpeningWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel L tree stack claims)

include hprove in
theorem app_pi2ProveWith (fuel : ℕ) (G : RecPiop.Circuit E) (view : Circuit) (setupStack : Array K)
    (setupTree : LeanVM.Prover.Tree) (iv input : List UInt8) (values : List PublicValue) (w : ℕ → K) :
    φ.app (pi2ProveWith H F fuel G view setupStack setupTree iv input values w) =
      pi2ProveWith (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel G view setupStack setupTree iv input values w := by
  simp only [pi2ProveWith, φ.app_bind, φ.app_pure, ← Morph.wr_run φ, wr_pi2ProveStreamWith, hprove]

include hprove in
theorem app_pi2ProverWith (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (fuel : ℕ)
    (input : Vector UInt8 32) (p1 : UniStatement.UniProof) :
    φ.app (pi2ProverWith H F D C Fa fuel input p1) =
      pi2ProverWith (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D C Fa fuel input p1 := by
  simp only [pi2ProverWith, φ.app_bind, φ.app_pure, app_setupTreesWithH2, app_ivOfH,
    app_pi2ProveWith φ H F hprove]

/-! ## The experiment and its stages -/

include hopen hprove in
theorem app_expW2 (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : m (Option UniStatement.UniProof)) (input : Vector UInt8 32) :
    φ.app (expW2 H F D C Fa p1o input) =
      expW2 (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D C Fa (φ.app p1o) input := by
  simp only [expW2, φ.app_bind, app_setupTreesWithH2]
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => exact φ.app_pure _
  | some p1 =>
    simp only [φ.app_bind, app_pi1GraphVerifierWithH φ H F hopen, app_pi2ProverWith φ H F hprove]
    refine bind_congr fun a1 ↦ bind_congr fun r ↦ ?_
    cases r with
    | none => exact φ.app_pure _
    | some p2 => simp only [φ.app_bind, φ.app_pure, app_verifierWithH2 φ H F hopen]

theorem wr_pre2 (G : RecPiop.Circuit E) (reads : List Read) (values : List PublicValue) (w : ℕ → K) :
    φ.wr (pre2 H G reads values w) = pre2 (fun x ↦ φ.app (H x)) G reads values w := by
  simp only [pre2, Morph.wr_bind, wr_sendPublic, Morph.wr_lift, Morph.app_commitWithH, Morph.wr_sendRoot,
    Morph.wr_pure]

theorem wr_mid2 (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ : E) :
    φ.wr (mid2 H G w α β γ) = mid2 (fun x ↦ φ.app (H x)) G w α β γ := by
  simp only [mid2, Morph.wr_bind, Morph.wr_lift, Morph.app_commitWithH, Morph.wr_sendRoot, Morph.wr_pure]

theorem wr_post2 (G : RecPiop.Circuit E) (setupStack : Array K) (input : List UInt8) (values : List PublicValue)
    (w : ℕ → K) (wS : Array K) (wT : LeanVM.Prover.Tree) (qS : Array K) (qT : LeanVM.Prover.Tree) (α β γ t : E) :
    φ.wr (post2 H G setupStack input values w wS wT qS qT α β γ t) =
      post2 (fun x ↦ φ.app (H x)) G setupStack input values w wS wT qS qT α β γ t := by
  simp only [post2, Morph.wr_bind, Morph.wr_sendScalars, Morph.wr_sampleW, Morph.wr_get, Morph.wr_pure]

include hopen in
theorem app_stageA (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : m (Option UniStatement.UniProof)) (input : Vector UInt8 32) :
    φ.app (stageA H F D C Fa p1o input) =
      stageA (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D C Fa (φ.app p1o) input := by
  simp only [stageA, φ.app_bind, app_setupTreesWithH2]
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => exact φ.app_pure _
  | some p1 =>
    simp only [φ.app_bind, φ.app_pure, app_pi1GraphVerifierWithH φ H F hopen, app_setupTreesWithH2, app_ivOfH,
      ← Morph.wr_run φ, wr_pre2]

theorem app_stageB (D : RecDeployment) (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest) :
    φ.app (stageB H D C a s₁ s₂ s₃) = stageB (fun x ↦ φ.app (H x)) D C a s₁ s₂ s₃ := by
  simp only [stageB, φ.app_bind, φ.app_pure, ← Morph.wr_run φ, wr_mid2]

include hopen hprove in
theorem app_stageC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB) (st : Digest) :
    φ.app (stageC H F D C input b st) =
      stageC (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D C input b st := by
  unfold stageC
  split
  · exact φ.app_pure _
  · simp only [φ.app_bind, ← Morph.wr_run φ, wr_post2, hprove]
    refine bind_congr fun x ↦ bind_congr fun pW ↦ bind_congr fun pS ↦ bind_congr fun pQ ↦ ?_
    split
    · simp only [φ.app_bind, φ.app_pure, app_verifierWithH2 φ H F hopen]
    · exact φ.app_pure _

end Morph

/-! ## Over the two calls -/

section Sim

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

theorem hopen_sim : ∀ (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : LeanVM.Protocol.Compile.Proof),
    (Morph.sim impl).app (E2ECompleteness.openingWithH callKeccak256 callKeccakF1600 L root claims proof) =
      E2ECompleteness.openingWithH (fun x ↦ (Morph.sim impl).app (callKeccak256 x))
        (fun s ↦ (Morph.sim impl).app (callKeccakF1600 s)) L root claims proof := by
  intro L root claims proof
  rw [Morph.sim_H, Morph.sim_F]
  exact E2ECompleteness.simulateQ_openingWithH impl L root claims proof

theorem hprove_sim : ∀ (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim),
    (Morph.sim impl).app (E2ECompleteness.proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims) =
      E2ECompleteness.proveOpeningWithH (fun x ↦ (Morph.sim impl).app (callKeccak256 x))
        (fun s ↦ (Morph.sim impl).app (callKeccakF1600 s)) fuel L tree stack claims := by
  intro fuel L tree stack claims
  rw [Morph.sim_H, Morph.sim_F]
  exact E2ECompleteness.simulateQ_proveOpeningWithH impl fuel L tree stack claims

/-- **The experiment over the two calls commutes with any simulation.** -/
theorem sim_expW2 (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : OracleComp KeccakCalls (Option UniStatement.UniProof)) (input : Vector UInt8 32) :
    simulateQ impl (expW2 callKeccak256 callKeccakF1600 D C Fa p1o input) =
      expW2 (implH impl) (implF impl) D C Fa (simulateQ impl p1o) input := by
  have h := app_expW2 (Morph.sim impl) callKeccak256 callKeccakF1600 (hopen_sim impl) (hprove_sim impl) D C Fa p1o
    input
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

theorem sim_stageA (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : OracleComp KeccakCalls (Option UniStatement.UniProof)) (input : Vector UInt8 32) :
    simulateQ impl (stageA callKeccak256 callKeccakF1600 D C Fa p1o input) =
      stageA (implH impl) (implF impl) D C Fa (simulateQ impl p1o) input := by
  have h := app_stageA (Morph.sim impl) callKeccak256 callKeccakF1600 (hopen_sim impl) D C Fa p1o input
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

theorem sim_stageB (D : RecDeployment) (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest) :
    simulateQ impl (stageB callKeccak256 D C a s₁ s₂ s₃) = stageB (implH impl) D C a s₁ s₂ s₃ := by
  have h := app_stageB (Morph.sim impl) callKeccak256 D C a s₁ s₂ s₃
  rw [Morph.sim_H] at h
  exact h

theorem sim_stageC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB) (st : Digest) :
    simulateQ impl (stageC callKeccak256 callKeccakF1600 D C input b st) =
      stageC (implH impl) (implF impl) D C input b st := by
  have h := app_stageC (Morph.sim impl) callKeccak256 callKeccakF1600 (hopen_sim impl) (hprove_sim impl) D C input
    b st
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

end Sim

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.sim_expW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.sim_expW2
