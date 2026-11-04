-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's analogue of `formal/UniComplete/UniComplete/
-- ProverDuplex.lean`, `VerifierHDuplex.lean` and `Rec3ProbExp.lean`'s `duplexVm_stagedU3`, for `Pi2ProbStaged`'s
-- staged run (`pi2Staged`: the setup, π1-rec3's honest prover, π1-rec3's graph, π2's honest prover
-- `crates/leanvm_rec/src/pi2/prover.rs`, the contract `formal/RecStatement`); uses
-- `formal/EndToEnd/Completeness/E2ECompleteness/Duplex.lean` (`Disc`, `disc_proveOpeningWithH`, `disc_openingWithH`,
-- `hOnly_commitWithH`) and leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the duplex discipline (`DuplexVm`, `DuplexP`, `HOnly`).
import RecCompose.Pi2P1

/-!
# The duplex discipline of π2's staged run (`Pi2RunDuplex`)

**`pi2RunDuplex_p1k : Pi2RunDuplex D C Fa (p1k D)`**: every Keccak-f[1600] call of `pi2Staged` (at π1-rec3's honest
prover) continues a duplex or starts one at a zero capacity, from no earlier answer (mumbai's `DuplexVm`). No
hypothesis.

* **The hash-only parts**: the setup (`hOnly_setupTreesWithH2`: π1's three trees, π2's setup tree), π2's IV
  (`hOnly_ivOfH`: the digest's three hashes and the IV's), the seed, π2's prover's stream (`wHOnly_pre2`, `mid2`,
  `post2`: the public values, the commitments, the challenges) and the contract's run on the calldata
  (`cHOnly_runWithH`: the channel's calculus `CHOnly`, every challenge a Keccak-256 call).
* **The permutation is called by the openings only**, each disciplined: π1-rec3's prover's three
  (`disc_uniProverRec3With`), the graph's three `PCS_OPEN`s and the contract's six (`disc_pcsOpenWithH`,
  `disc_openingWithH`), π2's prover's three (`disc_proveOpeningWithH`).
* **The staged run** (`disc_pi2Staged`): for any `P1k` that is disciplined (`Disc`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open RecStatement
open UniStatement (Chan ChanM)
open E2ECompleteness (Disc disc_pure disc_of_hOnly)
open UniComplete (WHOnly wHOnly_pure wHOnly_get wHOnly_lift wHOnly_sampleW wHOnly_sendRoot wHOnly_sendScalar
  wHOnly_sendScalars wHOnly_sendInteger disc_forIn_list)

namespace RecCompose.Pi2G

/-! ## The channel's calculus -/

/-- The channel's monad over the two calls. -/
abbrev CM := ChanM (OracleComp KeccakCalls)

/-- **From every state, the channel's run only hashes.** -/
def CHOnly {α : Type} (x : CM α) : Prop := ∀ c, HOnly (x.run.run c)

section Calculus

variable {α β : Type}

theorem CHOnly.bind {x : CM α} {f : α → CM β} (hx : CHOnly x) (hf : ∀ a, CHOnly (f a)) : CHOnly (x >>= f) := by
  intro c
  simp only [ExceptT.run_bind, StateT.run_bind]
  refine (hx c).bind fun z ↦ ?_
  obtain ⟨r, s⟩ := z
  cases r with
  | error e => exact hOnly_pure _
  | ok a => exact hf a s

theorem cHOnly_pure (a : α) : CHOnly (pure a : CM α) := fun _ ↦ hOnly_pure _

theorem cHOnly_get : CHOnly (get : CM Chan) := fun c ↦ by
  show HOnly ((Except.ok <$> (get : StateT Chan (OracleComp KeccakCalls) Chan)).run c)
  simp only [StateT.run_map, StateT.run_get]
  exact hOnly_pure _

theorem cHOnly_set (c' : Chan) : CHOnly (set c' : CM PUnit) := fun c ↦ by
  show HOnly ((Except.ok <$> (set c' : StateT Chan (OracleComp KeccakCalls) PUnit)).run c)
  simp only [StateT.run_map, StateT.run_set]
  exact hOnly_pure _

theorem cHOnly_modify (f : Chan → Chan) : CHOnly (modify f : CM PUnit) := fun c ↦ by
  show HOnly ((Except.ok <$> (modifyGet (fun s ↦ (PUnit.unit, f s)) :
    StateT Chan (OracleComp KeccakCalls) PUnit)).run c)
  simp only [StateT.run_map, StateT.run_modifyGet]
  exact hOnly_pure _

theorem cHOnly_throw (e : UniStatement.UniError) : CHOnly (throw e : CM α) := fun _ ↦ hOnly_pure _

theorem cHOnly_liftH (x : List UInt8) : CHOnly (liftM (callKeccak256 x) : CM Digest) := fun c ↦ by
  show HOnly ((ExceptT.lift (StateT.lift (callKeccak256 x)) : CM Digest).run.run c)
  simp only [ExceptT.run_lift, StateT.run_map, StateT.run_lift]
  rw [map_eq_bind_pure_comp]
  exact ((hOnly_queryH x).bind fun _ ↦ hOnly_pure _).bind fun _ ↦ hOnly_pure _

theorem CHOnly.map {x : CM α} (f : α → β) (hx : CHOnly x) : CHOnly (f <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact hx.bind fun _ ↦ cHOnly_pure _

theorem cHOnly_ite {x y : CM α} (cnd : Prop) [Decidable cnd] (hx : CHOnly x) (hy : CHOnly y) :
    CHOnly (if cnd then x else y) := by
  split
  · exact hx
  · exact hy

theorem cHOnly_forIn_list {γ : Type} (l : List γ) (b : β) (f : γ → β → CM (ForInStep β))
    (hf : ∀ a s, CHOnly (f a s)) : CHOnly (forIn l b f) := by
  induction l generalizing b with
  | nil => exact cHOnly_pure b
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a b).bind fun s ↦ ?_
    cases s with
    | done b => exact cHOnly_pure b
    | yield b => exact ih b

theorem cHOnly_forIn_range (n : ℕ) (b : β) (f : ℕ → β → CM (ForInStep β)) (hf : ∀ a s, CHOnly (f a s)) :
    CHOnly (forIn [0:n] b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact cHOnly_forIn_list _ b f hf

end Calculus

/-! ## The channel's steps -/

theorem cHOnly_takeBytes (n : ℕ) : CHOnly (UniStatement.takeBytes (m := OracleComp KeccakCalls) n) := by
  unfold UniStatement.takeBytes
  refine cHOnly_get.bind fun c ↦ ?_
  split
  · exact (cHOnly_set _).bind fun _ ↦ cHOnly_pure _
  · exact cHOnly_throw _

theorem cHOnly_nextScalar : CHOnly (UniStatement.nextScalar (m := OracleComp KeccakCalls)) :=
  (cHOnly_takeBytes _).bind fun _ ↦ cHOnly_pure _

theorem cHOnly_nextInteger (b : ℕ) : CHOnly (UniStatement.nextInteger (m := OracleComp KeccakCalls) b) :=
  (cHOnly_takeBytes _).bind fun _ ↦ cHOnly_pure _

theorem cHOnly_nextRoot : CHOnly (UniStatement.nextRoot (m := OracleComp KeccakCalls)) :=
  (cHOnly_takeBytes _).bind fun _ ↦ (cHOnly_takeBytes _).bind fun _ ↦ cHOnly_pure _

theorem cHOnly_nextScalars (n : ℕ) : CHOnly (UniStatement.nextScalars (m := OracleComp KeccakCalls) n) := by
  unfold UniStatement.nextScalars
  exact (cHOnly_forIn_range _ _ _ fun _ _ ↦ cHOnly_nextScalar.bind fun _ ↦ cHOnly_pure _).bind fun _ ↦
    cHOnly_pure _

theorem cHOnly_sampleH : CHOnly (UniComplete.sampleH callKeccak256) := by
  unfold UniComplete.sampleH
  exact cHOnly_get.bind fun _ ↦ (cHOnly_liftH _).bind fun _ ↦ (cHOnly_set _).bind fun _ ↦ cHOnly_pure _

theorem cHOnly_finish : CHOnly (UniStatement.finish (m := OracleComp KeccakCalls)) := by
  unfold UniStatement.finish
  exact cHOnly_get.bind fun _ ↦ cHOnly_ite _ (cHOnly_pure _) (cHOnly_throw _)

/-- **π2's walk on the calldata only hashes.** -/
theorem cHOnly_reduceWithH (s : Spec) (stmt : List E) : CHOnly (Pi2H.reduceWithH callKeccak256 s stmt) := by
  unfold Pi2H.reduceWithH
  refine (cHOnly_forIn_list _ _ _ fun rd pubs ↦ ?_).bind fun pubs ↦ ?_
  · rcases rd with b | _ | _
    · exact (cHOnly_nextInteger b).bind fun _ ↦ cHOnly_pure _
    · exact cHOnly_nextRoot.bind fun _ ↦ cHOnly_pure _
    · exact cHOnly_nextScalar.bind fun _ ↦ cHOnly_pure _
  · exact cHOnly_nextRoot.bind fun _ ↦ cHOnly_sampleH.bind fun _ ↦ cHOnly_sampleH.bind fun _ ↦
      cHOnly_sampleH.bind fun _ ↦ cHOnly_nextRoot.bind fun _ ↦ cHOnly_sampleH.bind fun _ ↦
      (cHOnly_nextScalars _).bind fun _ ↦ cHOnly_nextScalar.bind fun _ ↦ cHOnly_sampleH.bind fun _ ↦
      cHOnly_pure _

/-- **The contract's run on the calldata only hashes.** -/
theorem hOnly_runWithH (s : Spec) (iv input : List UInt8) (stream : Array UInt8) :
    HOnly (Pi2H.runWithH callKeccak256 s iv input stream) := by
  unfold Pi2H.runWithH
  refine (hOnly_queryH _).bind fun seed ↦ ?_
  exact (((cHOnly_reduceWithH s _).bind fun _ ↦ cHOnly_finish.bind fun _ ↦ cHOnly_pure _)
    (Chan.start seed stream)).bind fun _ ↦ hOnly_pure _

/-! ## The setup, the IV, the prover's stream -/

/-- **The setup only hashes** (π1's three trees, π2's setup tree). -/
theorem hOnly_setupTreesWithH2 (D : RecDeployment) : HOnly (Pi2H.setupTreesWithH callKeccak256 callKeccakF1600 D) := by
  unfold Pi2H.setupTreesWithH Pi2H.setupTreeWithH
  exact (UniComplete.hOnly_setupTreesWithH D.pi1).bind fun _ ↦ (E2ECompleteness.hOnly_commitWithH _ _).bind fun _ ↦
    hOnly_pure _

/-- **π2's IV only hashes** (the digest's three hashes, the IV's). -/
theorem hOnly_ivOfH (D : RecDeployment) (roots : RecSetupRoots) : HOnly (Pi2H.ivOfH callKeccak256 D roots) := by
  unfold Pi2H.ivOfH Pi2H.digestWithH Pi2H.ivWithH
  exact (((hOnly_queryH _).bind fun _ ↦ (hOnly_queryH _).bind fun _ ↦ (hOnly_queryH _).bind fun _ ↦
    hOnly_pure _).bind fun _ ↦ (hOnly_queryH _).bind fun _ ↦ hOnly_pure _)

/-- **The public values' writes only hash** (they do not hash). -/
theorem wHOnly_sendPublic : ∀ l : List (Read × PublicValue), WHOnly (sendPublic (m := OracleComp KeccakCalls) l)
  | [] => wHOnly_pure _
  | (.integer _, .integer _) :: rest => (wHOnly_sendInteger _ _).bind fun _ ↦ wHOnly_sendPublic rest
  | (.integer _, .root _) :: rest => wHOnly_sendPublic rest
  | (.integer _, .scalar _) :: rest => wHOnly_sendPublic rest
  | (.root, .integer _) :: rest => wHOnly_sendPublic rest
  | (.root, .root _) :: rest => (wHOnly_sendRoot _).bind fun _ ↦ wHOnly_sendPublic rest
  | (.root, .scalar _) :: rest => wHOnly_sendPublic rest
  | (.scalar, .integer _) :: rest => wHOnly_sendPublic rest
  | (.scalar, .root _) :: rest => wHOnly_sendPublic rest
  | (.scalar, .scalar _) :: rest => (wHOnly_sendScalar _).bind fun _ ↦ wHOnly_sendPublic rest

theorem wHOnly_pre2 (G : RecPiop.Circuit E) (reads : List Read) (values : List PublicValue) (w : ℕ → K) :
    WHOnly (pre2 callKeccak256 G reads values w) := by
  unfold pre2
  exact (wHOnly_sendPublic _).bind fun _ ↦ (wHOnly_lift (E2ECompleteness.hOnly_commitWithH _ _)).bind fun _ ↦
    (wHOnly_sendRoot _).bind fun _ ↦ wHOnly_pure _

theorem wHOnly_mid2 (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ : E) : WHOnly (mid2 callKeccak256 G w α β γ) := by
  unfold mid2
  exact (wHOnly_lift (E2ECompleteness.hOnly_commitWithH _ _)).bind fun _ ↦ (wHOnly_sendRoot _).bind fun _ ↦
    wHOnly_pure _

theorem wHOnly_post2 (G : RecPiop.Circuit E) (setupStack : Array K) (input : List UInt8) (values : List PublicValue)
    (w : ℕ → K) (wS : Array K) (wT : LeanVM.Prover.Tree) (qS : Array K) (qT : LeanVM.Prover.Tree) (α β γ t : E) :
    WHOnly (post2 callKeccak256 G setupStack input values w wS wT qS qT α β γ t) := by
  unfold post2
  exact (wHOnly_sendScalars _).bind fun _ ↦ wHOnly_sampleW.bind fun _ ↦ wHOnly_get.bind fun _ ↦ wHOnly_pure _

/-! ## The verifiers -/

/-- **π1-rec3's graph with its three `PCS_OPEN`s is disciplined.** -/
theorem disc_pi1GraphVerifierWithH (D : RecDeployment) (roots : UniStatement.SetupRoots) (input : Vector UInt8 32)
    (p : UniStatement.UniProof) : Disc (Pi2H.pi1GraphVerifierWithH callKeccak256 callKeccakF1600 D roots input p) := by
  unfold Pi2H.pi1GraphVerifierWithH
  split
  · exact disc_pure _
  · split
    · exact disc_pure _
    · split
      · exact disc_pure _
      · split
        · exact disc_pure _
        · refine (disc_forIn_list _ _ _ fun x s ↦ ?_).bind fun _ ↦ disc_pure _
          exact (UniComplete.disc_pcsOpenWithH _ _ _ _).bind fun _ ↦ disc_pure _

/-- **`PCS_OPEN` on a call's words is disciplined.** -/
theorem disc_pcsOpenAtH (reg : List (List UInt8 × Opener)) (words : List (List UInt8)) (p : Compile.Proof) :
    Disc (Pi2H.pcsOpenAtH callKeccak256 callKeccakF1600 reg words p) := by
  unfold Pi2H.pcsOpenAtH
  split
  · exact disc_pure _
  · exact UniComplete.disc_pcsOpenWithH _ _ _ _
  · exact E2ECompleteness.disc_openingWithH _ _ _ _

/-- **The contract is disciplined.** -/
theorem disc_contractWithH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    Disc (Pi2H.contractWithH callKeccak256 callKeccakF1600 D roots input proof) := by
  unfold Pi2H.contractWithH
  refine (disc_of_hOnly (hOnly_ivOfH D roots)).bind fun _ ↦ (disc_of_hOnly (hOnly_runWithH _ _ _ _)).bind fun o ↦ ?_
  split
  · exact disc_pure _
  · split
    · exact disc_pure _
    · dsimp only
      split
      · exact disc_pure _
      · refine (disc_forIn_list _ _ _ fun x s ↦ ?_).bind fun _ ↦ disc_pure _
        exact (disc_pcsOpenAtH _ _ _).bind fun _ ↦ disc_pure _

theorem disc_verifierWithH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    Disc (Pi2H.verifierWithH callKeccak256 callKeccakF1600 D roots input proof) := by
  unfold Pi2H.verifierWithH
  exact (disc_contractWithH D roots input proof).bind fun _ ↦ disc_pure _

/-! ## The staged run -/

theorem disc_stageA (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (hP : Disc P1k) (input : Vector UInt8 32) :
    Disc (stageA callKeccak256 callKeccakF1600 D C Fa P1k input) := by
  unfold stageA
  refine (disc_of_hOnly (hOnly_setupTreesWithH2 D)).bind fun trees ↦ hP.bind fun o ↦ ?_
  cases o with
  | none => exact disc_pure _
  | some p1 =>
    refine (disc_pi1GraphVerifierWithH D _ input p1).bind fun _ ↦
      (disc_of_hOnly (hOnly_setupTreesWithH2 D)).bind fun tr ↦
      (disc_of_hOnly (hOnly_ivOfH D tr.roots)).bind fun iv ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun seed ↦ ?_
    exact (disc_of_hOnly (wHOnly_pre2 _ _ _ _ _)).bind fun _ ↦ disc_pure _

theorem disc_stageB (D : RecDeployment) (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest) :
    Disc (stageB callKeccak256 D C a s₁ s₂ s₃) := by
  unfold stageB
  exact (disc_of_hOnly (wHOnly_mid2 _ _ _ _ _ _)).bind fun _ ↦ disc_pure _

theorem disc_stageC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB) (st : Digest) :
    Disc (stageC callKeccak256 callKeccakF1600 D C input b st) := by
  unfold stageC
  split
  · exact disc_pure _
  · refine (disc_of_hOnly (wHOnly_post2 _ _ _ _ _ _ _ _ _ _ _ _ _ _)).bind fun x ↦ ?_
    refine (E2ECompleteness.disc_proveOpeningWithH _ _ _ _ _).bind fun pW ↦
      (E2ECompleteness.disc_proveOpeningWithH _ _ _ _ _).bind fun pS ↦
      (E2ECompleteness.disc_proveOpeningWithH _ _ _ _ _).bind fun pQ ↦ ?_
    split
    · exact (disc_verifierWithH _ _ _ _).bind fun _ ↦ disc_pure _
    · exact disc_pure _

/-- **The staged run is disciplined**, for any disciplined π1 prover. -/
theorem disc_pi2Staged (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (hP : Disc P1k) (input : Vector UInt8 32) :
    Disc (pi2Staged D C Fa P1k input).run := by
  unfold Pi2P.Pi2Staged.run Pi2P.staged3 Pi2P.Pi2Staged.tail
  refine (disc_stageA D C Fa P1k hP input).bind fun a ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun _ ↦
    (disc_of_hOnly (hOnly_queryH _)).bind fun _ ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun _ ↦ ?_
  refine ((disc_stageB D C a _ _ _).bind fun b ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun st ↦
    (disc_stageC D C input b st).bind fun _ ↦ disc_pure _).bind fun _ ↦ disc_pure _

/-- **`Pi2RunDuplex` for π1-rec3's honest prover** (`disc_uniProverRec3With`, its Flock prover hash-only by its
commutation). -/
theorem pi2RunDuplex_p1k (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) :
    Pi2RunDuplex D C Fa (p1k D) := fun input rows q _ _ ↦
  (duplexVm_iff_duplexP _ _).mpr (disc_pi2Staged D C Fa _ (UniComplete.Rec3.disc_uniProverRec3With
    UniComplete.Rec3.flockProve3H (UniComplete.flockHashOnly_of_commutes _ UniComplete.Rec3.flockCommutes_flockProve3H)
    D.pi1 input rows q) input [])

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2G.disc_pi2Staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.disc_pi2Staged

/-- info: 'RecCompose.Pi2G.pi2RunDuplex_p1k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.pi2RunDuplex_p1k
