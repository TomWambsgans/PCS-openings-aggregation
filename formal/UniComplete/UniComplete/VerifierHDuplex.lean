-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the duplex discipline (`LeanVM.Rpm.DuplexVm`, `DuplexP`, `HOnly`), and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Duplex.lean`'s `Disc`, `disc_openingWithH`, `hOnly_commitWithH`.
import UniComplete.VerifierHSim
import E2ECompleteness.Duplex

/-!
# The duplex discipline of the univariate verifier and setup

Over the two calls, every Keccak-f[1600] call of the deployed verifier continues a duplex or starts one at a zero
capacity (mumbai's `DuplexVm`): **`duplexVm_verifierWithH`**, from any earlier answers
(`disc_verifierWithH`); the setup only hashes (`hOnly_setupTreesWithH`).

**The walk only hashes, by naturality.** Rather than a second pass over every function of the walk, its
hash-only-ness is read off `VerifierHSim`'s commutation: the run over `callKeccak256` is the run over the hash
oracle alone (`HashCalls`, `callHash`) simulated by `callKeccak256` (`hashToCalls`), and anything so simulated
calls the hash only (`hOnly_simulateQ_hash`). The permutation is called by the five openings only, each
disciplined (WithHash's `openingWithH`, E2ECompleteness's `disc_openingWithH`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement
open E2ECompleteness (Disc disc_pure disc_of_hOnly)

namespace UniComplete

/-! ## The hash alone -/

/-- **Keccak-256 alone**, as an oracle. -/
abbrev HashCalls : OracleSpec (List UInt8) := (List UInt8 →ₒ Digest)

/-- A call of the hash alone. -/
def callHash (x : List UInt8) : OracleComp HashCalls Digest := liftM (HashCalls.query x)

/-- The hash alone, answered by the two calls' hash. -/
def hashToCalls : QueryImpl HashCalls (OracleComp KeccakCalls) := fun x ↦ callKeccak256 x

/-- **What the hash alone simulates calls the hash only.** -/
theorem hOnly_simulateQ_hash {α : Type} (X : OracleComp HashCalls α) : HOnly (simulateQ hashToCalls X) := by
  induction X using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact hOnly_pure a
  | query_bind t k ih =>
    rw [simulateQ_bind]
    exact (show HOnly (simulateQ hashToCalls (liftM (HashCalls.query t))) by
      rw [simulateQ_spec_query]; exact hOnly_queryH t).bind ih

theorem sim_callHash : (fun x ↦ (Morph.sim hashToCalls).app (callHash x)) = callKeccak256 :=
  funext fun x ↦ simulateQ_spec_query hashToCalls x

/-- **The run on calldata only hashes.** -/
theorem hOnly_runWithH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) : HOnly (runWithH callKeccak256 shape iv publicInput stream blake2s mode) := by
  rw [← sim_callHash, ← Morph.app_runWithH (Morph.sim hashToCalls) callHash]
  exact hOnly_simulateQ_hash _

/-- The contract's IV only hashes. -/
theorem hOnly_ivWithH (D : Deployment) (roots : SetupRoots) :
    HOnly (Deployment.ivWithH callKeccak256 D roots) := by
  rw [← sim_callHash, ← Morph.app_ivWithH (Morph.sim hashToCalls) callHash]
  exact hOnly_simulateQ_hash _

/-- **The setup only hashes.** -/
theorem hOnly_setupTreesWithH (D : Deployment) : HOnly (setupTreesWithH callKeccak256 callKeccakF1600 D) := by
  unfold setupTreesWithH
  exact (E2ECompleteness.hOnly_commitWithH _ _).bind fun _ ↦ (E2ECompleteness.hOnly_commitWithH _ _).bind
    fun _ ↦ (E2ECompleteness.hOnly_commitWithH _ _).bind fun _ ↦ hOnly_pure _

/-! ## The verifier -/

/-- A loop of disciplined steps is disciplined. -/
theorem disc_forIn_list {α β : Type} (l : List α) (b : β) (f : α → β → OracleComp KeccakCalls (ForInStep β))
    (hf : ∀ a s, Disc (f a s)) : Disc (forIn l b f) := by
  induction l generalizing b with
  | nil => exact disc_pure b
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a b).bind fun s ↦ ?_
    cases s with
    | done b => exact disc_pure b
    | yield b => exact ih b

/-- `PCS_OPEN` is disciplined (WithHash's opening). -/
theorem disc_pcsOpenWithH (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : LeanVM.Protocol.Compile.Proof) :
    Disc (pcsOpenWithH callKeccak256 callKeccakF1600 vars root claims proof) :=
  E2ECompleteness.disc_openingWithH _ _ _ _

/-- **The verifier is disciplined**, from any earlier answers. -/
theorem disc_verifyWithH (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) :
    Disc (verifyWithH callKeccak256 callKeccakF1600 shape iv roots publicInput proof) := by
  unfold verifyWithH
  refine (disc_of_hOnly (hOnly_runWithH _ _ _ _ _ _)).bind fun o ↦ ?_
  split
  · exact disc_pure _
  · split
    · exact disc_pure _
    · refine (disc_forIn_list _ _ _ fun x s ↦ ?_).bind fun s ↦ ?_
      · split
        split
        · exact (disc_pcsOpenWithH _ _ _ _).bind fun _ ↦ disc_pure _
        · exact disc_pure _
      · split
        · exact (disc_pcsOpenWithH _ _ _ _).bind fun _ ↦ (disc_pcsOpenWithH _ _ _ _).bind fun _ ↦ disc_pure _
        · exact disc_pure _

/-- **The deployed verifier is disciplined**, from any earlier answers. -/
theorem disc_verifierWithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof) :
    Disc (Deployment.verifierWithH callKeccak256 callKeccakF1600 D roots input proof) := by
  unfold Deployment.verifierWithH
  exact (disc_of_hOnly (hOnly_ivWithH _ _)).bind fun _ ↦ disc_verifyWithH _ _ _ _ _

/-- **The deployed verifier follows the duplex discipline** (mumbai's `DuplexVm`, from no earlier answer). -/
theorem duplexVm_verifierWithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) :
    DuplexVm (Deployment.verifierWithH callKeccak256 callKeccakF1600 D roots input proof) [] :=
  (duplexVm_iff_duplexP _ _).mpr (disc_verifierWithH D roots input proof [])

end UniComplete

/-- info: 'UniComplete.duplexVm_verifierWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.duplexVm_verifierWithH

/-- info: 'UniComplete.disc_verifierWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.disc_verifierWithH

/-- info: 'UniComplete.hOnly_setupTreesWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.hOnly_setupTreesWithH
