-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the duplex discipline (`LeanVM.Rpm.DuplexVm`, `DuplexP`, `HOnly`), and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Duplex.lean`'s `Disc`, `disc_openingWithH`.
import UniComplete.Rec3VerifierHSim
import UniComplete.VerifierHDuplex

/-!
# The duplex discipline of π1-rec3's verifier

Over the two calls, every Keccak-f[1600] call of π1-rec3's deployed verifier continues a duplex or starts one at a
zero capacity (mumbai's `DuplexVm`): **`duplexVm_verifierRec3WithH`**, from any earlier answers
(`disc_verifierRec3WithH`, that is **`verifierDisc3 : VerifierDisc3`**, `Rec3Hyp.lean`).

**The walk only hashes, by naturality**, as `VerifierHDuplex.lean` reads the main line's: the run over
`callKeccak256` is the run over the hash alone (`HashCalls`, `callHash`) simulated by `callKeccak256`
(`hashToCalls`), by `Rec3VerifierHSim.lean`'s commutation with any monad morphism (`Rec3.Morph.app_runWithFsH`), and
anything so simulated calls the hash only (`hOnly_simulateQ_hash`); the IV likewise (`Rec3.Morph.app_ivRec3WithH`).
The permutation is called by the openings only (three with the walk, `C1`, `C2`, the setup; five without), each
disciplined (`disc_pcsOpenWithH`, E2ECompleteness's `disc_openingWithH`).

Decisions: stated, as `Rec3VerifierHSim.lean`'s lemmas, at every configuration of the run and of `verifyWithFsH`
(`blake2s`, `mode`, `fs`, `walk`); the main line's hash-only oracle and its lemmas (`HashCalls`, `callHash`,
`hashToCalls`, `hOnly_simulateQ_hash`, `sim_callHash`, `disc_forIn_list`, `disc_pcsOpenWithH`) are reused unchanged.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement
open E2ECompleteness (Disc disc_pure disc_of_hOnly)

namespace UniComplete.Rec3

open UniComplete (HashCalls callHash hashToCalls hOnly_simulateQ_hash sim_callHash disc_forIn_list
  disc_pcsOpenWithH)

/-! ## The hash alone -/

/-- **π1-rec3's run on calldata only hashes**, at every configuration. -/
theorem hOnly_runWithFsH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) (fs : FsShape) (walk : Bool) :
    HOnly (runWithFsH callKeccak256 shape iv publicInput stream blake2s mode fs walk) := by
  rw [← sim_callHash, ← Morph.app_runWithFsH (UniComplete.Morph.sim hashToCalls) callHash]
  exact hOnly_simulateQ_hash _

/-- π1-rec3's IV only hashes. -/
theorem hOnly_ivRec3WithH (D : Deployment) (roots : SetupRoots) :
    HOnly (Deployment.ivRec3WithH callKeccak256 D roots) := by
  rw [← sim_callHash, ← Morph.app_ivRec3WithH (UniComplete.Morph.sim hashToCalls) callHash]
  exact hOnly_simulateQ_hash _

/-! ## The verifier -/

/-- **π1-rec3's verifier is disciplined**, from any earlier answers. -/
theorem disc_verifyWithFsH (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) (fs : FsShape) (walk : Bool) :
    Disc (verifyWithFsH callKeccak256 callKeccakF1600 shape iv roots publicInput proof fs walk) := by
  unfold verifyWithFsH
  refine (disc_of_hOnly (hOnly_runWithFsH _ _ _ _ _ _ _ _)).bind fun o ↦ ?_
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
        · exact disc_pure _

/-- **π1-rec3's deployed verifier is disciplined**, from any earlier answers. -/
theorem disc_verifierRec3WithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof) :
    Disc (Deployment.verifierRec3WithH callKeccak256 callKeccakF1600 D roots input proof) := by
  unfold Deployment.verifierRec3WithH
  exact (disc_of_hOnly (hOnly_ivRec3WithH _ _)).bind fun _ ↦ disc_verifyWithFsH _ _ _ _ _ _ _

/-- **`VerifierDisc3`**: π1-rec3's deployed verifier is disciplined, from any earlier answers. -/
theorem verifierDisc3 : VerifierDisc3 := disc_verifierRec3WithH

/-- **π1-rec3's deployed verifier follows the duplex discipline** (mumbai's `DuplexVm`, from no earlier answer). -/
theorem duplexVm_verifierRec3WithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) :
    DuplexVm (Deployment.verifierRec3WithH callKeccak256 callKeccakF1600 D roots input proof) [] :=
  (duplexVm_iff_duplexP _ _).mpr (disc_verifierRec3WithH D roots input proof [])

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.verifierDisc3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.verifierDisc3

/-- info: 'UniComplete.Rec3.duplexVm_verifierRec3WithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.duplexVm_verifierRec3WithH
