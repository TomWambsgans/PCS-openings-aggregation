-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `formal/UniSound/UniSound/FsVerifier.lean`
-- (`uniVerifierBridge_of_walk`) to π2's contract (`formal/RecStatement/RecStatement/Security.lean`, `contractWith`).
import RecCompose.FsOps
import UniSound.FsVerifier

/-!
# π2's verifier bridge

**`pi2VerifierBridge`**: from any state of the lazily sampled permutation, π2's contract past its IV
(`contractRest`: π2's run on the stream, then the six `PCS_OPEN` calls) accepts at most as often as the composed
verifier (the chain `pi2Spec`, then the six openings `p2Ops`) passes `p2Check` with every opening accepting, from the
walk (`Pi2Walk`, `Pi2WalkReject`):

* a stream of another length is rejected (`Pi2WalkReject`);
* on a stream of `944` bytes the run is the chain (`Pi2Walk` at `F = π`), which both sides run first;
* per challenges: the run's verdict `all ≠ 0`; the six calls (`pcsCalls`) decode under the registry to the composed
  openings' inputs (π1's three on their plain layouts, `UniSound.pcsOpen_eq_early`; π2's three on `shW`, `shS`, `shQ`,
  `Bridge.openingWith_eq_ourVerifier'`), each F2's opening with the Statement's early stop, accepting at most as often
  as the composed one (`UniSound.early_le_rpm`); a call that does not decode rejects.
-/

set_option linter.unusedSectionVars false
-- TODO(remove with the sorry): the skeleton builds downstream while the bridge is proved.
set_option warningAsError false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local instance high] Completeness.instSampleableTypeE_completeness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack RecStatement.layoutWords

section With

variable {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)

/-- **π2's contract past its IV** (`contractWith` after `ivWith`): π2's run at the IV, then the six calls. -/
def contractRest (D : RecDeployment) (roots : RecSetupRoots) (iv : List UInt8) (input : Vector UInt8 32)
    (proof : RecProof) : m (Bool × List (List (List UInt8))) := do
  let c := D.circuitAt roots.pi1
  let o ← runWith F (Spec.of c.circuit) iv input.toList proof.stream
  match o.result with
  | .error _ => return (false, [])
  | .ok r =>
    if !o.accepts then return (false, []) else
    let calls := pcsCalls c.circuit (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2)
      proof.stream r
    if calls.length ≠ 6 then return (false, calls) else
    let reg := registryOf D.pi1.shape c.circuit.logN
    let mut ok := true
    for (words, p) in calls.zip proof.openings do
      ok := ok && (← pcsOpenAt F reg words p)
    return (ok, calls)

theorem contractWith_eq (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    D.contractWith F roots input proof = D.ivWith F roots >>= fun iv => contractRest F D roots iv input proof := rfl

end With

/-- **VERIFIER**: from any state of the lazily sampled permutation, π2's contract past its IV on a proof (its IV,
roots, input and recursive proof) accepts at most as often as the composed verifier on it passes `p2Check` with every
opening accepting. -/
def Pi2VerifierBridge (D : RecDeployment) : Prop :=
  ∀ (π : P2Pf) (s : Common.PermutationEdges LeanVM.Semantics.KeccakState),
    Pr{let x ← (simulateQ Common.lazyRandomPermutationOracles
        (contractRest Common.queryPermutation D (p2Roots π) π.iv.toList π.input π.proof)).run' s}[x.1 = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (simulateQ keccakCallsOverQueryPermutation
          (verU pi2Spec p2View (opsRun p2View (p2Ops D)) π))).run' s}[
        p2Check π v.1 ∧ ∀ k < (p2Ops D).length, v.2.getD k false = true]

/-- **THE VERIFIER BRIDGE** at the real deployment, from the walk. -/
theorem pi2VerifierBridge (D : RecDeployment) (hD : RecDeployment.Real D) (hW : Pi2Walk) (hR : Pi2WalkReject) :
    Pi2VerifierBridge D := by
  sorry

end RecCompose
