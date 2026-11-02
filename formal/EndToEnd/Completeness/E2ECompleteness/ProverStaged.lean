-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the two calls (`KeccakCalls`) and their simulation lemmas (`implH`, `implF`,
-- `simulateQ_queryH`).
import E2ECompleteness.ProverAccept

/-!
# The prover bridge on the staged run

Bridge-Completeness splits the two-call experiment into the chain's stages (`Staging.lean`:
`stageAG`, the setup, the index and witness trees and the label's hash; `stageBG`, the quotient tree
from `α, β, γ`; `proverTail`, the prover's tail from `t`). Here the stages are run with the two calls
answered by functions `H`, `F` (`implHF`, the `Id` monad), and:

* **`acc_stagedG`** (the acceptance part of `RejectGood`): when the prover's tail returns a proof and
  the staged run's challenges `(α, β, t)` avoid `badSet`, the verifier accepts it;
* **`red_stagedG`**: when the challenges avoid `badSet`, the reduction inside the prover's tail returns
  claims, so the tail fails only at an opening, that is a proof-of-work search;

for any circuit of `2^22` rows whose cells and wiring are the honest ones, and **`acc_staged`**,
**`red_staged`** at the membership circuit and the cells of a witness. Each stage at functions is its
stretch of `proveSpec` (`stageAG_id`, `stageBG_id`, `proverTail_id`), and the run's challenges are the
chain's, so `accept_core` and `reduce_honest` (`ProverAccept.lean`) apply.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness

/-- **The two calls answered by functions**: Keccak-256 by `H`, Keccak-f[1600] by `F`. -/
def implHF (H : Bytes → Digest) (F : KeccakState → KeccakState) : QueryImpl KeccakCalls Id
  | .inl x => (H x : Digest)
  | .inr s => (F s : KeccakState)

theorem implH_implHF (H : Bytes → Digest) (F : KeccakState → KeccakState) :
    implH (implHF H F) = H := rfl

theorem implF_implHF (H : Bytes → Digest) (F : KeccakState → KeccakState) :
    implF (implHF H F) = F := rfl

/-- The proof the prover's tail builds (`proverTail`'s `proof`). -/
def tailProof (C : Circuit) (a : AuxA) (bq : Tree × Array K) (t : E) : ReductionProof :=
  ⟨digestScalars a.2.2.1.root, digestScalars bq.1.root,
    Vector.ofFn fun j ↦
      novelEval a.2.2.2.1 j.val 4 (((digitsOf t (cellVars C.logRows)).drop 2).take
          (cellVars C.logRows - 2)) +
        (digitsOf t (cellVars C.logRows)).getD (cellVars C.logRows) 0 *
          novelEval a.2.2.2.2.1 j.val 4 (((digitsOf t (cellVars C.logRows)).drop 2).take 2),
    novelEval C.wiringTable 0 1 ((digitsOf t (cellVars C.logRows)).take (cellVars C.logRows))⟩

section Stages

attribute [local irreducible] commitWithH witnessStack quotientStack Layout.stackOf
  Domain.coefficients Domain.values quotientStackOf reduceWithH proveOpeningWithH

variable (H : Bytes → Digest) (F : KeccakState → KeccakState)

/-- **Stage A at functions.** -/
theorem stageAG_id (setup : OracleComp KeccakCalls Digest) (C : Circuit) (cells : Array K)
    (masks : Masks) (wp : Padding) (stmt : Statement) :
    simulateQ (implHF H F) (stageAG setup C cells masks wp stmt) =
      ((simulateQ (implHF H F) setup,
        commitWithH (m := Id) H (cellVars C.logRows) C.wiringTable,
        commitWithH (m := Id) H (cellVars C.logRows + 1)
          (witnessStack C.logRows (coefficients (cellVars C.logRows) 0 cells) (maskEntries masks) wp),
        coefficients (cellVars C.logRows) 0 cells, maskEntries masks,
        witnessStack C.logRows (coefficients (cellVars C.logRows) 0 cells) (maskEntries masks) wp),
      H (label (commitWithH (m := Id) H (cellVars C.logRows) C.wiringTable).root stmt),
      digestScalars (commitWithH (m := Id) H (cellVars C.logRows + 1)
        (witnessStack C.logRows (coefficients (cellVars C.logRows) 0 cells) (maskEntries masks)
          wp)).root) := by
  simp only [stageAG, simulateQ_bind, simulateQ_pure, simulateQ_commitWithH, simulateQ_queryH,
    implH_implHF]
  rfl

/-- **Stage B at functions.** -/
theorem stageBG_id (C : Circuit) (cells : Array K) (qp : Padding) (a : AuxA) (s₁ s₂ s₃ : Digest) :
    simulateQ (implHF H F) (stageBG C cells qp a s₁ s₂ s₃) =
      ((commitWithH (m := Id) H (cellVars C.logRows + 4)
          (quotientStackOf C cells qp a.2.2.2.1 a.2.2.2.2.1 (challengeOf s₁) (challengeOf s₂)
            (challengeOf s₃)),
        quotientStackOf C cells qp a.2.2.2.1 a.2.2.2.2.1 (challengeOf s₁) (challengeOf s₂)
          (challengeOf s₃)),
      digestScalars (commitWithH (m := Id) H (cellVars C.logRows + 4)
        (quotientStackOf C cells qp a.2.2.2.1 a.2.2.2.2.1 (challengeOf s₁) (challengeOf s₂)
          (challengeOf s₃))).root) := by
  simp only [stageBG, simulateQ_bind, simulateQ_pure, simulateQ_commitWithH, implH_implHF]
  rfl

/-- **The prover's tail at functions** is the prover's end (`finishSpec`) on its proof. -/
theorem proverTail_id (C : Circuit) (fuel : ℕ) (stmt : Statement) (a : AuxA) (bq : Tree × Array K)
    (t : E) :
    simulateQ (implHF H F) (proverTail C fuel stmt a bq t) =
      finishSpec (m := Id) H F fuel C.logRows stmt a.2.1 a.2.2.1 bq.1 C.wiringTable a.2.2.2.2.2 bq.2
        (tailProof C a bq t) := by
  unfold proverTail finishSpec
  simp only [simulateQ_bind, simulateQ_reduceWithH, implH_implHF]
  congr 1; funext x
  split
  · simp
  · simp only [simulateQ_bind, simulateQ_proveOpeningWithH, implH_implHF, implF_implHF]
    congr 1; funext o₁
    split
    · simp only [simulateQ_bind, simulateQ_proveOpeningWithH, implH_implHF, implF_implHF]
      congr 1; funext o₂
      split
      · simp only [simulateQ_bind, simulateQ_proveOpeningWithH, implH_implHF, implF_implHF]
        congr 1; funext o₃
        split <;> simp <;> rfl
      · simp
    · simp

end Stages

/-! ## The quotient stack, named -/

section Named


/-- `quotientStackOf` is `proveSpec`'s quotient stack, with its computations named. -/
theorem quotientStackOf_eq (C : Circuit) (cells : Array K) (qp : Padding) (wHat mask : Array K)
    (α β γ : E) :
    quotientStackOf C cells qp wHat mask α β γ =
      quotientStack C.logRows (coefficients (cellVars C.logRows) 0 (hValues C.logRows cells C.sigma α β γ))
        (coefficients (cellVars C.logRows + 2) (betaAt (cellVars C.logRows + 2))
          (qValuesOf C.logRows (wValuesOf C.logRows wHat mask) (sigmaValuesOf C.logRows C.wiringTable)
            (q0Of C.logRows (coefficients (cellVars C.logRows) 0 (hValues C.logRows cells C.sigma α β γ)))
            (blocksOf C.logRows γ) α β))
        (coefficients (cellVars C.logRows + 2) (betaAt (cellVars C.logRows + 2))
          (qGateValuesOf C.logRows (wValuesOf C.logRows wHat mask) (blocksOf C.logRows γ))) qp :=
  rfl

end Named

/-! ## The chain in the staged form -/

/-- **The reduction's chain, in the staged run's form**: its `α, β, γ, t` are the challenges of
`s₁ = H(s₀ ‖ r₁)`, `s₂ = H(s₁)`, `s₃ = H(s₂)`, `s₄ = H(s₃ ‖ r₂)`. -/
theorem chainH_staged (H : Bytes → Digest) (ir : Digest) (stmt : Statement) (p : ReductionProof) :
    let s₁ := H (chainIn (H (label ir stmt)) p.witnessRoot)
    let s₂ := H (digestBytes s₁)
    let s₃ := H (digestBytes s₂)
    (chainH H ir stmt p).1 = challengeOf s₁ ∧ (chainH H ir stmt p).2.1 = challengeOf s₂ ∧
      (chainH H ir stmt p).2.2.1 = challengeOf s₃ ∧
      (chainH H ir stmt p).2.2.2.1 = challengeOf (H (chainIn s₃ p.quotientRoot)) := by
  simp only [chainH, squeezeWithH_id, Chain.absorb, List.nil_append, List.flatMap_nil,
    List.append_nil, chainIn_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-! ## The acceptance and the reduction on the staged run -/

section Staged

attribute [local irreducible] commitWithH witnessStack quotientStack Layout.stackOf
  Domain.coefficients Domain.values reduceWithH proveOpeningWithH openingWithH hValues qValuesOf
  qGateValuesOf novelEval

variable (hK : Constants) (hcl : Bridge.ClaimsMatch stmtConsts) (hT : TablesMatch)
  (H : Bytes → Digest) (F : KeccakState → KeccakState) (C : Circuit) (hC : C.logRows = 22)
  (setup : OracleComp KeccakCalls Digest)
  (hsetup : simulateQ (implHF H F) setup =
    (commitWithH (m := Id) H (cellVars C.logRows) C.wiringTable).root)
  (stmt : Statement) (w : PcsQuotient.Secret) (hrel : Relation stmt w) (masks : Masks)
  (wp qp : Padding) (cells : Array K) (hcs : cells.size = 2 ^ 24)
  (hcells : ∀ b, cells.getD (Completeness.idx b) 0 =
    Completeness.cellBitsK Completeness.deployedMembership (secretOf w) b)
  (hss : C.sigma.size = 2 ^ 24)
  (hsig : ∀ b, point (C.sigma.getD (Completeness.idx b) 0) = deployedBasis.point (deployedSigma b))
  (A : AuxA × Digest × (E × E))
  (hA : simulateQ (implHF H F) (stageAG setup C cells masks wp stmt) = A)
  (s₁ s₂ s₃ : Digest) (hs₁ : H (chainIn A.2.1 A.2.2) = s₁) (hs₂ : H (digestBytes s₁) = s₂)
  (hs₃ : H (digestBytes s₂) = s₃)
  (B : (Tree × Array K) × (E × E)) (hB : simulateQ (implHF H F) (stageBG C cells qp A.1 s₁ s₂ s₃) = B)
  (s₄ : Digest) (hs₄ : H (chainIn s₃ B.2) = s₄)
  (hgood : (challengeOf s₁, challengeOf s₂, challengeOf s₄) ∉ badSet w masks)

include hC hsetup hA hB in
/-- The staged run's tables and proof are the honest tail's (`ProverAccept.lean`). -/
theorem staged_forms :
    C.wiringTable = sigmaHatOf C.sigma ∧
    A.1.1 = (commitWithH (m := Id) H 24 (sigmaHatOf C.sigma)).root ∧
    A.1.2.1 = commitWithH (m := Id) H 24 (sigmaHatOf C.sigma) ∧
    A.1.2.2.1 = commitWithH (m := Id) H 25 (wStackOf cells masks wp) ∧
    A.1.2.2.2.1 = wHatOf cells ∧ A.1.2.2.2.2.1 = maskEntries masks ∧
    A.1.2.2.2.2.2 = wStackOf cells masks wp ∧
    A.2.1 = H (label (commitWithH (m := Id) H 24 (sigmaHatOf C.sigma)).root stmt) ∧
    A.2.2 = digestScalars (commitWithH (m := Id) H 25 (wStackOf cells masks wp)).root ∧
    B.1.1 = commitWithH (m := Id) H 28
      (qStackOf cells C.sigma masks qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃)) ∧
    B.1.2 = qStackOf cells C.sigma masks qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃) ∧
    B.2 = digestScalars (commitWithH (m := Id) H 28
      (qStackOf cells C.sigma masks qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃))).root := by
  have hwt : C.wiringTable = sigmaHatOf C.sigma := by
    rw [Circuit.wiringTable, hC]
    rfl
  have hwS : witnessStack C.logRows (coefficients (cellVars C.logRows) 0 cells) (maskEntries masks)
      wp = wStackOf cells masks wp := by
    rw [witnessStack_eq, hC]
    rfl
  have hidx : commitWithH (m := Id) H (cellVars C.logRows) C.wiringTable =
      commitWithH (m := Id) H 24 (sigmaHatOf C.sigma) := by
    rw [hwt, hC]
    rfl
  have hwT : commitWithH (m := Id) H (cellVars C.logRows + 1)
      (witnessStack C.logRows (coefficients (cellVars C.logRows) 0 cells) (maskEntries masks) wp) =
      commitWithH (m := Id) H 25 (wStackOf cells masks wp) := by
    rw [hwS, hC]
    rfl
  rw [stageAG_id] at hA
  subst hA
  have hqS : ∀ α β γ, quotientStackOf C cells qp (coefficients (cellVars C.logRows) 0 cells)
      (maskEntries masks) α β γ = qStackOf cells C.sigma masks qp α β γ := by
    intro α β γ
    rw [quotientStackOf_eq, quotientStack_eq, hwt, hC]
    rfl
  rw [stageBG_id] at hB
  subst hB
  refine ⟨hwt, by rw [hsetup, hidx], hidx, hwT, ?_, rfl, hwS, by rw [hidx], by rw [hwT], ?_, ?_, ?_⟩
  · show coefficients (cellVars C.logRows) 0 cells = wHatOf cells
    rw [hC]
    rfl
  · show commitWithH (m := Id) H (cellVars C.logRows + 4) _ = _
    rw [hqS, hC]
    rfl
  · exact hqS _ _ _
  · show digestScalars (commitWithH (m := Id) H (cellVars C.logRows + 4) _).root = _
    rw [hqS, hC]
    rfl

include hK hcl hT hC hsetup hrel hcs hcells hss hsig hA hs₁ hs₂ hs₃ hB hs₄ hgood in
/-- **The reduction inside the prover's tail returns claims** when the staged run's challenges avoid
`badSet`: the tail can then fail only at an opening's proof of work. -/
theorem red_stagedG :
    reduceWithH (m := Id) H C.logRows A.1.2.1.root stmt (tailProof C A.1 B.1 (challengeOf s₄)) ≠
      none := by
  obtain ⟨hwt, -, hidx, hwT, hwH, hmk, hwS, hs0, hr1, hqT, hqS, hr2⟩ :=
    staged_forms H F C hC setup hsetup stmt masks wp qp cells A hA s₁ s₂ s₃ B hB
  have htail : tailProof C A.1 B.1 (challengeOf s₄) = proofOf H cells C.sigma masks wp qp
      (challengeOf s₁) (challengeOf s₂) (challengeOf s₃) (challengeOf s₄) := by
    unfold tailProof proofOf
    rw [hwT, hqT, hwH, hmk, hwt, hC]
    rfl
  have hch := chainH_staged H (commitWithH (m := Id) H 24 (sigmaHatOf C.sigma)).root stmt
    (proofOf H cells C.sigma masks wp qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃)
      (challengeOf s₄))
  dsimp only at hch
  have e₁ : H (chainIn (H (label (commitWithH (m := Id) H 24 (sigmaHatOf C.sigma)).root stmt))
      (proofOf H cells C.sigma masks wp qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃)
        (challengeOf s₄)).witnessRoot) = s₁ := by
    rw [← hs₁, hs0, hr1]
    rfl
  rw [e₁, hs₂, hs₃] at hch
  have e₄ : (proofOf H cells C.sigma masks wp qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃)
      (challengeOf s₄)).quotientRoot = B.2 := by rw [hr2]; rfl
  rw [e₄, hs₄] at hch
  obtain ⟨cl, hred, -⟩ := reduce_honest hK hcl hT H stmt w hrel masks wp qp cells C.sigma hcs hcells
    hss hsig _ _ _ _ hch.1 hch.2.1 hch.2.2.1 hch.2.2.2 hgood
  rw [hC, hidx, htail, hred]
  exact Option.some_ne_none _

include hK hcl hT hC hsetup hrel hcs hcells hss hsig hA hs₁ hs₂ hs₃ hB hs₄ hgood in
/-- **The staged run's honest proof is accepted** (`RejectGood`'s acceptance part): at functions
`H`, `F`, when the prover's tail returns a proof and the staged run's challenges avoid `badSet`, the
verifier, on the setup's root, accepts it. -/
theorem acc_stagedG (hO : OpeningAccepts) (fuel : ℕ) (π : PcsQuotient.Proof)
    (hπ : simulateQ (implHF H F) (proverTail C fuel stmt A.1 B.1 (challengeOf s₄)) = some π) :
    verifyWithH (m := Id) H F 22 A.1.1 stmt π = true := by
  obtain ⟨hwt, hroot, hidx, hwT, hwH, hmk, hwS, hs0, hr1, hqT, hqS, hr2⟩ :=
    staged_forms H F C hC setup hsetup stmt masks wp qp cells A hA s₁ s₂ s₃ B hB
  have htail : tailProof C A.1 B.1 (challengeOf s₄) = proofOf H cells C.sigma masks wp qp
      (challengeOf s₁) (challengeOf s₂) (challengeOf s₃) (challengeOf s₄) := by
    unfold tailProof proofOf
    rw [hwT, hqT, hwH, hmk, hwt, hC]
    rfl
  have hch := chainH_staged H (commitWithH (m := Id) H 24 (sigmaHatOf C.sigma)).root stmt
    (proofOf H cells C.sigma masks wp qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃)
      (challengeOf s₄))
  dsimp only at hch
  have e₁ : H (chainIn (H (label (commitWithH (m := Id) H 24 (sigmaHatOf C.sigma)).root stmt))
      (proofOf H cells C.sigma masks wp qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃)
        (challengeOf s₄)).witnessRoot) = s₁ := by
    rw [← hs₁, hs0, hr1]
    rfl
  rw [e₁, hs₂, hs₃] at hch
  have e₄ : (proofOf H cells C.sigma masks wp qp (challengeOf s₁) (challengeOf s₂) (challengeOf s₃)
      (challengeOf s₄)).quotientRoot = B.2 := by rw [hr2]; rfl
  rw [e₄, hs₄] at hch
  rw [proverTail_id, hidx, hwT, hqT, hwS, hqS, htail, hC, hwt] at hπ
  obtain ⟨red, hred, hoW, hoσ, hoQ, hpr⟩ := finishSpec_id_some H F hπ
  have hπe : π = ⟨proofOf H cells C.sigma masks wp qp (challengeOf s₁) (challengeOf s₂)
      (challengeOf s₃) (challengeOf s₄), π.witness, π.wiring, π.quotient⟩ := by
    rw [← hpr]
  rw [hroot, hπe]
  refine accept_core hK hcl hT H stmt w hrel masks wp qp cells C.sigma hcs hcells hss hsig _ _ _ _
    hch.1 hch.2.1 hch.2.2.1 hch.2.2.2 hgood hO F fuel π.witness π.wiring π.quotient
    fun red' hred' ↦ ?_
  rw [hred] at hred'
  obtain rfl := Option.some.inj hred'
  exact ⟨hoW, hoσ, hoQ⟩

end Staged

end E2ECompleteness

/-- info: 'E2ECompleteness.stageAG_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.stageAG_id

/-- info: 'E2ECompleteness.proverTail_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.proverTail_id

/-- info: 'E2ECompleteness.red_stagedG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.red_stagedG

/-- info: 'E2ECompleteness.acc_stagedG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.acc_stagedG
