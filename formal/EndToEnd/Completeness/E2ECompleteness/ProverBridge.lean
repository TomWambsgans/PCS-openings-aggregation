-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the two calls (`KeccakCalls`) and their simulation lemmas.
import E2ECompleteness.ProverStaged
import E2ECompleteness.ProverOpening

/-!
# The prover bridge, at the deployed circuit

`RejectGood`'s two deterministic parts (`Assemble.lean`), on the deployed staged run
(`stagedRun`: the setup `setupWithH`, the membership circuit, the cells of a witness), at every hash
function `H` and permutation `F`:

* **`acc_staged`**: when the prover's tail returns a proof and the staged run's challenges
  `(α, β, t)` avoid `badSet`, the verifier accepts it;
* **`red_staged`**: when they avoid `badSet`, the reduction inside the prover's tail returns claims
  (so the tail fails only at an opening's proof of work).

The honest WHIR opening's acceptance (`OpeningAccepts`) is the opening helper's
`openingAccepts_layouts` (`ProverOpening.lean`). What remains as hypotheses: the Statement's
constants (`Constants`), its claims being Compose's (`Bridge.ClaimsMatch stmtConsts`), the
membership circuit being F0b's (`CircuitMatch`), and the prover's NTT tables being Completeness's
(`TablesMatch`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open LeanVM.Protocol.Compile.Rom (implH implF)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

/-- **The honest WHIR opening of true stack claims is accepted** at the three layouts (the opening
helper's `openingAccepts_layouts`). -/
theorem openingAccepts : OpeningAccepts := fun H F fuel L hL ↦ openingAccepts_layouts H F fuel L hL

/-- The membership circuit has `2^22` rows. -/
theorem membership_logRows : (membership logRows).logRows = 22 := rfl

section Deployed

attribute [local irreducible] commitWithH

/-- The setup at functions is the root of the membership circuit's wiring table's commitment. -/
theorem setupWithH_id (H : Bytes → Digest) (F : KeccakState → KeccakState) :
    simulateQ (implHF H F) (setupWithH callKeccak256) =
      (commitWithH (m := Id) H (cellVars (membership logRows).logRows)
        (membership logRows).wiringTable).root := by
  rw [simulateQ_setupWithH, implH_implHF]
  rfl

end Deployed

variable (hK : Constants) (hcl : Bridge.ClaimsMatch stmtConsts) (hcirc : CircuitMatch)
  (hT : TablesMatch) (H : Bytes → Digest) (F : KeccakState → KeccakState) (stmt : Statement)
  (w : PcsQuotient.Secret) (hrel : Relation stmt w) (masks : Masks) (wp qp : Padding)
  (A : AuxA × Digest × (E × E))
  (hA : simulateQ (implHF H F)
    (stageAG (setupWithH callKeccak256) (membership logRows) (cellsOf w) masks wp stmt) = A)
  (s₁ s₂ s₃ : Digest) (hs₁ : H (chainIn A.2.1 A.2.2) = s₁) (hs₂ : H (digestBytes s₁) = s₂)
  (hs₃ : H (digestBytes s₂) = s₃)
  (B : (Tree × Array K) × (E × E))
  (hB : simulateQ (implHF H F) (stageBG (membership logRows) (cellsOf w) qp A.1 s₁ s₂ s₃) = B)
  (s₄ : Digest) (hs₄ : H (chainIn s₃ B.2) = s₄)
  (hgood : (challengeOf s₁, challengeOf s₂, challengeOf s₄) ∉ badSet w masks)

include hK hcl hcirc hT hrel hA hs₁ hs₂ hs₃ hB hs₄ hgood in
/-- **`RejectGood`'s acceptance part**, at the deployed staged run: at functions `H`, `F`, when the
prover's tail returns a proof and the staged run's challenges `(challengeOf s₁, challengeOf s₂,
challengeOf s₄)` avoid `badSet`, the verifier accepts it on the setup's root. -/
theorem acc_staged (π : PcsQuotient.Proof)
    (hπ : simulateQ (implHF H F)
      (proverTail (membership logRows) nonceFuel stmt A.1 B.1 (challengeOf s₄)) = some π) :
    verifyWithH (m := Id) H F logRows A.1.1 stmt π = true :=
  acc_stagedG hK hcl hT H F (membership logRows) membership_logRows (setupWithH callKeccak256)
    (setupWithH_id H F) stmt w hrel masks wp qp (cellsOf w) (cellsOf_size w) (hcirc.cells w)
    hcirc.sigmaSize hcirc.sigma A hA s₁ s₂ s₃ hs₁ hs₂ hs₃ B hB s₄ hs₄ hgood openingAccepts
    nonceFuel π hπ

include hK hcl hcirc hT hrel hA hs₁ hs₂ hs₃ hB hs₄ hgood in
/-- **`RejectGood`'s reduction part**, at the deployed staged run: when the staged run's challenges
avoid `badSet`, the reduction inside the prover's tail returns claims. -/
theorem red_staged :
    reduceWithH (m := Id) H logRows A.1.2.1.root stmt
      (tailProof (membership logRows) A.1 B.1 (challengeOf s₄)) ≠ none :=
  red_stagedG hK hcl hT H F (membership logRows) membership_logRows (setupWithH callKeccak256)
    (setupWithH_id H F) stmt w hrel masks wp qp (cellsOf w) (cellsOf_size w) (hcirc.cells w)
    hcirc.sigmaSize hcirc.sigma A hA s₁ s₂ s₃ hs₁ hs₂ hs₃ B hB s₄ hs₄ hgood

end E2ECompleteness

/-- info: 'E2ECompleteness.acc_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.acc_staged

/-- info: 'E2ECompleteness.red_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.red_staged
