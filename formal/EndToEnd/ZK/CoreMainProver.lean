-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The statement's prover (`proveWith`, `proveOpeningWith`, `commitWith`, the chain) runs leanerVM's
-- code (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Run.lean`,
-- `Statement/Keccak.lean`), as `formal/Statement` adapts it.
import ZK.CoreMainHist
import ZK.CoreRed
import E2ECompleteness.ProverRun
import E2ECompleteness.ProverStaged

/-!
# The statement's prover against a permutation, by its named parts

`proverDet π stmt w c` (`ProverBridgeReduce.lean`) is the statement's honest prover run in `Id`
against the permutation `π`. With E2ECompleteness's named form of the prover (`proveSpec`,
`runOf`, `finishSpec`, `WithHash.lean`, `ProverRun.lean`) at Keccak-256 over `π`:

* **`proverDet_some`**: when it makes the proof `x`, the reduction on its own reduction proof returned
  claims `r`, each opening's proof is `proveOpeningWith` over `π` on its tree, stack and claims, and
  `x`'s reduction proof is the run's;
* the run's parts in the deployed terms (`runD_*`): the index tree (the circuit's commitment), the
  witness stack `wStackD w c` and tree, the quotient stack `qStackD w c (α, β, γ)` and tree, and the
  challenges `α, β, γ, t` the decoded answers of the skeleton's chain (`chainOuts`, for any
  completions `gH`, `gF`), the four row values and `next` at `t`.

Nothing large is evaluated: the run's fields are projections of `runOf`, and the trees are named, not
built.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open PcsQuotient.Domain PcsQuotient.Transcript
open QuotientZk.Deployed (Out Inp Msg Item KSt)
open QuotientRpm (Limbs rootWords scalarWord)

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf chainChal)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

section Prover

variable (π : Equiv.Perm Eager.St) (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding)

/-- **The statement prover's run before its openings**, against `π` (E2ECompleteness's `runOf` at
Keccak-256 over `π`). -/
noncomputable def runD : E2ECompleteness.Run :=
  E2ECompleteness.runOf (keccak256With (permId π)) (membership logRows) stmt
    ((membership logRows).cells (membershipInputs w)) c.1 c.2.1 c.2.2

theorem membership_logRows' : (membership logRows).logRows = logRows := rfl

/-- **The prover against `π` is its run, then its end** (`proveSpec_id`). -/
theorem proverDet_eq :
    proverDet π stmt w c =
      E2ECompleteness.finishSpec (m := Id) (keccak256With (permId π)) (permId π) nonceFuel
        (membership logRows).logRows stmt (runD π stmt w c).indexTree (runD π stmt w c).witnessTree
        (runD π stmt w c).quotientTree (runD π stmt w c).sigmaHat (runD π stmt w c).wStack
        (runD π stmt w c).qStack (runD π stmt w c).proof := by
  unfold proverDet prover
  rw [E2ECompleteness.proverWith_eqH]
  unfold E2ECompleteness.proverWithH
  rw [E2ECompleteness.proveWithH_eq_spec]
  exact E2ECompleteness.proveSpec_id (keccak256With (permId π)) (permId π) nonceFuel
    (membership logRows) stmt _ c.1 c.2.1 c.2.2

/-- **The prover's proof, by its parts**: the reduction's claims on the run's proof, the three
openings' proofs, the run's reduction proof. -/
theorem proverDet_some {x : Proof} (h : proverDet π stmt w c = some x) :
    ∃ r : Reduced,
      (reduceWith (permId π) logRows (runD π stmt w c).indexTree.root stmt
        (runD π stmt w c).proof).run = some r ∧
      (proveOpeningWith (permId π) nonceFuel (witnessLayout logRows) (runD π stmt w c).witnessTree
        (runD π stmt w c).wStack [r.claims.witness]).run = some x.witness ∧
      (proveOpeningWith (permId π) nonceFuel (wiringLayout logRows) (runD π stmt w c).indexTree
        (runD π stmt w c).sigmaHat [r.claims.wiring]).run = some x.wiring ∧
      (proveOpeningWith (permId π) nonceFuel (quotientLayout logRows) (runD π stmt w c).quotientTree
        (runD π stmt w c).qStack [r.claims.quotient, r.claims.sum]).run = some x.quotient ∧
      x.reduction = (runD π stmt w c).proof := by
  rw [proverDet_eq] at h
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := E2ECompleteness.finishSpec_id_some
    (keccak256With (permId π)) (permId π) h
  refine ⟨r, h1, ?_, ?_, ?_, h5⟩
  · rw [E2ECompleteness.proveOpeningWith_eqH]; exact h2
  · rw [E2ECompleteness.proveOpeningWith_eqH]; exact h3
  · rw [E2ECompleteness.proveOpeningWith_eqH]; exact h4

/-! ## The run's parts -/

end Prover

section Parts

attribute [local irreducible] E2ECompleteness.commitWithH PcsQuotient.Layout.stackOf
  PcsQuotient.witnessStack PcsQuotient.quotientStack PcsQuotient.Domain.coefficients
  PcsQuotient.Domain.values E2ECompleteness.hValues E2ECompleteness.qValuesOf
  E2ECompleteness.qGateValuesOf commitWith

variable (π : Equiv.Perm Eager.St) (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding)

theorem runD_sigmaHat : (runD π stmt w c).sigmaHat = (membership logRows).wiringTable := rfl

/-- The index tree: the circuit's commitment over `π`. -/
theorem runD_indexTree : (runD π stmt w c).indexTree =
    (commitWith (permId π) (cellVars logRows) (membership logRows).wiringTable).run := by
  unfold runD
  rw [E2ECompleteness.runOf_indexTree, ← E2ECompleteness.commitWith_eqH, membership_logRows']
  rfl

/-- The witness stack. -/
theorem runD_wStack : (runD π stmt w c).wStack = wStackD w c := by
  unfold runD
  rw [E2ECompleteness.runOf_wStack, E2ECompleteness.runOf_wHat, E2ECompleteness.runOf_mask,
    membership_logRows']
  rfl

/-- The witness tree. -/
theorem runD_witnessTree : (runD π stmt w c).witnessTree =
    (commitWith (permId π) (cellVars logRows + 1) (wStackD w c)).run := by
  rw [show (runD π stmt w c).witnessTree = E2ECompleteness.commitWithH (m := Id)
    (keccak256With (permId π)) (cellVars (membership logRows).logRows + 1)
      (runD π stmt w c).wStack from rfl, ← E2ECompleteness.commitWith_eqH, runD_wStack,
      membership_logRows']
  rfl

/-- The quotient stack at the run's `α, β, γ`. -/
theorem runD_qStack : (runD π stmt w c).qStack =
    qStackD w c ((runD π stmt w c).α, (runD π stmt w c).β, (runD π stmt w c).γ) := by
  unfold runD
  rw [E2ECompleteness.runOf_qStack, E2ECompleteness.runOf_hHat, E2ECompleteness.runOf_qHat,
    E2ECompleteness.runOf_qGateHat, E2ECompleteness.runOf_wHat, E2ECompleteness.runOf_mask,
    E2ECompleteness.runOf_sigmaHat, qStackD, E2ECompleteness.quotientStackOf_eq]
  rfl

/-- The quotient tree. -/
theorem runD_quotientTree : (runD π stmt w c).quotientTree =
    (commitWith (permId π) (cellVars logRows + 4)
      (qStackD w c ((runD π stmt w c).α, (runD π stmt w c).β, (runD π stmt w c).γ))).run := by
  rw [show (runD π stmt w c).quotientTree = E2ECompleteness.commitWithH (m := Id)
    (keccak256With (permId π)) (cellVars (membership logRows).logRows + 4)
      (runD π stmt w c).qStack from rfl, ← E2ECompleteness.commitWith_eqH, runD_qStack,
      membership_logRows']
  rfl

/-- The reduction proof: the two roots' halves, the four row values and `next` at `t`. -/
theorem runD_proof : (runD π stmt w c).proof =
    ⟨digestScalars (runD π stmt w c).witnessTree.root,
      digestScalars (runD π stmt w c).quotientTree.root,
      E2ECompleteness.rowValuesAt logRows (wHatD w) (maskEntries c.1) (runD π stmt w c).t,
      E2ECompleteness.nextAt logRows (membership logRows).wiringTable (runD π stmt w c).t⟩ := rfl

/-! ## The run's challenges are the skeleton's chain's -/

theorem runD_chain :
    (E2ECompleteness.chainH (keccak256With (permId π)) (runD π stmt w c).indexTree.root stmt
        (runD π stmt w c).proof).1 = (runD π stmt w c).α ∧
      (E2ECompleteness.chainH (keccak256With (permId π)) (runD π stmt w c).indexTree.root stmt
        (runD π stmt w c).proof).2.1 = (runD π stmt w c).β ∧
      (E2ECompleteness.chainH (keccak256With (permId π)) (runD π stmt w c).indexTree.root stmt
        (runD π stmt w c).proof).2.2.1 = (runD π stmt w c).γ ∧
      (E2ECompleteness.chainH (keccak256With (permId π)) (runD π stmt w c).indexTree.root stmt
        (runD π stmt w c).proof).2.2.2.1 = (runD π stmt w c).t :=
  E2ECompleteness.runOf_chain _ _ _ _ _ _ _

variable (gH : List UInt8 → KSt) (gF : KSt → DigestBytes)

/-- **`α`**: the decoded first answer of the skeleton's chain on the run's roots. -/
theorem runD_α (rQ : Digest) (vals : List Limbs) :
    (runD π stmt w c).α = chainChal ((chainOuts π gH gF (runD π stmt w c).indexTree.root
      (runD π stmt w c).witnessTree.root rQ (stmtBytesD stmt) vals).getD 0 default) := by
  rw [← (runD_chain π stmt w c).1]
  show ((((Transcript.Chain.startWith (permId π)
      (label (runD π stmt w c).indexTree.root stmt)).run.absorb
        (digestScalars (runD π stmt w c).witnessTree.root).1).absorb
          (digestScalars (runD π stmt w c).witnessTree.root).2).squeezeWith (permId π)).run.1 = _
  rw [startWith_label, squeeze_root π gH gF]
  rfl

/-- **`β`**. -/
theorem runD_β (rQ : Digest) (vals : List Limbs) :
    (runD π stmt w c).β = chainChal ((chainOuts π gH gF (runD π stmt w c).indexTree.root
      (runD π stmt w c).witnessTree.root rQ (stmtBytesD stmt) vals).getD 1 default) := by
  rw [← (runD_chain π stmt w c).2.1]
  show (((((Transcript.Chain.startWith (permId π)
      (label (runD π stmt w c).indexTree.root stmt)).run.absorb
        (digestScalars (runD π stmt w c).witnessTree.root).1).absorb
          (digestScalars (runD π stmt w c).witnessTree.root).2).squeezeWith
            (permId π)).run.2.squeezeWith (permId π)).run.1 = _
  rw [startWith_label, squeeze_root π gH gF, squeeze_plain π gH gF]
  rfl

/-- **`γ`**. -/
theorem runD_γ (rQ : Digest) (vals : List Limbs) :
    (runD π stmt w c).γ = chainChal ((chainOuts π gH gF (runD π stmt w c).indexTree.root
      (runD π stmt w c).witnessTree.root rQ (stmtBytesD stmt) vals).getD 2 default) := by
  rw [← (runD_chain π stmt w c).2.2.1]
  show ((((((Transcript.Chain.startWith (permId π)
      (label (runD π stmt w c).indexTree.root stmt)).run.absorb
        (digestScalars (runD π stmt w c).witnessTree.root).1).absorb
          (digestScalars (runD π stmt w c).witnessTree.root).2).squeezeWith
            (permId π)).run.2.squeezeWith (permId π)).run.2.squeezeWith (permId π)).run.1 = _
  rw [startWith_label, squeeze_root π gH gF, squeeze_plain π gH gF, squeeze_plain π gH gF]
  rfl

/-- **`t`**: the decoded fourth answer, on the run's quotient root. -/
theorem runD_t (vals : List Limbs) :
    (runD π stmt w c).t = chainChal ((chainOuts π gH gF (runD π stmt w c).indexTree.root
      (runD π stmt w c).witnessTree.root (runD π stmt w c).quotientTree.root (stmtBytesD stmt)
        vals).getD 3 default) := by
  rw [← (runD_chain π stmt w c).2.2.2]
  show (((((((((Transcript.Chain.startWith (permId π)
      (label (runD π stmt w c).indexTree.root stmt)).run.absorb
        (digestScalars (runD π stmt w c).witnessTree.root).1).absorb
          (digestScalars (runD π stmt w c).witnessTree.root).2).squeezeWith
            (permId π)).run.2.squeezeWith (permId π)).run.2.squeezeWith (permId π)).run.2.absorb
              (digestScalars (runD π stmt w c).quotientTree.root).1).absorb
                (digestScalars (runD π stmt w c).quotientTree.root).2).squeezeWith (permId π)).run.1 = _
  rw [startWith_label, squeeze_root π gH gF, squeeze_plain π gH gF, squeeze_plain π gH gF,
    squeeze_root π gH gF]
  rfl

end Parts

end PcsQuotient.EndToEnd.Core
