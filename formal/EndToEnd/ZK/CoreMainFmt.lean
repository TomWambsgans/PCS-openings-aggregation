-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The verifier's program (`verifyStackedOpening`), the setup (`setupWith`) and the chain
-- (`reduceWith`) are leanerVM's and `formal/Statement`'s (branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0).
import ZK.CoreMainHist
import ZK.CoreBudget
import ZK.CoreRed
import ZK.CoreEnd

/-!
# `fmt` on the skeleton's proof, against a permutation

* **`fmtCore_eq`**: `fmtCore` against `π` on a proof whose roots are digests' bytes and whose values
  are the limbs of `v`, when the reduction over `π` on the roots' halves and `v` returns the claims
  `r` and each opening's production (`fillOpening`) returns a proof, is the statement's proof of the
  reduction proof and the three openings;
* **the deployed openings' events** (`follows_W`, `follows_σ`, `follows_Q`): the verifier's program
  at the deployed layouts follows them (`follows_verifyStackedOpening`); they open at most `6` times,
  at most `225` positions each (`openedIn_*`, `queriesOK_*`);
* **`multis_small`**: the statement's run of the honest script from a level-0 tree of `64`-word rows
  makes at most `8` multiproofs within `FmtSmall`'s bounds.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open QuotientRpm (Limbs)

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

variable (π : Equiv.Perm Eager.St)

/-! ## The formatting -/

theorem sim_setupWith : simulateQ (permOnly π) (setupWith permF) = setupWith (permId π) := by
  have h := Param.setupWith_hom (simHom (permOnly π)) permF
  simp only [simHom_app, Merkle.sim_permF] at h
  exact h

theorem sim_reduceWith (lr : ℕ) (ir : Digest) (stmt : Statement) (p : ReductionProof) :
    simulateQ (permOnly π) (reduceWith permF lr ir stmt p) = reduceWith (permId π) lr ir stmt p := by
  have h := Param.reduceWith_hom (simHom (permOnly π)) permF lr ir stmt p
  simp only [simHom_app, Merkle.sim_permF] at h
  exact h

/-- **`fmtCore` against `π`**, from the reduction's claims and the three productions. -/
theorem fmtCore_eq (stmt : Statement) (rW rQ : Digest) (a : Vector E 4) (next : E)
    (oW oσ oQ : List Limbs × List Multi) (r : Reduced) (xw xσ xq : Compile.Proof)
    (hr : (reduceWith (permId π) logRows (setupWith (permId π)).run stmt
      ⟨digestScalars rW, digestScalars rQ, a, next⟩).run = some r)
    (hw : (simulateQ (permOnly π)
      (fillOpening (witnessLayout logRows) r.witnessRoot [r.claims.witness] oW)).run = some xw)
    (hσ : (simulateQ (permOnly π)
      (fillOpening (wiringLayout logRows) (setupWith (permId π)).run [r.claims.wiring] oσ)).run =
        some xσ)
    (hq : (simulateQ (permOnly π) (fillOpening (quotientLayout logRows) r.quotientRoot
      [r.claims.quotient, r.claims.sum] oQ)).run = some xq) :
    (simulateQ (permOnly π)
        (fmtCore stmt ⟨Digest.toBytes rW, Digest.toBytes rQ, valsOf (a.get, next), [oW, oσ, oQ]⟩)).run =
      some ⟨⟨digestScalars rW, digestScalars rQ, a, next⟩, xw, xσ, xq⟩ := by
  unfold fmtCore
  simp only [reductionOf_valsOf, ofFn_get_vec, simulateQ_bind, sim_setupWith, sim_reduceWith,
    Id.run_bind]
  rw [hr]
  simp only [simulateQ_bind, simulateQ_pure, Id.run_bind]
  rw [hw, hσ, hq]
  rfl

/-- The setup over `π` is the root of the circuit's commitment. -/
theorem setupWith_run : (setupWith (permId π)).run =
    (commitWith (permId π) (cellVars logRows) (membership logRows).wiringTable).run.root := by
  show (commitWith (permId π) ((membership logRows).logRows + 2)
    (membership logRows).wiringTable).run.root = _
  rw [show (membership logRows).logRows = logRows from rfl]
  rfl

/-! ## The deployed openings' events -/

theorem follows_W (cls : List Claim) :
    Follows (Render.openingEv (QuotientZk.Deployed.witnessShape idWD))
      (verifyStackedOpening (witnessLayout logRows).logN logInvRate
        (stackClaims (witnessLayout logRows) cls)) [] := by
  rw [openingEv_W]
  exact follows_verifyStackedOpening 25 _ cfgW ladder_W cfgOK_W

theorem follows_σ (cls : List Claim) :
    Follows (Render.openingEv (QuotientZk.Deployed.wiringShape idσD rowsWD))
      (verifyStackedOpening (wiringLayout logRows).logN logInvRate
        (stackClaims (wiringLayout logRows) cls)) [] := by
  rw [openingEv_σ]
  exact follows_verifyStackedOpening 24 _ cfgW ladder_σ cfgOK_σ

theorem follows_Q (cls : List Claim) :
    Follows (Render.openingEv (QuotientZk.Deployed.quotientShape idQD))
      (verifyStackedOpening (quotientLayout logRows).logN logInvRate
        (stackClaims (quotientLayout logRows) cls)) [] := by
  rw [openingEv_Q]
  exact follows_verifyStackedOpening 28 _ cfgQ ladder_Q cfgOK_Q

theorem openedIn_W : openedIn (Render.openingEv (QuotientZk.Deployed.witnessShape idWD)) ≤ 8 := by
  rw [openingEv_W]; decide +kernel
theorem openedIn_σ : openedIn (Render.openingEv (QuotientZk.Deployed.wiringShape idσD rowsWD)) ≤ 8 := by
  rw [openingEv_σ]; decide +kernel
theorem openedIn_Q : openedIn (Render.openingEv (QuotientZk.Deployed.quotientShape idQD)) ≤ 8 := by
  rw [openingEv_Q]; decide +kernel

theorem queriesOK_W : queriesOK (Render.openingEv (QuotientZk.Deployed.witnessShape idWD)) = true := by
  rw [openingEv_W]; decide +kernel
theorem queriesOK_σ :
    queriesOK (Render.openingEv (QuotientZk.Deployed.wiringShape idσD rowsWD)) = true := by
  rw [openingEv_σ]; decide +kernel
theorem queriesOK_Q :
    queriesOK (Render.openingEv (QuotientZk.Deployed.quotientShape idQD)) = true := by
  rw [openingEv_Q]; decide +kernel

/-! ## The multiproofs -/

variable (fuel : ℕ)

/-- **An opening's multiproofs are small**: the honest script's run from a level-0 tree of WHIR
words (`64` words a row), on events with at most `8` openings of at most `2^10` positions. -/
theorem multis_small (evs : List Render.Ev) (L : PcsQuotient.Layout) (stack : Array K)
    (cls : List Claim) (sp : Sponge) (μ : ℕ) (t : Tree) (ht : ∀ p, t.word p = stackWordFast μ 1 stack p)
    (ho : openedIn evs ≤ 8) (hq : queriesOK evs = true) (str : List E) (ops : List Opening)
    (ms : List Multi)
    (hr : runEvS π fuel evs (some (openingScript L stack cls)) sp [t] [] = some (str, ops, ms)) :
    ms.length ≤ 8 ∧ ∀ mp ∈ ms, mp.1.length ≤ 2 ^ 10 ∧ ∀ r ∈ mp.2.1, r.length ≤ 2 ^ 10 := by
  obtain ⟨h1, h2⟩ := runEvS_small π fuel evs _ sp [t] [] str ops ms
    (Render.wordsLE_openingScript L stack cls)
    (fun t' ht' p ↦ by
      rw [List.mem_singleton.mp ht', ht, length_stackWordFast]; norm_num) hq hr
  exact ⟨h1.trans ho, h2⟩

end PcsQuotient.EndToEnd.Core
