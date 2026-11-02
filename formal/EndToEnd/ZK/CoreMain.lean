-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The statement's prover (`proveWith`, `proveOpeningWith`) and the verifier's program are leanerVM's
-- (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0), as `formal/Statement` adapts them.
import ZK.CoreMainTop
import ZK.CoreMainFmt

/-!
# The deployed core

**`coreD`**: `CoreD stmt w` (`ZK/CoreDefs.lean`) for every witness of the relation: for every coins
`s` of the skeleton model, permutation `π` and completions `gH`, `gF`, whenever the statement's
prover with `π` makes the proof `x` and its `α, β` are not degenerate, `fmt` with `π` turns the
skeleton's proof against `Gof (kDet π) π gH gF` (the deployed prover `Pb`, WHIR's honest prover as
renderer) into `x`. It is the last hypothesis of `zeroKnowledge_final` (`ZK/CoreEnd.lean`), discharged
in **`zeroKnowledge_closed`**.

The assembly (`coreD_of`), nothing large evaluated:

1. **the statement's side** (`CoreMainProver.lean`): `proverDet_some` (the reduction's claims `r` on
   the run's reduction proof, each opening `proveOpeningWith` on its tree, stack and claims), the
   run's parts (`runD_*`); each opening's proof is the statement's event-driven run of the honest
   script (`proveOpening_eq`, `follows_W`, `follows_σ`, `follows_Q`);
2. **the skeleton's side** (`CoreMainTop.lean`, `CoreMainSkel.lean`, `CoreMainHist.lean`):
   `skelDet_eq`, the skeleton's proof from the statement's trees, chain answers, values and runs (the
   reduction's part step by step, then `openings_eq`, the histories by `nc_opening`);
3. **`fmt`** (`CoreMainFmt.lean`): within its budget (`fmtDet_eq_core`, the multiproofs small:
   `multis_small`), `fmtCore` on that proof (`fmtCore_eq`), each opening produced by `fillOpening_eq`
   from the run's stream and multiproofs, is the statement's proof.

`coreD_of` takes the renderer's messages inside the two secret openings as hypotheses in the form
`opening_eq` uses them (`MsgHW`, `MsgHQ`: the deployed prover's message after `h₀ ++ chs` is the drive
of the statement's honest script from the statement's level-0 word); `CoreRender.lean` proves them
(`msgH_W`, `msgH_Q`), and the wiring opening's (`msg_σ`), so **`coreD`** has no hypothesis.
-/

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Out Inp Msg Item KSt Tbl Pos)
open Primitives
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open PcsQuotient.EndToEnd.Core
open Render (limbsOf chainChal)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-- **The deployed core from the renderer's messages inside the secret openings** (`MsgHW`,
`MsgHQ`, the shape `opening_eq` uses: the drive of the statement's honest script). -/
theorem coreD_of (stmt : Statement) (w : Secret) (hw : Relation stmt w) (hAW : MsgHW stmt w)
    (hAQ : MsgHQ stmt w) : CoreD stmt w := by
  intro s π gH gF x hx hab
  have hab' : ¬ BadABD w s.1 ((runD π stmt w (decodeCoins (eD s))).α,
      (runD π stmt w (decodeCoins (eD s))).β) := by
    rw [runD_α π stmt w _ gH gF default [], runD_β π stmt w _ gH gF default [], runD_indexTree,
      runD_witnessTree, ← abDet_eq π gH gF stmt w _ default [], ← decodeCoins_eD_masks s]
    exact hab
  -- the statement's side
  obtain ⟨r, hred, hoW, hoσ, hoQ, hxr⟩ := proverDet_some π stmt w (decodeCoins (eD s)) hx
  rw [runD_proof] at hred hxr
  rw [runD_wStack, proveOpening_eq π nonceFuel _ _ _ _ _ (follows_W _)] at hoW
  rw [runD_sigmaHat, proveOpening_eq π nonceFuel _ _ _ _ _ (follows_σ _)] at hoσ
  rw [runD_qStack, proveOpening_eq π nonceFuel _ _ _ _ _ (follows_Q _)] at hoQ
  obtain ⟨⟨strW, opsW, msW⟩, hrW, hxW⟩ := Option.map_eq_some_iff.mp hoW
  obtain ⟨⟨strσ, opsσ, msσ⟩, hrσ, hxσ⟩ := Option.map_eq_some_iff.mp hoσ
  obtain ⟨⟨strQ, opsQ, msQ⟩, hrQ, hxQ⟩ := Option.map_eq_some_iff.mp hoQ
  -- the skeleton's side
  rw [skelDet_eq stmt w s π gH gF hw hAW hAQ hab' r hred strW opsW msW hrW strσ opsσ msσ hrσ
    strQ opsQ msQ hrQ]
  -- `fmt`
  have hcs := claims_skel π gH gF _ _ _ stmt _ _ [] r hred
  rw [fmtDet_eq_core π stmt _ ?small]
  · rw [fmtCore_eq π stmt _ _ _ _ _ _ _ r x.witness x.wiring x.quotient ?hr ?hw ?hσ ?hq]
    · rw [← hxr]
    · rw [setupWith_run, ← runD_indexTree]
      exact hred
    · rw [hcs.1, ← hxW]
      exact fillOpening_eq π nonceFuel _ _ _ _ _ _ _ _ (follows_W _)
        (by rw [treeW_eq]; exact heights_W idWD) (by rw [treeW_eq]; exact treeOK_build π _ _)
        (by rw [treeW_eq]; rfl) hrW
    · rw [setupWith_run, ← runD_indexTree, ← hxσ]
      exact fillOpening_eq π nonceFuel _ _ _ _ _ _ _ _ (follows_σ _)
        (by rw [treeσ_eq]; exact heights_σ idσD rowsWD) (by rw [treeσ_eq]; exact treeOK_build π _ _)
        (by rw [treeσ_eq]; rfl) hrσ
    · rw [hcs.2.1, ← hxQ]
      exact fillOpening_eq π nonceFuel _ _ _ _ _ _ _ _ (follows_Q _)
        (by rw [treeQ_eq]; exact heights_Q idQD) (by rw [treeQ_eq]; exact treeOK_build π _ _)
        (by rw [treeQ_eq]; rfl) hrQ
  · intro o ho
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact multis_small π nonceFuel _ _ _ _ _ 25 _ (by rw [treeW_eq]; intro p; rfl) openedIn_W
        queriesOK_W _ _ _ hrW
    · exact multis_small π nonceFuel _ _ _ _ _ 24 _ (by rw [treeσ_eq]; intro p; rfl) openedIn_σ
        queriesOK_σ _ _ _ hrσ
    · exact multis_small π nonceFuel _ _ _ _ _ 28 _ (by rw [treeQ_eq]; intro p; rfl) openedIn_Q
        queriesOK_Q _ _ _ hrQ

/-- **The deployed core**: `CoreD stmt w` for every witness of the relation. -/
theorem coreD : ∀ stmt w, Relation stmt w → CoreD stmt w := fun stmt w hw ↦
  coreD_of stmt w hw (msgHW_holds stmt w) (msgHQ_holds stmt w hw)

/-- **Zero knowledge of the membership proof** (`zeroKnowledge_final` with its deterministic core
`coreD`): `ZeroKnowledgeWith` at `zkBoundEnd ((2^24 + 2^70)·12) fmtBudget (· ↦ deltaNone)`, the
simulator the joint model's with WHIR's honest prover as renderer. -/
theorem zeroKnowledge_closed (s₀ : RpmSimState) :
    ZeroKnowledgeWith s₀
      (zkSimulator (fun _ ↦ deployedPub deployedRep)
        (fun stmt ↦ deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y
          (Render.whirRenderer deployedRep stmt) inKD sigmaAtD)
        (fun stmt ↦ skelSetup (stmtBytesD stmt) idWD idσD idQD rowsWD) fmt)
      rpmSimOracle (zkBoundEnd ((2 ^ 24 + 2 ^ 70) * 12) fmtBudget fun _ ↦ E2ECompleteness.deltaNone) :=
  zeroKnowledge_final s₀ fun stmt w hw ↦ coreD stmt w hw

end PcsQuotient.EndToEnd

/-- info: 'PcsQuotient.EndToEnd.coreD_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.coreD_of

/-- info: 'PcsQuotient.EndToEnd.coreD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.coreD

/--
info: 'PcsQuotient.EndToEnd.zeroKnowledge_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_closed
