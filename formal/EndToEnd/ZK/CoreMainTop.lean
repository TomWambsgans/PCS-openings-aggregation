-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoreMainSkel

/-!
# The skeleton's proof against the oracle

**`skelDet_eq`**: the deployed skeleton with its setup, run by the deployed prover against
`Gof (kDet π) π gH gF`, outputs the statement's roots as bytes, its five values' limbs and, per
opening, the root's two scalars then the statement's run's stream as limbs, with the run's
multiproofs: the reduction's part step by step (`tree₀σ`, `tree₀W`, the seed and `α, β, γ`, `tree₀Q`,
`t`, the values `msgD_four`, `ρ`, the wiring tree again), then the three openings (`openings_eq`).
-/

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open PcsQuotient.Domain
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Out Inp Msg Item KSt Tbl Pos)
open QuotientRpm (Limbs rootWords scalarWord)
open Primitives

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf chainChal evRun lastMsg)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

section Skel

variable (stmt : Statement) (w : Secret) (s : RandD K) (π : Equiv.Perm Eager.St)
  (gH : List UInt8 → KSt) (gF : KSt → DigestBytes)

local notation "P" => QuotientZk.DRpm.ofBytes (PbD stmt w)
local notation "G" => Gof (kDet π) π gH gF
local notation "cD" => decodeCoins (eD s)
local notation "R" => runD π stmt w (decodeCoins (eD s))

set_option quotPrecheck false in
local notation "aD" => E2ECompleteness.rowValuesAt logRows (wHatD w)
  (maskEntries (decodeCoins (eD s)).1) (runD π stmt w (decodeCoins (eD s))).t
set_option quotPrecheck false in
local notation "nD" => E2ECompleteness.nextAt logRows (membership logRows).wiringTable
  (runD π stmt w (decodeCoins (eD s))).t

open Merkle (runDet_bind runDet_pure)
open QuotientZk.Deployed (tree₀ hashH chalH getMsg takeScalars kcTag rootOf witnessShape
  wiringShape quotientShape deployedShape skel)

/-! ## The skeleton, its definitions unfolded generically

Every unfolding below is a lemma proved for variables (`rfl` there), then rewritten: a definitional
unfolding on the concrete goal would let Lean reduce the run of the whole skeleton. -/

theorem skelDet_def {β : Type} (X : OracleComp QuotientZk.Deployed.DSpec β) :
    skelDet P G s X = (runDet P G s X []).1 := rfl

theorem skelSetup_def (sb : Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rows : List (List UInt8)) :
    skelSetup sb idW idσ idQ rows = (tree₀ (wiringShape idσ rows) >>= fun lv ↦
      skel (deployedShape ⟨rootOf lv, sb⟩ idW idσ idQ rows)) := rfl

theorem skel_deployed (ir : QuotientRpm.Bytes32) (sb : Vector UInt8 64)
    (idW idσ idQ : QuotientRpm.Bytes32) (rows : List (List UInt8)) :
    skel (deployedShape ⟨ir, sb⟩ idW idσ idQ rows) = (do
      let lvW ← tree₀ (witnessShape idW)
      let st₀ ← hashH (kcTag ++ ir.toList ++ sb.toList)
      let st₁ ← chalH (st₀.toList ++ rootWords (rootOf lvW))
      let st₂ ← chalH st₁.toList
      let st₃ ← chalH st₂.toList
      let lvQ ← tree₀ (quotientShape idQ)
      let st₄ ← chalH (st₃.toList ++ rootWords (rootOf lvQ))
      let m ← getMsg
      let (vals, _) := takeScalars m 5
      let _ ← chalH (st₄.toList ++ vals.flatMap scalarWord)
      let lvσ ← tree₀ (wiringShape idσ rows)
      let oW ← QuotientZk.Deployed.opening (witnessShape idW) lvW
      let oσ ← QuotientZk.Deployed.opening (wiringShape idσ rows) lvσ
      let oQ ← QuotientZk.Deployed.opening (quotientShape idQ) lvQ
      return (⟨rootOf lvW, rootOf lvQ, vals, [oW, oσ, oQ]⟩ : QuotientZk.Deployed.Proof)) := rfl

/-! ## The steps against the oracle -/

theorem hashH_bind {β : Type} (m : List UInt8) (f : QuotientRpm.Bytes32 → OracleComp QuotientZk.Deployed.DSpec β)
    (hist : List Out) :
    runDet P G s (hashH m >>= f) hist = runDet P G s (f (kDet π m)) hist := by
  rw [runDet_bind, Merkle.runDet_hashH, G_fst]

theorem chalH_bind {β : Type} (m : List UInt8) (f : QuotientRpm.Bytes32 → OracleComp QuotientZk.Deployed.DSpec β)
    (hist : List Out) (h : hist.length < 394) :
    runDet P G s (chalH m >>= f) hist = runDet P G s (f (G (.inl m)).1) (hist ++ [G (.inl m)]) := by
  rw [runDet_bind, runDet_chalH_lt stmt w s π gH gF m hist h]

theorem getMsg_bind {β : Type} (f : Msg → OracleComp QuotientZk.Deployed.DSpec β) (hist : List Out) :
    runDet P G s (getMsg >>= f) hist = runDet P G s (f (msgD stmt w s hist)) hist := by
  rw [runDet_bind, runDet_getMsg]
  rfl

theorem tree₀σ_bind {β : Type} (f : List (List QuotientRpm.Bytes32) → OracleComp QuotientZk.Deployed.DSpec β)
    (hist : List Out) :
    runDet P G s (tree₀ (wiringShape idσD rowsWD) >>= f) hist =
      runDet P G s (f (treeBytesOf (R).indexTree)) hist :=
  runDet_bind_of stmt w s π gH gF (tree₀σ stmt w s π gH gF hist)

theorem tree₀W_bind {β : Type} (f : List (List QuotientRpm.Bytes32) → OracleComp QuotientZk.Deployed.DSpec β) :
    runDet P G s (tree₀ (witnessShape idWD) >>= f) [] =
      runDet P G s (f (treeBytesOf (R).witnessTree)) [] :=
  runDet_bind_of stmt w s π gH gF (tree₀W stmt w s π gH gF)

theorem tree₀Q_bind {β : Type} (hw : Relation stmt w) (hbad : ¬ BadABD w s.1 ((R).α, (R).β))
    (f : List (List QuotientRpm.Bytes32) → OracleComp QuotientZk.Deployed.DSpec β) (hist : List Out)
    (hl : hist.length = 3) (habc : (chOf deployedRep.limbs hist).1.1.1 = ((R).α, (R).β, (R).γ)) :
    runDet P G s (tree₀ (quotientShape idQD) >>= f) hist =
      runDet P G s (f (treeBytesOf (R).quotientTree)) hist :=
  runDet_bind_of stmt w s π gH gF (tree₀Q stmt w s π gH gF hw hbad hist hl habc)

/-- **The skeleton's proof against the oracle** is the statement's roots as bytes, its five values'
limbs, and per opening the root's two scalars and the statement's run's stream as limbs, with the
run's multiproofs. -/
theorem skelDet_eq (hw : Relation stmt w) (hAW : MsgHW stmt w) (hAQ : MsgHQ stmt w)
    (hbad : ¬ BadABD w s.1 ((R).α, (R).β)) (r : Reduced)
    (hr : (reduceWith (permId π) logRows (R).indexTree.root stmt
      ⟨digestScalars (R).witnessTree.root, digestScalars (R).quotientTree.root, aD, nD⟩).run = some r)
    (strW : List E) (opsW : List Opening) (msW : List Multi)
    (hrW : runEvS π nonceFuel (Render.openingEv (QuotientZk.Deployed.witnessShape idWD))
      (some (openingScript (witnessLayout logRows) (wStackD w cD) [r.claims.witness]))
      (startSponge π (witnessLayout logRows) [r.claims.witness] (R).witnessTree.root)
      [(R).witnessTree] [] = some (strW, opsW, msW))
    (strσ : List E) (opsσ : List Opening) (msσ : List Multi)
    (hrσ : runEvS π nonceFuel (Render.openingEv (QuotientZk.Deployed.wiringShape idσD rowsWD))
      (some (openingScript (wiringLayout logRows) (membership logRows).wiringTable [r.claims.wiring]))
      (startSponge π (wiringLayout logRows) [r.claims.wiring] (R).indexTree.root)
      [(R).indexTree] [] = some (strσ, opsσ, msσ))
    (strQ : List E) (opsQ : List Opening) (msQ : List Multi)
    (hrQ : runEvS π nonceFuel (Render.openingEv (QuotientZk.Deployed.quotientShape idQD))
      (some (openingScript (quotientLayout logRows) (qStackD w cD ((R).α, (R).β, (R).γ))
        [r.claims.quotient, r.claims.sum]))
      (startSponge π (quotientLayout logRows) [r.claims.quotient, r.claims.sum] (R).quotientTree.root)
      [(R).quotientTree] [] = some (strQ, opsQ, msQ)) :
    skelDet P G s (skelSetup (stmtBytesD stmt) idWD idσD idQD rowsWD) =
      ⟨Digest.toBytes (R).witnessTree.root, Digest.toBytes (R).quotientTree.root,
        valsOf ((aD).get, nD),
        [(((digestScalars (R).witnessTree.root).1 :: (digestScalars (R).witnessTree.root).2 ::
            strW).map limbsOf, msW),
          (((digestScalars (R).indexTree.root).1 :: (digestScalars (R).indexTree.root).2 ::
            strσ).map limbsOf, msσ),
          (((digestScalars (R).quotientTree.root).1 :: (digestScalars (R).quotientTree.root).2 ::
            strQ).map limbsOf, msQ)]⟩ := by
  have hTσ : TreeOK π (R).indexTree := by rw [treeσ_eq]; exact treeOK_build π _ _
  have hTW : TreeOK π (R).witnessTree := by rw [treeW_eq]; exact treeOK_build π _ _
  have hTQ : TreeOK π (R).quotientTree := by rw [treeQ_eq]; exact treeOK_build π _ _
  rw [skelDet_def, skelSetup_def, tree₀σ_bind, rootOf_treeBytesOf π _ hTσ, skel_deployed]
  -- the witness tree, the seed, `α, β, γ`
  rw [tree₀W_bind, rootOf_treeBytesOf π _ hTW, hashH_bind]
  rw [chalH_bind stmt w s π gH gF]
  on_goal 2 => simp
  rw [List.nil_append, chalH_bind stmt w s π gH gF]
  on_goal 2 => simp
  rw [List.singleton_append, chalH_bind stmt w s π gH gF]
  on_goal 2 => simp
  simp only [List.cons_append, List.nil_append]
  -- the quotient tree, `t`
  rw [tree₀Q_bind stmt w s π gH gF hw hbad]
  on_goal 3 =>
    rw [chOf_abc, runD_α π stmt w cD gH gF (R).quotientTree.root (valsOf ((aD).get, nD)),
      runD_β π stmt w cD gH gF (R).quotientTree.root (valsOf ((aD).get, nD)),
      runD_γ π stmt w cD gH gF (R).quotientTree.root (valsOf ((aD).get, nD))]
    simp only [chainOuts, List.getD_cons_zero, List.getD_cons_succ]
  on_goal 2 => simp
  rw [rootOf_treeBytesOf π _ hTQ, chalH_bind stmt w s π gH gF]
  on_goal 2 => simp
  simp only [List.cons_append, List.nil_append]
  -- the five values, `ρ`
  rw [getMsg_bind, msgD_four stmt w s]
  on_goal 2 => simp
  rw [jvD_fst_eq w s _ (R).t]
  on_goal 2 =>
    rw [runD_t π stmt w cD gH gF (valsOf ((aD).get, nD))]
    simp only [chainOuts, List.getD_cons_zero, List.getD_cons_succ]
  rw [takeScalars_valsOf]
  dsimp only
  rw [chalH_bind stmt w s π gH gF]
  on_goal 2 => simp
  simp only [List.cons_append, List.nil_append]
  -- the wiring tree again, the openings
  rw [tree₀σ_bind]
  exact openings_eq stmt w s π gH gF hAW hAQ hbad r hr strW opsW msW hrW strσ opsσ msσ hrσ strQ
    opsQ msQ hrQ _ (by simp only [chainOuts])

end Skel

end PcsQuotient.EndToEnd.Core
