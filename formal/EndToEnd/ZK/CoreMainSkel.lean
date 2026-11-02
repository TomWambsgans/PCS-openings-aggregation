-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The statement's trees (`buildTreeM`, `commitWith`, `stackWordFast`) and the openings' runs are
-- leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Run.lean`,
-- `Statement/Prover/Ntt.lean`).
import ZK.CoreMainProver
import ZK.CoreRender

/-!
# The skeleton's steps and openings against the oracle, at the statement's run

The deployed skeleton with its setup (`skelSetup`), run by the deployed prover (`Pb` with WHIR's
honest prover as renderer, `PbD`) against `G = Gof (kDet π) π gH gF`, step by step (assembled in
`CoreMainTop.lean`'s `skelDet_eq`):

* the wiring table's tree is the statement's index tree (`tree₀σ`: `tree₀_wiring`), the witness
  table's its witness tree (`tree₀W`: `tree₀_secret`, `pbRow_W`), the quotient table's, after
  `α, β, γ`, its quotient tree at those challenges (`tree₀Q`: `pbRow_Q`, off the degenerate `α, β`);
* the message after `t` is the five values (`msgD_four`), the statement prover's (`jvD_fst_eq`,
  `redMsgs_eq`); at an opening's start only the claims' bytes (`msgD_start`);
* **`openings_eq`**: after the chain's five answers (`chainOuts` of the statement's roots and values),
  each opening starts after `5`, `128`, `242` answers (`nc_opening`) with the claims' bytes
  (`claims_skel`), and is the statement's run of the honest script from its tree (`opening_eq`, with
  the renderer's messages: `MsgHW`, `msg_σ`, `MsgHQ`).

`MsgHW`, `MsgHQ` are `CoreRender.lean`'s `msgH_W`, `msgH_Q` as hypotheses (`msgHW_holds`,
`msgHQ_holds`).
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

theorem ifT {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ifF {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-- **The deployed prover**, its leaves byte strings. -/
noncomputable abbrev PbD (stmt : Statement) (w : Secret) :
    QuotientZk.Proto (RandD K) (List UInt8) Out Msg Tbl Pos :=
  Pb deployedRep P₀D (gKD w) vanD (stmtWD stmt) F192.Y (TWD w) (TQD w)
    (Render.whirRenderer deployedRep stmt)

theorem msgFn_PbD (stmt : Statement) (w : Secret) (s : RandD K) (h : List Out) :
    (QuotientZk.DRpm.ofBytes (PbD stmt w)).msgFn s h = msgD stmt w s h := rfl

theorem n_PbD (stmt : Statement) (w : Secret) : (QuotientZk.DRpm.ofBytes (PbD stmt w)).n = 394 := rfl

/-! ## The messages at the reduction's steps and the openings' starts -/

section Msgs

variable (stmt : Statement) (w : Secret) (s : RandD K)

/-- **After `t`** (four answers): the five values of the joint view. -/
theorem msgD_four (h : List Out) (hh : h.length = 4) :
    msgD stmt w s h = [.scalars (valsOf (jvD w (chOf deployedRep.limbs h) s).1)] := by
  rw [msgD_eq stmt w s h (by omega) (by omega) (by omega), hh]
  unfold Render.whirRenderer
  rw [ifT rfl]
  rfl

/-- **At an opening's start** (after `5`, `128` or `242` answers): the claims' bytes only. -/
theorem msgD_start (h : List Out) (cl : Claims)
    (hcl : Render.chainClaims stmt h (jvD w (chOf deployedRep.limbs h) s).1 = some cl)
    (hk : h.length = 5 ∨ h.length = 128 ∨ h.length = 242) :
    msgD stmt w s h = claimMsg deployedRep P₀D (stmtWD stmt) F192.Y h.length
      (chOf deployedRep.limbs h) (jvD w (chOf deployedRep.limbs h) s).1 := by
  have hva : (avail h.length (jvD w (chOf deployedRep.limbs h) s)).1 =
      (jvD w (chOf deployedRep.limbs h) s).1 := ifT (by omega) _ _
  unfold msgD PbMsg msgPub Render.whirRenderer
  rw [hva, ifF (show ¬ h.length = 4 by omega), hcl]
  simp only
  rw [ifF (by omega), ifF (by omega), ifF (by omega), List.append_nil]

/-- **The joint view's five values** are the statement prover's at the `t` of the fourth answer. -/
theorem jvD_fst_eq (h : List Out) (t : E) (ht : chainChal (h.getD 3 default) = t) :
    (jvD w (chOf deployedRep.limbs h) s).1 =
      ((E2ECompleteness.rowValuesAt logRows (wHatD w) (maskEntries (decodeCoins (eD s)).1) t).get,
        E2ECompleteness.nextAt logRows (membership logRows).wiringTable t) := by
  show redMsgs P₀D (gKD w) vanD (dH deployedRep.limbs (h.getD 3 default)) s.1 = _
  rw [dH_eq_chainChal, ht, redMsgs_eq, decodeCoins_eD_masks]

/-- The chain challenges `α, β, γ` of answers. -/
theorem chOf_abc (h : List Out) :
    (chOf deployedRep.limbs h).1.1.1 = (chainChal (h.getD 0 default), chainChal (h.getD 1 default),
      chainChal (h.getD 2 default)) := by
  show (dH deployedRep.limbs (h.getD 0 default), dH deployedRep.limbs (h.getD 1 default),
    dH deployedRep.limbs (h.getD 2 default)) = _
  rw [dH_eq_chainChal, dH_eq_chainChal, dH_eq_chainChal]

end Msgs

/-! ## The statement's trees -/

section Trees

variable (π : Equiv.Perm Eager.St) (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding)

theorem treeσ_eq : (runD π stmt w c).indexTree =
    (buildTreeM (permId π) 19 (stackWordFast 24 1 (membership logRows).wiringTable)).run := by
  rw [runD_indexTree]; rfl

theorem treeW_eq : (runD π stmt w c).witnessTree =
    (buildTreeM (permId π) 20 (stackWordFast 25 1 (wStackD w c))).run := by
  rw [runD_witnessTree]; rfl

theorem treeQ_eq : (runD π stmt w c).quotientTree =
    (buildTreeM (permId π) 23 (stackWordFast 28 1
      (qStackD w c ((runD π stmt w c).α, (runD π stmt w c).β, (runD π stmt w c).γ)))).run := by
  rw [runD_quotientTree]; rfl

theorem treeOK_build (d : ℕ) (word : Word) : TreeOK π (buildTreeM (permId π) d word).run := rfl

theorem rootOf_treeBytesOf (t : Tree) (ht : TreeOK π t) :
    QuotientZk.Deployed.rootOf (treeBytesOf t) = Digest.toBytes t.root := by
  have h1 := Merkle.tree_root π t.height t.word
  rw [← Merkle.tree_levels] at h1
  unfold Merkle.treeBytes at h1
  rw [← ht] at h1
  exact h1

end Trees

/-! ## The renderer's messages inside the secret openings -/

/-- **The renderer's messages inside the witness opening**, in the form `opening_eq` uses (the shape
of `CoreRender.lean`'s `msgH_W`): after the five chain answers `h₀` (claims `cl` at them, the
witness claim's point the joint model's) and `1 ≤ |chs| <` the opening's draws, the deployed
prover's message is the drive of the statement's honest script on its witness stack, commitment `0`
the statement's WHIR word. -/
def MsgHW (stmt : Statement) (w : Secret) : Prop :=
  ∀ (s : RandD K) (h₀ : List Out), h₀.length = 5 → ∀ cl : Claims,
    Render.chainClaims stmt h₀ (jvD w (chOf deployedRep.limbs h₀) s).1 = some cl →
    cl.witness.point = pointW (chOf deployedRep.limbs h₀) →
    ∀ chs : List Out, 1 ≤ chs.length →
      chs.length < drawsIn (Render.openingEv (QuotientZk.Deployed.witnessShape idWD)) →
      msgD stmt w s (h₀ ++ chs) =
        lastMsg (evRun (Render.openingEv (QuotientZk.Deployed.witnessShape idWD)) chs
          ⟨some (openingScript (witnessLayout logRows) (wStackD w (decodeCoins (eD s))) [cl.witness]),
            [((QuotientZk.Deployed.witnessShape idWD).depth₀,
              stackWordFast 25 1 (wStackD w (decodeCoins (eD s))))], [], [], []⟩)

/-- **The renderer's messages inside the quotient opening** (the shape of `msgH_Q`): after `242`
answers `h₀` whose `α, β` are not degenerate, the claims `cl` at the first five, their points the
joint model's. -/
def MsgHQ (stmt : Statement) (w : Secret) : Prop :=
  ∀ (s : RandD K) (h₀ : List Out), h₀.length = 242 →
    ¬ BadABD w s.1 ((chOf deployedRep.limbs h₀).1.1.1.1, (chOf deployedRep.limbs h₀).1.1.1.2.1) →
    ∀ cl : Claims, Render.chainClaims stmt h₀ (jvD w (chOf deployedRep.limbs h₀) s).1 = some cl →
    cl.quotient.point =
      pointQ P₀D F192.Y (chOf deployedRep.limbs h₀) (jvD w (chOf deployedRep.limbs h₀) s).1 →
    cl.sum.point = pointS F192.Y →
    ∀ chs : List Out, 1 ≤ chs.length →
      chs.length < drawsIn (Render.openingEv (QuotientZk.Deployed.quotientShape idQD)) →
      msgD stmt w s (h₀ ++ chs) =
        lastMsg (evRun (Render.openingEv (QuotientZk.Deployed.quotientShape idQD)) chs
          ⟨some (openingScript (quotientLayout logRows)
              (qStackD w (decodeCoins (eD s)) (chOf deployedRep.limbs h₀).1.1.1) [cl.quotient, cl.sum]),
            [((QuotientZk.Deployed.quotientShape idQD).depth₀,
              stackWordFast 28 1 (qStackD w (decodeCoins (eD s)) (chOf deployedRep.limbs h₀).1.1.1))],
            [], [], []⟩)

/-- `CoreRender.lean`'s `msgH_W` is `MsgHW`. -/
theorem msgHW_holds (stmt : Statement) (w : Secret) : MsgHW stmt w :=
  fun s h₀ hh cl hcl hpt chs h1 h2 ↦ msgH_W stmt w s h₀ hh cl hcl hpt chs h1 h2

/-- `CoreRender.lean`'s `msgH_Q` is `MsgHQ`, for a witness of the relation. -/
theorem msgHQ_holds (stmt : Statement) (w : Secret) (hw : Relation stmt w) : MsgHQ stmt w :=
  fun s h₀ hh hbad cl hcl hptQ hptS chs h1 h2 ↦
    msgH_Q stmt w hw s h₀ hh hbad cl hcl hptQ hptS chs h1 h2

/-! ## The skeleton -/

section Skel

variable (stmt : Statement) (w : Secret) (s : RandD K) (π : Equiv.Perm Eager.St)
  (gH : List UInt8 → KSt) (gF : KSt → DigestBytes)

local notation "P" => QuotientZk.DRpm.ofBytes (PbD stmt w)
local notation "G" => Gof (kDet π) π gH gF
local notation "cD" => decodeCoins (eD s)
local notation "R" => runD π stmt w (decodeCoins (eD s))

open Merkle (runDet_bind runDet_pure)

theorem runDet_chalH_lt (m : List UInt8) (hist : List Out) (h : hist.length < 394) :
    runDet P G s (QuotientZk.Deployed.chalH m) hist = ((G (.inl m)).1, hist ++ [G (.inl m)]) := by
  rw [runDet_chalH, ifT (by rw [n_PbD]; exact h)]

theorem runDet_bind_of {α β : Type} {X : OracleComp QuotientZk.Deployed.DSpec α}
    {f : α → OracleComp QuotientZk.Deployed.DSpec β} {hist : List Out} {a : α} {h' : List Out}
    (h : runDet P G s X hist = (a, h')) : runDet P G s (X >>= f) hist = runDet P G s (f a) h' := by
  rw [runDet_bind, h]

/-- The wiring table's tree is the statement's index tree. -/
theorem tree₀σ (hist : List Out) :
    runDet P G s (QuotientZk.Deployed.tree₀ (QuotientZk.Deployed.wiringShape idσD rowsWD)) hist =
      (treeBytesOf (R).indexTree, hist) := by
  rw [tree₀_wiring, treeσ_eq]
  rfl

/-- The witness table's tree is the statement's witness tree. -/
theorem tree₀W :
    runDet P G s (QuotientZk.Deployed.tree₀ (QuotientZk.Deployed.witnessShape idWD)) [] =
      (treeBytesOf (R).witnessTree, []) := by
  rw [tree₀_secret (PbD stmt w) π gH gF s (QuotientZk.Deployed.witnessShape idWD) 0 rfl
    (stackWordFast 25 1 (wStackD w cD)) [] (by show PbcK 0 ≤ 0; rw [PbcK_zero]) ?_, treeW_eq]
  · rfl
  · intro x hx
    have hx' : x < 2 ^ 20 := hx
    rw [show (PbD stmt w).rowFn = PbRow deployedRep P₀D F192.Y (TWD w) (TQD w) from rfl,
      pbRow_W w s _ _ (by show x % 2 ^ 23 < 2 ^ 20; omega)]
    show (stackWordFast 25 1 (wStackD w cD) (x % 2 ^ 23)).flatMap kBytes = _
    rw [Nat.mod_eq_of_lt (by omega)]

/-- The quotient table's tree, after answers whose `α, β, γ` are the statement's, off the degenerate
`α, β`, is the statement's quotient tree. -/
theorem tree₀Q (hw : Relation stmt w) (hbad : ¬ BadABD w s.1 ((R).α, (R).β)) (hist : List Out)
    (hl : hist.length = 3) (habc : (chOf deployedRep.limbs hist).1.1.1 = ((R).α, (R).β, (R).γ)) :
    runDet P G s (QuotientZk.Deployed.tree₀ (QuotientZk.Deployed.quotientShape idQD)) hist =
      (treeBytesOf (R).quotientTree, hist) := by
  rw [tree₀_secret (PbD stmt w) π gH gF s (QuotientZk.Deployed.quotientShape idQD) 1 rfl
    (stackWordFast 28 1 (qStackD w cD ((R).α, (R).β, (R).γ))) hist
      (by show PbcK 1 ≤ hist.length; rw [PbcK_one, hl]) ?_, treeQ_eq]
  · rfl
  · intro x hx
    have hx' : x < 2 ^ 23 := hx
    have htake : hist.take ((PbD stmt w).cK 1) = hist := by
      rw [show (PbD stmt w).cK 1 = 3 from PbcK_one, ← hl, List.take_length]
    have hbad' : ¬ BadABD w s.1 ((chOf deployedRep.limbs hist).1.1.1.1,
        (chOf deployedRep.limbs hist).1.1.1.2.1) := by
      rw [habc]; exact hbad
    rw [htake, show (PbD stmt w).rowFn = PbRow deployedRep P₀D F192.Y (TWD w) (TQD w) from rfl,
      pbRow_Q stmt w hw s hist _ hbad', habc]
    show (stackWordFast 28 1 (qStackD w cD ((R).α, (R).β, (R).γ)) (x % 2 ^ 23)).flatMap kBytes = _
    rw [Nat.mod_eq_of_lt hx']

theorem len_treeBytesOf (d : ℕ) (word : Word) :
    (treeBytesOf (buildTreeM (permId π) d word).run).length = d + 1 := by
  unfold treeBytesOf
  rw [List.length_map, Array.length_toList, Merkle.buildTree_run, List.size_toArray,
    Merkle.treeLevels_length]

set_option quotPrecheck false in
local notation "aD" => E2ECompleteness.rowValuesAt logRows (wHatD w)
  (maskEntries (decodeCoins (eD s)).1) (runD π stmt w (decodeCoins (eD s))).t
set_option quotPrecheck false in
local notation "nD" => E2ECompleteness.nextAt logRows (membership logRows).wiringTable
  (runD π stmt w (decodeCoins (eD s))).t
set_option quotPrecheck false in
local notation "h5" => chainOuts π gH gF (runD π stmt w (decodeCoins (eD s))).indexTree.root
  (runD π stmt w (decodeCoins (eD s))).witnessTree.root
  (runD π stmt w (decodeCoins (eD s))).quotientTree.root (stmtBytesD stmt) (valsOf ((aD).get, nD))

/-- The joint view's five values after the chain's answers and any later ones. -/
theorem jvD_h5 (rest : List Out) :
    (jvD w (chOf deployedRep.limbs (h5 ++ rest)) s).1 = ((aD).get, nD) := by
  rw [jv_fst_append w s _ rest (by rw [length_chainOuts])]
  exact jvD_fst_eq w s _ _ (runD_t π stmt w cD gH gF _).symm

/-- The chain challenges `α, β, γ` after the chain's answers and any later ones. -/
theorem chOf_h5 (rest : List Out) :
    (chOf deployedRep.limbs (h5 ++ rest)).1.1.1 = ((R).α, (R).β, (R).γ) := by
  rw [show (chOf deployedRep.limbs (h5 ++ rest)).1.1.1 = (chOf deployedRep.limbs h5).1.1.1 by
    rw [chOf_fst_append _ rest (by rw [length_chainOuts])], chOf_abc,
    runD_α π stmt w cD gH gF (R).quotientTree.root (valsOf ((aD).get, nD)),
    runD_β π stmt w cD gH gF (R).quotientTree.root (valsOf ((aD).get, nD)),
    runD_γ π stmt w cD gH gF (R).quotientTree.root (valsOf ((aD).get, nD))]

/-- **The three openings**, after the chain's answers: the statement's runs of the honest scripts
from its trees. -/
theorem openings_eq (hAW : MsgHW stmt w) (hAQ : MsgHQ stmt w)
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
      [(R).quotientTree] [] = some (strQ, opsQ, msQ))
    (h₀ : List Out) (hh : h₀ = h5) :
    (runDet P G s (do
      let oW ← QuotientZk.Deployed.opening (QuotientZk.Deployed.witnessShape idWD)
        (treeBytesOf (R).witnessTree)
      let oσ ← QuotientZk.Deployed.opening (QuotientZk.Deployed.wiringShape idσD rowsWD)
        (treeBytesOf (R).indexTree)
      let oQ ← QuotientZk.Deployed.opening (QuotientZk.Deployed.quotientShape idQD)
        (treeBytesOf (R).quotientTree)
      return (⟨Digest.toBytes (R).witnessTree.root, Digest.toBytes (R).quotientTree.root,
        valsOf ((aD).get, nD), [oW, oσ, oQ]⟩ : QuotientZk.Deployed.Proof)) h₀).1 =
      ⟨Digest.toBytes (R).witnessTree.root, Digest.toBytes (R).quotientTree.root,
        valsOf ((aD).get, nD),
        [(((digestScalars (R).witnessTree.root).1 :: (digestScalars (R).witnessTree.root).2 ::
            strW).map limbsOf, msW),
          (((digestScalars (R).indexTree.root).1 :: (digestScalars (R).indexTree.root).2 ::
            strσ).map limbsOf, msσ),
          (((digestScalars (R).quotientTree.root).1 :: (digestScalars (R).quotientTree.root).2 ::
            strQ).map limbsOf, msQ)]⟩ := by
  subst hh
  have hcs := fun rest ↦ claims_skel π gH gF _ _ _ stmt _ _ rest r hr
  have hcs0 := hcs []
  simp only [List.append_nil] at hcs0
  have hv0 : (jvD w (chOf deployedRep.limbs h5) s).1 = ((aD).get, nD) :=
    jvD_fst_eq w s _ _ (runD_t π stmt w cD gH gF _).symm
  have hcl0 : Render.chainClaims stmt h5 (jvD w (chOf deployedRep.limbs h5) s).1 = some r.claims := by
    rw [hv0]; exact hcs0.2.2.1
  have hcl : ∀ rest, Render.chainClaims stmt (h5 ++ rest)
      (jvD w (chOf deployedRep.limbs (h5 ++ rest)) s).1 = some r.claims := fun rest ↦ by
    rw [jvD_h5]; exact (hcs rest).2.2.1
  have hl5 : (h5).length = 5 := length_chainOuts _ _ _ _ _ _ _ _
  have hfuel : nonceFuel < 2 ^ 64 := by unfold nonceFuel; norm_num
  have hTσ : TreeOK π (R).indexTree := by rw [treeσ_eq]; exact treeOK_build π _ _
  have hTW : TreeOK π (R).witnessTree := by rw [treeW_eq]; exact treeOK_build π _ _
  have hTQ : TreeOK π (R).quotientTree := by rw [treeQ_eq]; exact treeOK_build π _ _
  have hwW : ((R).witnessTree.height, (R).witnessTree.word) =
      ((QuotientZk.Deployed.witnessShape idWD).depth₀, stackWordFast 25 1 (wStackD w cD)) := by
    rw [treeW_eq]; rfl
  have hwσ : ((R).indexTree.height, (R).indexTree.word) =
      ((QuotientZk.Deployed.wiringShape idσD rowsWD).depth₀,
        stackWordFast 24 1 (membership logRows).wiringTable) := by
    rw [treeσ_eq]; rfl
  have hwQ : ((R).quotientTree.height, (R).quotientTree.word) =
      ((QuotientZk.Deployed.quotientShape idQD).depth₀,
        stackWordFast 28 1 (qStackD w cD ((R).α, (R).β, (R).γ))) := by
    rw [treeQ_eq]; rfl
  have hdW : (R).witnessTree.height = (QuotientZk.Deployed.witnessShape idWD).depth₀ := by
    rw [treeW_eq]; rfl
  have hdσ : (R).indexTree.height = (QuotientZk.Deployed.wiringShape idσD rowsWD).depth₀ := by
    rw [treeσ_eq]; rfl
  have hdQ : (R).quotientTree.height = (QuotientZk.Deployed.quotientShape idQD).depth₀ := by
    rw [treeQ_eq]; rfl
  -- the witness opening
  obtain ⟨l₁, hl₁, hlen₁⟩ := nc_opening P G s (QuotientZk.Deployed.witnessShape idWD)
    (treeBytesOf (R).witnessTree) (by rw [treeW_eq, len_treeBytesOf]; rfl) (by decide) h5
    (by rw [hl5, draws_W, n_PbD]; norm_num)
  have eW := opening_eq π nonceFuel P gH gF s (QuotientZk.Deployed.witnessShape idWD)
    (witnessLayout logRows) [r.claims.witness] (R).witnessTree (claimBytes [r.claims.witness]) h5
    _ strW opsW msW hfuel hTW hdW
    (by rw [hdW]; exact heights_W idWD) (last_W idWD) (by decide)
    (by rw [hl5, draws_W, n_PbD]; norm_num)
    (by rw [msgFn_PbD, msgD_start stmt w s h5 r.claims hcl0 (Or.inl hl5), hl5, hv0]
        exact hcs0.2.2.2.2.2.1)
    (seed_witness π _)
    (fun chs h1 h2 ↦ by
      rw [msgFn_PbD, hAW s h5 hl5 r.claims hcl0 hcs0.2.2.2.1.symm chs h1 h2, hwW])
    hrW
  rw [runDet_bind_of stmt w s π gH gF (Prod.ext eW hl₁ : runDet P G s
    (QuotientZk.Deployed.opening (QuotientZk.Deployed.witnessShape idWD)
      (treeBytesOf (R).witnessTree)) h5 = (_, h5 ++ l₁))]
  try dsimp only
  -- the wiring opening
  have hl128 : (h5 ++ l₁).length = 128 := by rw [List.length_append, hl5, hlen₁, draws_W]
  obtain ⟨l₂, hl₂, hlen₂⟩ := nc_opening P G s (QuotientZk.Deployed.wiringShape idσD rowsWD)
    (treeBytesOf (R).indexTree) (by rw [treeσ_eq, len_treeBytesOf]; rfl) (by decide) (h5 ++ l₁)
    (by rw [hl128, draws_σ, n_PbD]; norm_num)
  have eσ := opening_eq π nonceFuel P gH gF s (QuotientZk.Deployed.wiringShape idσD rowsWD)
    (wiringLayout logRows) [r.claims.wiring] (R).indexTree (claimBytes [r.claims.wiring]) (h5 ++ l₁)
    _ strσ opsσ msσ hfuel hTσ hdσ
    (by rw [hdσ]; exact heights_σ idσD rowsWD) (last_σ idσD rowsWD) (by decide)
    (by rw [hl128, draws_σ, n_PbD]; norm_num)
    (by rw [msgFn_PbD, msgD_start stmt w s (h5 ++ l₁) r.claims (hcl l₁) (Or.inr (Or.inl hl128)),
          hl128, jvD_h5]
        exact (hcs l₁).2.2.2.2.2.2.1)
    (seed_wiring π rowsWD _)
    (fun chs h1 h2 ↦ by
      rw [msgFn_PbD, msg_σ stmt w s (h5 ++ l₁) hl128 r.claims (hcl l₁) chs h1 h2, hwσ])
    hrσ
  rw [runDet_bind_of stmt w s π gH gF (Prod.ext eσ hl₂ : runDet P G s
    (QuotientZk.Deployed.opening (QuotientZk.Deployed.wiringShape idσD rowsWD)
      (treeBytesOf (R).indexTree)) (h5 ++ l₁) = (_, h5 ++ l₁ ++ l₂))]
  try dsimp only
  -- the quotient opening
  have hl242 : (h5 ++ l₁ ++ l₂).length = 242 := by
    rw [List.length_append, hl128, hlen₂, draws_σ]
  have hass : h5 ++ l₁ ++ l₂ = h5 ++ (l₁ ++ l₂) := List.append_assoc _ _ _
  have habc : (chOf deployedRep.limbs (h5 ++ l₁ ++ l₂)).1.1.1 = ((R).α, (R).β, (R).γ) := by
    rw [hass, chOf_h5]
  have hclQ : Render.chainClaims stmt (h5 ++ l₁ ++ l₂)
      (jvD w (chOf deployedRep.limbs (h5 ++ l₁ ++ l₂)) s).1 = some r.claims := by
    rw [hass]; exact hcl _
  have hpts := (hcs (l₁ ++ l₂)).2.2.2.2.1
  rw [← hass] at hpts
  have hptQ : r.claims.quotient.point = pointQ P₀D F192.Y (chOf deployedRep.limbs (h5 ++ l₁ ++ l₂))
      (jvD w (chOf deployedRep.limbs (h5 ++ l₁ ++ l₂)) s).1 := by
    rw [hass, jvD_h5, ← hass]; exact (List.cons.inj hpts).1.symm
  have hptS : r.claims.sum.point = pointS F192.Y :=
    (List.cons.inj (List.cons.inj hpts).2).1.symm
  obtain ⟨l₃, hl₃, -⟩ := nc_opening P G s (QuotientZk.Deployed.quotientShape idQD)
    (treeBytesOf (R).quotientTree) (by rw [treeQ_eq, len_treeBytesOf]; rfl) (by decide)
    (h5 ++ l₁ ++ l₂) (by rw [hl242, draws_Q, n_PbD])
  have eQ := opening_eq π nonceFuel P gH gF s (QuotientZk.Deployed.quotientShape idQD)
    (quotientLayout logRows) [r.claims.quotient, r.claims.sum] (R).quotientTree
    (claimBytes [r.claims.quotient, r.claims.sum]) (h5 ++ l₁ ++ l₂)
    _ strQ opsQ msQ hfuel hTQ hdQ
    (by rw [hdQ]; exact heights_Q idQD) (last_Q idQD) (by decide)
    (by rw [hl242, draws_Q, n_PbD])
    (by rw [msgFn_PbD, msgD_start stmt w s (h5 ++ l₁ ++ l₂) r.claims hclQ (Or.inr (Or.inr hl242)),
          hl242, hass, jvD_h5]
        exact (hcs (l₁ ++ l₂)).2.2.2.2.2.2.2)
    (seed_quotient π _)
    (fun chs h1 h2 ↦ by
      rw [msgFn_PbD, hAQ s (h5 ++ l₁ ++ l₂) hl242 (by rw [habc]; exact hbad) r.claims
        hclQ hptQ hptS chs h1 h2, habc, hwQ])
    hrQ
  rw [runDet_bind_of stmt w s π gH gF (Prod.ext eQ hl₃ : runDet P G s
    (QuotientZk.Deployed.opening (QuotientZk.Deployed.quotientShape idQD)
      (treeBytesOf (R).quotientTree)) (h5 ++ l₁ ++ l₂) = (_, h5 ++ l₁ ++ l₂ ++ l₃))]
  try dsimp only
  rw [runDet_pure]

end Skel

end PcsQuotient.EndToEnd.Core
