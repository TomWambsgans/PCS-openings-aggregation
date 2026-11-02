-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR prover (`openingScript`: mumbai's `openingFast` with this protocol's weight table,
-- `stackTableA`, `stackWordFast`) is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/Prover/Whir.lean`, `Statement/Prover/Ntt.lean`).
import ZK.CoreRenderPos

/-!
# The renderer's messages during an opening

The deployed prover (`Pb` with WHIR's honest prover as renderer, `whirRenderer`) sends, strictly
inside an opening, no claims' bytes and the renderer's drive of the opening's events (`evRun`) on the
available part of the joint view. Here, for the three openings (witness after `5` answers, wiring
after `128`, quotient after `242`), with `chs` the opening's answers so far (`1 ≤ |chs| < ` its
draws) and `cl` the verifier's claims at the first five answers:

* **A** (`msg_W`, `msg_σ`, `msg_Q`): the message is the drive of the hybrid script with the **full**
  view (the lane rounds and `f¹` of the joint view at any answers extending `h₀ ++ chs`) and with
  commitment `0` the statement's WHIR word: the drive never reads a lane round, the folded table or
  an opened row before it is available (`agree_hybrid`, `evRun_congr`), and the rows it reads at
  commitment `0` are at the queried positions, where the view's rows are the word's (`word0W_eq`);
* **A, honest** (`msgH_W`, `msgH_Q`): the message is the drive of **the statement's honest script**
  (`openingScript` on the statement's stack), a drive independent of `chs`, as `drive`'s and
  `opening_eq`'s hypothesis `hmsg` asks: along the draws' challenges the hybrid script with the view
  at `h₀ ++ chs` agrees with the honest one (`agree_hybrid_honest`, `viewW`, `viewQ`), the claims'
  points the joint model's (`hpt`);
* **B** (`runEvS_W`, `runEvS_Q`): the statement's run of the hybrid script with the view at challenges
  `c` is its run of the honest script, when `c`'s `λ` and lane challenges are the first seven the run
  squeezes (`runEvS_congr`).
-/

open Polynomial QuotientSecurity QuotientSecurity.Hiding
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient.Domain
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Out Msg)
open Primitives

namespace PcsQuotient.EndToEnd.Core

open Render (evRun lastMsg hybridScript)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-- The deployed prover's message. -/
noncomputable abbrev msgD (stmt : Statement) (w : Secret) (s : RandD K) (h : List Out) : Msg :=
  PbMsg deployedRep P₀D (gKD w) vanD (stmtWD stmt) F192.Y (TWD w) (TQD w)
    (Render.whirRenderer deployedRep stmt) s h

/-- No claims' bytes strictly inside an opening. -/
theorem claimMsg_inside (stmt : Statement) (k : ℕ) (c : DChal E) (v : Vals E) (h5 : k ≠ 5)
    (h128 : k ≠ 128) (h242 : k ≠ 242) : claimMsg deployedRep P₀D (stmtWD stmt) F192.Y k c v = [] := by
  unfold claimMsg
  rw [ite_eq_right h5, ite_eq_right h128, ite_eq_right h242]

/-- The deployed prover's message after `h`: the renderer's on the available view. -/
theorem msgD_eq (stmt : Statement) (w : Secret) (s : RandD K) (h : List Out) (h5 : h.length ≠ 5)
    (h128 : h.length ≠ 128) (h242 : h.length ≠ 242) :
    msgD stmt w s h = Render.whirRenderer deployedRep stmt h.length h
      (avail h.length (jvD w (chOf deployedRep.limbs h) s)) := by
  unfold msgD PbMsg msgPub
  rw [claimMsg_inside stmt _ _ _ h5 h128 h242, List.nil_append]

theorem depth₀_W (id : QuotientRpm.Bytes32) : (QuotientZk.Deployed.witnessShape id).depth₀ = 20 := rfl
theorem depth₀_σ (id : QuotientRpm.Bytes32) (rows : List (List UInt8)) :
    (QuotientZk.Deployed.wiringShape id rows).depth₀ = 19 := rfl
theorem depth₀_Q (id : QuotientRpm.Bytes32) : (QuotientZk.Deployed.quotientShape id).depth₀ = 23 := rfl

/-! ## A: the witness opening -/

/-- **A, witness**: strictly inside the witness opening, the deployed prover's message is the drive of
the hybrid script with the full view (at any answers `h₀ ++ chs ++ rest`) and commitment `0` the
statement's WHIR word of its witness stack. -/
theorem msg_W (stmt : Statement) (w : Secret) (s : RandD K) (h₀ : List Out) (hh₀ : h₀.length = 5)
    (cl : Claims) (hcl : Render.chainClaims stmt h₀ (jvD w (chOf deployedRep.limbs h₀) s).1 = some cl)
    (chs rest : List Out) (hc1 : 1 ≤ chs.length)
    (hc2 : chs.length < drawsIn (Render.openingEv (QuotientZk.Deployed.witnessShape idWD))) :
    msgD stmt w s (h₀ ++ chs) =
      lastMsg (evRun (Render.openingEv (QuotientZk.Deployed.witnessShape idWD)) chs
        ⟨some (hybridScript (witnessLayout logRows) [cl.witness]
            (Render.laneAt (jvD w (chOf deployedRep.limbs (h₀ ++ chs ++ rest)) s).2.2.1.1)
            (Array.ofFn (jvD w (chOf deployedRep.limbs (h₀ ++ chs ++ rest)) s).2.2.1.2.1)),
          [((QuotientZk.Deployed.witnessShape idWD).depth₀,
            stackWordFast 25 1 (wStackD w (decodeCoins (eD s))))], [], [], []⟩) := by
  rw [draws_W] at hc2
  have hk : (h₀ ++ chs).length = 5 + chs.length := by rw [List.length_append, hh₀]
  have hva : avail (h₀ ++ chs).length (jvD w (chOf deployedRep.limbs (h₀ ++ chs)) s) =
      avail (h₀ ++ chs).length (jvD w (chOf deployedRep.limbs (h₀ ++ chs ++ rest)) s) := by
    have e := avail_jv_take deployedRep P₀D (gKD w) vanD F192.Y (TWD w) (TQD w) (h₀ ++ chs ++ rest)
      s (h₀ ++ chs).length
    rwa [List.take_left' rfl] at e
  have hcl' : Render.chainClaims stmt (h₀ ++ chs)
      (avail (h₀ ++ chs).length (jvD w (chOf deployedRep.limbs (h₀ ++ chs)) s)).1 = some cl := by
    rw [avail_fst w s h₀ chs (by omega), chainClaims_append stmt h₀ chs (by omega)]
    exact hcl
  rw [msgD_eq stmt w s _ (by omega) (by omega) (by omega)]
  unfold Render.whirRenderer
  rw [ite_eq_right (by omega), hcl']
  simp only
  rw [ite_eq_left ⟨by omega, by omega⟩, List.drop_left' hh₀]
  unfold Render.openingMsg
  rw [show Render.openingEv (QuotientZk.Deployed.witnessShape default) =
    Render.openingEv (QuotientZk.Deployed.witnessShape idWD) by rw [openingEv_W, openingEv_W]]
  refine congrArg lastMsg ?_
  refine evRun_congr (fun p ↦ 52 ≤ chs.length ∧
      p ∈ posOf (((chs.drop 26).take 25).map drawLimbs) 20 224) _ chs _ _ ?_ ?_ rfl rfl rfl
    (posOK_W idWD _ chs fun h52 p hp ↦ ⟨h52, hp⟩)
  · show Agree (chs.map Render.drawChal) _ _
    refine agree_hybrid _ _ _ _ _ _ ladder_W' rfl _ (fun j hj ↦ ?_) (fun h7 ↦ ?_)
    · rw [hva]
      simp only [List.length_map] at hj
      exact laneAt_availL0 5 56 _ _ j (by omega)
    · rw [hva]
      simp only [List.length_map] at h7
      exact congrArg Array.ofFn (f1_availL0 5 56 _ _ (by omega))
  · refine ⟨_, _, [], rfl, rfl, (depth₀_W default).trans (depth₀_W idWD).symm, fun p hp ↦ ?_⟩
    obtain ⟨h52, hp⟩ := hp
    show Render.word0W deployedRep (h₀ ++ chs) _
      (p % 2 ^ (QuotientZk.Deployed.witnessShape default).depth₀) = _
    rw [depth₀_W]
    rw [posOf_eq_queried _ _ _ (by norm_num), ← drawsW_append h₀ chs hh₀ (by omega)] at hp
    exact word0W_eq w s (h₀ ++ chs) (by omega) p hp

/-! ## A: the wiring opening -/

/-- **A, wiring**: strictly inside the wiring opening, the deployed prover's message is the drive of
the honest script on the circuit's wiring table, commitment `0` its WHIR word. -/
theorem msg_σ (stmt : Statement) (w : Secret) (s : RandD K) (h₀ : List Out) (hh₀ : h₀.length = 128)
    (cl : Claims) (hcl : Render.chainClaims stmt h₀ (jvD w (chOf deployedRep.limbs h₀) s).1 = some cl)
    (chs : List Out) (hc1 : 1 ≤ chs.length)
    (hc2 : chs.length < drawsIn (Render.openingEv (QuotientZk.Deployed.wiringShape idσD rowsWD))) :
    msgD stmt w s (h₀ ++ chs) =
      lastMsg (evRun (Render.openingEv (QuotientZk.Deployed.wiringShape idσD rowsWD)) chs
        ⟨some (openingScript (wiringLayout logRows) (membership logRows).wiringTable [cl.wiring]),
          [((QuotientZk.Deployed.wiringShape idσD rowsWD).depth₀,
            stackWordFast 24 1 (membership logRows).wiringTable)], [], [], []⟩) := by
  rw [draws_σ] at hc2
  have hk : (h₀ ++ chs).length = 128 + chs.length := by rw [List.length_append, hh₀]
  have hcl' : Render.chainClaims stmt (h₀ ++ chs)
      (avail (h₀ ++ chs).length (jvD w (chOf deployedRep.limbs (h₀ ++ chs)) s)).1 = some cl := by
    rw [avail_fst w s h₀ chs (by omega), chainClaims_append stmt h₀ chs (by omega)]
    exact hcl
  rw [msgD_eq stmt w s _ (by omega) (by omega) (by omega)]
  unfold Render.whirRenderer
  rw [ite_eq_right (by omega), hcl']
  simp only
  rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, List.drop_left' hh₀]
  unfold Render.openingMsg
  rw [show Render.openingEv (QuotientZk.Deployed.wiringShape default []) =
    Render.openingEv (QuotientZk.Deployed.wiringShape idσD rowsWD) by rw [openingEv_σ, openingEv_σ],
    depth₀_σ, depth₀_σ]
  have e : Render.word0σ = stackWordFast 24 1 (membership logRows).wiringTable := rfl
  rw [e]

/-! ## A: the quotient opening -/

/-- **A, quotient**: strictly inside the quotient opening, the deployed prover's message is the drive
of the hybrid script with the full view and commitment `0` the statement's WHIR word of its quotient
stack at the answers' `α, β, γ` (off the degenerate `α, β`, for a witness of the relation). -/
theorem msg_Q (stmt : Statement) (w : Secret) (hw : Relation stmt w) (s : RandD K) (h₀ : List Out)
    (hh₀ : h₀.length = 242) (hbad : ¬ BadABD w s.1
      ((chOf deployedRep.limbs h₀).1.1.1.1, (chOf deployedRep.limbs h₀).1.1.1.2.1))
    (cl : Claims) (hcl : Render.chainClaims stmt h₀ (jvD w (chOf deployedRep.limbs h₀) s).1 = some cl)
    (chs rest : List Out) (hc1 : 1 ≤ chs.length)
    (hc2 : chs.length < drawsIn (Render.openingEv (QuotientZk.Deployed.quotientShape idQD))) :
    msgD stmt w s (h₀ ++ chs) =
      lastMsg (evRun (Render.openingEv (QuotientZk.Deployed.quotientShape idQD)) chs
        ⟨some (hybridScript (quotientLayout logRows) [cl.quotient, cl.sum]
            (Render.laneAt (jvD w (chOf deployedRep.limbs (h₀ ++ chs ++ rest)) s).2.2.2.1)
            (Array.ofFn (jvD w (chOf deployedRep.limbs (h₀ ++ chs ++ rest)) s).2.2.2.2.1)),
          [((QuotientZk.Deployed.quotientShape idQD).depth₀,
            stackWordFast 28 1 (qStackD w (decodeCoins (eD s)) (chOf deployedRep.limbs h₀).1.1.1))],
          [], [], []⟩) := by
  rw [draws_Q] at hc2
  have hk : (h₀ ++ chs).length = 242 + chs.length := by rw [List.length_append, hh₀]
  have hva : avail (h₀ ++ chs).length (jvD w (chOf deployedRep.limbs (h₀ ++ chs)) s) =
      avail (h₀ ++ chs).length (jvD w (chOf deployedRep.limbs (h₀ ++ chs ++ rest)) s) := by
    have e := avail_jv_take deployedRep P₀D (gKD w) vanD F192.Y (TWD w) (TQD w) (h₀ ++ chs ++ rest)
      s (h₀ ++ chs).length
    rwa [List.take_left' rfl] at e
  have hcl' : Render.chainClaims stmt (h₀ ++ chs)
      (avail (h₀ ++ chs).length (jvD w (chOf deployedRep.limbs (h₀ ++ chs)) s)).1 = some cl := by
    rw [avail_fst w s h₀ chs (by omega), chainClaims_append stmt h₀ chs (by omega)]
    exact hcl
  have habc : (chOf deployedRep.limbs (h₀ ++ chs)).1.1.1 = (chOf deployedRep.limbs h₀).1.1.1 := by
    rw [chOf_fst_append h₀ chs (by omega)]
  rw [msgD_eq stmt w s _ (by omega) (by omega) (by omega)]
  unfold Render.whirRenderer
  rw [ite_eq_right (by omega), hcl']
  simp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, List.drop_left' hh₀]
  unfold Render.openingMsg
  rw [show Render.openingEv (QuotientZk.Deployed.quotientShape default) =
    Render.openingEv (QuotientZk.Deployed.quotientShape idQD) by rw [openingEv_Q, openingEv_Q]]
  refine congrArg lastMsg ?_
  refine evRun_congr (fun p ↦ 59 ≤ chs.length ∧
      p ∈ posOf (((chs.drop 29).take 29).map drawLimbs) 23 225) _ chs _ _ ?_ ?_ rfl rfl rfl
    (posOK_Q idQD _ chs fun h59 p hp ↦ ⟨h59, hp⟩)
  · show Agree (chs.map Render.drawChal) _ _
    refine agree_hybrid _ _ _ _ _ _ ladder_Q' rfl _ (fun j hj ↦ ?_) (fun h7 ↦ ?_)
    · rw [hva]
      simp only [List.length_map] at hj
      exact laneAt_availL0 242 300 _ _ j (by omega)
    · rw [hva]
      simp only [List.length_map] at h7
      exact congrArg Array.ofFn (f1_availL0 242 300 _ _ (by omega))
  · refine ⟨_, _, [], rfl, rfl, (depth₀_Q default).trans (depth₀_Q idQD).symm, fun p hp ↦ ?_⟩
    obtain ⟨h59, hp⟩ := hp
    show Render.word0Q deployedRep (h₀ ++ chs) _
      (p % 2 ^ (QuotientZk.Deployed.quotientShape default).depth₀) = _
    rw [depth₀_Q]
    rw [posOf_eq_queried _ _ _ (by norm_num), ← drawsQ_append h₀ chs hh₀ (by omega)] at hp
    rw [word0Q_eq stmt w hw s (h₀ ++ chs) (by rw [habc]; exact hbad) (by omega) p hp, habc]

/-! ## The hybrid script with the view at given challenges is the honest one -/

/-- **The witness opening's hybrid script, the view at the challenges `c`, agrees with the honest
script** along any challenges `P` whose first is `c`'s `λ` and next six `c`'s lane challenges (as far
as `P` goes). -/
theorem agree_W (w : Secret) (s : RandD K) (c : DChal E) (v : E) (P : List E)
    (hhead : 1 ≤ P.length → P.headD 0 = lam₁ c)
    (htail : ∀ j ≤ 6, j < P.length → (P.drop 1).take j = (List.ofFn (phi₁ c)).take j) :
    Agree P (hybridScript (witnessLayout logRows) [⟨pointW c, v⟩]
        (Render.laneAt (jvD w c s).2.2.1.1) (Array.ofFn (jvD w c s).2.2.1.2.1))
      (openingScript (witnessLayout logRows) (wStackD w (decodeCoins (eD s))) [⟨pointW c, v⟩]) := by
  have hv := viewW c (stackWm w s) (wStackD w (decodeCoins (eD s))) (stackW w s) (size_wStackD w _) v
    (novelEnc deployedRep.w Lw.logLane (slotFn 20 224 (drawsW c)))
  dsimp only at hv
  obtain ⟨hv1, hv2⟩ := hv
  refine agree_hybrid_honest _ _ _ _ _ ladder_W' rfl P (fun j hj hjn ↦ ?_) (fun h7 ↦ ?_)
  · rw [stackClaims_length_W, hhead (by omega), htail j (by omega) hjn]
    unfold Render.laneAt
    rw [dite_eq_left hj]
    exact hv1 ⟨j, hj⟩
  · rw [htail 6 le_rfl (by omega), List.take_of_length_le (by simp)]
    exact hv2

/-- **The quotient opening's hybrid script, the view at the challenges `c`, agrees with the honest
script** (off the degenerate `α, β` of `c`, for a witness of the relation). -/
theorem agree_Q (stmt : Statement) (w : Secret) (hw : Relation stmt w) (s : RandD K) (c : DChal E)
    (hbad : ¬ BadABD w s.1 (c.1.1.1.1, c.1.1.1.2.1)) (v₁ v₂ : E) (P : List E)
    (hhead : 1 ≤ P.length → P.headD 0 = lam₂ c)
    (htail : ∀ j ≤ 6, j < P.length → (P.drop 1).take j = (List.ofFn (phi₂ c)).take j) :
    Agree P (hybridScript (quotientLayout logRows)
        [⟨pointQ P₀D F192.Y c (jvD w c s).1, v₁⟩, ⟨pointS F192.Y, v₂⟩]
        (Render.laneAt (jvD w c s).2.2.2.1) (Array.ofFn (jvD w c s).2.2.2.2.1))
      (openingScript (quotientLayout logRows) (qStackD w (decodeCoins (eD s)) c.1.1.1)
        [⟨pointQ P₀D F192.Y c (jvD w c s).1, v₁⟩, ⟨pointS F192.Y, v₂⟩]) := by
  have hv := viewQ c (jvD w c s).1 (stackQm w c.1.1.1 s) (qStackD w (decodeCoins (eD s)) c.1.1.1)
    (stackQ stmt w hw s _ hbad) (size_qStackD w _ _) v₁ v₂
    (novelEnc deployedRep.w Lq.logLane (slotFn 23 225 (drawsQ c)))
  dsimp only at hv
  obtain ⟨hv1, hv2⟩ := hv
  refine agree_hybrid_honest _ _ _ _ _ ladder_Q' rfl P (fun j hj hjn ↦ ?_) (fun h7 ↦ ?_)
  · rw [stackClaims_length_Q, hhead (by omega), htail j (by omega) hjn]
    unfold Render.laneAt
    rw [dite_eq_left hj]
    exact hv1 ⟨j, hj⟩
  · rw [htail 6 le_rfl (by omega), List.take_of_length_le (by simp)]
    exact hv2

/-! ## A, honest: the drive of the statement's honest script -/

/-- **A, witness, honest**: strictly inside the witness opening, the deployed prover's message is the
drive of the statement's honest script on its witness stack (whatever the answers `chs`), the claim's
point the joint model's (`hpt`). -/
theorem msgH_W (stmt : Statement) (w : Secret) (s : RandD K) (h₀ : List Out) (hh₀ : h₀.length = 5)
    (cl : Claims) (hcl : Render.chainClaims stmt h₀ (jvD w (chOf deployedRep.limbs h₀) s).1 = some cl)
    (hpt : cl.witness.point = pointW (chOf deployedRep.limbs h₀))
    (chs : List Out) (hc1 : 1 ≤ chs.length)
    (hc2 : chs.length < drawsIn (Render.openingEv (QuotientZk.Deployed.witnessShape idWD))) :
    msgD stmt w s (h₀ ++ chs) =
      lastMsg (evRun (Render.openingEv (QuotientZk.Deployed.witnessShape idWD)) chs
        ⟨some (openingScript (witnessLayout logRows) (wStackD w (decodeCoins (eD s))) [cl.witness]),
          [((QuotientZk.Deployed.witnessShape idWD).depth₀,
            stackWordFast 25 1 (wStackD w (decodeCoins (eD s))))], [], [], []⟩) := by
  rw [msg_W stmt w s h₀ hh₀ cl hcl chs [] hc1 hc2, List.append_nil]
  refine congrArg lastMsg (evRun_congr (fun _ ↦ True) _ chs _ _ ?_
    ⟨_, _, [], rfl, rfl, rfl, fun _ _ ↦ rfl⟩ rfl rfl rfl (posOK_true _ _ _))
  rw [draws_W] at hc2
  have hcw : (⟨pointW (chOf deployedRep.limbs (h₀ ++ chs)), cl.witness.value⟩ : Claim) =
      cl.witness := by
    rw [pointW_congr (chOf_fst_append h₀ chs (by omega)), ← hpt]
  have hhead : 1 ≤ (chs.map Render.drawChal).length →
      (chs.map Render.drawChal).headD 0 = lam₁ (chOf deployedRep.limbs (h₀ ++ chs)) := fun _ ↦ by
    rw [lam₁_chOf]
    exact headD_eq 5 h₀ chs hh₀ hc1
  have htail : ∀ j ≤ 6, j < (chs.map Render.drawChal).length →
      ((chs.map Render.drawChal).drop 1).take j =
        (List.ofFn (phi₁ (chOf deployedRep.limbs (h₀ ++ chs)))).take j := fun j hj hjn ↦ by
    simp only [List.length_map] at hjn
    exact (ofFn_take_eq 5 _ h₀ chs hh₀ (fun i ↦ phi₁_chOf _ _ i) j hj hjn).symm
  have h := agree_W w s (chOf deployedRep.limbs (h₀ ++ chs)) cl.witness.value _ hhead htail
  rw [hcw] at h
  exact h

/-- **A, quotient, honest**: strictly inside the quotient opening, the deployed prover's message is the
drive of the statement's honest script on its quotient stack at the answers' `α, β, γ` (whatever the
answers `chs`), the claims' points the joint model's (`hptQ`, `hptS`). -/
theorem msgH_Q (stmt : Statement) (w : Secret) (hw : Relation stmt w) (s : RandD K) (h₀ : List Out)
    (hh₀ : h₀.length = 242) (hbad : ¬ BadABD w s.1
      ((chOf deployedRep.limbs h₀).1.1.1.1, (chOf deployedRep.limbs h₀).1.1.1.2.1))
    (cl : Claims) (hcl : Render.chainClaims stmt h₀ (jvD w (chOf deployedRep.limbs h₀) s).1 = some cl)
    (hptQ : cl.quotient.point =
      pointQ P₀D F192.Y (chOf deployedRep.limbs h₀) (jvD w (chOf deployedRep.limbs h₀) s).1)
    (hptS : cl.sum.point = pointS F192.Y)
    (chs : List Out) (hc1 : 1 ≤ chs.length)
    (hc2 : chs.length < drawsIn (Render.openingEv (QuotientZk.Deployed.quotientShape idQD))) :
    msgD stmt w s (h₀ ++ chs) =
      lastMsg (evRun (Render.openingEv (QuotientZk.Deployed.quotientShape idQD)) chs
        ⟨some (openingScript (quotientLayout logRows)
            (qStackD w (decodeCoins (eD s)) (chOf deployedRep.limbs h₀).1.1.1) [cl.quotient, cl.sum]),
          [((QuotientZk.Deployed.quotientShape idQD).depth₀,
            stackWordFast 28 1 (qStackD w (decodeCoins (eD s)) (chOf deployedRep.limbs h₀).1.1.1))],
          [], [], []⟩) := by
  rw [msg_Q stmt w hw s h₀ hh₀ hbad cl hcl chs [] hc1 hc2, List.append_nil]
  refine congrArg lastMsg (evRun_congr (fun _ ↦ True) _ chs _ _ ?_
    ⟨_, _, [], rfl, rfl, rfl, fun _ _ ↦ rfl⟩ rfl rfl rfl (posOK_true _ _ _))
  rw [draws_Q] at hc2
  have habc : (chOf deployedRep.limbs (h₀ ++ chs)).1.1.1 = (chOf deployedRep.limbs h₀).1.1.1 := by
    rw [chOf_fst_append h₀ chs (by omega)]
  have hcq : [(⟨pointQ P₀D F192.Y (chOf deployedRep.limbs (h₀ ++ chs))
        (jvD w (chOf deployedRep.limbs (h₀ ++ chs)) s).1, cl.quotient.value⟩ : Claim),
      ⟨pointS F192.Y, cl.sum.value⟩] = [cl.quotient, cl.sum] := by
    rw [pointQ_congr P₀D F192.Y (chOf_fst_append h₀ chs (by omega)),
      jv_fst_append w s h₀ chs (by omega), ← hptQ, ← hptS]
  have hhead : 1 ≤ (chs.map Render.drawChal).length →
      (chs.map Render.drawChal).headD 0 = lam₂ (chOf deployedRep.limbs (h₀ ++ chs)) := fun _ ↦ by
    rw [lam₂_chOf]
    exact headD_eq 242 h₀ chs hh₀ hc1
  have htail : ∀ j ≤ 6, j < (chs.map Render.drawChal).length →
      ((chs.map Render.drawChal).drop 1).take j =
        (List.ofFn (phi₂ (chOf deployedRep.limbs (h₀ ++ chs)))).take j := fun j hj hjn ↦ by
    simp only [List.length_map] at hjn
    refine (ofFn_take_eq 242 _ h₀ chs hh₀ (fun i ↦ ?_) j hj hjn).symm
    rw [phi₂_chOf, show 5 + (7 + (116 + (114 + ((i : ℕ) + 1)))) = 242 + ((i : ℕ) + 1) by omega]
  have h := agree_Q stmt w hw s (chOf deployedRep.limbs (h₀ ++ chs)) (by rw [habc]; exact hbad)
    cl.quotient.value cl.sum.value _ hhead htail
  rw [hcq, habc] at h
  exact h

/-! ## B: the statement's run of the hybrid script is its run of the honest one -/

theorem headD_of_take (P : List E) (a : E) (l : List E) (h : P.take 7 = a :: l) :
    1 ≤ P.length → P.headD 0 = a := by
  rcases P with _ | ⟨b, P⟩
  · intro h1
    simp at h1
  · intro _
    change b :: P.take 6 = a :: l at h
    exact (List.cons.inj h).1

theorem tail_of_take (P : List E) (a : E) (f : Fin 6 → E) (h : P.take 7 = a :: List.ofFn f) :
    ∀ j ≤ 6, j < P.length → (P.drop 1).take j = (List.ofFn f).take j := by
  intro j hj _
  have e : (P.drop 1).take 6 = List.ofFn f := by
    have := congrArg (List.drop 1) h
    rw [List.drop_take] at this
    exact this
  rw [← e, List.take_take, min_eq_left hj]

/-- **B, witness**: the statement's run of the witness opening's hybrid script, the view at the
challenges `c`, is its run of the honest script on the statement's witness stack, when the first
seven challenges the run squeezes are `c`'s `λ` and lane challenges. -/
theorem runEvS_W (π : Equiv.Perm Eager.St) (fuel : ℕ) (id : QuotientRpm.Bytes32) (w : Secret)
    (s : RandD K) (c : DChal E) (v : E) (sp : Sponge) (cs : List Tree) (pl : List QuotientRpm.Limbs)
    (hch : (chalsEvS π fuel (Render.openingEv (QuotientZk.Deployed.witnessShape id))
      (some (hybridScript (witnessLayout logRows) [⟨pointW c, v⟩]
        (Render.laneAt (jvD w c s).2.2.1.1) (Array.ofFn (jvD w c s).2.2.1.2.1))) sp cs pl).take 7 =
      lam₁ c :: List.ofFn (phi₁ c)) :
    runEvS π fuel (Render.openingEv (QuotientZk.Deployed.witnessShape id))
        (some (hybridScript (witnessLayout logRows) [⟨pointW c, v⟩]
          (Render.laneAt (jvD w c s).2.2.1.1) (Array.ofFn (jvD w c s).2.2.1.2.1))) sp cs pl =
      runEvS π fuel (Render.openingEv (QuotientZk.Deployed.witnessShape id))
        (some (openingScript (witnessLayout logRows) (wStackD w (decodeCoins (eD s)))
          [⟨pointW c, v⟩])) sp cs pl :=
  runEvS_congr π fuel _ _ _ sp cs pl
    (agree_W w s c v _ (headD_of_take _ _ _ hch) (tail_of_take _ _ _ hch))

/-- **B, quotient**: the statement's run of the quotient opening's hybrid script, the view at the
challenges `c`, is its run of the honest script on the statement's quotient stack at `c`'s `α, β, γ`
(off the degenerate `α, β`, for a witness of the relation), when the first seven challenges the run
squeezes are `c`'s `λ` and lane challenges. -/
theorem runEvS_Q (π : Equiv.Perm Eager.St) (fuel : ℕ) (id : QuotientRpm.Bytes32) (stmt : Statement)
    (w : Secret) (hw : Relation stmt w) (s : RandD K) (c : DChal E)
    (hbad : ¬ BadABD w s.1 (c.1.1.1.1, c.1.1.1.2.1)) (v₁ v₂ : E) (sp : Sponge) (cs : List Tree)
    (pl : List QuotientRpm.Limbs)
    (hch : (chalsEvS π fuel (Render.openingEv (QuotientZk.Deployed.quotientShape id))
      (some (hybridScript (quotientLayout logRows)
        [⟨pointQ P₀D F192.Y c (jvD w c s).1, v₁⟩, ⟨pointS F192.Y, v₂⟩]
        (Render.laneAt (jvD w c s).2.2.2.1) (Array.ofFn (jvD w c s).2.2.2.2.1))) sp cs pl).take 7 =
      lam₂ c :: List.ofFn (phi₂ c)) :
    runEvS π fuel (Render.openingEv (QuotientZk.Deployed.quotientShape id))
        (some (hybridScript (quotientLayout logRows)
          [⟨pointQ P₀D F192.Y c (jvD w c s).1, v₁⟩, ⟨pointS F192.Y, v₂⟩]
          (Render.laneAt (jvD w c s).2.2.2.1) (Array.ofFn (jvD w c s).2.2.2.2.1))) sp cs pl =
      runEvS π fuel (Render.openingEv (QuotientZk.Deployed.quotientShape id))
        (some (openingScript (quotientLayout logRows) (qStackD w (decodeCoins (eD s)) c.1.1.1)
          [⟨pointQ P₀D F192.Y c (jvD w c s).1, v₁⟩, ⟨pointS F192.Y, v₂⟩])) sp cs pl :=
  runEvS_congr π fuel _ _ _ sp cs pl
    (agree_Q stmt w hw s c hbad v₁ v₂ _ (headD_of_take _ _ _ hch) (tail_of_take _ _ _ hch))

end PcsQuotient.EndToEnd.Core

/-! ## Axioms -/

/-- info: 'PcsQuotient.EndToEnd.Core.evRun_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.evRun_congr

/--
info: 'PcsQuotient.EndToEnd.Core.runEvS_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.runEvS_congr

/--
info: 'PcsQuotient.EndToEnd.Core.agree_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.agree_hybrid

/--
info: 'PcsQuotient.EndToEnd.Core.agree_hybrid_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.agree_hybrid_honest

/-- info: 'PcsQuotient.EndToEnd.Core.msg_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.msg_W

/-- info: 'PcsQuotient.EndToEnd.Core.msg_σ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.msg_σ

/-- info: 'PcsQuotient.EndToEnd.Core.msg_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.msg_Q

/-- info: 'PcsQuotient.EndToEnd.Core.msgH_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.msgH_W

/-- info: 'PcsQuotient.EndToEnd.Core.msgH_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.msgH_Q

/-- info: 'PcsQuotient.EndToEnd.Core.runEvS_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.runEvS_W

/-- info: 'PcsQuotient.EndToEnd.Core.runEvS_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.runEvS_Q

