-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR word `stackWordFast` is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/Prover/Ntt.lean`); the opening's events are read off `Deployed.opening`.
import ZK.CoreRenderSame
import ZK.CoreDeployed
import ZK.CoreTables
import ZK.CoreView

/-!
# The deployed openings: where commitment `0` is opened, and the view's parts

The facts `CoreRender.lean` combines, at the deployed instance:

* **the challenges** (`dF_eq_drawChal`): the joint model's draw challenge (`dF`, the deployed limbs)
  is the renderer's (`drawChal`); the lane challenges of an opening starting after `k₀` answers are the
  draws' (`ofFn_take_eq`); the claims (`chainClaims_append`) and the five values (`avail_fst`) read
  only the first five answers;
* **availability** (`laneAt_availL0`, …): a lane round is the full view's once drawn for, and so are
  the folded table and the opened rows;
* **commitment `0`'s opened rows** (`posOK_W`, `posOK_Q`): in a secret opening, the events open
  commitment `0` once, at the windows of the position draws `26 … 50` (witness) or `29 … 57`
  (quotient) of the opening, which are the joint model's level-0 draws (`drawsW_append`,
  `drawsQ_append`); at those positions the renderer's rows from the view are the statement's WHIR
  word's (`word0W_eq`, `word0Q_eq`: `jv_W_rows`, `slotFn_slotOf`, `codeW`, `stackW`).
-/

open Polynomial QuotientSecurity QuotientSecurity.Hiding
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient.Domain
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Out Msg)
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-- The deployed joint view. -/
noncomputable abbrev jvD (w : Secret) (c : DChal E) (s : RandD K) : JV K E :=
  jv deployedRep P₀D (gKD w) vanD F192.Y (TWD w) (TQD w) c s

/-! ## Challenges -/

/-- **A draw's challenge**: the joint model's (`dF`, the deployed limbs) is the renderer's. -/
theorem dF_eq_drawChal (o : Out) : dF deployedRep.limbs o = Render.drawChal o := by
  apply deployedRep.limbs.injective
  show deployedRep.limbs (deployedRep.limbs.symm (drawLimbs o)) = _
  rw [Equiv.apply_symm_apply]
  show drawLimbs o = Render.limbsOf (Compile.challengeOf o.2)
  rw [Duplex.limbsOf_challengeOf]
  rfl

theorem getD_append_left' (h₀ chs : List Out) {i : ℕ} (hi : i < h₀.length) :
    (h₀ ++ chs).getD i default = h₀.getD i default := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_right' (h₀ chs : List Out) {i : ℕ} (hi : h₀.length ≤ i) :
    (h₀ ++ chs).getD i default = chs.getD (i - h₀.length) default := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

/-- **The lane challenges are the draws'**: an opening's `j ≤ 6` lane challenges (`f i` the joint
model's at answer `k₀ + i + 1`) are the challenges of the opening's draws `1 … j`. -/
theorem ofFn_take_eq (k₀ : ℕ) (f : Fin 6 → E) (h₀ chs : List Out) (hh : h₀.length = k₀)
    (hf : ∀ i : Fin 6, f i = dF deployedRep.limbs ((h₀ ++ chs).getD (k₀ + ((i : ℕ) + 1)) default))
    (j : ℕ) (hj : j ≤ 6) (hjn : j < chs.length) :
    (List.ofFn f).take j = ((chs.map Render.drawChal).drop 1).take j := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn, List.length_drop, List.length_map]
    omega
  · intro i h1 h2
    simp only [List.length_take, List.length_ofFn] at h1
    have hi : i < 6 := by omega
    have hin : i + 1 < chs.length := by omega
    simp only [List.getElem_take, List.getElem_ofFn, List.getElem_drop, List.getElem_map]
    rw [hf]
    show dF deployedRep.limbs ((h₀ ++ chs).getD (k₀ + (i + 1)) default) = _
    rw [getD_append_right' _ _ (by omega), dF_eq_drawChal,
      List.getD_eq_getElem _ _ (by omega)]
    congr 2
    omega

/-- The first lane challenge (`λ`) is the first draw's. -/
theorem headD_eq (k₀ : ℕ) (h₀ chs : List Out) (hh : h₀.length = k₀) (hn : 1 ≤ chs.length) :
    (chs.map Render.drawChal).headD 0 = dF deployedRep.limbs ((h₀ ++ chs).getD k₀ default) := by
  rw [getD_append_right' _ _ (by omega), hh, Nat.sub_self, dF_eq_drawChal]
  rcases chs with _ | ⟨o, chs⟩
  · simp at hn
  · rfl

/-- **The claims read the first five answers.** -/
theorem chainClaims_append (stmt : Statement) (h₀ chs : List Out) (hh : 5 ≤ h₀.length)
    (v : Vals E) : Render.chainClaims stmt (h₀ ++ chs) v = Render.chainClaims stmt h₀ v := by
  unfold Render.chainClaims
  rw [getD_append_left' h₀ chs (by omega : 0 < h₀.length),
    getD_append_left' h₀ chs (by omega : 1 < h₀.length),
    getD_append_left' h₀ chs (by omega : 2 < h₀.length),
    getD_append_left' h₀ chs (by omega : 3 < h₀.length),
    getD_append_left' h₀ chs (by omega : 4 < h₀.length)]

/-- The chain challenges read the first five answers. -/
theorem chOf_fst_append (h₀ chs : List Out) (hh : 5 ≤ h₀.length) :
    (chOf (E := E) deployedRep.limbs (h₀ ++ chs)).1 = (chOf deployedRep.limbs h₀).1 := by
  have e := chOf_take_fst deployedRep.limbs (h₀ ++ chs) (k := h₀.length) hh
  rw [List.take_left' rfl] at e
  exact e.symm

/-- The five values read the first five answers. -/
theorem jv_fst_append (w : Secret) (s : RandD K) (h₀ chs : List Out) (hh : 5 ≤ h₀.length) :
    (jvD w (chOf deployedRep.limbs (h₀ ++ chs)) s).1 = (jvD w (chOf deployedRep.limbs h₀) s).1 := by
  rw [jv_red, jv_red, chOf_fst_append h₀ chs hh]

/-- **The five values** available after the answers `h₀ ++ chs` are the joint view's at `h₀`. -/
theorem avail_fst (w : Secret) (s : RandD K) (h₀ chs : List Out) (hh : 5 ≤ h₀.length) :
    (avail (h₀ ++ chs).length (jvD w (chOf deployedRep.limbs (h₀ ++ chs)) s)).1 =
      (jvD w (chOf deployedRep.limbs h₀) s).1 := by
  show (if 4 ≤ (h₀ ++ chs).length then _ else 0) = _
  rw [ite_eq_left (by rw [List.length_append]; omega)]
  exact jv_fst_append w s h₀ chs hh

/-! ## Availability -/

theorem laneAt_availL0 {ι Yt Q : Type} (st pe k : ℕ) (lv : L0View E ι Yt Q K) (j : ℕ)
    (hj : st + 1 + j ≤ k) : Render.laneAt (availL0 st pe k lv).1 j = Render.laneAt lv.1 j := by
  unfold Render.laneAt
  split_ifs with h
  · exact ite_eq_left hj
  · rfl

theorem f1_availL0 {ι Yt Q : Type} (st pe k : ℕ) (lv : L0View E ι Yt Q K) (hk : st + 7 ≤ k) :
    (availL0 st pe k lv).2.1 = lv.2.1 := ite_eq_left hk

theorem rows_availL0 {ι Yt Q : Type} (st pe k : ℕ) (lv : L0View E ι Yt Q K) (hk : pe ≤ k) :
    (availL0 st pe k lv).2.2 = lv.2.2 := ite_eq_left hk

/-! ## Where commitment `0` is opened -/

/-- No position draw and no opened rows. -/
def plainB : List Render.Ev → Bool
  | [] => true
  | .draw :: evs => plainB evs
  | .send _ :: evs => plainB evs
  | .commit _ :: evs => plainB evs
  | .grind :: evs => plainB evs
  | .posDraw :: _ => false
  | .opened _ _ _ :: _ => false

/-- No opened rows of commitment `0`. -/
def noOpen0B : List Render.Ev → Bool
  | [] => true
  | .opened lvl _ _ :: evs => decide (lvl ≠ 0) && noOpen0B evs
  | _ :: evs => noOpen0B evs

theorem posOK_noOpen0 (G : ℕ → Prop) : ∀ (evs : List Render.Ev) (chs : List Out)
    (pl : List QuotientRpm.Limbs), noOpen0B evs = true → PosOK G evs chs pl
  | [], _, _, _ => trivial
  | .draw :: _, [], _, _ => trivial
  | .draw :: evs, _ :: chs, pl, h => posOK_noOpen0 G evs chs pl h
  | .posDraw :: _, [], _, _ => trivial
  | .posDraw :: evs, _ :: chs, _, h => posOK_noOpen0 G evs chs _ h
  | .send _ :: evs, chs, pl, h => posOK_noOpen0 G evs chs pl h
  | .commit _ :: evs, chs, pl, h => posOK_noOpen0 G evs chs pl h
  | .grind :: evs, chs, pl, h => posOK_noOpen0 G evs chs pl h
  | .opened lvl _ _ :: evs, chs, _, h => by
    simp only [noOpen0B, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fun h0 ↦ absurd h0 h.1, posOK_noOpen0 G evs chs [] h.2⟩

/-- `G` everywhere: nothing to check. -/
theorem posOK_true : ∀ (evs : List Render.Ev) (chs : List Out) (pl : List QuotientRpm.Limbs),
    PosOK (fun _ ↦ True) evs chs pl
  | [], _, _ => trivial
  | .draw :: _, [], _ => trivial
  | .draw :: evs, _ :: chs, pl => posOK_true evs chs pl
  | .posDraw :: _, [], _ => trivial
  | .posDraw :: evs, _ :: chs, _ => posOK_true evs chs _
  | .send _ :: evs, chs, pl => posOK_true evs chs pl
  | .commit _ :: evs, chs, pl => posOK_true evs chs pl
  | .grind :: evs, chs, pl => posOK_true evs chs pl
  | .opened _ _ _ :: evs, chs, _ => ⟨fun _ _ _ ↦ trivial, posOK_true evs chs []⟩

/-- Plain events take their draws' answers. -/
theorem posOK_plain (G : ℕ → Prop) (R : List Render.Ev) : ∀ (evs : List Render.Ev) (chs : List Out)
    (pl : List QuotientRpm.Limbs), plainB evs = true →
    (drawsIn evs ≤ chs.length → PosOK G R (chs.drop (drawsIn evs)) pl) → PosOK G (evs ++ R) chs pl
  | [], chs, pl, _, h => h (Nat.zero_le _)
  | .draw :: _, [], _, _, _ => trivial
  | .draw :: evs, _ :: chs, pl, hp, h => posOK_plain G R evs chs pl hp fun hn ↦ h (by
      simp only [drawsIn, List.length_cons]; omega)
  | .send _ :: evs, chs, pl, hp, h => posOK_plain G R evs chs pl hp h
  | .commit _ :: evs, chs, pl, hp, h => posOK_plain G R evs chs pl hp h
  | .grind :: evs, chs, pl, hp, h => posOK_plain G R evs chs pl hp h

/-- Position draws take their answers' limbs. -/
theorem posOK_posDraws (G : ℕ → Prop) (R : List Render.Ev) : ∀ (m : ℕ) (chs : List Out)
    (pl : List QuotientRpm.Limbs),
    (m ≤ chs.length → PosOK G R (chs.drop m) (pl ++ (chs.take m).map drawLimbs)) →
    PosOK G (List.replicate m .posDraw ++ R) chs pl
  | 0, chs, pl, h => by simpa using h (Nat.zero_le _)
  | _ + 1, [], _, _ => trivial
  | m + 1, o :: chs, pl, h => by
    refine posOK_posDraws G R m chs _ fun hm ↦ ?_
    have := h (by simp only [List.length_cons]; omega)
    simp only [List.drop_succ_cons, List.take_succ_cons, List.map_cons, List.append_assoc,
      List.singleton_append] at this ⊢
    exact this

/-- A draw, then commitment `0`'s opened rows. -/
theorem posOK_open0 (G : ℕ → Prop) (R : List Render.Ev) (q b : ℕ) (chs : List Out)
    (pl : List QuotientRpm.Limbs)
    (h : 1 ≤ chs.length → (∀ p ∈ posOf pl b q, G p) ∧ PosOK G R (chs.drop 1) []) :
    PosOK G (.draw :: .opened 0 q b :: R) chs pl := by
  rcases chs with _ | ⟨o, chs⟩
  · trivial
  · obtain ⟨h1, h2⟩ := h (by simp)
    exact ⟨fun _ ↦ h1, h2⟩

/-- The witness opening up to its level-0 position draws. -/
def preW : List Render.Ev :=
  [.draw, .send 2] ++ Render.roundsEv 6 ++ [.commit 19] ++ Render.oodEv 19 ++ [.grind]

/-- The witness opening after its level-0 opened rows. -/
def postW : List Render.Ev := (Render.openingEv (QuotientZk.Deployed.witnessShape default)).drop 63

/-- The quotient opening up to its level-0 position draws. -/
def preQ : List Render.Ev :=
  [.draw, .send 2] ++ Render.roundsEv 6 ++ [.commit 22] ++ Render.oodEv 22 ++ [.grind]

/-- The quotient opening after its level-0 opened rows. -/
def postQ : List Render.Ev := (Render.openingEv (QuotientZk.Deployed.quotientShape default)).drop 70

theorem split_W (id : QuotientRpm.Bytes32) :
    Render.openingEv (QuotientZk.Deployed.witnessShape id) =
      preW ++ (List.replicate 25 .posDraw ++ (.draw :: .opened 0 224 20 :: postW)) := by
  unfold postW
  rw [openingEv_W, openingEv_W]
  decide +kernel

theorem split_Q (id : QuotientRpm.Bytes32) :
    Render.openingEv (QuotientZk.Deployed.quotientShape id) =
      preQ ++ (List.replicate 29 .posDraw ++ (.draw :: .opened 0 225 23 :: postQ)) := by
  unfold postQ
  rw [openingEv_Q, openingEv_Q]
  decide +kernel

theorem plain_preW : plainB preW = true := by decide +kernel
theorem plain_preQ : plainB preQ = true := by decide +kernel
theorem draws_preW : drawsIn preW = 26 := by decide +kernel
theorem draws_preQ : drawsIn preQ = 29 := by decide +kernel

theorem noOpen0_postW : noOpen0B postW = true := by
  unfold postW
  rw [openingEv_W]
  decide +kernel

theorem noOpen0_postQ : noOpen0B postQ = true := by
  unfold postQ
  rw [openingEv_Q]
  decide +kernel

/-- **The witness opening opens commitment `0` at the windows of its position draws `26 … 50`.** -/
theorem posOK_W (id : QuotientRpm.Bytes32) (G : ℕ → Prop) (chs : List Out)
    (hG : 52 ≤ chs.length → ∀ p ∈ posOf (((chs.drop 26).take 25).map drawLimbs) 20 224, G p) :
    PosOK G (Render.openingEv (QuotientZk.Deployed.witnessShape id)) chs [] := by
  rw [split_W]
  refine posOK_plain G _ preW chs [] plain_preW fun h26 ↦ ?_
  rw [draws_preW] at h26 ⊢
  refine posOK_posDraws G _ 25 _ [] fun h25 ↦ ?_
  refine posOK_open0 G _ _ _ _ _ fun h1 ↦ ⟨?_, posOK_noOpen0 G _ _ _ noOpen0_postW⟩
  rw [List.nil_append]
  simp only [List.length_drop] at h1 h25
  exact hG (by omega)

/-- **The quotient opening opens commitment `0` at the windows of its position draws `29 … 57`.** -/
theorem posOK_Q (id : QuotientRpm.Bytes32) (G : ℕ → Prop) (chs : List Out)
    (hG : 59 ≤ chs.length → ∀ p ∈ posOf (((chs.drop 29).take 29).map drawLimbs) 23 225, G p) :
    PosOK G (Render.openingEv (QuotientZk.Deployed.quotientShape id)) chs [] := by
  rw [split_Q]
  refine posOK_plain G _ preQ chs [] plain_preQ fun h29 ↦ ?_
  rw [draws_preQ] at h29 ⊢
  refine posOK_posDraws G _ 29 _ [] fun h29' ↦ ?_
  refine posOK_open0 G _ _ _ _ _ fun h1 ↦ ⟨?_, posOK_noOpen0 G _ _ _ noOpen0_postQ⟩
  rw [List.nil_append]
  simp only [List.length_drop] at h1 h29'
  exact hG (by omega)

/-! ## Commitment `0`'s opened rows -/

theorem posOf_eq_queried (ds : List QuotientRpm.Limbs) (b q : ℕ) (hb : 1 ≤ b) :
    posOf ds b q = queried b q ds := by
  unfold posOf queried
  rw [max_eq_left hb]

theorem mem_slotsOf_of_queried {b q x : ℕ} {ds : List QuotientRpm.Limbs}
    (h : x ∈ queried b q ds) : x ∈ slotsOf b q ds := by
  unfold slotsOf
  have hl : (queried b q ds).dedup.length ≤ q :=
    (List.dedup_sublist _).length_le.trans (by unfold queried; exact List.length_take_le _ _)
  rw [List.take_append, List.take_of_length_le hl]
  exact List.mem_append_left _ (List.mem_dedup.mpr h)

/-- **The witness opening's position draws are the joint model's level-0 draws** (`drawsW`). -/
theorem drawsW_append (h₀ chs : List Out) (hh : h₀.length = 5) (hn : 51 ≤ chs.length) :
    drawsW (chOf deployedRep.limbs (h₀ ++ chs)) = ((chs.drop 26).take 25).map drawLimbs := by
  unfold drawsW
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_take, List.getElem_drop]
    rw [gW_chOf]
    show drawLimbs ((h₀ ++ chs).getD (5 + (7 + (19 + i))) default) = _
    rw [getD_append_right' _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    congr 2
    omega

/-- **The quotient opening's position draws are the joint model's level-0 draws** (`drawsQ`). -/
theorem drawsQ_append (h₀ chs : List Out) (hh : h₀.length = 242) (hn : 58 ≤ chs.length) :
    drawsQ (chOf deployedRep.limbs (h₀ ++ chs)) = ((chs.drop 29).take 29).map drawLimbs := by
  unfold drawsQ
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_take, List.getElem_drop]
    rw [gQ_chOf]
    show drawLimbs ((h₀ ++ chs).getD (5 + (7 + (116 + (114 + (7 + (22 + i)))))) default) = _
    rw [getD_append_right' _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    congr 2
    omega

/-- **The witness table's rows from the view are the statement's WHIR word's** at the queried
positions, once the rows are drawn for. -/
theorem word0W_eq (w : Secret) (s : RandD K) (h : List Out) (hk : 56 ≤ h.length) (p : ℕ)
    (hp : p ∈ queried 20 224 (drawsW (chOf deployedRep.limbs h))) :
    Render.word0W deployedRep h (avail h.length (jvD w (chOf deployedRep.limbs h) s)) (p % 2 ^ 20) =
      stackWordFast 25 1 (wStackD w (decodeCoins (eD s))) (p % 2 ^ 20) := by
  have hp20 : p < 2 ^ 20 := lt_of_mem_queried hp
  rw [Nat.mod_eq_of_lt hp20]
  have hmem : p ∈ slotsW (chOf deployedRep.limbs h) := mem_slotsOf_of_queried hp
  unfold Render.word0W
  rw [show (avail h.length (jvD w (chOf deployedRep.limbs h) s)).2.2.1.2.2 =
    (jvD w (chOf deployedRep.limbs h) s).2.2.1.2.2 from rows_availL0 5 56 _ _ hk, jv_W_rows,
    rowsMap_eq_rowAt]
  have e : novelEnc deployedRep.w Lw.logLane (slotFn 20 224 (drawsW (chOf deployedRep.limbs h)))
      (slotOf 20 224 (drawsW (chOf deployedRep.limbs h)) p) = codeAt deployedRep Lw.logLane p := by
    funext y
    simp only [novelEnc, codeAt]
    rw [slotFn_slotOf _ _ _ hmem]
  rw [e]
  exact codeW (stackWm w s) _ (stackW w s) (size_wStackD w _) p hp20

/-- **The quotient table's rows from the view are the statement's WHIR word's** (of the quotient
stack at the answers' `α, β, γ`, off the degenerate `α, β`) at the queried positions. -/
theorem word0Q_eq (stmt : Statement) (w : Secret) (hw : Relation stmt w) (s : RandD K)
    (h : List Out) (hbad : ¬ BadABD w s.1
      ((chOf deployedRep.limbs h).1.1.1.1, (chOf deployedRep.limbs h).1.1.1.2.1))
    (hk : 300 ≤ h.length) (p : ℕ) (hp : p ∈ queried 23 225 (drawsQ (chOf deployedRep.limbs h))) :
    Render.word0Q deployedRep h (avail h.length (jvD w (chOf deployedRep.limbs h) s)) (p % 2 ^ 23) =
      stackWordFast 28 1 (qStackD w (decodeCoins (eD s)) (chOf deployedRep.limbs h).1.1.1)
        (p % 2 ^ 23) := by
  have hp23 : p < 2 ^ 23 := lt_of_mem_queried hp
  rw [Nat.mod_eq_of_lt hp23]
  have hmem : p ∈ slotsQ (chOf deployedRep.limbs h) := mem_slotsOf_of_queried hp
  unfold Render.word0Q
  rw [show (avail h.length (jvD w (chOf deployedRep.limbs h) s)).2.2.2.2.2 =
    (jvD w (chOf deployedRep.limbs h) s).2.2.2.2.2 from rows_availL0 242 300 _ _ hk, jv_Q_rows,
    rowsMap_eq_rowAt]
  have e : novelEnc deployedRep.w Lq.logLane (slotFn 23 225 (drawsQ (chOf deployedRep.limbs h)))
      (slotOf 23 225 (drawsQ (chOf deployedRep.limbs h)) p) = codeAt deployedRep Lq.logLane p := by
    funext y
    simp only [novelEnc, codeAt]
    rw [slotFn_slotOf _ _ _ hmem]
  rw [e]
  exact codeQ (stackQm w (chOf deployedRep.limbs h).1.1.1 s) _
    (stackQ stmt w hw s _ hbad) (size_qStackD w _ _) p hp23

/-! ## The layouts' ladders and claims -/

theorem ladder_W' : Whir.ladder (witnessLayout logRows).logN logInvRate = some cfgW := ladder_W
theorem ladder_Q' : Whir.ladder (quotientLayout logRows).logN logInvRate = some cfgQ := ladder_Q

/-- A hidden layout batches the gadget after the claims. -/
theorem stackClaims_length_W (cls : List Claim) :
    (stackClaims (witnessLayout logRows) cls).length = cls.length + 1 := by
  unfold stackClaims
  rw [List.length_append, List.length_map]
  rfl

theorem stackClaims_length_Q (cls : List Claim) :
    (stackClaims (quotientLayout logRows) cls).length = cls.length + 1 := by
  unfold stackClaims
  rw [List.length_append, List.length_map]
  rfl

end PcsQuotient.EndToEnd.Core
