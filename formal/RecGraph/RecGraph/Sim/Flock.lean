-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockTerminal
import RecGraph.Sim.FlockTower
import RecGraph.Sim.ComposeBase

/-!
# Flock with the walked terminal, simulated: `Pi1.verifyWalked` against `UniStatement.Flock.verifyWalkedFs`

At π1-rec3's shape (`log_n = 32`, `flockMain`: a skip of 3, the slices in tower order; `.rec3`), as `Sim` instances
(`Sim/Chan.lean`):

* `zerocheck_sim`: the seven fixed coordinates, the drawn run (one challenge and its squares), the coset's eight
  values, `z`, the skip's interpolation (`lagrangeInterpolate_ph`), the 29 rounds, `v_a`, `v_b`, `v_c`;
* `front_sim`: `α`, the lincheck's claim, its 8 rounds, the 64 slices;
* `ringEnd_sim`: the map's six challenges, the target (`towerTarget_ph`);
* `verifyWalked_sim`: the front, the walked terminal (`walkedTerminal_ph`) against the lincheck's last claim, a zero,
  the ring switch's end.

The bytes (3552) and the challenges (46) are counted from the definitions. The challenge nodes are tracked
(`Sim.chIds_len`, `sim_sumcheckDrawn_ch`): the 40th challenge of the part (index 39) is the lincheck's last round, the
first coordinate of Flock's point.
-/

-- The judgment's rules are `RecGraph.Sim.Sim.*`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## The challenge nodes -/

theorem chIds_prefix {st st' : RecState} (h : Grows st st') : ∃ L, chIds st' = chIds st ++ L := by
  obtain ⟨⟨ys, hys⟩, _⟩ := h
  unfold chIds
  have hsz : st'.nodes.size = st.nodes.size + ys.length := by
    have := congrArg List.length hys; simpa using this
  rw [hys, hsz, List.range_add, List.zip_append (by simp), List.filter_append, List.map_append]
  exact ⟨_, rfl⟩

theorem chIds_of_nodes {st st' : RecState} (h : st'.nodes = st.nodes) : chIds st' = chIds st := by
  unfold chIds; rw [h]

section Flock

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream
local notation "OptRp'" => OptRp π iv publicInput stream

/-- **The challenge nodes a part draws**: `ch` of them, appended. -/
theorem Sim.chIds_len {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p u n ch
      (fun st' a b ↦ R st' a b ∧ ∃ L, chIds st' = chIds st ++ L ∧ L.length = ch) := by
  intro c hc hle
  obtain ⟨hs, hf⟩ := h c hc hle
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b, c', hu, hc', hcur, hch, hgr, hR⟩ := hs hr
  refine ⟨b, c', hu, hc', hcur, hch, hgr, hR, ?_⟩
  obtain ⟨L, hL⟩ := chIds_prefix hgr
  refine ⟨L, hL, ?_⟩
  have h1 := congrArg List.length hc.chal
  have h2 := congrArg List.length hc'.chal
  simp only [Array.length_toList, List.length_map] at h1 h2
  rw [hL, List.length_append] at h2
  omega

theorem sumcheckBytes_some (count : ℕ) (l : List E) :
    sumcheckBytes count (l.map some) = rpBytes count true * l.length := by
  induction l with
  | nil => simp [sumcheckBytes]
  | cons x t ih =>
    simp only [sumcheckBytes, List.map_cons, List.sum_cons, Option.isSome_some] at ih ⊢
    rw [ih]; simp [Nat.mul_succ]; omega

theorem sumcheckBytes_none (count k : ℕ) :
    sumcheckBytes count (List.replicate k none) = rpBytes count false * k := by
  induction k with
  | zero => simp [sumcheckBytes]
  | succ k ih =>
    simp only [sumcheckBytes, List.replicate_succ, List.map_cons, List.sum_cons, Option.isSome_none] at ih ⊢
    rw [ih, Nat.mul_succ]; omega

/-- **`sumcheck_drawn`, its challenge nodes**: those of the point, appended in order. -/
theorem sim_sumcheckDrawn_ch (st : RecState) {claim : Nat} {c : E} (count : Nat) {eqs : List (Option Nat)}
    {eqsE : List (Option E)} (narrow : Bool) (hc : Rp' st claim c)
    (he : List.Forall₂ (OptRp' st) eqs eqsE) :
    Sim π iv publicInput stream st (Pi1.sumcheckDrawn claim count eqs narrow)
      (UniStatement.sumcheckDrawn (Fp π) c count eqsE narrow) (sumcheckBytes count eqsE) eqsE.length
      (fun st' a b ↦ RpL' st' a.1 b.1 ∧ Rp' st' a.2 b.2 ∧ chIds st' = chIds st ++ a.1) := by
  refine Sim.of_good fun hg ↦ ?_
  have hlen := he.length_eq
  unfold Pi1.sumcheckDrawn UniStatement.sumcheckDrawn
  refine Sim.cast ?_ ?_ ((Sim.forIn_list st eqs eqsE
    (fun _ st' (s : Array Nat × Nat) (t : Array E × E) ↦
      RpL' st' s.1.toList t.1.toList ∧ Rp' st' s.2 t.2 ∧ chIds st' = chIds st ++ s.1.toList)
    (fun i ↦ rpBytes count (eqsE.getD i none).isSome) (fun _ ↦ 1) _ _ hlen ?_ st (#[], claim) (#[], c) hg
    (Grows.refl st) ⟨List.Forall₂.nil, hc, by simp⟩).map (f := fun s ↦ (s.1.toList, s.2))
      (g := fun t ↦ (t.1.toList, t.2)) fun _ _ _ _ _ h ↦ h)
  · rw [hlen]; exact sum_range_getD (fun e ↦ rpBytes count e.isSome) none eqsE
  · rw [sum_const_range, hlen, Nat.one_mul]
  · intro i hi hj st' s t hg' hgr' ⟨hpt, hcl, hch⟩
    have heq : OptRp' st' eqs[i] eqsE[i] :=
      (List.forall₂_iff_get.mp he).2 i hi hj |>.grow hg.inv.kinv hgr'
    refine Sim.cast (n := rpBytes count eqsE[i].isSome + (0 + 0)) (ch := 0 + (1 + 0))
      (by rw [List.getD_eq_getElem _ _ hj]; rfl) rfl ?_
    refine Sim.bind (sim_roundPoly st' count hcl heq).chIds_len fun st1 ms xs hg1 hgr1 ⟨hms, L1, hL1, hL1l⟩ ↦ ?_
    rw [List.length_eq_zero_iff.mp hL1l, List.append_nil] at hL1
    refine Sim.bind (sim_sampleDrawn π iv publicInput stream st1 narrow) fun st2 z ze hg2 hgr2 ⟨hz, hzc, _⟩ ↦ ?_
    refine Sim.of_psim (PSim.bind (polyEval_psim st2 hg2 (hms.grow π iv publicInput stream hg1.inv.kinv hgr2) hz)
      fun st3 c' hst3 hc' ↦ PSim.pure hst3.good ⟨_, _, rfl, rfl, ?_, hc', ?_⟩)
    · rw [Array.toList_push, Array.toList_push]
      exact ((hpt.grow π iv publicInput stream hg'.inv.kinv (hgr1.trans hgr2)).snoc hz).pgrow hg2 hst3
    · rw [hst3.chal, hzc, hL1, hch, Array.toList_push, List.append_assoc]

-- BEGIN ZC

theorem squares_length (x : E) (n : ℕ) : (UniStatement.squares x n).length = n := by
  rw [squares_eq]; simp

theorem forall₂_replicate {st : RecState} {z : Sym} {x : E} (h : Rp' st z x) (n : ℕ) :
    RpL' st (List.replicate n z) (List.replicate n x) := by
  induction n with
  | zero => exact List.Forall₂.nil
  | succ n ih => rw [List.replicate_succ, List.replicate_succ]; exact List.Forall₂.cons h ih

theorem forall₂_optRp_grow {st st' : RecState} (hg : Good st) (hgr : Grows st st') {l : List (Option Sym)}
    {L : List (Option E)} (h : List.Forall₂ (OptRp' st) l L) : List.Forall₂ (OptRp' st') l L :=
  h.imp fun _ _ hr ↦ hr.grow hg.inv.kinv hgr

theorem forall₂_some {st : RecState} {l : List Sym} {L : List E} (h : RpL' st l L) :
    List.Forall₂ (OptRp' st) (l.map some) (L.map some) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem fixedChallenges_length : Flock.fixedChallenges.length = 7 := rfl

/-- `FsShape::draw` at `.rec3`: one challenge, its squares. -/
theorem sim_drawRun_rec3B (st : RecState) (count : ℕ) (hc : count ≠ 0) :
    Sim π iv publicInput stream st (Pi1.drawRun .rec3 count) (UniStatement.drawRun (Fp π) .rec3 count) 0 1
      (fun st' a b ↦ RpL' st' a b ∧ b.length = count) := by
  unfold Pi1.drawRun UniStatement.drawRun
  simp only [hc, ↓reduceIte]
  refine Sim.cast (n := 0 + 0) (ch := 1 + 0) rfl rfl ?_
  exact Sim.bind (sim_sample π iv publicInput stream st) fun st1 a x hg1 _ ⟨hx, _⟩ ↦
    Sim.of_psim ((squares_psim st1 hg1 hx count).mono fun st' a' _ h ↦ ⟨h, squares_length x count⟩)

/-- **`zerocheck(32, 3, rec3)`**, without the challenge nodes. -/
theorem zerocheck_sim0 (st : RecState) :
    Sim π iv publicInput stream st (Pi1.zerocheck 32 3 .rec3) (Flock.zerocheckFs (Fp π) 32 3 .rec3) 1632 31
      (fun st' a b ↦ OptRp' st' a.1 b.1 ∧ RpL' st' a.2.1 b.2.1 ∧ Rp' st' a.2.2.1 b.2.2.1 ∧
        Rp' st' a.2.2.2.1 b.2.2.2.1 ∧ Rp' st' a.2.2.2.2 b.2.2.2.2 ∧ b.2.1.length = 29 ∧ ∃ z, b.1 = some z) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.zerocheck Flock.zerocheckFs
  dsimp only
  simp only [show (3 : ℕ) > 0 by norm_num, ↓reduceIte]
  refine Sim.cast (n := 0 + (24 * 2 ^ 3 + (0 + (0 + (1392 + (24 + (24 + 0))))))) (ch := 1 + (0 + (1 + (0 + (29 + (0 + (0 + 0))))))) (by norm_num) (by norm_num) ?_
  refine Sim.pbind (b := ()) (R := fun st' (acc : Array (Option Sym)) _ ↦
    List.Forall₂ (OptRp' st') acc.toList (Flock.fixedChallenges.map some)) (by
      refine PH.psim ((PH.forIn_list _ _ _ st (fun j st' (acc : Array (Option Sym)) ↦
        List.Forall₂ (OptRp' st') acc.toList ((Flock.fixedChallenges.take j).map some)) hg (by simp) ?_).mono
        fun st' acc _ h ↦ ?_)
      · intro j hj st' acc hs' hacc
        refine PH.bind' (PH.const (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hs'.good _)
          fun st'' d hs'' hd ↦ PH.ret hs''.good ⟨_, rfl, ?_⟩
        rw [Array.toList_push, take_succ_getElem _ _ hj, List.map_append]
        exact List.rel_append (forall₂_optRp_grow hs'.good hs''.grows hacc) (List.Forall₂.cons hd List.Forall₂.nil)
      · rwa [List.take_length] at h) fun st1 acc hg1 hgr1 hacc ↦ ?_
  refine Sim.bind (sim_drawRun_rec3B st1 (32 - 3 - Flock.nFixed) (by decide))
    fun st2 drawn sampled hg2 hgr2 ⟨hdr, hsl⟩ ↦ ?_
  refine Sim.bind (sim_nextScalars π iv publicInput stream st2 (2 ^ 3)) fun st3 cs cU hg3 hgr3 hcs ↦ ?_
  refine Sim.bind (sim_sample π iv publicInput stream st3) fun st4 z zU hg4 hgr4 ⟨hz, _⟩ ↦ ?_
  refine Sim.pbind (zeroP π iv publicInput stream hg4) fun st5 zz hg5 hgr5 hzz ↦ ?_
  have hz5 := hz.grow π iv publicInput stream hg4.inv.kinv hgr5
  have hcs5 := (hcs.grow π iv publicInput stream hg3.inv.kinv hgr4).grow π iv publicInput stream hg4.inv.kinv hgr5
  refine Sim.pbind (PH.psim (R := Rp π iv publicInput stream)
    (lagrangeInterpolate_ph hg5 hz5 (2 ^ (3 + 1)) (show RpL' st5 (List.replicate (2 ^ 3) zz ++ cs)
      (List.replicate (2 ^ 3) 0 ++ cU) from List.rel_append (forall₂_replicate hzz _) hcs5)))
    fun st6 lg hg6 hgr6 hlg ↦ ?_
  generalize Flock.lagrangeInterpolate (2 ^ (3 + 1)) (List.replicate (2 ^ 3) 0 ++ cU) zU = LU at hlg ⊢
  refine Sim.bind (Sim.pure_of_pstep (PStep.refl st6 hg6)
    (R := fun st' (a : Option Sym × Sym) (b : Option E × E) ↦ OptRp' st' a.1 b.1 ∧ Rp' st' a.2 b.2 ∧
      ∃ z', b.1 = some z')
    ?_) fun st7 x xU hg7 hgr7 ⟨hx1, hx2, hx3⟩ ↦ ?_
  · exact ⟨hz5.grow π iv publicInput stream hg5.inv.kinv hgr6, hlg, zU, rfl⟩
  rw [← UniStatement.sumcheckDrawn_false]
  have hgr17 := hgr2.trans (hgr3.trans (hgr4.trans (hgr5.trans (hgr6.trans hgr7))))
  have heqs : List.Forall₂ (OptRp' st7) (acc ++ (List.map some drawn).toArray).toList
      (List.map some (Flock.fixedChallenges ++ sampled)) := by
    rw [Array.toList_append, List.map_append]
    refine List.rel_append (forall₂_optRp_grow hg1 hgr17 hacc) ?_
    exact forall₂_some (hdr.grow π iv publicInput stream hg2.inv.kinv
      (hgr3.trans (hgr4.trans (hgr5.trans (hgr6.trans hgr7)))))
  refine Sim.bind (Sim.cast (n' := 1392) (ch' := 29) (by
      rw [sumcheckBytes_some, List.length_append, fixedChallenges_length, hsl]; simp [rpBytes, Flock.nFixed])
    (by simp [fixedChallenges_length, hsl, Flock.nFixed]) (sim_sumcheckDrawn_ch st7 3 false hx2 heqs).chIds_len)
    fun st8 sc scU hg8 hgr8 ⟨⟨hpt, hcl, hch⟩, L, hL, hLl⟩ ↦ ?_
  have hptl : scU.1.length = 29 := by
    rw [hch] at hL
    rw [← hpt.length, List.append_cancel_left hL, hLl]
    simp [fixedChallenges_length, hsl, Flock.nFixed]
  refine Sim.bind (sim_nextScalar π iv publicInput stream st8) fun st9 vA vAU hg9 hgr9 hvA ↦ ?_
  refine Sim.bind (sim_nextScalar π iv publicInput stream st9) fun st10 vB vBU hg10 hgr10 hvB ↦ ?_
  have hvA' := hvA.grow π iv publicInput stream hg9.inv.kinv hgr10
  refine Sim.of_psim (PSim.bind (PSim.mul hg10 hvA' hvB) fun st11 ab hst11 hab ↦ ?_)
  have hcl' := ((hcl.grow π iv publicInput stream hg8.inv.kinv (hgr9.trans hgr10)).pgrow hg10 hst11)
  refine PSim.bind (PSim.add hst11.good hcl' hab) fun st12 vC hst12 hvC ↦ PSim.pure hst12.good ?_
  have hgr812 := (hgr9.trans hgr10).trans (hst11.grows.trans hst12.grows)
  refine ⟨?_, (hpt.grow π iv publicInput stream hg8.inv.kinv hgr812), ?_, ?_, hvC, hptl, hx3⟩
  · exact hx1.grow hg7.inv.kinv (hgr8.trans hgr812)
  · exact ((hvA'.pgrow hg10 hst11).pgrow hst11.good hst12)
  · exact ((hvB.pgrow hg10 hst11).pgrow hst11.good hst12)

/-- **`zerocheck(32, 3, rec3)`**: the skip's point, the rounds' point (29 coordinates), `v_a`, `v_b`, `v_c`; 31
challenge nodes appended. -/
theorem zerocheck_sim (st : RecState) :
    Sim π iv publicInput stream st (Pi1.zerocheck 32 3 .rec3) (Flock.zerocheckFs (Fp π) 32 3 .rec3) 1632 31
      (fun st' a b ↦ (OptRp' st' a.1 b.1 ∧ RpL' st' a.2.1 b.2.1 ∧ Rp' st' a.2.2.1 b.2.2.1 ∧
        Rp' st' a.2.2.2.1 b.2.2.2.1 ∧ Rp' st' a.2.2.2.2 b.2.2.2.2 ∧ b.2.1.length = 29 ∧ ∃ z, b.1 = some z) ∧
        ∃ L, chIds st' = chIds st ++ L ∧ L.length = 31) :=
  (zerocheck_sim0 st).chIds_len

-- END ZC

-- BEGIN FRONT

/-- `next_scalars(count)`, its length. -/
theorem sim_nextScalars_len (st : RecState) (count : Nat) :
    Sim π iv publicInput stream st (Pi1.nextScalars count) (UniStatement.nextScalars (m := Id) count) (24 * count) 0
      (fun st' is xs ↦ RpL' st' is xs ∧ xs.length = count) := by
  refine Sim.of_good fun hg ↦ ?_
  show Sim π iv publicInput stream st
    (forIn [:count] (#[] : Array Sym) (fun _ s ↦ Pi1.nextScalar >>= fun x ↦ pure (ForInStep.yield (s.push x))) >>=
      fun s ↦ pure s.toList)
    (forIn [:count] (#[] : Array E)
      (fun _ s ↦ UniStatement.nextScalar (m := Id) >>= fun x ↦ pure (ForInStep.yield (s.push x))) >>=
      fun s ↦ pure s.toList) _ _ _
  rw [forIn_range, forIn_range]
  have hl := Sim.forIn_list (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) st
    (List.range' 0 (count - 0)) (List.range' 0 (count - 0))
    (fun i st (s : Array Sym) (t : Array E) ↦ RpL' st s.toList t.toList ∧ t.size = i)
    (fun _ ↦ 24) (fun _ ↦ 0) (fun _ s ↦ Pi1.nextScalar >>= fun x ↦ pure (ForInStep.yield (s.push x)))
    (fun _ s ↦ UniStatement.nextScalar (m := Id) >>= fun x ↦ pure (ForInStep.yield (s.push x))) rfl
    (fun i _ _ st' s t hg' _ hI ↦ (sim_nextScalar π iv publicInput stream st').map
      (fun st'' a b _ hgr'' hr ↦ ⟨s.push a, t.push b, rfl, rfl, by
        rw [Array.toList_push, Array.toList_push]
        exact (hI.1.grow π iv publicInput stream hg'.inv.kinv hgr'').snoc hr, by simp [hI.2]⟩))
    st #[] #[] hg (Grows.refl st) ⟨List.Forall₂.nil, rfl⟩
  refine Sim.cast (by rw [sum_const_range, List.length_range', Nat.sub_zero]) (by simp)
    (hl.map fun _ _ _ _ _ h ↦ ⟨h.1, by simpa using h.2⟩)

theorem forall₂_none {st : RecState} (n : ℕ) :
    List.Forall₂ (OptRp' st) (List.replicate n none) (List.replicate n none) := by
  induction n with
  | zero => exact List.Forall₂.nil
  | succ n ih => rw [List.replicate_succ, List.replicate_succ]; exact List.Forall₂.cons trivial ih

theorem head_rev_append (l rest : List ℕ) (h : l.length = 8) : (l.reverse ++ rest).headD 0 = l.getD 7 0 := by
  have hne : l.reverse ≠ [] := by intro h'; have := congrArg List.length h'; simp [h] at this
  rw [List.headD_eq_head?_getD, List.head?_append_of_ne_nil _ hne, List.head?_reverse, List.getLast?_eq_getElem?,
    List.getD_eq_getElem?_getD, h]

theorem getD_39 (L1 : List ℕ) (a : ℕ) (l : List ℕ) (h1 : L1.length = 31) : (L1 ++ [a] ++ l).getD 39 0 = l.getD 7 0 := by
  rw [List.getD_append_right _ _ _ _ (by simp [h1])]; simp [h1]

section FrontDefs

variable (π iv publicInput stream)

/-- **What the front leaves, related** (π1-rec3's shape: the skip's point drawn, 3 low row coordinates, the 8
lincheck ones, the 64 slices sent, Flock's point of 26 coordinates). -/
structure FrontR (st : RecState) (fr : FrontS) (f : Flock.Front) : Prop where
  zSkip : OptRp' st fr.zSkip f.zSkip
  zSome : ∃ z, f.zSkip = some z
  rowLow : RpL' st fr.rowLow f.rowLow
  rowLowLen : f.rowLow.length = 3
  chiIn : RpL' st fr.chiIn f.chiIn
  chiInLen : f.chiIn.length = 8
  chiInPrime : RpL' st fr.chiInPrime f.chiInPrime
  alpha : Rp' st fr.alpha f.alpha
  rLc : Rp' st fr.rLc f.rLc
  slices : ∃ S, f.slices = some S ∧ RpL' st fr.slices S ∧ S.length = 64
  point : RpL' st fr.point f.point
  pointLen : f.point.length = 26

end FrontDefs

local notation "FrontR'" => FrontR π iv publicInput stream

theorem FrontR.grow {st st' : RecState} (hg : Good st) (hgr : Grows st st') {fr : FrontS} {f : Flock.Front}
    (h : FrontR' st fr f) : FrontR' st' fr f := by
  have hk := hg.inv.kinv
  obtain ⟨S, hS1, hS2, hS3⟩ := h.slices
  exact ⟨h.zSkip.grow hk hgr, h.zSome, h.rowLow.grow π iv publicInput stream hk hgr, h.rowLowLen,
    h.chiIn.grow π iv publicInput stream hk hgr, h.chiInLen, h.chiInPrime.grow π iv publicInput stream hk hgr,
    h.alpha.grow π iv publicInput stream hk hgr, h.rLc.grow π iv publicInput stream hk hgr,
    ⟨S, hS1, hS2.grow π iv publicInput stream hk hgr, hS3⟩, h.point.grow π iv publicInput stream hk hgr, h.pointLen⟩

/-- **`front(32, flockMain, rec3)`**: the zerocheck, `α`, the lincheck's 8 rounds, the 64 slices; 40 challenge nodes,
the 40th the lincheck's last round, Flock's point's first coordinate. -/
theorem front_sim (st : RecState) :
    Sim π iv publicInput stream st (Pi1.front 32 flockMain .rec3) (Flock.frontFs (Fp π) 32 flockMain .rec3) 3552 40
      (fun st' fr f ↦ FrontR' st' fr f ∧
        ∃ L, chIds st' = chIds st ++ L ∧ L.length = 40 ∧ L.getD 39 0 = fr.point.headD 0) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.front Flock.frontFs
  dsimp only
  refine Sim.cast (n := 1632 + (0 + (384 + (24 * Flock.kBits + 0))))
    (ch := 31 + (1 + (8 + (0 + 0)))) (by simp [Flock.kBits]) rfl ?_
  refine Sim.bind (zerocheck_sim st) fun st1 x xU hg1 hgr1 ⟨⟨hz, hchi, hvA, hvB, hvC, hchil, hzs⟩, L1, hL1, hL1l⟩ ↦ ?_
  refine Sim.bind (sim_sample π iv publicInput stream st1) fun st2 al alU hg2 hgr2 ⟨hal, hal2, _⟩ ↦ ?_
  have hk1 := hg1.inv.kinv
  refine Sim.pbind' (PSim.mul hg2 hal (hvB.grow π iv publicInput stream hk1 hgr2)) fun st3 t1 hs3 ht1 ↦ ?_
  refine Sim.pbind' (PSim.add hs3.good ((hvA.grow π iv publicInput stream hk1 hgr2).pgrow hg2 hs3) ht1)
    fun st4 s1 hs4 hs1 ↦ ?_
  have hal4 := (hal.pgrow hg2 hs3).pgrow hs3.good hs4
  refine Sim.pbind' (pow_psim st4 hs4.good hal4 2 (by norm_num)) fun st5 a2 hs5 ha2 ↦ ?_
  have hvC5 := ((((hvC.grow π iv publicInput stream hk1 hgr2).pgrow hg2 hs3).pgrow hs3.good hs4).pgrow hs4.good hs5)
  refine Sim.pbind' (PSim.mul hs5.good ha2 hvC5) fun st6 t2 hs6 ht2 ↦ ?_
  refine Sim.pbind' (PSim.add hs6.good ((hs1.pgrow hs4.good hs5).pgrow hs5.good hs6) ht2) fun st7 s2 hs7 hs2 ↦ ?_
  have hal7 := ((hal4.pgrow hs4.good hs5).pgrow hs5.good hs6).pgrow hs6.good hs7
  refine Sim.pbind' (pow_psim st7 hs7.good hal7 3 (by norm_num)) fun st8 a3 hs8 ha3 ↦ ?_
  refine Sim.pbind' (PSim.add hs8.good (hs2.pgrow hs7.good hs8) ha3) fun st9 cl hs9 hcl ↦ ?_
  have hch29 : chIds st9 = chIds st2 :=
    (((((hs9.chal.trans hs8.chal).trans hs7.chal).trans hs6.chal).trans hs5.chal).trans hs4.chal).trans hs3.chal
  rw [← UniStatement.sumcheckDrawn_false]
  refine Sim.bind (Sim.cast (n' := 384) (ch' := 8) (by
      rw [sumcheckBytes_none]; simp [rpBytes, Flock.lincheckRounds, blake2sR1csLogSize])
    (by simp [Flock.lincheckRounds, blake2sR1csLogSize])
    (sim_sumcheckDrawn_ch st9 3 false hcl (forall₂_none _)).chIds_len)
    fun st10 sc scU hg10 hgr10 ⟨⟨hpt, hrl, hch⟩, Lsc, hLsc, hLscl⟩ ↦ ?_
  have hlin : sc.1.length = 8 := by
    rw [hch] at hLsc
    rw [List.append_cancel_left hLsc, hLscl]; simp [Flock.lincheckRounds, blake2sR1csLogSize]
  rw [iteF (by decide)]
  rw [bind_map_left]
  refine Sim.bind (sim_nextScalars_len st10 Flock.kBits).chIds_len
    fun st11 sl slU hg11 hgr11 ⟨⟨hsl, hsll⟩, Lsl, hLsl, hLsll⟩ ↦ ?_
  rw [List.length_eq_zero_iff.mp hLsll, List.append_nil] at hLsl
  refine Sim.pure_of_pstep (PStep.refl st11 hg11) ?_
  have hs39 := hs3.trans (hs4.trans (hs5.trans (hs6.trans (hs7.trans (hs8.trans hs9)))))
  have hgr := hgr2.trans (hs39.grows.trans (hgr10.trans hgr11))
  have hchi' := hchi.grow π iv publicInput stream hk1 hgr
  have hptU := hpt.grow π iv publicInput stream hg10.inv.kinv hgr11
  have hsclen : scU.1.length = 8 := by rw [← hpt.length, hlin]
  refine ⟨⟨hz.grow hk1 hgr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hzs
  · exact List.forall₂_take _ hchi'
  · simp [hchil, Flock.packing, flockMain]
  · exact List.forall₂_take _ (List.forall₂_drop _ hchi')
  · simp [hchil, Flock.packing, flockMain, Flock.lincheckRounds, blake2sR1csLogSize]
  · exact List.rel_reverse hptU
  · exact (hal.pgrow hg2 hs39).grow π iv publicInput stream hs39.good.inv.kinv (hgr10.trans hgr11)
  · exact hrl.grow π iv publicInput stream hg10.inv.kinv hgr11
  · exact ⟨slU, rfl, hsl, hsll⟩
  · exact List.rel_append (List.rel_reverse hptU) (List.forall₂_drop _ (List.forall₂_drop _ hchi'))
  · simp [hchil, hsclen, Flock.packing, flockMain, Flock.lincheckRounds, blake2sR1csLogSize]
  · refine ⟨L1 ++ [al] ++ sc.1, ?_, ?_, ?_⟩
    · show chIds st11 = _
      rw [hLsl, hch, hch29, hal2, hL1, List.append_assoc, List.append_assoc, List.append_assoc]
    · simp [hL1l, hlin]
    · rw [getD_39 _ _ _ hL1l]
      exact (head_rev_append _ _ hlin).symm

-- END FRONT

end Flock

end RecGraph.Sim
