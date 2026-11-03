-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.ComposeSpec

/-!
# π1-rec3's verifier, composed: `reduce` against `reduceWithFs`

`reduce_simQ`: from the parts (`Sim/ComposeSpec.lean`), `Pi1.reduce reference words` simulates
`reduceWithFs (Fp π) reference publicWords (.flock flockMain) .point .rec3 true` for the runs ending off the hazard
(`SimE … NoHazardAt`), the outputs related by `RedR` (the roots at their stream offsets, the openings, no pending
matrices). The proof steps through both programs in lockstep; at the tail it splits on the hazard at the recorder's
values of challenges 42 and 49 (`SimE.of_cond`): off it, the tail's part (`TailSpec`, with `ShapeSpec`'s `OK`); on it,
no run ends off the hazard (`Mono`: the final channel keeps challenges 42 and 49).
-/

-- The judgments are `RecGraph.Sim.Sim`, `RecGraph.Sim.SimE`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## The shape's facts -/

theorem hvalid : (!reference.validate (Blake2s.flock flockMain != Blake2s.omitted)) = false := by
  rw [UniSound.Ids.reference_eq]; decide

theorem htower : (flockMain.slices == Flock.Slices.tower) = true := by decide

theorem hmode : (ClaimsMode.point == ClaimsMode.point) = true := rfl

theorem hlogN : blake2sR1csLogSize + reference.heights.getD opBlake2s 0 = 32 := by
  rw [reference_blake2s_height]; rfl

theorem heights_length : reference.heights.length = 6 := by rw [UniSound.Ids.reference_eq]; rfl

theorem constraintVars_eq : reference.constraintVars = 21 := by rw [UniSound.Ids.reference_eq]; rfl

theorem heights_le (r : Nat) (hr : r ∈ reference.heights) : r ≤ 18 := by
  rw [UniSound.Ids.reference_eq] at hr
  simp at hr
  omega

theorem wLen_ge : 27 ≤ wLen := by
  unfold wLen
  rw [constraintVars_eq]
  omega

theorem eqKernel_sizeC (xs : List E) : (UniStatement.eqKernel xs).size = 2 ^ xs.length := by
  unfold UniStatement.eqKernel
  suffices h : ∀ (a : Array E) (k : Nat), a.size = 2 ^ k →
      (xs.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) a).size = 2 ^ (k + xs.length) by
    simpa using h #[1] 0 rfl
  induction xs with
  | nil => intro a k h; simpa using h
  | cons x xs ih =>
    intro a k h
    rw [List.foldl_cons, ih _ (k + 1) (by simp [h, Nat.pow_succ]; ring)]
    simp only [List.length_cons]
    ring_nf

theorem digits_length (t : E) (n : Nat) : (UniStatement.digits t n).length = n := by
  rw [digits_eq]; simp

/-! ## Small pieces -/

section Pieces

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-- **`Relations::equal(column, point, value)`**. -/
theorem equalS_psim (st : RecState) (hg : Good st) (col : Column) {pt : List Nat} {ptE : List E} {v : Nat} {vE : E}
    (hpt : RpL π iv publicInput stream st pt ptE) (hv : Rp π iv publicInput stream st v vE) :
    PSim st (equalS col pt v) (Relation.equal col ptE vE) (RpRel π iv publicInput stream) := by
  unfold equalS Relation.equal
  refine PSim.bind (oneP π iv publicInput stream hg) fun st' o hst ho ↦ PSim.pure hst.good ?_
  exact ⟨List.Forall₂.cons ⟨rfl, rfl, hpt.pgrow hg hst, ho⟩ List.Forall₂.nil, hv.pgrow hg hst⟩

theorem RpRels.push {st : RecState} {a : Array RelationS} {b : Array Relation} {r : RelationS} {u : Relation}
    (h : RpRels π iv publicInput stream st a.toList b.toList) (hr : RpRel π iv publicInput stream st r u) :
    RpRels π iv publicInput stream st (a.push r).toList (b.push u).toList := by
  rw [Array.toList_push, Array.toList_push]
  exact List.rel_append h (List.Forall₂.cons hr List.Forall₂.nil)

theorem RpRels.append {st : RecState} {a : Array RelationS} {b : Array Relation} {rs : List RelationS}
    {us : List Relation} (h : RpRels π iv publicInput stream st a.toList b.toList)
    (hr : RpRels π iv publicInput stream st rs us) :
    RpRels π iv publicInput stream st (a ++ rs.toArray).toList (b ++ us.toArray).toList := by
  rw [Array.toList_append, Array.toList_append, List.toList_toArray, List.toList_toArray]
  exact List.rel_append h hr

/-- An entry of an array of nodes, represented. -/
theorem RpL.arr {st : RecState} {a : Array Nat} {b : Array E} (h : RpL π iv publicInput stream st a.toList b.toList)
    {k : Nat} (hk : k < b.size) : Rp π iv publicInput stream st (a.getD k 0) (b.getD k 0) :=
  RpL.arrGetDC π iv publicInput stream h (by have := h.length; simp at this; omega)

/-- The memory's pull relation. -/
theorem memRel_rp {st : RecState} {w : List Nat} {wE : List E} {weights : Array Nat} {weightsE : Array E}
    {mp4 : Nat} {V : E} (hw : RpL π iv publicInput stream st w wE)
    (hwt : RpL π iv publicInput stream st weights.toList weightsE.toList) (hws : weightsE.size = 16)
    (hv : Rp π iv publicInput stream st mp4 V) (lm : Nat) :
    RpRel π iv publicInput stream st
      { terms := (List.range 3).map fun k ↦ termS (.memory k) (w.take lm) (weights.getD (3 + k) 0), value := mp4 }
      { terms := (List.range 3).map fun k ↦ term (.memory k) (wE.take lm) (weightsE.getD (3 + k) 0), value := V } := by
  refine ⟨?_, hv⟩
  show List.Forall₂ _ _ _
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun k hk ↦ ⟨rfl, rfl, RpL.takeC π iv publicInput stream hw lm, ?_⟩
  exact hwt.arr (by rw [hws]; simp at hk; omega)

/-- The ring term's relation. -/
theorem ringRel_rp {st : RecState} {fp : List Nat} {fpE : List E} {o tgt : Nat} {tgtE : E}
    (hfp : RpL π iv publicInput stream st fp fpE) (ho : Rp π iv publicInput stream st o 1)
    (ht : Rp π iv publicInput stream st tgt tgtE) :
    RpRel π iv publicInput stream st
      { terms := [{ column := .qflock, point := fp, twist := ringTwist, coefficient := o }], value := tgt }
      { terms := [{ column := .qflock, point := fpE, twist := ringTwist, coefficient := 1 }], value := tgtE } :=
  ⟨List.Forall₂.cons ⟨rfl, rfl, hfp, ho⟩ List.Forall₂.nil, ht⟩

/-- **`Z_act`, the active rows' vanishing polynomials** (`reduce`'s step 3), against the `map`. -/
theorem active_psim (st : RecState) (hg : Good st) {w : List Nat} {wE : List E}
    (hw : RpL π iv publicInput stream st w wE) (hwl : wE.length = wLen) {counts : List (List Nat)}
    {countsE : List (List E)} (hc : List.Forall₂ (RpL π iv publicInput stream st) counts countsE)
    (hcl : List.Forall₂ (fun bs r ↦ bs.length = r + 1) countsE reference.heights) :
    PSim st (forIn (counts.zip reference.heights) (#[] : Array Nat) fun x s ↦ do
        let a ← Pi1.activeVanishingFromBits w x.1 x.2
        pure (ForInStep.yield (s.push a))) ()
      (fun st' a _ ↦ RpL π iv publicInput stream st' a.toList
        ((countsE.zip reference.heights).map fun x ↦ UniStatement.activeVanishingFromBits wE x.1 x.2)) := by
  have hl1 := List.Forall₂.length_eq hc
  have hl2 := List.Forall₂.length_eq hcl
  refine PSim.mono (PSim.forIn_inv st (counts.zip reference.heights)
    (fun i st (s : Array Nat) ↦ RpL π iv publicInput stream st s.toList
      (((countsE.zip reference.heights).take i).map fun x ↦ UniStatement.activeVanishingFromBits wE x.1 x.2)) _
    ?_ st #[] (PStep.refl st hg) List.Forall₂.nil) fun st' a _ h ↦ ?_
  · intro i hi st1 s hst hI
    simp only [List.length_zip] at hi
    have hci : i < counts.length := by omega
    have hcE : i < countsE.length := by omega
    have hhi : i < reference.heights.length := by omega
    simp only [List.getElem_zip]
    have hbs := ((List.forall₂_iff_get.mp hc).2 i hci hcE).pgrow hg hst
    have hbl := (List.forall₂_iff_get.mp hcl).2 i hcE hhi
    simp only [List.get_eq_getElem] at hbs hbl
    have hr := heights_le _ (List.getElem_mem hhi)
    have := wLen_ge
    refine PSim.bind (activeVanishingFromBits_psim st1 hst.good (hw.pgrow hg hst) hbs reference.heights[i]
      (by omega) (by omega)) fun st2 a hst2 ha ↦ PSim.pure hst2.good ⟨_, rfl, ?_⟩
    rw [Array.toList_push, take_succ_map _ _ i (by simp; omega)]
    simp only [List.getElem_zip]
    exact (hI.pgrow hst.good hst2).snoc ha
  · simp only [List.length_zip] at h
    rw [List.take_of_length_le (by simp only [List.length_zip]; omega)] at h
    exact h

end Pieces

/-! ## The tail, in the form `reduce` has it -/

section Tail

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-- The tail's `Sim`, in continuation form (the shape `reduce`'s do-block has). -/
theorem tail_cps {OK : List Relation → List (Column × Nat × Bool) → Prop}
    {nB chB : List Relation → List (Column × Nat × Bool) → Nat} (hTail : TailSpec OK nB chB)
    {st : RecState} (hg : Good st) (h0 : 0 < st.nodes.size) {relsS : List RelationS} {rels : List Relation}
    {rhoS : Nat} {ρ : E} {c2 : List (Column × Nat × Bool)} {mapS : List Nat} {mapE : List E}
    (hr : RpRels π iv publicInput stream st relsS rels) (hrho : Rp π iv publicInput stream st rhoS ρ)
    (hm : RpL π iv publicInput stream st mapS mapE) (hok : OK rels c2)
    {γ δ : Type} {K : List (Commitment × List Sym × Sym) → Prog γ}
    {Kc : List (Commitment × Opening) × Option Flock.MatrixClaim → ChanM Id δ} {m ch : Nat}
    {S : RecState → γ → δ → Prop}
    (hK : ∀ st' a b, Good st' → Grows st st' → OpeningsR π iv publicInput stream st' a b.1 → b.2 = none →
      Sim π iv publicInput stream st' (K a) (Kc b) m ch S) :
    Sim π iv publicInput stream st
      (forIn commitments (#[] : Array (Commitment × CombinedS)) (fun c s ↦ do
          let x ← Pi1.combine relsS c rhoS
          match x with
          | some claim => pure (ForInStep.yield (s.push (c, claim)))
          | _ => pure (ForInStep.yield s)) >>= fun s ↦
        one >>= fun _ ↦ Pi1.batch s.toList (layouts reference c2) (some mapS) >>= K)
      (tailU π rels ρ c2 mapE >>= Kc) (nB rels c2 + m) (chB rels c2 + ch) S := by
  have h := Sim.bind (hTail π iv publicInput stream st relsS rels rhoS ρ c2 mapS mapE hg h0 hr hrho hm hok)
    (k := K) (f := Kc) fun st' a b hg' hgr ⟨ho, hn⟩ ↦ hK st' a b hg' hgr ho hn
  refine Sim.congr ?_ rfl h
  simp only [tailP, prog_bind_assoc]
  rfl

end Tail

/-- `regrow hg hgr`: transport the representations along `hgr : Grows st st'` (`hg : Good st`). -/
macro "regrow " hg:ident hgr:ident : tactic =>
  `(tactic| (have hk' := ($hg).inv.kinv; sgrow hk' $hgr; clear hk' $hgr))

/-! ## `reduce` against `reduceWithFs` -/

section Reduce

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

theorem getD_toList_map {st : RecState} {l : List Nat} (k : Nat) (hk : k < l.length) :
    (l.map (val π iv publicInput stream st)).getD k 0 = val π iv publicInput stream st (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk, List.getElem_map]

theorem chIds_getD_grow {st st' : RecState} (hgr : Grows st st') {k : Nat} (hk : k < (chIds st).length) :
    (chIds st').getD k 0 = (chIds st).getD k 0 := by
  obtain ⟨l, hl⟩ := chIds_grows hgr
  rw [hl, List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hk,
    List.getElem_append_left hk]

/-- **`DegreeSpec`**: the constraint relation's degree is the shape's (`UniSound`'s `crOf_deg`). -/
theorem degreeSpec : DegreeSpec := by
  intro partsE pwE gammaE tE cvE wE hl
  rw [UniSound.Ids.Eval.constraintRelation_eq]
  exact UniSound.Ids.Eval.crOf_deg _ _ _ _ _ _ _ (by rw [hl]; decide)

theorem getD_of_prefix {a b : Array E} {l : List E} (h : a.toList = b.toList ++ l) {k : Nat} (hk : k < b.size) :
    a.getD k 0 = b.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← Array.getElem?_toList, h,
    List.getElem?_append_left (by simpa using hk)]

/-- **On the hazard, no run ends off it**: a run only extends the challenges, so the final channel keeps
challenges 42 and 49. -/
theorem not_noHazard_of_mono {β : Type} {u : ChanM Id β} (hm : Mono u) {c : Chan} (h50 : 50 ≤ c.challenges.size)
    (hz : Hazard (c.challenges.getD 42 0) (c.challenges.getD 49 0)) : ¬ NoHazardAt ((u.run).run c).2 := by
  obtain ⟨l, hl⟩ := hm c
  unfold NoHazardAt
  rw [getD_of_prefix hl (by omega), getD_of_prefix hl (by omega)]
  exact not_not.mpr hz

/-- The challenges' values a coupled channel holds. -/
theorem couple_getD {st : RecState} {c : Chan} (hc : Couple π iv publicInput stream st c) {k : Nat}
    (hk : k < (chIds st).length) :
    c.challenges.getD k 0 = val π iv publicInput stream st ((chIds st).getD k 0) := by
  have e := hc.chal
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e, ← List.getD_eq_getElem?_getD]
  exact getD_toList_map k hk

end Reduce

set_option maxHeartbeats 1000000 in
/-- **`reduce` against `reduceWithFs`**, from the parts: for the runs ending off the hazard at challenges 42 and 49
(`SimE … NoHazardAt`), the roots at their offsets, the openings and no pending matrices (`RedR`). -/
theorem reduce_simQ (PR : PartRep) (hPR : PartRepGrows PR) {TS : Table → List E → TablePart × List Relation → Prop}
    {CS : List E → E → Relation → Prop} {HS : List E → List Relation × List (Column × Nat × Bool) → Prop}
    {OK : List Relation → List (Column × Nat × Bool) → Prop} {nT : Table → Nat}
    {nB chB : List Relation → List (Column × Nat × Bool) → Nat}
    (hF : FlockSpec) (hT : TableSpec PR TS nT) (hC : ConstraintSpec PR CS) (hD : DegreeSpec) (hH : HeapSpec PR HS)
    (hTail : TailSpec OK nB chB) (hS : ShapeSpec TS CS HS OK)
    {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}
    (st : RecState) (words : List Nat) (wordsE : List E) (hg : Good st) (hseed : st.nodes[0]? = some Node.seed)
    (hcur : st.cursor = 0) (hch : chIds st = []) (hw : RpL π iv publicInput stream st words wordsE)
    (hwl : wordsE.length = 4) :
    SimE π iv publicInput stream NoHazardAt st (Pi1.reduce reference words)
      (reduceWithFs (Fp π) reference wordsE (.flock flockMain) .point .rec3 true)
      (RedR π iv publicInput stream) := by
  have hG0 : Grows st st := Grows.refl st
  unfold Pi1.reduce
  simp only [reduceWithFs, hvalid, Bool.false_eq_true, ↓reduceIte, htower, hmode, Bool.true_and, pure_bind]
  rw [hlogN]
  -- 0. The row counts.
  refine SimE.bind ((sim_countBits st reference.heights).withChIds.withCursor) ?_
  intro s1 counts countsE g1 gr1 hR
  obtain ⟨⟨⟨hcnt, hcntl⟩, l1, hl1, hl1n⟩, hcur1⟩ := hR
  regrow hg gr1
  have hch1 : chIds s1 = [] := by rw [hl1, hch, List.eq_nil_of_length_eq_zero hl1n]; rfl
  have hcur1' : s1.cursor = 24 := by rw [hcur1, hcur, heights_length]
  have hG1 : Grows s1 s1 := Grows.refl s1
  -- 1. C1's root, α, β, γ.
  refine SimE.bind ((sim_nextRoot π iv publicInput stream s1).withChIds.withCursor) ?_
  intro s2 root1 root1E g2 gr2 hR
  obtain ⟨⟨⟨hr1a, hr1b, hr1na, hr1nb⟩, l2, hl2, hl2n⟩, hcur2⟩ := hR
  regrow g1 gr2
  have hch2 : chIds s2 = [] := by rw [hl2, hch1, List.eq_nil_of_length_eq_zero hl2n]; rfl
  have hG2 : Grows s2 s2 := Grows.refl s2
  refine SimE.bind ((sim_drawRun_rec3 s2 4).withChIds.withCursor) ?_
  intro s3 alphas alphasE g3 gr3 hR
  obtain ⟨⟨⟨halpha, halphal⟩, l3, hl3, hl3n⟩, hcur3⟩ := hR
  regrow g2 gr3
  refine SimE.bind (sim_sample π iv publicInput stream s3).withCursor ?_
  intro s4 beta betaE g4 gr4 hR
  obtain ⟨⟨hbeta, hch4, -, -⟩, hcur4⟩ := hR
  regrow g3 gr4
  refine SimE.bind (sim_sample π iv publicInput stream s4).withCursor ?_
  intro s5 gamma gammaE g5 gr5 hR
  obtain ⟨⟨hgamma, hch5, -, -⟩, hcur5⟩ := hR
  regrow g4 gr5
  have hlen5 : (chIds s5).length = 3 := by
    rw [hch5, hch4, hl3, hch2]; simp at hl3n ⊢; omega
  refine SimE.pbind (eqKernel_psim s5 g5 halpha) ?_
  intro s6 weights ps6 hwts
  have gr6 := ps6.grows
  have g6 := ps6.good
  regrow g5 gr6
  have hlen6 : (chIds s6).length = 3 := by rw [ps6.chal, hlen5]
  -- 2. Flock.
  refine SimE.bind ((hF π iv publicInput stream s6).withChIds.withCursor) ?_
  intro s7 fl flE g7 gr7 hR
  obtain ⟨⟨⟨hfp, hfpl, ⟨mapE, tgtE, hend, hmap, htgt⟩, hp0⟩, l7, hl7, hl7n⟩, hcur7⟩ := hR
  regrow g6 gr7
  obtain ⟨fp, map, tgt⟩ := fl
  obtain ⟨fpE, endE⟩ := flE
  simp only at hend hfp hfpl hmap htgt hp0
  subst hend
  rw [hlen6] at hp0
  have hlen7 : (chIds s7).length = 49 := by rw [hl7, List.length_append, hlen6, hl7n]
  have hG7 : Grows s7 s7 := Grows.refl s7
  have hcur7' : s7.cursor = 3608 := by
    rw [hcur7, ps6.cursor, hcur5, hcur4, hcur3, hcur2, hcur1']
  clear hcur7 hcur5 hcur4 hcur3 hcur2 hcur1 hcur hl1 hl1n hl2 hl2n hl3 hl3n hch1 hch2 hch4 hch5 hlen5 hlen6 hl7 hl7n
  dsimp only
  -- 3. C2's root, t, the digits, Z_act.
  refine SimE.bind ((sim_nextRoot π iv publicInput stream s7).withChIds) ?_
  intro s8 root2 root2E g8 gr8 hR
  obtain ⟨⟨hr2a, hr2b, hr2na, hr2nb⟩, l8, hl8, hl8n⟩ := hR
  regrow g7 gr8
  have hlen8 : (chIds s8).length = 49 := by rw [hl8, List.length_append, hlen7, hl8n]
  have hG8 : Grows s8 s8 := Grows.refl s8
  rw [hcur7'] at hr2na hr2nb
  refine SimE.bind (sim_sample π iv publicInput stream s8) ?_
  intro s9 t tE g9 gr9 hR
  obtain ⟨ht, hch9, -, -⟩ := hR
  regrow g8 gr9
  have hG9 : Grows s9 s9 := Grows.refl s9
  have ht49 : (chIds s9).getD 49 0 = t := by
    rw [hch9, List.getD_eq_getElem _ _ (by simp [hlen8]), List.getElem_append_right (by omega)]
    simp [hlen8]
  have hlen9 : (chIds s9).length = 50 := by rw [hch9]; simp [hlen8]
  clear hch9 hl8 hl8n hlen8
  refine SimE.pbind (digits_psim s9 g9 ht wLen) ?_
  intro s10 w ps10 hw10
  have gr10 := ps10.grows
  have g10 := ps10.good
  regrow g9 gr10
  have hcnt10 := RpLL.sg g1.inv.kinv hG1 hcnt
  refine SimE.pbind (active_psim s10 g10 hw10 (digits_length _ _) hcnt10 hcntl) ?_
  intro s11 active ps11 hact
  have gr11 := ps11.grows
  have g11 := ps11.good
  regrow g10 gr11
  clear hcnt10
  -- 4. The tables.
  have hws : (UniStatement.eqKernel alphasE).size = 16 := by simp [eqKernel_sizeC, halphal]
  have hG11 : Grows s11 s11 := Grows.refl s11
  refine SimE.bind (Sim.forIn_list s11 tables tables
    (fun i st (s : Array RelationS × Array TablePartS) (u : Array Relation × Array TablePart) ↦
      RpRels π iv publicInput stream st s.1.toList u.1.toList ∧
      List.Forall₂ (PR π iv publicInput stream st) s.2.toList u.2.toList ∧
      ∃ outs : List (TablePart × List Relation),
        List.Forall₂ (fun tb o ↦ TS tb (UniStatement.digits tE wLen) o) (tables.take i) outs ∧
        u.1 = tabRels outs ∧ u.2.toList = outs.map (·.1))
    (fun i ↦ (tables.map nT).getD i 0) (fun _ ↦ 0) _ _ rfl ?_ s11 (#[], #[]) (#[], #[]) g11 (Grows.refl s11)
    ⟨List.Forall₂.nil, List.Forall₂.nil, [], List.Forall₂.nil, rfl, rfl⟩) ?_
  · intro i hi _ st' s u g' gr' hI
    obtain ⟨hrels, hparts, outs, hts, hu1, hu2⟩ := hI
    have hk11 := g11.inv.kinv
    refine Sim.cast (n := nT tables[i] + 0) (ch := 0 + 0)
      (by rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]; rfl) rfl ?_
    refine Sim.bind (hT π iv publicInput stream st' tables[i] (List.getElem_mem hi) weights
      (UniStatement.eqKernel alphasE) beta betaE w (UniStatement.digits tE wLen) (nodes_grow (hG0.trans gr') hseed)
      (hwts.sg hk11 gr') hws (hbeta.sg hk11 gr') (hw10.sg hk11 gr') (digits_length _ _)) ?_
    intro st'' a b g'' gr'' hR
    obtain ⟨hpr, hrr, hts1⟩ := hR
    refine Sim.pure_of_pstep (PStep.refl st'' g'') ⟨_, _, rfl, rfl, ?_⟩
    refine ⟨RpRels.append (hrels.sg g'.inv.kinv gr'') hrr, ?_, outs ++ [b], ?_, ?_, ?_⟩
    · rw [Array.toList_push, Array.toList_push]
      exact List.rel_append (hparts.imp fun _ _ h ↦ hPR π iv publicInput stream st' st'' _ _ g'.inv.kinv gr'' h)
        (List.Forall₂.cons hpr List.Forall₂.nil)
    · rw [List.take_add_one, List.getElem?_eq_getElem hi]
      exact List.rel_append hts (List.Forall₂.cons hts1 List.Forall₂.nil)
    · rw [hu1]; unfold tabRels; rw [List.foldl_append]; rfl
    · rw [Array.toList_push, hu2, List.map_append]; rfl
  intro s12 S T g12 gr12 hI
  obtain ⟨hrelsT, hpartsT, outs, htsT, hT1, hT2⟩ := hI
  rw [hT1] at hrelsT
  regrow g11 gr12
  have hG12 : Grows s12 s12 := Grows.refl s12
  have htabs : List.Forall₂ (fun tb o ↦ TS tb (UniStatement.digits tE wLen) o) tables outs := by
    rw [List.take_length] at htsT; exact htsT
  have houtl : outs.length = 6 := by rw [← htabs.length_eq]; rfl
  have hpl : T.2.toList.length = 6 := by rw [hT2, List.length_map, houtl]
  -- The memory's and the bytecode's values.
  refine SimE.pbind (oneP π iv publicInput stream g12) ?_
  intro s13 o ps13 ho
  have gr13 := ps13.grows; have g13 := ps13.good; regrow g12 gr13
  refine SimE.bind (sim_nextScalar π iv publicInput stream s13) ?_
  intro s14 mfc mfcE g14 gr14 hmfc
  regrow g13 gr14
  refine SimE.bind (sim_nextScalar π iv publicInput stream s14) ?_
  intro s15 addr addrE g15 gr15 haddr
  regrow g14 gr15
  refine SimE.bind (sim_nextScalar π iv publicInput stream s15) ?_
  intro s16 mpl mplE g16 gr16 hmpl
  regrow g15 gr16
  refine SimE.pbind (equalS_psim s16 g16 (.memory 3)
    (RpL.takeC π iv publicInput stream hw10 reference.logMemory) hmfc) ?_
  intro s17 d1 ps17 hd1
  have gr17 := ps17.grows; have g17 := ps17.good; regrow g16 gr17
  refine SimE.pbind (equalS_psim s17 g17 .address
    (RpL.takeC π iv publicInput stream hw10 reference.logMemory) haddr) ?_
  intro s18 d2 ps18 hd2
  have gr18 := ps18.grows; have g18 := ps18.good; regrow g17 gr18
  refine SimE.pbind (PSim.add g18 hmpl hbeta) ?_
  intro s19 mp1 ps19 hmp1
  have gr19 := ps19.grows; have g19 := ps19.good; regrow g18 gr19
  refine SimE.pbind (constP π iv publicInput stream g19 sepMem) ?_
  intro s20 cm ps20 hcm
  have gr20 := ps20.grows; have g20 := ps20.good; regrow g19 gr20
  refine SimE.pbind (PSim.mul g20 (hwts.arr (k := 0) (by rw [hws]; omega)) hcm) ?_
  intro s21 w0m ps21 hw0m
  have gr21 := ps21.grows; have g21 := ps21.good; regrow g20 gr21
  refine SimE.pbind (PSim.add g21 hmp1 hw0m) ?_
  intro s22 mp2 ps22 hmp2
  have gr22 := ps22.grows; have g22 := ps22.good; regrow g21 gr22
  refine SimE.pbind (PSim.mul g22 (hwts.arr (k := 1) (by rw [hws]; omega)) haddr) ?_
  intro s23 w1a ps23 hw1a
  have gr23 := ps23.grows; have g23 := ps23.good; regrow g22 gr23
  refine SimE.pbind (PSim.add g23 hmp2 hw1a) ?_
  intro s24 mp3 ps24 hmp3
  have gr24 := ps24.grows; have g24 := ps24.good; regrow g23 gr24
  refine SimE.pbind (PSim.mul g24 (hwts.arr (k := 2) (by rw [hws]; omega)) hmfc) ?_
  intro s25 w2m ps25 hw2m
  have gr25 := ps25.grows; have g25 := ps25.good; regrow g24 gr25
  refine SimE.pbind (PSim.add g25 hmp3 hw2m) ?_
  intro s26 mp4 ps26 hmp4
  have gr26 := ps26.grows; have g26 := ps26.good; regrow g25 gr26
  refine SimE.pbind (PSim.add g26 ho hmfc) ?_
  intro s27 om ps27 hom
  have gr27 := ps27.grows; have g27 := ps27.good; regrow g26 gr27
  refine SimE.pbind (PSim.mul g27 (hwts.arr (k := 2) (by rw [hws]; omega)) hom) ?_
  intro s28 w2om ps28 hw2om
  have gr28 := ps28.grows; have g28 := ps28.good; regrow g27 gr28
  refine SimE.pbind (PSim.add g28 hmpl hw2om) ?_
  intro s29 mps ps29 hmps
  have gr29 := ps29.grows; have g29 := ps29.good; regrow g28 gr29
  refine SimE.bind (sim_nextScalar π iv publicInput stream s29) ?_
  intro s30 bfc bfcE g30 gr30 hbfc
  regrow g29 gr30
  refine SimE.bind (sim_nextScalar π iv publicInput stream s30) ?_
  intro s31 bpl bplE g31 gr31 hbpl
  regrow g30 gr31
  refine SimE.pbind (equalS_psim s31 g31 .bytecodeFinal
    (RpL.takeC π iv publicInput stream hw10 reference.logBytecode) hbfc) ?_
  intro s32 d3 ps32 hd3
  have gr32 := ps32.grows; have g32 := ps32.good; regrow g31 gr32
  refine SimE.pbind (PSim.add g32 hbpl hbeta) ?_
  intro s33 bp1 ps33 hbp1
  have gr33 := ps33.grows; have g33 := ps33.good; regrow g32 gr33
  refine SimE.pbind (PSim.mul g33 (hwts.arr (k := 2) (by rw [hws]; omega)) hbfc) ?_
  intro s34 w2b ps34 hw2b
  have gr34 := ps34.grows; have g34 := ps34.good; regrow g33 gr34
  refine SimE.pbind (PSim.add g34 hbp1 hw2b) ?_
  intro s35 bp2 ps35 hbp2
  have gr35 := ps35.grows; have g35 := ps35.good; regrow g34 gr35
  refine SimE.pbind (equalS_psim s35 g35 .bytecodeTuple
    (RpL.appendC π iv publicInput stream halpha (RpL.takeC π iv publicInput stream hw10 reference.logBytecode))
    hbp2) ?_
  intro s36 d4 ps36 hd4
  have gr36 := ps36.grows; have g36 := ps36.good; regrow g35 gr36
  refine SimE.pbind (PSim.add g36 ho hbfc) ?_
  intro s37 ob ps37 hob
  have gr37 := ps37.grows; have g37 := ps37.good; regrow g36 gr37
  refine SimE.pbind (PSim.mul g37 (hwts.arr (k := 2) (by rw [hws]; omega)) hob) ?_
  intro s38 w2ob ps38 hw2ob
  have gr38 := ps38.grows; have g38 := ps38.good; regrow g37 gr38
  refine SimE.pbind (PSim.add g38 hbpl hw2ob) ?_
  intro s39 bps ps39 hbps
  have gr39 := ps39.grows; have g39 := ps39.good; regrow g38 gr39
  refine SimE.bind (sim_nextScalar π iv publicInput stream s39) ?_
  intro s40 hv hvE g40 gr40 hhv
  regrow g39 gr40
  refine SimE.bind (sim_nextScalar π iv publicInput stream s40) ?_
  intro s41 cv cvE g41 gr41 hcv
  regrow g40 gr41
  -- 5. The constraint quotient's relation.
  have hparts41 := hpartsT.imp fun _ _ h ↦ hPR π iv publicInput stream s12 s41 _ _ g12.inv.kinv hG12 h
  refine SimE.pbind (hC π iv publicInput stream s41 S.2.toList T.2.toList words wordsE gamma t cv gammaE tE cvE w
    (UniStatement.digits tE wLen) g41 (nodes_grow hG0 hseed) hparts41 hw hwl hgamma ht hcv hw10 rfl) ?_
  intro s42 constraint ps42 hcons
  obtain ⟨hconsR, hCS⟩ := hcons
  have gr42 := ps42.grows; have g42 := ps42.good; regrow g41 gr42
  clear hparts41
  rw [hD T.2.toList wordsE gammaE tE cvE (UniStatement.digits tE wLen) hpl]
  -- 6. The heap's relations.
  have hparts42 := hpartsT.imp fun _ _ h ↦ hPR π iv publicInput stream s12 s42 _ _ g12.inv.kinv hG12 h
  have hactl : ((countsE.zip reference.heights).map fun x ↦
      UniStatement.activeVanishingFromBits (UniStatement.digits tE wLen) x.1 x.2).length = 6 := by
    simp [hcntl.length_eq, heights_length]
  refine SimE.pbind (hH π iv publicInput stream s42 active.toList _ S.2.toList T.2.toList weights
    (UniStatement.eqKernel alphasE) beta hv cv mpl mps bpl bps betaE hvE cvE mplE _ bplE _ w
    (UniStatement.digits tE wLen) g42 (nodes_grow hG0 hseed) hact hactl hparts42 hpl hwts hws hbeta hhv hcv hmpl
    hmps hbpl hbps hw10 (digits_length _ _)) ?_
  intro s43 heapP ps43 hheap
  obtain ⟨hheapR, hcols, hHS⟩ := hheap
  have gr43 := ps43.grows; have g43 := ps43.good; regrow g42 gr43
  clear hparts42
  rw [hcols]
  -- 7. Flock's claim on q_flock.
  refine SimE.pbind (oneP π iv publicInput stream g43) ?_
  intro s44 o4 ps44 ho4
  have gr44 := ps44.grows; have g44 := ps44.good; regrow g43 gr44
  -- The hazard at the recorder's challenges 42 and 49.
  obtain ⟨l9, hl9⟩ := chIds_grows hG9
  have hlen44 : 50 ≤ (chIds s44).length := by rw [hl9, List.length_append, hlen9]; omega
  have h42 : (chIds s44).getD 42 0 = (chIds s7).getD 42 0 := chIds_getD_grow hG7 (by omega)
  have h49 : (chIds s44).getD 49 0 = t := by rw [chIds_getD_grow hG9 (by omega), ht49]
  have h42lt : (chIds s7).getD 42 0 < s7.nodes.size := by
    apply chIds_lt
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hp0' : val π iv publicInput stream s44 ((chIds s44).getD 42 0) = fpE.headD 0 := by
    rw [h42, val_sg g7.inv.kinv hG7 h42lt]
    exact hp0
  have ht44 : val π iv publicInput stream s44 ((chIds s44).getD 49 0) = tE := by rw [h49]; exact ht.2
  refine SimE.of_cond (¬ Hazard (val π iv publicInput stream s44 ((chIds s44).getD 42 0))
    (val π iv publicInput stream s44 ((chIds s44).getD 49 0))) ?_ ?_
  · intro hP
    rw [hp0', ht44] at hP
    refine SimE.bind (sim_sample π iv publicInput stream s44) ?_
    intro s45 rho rhoE g45 gr45 hR
    obtain ⟨hrho, -, -, -⟩ := hR
    regrow g44 gr45
    have hok := hS tE alphasE betaE fpE tgtE outs mfcE addrE mplE bfcE bplE _ _ halphal hfpl htabs hCS hHS hP
    rw [hT1]
    have h0' : 0 < s45.nodes.size := by
      have := nodes_grow hG0 hseed
      rcases Nat.lt_or_ge 0 s45.nodes.size with h | h
      · exact h
      · simp [Array.getElem?_eq_none h] at this
    refine SimE.of_sim (tail_cps (m := 0) (ch := 0) hTail g45 h0' (RpRels.push (RpRels.append (RpRels.push (RpRels.push (RpRels.push
      (RpRels.push (RpRels.push (RpRels.push hrelsT hd1) hd2) (memRel_rp hw10 hwts hws hmp4 reference.logMemory))
        hd3) hd4) hconsR) hheapR) (ringRel_rp hfp ho4 htgt)) hrho hmap hok ?_)
    intro s46 openings b g46 gr46 hop hn
    obtain ⟨bo, bd⟩ := b
    simp only at hn hop
    subst hn
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hk45 := g45.inv.kinv
    refine Sim.pure_of_pstep (PStep.refl s46 g46) ⟨⟨hr1a.sg hk45 gr46, hr1b.sg hk45 gr46, ?_, ?_⟩,
      ⟨hr2a.sg hk45 gr46, hr2b.sg hk45 gr46, nodes_grow (hG8.trans gr46) hr2na,
        nodes_grow (hG8.trans gr46) hr2nb⟩, hop, rfl⟩
    · rw [← hcur1']; exact nodes_grow (hG2.trans gr46) hr1na
    · rw [← hcur1']; exact nodes_grow (hG2.trans gr46) hr1nb
  · intro hnP c hc
    rw [not_not] at hnP
    have hsize : (chIds s44).length = c.challenges.size := by
      have e := congrArg List.length hc.chal
      simpa using e.symm
    refine not_noHazard_of_mono (Mono.bind (Mono.sample π) fun _ ↦ Mono.bind (Mono.batchFs π _ _ _ _) fun x ↦ by
      split <;> exact Mono.ret _) (by omega) ?_
    rw [couple_getD hc (by omega), couple_getD hc (by omega)]
    exact hnP

end RecGraph.Sim
