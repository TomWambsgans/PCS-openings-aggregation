-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.ComposeSpec

/-!
# π1-rec3's verifier, composed: `reduce` against `reduceWithFs`

`reduce_simQ`: from the parts (`Sim/ComposeSpec.lean`), `Pi1.reduce reference words` simulates
`reduceWithFs (Fp π) reference publicWords (.flock flockMain) .point .rec3 true` for the runs ending off the hazard
(`SimQ … NoHazardAt`), the outputs related by `RedR` (the roots at their stream offsets, the openings, no pending
matrices). The proof steps through both programs in lockstep; at the tail it splits on the hazard at the recorder's
values of challenges 42 and 49 (`SimQ.of_cond`): off it, the tail's part (`TailSpec`, with `ShapeSpec`'s `OK`); on it,
no run ends off the hazard (`Mono`: the final channel keeps challenges 42 and 49).
-/

-- The judgments are `RecGraph.Sim.Sim`, `RecGraph.Sim.SimQ`.
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

theorem eqKernel_size (xs : List E) : (UniStatement.eqKernel xs).size = 2 ^ xs.length := by
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

theorem squares_length (x : E) (n : Nat) : (UniStatement.squares x n).length = n := by
  rw [squares_eq]; simp

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
  `(tactic| (have hk' := ($hg).inv.kinv; sgrow hk' $hgr; clear hk'))

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

/-- The challenges' values a coupled channel holds. -/
theorem couple_getD {st : RecState} {c : Chan} (hc : Couple π iv publicInput stream st c) {k : Nat}
    (hk : k < (chIds st).length) :
    c.challenges.getD k 0 = val π iv publicInput stream st ((chIds st).getD k 0) := by
  have e := hc.chal
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e, ← List.getD_eq_getElem?_getD]
  exact getD_toList_map k hk

end Reduce

end RecGraph.Sim
