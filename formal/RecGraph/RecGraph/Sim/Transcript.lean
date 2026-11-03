-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Pure

/-!
# The simulation: the transcript's pieces

`Sim` instances (`Sim/Chan.lean`) of `Pi1/Ops.lean`'s and `Pi1/Verifier.lean`'s transcript functions against
`UniStatement`'s:

* `sim_roundPoly`: a sumcheck round's message (both cases: `c_1` from the claim, or `c_0` with the eq factor);
* `sim_sumcheckDrawn`: the sumcheck, any equalities' list, narrow or not;
* `sim_pairRoundPoly`, `sim_sumcheckPairsDrawn`: π1-rec3's paired rounds, then the odd variable's plain round;
* `sim_drawRun`: `FsShape::draw` (every shape: `main` draws each challenge, the others one and its squares);
* `sim_countBits`: the row counts, each a 4-byte integer, its range and its bits (`intBits`; a count is below
  `2^32`).

The bytes and the challenges each reads and draws are functions of the shape only: `rpBytes`, `sumcheckBytes`,
`pairBytes`, `pairsBytes`, `pairsCh`, `drawCh`.
-/

-- The judgment's rules are `RecGraph.Sim.Sim.*`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

section Transcript

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-- A part against `pure`: a pure part first, then any program part. -/
theorem Sim.pbind {st : RecState} {α β γ δ : Type} {p : Prog α} {b : β} {R : RecState → α → β → Prop}
    {k : α → Prog γ} {u : ChanM Id δ} {m ch : Nat} {S : RecState → γ → δ → Prop}
    (h1 : PSim st p b R)
    (h2 : ∀ st' a, Good st' → Grows st st' → R st' a b → Sim π iv publicInput stream st' (k a) u m ch S) :
    Sim π iv publicInput stream st (p >>= k) u m ch S := by
  have h1' : PSim st p b (fun st' a b' ↦ R st' a b' ∧ b' = b) := ⟨h1.1, h1.2, rfl⟩
  have := Sim.bind (Sim.of_psim (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) h1')
    (f := fun _ ↦ u) fun st' a b' hg hgr ⟨hR, hb⟩ ↦ h2 st' a hg hgr (hb ▸ hR)
  rw [pure_bind] at this
  exact Sim.cast (Nat.zero_add m) (Nat.zero_add ch) this

/-- A `[a:b]` loop on both sides, as the loop over `List.range' a (b - a)`. -/
theorem Sim.forIn_range_congr {st : RecState} {σ τ γ δ : Type} {a b : Nat} {s : σ} {t : τ}
    {body : Nat → σ → Prog (ForInStep σ)} {ubody : Nat → τ → ChanM Id (ForInStep τ)} {k : σ → Prog γ}
    {f : τ → ChanM Id δ} {n ch : Nat} {R : RecState → γ → δ → Prop}
    (h : Sim π iv publicInput stream st (forIn (List.range' a (b - a)) s body >>= k)
      (forIn (List.range' a (b - a)) t ubody >>= f) n ch R) :
    Sim π iv publicInput stream st (forIn [a:b] s body >>= k) (forIn [a:b] t ubody >>= f) n ch R := by
  rw [forIn_range, forIn_range]
  exact h

/-- The eq factors, related: both absent, or both there, represented. -/
def OptRp (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState) :
    Option Nat → Option E → Prop
  | none, none => True
  | some r, some x => Rp π iv publicInput stream st r x
  | _, _ => False

theorem OptRp.grow {st st' : RecState} (hk : KInv st) (hg : Grows st st') {e : Option Nat} {x : Option E}
    (h : OptRp π iv publicInput stream st e x) : OptRp π iv publicInput stream st' e x := by
  cases e <;> cases x <;> simp only [OptRp] at h ⊢
  exact h.grow π iv publicInput stream hk hg

/-! ## A round's message -/

/-- The bytes of a round's message: `c_0` and `c_2 …` without the eq factor, `c_1 …` with it. -/
def rpBytes (count : Nat) (hasEq : Bool) : Nat := if hasEq then 24 * (count - 1) else 24 + 24 * (count - 2)

/-- **`sumcheck_round_poly(count, claim, eq_factor)`**. -/
theorem sim_roundPoly (st : RecState) (count : Nat) {claim : Nat} {c : E} {e : Option Nat} {x : Option E}
    (hc : Rp π iv publicInput stream st claim c) (he : OptRp π iv publicInput stream st e x) :
    Sim π iv publicInput stream st (Pi1.roundPoly count claim e) (UniStatement.roundPoly (m := Id) count c x)
      (rpBytes count x.isSome) 0 (fun st' ms xs ↦ RpL π iv publicInput stream st' ms xs) := by
  refine Sim.of_good fun hg ↦ ?_
  cases e <;> cases x <;> simp only [OptRp] at he
  · -- No eq factor: `c_0` read, `c_1 = claim + Σ tail`.
    refine Sim.cast (n := 24 + (24 * (count - 2) + 0)) (ch := 0 + (0 + 0)) (by simp [rpBytes]) rfl ?_
    refine Sim.bind (sim_nextScalar π iv publicInput stream st) fun st1 k0 x0 hg1 hgr1 hk0 ↦ ?_
    refine Sim.bind (sim_nextScalars π iv publicInput stream st1 (count - 2)) fun st2 ts xs hg2 hgr2 hts ↦ ?_
    have hc2 := hc.grow π iv publicInput stream hg.inv.kinv (hgr1.trans hgr2)
    refine Sim.of_psim (PSim.bind (sum_psim st2 hg2 hts) fun st3 s hst3 hs ↦ ?_)
    refine PSim.bind (PSim.add hst3.good (hc2.pgrow hg2 hst3) hs) fun st4 c1 hst4 hc1 ↦ PSim.pure hst4.good ?_
    have hk4 := ((hk0.grow π iv publicInput stream hg1.inv.kinv hgr2).pgrow hg2 hst3).pgrow hst3.good hst4
    exact List.Forall₂.cons hk4 (List.Forall₂.cons hc1 ((hts.pgrow hg2 hst3).pgrow hst3.good hst4))
  · -- The eq factor `r`: `c_0 = claim + r Σ tail`.
    refine Sim.cast (n := 24 * (count - 1) + 0) (ch := 0 + 0) (by simp [rpBytes]) rfl ?_
    refine Sim.bind (sim_nextScalars π iv publicInput stream st (count - 1)) fun st2 ts xs hg2 hgr2 hts ↦ ?_
    have hc2 := hc.grow π iv publicInput stream hg.inv.kinv hgr2
    have hr2 := he.grow π iv publicInput stream hg.inv.kinv hgr2
    refine Sim.of_psim (PSim.bind (sum_psim st2 hg2 hts) fun st3 s hst3 hs ↦ ?_)
    refine PSim.bind (PSim.mul hst3.good (hr2.pgrow hg2 hst3) hs) fun st4 p hst4 hp ↦ ?_
    refine PSim.bind (PSim.add hst4.good ((hc2.pgrow hg2 hst3).pgrow hst3.good hst4) hp) fun st5 c0 hst5 hc0 ↦
      PSim.pure hst5.good ?_
    exact List.Forall₂.cons hc0 (((hts.pgrow hg2 hst3).pgrow hst3.good hst4).pgrow hst4.good hst5)

/-! ## The sumcheck -/

/-- The bytes of a sumcheck: each round's message. -/
def sumcheckBytes (count : Nat) (equalities : List (Option E)) : Nat :=
  (equalities.map fun e ↦ rpBytes count e.isSome).sum

theorem sum_range_getD {α : Type} (f : α → Nat) (d : α) (l : List α) :
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, Nat.add_comm]

/-- **`sumcheck_drawn(claim, count, equalities, narrow)`**: one round per equality, its message then a challenge;
the point and the final claim. -/
theorem sim_sumcheckDrawn (st : RecState) {claim : Nat} {c : E} (count : Nat) {eqs : List (Option Nat)}
    {eqsE : List (Option E)} (narrow : Bool) (hc : Rp π iv publicInput stream st claim c)
    (he : List.Forall₂ (OptRp π iv publicInput stream st) eqs eqsE) :
    Sim π iv publicInput stream st (Pi1.sumcheckDrawn claim count eqs narrow)
      (UniStatement.sumcheckDrawn (Fp π) c count eqsE narrow) (sumcheckBytes count eqsE) eqsE.length
      (fun st' a b ↦ RpL π iv publicInput stream st' a.1 b.1 ∧ Rp π iv publicInput stream st' a.2 b.2) := by
  refine Sim.of_good fun hg ↦ ?_
  have hlen := he.length_eq
  unfold Pi1.sumcheckDrawn UniStatement.sumcheckDrawn
  refine Sim.cast ?_ ?_ ((Sim.forIn_list st eqs eqsE
    (fun _ st (s : Array Nat × Nat) (t : Array E × E) ↦
      RpL π iv publicInput stream st s.1.toList t.1.toList ∧ Rp π iv publicInput stream st s.2 t.2)
    (fun i ↦ rpBytes count (eqsE.getD i none).isSome) (fun _ ↦ 1) _ _ hlen ?_ st (#[], claim) (#[], c) hg
    (Grows.refl st) ⟨List.Forall₂.nil, hc⟩).map (f := fun s ↦ (s.1.toList, s.2)) (g := fun t ↦ (t.1.toList, t.2))
      fun _ _ _ _ _ h ↦ h)
  · rw [hlen]; exact sum_range_getD (fun e ↦ rpBytes count e.isSome) none eqsE
  · rw [sum_const_range, hlen, Nat.one_mul]
  · intro i hi hj st' s t hg' hgr' ⟨hpt, hcl⟩
    have heq : OptRp π iv publicInput stream st' eqs[i] eqsE[i] :=
      (List.forall₂_iff_get.mp he).2 i hi hj |>.grow hg.inv.kinv hgr'
    refine Sim.cast (n := rpBytes count eqsE[i].isSome + (0 + 0)) (ch := 0 + (1 + 0))
      (by rw [List.getD_eq_getElem _ _ hj]; rfl) rfl ?_
    refine Sim.bind (sim_roundPoly st' count hcl heq) fun st1 ms xs hg1 hgr1 hms ↦ ?_
    refine Sim.bind (sim_sampleDrawn π iv publicInput stream st1 narrow) fun st2 z ze hg2 hgr2 ⟨hz, _⟩ ↦ ?_
    refine Sim.of_psim (PSim.bind (polyEval_psim st2 hg2 (hms.grow π iv publicInput stream hg1.inv.kinv hgr2) hz)
      fun st3 c' hst3 hc' ↦ PSim.pure hst3.good ⟨_, _, rfl, rfl, ?_, hc'⟩)
    rw [Array.toList_push, Array.toList_push]
    exact ((hpt.grow π iv publicInput stream hg'.inv.kinv (hgr1.trans hgr2)).snoc hz).pgrow hg2 hst3

/-! ## π1-rec3's paired rounds -/

/-- A pair's message: `c_0, c_1, c_2`, then `c_4 …` to the degree `4 · degree`. -/
def pairBytes (degree : Nat) : Nat := 24 * 3 + 24 * (4 * degree - 3)

theorem pairRoundPoly_eq (claim : E) (high : List E) :
    (high.zip (List.range high.length)).foldl (fun acc (c, k) ↦ if (k + 4) % 3 = 0 then acc + c else acc) claim =
      (high.zip (List.range high.length)).foldl (fun acc p ↦ if (p.2 + 4) % 3 = 0 then acc + p.1 else acc) claim := by
  congr 1

/-- **`pair_round_poly(degree, claim)`**: `c_0, c_1, c_2` and `c_4 …` read, `c_3` from the claim and the read
`c_e` with `e > 0`, `3 | e`. -/
theorem sim_pairRoundPoly (st : RecState) (degree : Nat) {claim : Nat} {c : E}
    (hc : Rp π iv publicInput stream st claim c) :
    Sim π iv publicInput stream st (Pi1.pairRoundPoly degree claim) (UniStatement.pairRoundPoly (m := Id) degree c)
      (pairBytes degree) 0 (fun st' ms xs ↦ RpL π iv publicInput stream st' ms xs) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.pairRoundPoly UniStatement.pairRoundPoly
  refine Sim.cast (n := 24 * 3 + (24 * (4 * degree - 3) + 0)) (ch := 0 + (0 + 0)) (by simp [pairBytes]) rfl ?_
  refine Sim.bind (sim_nextScalars π iv publicInput stream st 3) fun st1 lo los hg1 hgr1 hlo ↦ ?_
  refine Sim.bind (sim_nextScalars π iv publicInput stream st1 (4 * degree - 3)) fun st2 hi his hg2 hgr2 hhi ↦ ?_
  have hc2 := hc.grow π iv publicInput stream hg.inv.kinv (hgr1.trans hgr2)
  have hlen : (hi.zip (List.range hi.length)).length = (his.zip (List.range his.length)).length := by
    simp [hhi.length]
  rw [pairRoundPoly_eq]
  refine Sim.of_psim (PSim.bind (PSim.forIn_list st2 (hi.zip (List.range hi.length))
    (his.zip (List.range his.length)) (fun _ st (s : Nat) (t : E) ↦ Rp π iv publicInput stream st s t) _
    (fun acc p ↦ if (p.2 + 4) % 3 = 0 then acc + p.1 else acc) hlen ?_ st2 claim c (PStep.refl st2 hg2) hc2)
    fun st3 c3 hst3 hc3 ↦ PSim.pure hst3.good ?_)
  · intro i hi' hj st' s t hst' hI
    simp only [List.getElem_zip, List.getElem_range]
    simp only [List.length_zip, List.length_range, Nat.min_self] at hi' hj
    by_cases h3 : (i + 4) % 3 = 0
    · simp only [h3, ↓reduceIte]
      exact PSim.bind (PSim.add hst'.good hI ((hhi.get i hi' hj).pgrow hg2 hst')) fun st'' q hst'' hq ↦
        PSim.pure hst''.good ⟨q, rfl, hq⟩
    · simp only [h3, ↓reduceIte]
      exact PSim.pure hst'.good ⟨s, rfl, hI⟩
  · have hlo3 := (hlo.grow π iv publicInput stream hg1.inv.kinv hgr2).pgrow hg2 hst3
    exact List.rel_append (List.rel_append hlo3 (List.Forall₂.cons hc3 List.Forall₂.nil)) (hhi.pgrow hg2 hst3)

/-- The bytes of `sumcheck_pairs_drawn`: a message a pair, and with the variables odd a last plain round. -/
def pairsBytes (degree vars : Nat) : Nat :=
  vars / 2 * pairBytes degree + if vars % 2 = 1 then rpBytes (degree + 1) false else 0

/-- Its challenges: one a pair, and the last round's. -/
def pairsCh (vars : Nat) : Nat := vars / 2 + if vars % 2 = 1 then 1 else 0

/-- **`sumcheck_pairs_drawn(claim, degree, vars, narrow)`**: the point, the challenges, the last claim. -/
theorem sim_sumcheckPairsDrawn (st : RecState) {claim : Nat} {c : E} (degree vars : Nat) (narrow : Bool)
    (hc : Rp π iv publicInput stream st claim c) :
    Sim π iv publicInput stream st (Pi1.sumcheckPairsDrawn claim degree vars narrow)
      (UniStatement.sumcheckPairsDrawn (Fp π) c degree vars narrow) (pairsBytes degree vars) (pairsCh vars)
      (fun st' a b ↦ RpL π iv publicInput stream st' a.1 b.1 ∧ RpL π iv publicInput stream st' a.2.1 b.2.1 ∧
        Rp π iv publicInput stream st' a.2.2 b.2.2) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.sumcheckPairsDrawn UniStatement.sumcheckPairsDrawn
  refine Sim.forIn_range_congr ?_
  refine Sim.cast (n := (∑ _i ∈ Finset.range (List.range' 0 (vars / 2 - 0)).length, pairBytes degree) +
      (if vars % 2 = 1 then rpBytes (degree + 1) false else 0))
    (ch := (∑ _i ∈ Finset.range (List.range' 0 (vars / 2 - 0)).length, 1) + (if vars % 2 = 1 then 1 else 0))
    (by rw [sum_const_range, List.length_range', Nat.sub_zero, pairsBytes, Nat.mul_comm])
    (by rw [sum_const_range, List.length_range', Nat.sub_zero, Nat.one_mul, pairsCh])
    (Sim.bind (Sim.forIn_list st (List.range' 0 (vars / 2 - 0)) (List.range' 0 (vars / 2 - 0))
      (fun _ st (s : Array Nat × Array Nat × Nat) (t : Array E × Array E × E) ↦
        RpL π iv publicInput stream st s.1.toList t.1.toList ∧
          RpL π iv publicInput stream st s.2.1.toList t.2.1.toList ∧ Rp π iv publicInput stream st s.2.2 t.2.2)
      (fun _ ↦ pairBytes degree) (fun _ ↦ 1) _ _ rfl ?_ st (#[], #[], claim) (#[], #[], c) hg (Grows.refl st)
      ⟨List.Forall₂.nil, List.Forall₂.nil, hc⟩) ?_)
  · intro i _ _ st' s t hg' _ ⟨hp, hch, hcl⟩
    refine Sim.cast (n := pairBytes degree + (0 + 0)) (ch := 0 + (1 + 0)) rfl rfl ?_
    refine Sim.bind (sim_pairRoundPoly st' degree hcl) fun st1 ms xs hg1 hgr1 hms ↦ ?_
    refine Sim.bind (sim_sampleDrawn π iv publicInput stream st1 narrow) fun st2 z ze hg2 hgr2 ⟨hz, _⟩ ↦ ?_
    have hgr12 := hgr1.trans hgr2
    refine Sim.of_psim (PSim.bind (pairPoint_psim st2 hg2 hz) fun st3 pp hst3 hpp ↦ ?_)
    refine PSim.bind (polyEval_psim st3 hst3.good
      ((hms.grow π iv publicInput stream hg1.inv.kinv hgr2).pgrow hg2 hst3) (hz.pgrow hg2 hst3))
      fun st4 c' hst4 hc' ↦ PSim.pure hst4.good ⟨_, _, rfl, rfl, ?_, ?_, hc'⟩
    · rw [Array.toList_append, Array.toList_append, List.toList_toArray, List.toList_toArray]
      exact RpL.pgrow hst3.good hst4
        (List.rel_append ((hp.grow π iv publicInput stream hg'.inv.kinv hgr12).pgrow hg2 hst3) hpp)
    · rw [Array.toList_push, Array.toList_push]
      exact (((hch.grow π iv publicInput stream hg'.inv.kinv hgr12).snoc hz).pgrow hg2 hst3).pgrow hst3.good hst4
  · -- With the variables odd, a last plain round.
    intro st1 s t hg1 _ ⟨hp, hch, hcl⟩
    by_cases hodd : vars % 2 = 1
    · simp only [hodd, ↓reduceIte]
      refine Sim.cast (n := rpBytes (degree + 1) false + 0) (ch := 1 + 0) rfl rfl ?_
      have hsd := sim_sumcheckDrawn st1 (degree + 1) (eqs := [none]) (eqsE := [none]) narrow hcl
        (List.Forall₂.cons trivial List.Forall₂.nil)
      refine Sim.bind (Sim.cast (by simp [sumcheckBytes]) rfl hsd) ?_
      rintro st2 ⟨al, ae⟩ ⟨bl, be⟩ hg2 hgr2 ⟨hl2, hc2⟩
      refine Sim.pure_of_pstep (PStep.refl st2 hg2) ?_
      simp only [record_pure, Array.toList_append]
      exact ⟨List.rel_append (hp.grow π iv publicInput stream hg1.inv.kinv hgr2) hl2,
        List.rel_append (hch.grow π iv publicInput stream hg1.inv.kinv hgr2) hl2, hc2⟩
    · simp only [hodd, ↓reduceIte]
      exact Sim.pure_of_pstep (PStep.refl st1 hg1) ⟨hp, hch, hcl⟩

/-! ## `FsShape::draw` -/

/-- The challenges `FsShape::draw(count)` draws: each (`main`), or one (the others). -/
def drawCh (fs : FsShape) (count : Nat) : Nat :=
  match fs with
  | .main => count
  | .rec1 | .rec2 | .rec3 => if count = 0 then 0 else 1

theorem sim_drawRun_squares (st : RecState) (count : Nat) :
    Sim π iv publicInput stream st (if count = 0 then pure [] else do let c ← Pi1.sample; Pi1.squares c count)
      (if count = 0 then pure [] else do let c ← UniStatement.sample (Fp π); pure (UniStatement.squares c count))
      0 (if count = 0 then 0 else 1) (fun st' a b ↦ RpL π iv publicInput stream st' a b) := by
  refine Sim.of_good fun hg ↦ ?_
  by_cases h0 : count = 0
  · simp only [h0, ↓reduceIte]
    exact Sim.pure_of_pstep (PStep.refl st hg) List.Forall₂.nil
  · simp only [h0, ↓reduceIte]
    refine Sim.cast (n := 0 + 0) (ch := 1 + 0) rfl rfl ?_
    exact Sim.bind (sim_sample π iv publicInput stream st) fun st1 a x hg1 _ ⟨hx, _⟩ ↦
      Sim.of_psim (squares_psim st1 hg1 hx count)

/-- **`FsShape::draw(channel, count)`**: the run of challenges. -/
theorem sim_drawRun (st : RecState) (fs : FsShape) (count : Nat) :
    Sim π iv publicInput stream st (Pi1.drawRun fs count) (UniStatement.drawRun (Fp π) fs count) 0 (drawCh fs count)
      (fun st' a b ↦ RpL π iv publicInput stream st' a b) := by
  cases fs with
  | main => exact (sim_samples π iv publicInput stream st count).mono fun _ _ _ _ _ h ↦ h.1
  | rec1 => exact sim_drawRun_squares st count
  | rec2 => exact sim_drawRun_squares st count
  | rec3 => exact sim_drawRun_squares st count

/-! ## The row counts -/

theorem bitsValue_eK (k s w : Nat) (hk : k < 2 ^ 64) : bitsValue (eK (UInt64.ofNat k)) s w = intBits k s w := by
  have hk' : k < UInt64.size := by
    have : (2 : Nat) ^ 64 = UInt64.size := by norm_num [UInt64.size]
    exact this ▸ hk
  unfold bitsValue
  rw [show ((eK (UInt64.ofNat k)).limb 0).lane = UInt64.ofNat k from rfl, UInt64.toNat_ofNat_of_lt' hk']

/-- **The row counts** (`countBits`): each a 4-byte integer, its range and its top-bit condition required zero, its
bits `0..=r`. -/
theorem sim_countBits (st : RecState) (heights : List Nat) :
    Sim π iv publicInput stream st (Pi1.countBits heights) (UniStatement.countBits (m := Id) heights)
      (4 * heights.length) 0 (fun st' a b ↦ List.Forall₂ (RpL π iv publicInput stream st') a b) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.countBits UniStatement.countBits
  refine Sim.cast ?_ ?_ ((Sim.forIn_list st heights heights
    (fun _ st (s : Array (List Nat)) (t : Array (List E)) ↦
      List.Forall₂ (RpL π iv publicInput stream st) s.toList t.toList)
    (fun _ ↦ 4) (fun _ ↦ 0) _ _ rfl ?_ st #[] #[] hg (Grows.refl st) List.Forall₂.nil).map
      (f := fun s ↦ s.toList) (g := fun t ↦ t.toList) fun _ _ _ _ _ h ↦ h)
  · rw [sum_const_range, Nat.mul_comm]
  · simp
  · intro i hi _ st' s t hg' _ hI
    refine Sim.cast (n := 4 + 0) (ch := 0 + 0) rfl rfl ?_
    refine Sim.bind (sim_nextInteger π iv publicInput stream st' 4 (by norm_num)) fun st1 cnt k hg1 hgr1 ⟨hcnt, hk⟩ ↦ ?_
    have hk64 : k < 2 ^ 64 := lt_of_lt_of_le hk (by norm_num)
    have hb : ∀ {stx : RecState} (s w : Nat), Good stx → Grows st1 stx →
        PSim stx (Pi1.bits cnt s w) (intBits k s w) (Rp π iv publicInput stream) := fun s w hgx hgrx ↦ by
      have := PSim.bits hgx (hcnt.grow π iv publicInput stream hg1.inv.kinv hgrx) s w
      rw [bitsValue_eK k s w hk64] at this
      exact this
    refine Sim.pbind (hb (heights[i] + 1) 32 hg1 (Grows.refl st1)) fun st2 b1 hg2 hgr2 hb1 ↦ ?_
    refine Sim.cast (n := 0 + 0) (ch := 0 + 0) rfl rfl
      (Sim.bind (sim_requireZero π iv publicInput stream st2 b1 _ hb1) fun st3 _ _ hg3 hgr3 _ ↦ ?_)
    refine Sim.pbind (hb heights[i] 1 hg3 (hgr2.trans hgr3)) fun st4 hiN hg4 hgr4 hhi ↦ ?_
    refine Sim.pbind (hb 0 heights[i] hg4 ((hgr2.trans hgr3).trans hgr4)) fun st5 loN hg5 hgr5 hlo ↦ ?_
    refine Sim.pbind (PSim.mul hg5 (hhi.grow π iv publicInput stream hg4.inv.kinv hgr5) hlo)
      fun st6 mN hg6 hgr6 hm ↦ ?_
    refine Sim.cast (n := 0 + 0) (ch := 0 + 0) rfl rfl
      (Sim.bind (sim_requireZero π iv publicInput stream st6 mN _ hm) fun st7 _ _ hg7 hgr7 _ ↦ ?_)
    have hgr17 : Grows st1 st7 := hgr2.trans (hgr3.trans (hgr4.trans (hgr5.trans (hgr6.trans hgr7))))
    refine Sim.of_psim (PSim.bind (PSim.congr (forIn_range 0 (heights[i] + 1) _ _).symm rfl
      (PSim.forIn_inv st7 (List.range' 0 (heights[i] + 1 - 0))
      (fun j st (bs : Array Nat) ↦ RpL π iv publicInput stream st bs.toList
        ((List.range j).map fun b ↦ intBits k b 1)) _ ?_ st7 #[] (PStep.refl st7 hg7) List.Forall₂.nil))
      fun st8 bs hst8 hbs ↦ PSim.pure hst8.good ⟨_, _, rfl, rfl, ?_⟩)
    · intro j _ st9 bs hst9 hJ
      simp only [List.getElem_range', Nat.zero_add, Nat.one_mul]
      exact PSim.bind (hb j 1 hst9.good (hgr17.trans hst9.grows)) fun st10 x hst10 hx ↦
        PSim.pure hst10.good ⟨_, rfl, by rw [Array.toList_push, map_range_succ]; exact (hJ.pgrow hst9.good hst10).snoc hx⟩
    · rw [Array.toList_push, Array.toList_push]
      simp only [List.length_range', Nat.sub_zero] at hbs
      exact List.rel_append ((hI.imp fun _ _ h ↦ h.grow π iv publicInput stream hg'.inv.kinv
        (hgr1.trans hgr17)).imp fun _ _ h ↦ h.pgrow hg7 hst8) (List.Forall₂.cons hbs List.Forall₂.nil)

/-! ## The end of the stream -/

set_option linter.unusedSimpArgs false in
/-- **`finish`**: the stream read to its end, or `StreamNotConsumed` (the channel unchanged). -/
theorem finish_run (c : Chan) :
    ((UniStatement.finish (m := Id)).run).run c =
      if c.cursor = c.data.size then (.ok (), c) else (.error .streamNotConsumed, c) := by
  unfold UniStatement.finish
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind, get, getThe, MonadStateOf.get,
    ExceptT.lift, liftM, monadLift, MonadLift.monadLift, pure, ExceptT.pure]
  simp only [Functor.map, StateT.map, StateT.get, ExceptT.bindCont]
  simp only [pure_bind]
  rw [show (pure (Except.ok c, c) : Id (Except UniError Chan × Chan)) = (Except.ok c, c) from rfl]
  dsimp only
  by_cases h : c.cursor = c.data.size
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    rfl

end Transcript

end RecGraph.Sim
