-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Claims
import RecGraph.Sim.Transcript

/-!
# The simulation: the paired batch

`batch` at π1-rec3 (`FsShape::Rec3`: the paired and narrow rounds, no pending matrices, no bit-slice claim) against
`UniStatement.batchFs`'s `.rec3` branch: `sim_batch`. The claims enter through `CombRep` (`Claims.lean`): their value,
and their weight at the batch's point, the program's (`weight_at`, `weightAt_phc`) equal to `UniStatement`'s off the
merge hazard. The openings (commitment, `r.take vars`, value) are represented (`RpOpening`), and the terminal zero is
pushed (`sim_requireZero`).

* **Recorded shapes** (`Out p Q`: the program's recorded output satisfies `Q` from every state): `out_bind`,
  `out_forIn`; the sumchecks' points have their variables' length (`sumcheckPairsDrawn_out`), so the batch's point
  reaches every block of every stack.
* `Sim.withRecord`: a part's outputs are its recording's.
-/

-- `Sim.withRecord` is a rule of the judgment `RecGraph.Sim.Sim`, in the framework's namespace.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## Recorded shapes -/

/-- **A program's recorded output satisfies `Q`**, from every state. -/
def Out {α : Type} (p : Prog α) (Q : α → Prop) : Prop := ∀ st, Q (p.record st).1

theorem out_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Out (pure a) Q := fun _ ↦ h

theorem out_any {α : Type} (p : Prog α) : Out p fun _ ↦ True := fun _ ↦ trivial

theorem out_bind {α β : Type} {p : Prog α} {k : α → Prog β} {Q : α → Prop} {R : β → Prop} (hp : Out p Q)
    (hk : ∀ a, Q a → Out (k a) R) : Out (p >>= k) R := fun st ↦ by
  rw [record_bind]
  exact hk _ (hp st) _

theorem out_forIn {α β : Type} (f : α → β → Prog (ForInStep β)) (I : ℕ → β → Prop)
    (hf : ∀ k a b, I k b → Out (f a b) fun r ↦ ∃ b', r = .yield b' ∧ I (k + 1) b') :
    ∀ (l : List α) (k : ℕ) (init : β), I k init → Out (forIn l init f) (I (k + l.length)) := by
  intro l
  induction l with
  | nil => intro k init h; exact out_pure h
  | cons a l ih =>
    intro k init h
    rw [List.forIn_cons]
    refine out_bind (hf k a init h) fun r ⟨b', hr, hb'⟩ ↦ ?_
    subst hr
    have e : k + (a :: l).length = k + 1 + l.length := by simp; omega
    rw [e]
    exact ih (k + 1) b' hb'

theorem pairPoint_out (z : Nat) : Out (Pi1.pairPoint z) fun l ↦ l.length = 2 := by
  unfold Pi1.pairPoint
  exact out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦
    out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦ out_pure rfl

theorem sumcheckDrawn_out (claim count : Nat) (eqs : List (Option Nat)) (narrow : Bool) :
    Out (Pi1.sumcheckDrawn claim count eqs narrow) fun r ↦ r.1.length = eqs.length := by
  unfold Pi1.sumcheckDrawn
  refine out_bind (out_forIn _ (fun k (b : Array Nat × Nat) ↦ b.1.size = k) ?_ eqs 0 (#[], claim) rfl)
    fun r hr ↦ out_pure ?_
  · intro k _ b hb
    exact out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦
      out_pure ⟨_, rfl, by simp [hb]⟩
  · simpa using hr

/-- **The paired sumcheck's point has its variables' length.** -/
theorem sumcheckPairsDrawn_out (claim degree vars : Nat) (narrow : Bool) :
    Out (Pi1.sumcheckPairsDrawn claim degree vars narrow) fun r ↦ r.1.length = vars := by
  unfold Pi1.sumcheckPairsDrawn
  dsimp only
  rw [forIn_range]
  refine out_bind (out_forIn _ (fun k (b : Array Nat × Array Nat × Nat) ↦ b.1.size = 2 * k) ?_
    (List.range' 0 (vars / 2 - 0)) 0 (#[], #[], claim) rfl) fun r hr ↦ ?_
  · intro k _ b hb
    refine out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦ out_bind (pairPoint_out _) fun pp hpp ↦
      out_bind (out_any _) fun _ _ ↦ out_pure ⟨_, rfl, ?_⟩
    simp only [Array.size_append, List.size_toArray, hb, hpp]
    ring
  · simp only [List.length_range', Nat.sub_zero, zero_add] at hr
    by_cases hodd : vars % 2 = 1
    · simp only [hodd, ↓reduceIte]
      refine out_bind (sumcheckDrawn_out _ _ _ _) fun le hle ↦ ?_
      obtain ⟨last, end_⟩ := le
      refine out_pure ?_
      simp only [List.length_cons, List.length_nil] at hle
      simp only [Array.length_toList, Array.size_append, List.size_toArray, hr, hle]
      omega
    · simp only [hodd, ↓reduceIte]
      refine out_pure ?_
      simp only [Array.length_toList, hr]
      omega

/-! ## The batch -/

/-- A commitment's layout, as the batch looks it up. -/
def layoutAt (layouts : List (Commitment × StackLayout)) (c : Commitment) : StackLayout :=
  ((layouts.find? (·.1 == c)).map (·.2)).getD default

/-- The batch's variables: the longest stack's. -/
def bvars (layouts : List (Commitment × StackLayout)) : ℕ := (layouts.map (·.2.vars)).foldl max 0

theorem foldl_max_le (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := ih (max a x)
    refine ⟨(le_max_left a x).trans h1, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (le_max_right a y).trans h1
    · exact h2 y hy

theorem layoutAt_vars_le (layouts : List (Commitment × StackLayout)) (c : Commitment) :
    (layoutAt layouts c).vars ≤ bvars layouts := by
  unfold layoutAt bvars
  cases h : layouts.find? (·.1 == c) with
  | none => exact Nat.zero_le _
  | some x =>
    exact (foldl_max_le _ 0).2 _ (List.mem_map.mpr ⟨x, List.mem_of_find?_eq_some h, rfl⟩)

theorem phc_psim {st : RecState} {α β : Type} {p : Prog α} {b : β} {R : RecState → α → β → Prop}
    (h : PHc st p fun a st' ↦ R st' a b) : PSim st p b R := h

section Batch

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **A part's outputs are its recording's.** -/
theorem Sim.withRecord {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p u n ch fun st' a b ↦ R st' a b ∧ a = (p.record st).1 := by
  intro c hc hle
  obtain ⟨hs, hf⟩ := h c hc hle
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b, c', hu, hc', hcur, hch, hg, hR⟩ := hs hr
  exact ⟨b, c', hu, hc', hcur, hch, hg, hR, rfl⟩

/-- **An opening, represented**: the same commitment; a point claim (no bit-slice claim), its point and value
represented. -/
def RpOpening (st : RecState) (x : Commitment × List Nat × Nat) (y : Commitment × Opening) : Prop :=
  x.1 = y.1 ∧ ∃ pt v, y.2 = .point pt v none ∧ RpL π iv publicInput stream st x.2.1 pt ∧
    Rp π iv publicInput stream st x.2.2 v

theorem RpOpening.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {x : Commitment × List Nat × Nat}
    {y : Commitment × Opening} (h : RpOpening π iv publicInput stream st x y) :
    RpOpening π iv publicInput stream st' x y := by
  obtain ⟨h1, pt, v, h2, h3, h4⟩ := h
  exact ⟨h1, pt, v, h2, RpL.pgrow hg hs h3, Rp.pgrow hg hs h4⟩

theorem RpOpening.grow {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {x : Commitment × List Nat × Nat}
    {y : Commitment × Opening} (h : RpOpening π iv publicInput stream st x y) :
    RpOpening π iv publicInput stream st' x y := by
  obtain ⟨h1, pt, v, h2, h3, h4⟩ := h
  exact ⟨h1, pt, v, h2, RpL.grow π iv publicInput stream hk hgr h3, Rp.grow π iv publicInput stream hk hgr h4⟩

/-- **The paired batch** (`batch` at π1-rec3) against `batchFs`'s `.rec3` branch (no pending matrices, no bit-slice
claim): the combined claims related commitment by commitment (`CombRep` at the commitment's layout), every block of
every layout within its stack, the ring map represented. It reads the paired sumcheck's bytes and the claims' values,
draws `λ` and the sumcheck's challenges, pushes the terminal zero; its openings are `UniStatement`'s point claims
(`RpOpening`), and no matrices' claim is left. -/
theorem sim_batch (st : RecState) {combS : List (Commitment × CombinedS)} {comb : List (Commitment × Combined)}
    (layouts : List (Commitment × StackLayout))
    (hc : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRep π iv publicInput stream st (layoutAt layouts a.1) a.2 b.2)
      combS comb)
    (hV : ∀ c col, ∀ b ∈ (layoutAt layouts c).limbs col, b.2.1 ≤ (layoutAt layouts c).vars)
    {mapS : List Nat} {map : List E} (hm : RpL π iv publicInput stream st mapS map) (h0 : 0 < st.nodes.size) :
    Sim π iv publicInput stream st (Pi1.batch combS layouts (some mapS))
      (batchFs (Fp π) .rec3 comb layouts none (some map) none)
      (pairsBytes 2 (bvars layouts) + 24 * comb.length) (1 + pairsCh (bvars layouts))
      (fun st' a b ↦ b.2 = none ∧ List.Forall₂ (RpOpening π iv publicInput stream st') a b.1) := by
  refine Sim.of_good fun hg ↦ ?_
  have hk := hg.inv.kinv
  have hlen := List.Forall₂.length_eq hc
  have hz0 : Rp π iv publicInput stream st 0 (val π iv publicInput stream st 0) := rp_val π iv publicInput stream h0
  unfold Pi1.batch batchFs
  dsimp only
  refine Sim.cast (n := 0 + (pairsBytes 2 (bvars layouts) + (24 * comb.length + (0 + 0))))
    (ch := 1 + (pairsCh (bvars layouts) + (0 + (0 + 0)))) (by omega) (by omega) ?_
  refine Sim.bind (sim_sample π iv publicInput stream st) fun st1 lam lamE hg1 hgr1 ⟨hlam, _⟩ ↦ ?_
  refine Sim.pbind (phc_psim (b := (0 : E)) (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
    (phc_zero π iv publicInput stream hg1)) fun st2 t0 hg2 hgr2 ht0 ↦ ?_
  refine Sim.pbind (phc_psim (b := (1 : E)) (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
    (phc_one π iv publicInput stream hg2)) fun st3 s0 hg3 hgr3 hs0 ↦ ?_
  have hgr03 := hgr1.trans (hgr2.trans hgr3)
  have hlam3 := Rp.grow π iv publicInput stream hg1.inv.kinv (hgr2.trans hgr3) hlam
  have hc3 : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRep π iv publicInput stream st3 (layoutAt layouts a.1) a.2 b.2)
      combS comb :=
    hc.imp fun _ _ h ↦ ⟨h.1, CombRep.grow π iv publicInput stream hk hgr03 h.2⟩
  -- `λ`'s combination of the claims' values: the sumcheck's target.
  refine Sim.pbind (phc_psim (b := comb.foldl (fun acc x ↦ (acc.1 + acc.2 * x.2.value, acc.2 * lamE)) (0, 1))
    (R := fun st' (a : Nat × Nat) (b : E × E) ↦ Rp π iv publicInput stream st' a.1 b.1 ∧
      Rp π iv publicInput stream st' a.2 b.2)
    (phc_forIn (fun a a' s ↦ (a.1 = a'.1 ∧ CombRep π iv publicInput stream s (layoutAt layouts a.1) a.2 a'.2) ∧
        Rp π iv publicInput stream s lam lamE)
      (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, CombRep.grow π iv publicInput stream hg.inv.kinv hs.grows h.1.2⟩,
        Rp.pgrow hg hs h.2⟩) _
      (fun acc (x : Commitment × Combined) ↦ (acc.1 + acc.2 * x.2.value, acc.2 * lamE))
      (fun (b : Nat × Nat) (acc : E × E) s ↦ Rp π iv publicInput stream s b.1 acc.1 ∧
        Rp π iv publicInput stream s b.2 acc.2) ?_ combS comb st3 (t0, s0) (0, 1) hg3
      (hc3.imp fun _ _ h ↦ ⟨h, hlam3⟩) ⟨Rp.grow π iv publicInput stream hg2.inv.kinv hgr3 ht0, hs0⟩))
    fun st4 ts hg4 hgr4 hts ↦ ?_
  · rintro ⟨com, claim⟩ ⟨com', cb⟩ ⟨t, s⟩ ⟨tE, sE⟩ st' hg' ⟨⟨-, hcr⟩, hl⟩ ⟨ht, hs⟩
    dsimp only at ht hs ⊢
    exact phc_bind (phc_mul π iv publicInput stream hg' hs hcr.value) fun sv st1 hs1 hsv ↦
      phc_bind (phc_add π iv publicInput stream hs1.good (Rp.pgrow hg' hs1 ht) hsv) fun t' st2 hs2 ht' ↦
        phc_bind (phc_mul π iv publicInput stream hs2.good (Rp.pgrow hs1.good hs2 (Rp.pgrow hg' hs1 hs))
          (Rp.pgrow hs1.good hs2 (Rp.pgrow hg' hs1 hl))) fun s' st3 hs3 hs' ↦
          phc_pure _ hs3.good ⟨_, rfl, Rp.pgrow hs2.good hs3 ht', hs'⟩
  -- The paired sumcheck.
  have hgr04 := hgr03.trans hgr4
  refine Sim.bind (Sim.withRecord π iv publicInput stream (sim_sumcheckPairsDrawn st4 2 (bvars layouts) true hts.1))
    fun st5 sc scE hg5 hgr5 ⟨⟨hr, _, hlast⟩, hrec⟩ ↦ ?_
  have hrlen : sc.1.length = bvars layouts := by
    have := sumcheckPairsDrawn_out ts.1 2 (List.foldl max 0 (List.map (fun x ↦ x.2.vars) layouts)) true st4
    rw [← hrec] at this
    exact this
  obtain ⟨rS, chS, lastS⟩ := sc
  obtain ⟨rE, chE, lastE⟩ := scE
  dsimp only at hr hlast hrlen ⊢
  have hrElen : rE.length = bvars layouts := (RpL.lengthC π iv publicInput stream hr).symm.trans hrlen
  rw [pure_bind, show combS.length = comb.length from hlen]
  have hgr05 := hgr04.trans hgr5
  refine Sim.bind (sim_nextScalars π iv publicInput stream st5 comb.length) fun st6 vS vE hg6 hgr6 hv ↦ ?_
  rw [pure_bind]
  have hgr56 := hgr6
  have hgr06 := hgr05.trans hgr6
  have hr6 := RpL.grow π iv publicInput stream hg5.inv.kinv hgr6 hr
  have hlast6 := Rp.grow π iv publicInput stream hg5.inv.kinv hgr6 hlast
  have hlam6 := Rp.grow π iv publicInput stream hg1.inv.kinv ((hgr2.trans hgr3).trans (hgr4.trans (hgr5.trans hgr6))) hlam
  have hm6 := RpL.grow π iv publicInput stream hk hgr06 hm
  have hz06 := Rp.grow π iv publicInput stream hk hgr06 hz0
  have hc6 : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRep π iv publicInput stream st6 (layoutAt layouts a.1) a.2 b.2)
      combS comb :=
    hc.imp fun _ _ h ↦ ⟨h.1, CombRep.grow π iv publicInput stream hk hgr06 h.2⟩
  have hzip := forall₂_zipC hc6 hv
  -- The weights, the extensions, the openings.
  refine Sim.pbind (phc_psim (b := (0 : E)) (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
    (phc_zero π iv publicInput stream hg6)) fun st7 m0 hg7 hgr7 hm0 ↦ ?_
  refine Sim.pbind (phc_psim (b := (1 : E)) (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
    (phc_one π iv publicInput stream hg7)) fun st8 n0 hg8 hgr8 hn0 ↦ ?_
  have hgr68 := hgr7.trans hgr8
  have hctx8 : RpL π iv publicInput stream st8 rS rE ∧ Rp π iv publicInput stream st8 lam lamE ∧
      RpL π iv publicInput stream st8 mapS map ∧
      Rp π iv publicInput stream st8 0 (val π iv publicInput stream st 0) :=
    ⟨RpL.grow π iv publicInput stream hg6.inv.kinv hgr68 hr6, Rp.grow π iv publicInput stream hg6.inv.kinv hgr68 hlam6,
      RpL.grow π iv publicInput stream hg6.inv.kinv hgr68 hm6, Rp.grow π iv publicInput stream hg6.inv.kinv hgr68 hz06⟩
  have hzip8 := hzip.imp fun _ _ h ↦ (show ((_ ∧ CombRep π iv publicInput stream st8 _ _ _) ∧ _) ∧ _ from
    ⟨⟨⟨h.1.1, CombRep.grow π iv publicInput stream hg6.inv.kinv hgr68 h.1.2⟩,
      Rp.grow π iv publicInput stream hg6.inv.kinv hgr68 h.2⟩, hctx8⟩)
  refine Sim.pbind (phc_psim
    (b := (comb.zip vE).foldl (fun (acc : E × E × Array (Commitment × Opening) × Option Combined)
      (x : (Commitment × Combined) × E) ↦
      (acc.1 + acc.2.1 * weightAt x.1.2 (layoutAt layouts x.1.1) rE (some map) *
          List.foldl (fun e j ↦ e * (1 + rE.getD j 0)) 1
            (List.range' (layoutAt layouts x.1.1).vars (bvars layouts - (layoutAt layouts x.1.1).vars)) * x.2,
        acc.2.1 * lamE,
        acc.2.2.1.push (x.1.1, Opening.point (List.take (layoutAt layouts x.1.1).vars rE) x.2
          (if (x.1.1 == Commitment.c1) = true then (acc.2.2.2, none) else (none, acc.2.2.2)).1),
        (if (x.1.1 == Commitment.c1) = true then (acc.2.2.2, none) else (none, acc.2.2.2)).2)) (0, 1, #[], none))
    (R := fun st' (a : Nat × Nat × Array (Commitment × List Nat × Nat))
      (b : E × E × Array (Commitment × Opening) × Option Combined) ↦
      Rp π iv publicInput stream st' a.1 b.1 ∧ Rp π iv publicInput stream st' a.2.1 b.2.1 ∧
        List.Forall₂ (RpOpening π iv publicInput stream st') a.2.2.toList b.2.2.1.toList ∧ b.2.2.2 = none)
    (phc_forIn (fun a a' s ↦ ((a.1.1 = a'.1.1 ∧
          CombRep π iv publicInput stream s (layoutAt layouts a.1.1) a.1.2 a'.1.2) ∧
        Rp π iv publicInput stream s a.2 a'.2) ∧
        (RpL π iv publicInput stream s rS rE ∧ Rp π iv publicInput stream s lam lamE ∧
          RpL π iv publicInput stream s mapS map ∧ Rp π iv publicInput stream s 0 (val π iv publicInput stream st 0)))
      (fun _ _ _ _ hg hs h ↦ ⟨⟨⟨h.1.1.1, CombRep.grow π iv publicInput stream hg.inv.kinv hs.grows h.1.1.2⟩,
        Rp.pgrow hg hs h.1.2⟩, RpL.pgrow hg hs h.2.1, Rp.pgrow hg hs h.2.2.1, RpL.pgrow hg hs h.2.2.2.1,
          Rp.pgrow hg hs h.2.2.2.2⟩) _ _
      (fun (b : Nat × Nat × Array (Commitment × List Nat × Nat))
        (acc : E × E × Array (Commitment × Opening) × Option Combined) s ↦
        Rp π iv publicInput stream s b.1 acc.1 ∧ Rp π iv publicInput stream s b.2.1 acc.2.1 ∧
          List.Forall₂ (RpOpening π iv publicInput stream s) b.2.2.toList acc.2.2.1.toList ∧ acc.2.2.2 = none)
      ?_ (combS.zip vS) (comb.zip vE) st8 (m0, n0, #[]) (0, 1, #[], none) hg8 hzip8
      ⟨Rp.grow π iv publicInput stream hg7.inv.kinv hgr8 hm0, hn0, List.Forall₂.nil, rfl⟩))
    fun st9 res hg9 hgr9 hres ↦ ?_
  · rintro ⟨⟨com, claim⟩, value⟩ ⟨⟨com', cb⟩, x⟩ ⟨sm, sc2, ops⟩ ⟨smE, scE2, opsE, bsE⟩ s hg
      ⟨⟨⟨hcom, hcr⟩, hval⟩, hrS, hlamS, hmS, hz0S⟩ ⟨hsm, hsc, hops, hbs⟩
    dsimp only at hcom hcr hval hsm hsc hops hbs ⊢
    subst hbs
    rw [← hcom]
    have hbs' : (if (com == Commitment.c1) = true then ((none : Option Combined), (none : Option Combined))
        else (none, none)) = (none, none) := by split <;> rfl
    rw [hbs']
    have hLv := layoutAt_vars_le layouts com
    have hrl : ∀ col, ∀ b ∈ (layoutAt layouts com).limbs col, b.2.1 ≤ rE.length := fun col b hb ↦
      (hV com col b hb).trans (hLv.trans hrElen.symm.le)
    refine phc_bind (weightAt_phc π iv publicInput stream hg hcr.held (layoutAt layouts com) hrS hmS hz0S)
      fun w s1 hs1 hw ↦ ?_
    rw [hcr.weight rE map _ hrl] at hw
    refine phc_bind (phc_one π iv publicInput stream hs1.good) fun e0 s2 hs2 he0 ↦ ?_
    rw [forIn_range]
    have hs12 := hs1.trans hs2
    refine phc_bind (phc_forIn_same (fun j ↦ j < bvars layouts)
      (fun s' ↦ RpL π iv publicInput stream s' rS rE) (fun _ _ hg hs h ↦ RpL.pgrow hg hs h) _
      (fun e j ↦ e * (1 + rE.getD j 0)) (fun (b : Nat) (c : E) s ↦ Rp π iv publicInput stream s b c) ?_ _ ?_ s2 e0 1
      hs2.good (RpL.pgrow hg hs12 hrS) he0) fun ext s3 hs3 hext ↦ ?_
    · intro j b c s' hg' hj hr' hbc
      have hrj := RpL.getDC π iv publicInput stream hr' (k := j) (by rw [RpL.lengthC π iv publicInput stream hr', hrElen]; exact hj)
      exact phc_bind (phc_one π iv publicInput stream hg') fun o s4 hs4 ho ↦
        phc_bind (phc_add π iv publicInput stream hs4.good ho (Rp.pgrow hg' hs4 hrj)) fun t s5 hs5 ht ↦
          phc_bind (phc_mul π iv publicInput stream hs5.good (Rp.pgrow hs4.good hs5 (Rp.pgrow hg' hs4 hbc)) ht)
            fun _ s6 hs6 h ↦ phc_pure _ hs6.good ⟨_, rfl, h⟩
    · intro j hj
      rw [List.mem_range'_1] at hj
      have hLv' := layoutAt_vars_le layouts com
      unfold layoutAt bvars at hLv'
      unfold bvars
      omega
    have hs13 := hs12.trans hs3
    refine phc_bind (phc_mul π iv publicInput stream hs3.good (Rp.pgrow hg hs13 hsc)
      (Rp.pgrow hs2.good hs3 (Rp.pgrow hs1.good hs2 hw))) fun sw s4 hs4 hsw ↦ ?_
    refine phc_bind (phc_mul π iv publicInput stream hs4.good hsw (Rp.pgrow hs3.good hs4 hext)) fun swe s5 hs5 hswe ↦ ?_
    have hs15 := hs13.trans (hs4.trans hs5)
    refine phc_bind (phc_mul π iv publicInput stream hs5.good hswe (Rp.pgrow hg hs15 hval)) fun swev s6 hs6 hswev ↦ ?_
    have hs16 := hs15.trans hs6
    refine phc_bind (phc_add π iv publicInput stream hs6.good (Rp.pgrow hg hs16 hsm) hswev) fun sm' s7 hs7 hsm' ↦ ?_
    have hs17 := hs16.trans hs7
    refine phc_bind (phc_mul π iv publicInput stream hs7.good (Rp.pgrow hg hs17 hsc) (Rp.pgrow hg hs17 hlamS))
      fun sc' s8 hs8 hsc' ↦ phc_pure _ hs8.good ⟨_, rfl, Rp.pgrow hs7.good hs8 hsm', hsc', ?_, rfl⟩
    have hs18 := hs17.trans hs8
    rw [Array.toList_push, Array.toList_push]
    exact List.rel_append ((hops.imp fun _ _ h ↦ RpOpening.pgrow π iv publicInput stream hg hs18 h))
      (List.Forall₂.cons ⟨rfl, _, _, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hg hs18 hrS) _,
        Rp.pgrow hg hs18 hval⟩ List.Forall₂.nil)
  · obtain ⟨hsum, -, hops, -⟩ := hres
    have hlast9 := Rp.grow π iv publicInput stream hg6.inv.kinv (hgr68.trans hgr9) hlast6
    refine Sim.pbind (phc_psim (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
      (phc_add π iv publicInput stream hg9 hsum hlast9)) fun st10 d hg10 hgr10 hd ↦ ?_
    refine Sim.bind (sim_requireZero π iv publicInput stream st10 d _ hd) fun st11 _ _ hg11 hgr11 _ ↦ ?_
    exact Sim.pure_of_pstep (PStep.refl st11 hg11) ⟨rfl, hops.imp fun _ _ h ↦
      RpOpening.grow π iv publicInput stream hg9.inv.kinv (hgr10.trans hgr11) h⟩

end Batch

/-! ## The tail of `reduce`: one claim per commitment, then the batch -/

/-- **`reduce`'s tail** (after `ρ`): one combined claim per commitment that has relations, then the batch at the
layouts of `reference` with `C2`'s columns `c2`. -/
def tailS (relsS : List RelationS) (rhoS : Sym) (c2 : List (Column × ℕ × Bool)) (mapS : List Sym) :
    Prog (List (Commitment × List Sym × Sym)) := do
  let mut combined : Array (Commitment × CombinedS) := #[]
  for c in commitments do
    if let some claim ← combine relsS c rhoS then
      combined := combined.push (c, claim)
  let _ ← one
  batch combined.toList (layouts reference c2) (some mapS)

/-- A layout's blocks lie inside its stack: each block's variables at most the stack's. -/
theorem limbs_vars_le {L : StackLayout} (hal : UniSound.Ids.LayoutAligned L) (col : Column) :
    ∀ b ∈ L.limbs col, b.2.1 ≤ L.vars := by
  intro b hb
  unfold StackLayout.limbs at hb
  obtain ⟨blk, hblk, he⟩ := List.mem_filterMap.mp hb
  obtain ⟨c, l, v, o⟩ := blk
  by_cases hc : c = col
  · simp only [hc, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at he
    subst he
    have h := (hal _ hblk).2
    have h2 : 2 ^ v ≤ 2 ^ L.vars := le_trans (Nat.le_add_left _ _) h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  · simp [hc] at he

/-- The layouts' blocks lie inside their stacks, at every shape and `C2` column list. -/
theorem layouts_vars_le (shape : Shape) (c2 : List (Column × ℕ × Bool)) (c : Commitment) (col : Column) :
    ∀ b ∈ (layoutAt (layouts shape c2) c).limbs col, b.2.1 ≤ (layoutAt (layouts shape c2) c).vars := by
  cases c
  · exact limbs_vars_le (UniSound.Ids.layoutAligned_new _) col
  · exact limbs_vars_le (UniSound.Ids.layoutAligned_new _) col
  · exact limbs_vars_le (UniSound.Ids.layoutAligned_new _) col

theorem foldl_filterMapC {α β : Type} (f : α → Option β) (l : List α) (a0 : List β) :
    l.foldl (fun acc x ↦ acc ++ (f x).toList) a0 = a0 ++ l.filterMap f := by
  induction l generalizing a0 with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.filterMap_cons]
    cases f x <;> simp

theorem combine_nil (c : Commitment) (ρ : E) : combine [] c ρ = none := rfl

section Tail

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **The terms' kinds and the hazard's absence**, for every commitment, at the layouts of `reference` with `C2`'s
columns `c2`: what `combine_weight` asks of the relations. -/
def TailOK (rels : List Relation) (c2 : List (Column × ℕ × Bool)) : Prop :=
  ∀ c ∈ commitments, LayoutOK (layoutAt (layouts reference c2) c) ∧
    (∀ r ∈ UniSound.Ids.mine rels c, ∀ tm ∈ r.terms,
      TermKind (layoutAt (layouts reference c2) c) tm.column tm.point tm.twist) ∧
    (∀ r ∈ UniSound.Ids.mine rels c, ∀ tm ∈ r.terms, (∃ j, tm.column = .qflockSlot j) →
      ∀ r' ∈ UniSound.Ids.mine rels c, ∀ tm' ∈ r'.terms, tm.point.length < tm'.point.length →
        tm'.point.take tm.point.length ≠ tm.point)

/-- The openings, as `Compose` states them. -/
def OpeningsR (st : RecState) (a : List (Commitment × List Nat × Nat)) (b : List (Commitment × Opening)) : Prop :=
  List.Forall₂ (fun x y ↦ ∃ ptE vE, y = (x.1, .point ptE vE none) ∧ RpL π iv publicInput stream st x.2.1 ptE ∧
    Rp π iv publicInput stream st x.2.2 vE) a b

/-- The tail's bytes: the paired sumcheck's and the claims' values. -/
def tailBytes (rels : List Relation) (rho : E) (c2 : List (Column × ℕ × Bool)) : ℕ :=
  pairsBytes 2 (bvars (layouts reference c2)) +
    24 * (commitments.filterMap fun x ↦ (combine rels x rho).map ((x, ·))).length

/-- **`reduce`'s tail, off the merge hazard**: one claim per commitment (`combine_weight`), then the batch
(`sim_batch`), against `UniStatement`'s `filterMap` of `combine` and `batchFs`'s `.rec3` branch. -/
theorem sim_tail (st : RecState) {relsS : List RelationS} {rels : List Relation}
    (hr : RpRels π iv publicInput stream st relsS rels) {rhoS : Nat} {ρ : E}
    (hrho : Rp π iv publicInput stream st rhoS ρ) (c2 : List (Column × ℕ × Bool)) {mapS : List Nat} {map : List E}
    (hm : RpL π iv publicInput stream st mapS map) (h0 : 0 < st.nodes.size) (hok : TailOK rels c2) :
    Sim π iv publicInput stream st (tailS relsS rhoS c2 mapS)
      (batchFs (Fp π) .rec3 (commitments.filterMap fun x ↦ (combine rels x ρ).map ((x, ·))) (layouts reference c2)
        (combine [] .c1 1) (some map) none)
      (tailBytes rels ρ c2) (1 + pairsCh (bvars (layouts reference c2)))
      (fun st' a b ↦ OpeningsR π iv publicInput stream st' a b.1 ∧ b.2 = none) := by
  refine Sim.of_good fun hg ↦ ?_
  rw [combine_nil]
  unfold tailS
  refine Sim.pbind (phc_psim (b := commitments.filterMap fun x ↦ (combine rels x ρ).map ((x, ·)))
    (R := fun st' (a : Array (Commitment × CombinedS)) (b : List (Commitment × Combined)) ↦
      List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRep π iv publicInput stream st'
        (layoutAt (layouts reference c2) a.1) a.2 b.2) a.toList b) ?_) fun st1 cS hg1 hgr1 hcS ↦ ?_
  · rw [← List.nil_append (commitments.filterMap _), ← foldl_filterMapC]
    refine phc_forIn_same (fun c ↦ c ∈ commitments)
      (fun s ↦ RpRels π iv publicInput stream s relsS rels ∧ Rp π iv publicInput stream s rhoS ρ)
      (fun _ _ hg hs h ↦ ⟨RpRels.pgrow π iv publicInput stream hg hs h.1, Rp.pgrow hg hs h.2⟩) _ _
      (fun (b : Array (Commitment × CombinedS)) (acc : List (Commitment × Combined)) s ↦
        List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRep π iv publicInput stream s
          (layoutAt (layouts reference c2) a.1) a.2 b.2) b.toList acc) ?_ commitments (fun _ h ↦ h) st #[] [] hg
      ⟨hr, hrho⟩ List.Forall₂.nil
    intro c b acc s hg' hc ⟨hr', hrho'⟩ hb
    obtain ⟨hL, hK, hself⟩ := hok c hc
    refine phc_bind (combine_weight π iv publicInput stream hg' hr' c hrho' _ hL hK hself) fun out s' hs hout ↦ ?_
    have hb' := hb.imp fun _ _ h ↦ ⟨h.1, CombRep.grow π iv publicInput stream hg'.inv.kinv hs.grows h.2⟩
    cases hcb : combine rels c ρ with
    | none =>
      rw [hcb] at hout
      cases out with
      | none => exact phc_pure _ hs.good ⟨_, rfl, by simpa using hb'⟩
      | some _ => exact hout.elim
    | some cb =>
      rw [hcb] at hout
      cases out with
      | none => exact hout.elim
      | some cS =>
        refine phc_pure _ hs.good ⟨_, rfl, ?_⟩
        rw [Array.toList_push]
        exact List.rel_append hb' (List.Forall₂.cons ⟨rfl, hout⟩ List.Forall₂.nil)
  · refine Sim.pbind (phc_psim (b := ()) (R := fun _ _ _ ↦ True) (phc_conseq (phc_one π iv publicInput stream hg1)
      fun _ _ _ _ ↦ trivial)) fun st2 _ hg2 hgr2 _ ↦ ?_
    have hgr02 := hgr1.trans hgr2
    have hc2 := hcS.imp fun _ _ h ↦ ⟨h.1, CombRep.grow π iv publicInput stream hg1.inv.kinv hgr2 h.2⟩
    refine Sim.mono (Sim.cast ?_ rfl (sim_batch π iv publicInput stream st2 (layouts reference c2) hc2
      (layouts_vars_le reference c2) (RpL.grow π iv publicInput stream hg.inv.kinv hgr02 hm)
      (lt_of_lt_of_le h0 (Grows.size_le hgr02)))) fun st' a b _ _ ⟨hb2, hops⟩ ↦ ⟨?_, hb2⟩
    · rfl
    · clear hb2
      induction hops with
      | nil => exact List.Forall₂.nil
      | cons h _ ih =>
        obtain ⟨h1, pt, v, h2, h3, h4⟩ := h
        refine List.Forall₂.cons ⟨pt, v, ?_, h3, h4⟩ ih
        exact Prod.ext h1.symm h2

end Tail

end RecGraph.Sim
