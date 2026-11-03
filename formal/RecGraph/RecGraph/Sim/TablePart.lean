-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. A table's reads and the sent columns' pattern are
-- `formal/UniSound`'s (`CodeTables.lean`: `tableReads`, `SamePat`, `sentPat`, `sum_flushReads`).
import RecGraph.Sim.Relations
import UniSound.CodeTables
import UniSound.Ids.Facts

/-!
# The simulation: a table's part

* `tablePart_sim`: the program's `tablePart` simulates `UniStatement.tablePart`. It reads `24 · tableReads t` bytes
  (`UniSound.tableReads`: the sent columns, then each flush's sent fingerprints; which fingerprints are sent depends on
  which columns are, not on their values: `UniSound.sum_flushReads`). Its part and its relations are represented, and
  each relation's terms are in the table's columns, at `w[..lh]`, untwisted (`TabShape`).
* `tableSpec`: `TableSpec partR tableShape tableBytes`, `Compose`'s interface.
-/

set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- **A table's term**: in one of its columns, at `w[..lh]`, untwisted. -/
def TabTerm (t : Table) (lh : Nat) (wE : List E) (tm : Term) : Prop :=
  (∃ i, tm.column = .table t.opcode i) ∧ tm.point = wE.take lh ∧ tm.twist = 0

/-- **A table's relations, their shape**: every term a table's term. -/
def TabShape (t : Table) (lh : Nat) (wE : List E) (rels : List Relation) : Prop :=
  ∀ r ∈ rels, ∀ tm ∈ r.terms, TabTerm t lh wE tm

theorem TabShape.push {t : Table} {lh : Nat} {wE : List E} {a : Array Relation} {r : Relation}
    (h : TabShape t lh wE a.toList) (hr : ∀ tm ∈ r.terms, TabTerm t lh wE tm) : TabShape t lh wE (a.push r).toList := by
  intro r' hr' tm htm
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr'
  rcases hr' with hr' | rfl
  · exact h r' hr' tm htm
  · exact hr tm htm

theorem tabTerm_mapC (t : Table) (lh : Nat) (wE : List E) (l : List (ℕ × E)) :
    ∀ tm ∈ l.map (fun x ↦ term (Column.table t.opcode x.1) (List.take lh wE) x.2), TabTerm t lh wE tm := by
  intro tm htm
  rw [List.mem_map] at htm
  obtain ⟨x, _, rfl⟩ := htm
  exact ⟨⟨x.1, rfl⟩, rfl, rfl⟩

theorem sum_map_mulC {α : Type} (c : Nat) (f : α → Nat) :
    ∀ l : List α, (l.map fun x ↦ c * f x).sum = c * (l.map f).sum
  | [] => by simp
  | x :: l => by rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, sum_map_mulC c f l, Nat.mul_add]

theorem forall₂_setC {α β : Type} {R : α → β → Prop} {l : List α} {m : List β} (h : List.Forall₂ R l m) {x : α} {y : β}
    (hxy : R x y) : ∀ i, List.Forall₂ R (l.set i x) (m.set i y) := by
  induction h with
  | nil => intro i; exact List.Forall₂.nil
  | cons hr hl ih =>
    intro i
    cases i with
    | zero => exact List.Forall₂.cons hxy hl
    | succ i => exact List.Forall₂.cons hr (ih i)

/-- One step of the sent columns' pattern: a column set to any value, against it set to `0`. -/
theorem samePat_stepC (t : Table) (c : ℕ) (rest : List ℕ) (sentE : Array (Option E)) (v : E)
    (h : UniSound.SamePat (UniSound.consumeFold (fun _ ↦ 1) (UniSound.sentStep t []) (c :: rest) (sentE, #[]) []).1
      (UniSound.sentPat t)) :
    UniSound.SamePat (UniSound.consumeFold (fun _ ↦ 1) (UniSound.sentStep t []) rest (sentE.set! c (some v), #[]) []).1
      (UniSound.sentPat t) := by
  have h1 := UniSound.samePat_consume_sent t rest [] [] (sentE.set! c (some v), #[])
    (sentE.set! c (some 0), #[].push (Relation.equal (.table t.opcode c) [] 0)) [] []
    (UniSound.samePat_set (UniSound.samePat_refl sentE) c v 0)
  exact ⟨h1.1.trans h.1, fun i ↦ (h1.2 i).trans (h.2 i)⟩

section TablePart

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

theorem RpSent.growC {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {a : Array (Option Nat)}
    {b : Array (Option E)} (h : RpSent π iv publicInput stream st a b) : RpSent π iv publicInput stream st' a b :=
  List.Forall₂.imp (fun _ _ h ↦ RpO.grow π iv publicInput stream hk hgr h) h

theorem RpPairs.growC {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {a : List (Nat × Nat)}
    {b : List (Nat × E)} (h : RpPairs π iv publicInput stream st a b) : RpPairs π iv publicInput stream st' a b :=
  List.Forall₂.imp (fun _ _ h ↦ ⟨h.1, Rp.sg hk hgr h.2⟩) h

theorem RpRels.growC {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {a : List RelationS}
    {b : List Relation} (h : RpRels π iv publicInput stream st a b) : RpRels π iv publicInput stream st' a b :=
  List.Forall₂.imp (fun _ _ h ↦ ⟨List.Forall₂.imp (fun _ _ h ↦ ⟨h.1, h.2.1, RpL.sg hk hgr h.2.2.1,
    Rp.sg hk hgr h.2.2.2⟩) h.1, Rp.sg hk hgr h.2⟩) h

theorem RpRels.pushC {st : RecState} {a : Array RelationS} {b : Array Relation} {r : RelationS} {u : Relation}
    (h : RpRels π iv publicInput stream st a.toList b.toList) (hr : RpRel π iv publicInput stream st r u) :
    RpRels π iv publicInput stream st (a.push r).toList (b.push u).toList := by
  rw [Array.toList_push, Array.toList_push]
  exact List.rel_append h (List.Forall₂.cons hr List.Forall₂.nil)

theorem RpSent.setC {st : RecState} {a : Array (Option Nat)} {b : Array (Option E)}
    (h : RpSent π iv publicInput stream st a b) (c : Nat) {v : Nat} {x : E} (hv : Rp π iv publicInput stream st v x) :
    RpSent π iv publicInput stream st (a.set! c (some v)) (b.set! c (some x)) := by
  unfold RpSent
  rw [Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
    Array.toList_setIfInBounds]
  exact forall₂_setC h hv c

theorem rpSent_replicateC {st : RecState} (n : Nat) :
    RpSent π iv publicInput stream st (Array.replicate n none) (Array.replicate n none) := by
  unfold RpSent
  rw [Array.toList_replicate, Array.toList_replicate]
  induction n with
  | zero => exact List.Forall₂.nil
  | succ n ih => exact List.Forall₂.cons trivial ih

theorem RpPairs.isEmptyC {st : RecState} {a : List (Nat × Nat)} {b : List (Nat × E)}
    (h : RpPairs π iv publicInput stream st a b) : a.isEmpty = b.isEmpty := by
  unfold RpPairs at h
  cases h <;> rfl

/-- `linearise`'s terms in a table's columns, at `w[..lh]`. -/
theorem rpTerms_tabC {st : RecState} {w : List Nat} {wE : List E} (hw : RpL π iv publicInput stream st w wE)
    {l : List (Nat × Nat)} {m : List (Nat × E)} (h : RpPairs π iv publicInput stream st l m) (t : Table) (lh : Nat) :
    RpTermsC π iv publicInput stream st (l.map fun x ↦ termS (Column.table t.opcode x.1) (List.take lh w) x.2)
      (m.map fun x ↦ term (Column.table t.opcode x.1) (List.take lh wE) x.2) := by
  unfold RpPairs at h
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hr _ ih =>
    exact List.Forall₂.cons ⟨congrArg _ hr.1, rfl, RpL.takeC π iv publicInput stream hw lh, hr.2⟩ ih

/-- A table part's context: the weights, `β`, the point, the sent values, represented. -/
structure TpCtx (st : RecState) (weights : Array Nat) (weightsE : Array E) (beta : Nat) (betaE : E) (w : List Nat)
    (wE : List E) (sentS : Array (Option Nat)) (sentE : Array (Option E)) : Prop where
  hwt : RpL π iv publicInput stream st weights.toList weightsE.toList
  hbeta : Rp π iv publicInput stream st beta betaE
  hw : RpL π iv publicInput stream st w wE
  hsent : RpSent π iv publicInput stream st sentS sentE

theorem TpCtx.grow {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {weights weightsE beta betaE w wE sentS
    sentE} (h : TpCtx π iv publicInput stream st weights weightsE beta betaE w wE sentS sentE) :
    TpCtx π iv publicInput stream st' weights weightsE beta betaE w wE sentS sentE :=
  ⟨RpL.sg hk hgr h.hwt, Rp.sg hk hgr h.hbeta, RpL.sg hk hgr h.hw, RpSent.growC π iv publicInput stream hk hgr h.hsent⟩

theorem TpCtx.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {weights weightsE beta betaE w wE sentS
    sentE} (h : TpCtx π iv publicInput stream st weights weightsE beta betaE w wE sentS sentE) :
    TpCtx π iv publicInput stream st' weights weightsE beta betaE w wE sentS sentE :=
  h.grow π iv publicInput stream hg.inv.kinv hs.grows

end TablePart

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-- **A pure part first, then a `Sim`**, its postcondition as is. -/
theorem Sim.phcC {st : RecState} {α γ δ : Type} {p : Prog α} {P : α → RecState → Prop} {k : α → Prog γ}
    {u : ChanM Id δ} {m ch : Nat} {S : RecState → γ → δ → Prop} (h1 : PHc st p P)
    (h2 : ∀ st' a, PStep st st' → P a st' → Sim π iv publicInput stream st' (k a) u m ch S) :
    Sim π iv publicInput stream st (p >>= k) u m ch S :=
  Sim.pbind' (b := ()) (R := fun st' a _ ↦ P a st') h1 h2

/-- `tgrow [h₁, …] with hg hs`: `grow`, with a table part's facts. -/
syntax "tgrow " "[" ident,* "]" " with " term:max ppSpace term:max : tactic

/-- `tsgrow [h₁, …] with hk hgr`: the facts along `Grows`. -/
syntax "tsgrow " "[" ident,* "]" " with " term:max ppSpace term:max : tactic

set_option hygiene false in
macro_rules
  | `(tactic| tgrow [$h:ident] with $hg $hs') =>
    `(tactic| first
        | replace $h:ident := Rp.pgrow $hg $hs' $h
        | replace $h:ident := RpL.pgrow $hg $hs' $h
        | replace $h:ident := RpPairs.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := RpRels.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := TpCtx.pgrow _ _ _ _ $hg $hs' $h)
  | `(tactic| tgrow [$h:ident, $hs,*] with $hg $hs') =>
    `(tactic| (tgrow [$h] with $hg $hs'; tgrow [$hs,*] with $hg $hs'))

set_option hygiene false in
macro_rules
  | `(tactic| tsgrow [$h:ident] with $hk $hgr) =>
    `(tactic| first
        | replace $h:ident := Rp.sg $hk $hgr $h
        | replace $h:ident := RpL.sg $hk $hgr $h
        | replace $h:ident := RpPairs.growC _ _ _ _ $hk $hgr $h
        | replace $h:ident := RpRels.growC _ _ _ _ $hk $hgr $h
        | replace $h:ident := TpCtx.grow _ _ _ _ $hk $hgr $h)
  | `(tactic| tsgrow [$h:ident, $hs,*] with $hk $hgr) =>
    `(tactic| (tsgrow [$h] with $hk $hgr; tsgrow [$hs,*] with $hk $hgr))

variable (π iv publicInput stream)

/-- **A table's part** (`table_part`): the program's simulates `UniStatement`'s, reading `24 · tableReads t` bytes, its
part and its relations represented, its relations' terms the table's. -/
theorem tablePart_sim (st : RecState) (t : Table) (lh : Nat) {weights : Array Nat} {weightsE : Array E}
    {beta : Nat} {betaE : E} {w : List Nat} {wE : List E}
    (hwt : RpL π iv publicInput stream st weights.toList weightsE.toList)
    (hfl : ∀ tup ∈ t.flushes.pull ++ t.flushes.push, tup.length ≤ weightsE.size)
    (hbeta : Rp π iv publicInput stream st beta betaE) (hw : RpL π iv publicInput stream st w wE) :
    Sim π iv publicInput stream st (Pi1.tablePart t lh weights beta w)
      (UniStatement.tablePart (m := Id) t lh weightsE betaE wE) (24 * UniSound.tableReads t) 0
      (fun st' a b ↦ RpPart π iv publicInput stream st' a.1 b.1 ∧ RpRels π iv publicInput stream st' a.2 b.2 ∧
        TabShape t lh wE b.2) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.tablePart UniStatement.tablePart
  dsimp only
  refine Sim.cast (n := 24 * (sentColumns t).length + 24 * ((t.flushes.pull.zip t.flushes.push).map
      (UniSound.flushReads #[] (UniSound.sentPat t))).sum) (ch := 0 + 0)
    (by unfold UniSound.tableReads; rw [Nat.mul_add]) rfl ?_
  refine Sim.bind (Sim.cast (by exact sum_const_range _ _) (by simp)
    (Sim.forIn_list (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) st (sentColumns t)
      (sentColumns t) (fun i q (s : Array (Option Nat) × Array RelationS) (u : Array (Option E) × Array Relation) ↦
        TpCtx π iv publicInput stream q weights weightsE beta betaE w wE s.1 u.1 ∧
        RpRels π iv publicInput stream q s.2.toList u.2.toList ∧ TabShape t lh wE u.2.toList ∧
        UniSound.SamePat
          (UniSound.consumeFold (fun _ ↦ 1) (UniSound.sentStep t []) ((sentColumns t).drop i) (u.1, #[]) []).1
          (UniSound.sentPat t))
      (fun _ ↦ 24) (fun _ ↦ 0) _ _ rfl ?_ st _ _ hg (Grows.refl st)
      ⟨⟨hwt, hbeta, hw, rpSent_replicateC π iv publicInput stream t.width⟩, List.Forall₂.nil,
        fun _ hr ↦ by simp at hr, UniSound.samePat_refl _⟩)) fun q1 a b hq1 _ hI ↦ ?_
  · intro i hi _ q0 s u hq0 _ hI
    obtain ⟨sentS, relsS⟩ := s
    obtain ⟨sentE, relsE⟩ := u
    obtain ⟨hc0, hr0, hsh0, hpat0⟩ := hI
    dsimp only at hc0 hr0 hsh0 hpat0 ⊢
    have hK0 := hq0.inv.kinv
    refine Sim.cast (n := 24 + 0) (ch := 0 + 0) rfl rfl
      (Sim.bind (sim_nextScalar π iv publicInput stream q0) fun q1 v vE hq1 hgr1 hv ↦ ?_)
    tsgrow [hc0, hr0] with hK0 hgr1
    refine Sim.phcC (equalS_phcC π iv publicInput stream hq1 _ (RpL.takeC π iv publicInput stream hc0.hw lh) hv)
      fun q2 r hq2 hr ↦ ?_
    tgrow [hc0, hr0, hv] with hq1 hq2
    exact Sim.pure_of_pstep (PStep.refl q2 hq2.good) ⟨_, _, rfl, rfl,
      ⟨hc0.hwt, hc0.hbeta, hc0.hw, RpSent.setC π iv publicInput stream hc0.hsent _ hv⟩,
      RpRels.pushC π iv publicInput stream hr0 hr,
      TabShape.push hsh0 (fun tm htm ↦ by
        rw [List.mem_singleton.mp htm]
        exact ⟨⟨_, rfl⟩, rfl, rfl⟩),
      samePat_stepC t _ _ sentE vE (by rw [← List.drop_eq_getElem_cons hi]; exact hpat0)⟩
  obtain ⟨sentS, relsS⟩ := a
  obtain ⟨sentE, relsE⟩ := b
  obtain ⟨hc, hrels, hshape, hpat⟩ := hI
  dsimp only at hc hrels hshape hpat ⊢
  rw [List.drop_length] at hpat
  replace hpat : UniSound.SamePat sentE (UniSound.sentPat t) := hpat
  refine Sim.phcC (phc_one π iv publicInput stream hq1) fun q2 pullS hq2 hpullS ↦ ?_
  tgrow [hc, hrels] with hq1 hq2
  refine Sim.phcC (phc_one π iv publicInput stream hq2.good) fun q3 pushS hq3 hpushS ↦ ?_
  tgrow [hc, hrels, hpullS] with hq2.good hq3
  refine Sim.cast ?_ (by simp) (Sim.bind (Sim.forIn_list (π := π) (iv := iv) (publicInput := publicInput)
    (stream := stream) q3 (t.flushes.pull.zip t.flushes.push) (t.flushes.pull.zip t.flushes.push)
    (fun _ q (s : Array RelationS × Nat × Nat × Nat × Nat) (u : Array Relation × E × E × Nat × Nat) ↦
      TpCtx π iv publicInput stream q weights weightsE beta betaE w wE sentS sentE ∧
      RpRels π iv publicInput stream q s.1.toList u.1.toList ∧ TabShape t lh wE u.1.toList ∧
      Rp π iv publicInput stream q s.2.1 u.2.1 ∧ Rp π iv publicInput stream q s.2.2.1 u.2.2.1 ∧
      s.2.2.2.1 = u.2.2.2.1 ∧ s.2.2.2.2 = u.2.2.2.2)
    (fun i ↦ 24 * UniSound.flushReads weightsE sentE ((t.flushes.pull.zip t.flushes.push).getD i ([], [])))
    (fun _ ↦ 0) _ _ rfl ?_ q3 _ _ hq3.good (Grows.refl q3)
    ⟨hc, hrels, hshape, hpullS, hpushS, rfl, rfl⟩)
    fun q4 s u hq4 _ hJ ↦ Sim.pure_of_pstep (PStep.refl q4 hq4)
      ⟨⟨hJ.2.2.2.1, hJ.2.2.2.2.1, hJ.2.2.2.2.2.1, hJ.2.2.2.2.2.2, hJ.1.hsent⟩, hJ.2.1, hJ.2.2.1⟩)
  · rw [Nat.add_zero]
    refine (sum_range_getD (fun x ↦ 24 * UniSound.flushReads weightsE sentE x) ([], []) _).trans ?_
    rw [sum_map_mulC, UniSound.sum_flushReads t weightsE sentE hpat]
  intro i hi _ q0 s u hq0 _ hJ
  obtain ⟨relsS', pullS', pushS', pdS, qdS⟩ := s
  obtain ⟨relsE', pullE', pushE', pdE, qdE⟩ := u
  obtain ⟨hc0, hr0, hsh0, hpl0, hps0, hpd0, hqd0⟩ := hJ
  dsimp only at hc0 hr0 hsh0 hpl0 hps0 hpd0 hqd0 ⊢
  have hmem := List.getElem_mem hi
  rw [List.getD_eq_getElem _ _ hi]
  generalize (t.flushes.pull.zip t.flushes.push)[i] = x at hmem ⊢
  obtain ⟨pulled, pushed⟩ := x
  obtain ⟨hmpl, hmps⟩ := List.of_mem_zip hmem
  have hl1 : pulled.length ≤ weightsE.size := hfl _ (List.mem_append_left _ hmpl)
  have hl3 : pushed.length ≤ weightsE.size := hfl _ (List.mem_append_right _ hmps)
  have hl2 : (difference pushed pulled).length ≤ weightsE.size := by
    unfold difference
    rw [List.length_map, List.length_zip]
    omega
  unfold UniSound.flushReads
  dsimp only
  refine Sim.phcC (linearise_phc π iv publicInput stream hq0 pulled hc0.hwt hc0.hsent hl1)
    fun q1 a hq1 ⟨hk1, hp1⟩ ↦ ?_
  tgrow [hc0, hr0, hpl0, hps0] with hq0 hq1
  rw [RpPairs.isEmptyC π iv publicInput stream hp1]
  cases he1 : (UniStatement.linearise pulled weightsE sentE).2.isEmpty <;>
    cases he2 : (UniStatement.linearise (difference pushed pulled) weightsE sentE).2.isEmpty <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · -- the pull's fingerprint sent, the push's sent
    refine Sim.cast (n := 24 + (24 + 0)) (ch := 0 + (0 + 0)) (by decide) (by decide) ?_
    have hK1 := hq1.good.inv.kinv
    refine Sim.bind (sim_nextScalar π iv publicInput stream q1) fun q2 v vE hq2 hgr2 hv ↦ ?_
    tsgrow [hc0, hr0, hpl0, hps0, hk1, hp1] with hK1 hgr2
    refine Sim.phcC (phc_add π iv publicInput stream hq2 hv hc0.hbeta) fun q3 vb hq3 hvb ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hk1, hp1, hv] with hq2 hq3
    refine Sim.phcC (phc_add π iv publicInput stream hq3.good hvb hk1) fun q4 vbk hq4 hvbk ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hp1, hv] with hq3.good hq4
    refine Sim.phcC (linearise_phc π iv publicInput stream hq4.good (difference pushed pulled) hc0.hwt hc0.hsent hl2)
      fun q5 c hq5 ⟨_, hpd⟩ ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hp1, hv, hvbk] with hq4.good hq5
    rw [RpPairs.isEmptyC π iv publicInput stream hpd, he2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Sim.phcC (linearise_phc π iv publicInput stream hq5.good pushed hc0.hwt hc0.hsent hl3)
      fun q6 d hq6 ⟨hkp, hpp⟩ ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hp1, hv, hvbk] with hq5.good hq6
    have hK6 := hq6.good.inv.kinv
    refine Sim.bind (sim_nextScalar π iv publicInput stream q6) fun q7 v1 vE1 hq7 hgr7 hv1 ↦ ?_
    tsgrow [hc0, hr0, hpl0, hps0, hp1, hv, hvbk, hkp, hpp] with hK6 hgr7
    refine Sim.phcC (phc_add π iv publicInput stream hq7 hv1 hc0.hbeta) fun q8 vb1 hq8 hvb1 ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hp1, hv, hvbk, hkp, hpp, hv1] with hq7 hq8
    refine Sim.phcC (phc_add π iv publicInput stream hq8.good hvb1 hkp) fun q9 vbk1 hq9 hvbk1 ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hp1, hv, hvbk, hpp, hv1] with hq8.good hq9
    refine Sim.phcC (phc_mul π iv publicInput stream hq9.good hpl0 hv) fun q10 pl hq10 hPl ↦ ?_
    tgrow [hc0, hr0, hps0, hp1, hvbk, hpp, hv1, hvbk1] with hq9.good hq10
    refine Sim.phcC (phc_mul π iv publicInput stream hq10.good hps0 hv1) fun q11 ps hq11 hPs ↦ ?_
    tgrow [hc0, hr0, hp1, hvbk, hpp, hvbk1, hPl] with hq10.good hq11
    exact Sim.pure_of_pstep (PStep.refl q11 hq11.good) ⟨_, _, rfl, rfl, hc0,
      RpRels.pushC π iv publicInput stream (RpRels.pushC π iv publicInput stream hr0
        ⟨rpTerms_tabC π iv publicInput stream hc0.hw hp1 t lh, hvbk⟩)
        ⟨rpTerms_tabC π iv publicInput stream hc0.hw hpp t lh, hvbk1⟩,
      TabShape.push (TabShape.push hsh0 (tabTerm_mapC t lh wE _)) (tabTerm_mapC t lh wE _), hPl, hPs,
      by rw [hpd0], by rw [hqd0]⟩
  · -- the pull's fingerprint sent, not the push's
    refine Sim.cast (n := 24 + 0) (ch := 0 + 0) (by decide) (by decide) ?_
    have hK1 := hq1.good.inv.kinv
    refine Sim.bind (sim_nextScalar π iv publicInput stream q1) fun q2 v vE hq2 hgr2 hv ↦ ?_
    tsgrow [hc0, hr0, hpl0, hps0, hk1, hp1] with hK1 hgr2
    refine Sim.phcC (phc_add π iv publicInput stream hq2 hv hc0.hbeta) fun q3 vb hq3 hvb ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hk1, hp1, hv] with hq2 hq3
    refine Sim.phcC (phc_add π iv publicInput stream hq3.good hvb hk1) fun q4 vbk hq4 hvbk ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hp1, hv] with hq3.good hq4
    refine Sim.phcC (linearise_phc π iv publicInput stream hq4.good (difference pushed pulled) hc0.hwt hc0.hsent hl2)
      fun q5 c hq5 ⟨hkd, hpd⟩ ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hp1, hv, hvbk] with hq4.good hq5
    rw [RpPairs.isEmptyC π iv publicInput stream hpd, he2]
    simp only [↓reduceIte]
    refine Sim.phcC (phc_add π iv publicInput stream hq5.good hv hkd) fun q6 dps hq6 hdps ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hp1, hv, hvbk] with hq5.good hq6
    refine Sim.phcC (phc_mul π iv publicInput stream hq6.good hpl0 hv) fun q7 pl hq7 hPl ↦ ?_
    tgrow [hc0, hr0, hps0, hp1, hvbk, hdps] with hq6.good hq7
    refine Sim.phcC (phc_mul π iv publicInput stream hq7.good hps0 hdps) fun q8 ps hq8 hPs ↦ ?_
    tgrow [hc0, hr0, hp1, hvbk, hPl] with hq7.good hq8
    exact Sim.pure_of_pstep (PStep.refl q8 hq8.good) ⟨_, _, rfl, rfl, hc0,
      RpRels.pushC π iv publicInput stream hr0 ⟨rpTerms_tabC π iv publicInput stream hc0.hw hp1 t lh, hvbk⟩,
      TabShape.push hsh0 (tabTerm_mapC t lh wE _), hPl, hPs, by rw [hpd0], by rw [hqd0]⟩
  · -- the push's fingerprint sent, not the pull's
    refine Sim.cast (n := 24 + 0) (ch := 0 + 0) (by decide) (by decide) ?_
    refine Sim.phcC (phc_add π iv publicInput stream hq1.good hc0.hbeta hk1) fun q2 dpl hq2 hdpl ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0] with hq1.good hq2
    refine Sim.phcC (linearise_phc π iv publicInput stream hq2.good (difference pushed pulled) hc0.hwt hc0.hsent hl2)
      fun q3 c hq3 ⟨_, hpd⟩ ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hdpl] with hq2.good hq3
    rw [RpPairs.isEmptyC π iv publicInput stream hpd, he2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Sim.phcC (linearise_phc π iv publicInput stream hq3.good pushed hc0.hwt hc0.hsent hl3)
      fun q4 d hq4 ⟨hkp, hpp⟩ ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hdpl] with hq3.good hq4
    have hK4 := hq4.good.inv.kinv
    refine Sim.bind (sim_nextScalar π iv publicInput stream q4) fun q5 v vE hq5 hgr5 hv ↦ ?_
    tsgrow [hc0, hr0, hpl0, hps0, hdpl, hkp, hpp] with hK4 hgr5
    refine Sim.phcC (phc_add π iv publicInput stream hq5 hv hc0.hbeta) fun q6 vb hq6 hvb ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hdpl, hkp, hpp, hv] with hq5 hq6
    refine Sim.phcC (phc_add π iv publicInput stream hq6.good hvb hkp) fun q7 vbk hq7 hvbk ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hdpl, hpp, hv] with hq6.good hq7
    refine Sim.phcC (phc_mul π iv publicInput stream hq7.good hpl0 hdpl) fun q8 pl hq8 hPl ↦ ?_
    tgrow [hc0, hr0, hps0, hpp, hv, hvbk] with hq7.good hq8
    refine Sim.phcC (phc_mul π iv publicInput stream hq8.good hps0 hv) fun q9 ps hq9 hPs ↦ ?_
    tgrow [hc0, hr0, hpp, hvbk, hPl] with hq8.good hq9
    exact Sim.pure_of_pstep (PStep.refl q9 hq9.good) ⟨_, _, rfl, rfl, hc0,
      RpRels.pushC π iv publicInput stream hr0 ⟨rpTerms_tabC π iv publicInput stream hc0.hw hpp t lh, hvbk⟩,
      TabShape.push hsh0 (tabTerm_mapC t lh wE _), hPl, hPs, by rw [hpd0], by rw [hqd0]⟩
  · -- neither fingerprint sent
    refine Sim.cast (n := 0) (ch := 0) (by decide) rfl ?_
    refine Sim.phcC (phc_add π iv publicInput stream hq1.good hc0.hbeta hk1) fun q2 dpl hq2 hdpl ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0] with hq1.good hq2
    refine Sim.phcC (linearise_phc π iv publicInput stream hq2.good (difference pushed pulled) hc0.hwt hc0.hsent hl2)
      fun q3 c hq3 ⟨hkd, hpd⟩ ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hdpl] with hq2.good hq3
    rw [RpPairs.isEmptyC π iv publicInput stream hpd, he2]
    simp only [↓reduceIte]
    refine Sim.phcC (phc_add π iv publicInput stream hq3.good hdpl hkd) fun q4 dps hq4 hdps ↦ ?_
    tgrow [hc0, hr0, hpl0, hps0, hdpl] with hq3.good hq4
    refine Sim.phcC (phc_mul π iv publicInput stream hq4.good hpl0 hdpl) fun q5 pl hq5 hPl ↦ ?_
    tgrow [hc0, hr0, hps0, hdps] with hq4.good hq5
    refine Sim.phcC (phc_mul π iv publicInput stream hq5.good hps0 hdps) fun q6 ps hq6 hPs ↦ ?_
    tgrow [hc0, hr0, hPl] with hq5.good hq6
    exact Sim.pure_of_pstep (PStep.refl q6 hq6.good) ⟨_, _, rfl, rfl, hc0, hr0, hsh0, hPl, hPs,
      by rw [hpd0], by rw [hqd0]⟩

/-- **A table's bytes**: `24` a value it reads (`UniSound.tableReads`). -/
def tableBytes (t : Table) : Nat := 24 * UniSound.tableReads t

/-- **A table's part, its shape**: its relations' terms in its columns, at `w[..h_t]` (`h_t` its log height). -/
def tableShape (t : Table) (wE : List E) (b : TablePart × List Relation) : Prop :=
  TabShape t (reference.heights.getD t.opcode 0) wE b.2

variable {π iv publicInput stream}

/-- **`TableSpec`**, `Compose`'s interface for a table's part. -/
theorem tableSpec : TableSpec partR tableShape tableBytes := by
  intro π iv publicInput stream st t ht weights weightsE beta betaE w wE _ hwt hsize hbeta hw _
  exact tablePart_sim π iv publicInput stream st t _ hwt
    (fun tup htup ↦ by rw [hsize]; exact ((UniSound.Ids.tablesFacts t ht).2 tup htup).1) hbeta hw

/-- info: 'RecGraph.Sim.tableSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tableSpec

end RecGraph.Sim
