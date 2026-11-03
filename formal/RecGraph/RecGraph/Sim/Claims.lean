-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The generic `combine` and its algebra are `formal/UniSound`'s
-- (`UniSound/Ids/Weights.lean`: `combineEq`, `mergedPrefix`, `mergedSelf`), over any type of coordinates.
import RecGraph.Sim.Tables
import UniSound.Ids.Weights

/-!
# The simulation: `combine` and the batch's weights

The program's `combine` compares points by their nodes, `UniStatement`'s by their values; the program's `weight_at`
groups the terms by row, `UniStatement`'s reads them one by one. Both claims enter the batch only through their value
and their weight at the batch's point.

* **`combine` over any coordinates** (`CombG`): `combineG`, `UniStatement.combine` with points over a type `Pt` with
  decidable equality, and its algebra ported from `UniSound` (`combineEqG`: the claim is the `ρ`-combination of the
  relations' terms at their merged points; `mergedPrefixG`, `mergedSelfG`). At `Pt = Nat` it is the program's
  `combine` on values (the points compared by node).
-/

namespace RecGraph.Sim.Gen

open LeanVM.Parameters UniStatement
open UniSound.Ids.Weights (Tm rd sum_map_modify rd_mergeTerm rd_empty rd_mergedFold)

set_option linter.unusedSectionVars false

variable {Pt : Type} [DecidableEq Pt]

/-- A term over coordinates `Pt`. -/
structure TermG (Pt : Type) where
  column : Column
  point : List Pt
  twist : ℕ
  coefficient : E

/-- A relation over coordinates `Pt`. -/
structure RelG (Pt : Type) where
  terms : List (TermG Pt)
  value : E

/-- A relation's commitment: its first term's. -/
def RelG.commitment (r : RelG Pt) : Commitment :=
  match r.terms with
  | t :: _ => t.column.commitment
  | [] => .c1

/-- A combined claim over coordinates `Pt`. -/
structure CombG (Pt : Type) where
  points : List (List Pt)
  terms : List (Column × ℕ × ℕ × E)
  value : E
  relations : ℕ

/-- `longestOf` over `Pt`. -/
def longestOfG (points : Array (List Pt)) (p : ℕ) : ℕ :=
  let pp := points.getD p []
  (List.range points.size).foldl (fun best q ↦
    let pq := points.getD q []
    if pq.length ≥ pp.length ∧ pq.take pp.length == pp ∧ pq.length > (points.getD best []).length then q
    else best) p

/-- **`combine` over `Pt`** (`UniStatement.combine`'s code). -/
def combineG (relations : List (RelG Pt)) (commitment : Commitment) (rho : E) : Option (CombG Pt) :=
  let mine := relations.filter (·.commitment == commitment)
  if mine.isEmpty then none else
  let (points, terms, value, _) := mine.foldl
    (fun (acc : Array (List Pt) × Array (Column × ℕ × ℕ × E) × E × E) relation ↦
      let (points, terms, value, scale) := acc
      let value := value + scale * relation.value
      let (points, terms) := relation.terms.foldl
        (fun (acc : Array (List Pt) × Array (Column × ℕ × ℕ × E)) t ↦
          let (points, terms) := acc
          let (points, p) := match points.findIdx? (· == t.point) with
            | some p => (points, p)
            | none => (points.push t.point, points.size)
          (points, mergeTerm terms t.column p t.twist (scale * t.coefficient)))
        (points, terms)
      (points, terms, value, scale * rho))
    (#[], #[], 0, 1)
  let longest := (List.range points.size).map (longestOfG points)
  let kept := (List.range points.size).filter fun p ↦ longest.getD p p == p
  let renumber (p : ℕ) : ℕ := kept.idxOf (longest.getD p p)
  let merged := terms.foldl (fun acc (column, p, twist, coefficient) ↦
    mergeTerm acc column (renumber p) twist coefficient) #[]
  some ⟨kept.map (points.getD · []), merged.toList, value, mine.length⟩

/-- The relations on one commitment. -/
def mineG (rels : List (RelG Pt)) (c : Commitment) : List (RelG Pt) := rels.filter (·.commitment == c)

/-- `combine`'s points: every term's point, each once, in order of first use. -/
def combinePointsG (rels : List (RelG Pt)) : Array (List Pt) :=
  rels.foldl (fun points r ↦ r.terms.foldl (fun points tm ↦
    match points.findIdx? (· == tm.point) with
    | some _ => points
    | none => points.push tm.point) points) #[]

/-- The point `combine` reads a term at `p` with: of the points having `p` as a prefix, the longest. -/
def mergedPointG (rels : List (RelG Pt)) (p : List Pt) : List Pt :=
  (combinePointsG rels).getD
    (longestOfG (combinePointsG rels) (((combinePointsG rels).findIdx? (· == p)).getD 0)) []

/-! ## The algebra (`UniSound.Ids.Weights`, over `Pt`) -/

/-- `combineG`'s step on one term (scale `s`): the point found or appended, the term merged. -/
def cInner (s : E) (acc : Array (List Pt) × Array Tm) (t : TermG Pt) : Array (List Pt) × Array Tm :=
  let pp : Array (List Pt) × ℕ := match acc.1.findIdx? (· == t.point) with
    | some p => (acc.1, p)
    | none => (acc.1.push t.point, acc.1.size)
  (pp.1, mergeTerm acc.2 t.column pp.2 t.twist (s * t.coefficient))

/-- `combineG`'s step on one relation. -/
def cOuter (ρ : E) (acc : Array (List Pt) × Array Tm × E × E) (r : RelG Pt) :
    Array (List Pt) × Array Tm × E × E :=
  let pt := r.terms.foldl (cInner acc.2.2.2) (acc.1, acc.2.1)
  (pt.1, pt.2, acc.2.2.1 + acc.2.2.2 * r.value, acc.2.2.2 * ρ)

/-- `combineG`'s `longest`. -/
def longestList (P : Array (List Pt)) : List ℕ := (List.range P.size).map (longestOfG P)

/-- `combineG`'s `kept`. -/
def keptOf (P : Array (List Pt)) : List ℕ :=
  (List.range P.size).filter fun p ↦ (longestList P).getD p p == p

/-- `combineG`'s `renumber`. -/
def renumberOf (P : Array (List Pt)) (p : ℕ) : ℕ := (keptOf P).idxOf ((longestList P).getD p p)

/-- `combineG`'s `merged`. -/
def mergedOf (P : Array (List Pt)) (T : Array Tm) : Array Tm :=
  T.foldl (fun acc x ↦ mergeTerm acc x.1 (renumberOf P x.2.1) x.2.2.1 x.2.2.2) #[]

theorem combineG_eq (rels : List (RelG Pt)) (c : Commitment) (ρ : E) :
    combineG rels c ρ = if (mineG rels c).isEmpty then none else
      some ⟨(keptOf ((mineG rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).1).map
          (((mineG rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).1.getD · []),
        (mergedOf ((mineG rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).1
          ((mineG rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).2.1).toList,
        ((mineG rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).2.2.1, (mineG rels c).length⟩ := rfl

/-- `combinePointsG`' step on one term. -/
def cpStep (P : Array (List Pt)) (tm : TermG Pt) : Array (List Pt) :=
  match P.findIdx? (· == tm.point) with
  | some _ => P
  | none => P.push tm.point

/-- `combinePointsG`' step on one relation. -/
def cpOuter (P : Array (List Pt)) (r : RelG Pt) : Array (List Pt) := r.terms.foldl cpStep P

theorem combinePointsG_eq (rels : List (RelG Pt)) : combinePointsG rels = rels.foldl cpOuter #[] := rfl

/-- The index `combineG` reads a term's point at. -/
def cIdx (P : Array (List Pt)) (tm : TermG Pt) : ℕ :=
  match P.findIdx? (· == tm.point) with
  | some p => p
  | none => P.size

theorem cInner_eq (s : E) (P : Array (List Pt)) (T : Array Tm) (t : TermG Pt) :
    cInner s (P, T) t = (cpStep P t, mergeTerm T t.column (cIdx P t) t.twist (s * t.coefficient)) := by
  cases h : P.findIdx? (· == t.point) <;> simp only [cInner, cpStep, cIdx, h]

theorem findIdx_some {P : Array (List Pt)} {pt : List Pt} {p : ℕ} (h : P.findIdx? (· == pt) = some p) :
    p < P.size ∧ P.getD p [] = pt := by
  obtain ⟨hp, hpred, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨hp, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp, Option.getD_some]
  simpa using hpred

theorem getD_mem {P : Array (List Pt)} {i : ℕ} (hi : i < P.size) : P.getD i [] ∈ P.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  exact Array.mem_def.mp (Array.getElem_mem hi)

theorem findIdx_of_mem {P : Array (List Pt)} {pt : List Pt} (h : pt ∈ P.toList) :
    ∃ i, P.findIdx? (· == pt) = some i := by
  cases hf : P.findIdx? (· == pt) with
  | some i => exact ⟨i, rfl⟩
  | none =>
    have := Array.findIdx?_eq_none_iff.mp hf pt (Array.mem_def.mpr h)
    simp at this

theorem push_getD (P : Array (List Pt)) (x : List Pt) (i : ℕ) :
    (P.push x).getD i [] = if i = P.size then x else P.getD i [] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.getD_eq_getD_getElem?]
  split_ifs <;> rfl

/-- `Q` extends `P`. -/
def Ext (Q P : Array (List Pt)) : Prop := P.size ≤ Q.size ∧ ∀ i < P.size, Q.getD i [] = P.getD i []

theorem Ext.refl (P : Array (List Pt)) : Ext P P := ⟨le_rfl, fun _ _ ↦ rfl⟩

theorem Ext.trans {R Q P : Array (List Pt)} (h1 : Ext R Q) (h2 : Ext Q P) : Ext R P :=
  ⟨h2.1.trans h1.1, fun i hi ↦ (h1.2 i (lt_of_lt_of_le hi h2.1)).trans (h2.2 i hi)⟩

theorem cpStep_ext (P : Array (List Pt)) (t : TermG Pt) : Ext (cpStep P t) P := by
  unfold cpStep
  split
  · exact Ext.refl P
  · refine ⟨by simp, fun i hi ↦ ?_⟩
    rw [push_getD, ite_eq_right (by omega)]

theorem cIdx_spec (P : Array (List Pt)) (t : TermG Pt) :
    cIdx P t < (cpStep P t).size ∧ (cpStep P t).getD (cIdx P t) [] = t.point := by
  unfold cIdx cpStep
  split
  · next p h => exact findIdx_some h
  · exact ⟨by simp, by rw [push_getD, ite_eq_left rfl]⟩

theorem mem_cpStep (P : Array (List Pt)) (t : TermG Pt) (x : List Pt) :
    x ∈ (cpStep P t).toList ↔ x ∈ P.toList ∨ x = t.point := by
  unfold cpStep
  split
  · next p h =>
    obtain ⟨hp, hpt⟩ := findIdx_some h
    refine ⟨Or.inl, fun h' ↦ h'.elim id fun hx ↦ ?_⟩
    rw [hx, ← hpt]
    exact getD_mem hp
  · simp

theorem cpFold_ext (ts : List (TermG Pt)) (P : Array (List Pt)) : Ext (ts.foldl cpStep P) P := by
  induction ts generalizing P with
  | nil => exact Ext.refl P
  | cons t ts ih => exact (ih (cpStep P t)).trans (cpStep_ext P t)

theorem mem_cpFold (ts : List (TermG Pt)) (P : Array (List Pt)) (x : List Pt) :
    x ∈ (ts.foldl cpStep P).toList ↔ x ∈ P.toList ∨ ∃ t ∈ ts, t.point = x := by
  induction ts generalizing P with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, mem_cpStep]
    constructor
    · rintro ((h | h) | ⟨t', ht', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨t, by simp, h.symm⟩
      · exact Or.inr ⟨t', by simp [ht'], h⟩
    · rintro (h | ⟨t', ht', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp ht' with rfl | ht'
        · exact Or.inl (Or.inr h.symm)
        · exact Or.inr ⟨t', ht', h⟩

theorem mem_cpOuterFold (l : List (RelG Pt)) (P : Array (List Pt)) (x : List Pt) :
    x ∈ (l.foldl cpOuter P).toList ↔ x ∈ P.toList ∨ ∃ r ∈ l, ∃ t ∈ r.terms, t.point = x := by
  induction l generalizing P with
  | nil => simp
  | cons r l ih =>
    rw [List.foldl_cons, ih, cpOuter, mem_cpFold]
    constructor
    · rintro ((h | ⟨t, ht, h⟩) | ⟨r', hr', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, by simp, t, ht, h⟩
      · exact Or.inr ⟨r', by simp [hr'], h⟩
    · rintro (h | ⟨r', hr', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hr' with rfl | hr'
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨r', hr', h⟩

/-- **`combinePointsG`' points are the terms' points.** -/
theorem mem_combinePoints (rels : List (RelG Pt)) (x : List Pt) :
    x ∈ (combinePointsG rels).toList ↔ ∃ r ∈ rels, ∃ t ∈ r.terms, t.point = x := by
  rw [combinePointsG_eq, mem_cpOuterFold]
  simp

theorem cInner_fold_fst (s : E) (ts : List (TermG Pt)) (P : Array (List Pt)) (T : Array Tm) :
    (ts.foldl (cInner s) (P, T)).1 = ts.foldl cpStep P := by
  induction ts generalizing P T with
  | nil => rfl
  | cons t ts ih => rw [List.foldl_cons, List.foldl_cons, cInner_eq, ih]

/-- **The inner fold's reading**, for a reading `G` of the indices that reads the final points. -/
theorem cInner_fold_rd (s : E) (F' : Column → List Pt → ℕ → E) (G : Column → ℕ → ℕ → E) :
    ∀ (ts : List (TermG Pt)) (P : Array (List Pt)) (T : Array Tm),
      (∀ i < (ts.foldl cpStep P).size, ∀ col tw, G col i tw = F' col ((ts.foldl cpStep P).getD i []) tw) →
      rd G (ts.foldl (cInner s) (P, T)).2 =
        rd G T + s * (ts.map fun t ↦ t.coefficient * F' t.column t.point t.twist).sum
  | [], P, T, _ => by simp
  | t :: ts, P, T, hG => by
    rw [List.foldl_cons] at hG
    rw [List.foldl_cons, cInner_eq, cInner_fold_rd s F' G ts _ _ hG, rd_mergeTerm]
    have hR := cpFold_ext ts (cpStep P t)
    obtain ⟨hlt, hpt⟩ := cIdx_spec P t
    have hG' := hG (cIdx P t) (lt_of_lt_of_le hlt hR.1) t.column t.twist
    rw [hR.2 _ hlt, hpt] at hG'
    rw [hG', List.map_cons, List.sum_cons]
    ring

theorem cOuter_step (ρ : E) (P : Array (List Pt)) (T : Array Tm) (v s : E) (r : RelG Pt) :
    cOuter ρ (P, T, v, s) r = ((r.terms.foldl (cInner s) (P, T)).1, (r.terms.foldl (cInner s) (P, T)).2,
      v + s * r.value, s * ρ) := rfl

theorem cOuter_fold_fst (ρ : E) : ∀ (l : List (RelG Pt)) (P : Array (List Pt)) (T : Array Tm) (v s : E),
    (l.foldl (cOuter ρ) (P, T, v, s)).1 = l.foldl cpOuter P
  | [], _, _, _, _ => rfl
  | r :: l, P, T, v, s => by
    rw [List.foldl_cons, cOuter_step, cOuter_fold_fst ρ l, cInner_fold_fst]
    rfl

theorem cOuter_fold_val (ρ : E) : ∀ (l : List (RelG Pt)) (n : ℕ) (P : Array (List Pt)) (T : Array Tm) (v : E),
    (l.foldl (cOuter ρ) (P, T, v, ρ ^ n)).2.2.1 = v + ((l.zipIdx n).map fun ri ↦ ρ ^ ri.2 * ri.1.value).sum
  | [], _, _, _, _ => by simp
  | r :: l, n, P, T, v => by
    rw [List.foldl_cons, cOuter_step, ← pow_succ, cOuter_fold_val ρ l (n + 1), List.zipIdx_cons,
      List.map_cons, List.sum_cons]
    ring

theorem cpOuter_fold_ext (l : List (RelG Pt)) (P : Array (List Pt)) : Ext (l.foldl cpOuter P) P := by
  induction l generalizing P with
  | nil => exact Ext.refl P
  | cons r l ih => exact (ih (cpOuter P r)).trans (cpFold_ext r.terms P)

theorem cOuter_fold_rd (ρ : E) (F' : Column → List Pt → ℕ → E) (G : Column → ℕ → ℕ → E) :
    ∀ (l : List (RelG Pt)) (n : ℕ) (P : Array (List Pt)) (T : Array Tm) (v : E),
      (∀ i < (l.foldl cpOuter P).size, ∀ col tw, G col i tw = F' col ((l.foldl cpOuter P).getD i []) tw) →
      rd G (l.foldl (cOuter ρ) (P, T, v, ρ ^ n)).2.1 = rd G T + ((l.zipIdx n).map fun ri ↦
        ρ ^ ri.2 * (ri.1.terms.map fun t ↦ t.coefficient * F' t.column t.point t.twist).sum).sum
  | [], _, _, _, _, _ => by simp
  | r :: l, n, P, T, v, hG => by
    rw [List.foldl_cons] at hG
    have hR := cpOuter_fold_ext l (cpOuter P r)
    rw [List.foldl_cons, cOuter_step, ← pow_succ, cOuter_fold_rd ρ F' G l (n + 1) _ _ _ ?_,
      cInner_fold_rd (ρ ^ n) F' G r.terms P T ?_, List.zipIdx_cons, List.map_cons, List.sum_cons]
    · ring
    · intro i hi col tw
      rw [hG i (lt_of_lt_of_le hi hR.1), hR.2 i hi]
      rfl
    · rw [cInner_fold_fst]
      exact hG

/-- **The merge's fold**: re-indexing the terms by `ren` reads them at `ren`. -/
theorem rd_mergedFold (H : Column → ℕ → ℕ → E) (ren : ℕ → ℕ) : ∀ (l : List Tm) (A : Array Tm),
    rd H (l.foldl (fun acc x ↦ mergeTerm acc x.1 (ren x.2.1) x.2.2.1 x.2.2.2) A) =
      rd H A + (l.map fun x ↦ x.2.2.2 * H x.1 (ren x.2.1) x.2.2.1).sum
  | [], _ => by simp
  | x :: l, A => by
    rw [List.foldl_cons, rd_mergedFold H ren l, rd_mergeTerm, List.map_cons, List.sum_cons]
    ring

/-! ### `longestOfG` -/

/-- `longestOfG`'s step. -/
def lStep (P : Array (List Pt)) (pp : List Pt) (best q : ℕ) : ℕ :=
  let pq := P.getD q []
  if pq.length ≥ pp.length ∧ pq.take pp.length == pp ∧ pq.length > (P.getD best []).length then q
  else best

theorem longestOf_eq (P : Array (List Pt)) (p : ℕ) :
    longestOfG P p = (List.range P.size).foldl (lStep P (P.getD p [])) p := rfl

/-- `q` extends `pp`. -/
def Extends (pp q : List Pt) : Prop := pp.length ≤ q.length ∧ q.take pp.length = pp

theorem Extends.refl (pp : List Pt) : Extends pp pp := ⟨le_rfl, List.take_of_length_le le_rfl⟩

theorem Extends.trans {a b c : List Pt} (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  have : c.take a.length = (c.take b.length).take a.length := by
    rw [List.take_take, min_eq_left h1.1]
  rw [this, h2.2, h1.2]

theorem lStep_spec (P : Array (List Pt)) (pp : List Pt) (best q : ℕ) :
    (Extends pp (P.getD q []) ∧ (P.getD best []).length < (P.getD q []).length ∧ lStep P pp best q = q) ∨
      (¬(Extends pp (P.getD q []) ∧ (P.getD best []).length < (P.getD q []).length) ∧
        lStep P pp best q = best) := by
  unfold lStep Extends
  dsimp only
  split_ifs with h
  · simp only [beq_iff_eq] at h
    exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2, rfl⟩
  · refine Or.inr ⟨fun ⟨⟨a, b⟩, c⟩ ↦ h ⟨a, by simpa using b, c⟩, rfl⟩

theorem lFold_congr (P : Array (List Pt)) (pp : List Pt) : ∀ (l : List ℕ) (b1 b2 : ℕ),
    P.getD b1 [] = P.getD b2 [] → P.getD (l.foldl (lStep P pp) b1) [] = P.getD (l.foldl (lStep P pp) b2) []
  | [], _, _, h => h
  | q :: l, b1, b2, h => by
    simp only [List.foldl_cons]
    apply lFold_congr P pp l
    unfold lStep
    simp only [h]
    split_ifs
    · rfl
    · exact h

theorem lFold_inv (P : Array (List Pt)) (pp : List Pt) : ∀ (l : List ℕ) (best : ℕ),
    (P.getD best []).length ≤ (P.getD (l.foldl (lStep P pp) best) []).length ∧
    (Extends pp (P.getD best []) → Extends pp (P.getD (l.foldl (lStep P pp) best) [])) ∧
    (∀ q ∈ l, Extends pp (P.getD q []) →
      (P.getD q []).length ≤ (P.getD (l.foldl (lStep P pp) best) []).length) ∧
    (l.foldl (lStep P pp) best = best ∨ l.foldl (lStep P pp) best ∈ l)
  | [], best => by simp
  | q :: l, best => by
    obtain ⟨ih1, ih2, ih3, ih4⟩ := lFold_inv P pp l (lStep P pp best q)
    simp only [List.foldl_cons]
    rcases lStep_spec P pp best q with ⟨hE, hlt, heq⟩ | ⟨hn, heq⟩
    · rw [heq] at ih1 ih2 ih3 ih4 ⊢
      refine ⟨hlt.le.trans ih1, fun _ ↦ ih2 hE, fun q' hq' hE' ↦ ?_, ?_⟩
      · rcases List.mem_cons.mp hq' with rfl | hq'
        · exact ih1
        · exact ih3 q' hq' hE'
      · rcases ih4 with h | h
        · exact Or.inr (by simp [h])
        · exact Or.inr (by simp [h])
    · rw [heq] at ih1 ih2 ih3 ih4 ⊢
      refine ⟨ih1, ih2, fun q' hq' hE' ↦ ?_, ?_⟩
      · rcases List.mem_cons.mp hq' with rfl | hq'
        · have : (P.getD q' []).length ≤ (P.getD best []).length := by
            by_contra hc
            exact hn ⟨hE', by omega⟩
          exact this.trans ih1
        · exact ih3 q' hq' hE'
      · rcases ih4 with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

theorem foldl_fixed {α β : Type*} (g : β → α → β) (b : β) :
    ∀ l : List α, (∀ q ∈ l, g b q = b) → l.foldl g b = b
  | [], _ => rfl
  | q :: l, h => by
    rw [List.foldl_cons, h q (by simp)]
    exact foldl_fixed g b l fun q' hq' ↦ h q' (by simp [hq'])

theorem longestOf_lt (P : Array (List Pt)) (p : ℕ) (hp : p < P.size) : longestOfG P p < P.size := by
  rw [longestOf_eq]
  rcases (lFold_inv P (P.getD p []) (List.range P.size) p).2.2.2 with h | h
  · rw [h]; exact hp
  · exact List.mem_range.mp h

theorem longestOf_ext (P : Array (List Pt)) (p : ℕ) :
    Extends (P.getD p []) (P.getD (longestOfG P p) []) := by
  rw [longestOf_eq]
  exact (lFold_inv P (P.getD p []) (List.range P.size) p).2.1 (Extends.refl _)

theorem longestOf_max (P : Array (List Pt)) (p : ℕ) : ∀ q < P.size, Extends (P.getD p []) (P.getD q []) →
    (P.getD q []).length ≤ (P.getD (longestOfG P p) []).length := by
  intro q hq hE
  rw [longestOf_eq]
  exact (lFold_inv P (P.getD p []) (List.range P.size) p).2.2.1 q (List.mem_range.mpr hq) hE

/-- **`longestOfG` is idempotent**: the longest extension has no strictly longer extension. -/
theorem longestOf_idem (P : Array (List Pt)) (p : ℕ) : longestOfG P (longestOfG P p) = longestOfG P p := by
  rw [longestOf_eq P (longestOfG P p)]
  apply foldl_fixed
  intro q hq
  rcases lStep_spec P (P.getD (longestOfG P p) []) (longestOfG P p) q with ⟨hE, hlt, _⟩ | ⟨_, h⟩
  · exfalso
    have := longestOf_max P p q (List.mem_range.mp hq) ((longestOf_ext P p).trans hE)
    omega
  · exact h

/-- `longestOfG` reads only its point. -/
theorem longestOf_congr (P : Array (List Pt)) (i j : ℕ) (h : P.getD i [] = P.getD j []) :
    P.getD (longestOfG P i) [] = P.getD (longestOfG P j) [] := by
  rw [longestOf_eq, longestOf_eq, h]
  exact lFold_congr P _ _ i j h

/-- A point of `P` at index `i`, merged: its longest extension. -/
theorem merged_getD (P : Array (List Pt)) (i : ℕ) (hi : i < P.size) :
    P.getD (longestOfG P ((P.findIdx? (· == P.getD i [])).getD 0)) [] = P.getD (longestOfG P i) [] := by
  obtain ⟨j, hj⟩ := findIdx_of_mem (getD_mem hi)
  rw [hj, Option.getD_some]
  exact longestOf_congr P j i (findIdx_some hj).2

/-- **The renumbered point is the merged point.** -/
theorem renumber_getD (P : Array (List Pt)) (i : ℕ) (hi : i < P.size) :
    ((keptOf P).map (P.getD · [])).getD (renumberOf P i) [] = P.getD (longestOfG P i) [] := by
  have hL : ∀ j < P.size, (longestList P).getD j j = longestOfG P j := by
    intro j hj
    simp [longestList, List.getD_eq_getElem?_getD, hj]
  have hb := longestOf_lt P i hi
  have hmem : longestOfG P i ∈ keptOf P := by
    simp only [keptOf, List.mem_filter, List.mem_range, hb, true_and, hL _ hb, longestOf_idem,
      beq_self_eq_true]
  unfold renumberOf
  rw [hL i hi]
  have hlt := List.idxOf_lt_length_iff.mpr hmem
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf]
  rfl

/-- **`combineG` is the `ρ`-combination.** -/
theorem combineEqG (rels : List (RelG Pt)) (c : Commitment) (ρ : E) (hne : mineG rels c ≠ []) :
    ∃ cb, combineG rels c ρ = some cb ∧
      cb.value = ((mineG rels c).zipIdx.map fun ri ↦ ρ ^ ri.2 * ri.1.value).sum ∧
      ∀ F : Column → List Pt → ℕ → E,
        (cb.terms.map fun tm ↦ tm.2.2.2 * F tm.1 (cb.points.getD tm.2.1 []) tm.2.2.1).sum =
          ((mineG rels c).zipIdx.map fun ri ↦ ρ ^ ri.2 * (ri.1.terms.map fun tm ↦
            tm.coefficient * F tm.column (mergedPointG (mineG rels c) tm.point) tm.twist).sum).sum := by
  have hE : ¬ (mineG rels c).isEmpty = true := by simpa [List.isEmpty_iff] using hne
  rw [combineG_eq, ite_eq_right hE]
  refine ⟨_, rfl, ?_, ?_⟩
  · have := cOuter_fold_val ρ (mineG rels c) 0 #[] #[] 0
    rw [pow_zero, zero_add] at this
    exact this
  · intro F
    set ms := mineG rels c with hms
    set res := ms.foldl (cOuter ρ) (#[], #[], 0, 1) with hres
    have hP : ms.foldl cpOuter #[] = res.1 := by rw [hres, cOuter_fold_fst]
    have hC : combinePointsG ms = res.1 := (combinePointsG_eq ms).trans hP
    have hres0 : res = ms.foldl (cOuter ρ) (#[], #[], 0, ρ ^ 0) := by rw [pow_zero]
    have hG : ∀ i < (ms.foldl cpOuter #[]).size, ∀ col tw,
        F col (((keptOf res.1).map (res.1.getD · [])).getD (renumberOf res.1 i) []) tw =
          F col (mergedPointG ms ((ms.foldl cpOuter #[]).getD i [])) tw := by
      intro i hi col tw
      rw [hP] at hi ⊢
      unfold mergedPointG
      rw [hC, renumber_getD _ _ hi, merged_getD _ _ hi]
    have hrd := cOuter_fold_rd ρ (fun col pt tw ↦ F col (mergedPointG ms pt) tw)
      (fun col p tw ↦ F col (((keptOf res.1).map (res.1.getD · [])).getD (renumberOf res.1 p) []) tw)
      ms 0 #[] #[] 0 hG
    rw [← hres0, rd_empty, zero_add] at hrd
    rw [← hrd]
    show rd (fun col p tw ↦ F col (((keptOf res.1).map (res.1.getD · [])).getD p []) tw)
      (mergedOf res.1 res.2.1) = _
    unfold mergedOf
    rw [← Array.foldl_toList, rd_mergedFold, rd_empty, zero_add]
    rfl

/-! ## Merged points -/

/-- A term's merged point: the longest of `combinePointsG` extending it. -/
theorem mergedPoint_spec (rels : List (RelG Pt)) (p : List Pt)
    (hp : ∃ r ∈ rels, ∃ tm ∈ r.terms, tm.point = p) :
    ∃ b < (combinePointsG rels).size, mergedPointG rels p = (combinePointsG rels).getD b [] ∧
      Extends p ((combinePointsG rels).getD b []) := by
  obtain ⟨i, hi⟩ := findIdx_of_mem ((mem_combinePoints rels p).mpr hp)
  obtain ⟨hlt, hpi⟩ := findIdx_some hi
  refine ⟨longestOfG (combinePointsG rels) i, longestOf_lt _ _ hlt, ?_, ?_⟩
  · unfold mergedPointG
    rw [hi, Option.getD_some]
  · rw [← hpi]
    exact longestOf_ext _ _

/-- **A merged point extends the point** and is a term's point. -/
theorem mergedPrefixG (rels : List (RelG Pt)) (p : List Pt) (hp : ∃ r ∈ rels, ∃ tm ∈ r.terms, tm.point = p) :
    (mergedPointG rels p).take p.length = p ∧ ∃ r ∈ rels, ∃ tm ∈ r.terms, tm.point = mergedPointG rels p := by
  obtain ⟨b, hb, heq, hE⟩ := mergedPoint_spec rels p hp
  rw [heq]
  exact ⟨hE.2, (mem_combinePoints rels _).mp (getD_mem hb)⟩

/-- **A point no longer point extends is not merged.** -/
theorem mergedSelfG (rels : List (RelG Pt)) (p : List Pt) (hp : ∃ r ∈ rels, ∃ tm ∈ r.terms, tm.point = p)
    (hno : ∀ r ∈ rels, ∀ tm ∈ r.terms, p.length < tm.point.length → tm.point.take p.length ≠ p) :
    mergedPointG rels p = p := by
  obtain ⟨b, hb, heq, hE⟩ := mergedPoint_spec rels p hp
  rw [heq]
  obtain ⟨r, hr, tm, htm, hpt⟩ := (mem_combinePoints rels _).mp (getD_mem hb)
  have hlen : ((combinePointsG rels).getD b []).length ≤ p.length := by
    by_contra hc
    exact hno r hr tm htm (by rw [hpt]; omega) (by rw [hpt]; exact hE.2)
  exact (List.take_of_length_le hlen).symm.trans hE.2

end RecGraph.Sim.Gen
