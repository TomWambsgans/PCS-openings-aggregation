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

/-! ## The program's `combine` is `combineG` over nodes -/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1
open Gen (TermG RelG CombG combineG mineG cOuter cInner cInner_eq cpStep cIdx keptOf renumberOf mergedOf
  longestList longestOfG combineG_eq)

/-- An optional pair, related. -/
def OptRel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

/-- `longestOfS` is `longestOfG` over nodes. -/
theorem longestOfS_eq : Pi1.longestOfS = longestOfG (Pt := Nat) := rfl

section CombineSim

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **A program term against a term over nodes**: the same column, point (its nodes) and twist, the coefficient
represented. -/
def RpTermN (st : RecState) (t : TermS) (u : TermG Nat) : Prop :=
  t.column = u.column ∧ t.point = u.point ∧ t.twist = u.twist ∧ Rp π iv publicInput stream st t.coefficient u.coefficient

/-- A program relation against a relation over nodes. -/
def RpRelN (st : RecState) (r : RelationS) (u : RelG Nat) : Prop :=
  List.Forall₂ (RpTermN π iv publicInput stream st) r.terms u.terms ∧ Rp π iv publicInput stream st r.value u.value

/-- A combined term: the same column, point index and twist, the coefficient represented. -/
def RpTm (st : RecState) (a : Column × ℕ × ℕ × Nat) (b : Column × ℕ × ℕ × E) : Prop :=
  a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 ∧ Rp π iv publicInput stream st a.2.2.2 b.2.2.2

/-- Combined terms, entry by entry. -/
def RpTms (st : RecState) (a : List (Column × ℕ × ℕ × Nat)) (b : List (Column × ℕ × ℕ × E)) : Prop :=
  List.Forall₂ (RpTm π iv publicInput stream st) a b

/-- **A program combined claim against one over nodes**: the same points (nodes), the terms related, the value
represented, the same count of relations. -/
def RpCombN (st : RecState) (cS : CombinedS) (cG : CombG Nat) : Prop :=
  cS.points = cG.points ∧ RpTms π iv publicInput stream st cS.terms cG.terms ∧
    Rp π iv publicInput stream st cS.value cG.value ∧ cS.relations = cG.relations

theorem RpTermN.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {t : TermS} {u : TermG Nat}
    (h : RpTermN π iv publicInput stream st t u) : RpTermN π iv publicInput stream st' t u :=
  ⟨h.1, h.2.1, h.2.2.1, Rp.pgrow hg hs h.2.2.2⟩

theorem RpRelN.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {r : RelationS} {u : RelG Nat}
    (h : RpRelN π iv publicInput stream st r u) : RpRelN π iv publicInput stream st' r u :=
  ⟨h.1.imp fun _ _ h ↦ RpTermN.pgrow π iv publicInput stream hg hs h, Rp.pgrow hg hs h.2⟩

theorem RpTm.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {a : Column × ℕ × ℕ × Nat}
    {b : Column × ℕ × ℕ × E} (h : RpTm π iv publicInput stream st a b) : RpTm π iv publicInput stream st' a b :=
  ⟨h.1, h.2.1, h.2.2.1, Rp.pgrow hg hs h.2.2.2⟩

theorem RpTms.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {a : List (Column × ℕ × ℕ × Nat)}
    {b : List (Column × ℕ × ℕ × E)} (h : RpTms π iv publicInput stream st a b) :
    RpTms π iv publicInput stream st' a b :=
  List.Forall₂.imp (fun _ _ h ↦ RpTm.pgrow π iv publicInput stream hg hs h) h

theorem RpRelN.commitment {st : RecState} {r : RelationS} {u : RelG Nat} (h : RpRelN π iv publicInput stream st r u) :
    r.commitment = u.commitment := by
  obtain ⟨rt, rv⟩ := r
  obtain ⟨ut, uv⟩ := u
  obtain ⟨ht, -⟩ := h
  unfold RelationS.commitment RelG.commitment
  cases ht with
  | nil => rfl
  | cons h1 _ => exact congrArg Column.commitment h1.1

theorem forall₂_filter_commitment {st : RecState} (c : Commitment) :
    ∀ {rs : List RelationS} {us : List (RelG Nat)}, List.Forall₂ (RpRelN π iv publicInput stream st) rs us →
      List.Forall₂ (RpRelN π iv publicInput stream st) (rs.filter (·.commitment == c)) (us.filter (·.commitment == c))
  | _, _, .nil => .nil
  | _, _, .cons (a := r) (b := u) h hl => by
    rw [List.filter_cons, List.filter_cons, RpRelN.commitment π iv publicInput stream h]
    by_cases hc : (u.commitment == c) = true
    · simp only [hc, ↓reduceIte]
      exact List.Forall₂.cons h (forall₂_filter_commitment c hl)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact forall₂_filter_commitment c hl

theorem RpTms.keys {st : RecState} {a : List (Column × ℕ × ℕ × Nat)} {b : List (Column × ℕ × ℕ × E)}
    (h : RpTms π iv publicInput stream st a b) :
    a.map (fun x ↦ (x.1, x.2.1, x.2.2.1)) = b.map (fun x ↦ (x.1, x.2.1, x.2.2.1)) := by
  induction h with
  | nil => rfl
  | cons hr _ ih => rw [List.map_cons, List.map_cons, ih, hr.1, hr.2.1, hr.2.2.1]

/-- **`mergeTerm`**: the program's on nodes is `UniStatement`'s. -/
theorem mergeTermS_phc {st : RecState} (hg : Good st) {A : Array (Column × ℕ × ℕ × Nat)}
    {B : Array (Column × ℕ × ℕ × E)} (h : RpTms π iv publicInput stream st A.toList B.toList) (column : Column)
    (p twist : ℕ) {cS : Nat} {c : E} (hc : Rp π iv publicInput stream st cS c) :
    PHc st (Pi1.mergeTermS A column p twist cS) fun A' st' ↦
      RpTms π iv publicInput stream st' A'.toList (mergeTerm B column p twist c).toList := by
  have hkey : A.toList.map (fun x ↦ (x.1, x.2.1, x.2.2.1)) = B.toList.map (fun x ↦ (x.1, x.2.1, x.2.2.1)) :=
    RpTms.keys π iv publicInput stream h
  have hfind : A.findIdx? (fun x : Column × ℕ × ℕ × Nat ↦ x.1 == column && x.2.1 == p && x.2.2.1 == twist) =
      B.findIdx? (fun x : Column × ℕ × ℕ × E ↦ x.1 == column && x.2.1 == p && x.2.2.1 == twist) := by
    rw [arr_findIdx?_toListC, arr_findIdx?_toListC]
    have h1 : A.toList.findIdx? (fun x : Column × ℕ × ℕ × Nat ↦ x.1 == column && x.2.1 == p && x.2.2.1 == twist) =
        (A.toList.map (fun x ↦ (x.1, x.2.1, x.2.2.1))).findIdx?
          (fun k : Column × ℕ × ℕ ↦ k.1 == column && k.2.1 == p && k.2.2 == twist) := by
      rw [List.findIdx?_map]; rfl
    have h2 : B.toList.findIdx? (fun x : Column × ℕ × ℕ × E ↦ x.1 == column && x.2.1 == p && x.2.2.1 == twist) =
        (B.toList.map (fun x ↦ (x.1, x.2.1, x.2.2.1))).findIdx?
          (fun k : Column × ℕ × ℕ ↦ k.1 == column && k.2.1 == p && k.2.2 == twist) := by
      rw [List.findIdx?_map]; rfl
    rw [h1, h2, hkey]
  have hlen : A.toList.length = B.toList.length := List.Forall₂.length_eq h
  unfold Pi1.mergeTermS mergeTerm
  rw [show (fun x : Column × ℕ × ℕ × Nat ↦ match x with | (c, q, k, _) => c == column && q == p && k == twist) =
    (fun x : Column × ℕ × ℕ × Nat ↦ x.1 == column && x.2.1 == p && x.2.2.1 == twist) from rfl,
    show (fun x : Column × ℕ × ℕ × E ↦ match x with | (c, q, k, _) => c == column && q == p && k == twist) =
    (fun x : Column × ℕ × ℕ × E ↦ x.1 == column && x.2.1 == p && x.2.2.1 == twist) from rfl, hfind]
  cases hi : B.findIdx? (fun x : Column × ℕ × ℕ × E ↦ x.1 == column && x.2.1 == p && x.2.2.1 == twist) with
  | none =>
    dsimp only
    refine phc_pure _ hg ?_
    rw [Array.toList_push, Array.toList_push]
    exact List.rel_append h (List.Forall₂.cons ⟨rfl, rfl, rfl, hc⟩ List.Forall₂.nil)
  | some i =>
    obtain ⟨hlt, -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    have hltB : i < B.toList.length := by simpa using hlt
    have hltA : i < A.toList.length := by omega
    have hltA' : i < A.size := by simpa using hltA
    have he : RpTm π iv publicInput stream st (A.getInternal i hltA') (B.toList[i]'hltB) :=
      forall₂_getElemC h i hltA hltB
    dsimp only
    simp only [hltA', ↓reduceDIte]
    generalize A.getInternal i hltA' = x at he
    obtain ⟨c0, q0, k0, v0⟩ := x
    dsimp only
    refine phc_bind (phc_add π iv publicInput stream hg he.2.2.2 hc) fun v st' hs hv ↦ phc_pure _ hs.good ?_
    rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, Array.toList_modify]
    refine forall₂_set_modifyC (RpTms.pgrow π iv publicInput stream hg hs h) i _ _ fun _ ↦ ?_
    generalize B.toList[i] = y at he hv
    obtain ⟨c1, q1, k1, v1⟩ := y
    exact ⟨he.1, he.2.1, he.2.2.1, hv⟩

/-- **The program's `combine` is `combineG` over nodes**: the relations related term by term, `ρ` represented. -/
theorem combine_phc {st : RecState} (hg : Good st) {relsS : List RelationS} {relsG : List (RelG Nat)}
    (hr : List.Forall₂ (RpRelN π iv publicInput stream st) relsS relsG) (c : Commitment) {rhoS : Nat} {ρ : E}
    (hrho : Rp π iv publicInput stream st rhoS ρ) :
    PHc st (Pi1.combine relsS c rhoS) fun out st' ↦
      OptRel (RpCombN π iv publicInput stream st') out (combineG relsG c ρ) := by
  have hm := forall₂_filter_commitment π iv publicInput stream c hr
  have hlen := List.Forall₂.length_eq hm
  rw [combineG_eq]
  unfold Pi1.combine
  dsimp only
  by_cases he : (mineG relsG c).isEmpty = true
  · have he' : (relsS.filter (·.commitment == c)).isEmpty = true := by
      rw [List.isEmpty_iff_length_eq_zero] at he ⊢
      unfold mineG at he
      omega
    rw [ite_eq_left he, ite_eq_left he']
    exact phc_pure none hg trivial
  · have he' : ¬ (relsS.filter (·.commitment == c)).isEmpty = true := by
      rw [List.isEmpty_iff_length_eq_zero] at he ⊢
      unfold mineG at he
      omega
    rw [ite_eq_right he, ite_eq_right he']
    refine phc_bind (phc_zero π iv publicInput stream hg) fun v0 st1 hs1 hv0 ↦ ?_
    refine phc_bind (phc_one π iv publicInput stream hs1.good) fun s0 st2 hs2 hs0 ↦ ?_
    have hm2 := (hm.imp fun _ _ h ↦ RpRelN.pgrow π iv publicInput stream hg hs1 h).imp fun _ _ h ↦
      RpRelN.pgrow π iv publicInput stream hs1.good hs2 h
    have hrho2 := Rp.pgrow hs1.good hs2 (Rp.pgrow hg hs1 hrho)
    refine phc_bind (phc_forIn (fun a a' st ↦ RpRelN π iv publicInput stream st a a')
      (fun _ _ _ _ hg hs h ↦ RpRelN.pgrow π iv publicInput stream hg hs h) _ (cOuter ρ)
      (fun (b : Array (List Nat) × Array (Column × ℕ × ℕ × Nat) × Nat × Nat)
        (acc : Array (List Nat) × Array (Column × ℕ × ℕ × E) × E × E) st ↦
        b.1 = acc.1 ∧ RpTms π iv publicInput stream st b.2.1.toList acc.2.1.toList ∧
          Rp π iv publicInput stream st b.2.2.1 acc.2.2.1 ∧ Rp π iv publicInput stream st b.2.2.2 acc.2.2.2 ∧
          Rp π iv publicInput stream st rhoS ρ) ?_ _ _ st2 (#[], #[], v0, s0) (#[], #[], 0, 1) hs2.good hm2
      ⟨rfl, List.Forall₂.nil, Rp.pgrow hs1.good hs2 hv0, hs0, hrho2⟩) fun res st3 hs3 hR ↦ ?_
    · rintro relation relG ⟨P, T, V, Sc⟩ ⟨P', T', V', Sc'⟩ st hg ⟨hterms, hval⟩ ⟨hP, hT, hV, hSc, hrho⟩
      dsimp only at hP hT hV hSc ⊢
      subst hP
      refine phc_bind (phc_mul π iv publicInput stream hg hSc hval) fun sv st1 hs1 hsv ↦ ?_
      grow [hT, hV, hSc, hrho] with hg hs1
      refine phc_bind (phc_add π iv publicInput stream hs1.good hV hsv) fun v' st2 hs2 hv' ↦ ?_
      grow [hT, hSc, hrho] with hs1.good hs2
      have hterms2 := (hterms.imp fun _ _ h ↦ RpTermN.pgrow π iv publicInput stream hg hs1 h).imp fun _ _ h ↦
        RpTermN.pgrow π iv publicInput stream hs1.good hs2 h
      refine phc_bind (phc_forIn (fun a a' st ↦ RpTermN π iv publicInput stream st a a')
        (fun _ _ _ _ hg hs h ↦ RpTermN.pgrow π iv publicInput stream hg hs h) _ (cInner Sc')
        (fun (b : Array (List Nat) × Array (Column × ℕ × ℕ × Nat))
          (acc : Array (List Nat) × Array (Column × ℕ × ℕ × E)) st ↦
          b.1 = acc.1 ∧ RpTms π iv publicInput stream st b.2.toList acc.2.toList ∧
            Rp π iv publicInput stream st Sc Sc') ?_ _ _ st2 (P, T) (P, T') hs2.good hterms2 ⟨rfl, hT, hSc⟩)
        fun r st3 hs3 hr ↦ ?_
      · rintro t tG ⟨PS, TS⟩ ⟨P, T⟩ st hg ⟨hcol, hpt, htw, hco⟩ ⟨hP, hT, hsc⟩
        dsimp only at hP hT ⊢
        rw [← hP, cInner_eq]
        unfold cpStep cIdx
        rw [hpt, hcol, htw]
        cases hf : PS.findIdx? (· == tG.point) with
        | none =>
          simp only [Option.getD_none, ↓reduceIte]
          refine phc_bind (phc_mul π iv publicInput stream hg hsc hco) fun cS st1 hs1 hcS ↦ ?_
          exact phc_bind (mergeTermS_phc π iv publicInput stream hs1.good (RpTms.pgrow π iv publicInput stream hg hs1 hT)
            tG.column _ tG.twist hcS) fun _ st2 hs2 hT2 ↦
            phc_pure _ hs2.good ⟨_, rfl, rfl, hT2, Rp.pgrow hs1.good hs2 (Rp.pgrow hg hs1 hsc)⟩
        | some q =>
          have hq := (Array.findIdx?_eq_some_iff_getElem.mp hf).1
          simp only [Option.getD_some]
          rw [ite_eq_right (Nat.ne_of_lt hq)]
          refine phc_bind (phc_mul π iv publicInput stream hg hsc hco) fun cS st1 hs1 hcS ↦ ?_
          exact phc_bind (mergeTermS_phc π iv publicInput stream hs1.good (RpTms.pgrow π iv publicInput stream hg hs1 hT)
            tG.column _ tG.twist hcS) fun _ st2 hs2 hT2 ↦
            phc_pure _ hs2.good ⟨_, rfl, rfl, hT2, Rp.pgrow hs1.good hs2 (Rp.pgrow hg hs1 hsc)⟩
      · obtain ⟨hP3, hT3, hSc3⟩ := hr
        grow [hrho] with hs2.good hs3
        have hv3 := Rp.pgrow hs2.good hs3 hv'
        exact phc_bind (phc_mul π iv publicInput stream hs3.good hSc3 hrho) fun _ st4 hs4 hs4' ↦
          phc_pure _ hs4.good ⟨_, rfl, hP3, RpTms.pgrow π iv publicInput stream hs3.good hs4 hT3,
            Rp.pgrow hs3.good hs4 hv3, hs4', Rp.pgrow hs3.good hs4 hrho⟩
    · obtain ⟨hP, hT, hV, -, -⟩ := hR
      have hP' : res.1 = ((mineG relsG c).foldl (cOuter ρ) (#[], #[], 0, 1)).1 := hP
      rw [← Array.forIn_toList]
      refine phc_bind (phc_forIn (fun a a' st ↦ RpTm π iv publicInput stream st a a')
        (fun _ _ _ _ hg hs h ↦ RpTm.pgrow π iv publicInput stream hg hs h) _
        (fun acc (x : Column × ℕ × ℕ × E) ↦ mergeTerm acc x.1 (renumberOf res.1 x.2.1) x.2.2.1 x.2.2.2)
        (fun (b : Array (Column × ℕ × ℕ × Nat)) (acc : Array (Column × ℕ × ℕ × E)) st ↦
          RpTms π iv publicInput stream st b.toList acc.toList) ?_ _ _ st3 #[] #[] hs3.good hT List.Forall₂.nil)
        fun mg st4 hs4 hmg ↦ phc_pure _ hs4.good ?_
      · rintro ⟨c0, p0, k0, v0⟩ ⟨c1, p1, k1, v1⟩ b acc st hg ⟨h1, h2, h3, h4⟩ hb
        dsimp only at h1 h2 h3 h4 ⊢
        subst h1 h2 h3
        exact phc_bind (mergeTermS_phc π iv publicInput stream hg hb _ _ _ h4) fun _ st' hs' h' ↦
          phc_pure _ hs'.good ⟨_, rfl, h'⟩
      · refine ⟨?_, ?_, Rp.pgrow hs3.good hs4 hV, ?_⟩
        · show List.map (fun x ↦ res.1.getD x []) (keptOf res.1) = _
          rw [hP']
        · show RpTms π iv publicInput stream st4 mg.toList (mergedOf _ _).toList
          unfold mergedOf
          rw [← Array.foldl_toList, ← hP']
          exact hmg
        · show (relsS.filter (·.commitment == c)).length = (mineG relsG c).length
          exact hlen

end CombineSim

end RecGraph.Sim

/-! ## The program's `weight_at`, on values -/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- A column's variables, as `partS` reads them: its first limb's. -/
def headVars (L : StackLayout) (column : Column) : ℕ := ((L.limbs column).headD (0, 0, 0)).2.1

/-- **`partS`'s value**: the column's limbs, each its basis entry (`z0` past the basis) times its selector at the
column's variables. -/
def partV (r : List E) (z0 : E) (L : StackLayout) (column : Column) : E :=
  (L.limbs column).foldl (fun s b ↦ s + (if b.1 = 0 then selector r (headVars L column) b.2.2
    else limbBasis.getD b.1 z0 * selector r (headVars L column) b.2.2)) 0

/-- **A row's value**, as the program computes it (`z0` the value of an out-of-range read): the ring-switch
weight, or `Π_(k < len) ((1 + r_k) + p_k)`. -/
def rowW (r map : List E) (z0 : E) (point : List E) (len twist : ℕ) : E :=
  if twist = ringTwist then
    ringWeightValue (point.take len ++ (r.map (1 + ·)).take len ++ map) (point.take len).length
  else (List.range' 0 len).foldl (fun a k ↦ a * ((r.map (1 + ·)).getD k z0 + point.getD k z0)) 1

/-- `q_flock`'s slot `j`'s eight low coordinates' `eq`, as the program computes it. -/
def accW (r : List E) (z0 : E) (j : ℕ) : E :=
  (List.range' 0 8).foldl (fun a b ↦ a * (if j.testBit b = true then r.getD b z0 else (r.map (1 + ·)).getD b z0)) 1

/-- A slot point's instance coordinates' `eq`, as the program computes it. -/
def instW (r point : List E) : E := (point.zip ((r.map (1 + ·)).drop 8)).foldl (fun a xa ↦ a * (xa.2 + xa.1)) 1

/-- **One term's weight as the program reads it** (coefficient `1`). -/
def termP (L : StackLayout) (r map : List E) (z0 : E) (column : Column) (point : List E) (twist : ℕ) : E :=
  match column with
  | .qflockSlot j => accW r z0 j * (instW r point * partV r z0 L .qflock)
  | _ => rowW r map z0 point (headVars L column) twist * partV r z0 L column

/-- **The program's weight, on values**: each term's coefficient times its weight as the program reads it. -/
def progW (C : Combined) (L : StackLayout) (r map : List E) (z0 : E) : E :=
  (C.terms.map fun x ↦ x.2.2.2 * termP L r map z0 x.1 (C.points.getD x.2.1 []) x.2.2.1).sum

/-- A keyed accumulator's reading. -/
def rdK {K : Type} (f : K → E) (V : List (K × E)) : E := (V.map fun e ↦ f e.1 * e.2).sum

/-- The rows' part of a prefix of the terms. -/
def rowT (L : StackLayout) (r : List E) (z0 : E) (f : ℕ × ℕ × ℕ → E) (x : Column × ℕ × ℕ × E) : E :=
  match x.1 with
  | .qflockSlot _ => 0
  | _ => f (x.2.1, headVars L x.1, x.2.2.1) * (x.2.2.2 * partV r z0 L x.1)

/-- The slots' part of a prefix of the terms. -/
def slotT (r : List E) (z0 : E) (g : ℕ → E) (x : Column × ℕ × ℕ × E) : E :=
  match x.1 with
  | .qflockSlot j => g x.2.1 * (x.2.2.2 * accW r z0 j)
  | _ => 0

section WeightSim

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- A combined term's values at `st`. -/
def valTm (st : RecState) (x : Column × ℕ × ℕ × Nat) : Column × ℕ × ℕ × E :=
  (x.1, x.2.1, x.2.2.1, val π iv publicInput stream st x.2.2.2)

/-- **A program combined claim's values** at `st`. -/
def valC (st : RecState) (cS : CombinedS) : Combined :=
  ⟨cS.points.map (·.map (val π iv publicInput stream st)), cS.terms.map (valTm π iv publicInput stream st),
    val π iv publicInput stream st cS.value, cS.relations⟩

/-- **A program combined claim's nodes are held** at `st`. -/
structure HeldC (st : RecState) (cS : CombinedS) : Prop where
  points : ∀ q ∈ cS.points, ∀ i ∈ q, i < st.nodes.size
  terms : ∀ x ∈ cS.terms, x.2.2.2 < st.nodes.size
  value : cS.value < st.nodes.size

/-- Keyed accumulators: the same keys, the values represented. -/
def RpKeyed {K : Type} (st : RecState) (a : List (K × Nat)) (b : List (K × E)) : Prop :=
  List.Forall₂ (fun x y ↦ x.1 = y.1 ∧ Rp π iv publicInput stream st x.2 y.2) a b

theorem RpKeyed.pgrow {K : Type} {st st' : RecState} (hg : Good st) (hs : PStep st st') {a : List (K × Nat)}
    {b : List (K × E)} (h : RpKeyed π iv publicInput stream st a b) : RpKeyed π iv publicInput stream st' a b :=
  List.Forall₂.imp (fun _ _ h ↦ ⟨h.1, Rp.pgrow hg hs h.2⟩) h

theorem HeldC.grows {st st' : RecState} (hgr : Grows st st') {cS : CombinedS} (h : HeldC st cS) : HeldC st' cS :=
  ⟨fun q hq i hi ↦ lt_of_lt_of_le (h.points q hq i hi) (Grows.size_le hgr),
    fun x hx ↦ lt_of_lt_of_le (h.terms x hx) (Grows.size_le hgr), lt_of_lt_of_le h.value (Grows.size_le hgr)⟩

/-- A held node represents its value. -/
theorem rp_val {st : RecState} {i : Nat} (hi : i < st.nodes.size) :
    Rp π iv publicInput stream st i (val π iv publicInput stream st i) := ⟨hi, rfl⟩

theorem rpL_val {st : RecState} {l : List Nat} (hl : ∀ i ∈ l, i < st.nodes.size) :
    RpL π iv publicInput stream st l (l.map (val π iv publicInput stream st)) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    exact List.Forall₂.cons (rp_val π iv publicInput stream (hl a (by simp)))
      (ih fun i hi ↦ hl i (by simp [hi]))

/-- A held claim's values do not change as the state grows. -/
theorem valC_grow {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {cS : CombinedS} (h : HeldC st cS) :
    valC π iv publicInput stream st' cS = valC π iv publicInput stream st cS := by
  unfold valC valTm
  congr 1
  · refine List.map_congr_left fun q hq ↦ List.map_congr_left fun i hi ↦ ?_
    exact val_grow π iv publicInput stream hk hgr (h.points q hq i hi)
  · refine List.map_congr_left fun x hx ↦ ?_
    rw [val_grow π iv publicInput stream hk hgr (h.terms x hx)]
  · exact val_grow π iv publicInput stream hk hgr h.value

/-- An out-of-range read of a node list is node `0`. -/
theorem RpL.getDz {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) {z0 : E}
    (h0 : Rp π iv publicInput stream st 0 z0) (k : Nat) : Rp π iv publicInput stream st (is.getD k 0) (xs.getD k z0) := by
  induction h generalizing k with
  | nil => simpa using h0
  | cons hr _ ih =>
    cases k with
    | zero => simpa using hr
    | succ k => simpa using ih k

theorem RpL.arrGetDz {st : RecState} {a : Array Nat} {xs : List E} (h : RpL π iv publicInput stream st a.toList xs)
    {z0 : E} (h0 : Rp π iv publicInput stream st 0 z0) (k : Nat) :
    Rp π iv publicInput stream st (a.getD k 0) (xs.getD k z0) := by
  have e : a.getD k 0 = a.toList.getD k 0 := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getD_eq_getElem?_getD]
  rw [e]
  exact RpL.getDz π iv publicInput stream h h0 k

theorem forall₂_zipC {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} :
    ∀ {l1 : List α} {m1 : List β} {l2 : List γ} {m2 : List δ}, List.Forall₂ R l1 m1 → List.Forall₂ S l2 m2 →
      List.Forall₂ (fun a b ↦ R a.1 b.1 ∧ S a.2 b.2) (l1.zip l2) (m1.zip m2)
  | _, _, _, _, .nil, _ => by simp
  | _, _, _, _, .cons _ _, .nil => by simp
  | _, _, _, _, .cons h1 t1, .cons h2 t2 => List.Forall₂.cons ⟨h1, h2⟩ (forall₂_zipC t1 t2)

theorem forall₂_getD_nilC {α β : Type} {R : List α → List β → Prop} (hd : R [] []) {l : List (List α)}
    {m : List (List β)} (h : List.Forall₂ R l m) (p : Nat) : R (l.getD p []) (m.getD p []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  exact forall₂_getElem?_getDC h [] [] hd p

/-- **The context of `weight_at`'s loops**: the point `r`, `1 + r`, the basis, node `0`, the claim's points, the map. -/
structure WCtx (st0 st : RecState) (cS : CombinedS) (rS opS basis mapS : List Nat) (r map : List E) (z0 : E) :
    Prop where
  hr : RpL π iv publicInput stream st rS r
  hop : RpL π iv publicInput stream st opS (r.map (1 + ·))
  hbasis : RpL π iv publicInput stream st basis limbBasis
  hz0 : Rp π iv publicInput stream st 0 z0
  hpts : ∀ p, RpL π iv publicInput stream st (cS.points.getD p []) ((valC π iv publicInput stream st0 cS).points.getD p [])
  hmap : RpL π iv publicInput stream st mapS map

theorem WCtx.pgrow {st0 st st' : RecState} (hg : Good st) (hs : PStep st st') {cS : CombinedS}
    {rS opS basis mapS : List Nat} {r map : List E} {z0 : E}
    (h : WCtx π iv publicInput stream st0 st cS rS opS basis mapS r map z0) :
    WCtx π iv publicInput stream st0 st' cS rS opS basis mapS r map z0 :=
  ⟨RpL.pgrow hg hs h.hr, RpL.pgrow hg hs h.hop, RpL.pgrow hg hs h.hbasis, Rp.pgrow hg hs h.hz0,
    fun p ↦ RpL.pgrow hg hs (h.hpts p), RpL.pgrow hg hs h.hmap⟩

/-- `selector` from the bottom: its first factor times the rest. -/
theorem selector_succ (r : List E) (fromVar offset : ℕ) (h : fromVar < r.length) :
    selector r fromVar offset = (if offset.testBit fromVar then r.getD fromVar 0 else 1 + r.getD fromVar 0) *
      selector r (fromVar + 1) offset := by
  unfold selector
  have e : r.length - fromVar = (r.length - (fromVar + 1)) + 1 := by omega
  rw [e, List.range'_succ, List.foldl_cons, UniSound.Ids.Weights.foldl_mul_map,
    UniSound.Ids.Weights.foldl_mul_map, one_mul, one_mul]

theorem selector_ge (r : List E) (fromVar offset : ℕ) (h : r.length ≤ fromVar) : selector r fromVar offset = 1 := by
  unfold selector
  rw [show r.length - fromVar = 0 by omega]
  rfl

/-- **`EqCache::selector`**: the program's is `UniStatement`'s. -/
theorem selectorS_phc {rS : List Nat} {r : List E} (offset : ℕ) :
    ∀ (fuel fromVar : ℕ) (st : RecState), Good st → RpL π iv publicInput stream st rS r →
      r.length - fromVar < fuel →
      PHc st (Pi1.selectorS rS fuel fromVar offset) fun i st' ↦
        Rp π iv publicInput stream st' i (selector r fromVar offset) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro fromVar st hg hr hf
    have hlen := RpL.lengthC π iv publicInput stream hr
    simp only [Pi1.selectorS]
    by_cases hge : fromVar ≥ rS.length
    · rw [ite_eq_left hge, selector_ge r fromVar offset (by omega)]
      exact phc_one π iv publicInput stream hg
    · rw [ite_eq_right hge, selector_succ r fromVar offset (by omega)]
      refine phc_bind (ih (fromVar + 1) st hg hr (by omega)) fun rest st1 hs1 hrest ↦ ?_
      have hrf : Rp π iv publicInput stream st1 (rS.getD fromVar 0) (r.getD fromVar 0) :=
        RpL.getDC π iv publicInput stream (RpL.pgrow hg hs1 hr) (by omega)
      by_cases hb : offset.testBit fromVar = true
      · simp only [hb, ↓reduceIte]
        exact phc_bind (phc_pure _ hs1.good hrf) fun f st2 hs2 hf ↦
          phc_mul π iv publicInput stream hs2.good hf (Rp.pgrow hs1.good hs2 hrest)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact phc_bind (phc_one π iv publicInput stream hs1.good) fun o st2 hs2 ho ↦
          phc_bind (phc_add π iv publicInput stream hs2.good ho (Rp.pgrow hs1.good hs2 hrf)) fun f st3 hs3 hf ↦
          phc_mul π iv publicInput stream hs3.good hf (Rp.pgrow hs2.good hs3 (Rp.pgrow hs1.good hs2 hrest))

/-- **`partS`**: the column's variables, and its part's value. -/
theorem partS_phc {st : RecState} (hg : Good st) {rS basis : List Nat} {r : List E}
    (hr : RpL π iv publicInput stream st rS r) (hb : RpL π iv publicInput stream st basis limbBasis) {z0 : E}
    (h0 : Rp π iv publicInput stream st 0 z0) (L : StackLayout) (column : Column) :
    PHc st (Pi1.partS rS basis L column) fun res st' ↦
      res.1 = headVars L column ∧ Rp π iv publicInput stream st' res.2 (partV r z0 L column) := by
  have hlen := RpL.lengthC π iv publicInput stream hr
  unfold Pi1.partS partV
  refine phc_bind (phc_zero π iv publicInput stream hg) fun s0 st1 hs1 hs0 ↦ ?_
  refine phc_bind (phc_forIn_same (fun _ ↦ True)
    (fun st ↦ RpL π iv publicInput stream st rS r ∧ RpL π iv publicInput stream st basis limbBasis ∧
      Rp π iv publicInput stream st 0 z0)
    (fun _ _ hg hs h ↦ ⟨RpL.pgrow hg hs h.1, RpL.pgrow hg hs h.2.1, Rp.pgrow hg hs h.2.2⟩) _ _
    (fun (b : Nat) (c : E) st ↦ Rp π iv publicInput stream st b c) ?_ _ (fun _ _ ↦ trivial) st1 s0 0 hs1.good
    ⟨RpL.pgrow hg hs1 hr, RpL.pgrow hg hs1 hb, Rp.pgrow hg hs1 h0⟩ hs0) fun res st2 hs2 hres ↦
      phc_pure _ hs2.good ⟨rfl, hres⟩
  rintro ⟨limb, v, off⟩ b c st hg - ⟨hr, hb, h0⟩ hbc
  dsimp only
  refine phc_bind (selectorS_phc π iv publicInput stream off (rS.length + 1) _ st hg hr (by omega))
    fun sel st1 hs1 hsel ↦ ?_
  by_cases hl : limb = 0
  · simp only [hl, ↓reduceIte]
    exact phc_bind (phc_pure _ hs1.good hsel) fun t st2 hs2 ht ↦
      phc_bind (phc_add π iv publicInput stream hs2.good
        (Rp.pgrow hs1.good hs2 (Rp.pgrow hg hs1 hbc)) ht) fun _ st3 hs3 h ↦ phc_pure _ hs3.good ⟨_, rfl, h⟩
  · simp only [hl, ↓reduceIte]
    have hbl := RpL.getDz π iv publicInput stream (RpL.pgrow hg hs1 hb) (Rp.pgrow hg hs1 h0) limb
    exact phc_bind (phc_mul π iv publicInput stream hs1.good hbl hsel) fun t st2 hs2 ht ↦
      phc_bind (phc_add π iv publicInput stream hs2.good
        (Rp.pgrow hs1.good hs2 (Rp.pgrow hg hs1 hbc)) ht) fun _ st3 hs3 h ↦ phc_pure _ hs3.good ⟨_, rfl, h⟩

end WeightSim

end RecGraph.Sim

/-! ## The program's `weight_at` is `progW` -/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

theorem foldl_snocC {α : Type} (l : List α) (a0 : List α) : l.foldl (fun a x ↦ a ++ [x]) a0 = a0 ++ l := by
  induction l generalizing a0 with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.append_assoc, List.singleton_append]

theorem foldl_snoc_oneC (l : List E) (a0 : List E) :
    l.foldl (fun a x ↦ a ++ [1 + x]) a0 = a0 ++ l.map (1 + ·) := by
  induction l generalizing a0 with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.append_assoc, List.singleton_append]

theorem rowT_of_ne {L : StackLayout} {r : List E} {z0 : E} {f : ℕ × ℕ × ℕ → E} {x : Column × ℕ × ℕ × E}
    (hx : ∀ j, x.1 ≠ .qflockSlot j) :
    rowT L r z0 f x = f (x.2.1, headVars L x.1, x.2.2.1) * (x.2.2.2 * partV r z0 L x.1) := by
  unfold rowT
  split
  · rename_i j h
    exact absurd h (hx j)
  · rfl

theorem slotT_of_ne {r : List E} {z0 : E} {g : ℕ → E} {x : Column × ℕ × ℕ × E} (hx : ∀ j, x.1 ≠ .qflockSlot j) :
    slotT r z0 g x = 0 := by
  unfold slotT
  split
  · rename_i j h
    exact absurd h (hx j)
  · rfl

theorem termP_of_ne {L : StackLayout} {r map : List E} {z0 : E} {column : Column} (hx : ∀ j, column ≠ .qflockSlot j)
    (point : List E) (twist : ℕ) :
    termP L r map z0 column point twist = rowW r map z0 point (headVars L column) twist * partV r z0 L column := by
  unfold termP
  split
  · exact absurd rfl (hx _)
  · rfl

theorem rdK_snoc {K : Type} (f : K → E) (V : List (K × E)) (k : K) (c : E) :
    rdK f (V ++ [(k, c)]) = rdK f V + f k * c := by
  simp [rdK, List.map_append, List.sum_append]

theorem rdK_modify {K : Type} (f : K → E) (V : List (K × E)) (i : ℕ) (hi : i < V.length) (c : E) :
    rdK f (V.modify i fun e ↦ (e.1, e.2 + c)) = rdK f V + f V[i].1 * c := by
  unfold rdK
  rw [UniSound.Ids.Weights.sum_map_modify _ _ V i hi]
  ring

/-- **The program's weight, split**: its rows' part and its slots' part. -/
theorem progW_split (C : Combined) (L : StackLayout) (r map : List E) (z0 : E) :
    progW C L r map z0 =
      (C.terms.map (rowT L r z0 fun key ↦ rowW r map z0 (C.points.getD key.1 []) key.2.1 key.2.2)).sum +
        (C.terms.map (slotT r z0 fun p ↦ instW r (C.points.getD p []) * partV r z0 L .qflock)).sum := by
  unfold progW
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
  obtain ⟨col, p, tw, k⟩ := x
  cases col <;> simp only [rowT, slotT, termP] <;> ring

section WeightSim2

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

theorem keyed_get {K : Type} [BEq K] [LawfulBEq K] {st : RecState} {A : Array (K × Nat)} {V : List (K × E)}
    (h : RpKeyed π iv publicInput stream st A.toList V) {k : K} {i : ℕ}
    (hi : A.findIdx? (fun x ↦ x.1 == k) = some i) (d : K × Nat) :
    ∃ hiV : i < V.length, V[i].1 = k ∧ Rp π iv publicInput stream st (A.getD i d).2 V[i].2 := by
  obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
  have hlen : A.toList.length = V.length := List.Forall₂.length_eq h
  have hltA : i < A.toList.length := by simpa using hlt
  have hiV : i < V.length := by omega
  have he := forall₂_getElemC h i hltA hiV
  refine ⟨hiV, ?_, ?_⟩
  · simp only [beq_iff_eq] at hp
    rw [← he.1]
    simpa using hp
  · have hget : A.getD i d = A.toList[i]'hltA := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hltA, Option.getD_some]
    rw [hget]
    exact he.2

theorem keyed_set {K : Type} {st : RecState} {A : Array (K × Nat)} {V : List (K × E)}
    (h : RpKeyed π iv publicInput stream st A.toList V) {k : K} {i : ℕ} (hiV : i < V.length) (hk : V[i].1 = k)
    {v : Nat} {c : E} (hv : Rp π iv publicInput stream st v (V[i].2 + c)) :
    RpKeyed π iv publicInput stream st (A.set! i (k, v)).toList (V.modify i fun e ↦ (e.1, e.2 + c)) := by
  rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  exact forall₂_set_modifyC h i _ _ fun _ ↦ ⟨hk.symm, hv⟩

theorem keyed_push {K : Type} {st : RecState} {A : Array (K × Nat)} {V : List (K × E)}
    (h : RpKeyed π iv publicInput stream st A.toList V) (k : K) {v : Nat} {c : E}
    (hv : Rp π iv publicInput stream st v c) :
    RpKeyed π iv publicInput stream st (A.push (k, v)).toList (V ++ [(k, c)]) := by
  rw [Array.toList_push]
  exact List.rel_append h (List.Forall₂.cons ⟨rfl, hv⟩ List.Forall₂.nil)

/-- The claim's points at the start, represented. -/
theorem pts_val {st : RecState} {cS : CombinedS} (hh : HeldC st cS) (p : ℕ) :
    RpL π iv publicInput stream st (cS.points.getD p []) ((valC π iv publicInput stream st cS).points.getD p []) := by
  show RpL π iv publicInput stream st (cS.points.getD p [])
    ((cS.points.map (·.map (val π iv publicInput stream st))).getD p ([].map (val π iv publicInput stream st)))
  rw [List.getD_map]
  apply rpL_val
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi
  cases hq : cS.points[p]? with
  | none => rw [hq] at hi; simp at hi
  | some q =>
    rw [hq, Option.getD_some] at hi
    exact hh.points q (List.mem_of_getElem? hq) i hi

/-- **`weight_at`**: on a held claim, the program's weight is `progW` of the claim's values (node `0` worth `z0`). -/
theorem weightAt_phc {st : RecState} (hg : Good st) {cS : CombinedS} (hh : HeldC st cS) (L : StackLayout)
    {rS : List Nat} {r : List E} (hr : RpL π iv publicInput stream st rS r) {mapS : List Nat} {map : List E}
    (hm : RpL π iv publicInput stream st mapS map) {z0 : E} (h0 : Rp π iv publicInput stream st 0 z0) :
    PHc st (Pi1.weightAt cS L rS (some mapS)) fun w st' ↦
      Rp π iv publicInput stream st' w (progW (valC π iv publicInput stream st cS) L r map z0) := by
  unfold Pi1.weightAt
  -- `1 + r`.
  refine phc_bind (phc_forIn (fun a a' st ↦ Rp π iv publicInput stream st a a')
    (fun _ _ _ _ hg hs h ↦ Rp.pgrow hg hs h) _ (fun (l : List E) x ↦ l ++ [1 + x])
    (fun (b : Array Nat) (l : List E) st ↦ RpL π iv publicInput stream st b.toList l) ?_ rS r st #[] [] hg hr
    List.Forall₂.nil) fun opS st1 hs1 hop ↦ ?_
  · intro a a' b l st hg ha hb
    exact phc_bind (phc_one π iv publicInput stream hg) fun o st1 hs1 ho ↦
      phc_bind (phc_add π iv publicInput stream hs1.good ho (Rp.pgrow hg hs1 ha)) fun s st2 hs2 hs ↦
        phc_pure _ hs2.good ⟨_, rfl, by
          rw [Array.toList_push]
          exact List.rel_append (RpL.pgrow hs1.good hs2 (RpL.pgrow hg hs1 hb)) (List.Forall₂.cons hs List.Forall₂.nil)⟩
  rw [foldl_snoc_oneC, List.nil_append] at hop
  -- The basis.
  refine phc_bind (phc_const π iv publicInput stream hs1.good _) fun b0 st2 hs2 hb0 ↦ ?_
  refine phc_bind (phc_const π iv publicInput stream hs2.good _) fun b1 st3 hs3 hb1 ↦ ?_
  refine phc_bind (phc_const π iv publicInput stream hs3.good _) fun b2 st4 hs4 hb2 ↦ ?_
  have hs04 : PStep st st4 := hs1.trans (hs2.trans (hs3.trans hs4))
  have hg4 := hs4.good
  have ctx : WCtx π iv publicInput stream st st4 cS rS opS.toList [b0, b1, b2] mapS r map z0 :=
    ⟨RpL.pgrow hg hs04 hr,
      RpL.pgrow hs3.good hs4 (RpL.pgrow hs2.good hs3 (RpL.pgrow hs1.good hs2 hop)),
      List.Forall₂.cons (Rp.pgrow hs3.good hs4 (Rp.pgrow hs2.good hs3 hb0))
        (List.Forall₂.cons (Rp.pgrow hs3.good hs4 hb1) (List.Forall₂.cons hb2 List.Forall₂.nil)),
      Rp.pgrow hg hs04 h0, fun p ↦ RpL.pgrow hg hs04 (pts_val π iv publicInput stream hh p), RpL.pgrow hg hs04 hm⟩
  -- The terms, grouped by row and by slot.
  have hterms : List.Forall₂ (fun a a' ↦ (a' = valTm π iv publicInput stream st a ∧
      Rp π iv publicInput stream st4 a.2.2.2 a'.2.2.2) ∧
      WCtx π iv publicInput stream st st4 cS rS opS.toList [b0, b1, b2] mapS r map z0) cS.terms
      (valC π iv publicInput stream st cS).terms := by
    show List.Forall₂ _ cS.terms (cS.terms.map (valTm π iv publicInput stream st))
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro x hx
    exact ⟨⟨rfl, Rp.pgrow hg hs04 (rp_val π iv publicInput stream (hh.terms x hx))⟩, ctx⟩
  refine phc_bind (phc_forIn (fun a a' st' ↦ (a' = valTm π iv publicInput stream st a ∧
      Rp π iv publicInput stream st' a.2.2.2 a'.2.2.2) ∧
      WCtx π iv publicInput stream st st' cS rS opS.toList [b0, b1, b2] mapS r map z0)
    (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, Rp.pgrow hg hs h.1.2⟩, WCtx.pgrow π iv publicInput stream hg hs h.2⟩) _
    (fun (acc : List (Column × ℕ × ℕ × E)) x ↦ acc ++ [x])
    (fun (b : Array ((ℕ × ℕ × ℕ) × Nat) × Array (ℕ × Nat)) (acc : List (Column × ℕ × ℕ × E)) st' ↦
      ∃ V W, RpKeyed π iv publicInput stream st' b.1.toList V ∧ RpKeyed π iv publicInput stream st' b.2.toList W ∧
        (∀ f, rdK f V = (acc.map (rowT L r z0 f)).sum) ∧ (∀ g, rdK g W = (acc.map (slotT r z0 g)).sum))
    ?_ _ _ st4 (#[], #[]) [] hg4 hterms ⟨[], [], List.Forall₂.nil, List.Forall₂.nil, fun _ ↦ rfl, fun _ ↦ rfl⟩)
    fun res st5 hs5 hres ↦ ?_
  · rintro ⟨column, p, twist, coeff⟩ x' ⟨rowsS, slotsS⟩ acc st' hg' ⟨⟨rfl, hco⟩, ctx'⟩ ⟨V, W, hV, hW, hrow, hslot⟩
    dsimp only [valTm] at hco hV hW ⊢
    split
    · rename_i j
      refine phc_bind (phc_one π iv publicInput stream hg') fun a0 st1 hs1 ha0 ↦ ?_
      rw [forIn_range]
      refine phc_bind (phc_forIn_same (fun _ ↦ True)
        (fun s' ↦ WCtx π iv publicInput stream st s' cS rS opS.toList [b0, b1, b2] mapS r map z0) (fun _ _ hg hs h ↦
          WCtx.pgrow π iv publicInput stream hg hs h) _
        (fun a b ↦ a * (if j.testBit b = true then r.getD b z0 else (r.map (1 + ·)).getD b z0))
        (fun (s : Nat) (e : E) st ↦ Rp π iv publicInput stream st s e) ?_ _ (fun _ _ ↦ trivial) st1 a0 1 hs1.good
        (WCtx.pgrow π iv publicInput stream hg' hs1 ctx') ha0) fun accS st2 hs2 hacc ↦ ?_
      · intro b s e st hg _ ctx hse
        by_cases hb : j.testBit b = true
        · simp only [hb, ↓reduceIte]
          exact phc_bind (phc_mul π iv publicInput stream hg hse (RpL.getDz π iv publicInput stream ctx.hr ctx.hz0 b))
            fun _ st' hs' h ↦ phc_pure _ hs'.good ⟨_, rfl, h⟩
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]
          exact phc_bind (phc_mul π iv publicInput stream hg hse
            (RpL.arrGetDz π iv publicInput stream ctx.hop ctx.hz0 b)) fun _ st' hs' h ↦ phc_pure _ hs'.good ⟨_, rfl, h⟩
      have hacc' : Rp π iv publicInput stream st2 accS (accW r z0 j) := hacc
      have hs12 : PStep st' st2 := hs1.trans hs2
      refine phc_bind (phc_mul π iv publicInput stream hs2.good (Rp.pgrow hg' hs12 hco) hacc') fun cv st3 hs3 hcv ↦ ?_
      have hV3 := RpKeyed.pgrow π iv publicInput stream hs2.good hs3 (RpKeyed.pgrow π iv publicInput stream hg' hs12 hV)
      have hW3 := RpKeyed.pgrow π iv publicInput stream hs2.good hs3 (RpKeyed.pgrow π iv publicInput stream hg' hs12 hW)
      have hx1 : ∀ f, rowT L r z0 f (Column.qflockSlot j, p, twist, val π iv publicInput stream st coeff) = 0 :=
        fun _ ↦ rfl
      have hx2 : ∀ g, slotT r z0 g (Column.qflockSlot j, p, twist, val π iv publicInput stream st coeff) =
          g p * (val π iv publicInput stream st coeff * accW r z0 j) := fun _ ↦ rfl
      have hrow' : ∀ f, rdK f V =
          ((acc ++ [(Column.qflockSlot j, p, twist, val π iv publicInput stream st coeff)]).map (rowT L r z0 f)).sum := by
        intro f
        rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx1, add_zero, hrow f]
      cases hf : slotsS.findIdx? (fun x ↦ x.1 == p) with
      | none =>
        refine phc_pure _ hs3.good ⟨_, rfl, V, _, hV3, keyed_push π iv publicInput stream hW3 p hcv, hrow', fun g ↦ ?_⟩
        rw [rdK_snoc, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx2, hslot g]
      | some i =>
        obtain ⟨hiW, hk, hget⟩ := keyed_get π iv publicInput stream hW3 hf (0, 0)
        refine phc_bind (phc_add π iv publicInput stream hs3.good hget hcv) fun v st4 hs4 hv ↦
          phc_pure _ hs4.good ⟨_, rfl, V, _, RpKeyed.pgrow π iv publicInput stream hs3.good hs4 hV3,
            keyed_set π iv publicInput stream (RpKeyed.pgrow π iv publicInput stream hs3.good hs4 hW3) hiW hk hv,
            hrow', fun g ↦ ?_⟩
        rw [rdK_modify _ _ _ hiW, hk, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx2,
          hslot g]
    · rename_i hns
      refine phc_bind (partS_phc π iv publicInput stream hg' ctx'.hr ctx'.hbasis ctx'.hz0 L _) fun vs st1 hs1 hvs ↦ ?_
      obtain ⟨vars, sm⟩ := vs
      obtain ⟨hvars, hsm⟩ := hvs
      dsimp only at hvars hsm ⊢
      subst hvars
      refine phc_bind (phc_mul π iv publicInput stream hs1.good (Rp.pgrow hg' hs1 hco) hsm) fun cv st2 hs2 hcv ↦ ?_
      have hV2 := RpKeyed.pgrow π iv publicInput stream hs1.good hs2 (RpKeyed.pgrow π iv publicInput stream hg' hs1 hV)
      have hW2 := RpKeyed.pgrow π iv publicInput stream hs1.good hs2 (RpKeyed.pgrow π iv publicInput stream hg' hs1 hW)
      have hne : ∀ j, (column, p, twist, val π iv publicInput stream st coeff).1 ≠ .qflockSlot j := fun j h ↦ hns j h
      have hx1 : ∀ f, rowT L r z0 f (column, p, twist, val π iv publicInput stream st coeff) =
          f (p, headVars L column, twist) * (val π iv publicInput stream st coeff * partV r z0 L column) :=
        fun _ ↦ rowT_of_ne hne
      have hx2 : ∀ g, slotT r z0 g (column, p, twist, val π iv publicInput stream st coeff) = 0 :=
        fun _ ↦ slotT_of_ne hne
      have hslot' : ∀ g, rdK g W =
          ((acc ++ [(column, p, twist, val π iv publicInput stream st coeff)]).map (slotT r z0 g)).sum := by
        intro g
        rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx2, add_zero, hslot g]
      cases hf : rowsS.findIdx? (fun x ↦ x.1 == (p, headVars L column, twist)) with
      | none =>
        refine phc_pure _ hs2.good ⟨_, rfl, _, W, keyed_push π iv publicInput stream hV2 _ hcv, hW2, fun f ↦ ?_, hslot'⟩
        rw [rdK_snoc, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx1, hrow f]
      | some i =>
        obtain ⟨hiV, hk, hget⟩ := keyed_get π iv publicInput stream hV2 hf ((0, 0, 0), 0)
        refine phc_bind (phc_add π iv publicInput stream hs2.good hget hcv) fun v st3 hs3 hv ↦
          phc_pure _ hs3.good ⟨_, rfl, _, W,
            keyed_set π iv publicInput stream (RpKeyed.pgrow π iv publicInput stream hs2.good hs3 hV2) hiV hk hv,
            RpKeyed.pgrow π iv publicInput stream hs2.good hs3 hW2, fun f ↦ ?_, hslot'⟩
        rw [rdK_modify _ _ _ hiV, hk, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx1,
          hrow f]
  · obtain ⟨V, W, hV, hW, hrow, hslot⟩ := hres
    rw [foldl_snocC, List.nil_append] at hrow hslot
    have ctx5 := WCtx.pgrow π iv publicInput stream hg4 hs5 ctx
    refine phc_bind (phc_zero π iv publicInput stream hs5.good) fun t0 st6 hs6 ht0 ↦ ?_
    have ctx6 := WCtx.pgrow π iv publicInput stream hs5.good hs6 ctx5
    rw [← Array.forIn_toList]
    refine phc_bind (phc_forIn (fun a a' s ↦ (a.1 = a'.1 ∧ Rp π iv publicInput stream s a.2 a'.2) ∧
        WCtx π iv publicInput stream st s cS rS opS.toList [b0, b1, b2] mapS r map z0)
      (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, Rp.pgrow hg hs h.1.2⟩, WCtx.pgrow π iv publicInput stream hg hs h.2⟩) _
      (fun t (e : (ℕ × ℕ × ℕ) × E) ↦
        t + (fun key : ℕ × ℕ × ℕ ↦ rowW r map z0 ((valC π iv publicInput stream st cS).points.getD key.1 [])
          key.2.1 key.2.2) e.1 * e.2)
      (fun (b : Nat) (a : E) s ↦ Rp π iv publicInput stream s b a) ?_ res.1.toList V st6 t0 0 hs6.good
      ((RpKeyed.pgrow π iv publicInput stream hs5.good hs6 hV).imp fun _ _ h ↦ ⟨h, ctx6⟩) ht0)
      fun t1 st7 hs7 ht1 ↦ ?_
    · rintro ⟨⟨p, len, twist⟩, sm⟩ e' t a s hg ⟨⟨h1, h2⟩, ctx⟩ hta
      dsimp only at h1 h2 ⊢
      rw [← h1]
      by_cases htw : twist = ringTwist
      · rw [ite_eq_left htw]
        have hp := ctx.hpts p
        refine phc_bind (phc_ringWeight π iv publicInput stream hg (RpL.takeC π iv publicInput stream hp len)
          (RpL.takeC π iv publicInput stream ctx.hop len) ctx.hmap) fun row s1 hs1 hrw ↦ ?_
        rw [RpL.lengthC π iv publicInput stream (RpL.takeC π iv publicInput stream hp len)] at hrw
        have hrw' : Rp π iv publicInput stream s1 row
            (rowW r map z0 ((valC π iv publicInput stream st cS).points.getD p []) len twist) := by
          unfold rowW
          rw [ite_eq_left htw]
          exact hrw
        exact phc_bind (phc_mul π iv publicInput stream hs1.good hrw' (Rp.pgrow hg hs1 h2)) fun rs s2 hs2 hrs ↦
          phc_bind (phc_add π iv publicInput stream hs2.good (Rp.pgrow hs1.good hs2 (Rp.pgrow hg hs1 hta)) hrs)
            fun _ s3 hs3 h ↦ phc_pure _ hs3.good ⟨_, rfl, h⟩
      · rw [ite_eq_right htw]
        refine phc_bind (phc_one π iv publicInput stream hg) fun o s1 hs1 ho ↦ ?_
        rw [forIn_range]
        refine phc_bind (phc_forIn_same (fun _ ↦ True)
          (fun s' ↦ WCtx π iv publicInput stream st s' cS rS opS.toList [b0, b1, b2] mapS r map z0)
          (fun _ _ hg hs h ↦ WCtx.pgrow π iv publicInput stream hg hs h) _
          (fun a k ↦ a * ((r.map (1 + ·)).getD k z0 + ((valC π iv publicInput stream st cS).points.getD p []).getD k z0))
          (fun (b : Nat) (c : E) s ↦ Rp π iv publicInput stream s b c) ?_ _ (fun _ _ ↦ trivial) s1 o 1 hs1.good
          (WCtx.pgrow π iv publicInput stream hg hs1 ctx) ho) fun prod s2 hs2 hprod ↦ ?_
        · intro k b c s hg _ ctx hbc
          exact phc_bind (phc_add π iv publicInput stream hg (RpL.arrGetDz π iv publicInput stream ctx.hop ctx.hz0 k)
            (RpL.getDz π iv publicInput stream (ctx.hpts p) ctx.hz0 k)) fun sS s1 hs1 hsS ↦
            phc_bind (phc_mul π iv publicInput stream hs1.good (Rp.pgrow hg hs1 hbc) hsS) fun _ s2 hs2 h ↦
              phc_pure _ hs2.good ⟨_, rfl, h⟩
        · have hrw' : Rp π iv publicInput stream s2 prod
              (rowW r map z0 ((valC π iv publicInput stream st cS).points.getD p []) len twist) := by
            unfold rowW
            rw [ite_eq_right htw]
            exact hprod
          have hs12 : PStep s s2 := hs1.trans hs2
          refine phc_bind (phc_pure (Q := fun i st' ↦ Rp π iv publicInput stream st' i
            (rowW r map z0 ((valC π iv publicInput stream st cS).points.getD p []) len twist)) _ hs2.good hrw')
            fun row s3 hs3 hrow ↦ ?_
          have hs13 : PStep s s3 := hs12.trans hs3
          exact phc_bind (phc_mul π iv publicInput stream hs3.good hrow (Rp.pgrow hg hs13 h2)) fun rs s4 hs4 hrs ↦
            phc_bind (phc_add π iv publicInput stream hs4.good (Rp.pgrow hs3.good hs4 (Rp.pgrow hg hs13 hta)) hrs)
              fun _ s5 hs5 h ↦ phc_pure _ hs5.good ⟨_, rfl, h⟩
    · have ctx7 := WCtx.pgrow π iv publicInput stream hs6.good hs7 ctx6
      dsimp only
      rw [← Array.forIn_toList]
      refine phc_bind (phc_forIn (fun a a' s ↦ (a.1 = a'.1 ∧ Rp π iv publicInput stream s a.2 a'.2) ∧
          WCtx π iv publicInput stream st s cS rS opS.toList [b0, b1, b2] mapS r map z0)
        (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, Rp.pgrow hg hs h.1.2⟩, WCtx.pgrow π iv publicInput stream hg hs h.2⟩) _
        (fun t (e : ℕ × E) ↦
          t + e.2 * instW r ((valC π iv publicInput stream st cS).points.getD e.1 []) * partV r z0 L .qflock)
        (fun (b : Nat) (a : E) s ↦ Rp π iv publicInput stream s b a) ?_ res.2.toList W st7 t1 _ hs7.good
        ((RpKeyed.pgrow π iv publicInput stream hs6.good hs7
            (RpKeyed.pgrow π iv publicInput stream hs5.good hs6 hW)).imp fun _ _ h ↦ ⟨h, ctx7⟩) ht1)
        fun t2 st8 hs8 ht2 ↦ ?_
      · rintro ⟨p, sm⟩ e' t a s hg ⟨⟨h1, h2⟩, ctx⟩ hta
        dsimp only at h1 h2 ⊢
        rw [← h1]
        refine phc_bind (partS_phc π iv publicInput stream hg ctx.hr ctx.hbasis ctx.hz0 L .qflock)
          fun vs s1 hs1 hvs ↦ ?_
        obtain ⟨fst, qf⟩ := vs
        obtain ⟨-, hqf⟩ := hvs
        dsimp only at hqf ⊢
        refine phc_bind (phc_one π iv publicInput stream hs1.good) fun o s2 hs2 ho ↦ ?_
        have ctx2 := WCtx.pgrow π iv publicInput stream hs1.good hs2 (WCtx.pgrow π iv publicInput stream hg hs1 ctx)
        refine phc_bind (phc_forIn (fun a a' s ↦ Rp π iv publicInput stream s a.1 a'.1 ∧
            Rp π iv publicInput stream s a.2 a'.2)
          (fun _ _ _ _ hg hs h ↦ ⟨Rp.pgrow hg hs h.1, Rp.pgrow hg hs h.2⟩) _ (fun a (xa : E × E) ↦ a * (xa.2 + xa.1))
          (fun (b : Nat) (c : E) s ↦ Rp π iv publicInput stream s b c) ?_ _ _ s2 o 1 hs2.good
          (forall₂_zipC (ctx2.hpts p) (RpL.dropC π iv publicInput stream ctx2.hop 8)) ho) fun inst s3 hs3 hinst ↦ ?_
        · rintro ⟨x, a⟩ ⟨x', a''⟩ b c s hg ⟨hx, ha⟩ hbc
          dsimp only at hx ha ⊢
          exact phc_bind (phc_add π iv publicInput stream hg ha hx) fun sS s1 hs1 hsS ↦
            phc_bind (phc_mul π iv publicInput stream hs1.good (Rp.pgrow hg hs1 hbc) hsS) fun _ s2 hs2 h ↦
              phc_pure _ hs2.good ⟨_, rfl, h⟩
        · have hs13 : PStep s s3 := hs1.trans (hs2.trans hs3)
          have hs23 : PStep s1 s3 := hs2.trans hs3
          exact phc_bind (phc_mul π iv publicInput stream hs3.good (Rp.pgrow hg hs13 h2) hinst) fun si s4 hs4 hsi ↦
            phc_bind (phc_mul π iv publicInput stream hs4.good hsi
              (Rp.pgrow hs3.good hs4 (Rp.pgrow hs1.good hs23 hqf))) fun siq s5 hs5 hsiq ↦
              phc_bind (phc_add π iv publicInput stream hs5.good
                (Rp.pgrow hs4.good hs5 (Rp.pgrow hs3.good hs4 (Rp.pgrow hg hs13 hta))) hsiq) fun _ s6 hs6 h ↦
                phc_pure _ hs6.good ⟨_, rfl, h⟩
      · have e1 : W.foldl (fun t (e : ℕ × E) ↦
            t + e.2 * instW r ((valC π iv publicInput stream st cS).points.getD e.1 []) * partV r z0 L .qflock)
            (V.foldl (fun t (e : (ℕ × ℕ × ℕ) × E) ↦
              t + (fun key : ℕ × ℕ × ℕ ↦ rowW r map z0 ((valC π iv publicInput stream st cS).points.getD key.1 [])
                key.2.1 key.2.2) e.1 * e.2) 0) = progW (valC π iv publicInput stream st cS) L r map z0 := by
          have h2 : (W.map fun (e : ℕ × E) ↦
              e.2 * instW r ((valC π iv publicInput stream st cS).points.getD e.1 []) * partV r z0 L .qflock).sum =
              rdK (fun p ↦ instW r ((valC π iv publicInput stream st cS).points.getD p []) * partV r z0 L .qflock) W := by
            unfold rdK
            exact congrArg List.sum (List.map_congr_left fun e _ ↦ by ring)
          rw [UniSound.Ids.Weights.foldl_add_map, UniSound.Ids.Weights.foldl_add_map, zero_add, h2, progW_split,
            ← hrow, ← hslot]
          rfl
        rw [← e1]
        exact phc_pure _ hs8.good ht2

end WeightSim2

end RecGraph.Sim

/-! ## A term's weight as the program reads it is `UniStatement`'s -/

namespace RecGraph.Sim

open LeanVM.Parameters UniStatement
open UniSound.Ids (limbScale)
open UniSound.Ids.Weights (wSum twistPt slotView ringRow zero_ne_ringTwist slotView_of_ne weightAt_single rowEq_eq
  foldl_mul_map foldl_add_map getD_of_take)

/-- **A layout's limbs**: fewer than three, every limb of a column at the column's variables. -/
def LayoutOK (L : StackLayout) : Prop := ∀ col, ∀ b ∈ L.limbs col, b.1 < 3 ∧ b.2.1 = headVars L col

/-- **A term's kind** at a layout (as the verifier's relations have them): untwisted, not a slot, its point of at least
its column's variables; or untwisted, a slot, `q_flock`'s blocks of at least `8` more variables than its point; or
the ring-switch term on a column of at most its point's variables. -/
def TermKind (L : StackLayout) (col : Column) (pt : List E) (tw : ℕ) : Prop :=
  (tw = 0 ∧ (∀ j, col ≠ .qflockSlot j) ∧ ∀ b ∈ L.limbs col, b.2.1 ≤ pt.length) ∨
  (tw = 0 ∧ (∃ j, col = .qflockSlot j) ∧ ∀ b ∈ L.limbs .qflock, 8 + pt.length ≤ b.2.1) ∨
  (tw = ringTwist ∧ (∀ j, col ≠ .qflockSlot j) ∧ ∀ b ∈ L.limbs col, b.2.1 ≤ pt.length)

theorem partV_eq {L : StackLayout} (hL : LayoutOK L) (r : List E) (z0 : E) (col : Column) :
    partV r z0 L col = ((L.limbs col).map fun b ↦ limbScale b.1 * selector r b.2.1 b.2.2).sum := by
  unfold partV
  rw [foldl_add_map, zero_add]
  refine congrArg List.sum (List.map_congr_left fun b hb ↦ ?_)
  obtain ⟨hb3, hbv⟩ := hL col b hb
  rw [← hbv]
  unfold limbScale
  by_cases h0 : b.1 = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    have hl : b.1 < limbBasis.length := by simp [limbBasis]; omega
    rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl]

theorem getD_lt_z {l : List E} {k : ℕ} (hk : k < l.length) (d : E) : l.getD k d = l.getD k 0 := by
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]

theorem opr_getD (r : List E) {k : ℕ} (hk : k < r.length) (d : E) : (r.map (1 + ·)).getD k d = 1 + r.getD k 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk, List.getElem_map]

theorem rowW_plain (r map : List E) (z0 : E) (pt q : List E) (hv : ℕ) (hr : hv ≤ r.length) (hp : hv ≤ pt.length)
    (hq : q.take pt.length = pt) : rowW r map z0 q hv 0 = rowEq pt hv r := by
  have hql : pt.length ≤ q.length := by
    have := congrArg List.length hq
    rw [List.length_take] at this
    omega
  unfold rowW
  rw [ite_eq_right zero_ne_ringTwist, foldl_mul_map, one_mul, rowEq_eq, ← List.range_eq_range']
  refine congrArg List.prod (List.map_congr_left fun k hk ↦ ?_)
  have hk := List.mem_range.mp hk
  rw [opr_getD r (by omega), getD_lt_z (l := q) (by omega) z0, getD_of_take hq (by omega)]
  ring

theorem rowW_ring (r map : List E) (z0 : E) (pt q : List E) (hv : ℕ) (hr : hv ≤ r.length) (hp : hv ≤ pt.length)
    (hq : q.take pt.length = pt) :
    rowW r map z0 q hv ringTwist = Flock.towerWeightAt (pt.take hv) ((r.map (1 + ·)).take hv) map := by
  have hql : pt.length ≤ q.length := by
    have := congrArg List.length hq
    rw [List.length_take] at this
    omega
  have h1 : (q.take hv).length = hv := by rw [List.length_take]; omega
  have h2 : ((r.map (1 + ·)).take hv).length = hv := by rw [List.length_take, List.length_map]; omega
  have hqt : q.take hv = pt.take hv := by rw [← hq, List.take_take, min_eq_left hp]
  unfold rowW ringWeightValue
  rw [ite_eq_left rfl, h1]
  have e3 : (q.take hv ++ (r.map (1 + ·)).take hv ++ map).drop (2 * hv) = map := by
    rw [show 2 * hv = (q.take hv ++ (r.map (1 + ·)).take hv).length by
      rw [List.length_append, h1, h2]; omega]
    exact List.drop_left
  rw [e3, List.append_assoc, List.take_left' h1, List.drop_left' h1, List.take_left' h2, hqt]

theorem zip_foldlC (pt l : List E) (c : E) (h : pt.length ≤ l.length) :
    (pt.zip l).foldl (fun a xa ↦ a * (xa.2 + xa.1)) c =
      c * ((List.range pt.length).map fun k ↦ l.getD k 0 + pt.getD k 0).prod := by
  induction pt generalizing l c with
  | nil => simp
  | cons x pt ih =>
    cases l with
    | nil => simp at h
    | cons y l =>
      rw [List.zip_cons_cons, List.foldl_cons, ih l _ (by simpa using h), List.length_cons, List.range_succ_eq_map,
        List.map_cons, List.prod_cons, List.map_map]
      simp only [Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]
      ring

theorem instW_eq (r pt : List E) (hr : 8 + pt.length ≤ r.length) :
    instW r pt = ((List.range pt.length).map fun k ↦ 1 + pt.getD k 0 + r.getD (8 + k) 0).prod := by
  unfold instW
  rw [zip_foldlC _ _ _ (by rw [List.length_drop, List.length_map]; omega), one_mul]
  refine congrArg List.prod (List.map_congr_left fun k hk ↦ ?_)
  have hk := List.mem_range.mp hk
  have e : ((r.map (1 + ·)).drop 8).getD k 0 = (r.map (1 + ·)).getD (8 + k) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [e, opr_getD r (by omega)]
  ring

theorem accW_eq (r : List E) (z0 : E) (j : ℕ) (hr : 8 ≤ r.length) :
    accW r z0 j = ((List.range 8).map fun k ↦ 1 + bitE j k + r.getD k 0).prod := by
  unfold accW
  rw [foldl_mul_map, one_mul, ← List.range_eq_range']
  refine congrArg List.prod (List.map_congr_left fun k hk ↦ ?_)
  have hk := List.mem_range.mp hk
  have hkr : k < r.length := by omega
  unfold bitE
  by_cases hb : j.testBit k = true
  · simp only [hb, ↓reduceIte]
    rw [getD_lt_z hkr, CharTwo.add_self_eq_zero, zero_add]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [opr_getD r hkr, add_zero]

theorem rowEq_slot (j : ℕ) (pt r : List E) :
    rowEq ((List.range 8).map (bitE j) ++ pt) ((List.range 8).map (bitE j) ++ pt).length r =
      ((List.range 8).map fun k ↦ 1 + bitE j k + r.getD k 0).prod *
        ((List.range pt.length).map fun k ↦ 1 + pt.getD k 0 + r.getD (8 + k) 0).prod := by
  rw [rowEq_eq, List.length_append, List.length_map, List.length_range, List.range_add, List.map_append,
    List.prod_append, List.map_map]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg List.prod (List.map_congr_left fun k hk ↦ ?_)
    have hk := List.mem_range.mp hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hk), List.getElem?_map,
      List.getElem?_range hk]
    rfl
  · refine congrArg List.prod (List.map_congr_left fun k _ ↦ ?_)
    simp only [Function.comp_apply]
    rw [List.getD_eq_getElem?_getD (l := (List.range 8).map (bitE j) ++ pt),
      List.getElem?_append_right (by simp), List.getD_eq_getElem?_getD]
    simp

theorem sum_factorC (l : List (ℕ × ℕ × ℕ)) (r : List E) (X : E) (Y : ℕ × ℕ × ℕ → E) (h : ∀ b ∈ l, Y b = X) :
    X * (l.map fun b ↦ limbScale b.1 * selector r b.2.1 b.2.2).sum =
      (l.map fun b ↦ limbScale b.1 * (Y b * selector r b.2.1 b.2.2)).sum := by
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun b hb ↦ ?_)
  rw [h b hb]
  ring

/-- **A term's weight as the program reads it is `UniStatement`'s**, read at any extension `q` of its point (its point
itself for a slot term), at a point `r` of at least every block's variables. -/
theorem termP_eq {L : StackLayout} (hL : LayoutOK L) (r map : List E) (z0 : E)
    (hr : ∀ col, ∀ b ∈ L.limbs col, b.2.1 ≤ r.length) {col : Column} {pt q : List E} {tw : ℕ}
    (hk : TermKind L col pt tw) (hq : q.take pt.length = pt) (hs : (∃ j, col = .qflockSlot j) → q = pt) :
    termP L r map z0 col q tw = weightAt ⟨[pt], [(col, 0, tw, 1)], 0, 1⟩ L r (some map) := by
  rw [weightAt_single]
  rcases hk with ⟨rfl, hne, hlen⟩ | ⟨rfl, ⟨j, rfl⟩, hlen⟩ | ⟨rfl, hne, hlen⟩
  · rw [termP_of_ne hne, partV_eq hL]
    unfold wSum
    rw [ite_eq_right zero_ne_ringTwist, slotView_of_ne hne]
    dsimp only
    refine sum_factorC _ r _ _ fun b hb ↦ ?_
    obtain ⟨_, hbv⟩ := hL col b hb
    rw [ite_eq_right (lt_irrefl 0)]
    show rowEq pt b.2.1 r = _
    rw [hbv]
    exact (rowW_plain r map z0 pt q _ (hbv ▸ hr col b hb) (hbv ▸ hlen b hb) hq).symm
  · rw [hs ⟨j, rfl⟩]
    simp only [termP]
    unfold wSum
    rw [ite_eq_right zero_ne_ringTwist]
    simp only [slotView]
    rw [partV_eq hL, ← mul_assoc]
    refine sum_factorC _ r _ _ fun b hb ↦ ?_
    have h8 : 8 + pt.length ≤ r.length := (hlen b hb).trans (hr .qflock b hb)
    have hpos : ((List.range 8).map (bitE j) ++ twistPt pt 0).length > 0 := by simp
    simp only [hpos, ↓reduceIte]
    show rowEq ((List.range 8).map (bitE j) ++ pt) ((List.range 8).map (bitE j) ++ pt).length r = _
    rw [rowEq_slot, accW_eq r z0 j (by omega), instW_eq r pt h8]
  · rw [termP_of_ne hne, partV_eq hL]
    unfold wSum
    rw [ite_eq_left rfl]
    refine sum_factorC _ r _ _ fun b hb ↦ ?_
    obtain ⟨_, hbv⟩ := hL col b hb
    show Flock.towerWeightAt (pt.take b.2.1) ((r.map (1 + ·)).take b.2.1) map = _
    rw [hbv]
    exact (rowW_ring r map z0 pt q _ (hbv ▸ hr col b hb) (hbv ▸ hlen b hb) hq).symm

end RecGraph.Sim

/-! ## `combineG`'s points and count -/

namespace RecGraph.Sim.Gen

open LeanVM.Parameters UniStatement

variable {Pt : Type} [DecidableEq Pt]

/-- **A combined claim's points are its relations' terms' points.** -/
theorem combineG_points_mem {rels : List (RelG Pt)} {c : Commitment} {ρ : E} {cG : CombG Pt}
    (h : combineG rels c ρ = some cG) : ∀ q ∈ cG.points, ∃ r ∈ mineG rels c, ∃ tm ∈ r.terms, tm.point = q := by
  rw [combineG_eq] at h
  split at h
  · exact absurd h (by simp)
  · obtain rfl := Option.some.inj h
    intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    have hP : ((mineG rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).1 = combinePointsG (mineG rels c) := by
      rw [cOuter_fold_fst, combinePointsG_eq]
    rw [hP]
    have hk' : k < (combinePointsG (mineG rels c)).size := by
      rw [← hP]
      unfold keptOf at hk
      exact List.mem_range.mp (List.mem_filter.mp hk).1
    exact (mem_combinePoints _ _).mp (getD_mem hk')

/-- A combined claim combines its commitment's relations. -/
theorem combineG_relations {rels : List (RelG Pt)} {c : Commitment} {ρ : E} {cG : CombG Pt}
    (h : combineG rels c ρ = some cG) : cG.relations = (mineG rels c).length := by
  rw [combineG_eq] at h
  split at h
  · exact absurd h (by simp)
  · obtain rfl := Option.some.inj h
    rfl

end RecGraph.Sim.Gen

/-! ## Off the hazard, both claims enter the batch alike -/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1
open Gen (TermG RelG CombG combineG mineG mergedPointG combineEqG mergedPrefixG combineG_points_mem
  combineG_relations)
open UniSound.Ids (mine)

theorem forall₂_mem_leftC {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ a ∈ l, ∃ b ∈ m, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons (b := b) hr hl, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨b, by simp, hr⟩
    · obtain ⟨b', hb', h'⟩ := forall₂_mem_leftC hl a h
      exact ⟨b', by simp [hb'], h'⟩

theorem forall₂_memC {α β : Type} {R : α → β → Prop} {l : List α} {m : List β} (h : List.Forall₂ R l m) :
    List.Forall₂ (fun a b ↦ R a b ∧ a ∈ l ∧ b ∈ m) l m := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hr _ ih =>
    exact List.Forall₂.cons ⟨hr, by simp, by simp⟩
      (ih.imp fun _ _ h ↦ ⟨h.1, by simp [h.2.1], by simp [h.2.2]⟩)

theorem forall₂_filterC {α β : Type} {R : α → β → Prop} (f : α → Bool) (g : β → Bool)
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ R (l.filter f) (m.filter g)
  | _, _, .nil => List.Forall₂.nil
  | _, _, .cons (a := a) (b := b) hr hl => by
    rw [List.filter_cons, List.filter_cons, hfg a b hr]
    by_cases hc : g b = true
    · simp only [hc, ↓reduceIte]
      exact List.Forall₂.cons hr (forall₂_filterC f g hfg hl)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact forall₂_filterC f g hfg hl

theorem sum_map_forall₂C {α β : Type} {R : α → β → Prop} (fa : α → E) (fb : β → E)
    (h : ∀ a b, R a b → fa a = fb b) : ∀ {l : List α} {m : List β}, List.Forall₂ R l m →
      (l.map fa).sum = (m.map fb).sum
  | _, _, .nil => rfl
  | _, _, .cons hr hl => by rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, h _ _ hr,
      sum_map_forall₂C fa fb h hl]

theorem sum_zipIdx_forall₂C {α β : Type} {R : α → β → Prop} (ρ : E) (fa : α → E) (fb : β → E)
    (h : ∀ a b, R a b → fa a = fb b) : ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ n,
      ((l.zipIdx n).map fun ri ↦ ρ ^ ri.2 * fa ri.1).sum = ((m.zipIdx n).map fun ri ↦ ρ ^ ri.2 * fb ri.1).sum
  | _, _, .nil, _ => rfl
  | _, _, .cons hr hl, n => by
    rw [List.zipIdx_cons, List.zipIdx_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, h _ _ hr,
      sum_zipIdx_forall₂C ρ fa fb h hl (n + 1)]

section CombineWeight

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- A program relation over nodes, its coefficients' and value's values at `st`. -/
def toG (st : RecState) (r : RelationS) : RelG Nat :=
  ⟨r.terms.map fun t ↦ ⟨t.column, t.point, t.twist, val π iv publicInput stream st t.coefficient⟩,
    val π iv publicInput stream st r.value⟩

/-- **A relation over nodes against `UniStatement`'s**: the same columns and twists, the points' values the points
(their nodes held), the same coefficients and value. -/
def Corr (st : RecState) (g : RelG Nat) (u : Relation) : Prop :=
  List.Forall₂ (fun (t : TermG Nat) (v : Term) ↦ t.column = v.column ∧ t.twist = v.twist ∧
    t.point.map (val π iv publicInput stream st) = v.point ∧ (∀ i ∈ t.point, i < st.nodes.size) ∧
    t.coefficient = v.coefficient) g.terms u.terms ∧ g.value = u.value

theorem toG_terms {st : RecState} {ts : List TermS} {us : List Term} (h : RpTermsC π iv publicInput stream st ts us) :
    List.Forall₂ (RpTermN π iv publicInput stream st) ts
      (ts.map fun t ↦ (⟨t.column, t.point, t.twist, val π iv publicInput stream st t.coefficient⟩ : TermG Nat)) := by
  unfold RpTermsC at h
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hr _ ih => exact List.Forall₂.cons ⟨rfl, rfl, rfl, rp_val π iv publicInput stream hr.2.2.2.1⟩ ih

theorem toG_corr_terms {st : RecState} {ts : List TermS} {us : List Term}
    (h : RpTermsC π iv publicInput stream st ts us) :
    List.Forall₂ (fun (t : TermG Nat) (v : Term) ↦ t.column = v.column ∧ t.twist = v.twist ∧
      t.point.map (val π iv publicInput stream st) = v.point ∧ (∀ i ∈ t.point, i < st.nodes.size) ∧
      t.coefficient = v.coefficient)
      (ts.map fun t ↦ (⟨t.column, t.point, t.twist, val π iv publicInput stream st t.coefficient⟩ : TermG Nat)) us := by
  unfold RpTermsC at h
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hr _ ih =>
    exact List.Forall₂.cons ⟨hr.1, hr.2.1, RpL.map_valC π iv publicInput stream hr.2.2.1,
      RpL.ltC π iv publicInput stream hr.2.2.1, hr.2.2.2.2⟩ ih

theorem toG_rpRelN {st : RecState} {r : RelationS} {u : Relation} (h : RpRel π iv publicInput stream st r u) :
    RpRelN π iv publicInput stream st r (toG π iv publicInput stream st r) :=
  ⟨toG_terms π iv publicInput stream h.1, rp_val π iv publicInput stream h.2.1⟩

theorem toG_corr {st : RecState} {r : RelationS} {u : Relation} (h : RpRel π iv publicInput stream st r u) :
    Corr π iv publicInput stream st (toG π iv publicInput stream st r) u :=
  ⟨toG_corr_terms π iv publicInput stream h.1, h.2.2⟩

theorem valTm_map {st : RecState} {a : List (Column × ℕ × ℕ × Nat)} {b : List (Column × ℕ × ℕ × E)}
    (h : RpTms π iv publicInput stream st a b) : a.map (valTm π iv publicInput stream st) = b := by
  unfold RpTms at h
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    rw [List.map_cons, ih]
    obtain ⟨h1, h2, h3, h4⟩ := hxy
    have e : valTm π iv publicInput stream st _ = _ := Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4.2))
    rw [e]

theorem Corr.commitment {st : RecState} {g : RelG Nat} {u : Relation} (h : Corr π iv publicInput stream st g u) :
    g.commitment = u.commitment := by
  obtain ⟨gt, gv⟩ := g
  obtain ⟨ut, uv⟩ := u
  obtain ⟨ht, -⟩ := h
  unfold RelG.commitment Relation.commitment
  cases ht with
  | nil => rfl
  | cons h1 _ => exact congrArg Column.commitment h1.1

/-- A kind is kept by an extension of the point (the point itself for a slot term). -/
theorem TermKind.extend {L : StackLayout} {col : Column} {pt q : List E} {tw : ℕ} (hk : TermKind L col pt tw)
    (hq : q.take pt.length = pt) (hs : (∃ j, col = .qflockSlot j) → q = pt) : TermKind L col q tw := by
  have hl : pt.length ≤ q.length := by
    have := congrArg List.length hq
    rw [List.length_take] at this
    omega
  rcases hk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, fun b hb ↦ (h3 b hb).trans hl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, by rw [hs h2]; exact h3⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, fun b hb ↦ (h3 b hb).trans hl⟩)

/-- The batch's view of a combined claim. -/
structure CombRep (st : RecState) (L : StackLayout) (cS : CombinedS) (cb : Combined) : Prop where
  held : HeldC st cS
  value : Rp π iv publicInput stream st cS.value cb.value
  relations : cS.relations = cb.relations
  weight : ∀ (r map : List E) (z0 : E), (∀ col, ∀ b ∈ L.limbs col, b.2.1 ≤ r.length) →
    progW (valC π iv publicInput stream st cS) L r map z0 = weightAt cb L r (some map)

theorem CombRep.grow {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {L : StackLayout} {cS : CombinedS}
    {cb : Combined} (h : CombRep π iv publicInput stream st L cS cb) : CombRep π iv publicInput stream st' L cS cb :=
  ⟨h.held.grows hgr, Rp.grow π iv publicInput stream hk hgr h.value, h.relations, fun r map z0 hr ↦ by
    rw [valC_grow π iv publicInput stream hk hgr h.held]
    exact h.weight r map z0 hr⟩

end CombineWeight

end RecGraph.Sim
