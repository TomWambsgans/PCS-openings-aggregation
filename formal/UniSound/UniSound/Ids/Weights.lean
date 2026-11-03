-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Bridges

/-!
# The batch's algebra, proved

The bridges of `Bridges.lean` about the verifier's `weightAt` and `combine` (`formal/UniStatement`):

* `weightAtLinear`: `weightAt` is linear in its claim's terms;
* `combineEq`: `combine` is the `ρ`-combination at the merged points;
* `termInner`, `slotInner`, `ringInner`: a term's weight on the cube against a zero-extended stack is
  its claim on the column's blocks;
* `mergedPrefix`, `mergedSelf`, `termWExtend`: merging a point into a longer one.

Everything is by generic fold lemmas (by induction); nothing is evaluated. The helpers live in
`UniSound.Ids.Weights`; the eight theorems are `UniSound.Ids.*`, named as their `Prop`s.
-/

namespace UniSound.Ids.Weights

open LeanVM.Parameters UniStatement Finset

/-! ## Generic folds -/

theorem foldl_add_map {α : Type*} (f : α → E) (l : List α) (a : E) :
    l.foldl (fun t x ↦ t + f x) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem foldl_eq_sum_of {α : Type*} (g : E → α → E) (f : α → E) (l : List α) (a : E)
    (h : ∀ t x, x ∈ l → g t x = t + f x) : l.foldl g a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, h a x (by simp), ih _ fun t y hy ↦ h t y (by simp [hy]), List.map_cons,
      List.sum_cons, add_assoc]

theorem foldl_mul_map {α : Type*} (f : α → E) (l : List α) (a : E) :
    l.foldl (fun t x ↦ t * f x) a = a * (l.map f).prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-! ## Twisted points -/

/-- A point's coordinates squared `k` times, as `twistedPoints` builds its `k`-th entry. -/
def twistPt (pt : List E) (k : ℕ) : List E := (fun l : List E ↦ l.map fun x ↦ x * x)^[k] pt

theorem twistedPoints_toList (pt : List E) (m : ℕ) :
    (twistedPoints pt m).toList = (List.range (m + 1)).map (twistPt pt) := by
  unfold twistedPoints
  induction m with
  | zero => simp [twistPt]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.range_succ (n := m + 1), List.map_append]
    have hback : ((List.range m).foldl (fun (acc : Array (List E)) _ ↦
        acc.push ((acc.back?.getD pt).map fun x ↦ x * x)) #[pt]).back?.getD pt = twistPt pt m := by
      rw [← Array.getLast?_toList, ih, List.getLast?_map, List.getLast?_range]
      simp
    simp only [Array.toList_push, ih, hback, List.map_cons, List.map_nil]
    congr 2
    simp only [twistPt]
    rw [Function.iterate_succ_apply']

theorem twistedPoints_getD (pt : List E) (m k : ℕ) (hk : k ≤ m) :
    (twistedPoints pt m).getD k [] = twistPt pt k := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, twistedPoints_toList, List.getElem?_map,
    List.getElem?_range (by omega)]
  rfl

theorem twistPt_eq_map (pt : List E) (k : ℕ) :
    twistPt pt k = pt.map fun x ↦ (fun y : E ↦ y * y)^[k] x := by
  induction k with
  | zero => simp [twistPt]
  | succ k ih =>
    simp only [twistPt] at ih ⊢
    rw [Function.iterate_succ_apply', ih, List.map_map]
    congr 1
    funext x
    simp only [Function.comp_apply]
    rw [Function.iterate_succ_apply']

theorem twistPt_nil (k : ℕ) : twistPt [] k = [] := by
  rw [twistPt_eq_map, List.map_nil]

/-! ## `weightAt` term by term -/

/-- `weightAt`'s view of a term's column at its (twisted) point: `q_flock`'s slot `j` reads `q_flock`
at `(bits(j), point)`, all its coordinates; another column itself at the point, its own variables. -/
def slotView (column : Column) (point : List E) : Column × List E × ℕ :=
  match column with
  | .qflockSlot j =>
    let row := (List.range 8).map (bitE j) ++ point
    (.qflock, row, row.length)
  | _ => (column, point, 0)

/-- The ring-switch row: the tower weight at the point's and `1 + r`'s first `vars` coordinates,
`0` without a map. -/
def ringRow (rm : Option (List E)) (pt r : List E) (vars : ℕ) : E :=
  match rm with
  | some map => Flock.towerWeightAt (pt.take vars) ((r.map (1 + ·)).take vars) map
  | none => 0

/-- `weightAt`'s step on one term (`pt` its point, `point` its twisted point). -/
def wStep (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point : List E) (total : E)
    (column : Column) (twist : ℕ) (coefficient : E) : E :=
  if twist = ringTwist then
    (L.limbs column).foldl (fun total b ↦ total +
      (if b.1 = 0 then coefficient else coefficient * limbBasis.getD b.1 0) *
        (ringRow rm pt r b.2.1 * selector r b.2.1 b.2.2)) total
  else
    (L.limbs (slotView column point).1).foldl (fun total b ↦ total +
      (if b.1 = 0 then coefficient else coefficient * limbBasis.getD b.1 0) *
        (rowEq (slotView column point).2.1
          (if (slotView column point).2.2 > 0 then (slotView column point).2.2 else b.2.1) r *
          selector r b.2.1 b.2.2)) total

/-- **One term's weight**, coefficient `1` (`pt` its point, `point` its twisted point). -/
def wSum (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point : List E) (column : Column)
    (twist : ℕ) : E :=
  if twist = ringTwist then
    ((L.limbs column).map fun b ↦ limbScale b.1 * (ringRow rm pt r b.2.1 * selector r b.2.1 b.2.2)).sum
  else
    ((L.limbs (slotView column point).1).map fun b ↦ limbScale b.1 *
      (rowEq (slotView column point).2.1
        (if (slotView column point).2.2 > 0 then (slotView column point).2.2 else b.2.1) r *
        selector r b.2.1 b.2.2)).sum

/-- `weightAt`'s twists per point. -/
def maxTwistOf (claim : Combined) : Array ℕ :=
  claim.terms.foldl (fun acc x ↦ if x.2.2.1 = ringTwist then acc else acc.modify x.2.1 (max x.2.2.1))
    (Array.replicate claim.points.toArray.size 0)

/-- `weightAt`'s twisted points. -/
def twistedOf (claim : Combined) : Array (Array (List E)) :=
  Array.ofFn (n := claim.points.toArray.size) fun p ↦
    twistedPoints (claim.points.toArray.getD p.val []) ((maxTwistOf claim).getD p.val 0)

theorem weightAt_foldl (claim : Combined) (L : StackLayout) (r : List E) (rm : Option (List E)) :
    weightAt claim L r rm = claim.terms.foldl (fun total x ↦
      wStep L r rm (claim.points.toArray.getD x.2.1 [])
        (((twistedOf claim).getD x.2.1 #[]).getD x.2.2.1 []) total x.1 x.2.2.1 x.2.2.2) 0 := rfl

theorem scale_eq (c : E) (limb : ℕ) :
    (if limb = 0 then c else c * limbBasis.getD limb 0) = c * limbScale limb := by
  unfold limbScale
  split_ifs <;> simp

theorem wStep_eq (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point : List E) (total : E)
    (column : Column) (twist : ℕ) (c : E) :
    wStep L r rm pt point total column twist c = total + c * wSum L r rm pt point column twist := by
  unfold wStep wSum
  split_ifs <;>
  · rw [foldl_add_map, ← List.sum_map_mul_left]
    refine congrArg (total + ·) (congrArg List.sum (List.map_congr_left fun b _ ↦ ?_))
    rw [scale_eq, mul_assoc]

theorem wSum_ring (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point point' : List E)
    (column : Column) : wSum L r rm pt point column ringTwist = wSum L r rm pt point' column ringTwist := by
  simp only [wSum, ite_true]

theorem getD_modify_le (acc : Array ℕ) (p t i : ℕ) : acc.getD i 0 ≤ (acc.modify p (max t)).getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?]
  by_cases hi : i < acc.size
  · rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (by simpa using hi), Array.getElem_modify]
    split_ifs <;> simp
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by simpa using hi)]

theorem le_getD_modify (acc : Array ℕ) (p t : ℕ) (hp : p < acc.size) : t ≤ (acc.modify p (max t)).getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem (by simpa using hp), Array.getElem_modify]
  simp

theorem maxTwist_fold (l : List (Column × ℕ × ℕ × E)) (acc : Array ℕ) :
    (l.foldl (fun acc x ↦ if x.2.2.1 = ringTwist then acc else acc.modify x.2.1 (max x.2.2.1)) acc).size =
        acc.size ∧
      (∀ i, acc.getD i 0 ≤ (l.foldl (fun acc x ↦ if x.2.2.1 = ringTwist then acc
        else acc.modify x.2.1 (max x.2.2.1)) acc).getD i 0) ∧
      ∀ x ∈ l, x.2.2.1 ≠ ringTwist → x.2.1 < acc.size → x.2.2.1 ≤ (l.foldl (fun acc x ↦
        if x.2.2.1 = ringTwist then acc else acc.modify x.2.1 (max x.2.2.1)) acc).getD x.2.1 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons]
    have hsz : (if y.2.2.1 = ringTwist then acc else acc.modify y.2.1 (max y.2.2.1)).size = acc.size := by
      split_ifs <;> simp
    have hle : ∀ i, acc.getD i 0 ≤
        (if y.2.2.1 = ringTwist then acc else acc.modify y.2.1 (max y.2.2.1)).getD i 0 := by
      intro i
      split_ifs
      · exact le_rfl
      · exact getD_modify_le _ _ _ _
    obtain ⟨ih1, ih2, ih3⟩ := ih (if y.2.2.1 = ringTwist then acc else acc.modify y.2.1 (max y.2.2.1))
    refine ⟨ih1.trans hsz, fun i ↦ (hle i).trans (ih2 i), ?_⟩
    intro x hx htw hp
    rcases List.mem_cons.mp hx with rfl | hx
    · refine le_trans ?_ (ih2 x.2.1)
      rw [ite_eq_right htw]
      exact le_getD_modify _ _ _ hp
    · exact ih3 x hx htw (hsz ▸ hp)

theorem ofFn_getD {α : Type*} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) :
    (Array.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split <;> simp

theorem toArray_getD (l : List (List E)) (i : ℕ) : l.toArray.getD i [] = l.getD i [] := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- A term's twisted point is its point twisted `twist` times (`[]` out of range). -/
theorem twistedOf_getD (claim : Combined) (x : Column × ℕ × ℕ × E) (hx : x ∈ claim.terms)
    (htw : x.2.2.1 ≠ ringTwist) :
    ((twistedOf claim).getD x.2.1 #[]).getD x.2.2.1 [] = twistPt (claim.points.getD x.2.1 []) x.2.2.1 := by
  by_cases hp : x.2.1 < claim.points.length
  · have hp' : x.2.1 < claim.points.toArray.size := by simpa using hp
    have hm : x.2.2.1 ≤ (maxTwistOf claim).getD x.2.1 0 :=
      (maxTwist_fold claim.terms (Array.replicate claim.points.toArray.size 0)).2.2 x hx htw
        (by simpa using hp)
    rw [twistedOf, ofFn_getD, dite_eq_left hp']
    show (twistedPoints (claim.points.toArray.getD x.2.1 []) ((maxTwistOf claim).getD x.2.1 0)).getD
      x.2.2.1 [] = _
    rw [twistedPoints_getD _ _ _ hm, toArray_getD]
  · rw [List.getD_eq_default _ _ (by omega), twistPt_nil, twistedOf, ofFn_getD,
      dite_eq_right (by simpa using hp)]
    simp

/-- **A one-term claim's weight.** -/
theorem weightAt_single (L : StackLayout) (r : List E) (rm : Option (List E)) (pt : List E)
    (column : Column) (twist : ℕ) :
    weightAt ⟨[pt], [(column, 0, twist, 1)], 0, 1⟩ L r rm = wSum L r rm pt (twistPt pt twist) column twist := by
  rw [weightAt_foldl, List.foldl_cons, List.foldl_nil, wStep_eq, zero_add, one_mul, toArray_getD]
  by_cases htw : twist = ringTwist
  · subst htw
    exact wSum_ring _ _ _ _ _ _ _
  · rw [twistedOf_getD _ (column, 0, twist, 1) (by simp) htw]
    rfl

/-- `termW` is one term's weight at the cube point. -/
theorem termW_eq (L : StackLayout) (rm : Option (List E)) (V : ℕ) (column : Column) (pt : List E)
    (twist u : ℕ) : termW L rm V column pt twist u = wSum L (bitsE u V) rm pt (twistPt pt twist) column twist :=
  weightAt_single _ _ _ _ _ _

/-- **`weightAt` is linear in its claim's terms.** -/
theorem _root_.UniSound.Ids.weightAtLinear : WeightAtLinear := by
  intro claim L r rm
  rw [weightAt_foldl, foldl_eq_sum_of _ (fun tm ↦ tm.2.2.2 * weightAt ⟨[claim.points.getD tm.2.1 []],
    [(tm.1, 0, tm.2.2.1, 1)], 0, 1⟩ L r rm) _ _ ?_, zero_add]
  intro t x hx
  rw [wStep_eq, weightAt_single, toArray_getD]
  by_cases htw : x.2.2.1 = ringTwist
  · rw [htw, wSum_ring _ _ _ _ _ (twistPt (claim.points.getD x.2.1 []) ringTwist)]
  · rw [twistedOf_getD claim x hx htw]

/-! ## `combine` -/

/-- A combined claim's term: column, point index, twist, coefficient. -/
abbrev Tm := Column × ℕ × ℕ × E

/-- **A reading of terms**: `Σ coefficient · H(column, point index, twist)`. -/
def rd (H : Column → ℕ → ℕ → E) (T : Array Tm) : E :=
  (T.toList.map fun tm ↦ tm.2.2.2 * H tm.1 tm.2.1 tm.2.2.1).sum

theorem sum_map_modify {α : Type*} (g : α → E) (f : α → α) :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length),
      ((l.modify i f).map g).sum = (l.map g).sum + g (f l[i]) - g l[i]
  | [], _, hi => absurd hi (by simp)
  | x :: l, 0, _ => by
    rw [List.modify_zero_cons]
    simp only [List.map_cons, List.sum_cons, List.getElem_cons_zero]
    ring
  | x :: l, i + 1, hi => by
    rw [List.modify_succ_cons]
    simp only [List.map_cons, List.sum_cons, List.getElem_cons_succ]
    rw [sum_map_modify g f l i (by simpa using hi)]
    ring

/-- **`mergeTerm` adds its term to every reading.** -/
theorem rd_mergeTerm (H : Column → ℕ → ℕ → E) (T : Array Tm) (column : Column) (p twist : ℕ) (c : E) :
    rd H (mergeTerm T column p twist c) = rd H T + c * H column p twist := by
  unfold mergeTerm
  split
  · next i h =>
    obtain ⟨hi, hpred, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
    unfold rd
    rw [Array.toList_modify, sum_map_modify _ _ _ _ (by simpa using hi)]
    rw [Array.getElem_toList] at *
    generalize T[i] = x at hpred ⊢
    obtain ⟨c', q, k, v⟩ := x
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpred
    ring
  · simp [rd, Array.toList_push]

theorem rd_empty (H : Column → ℕ → ℕ → E) : rd H #[] = 0 := by simp [rd]

/-- `combine`'s step on one term (scale `s`): the point found or appended, the term merged. -/
def cInner (s : E) (acc : Array (List E) × Array Tm) (t : Term) : Array (List E) × Array Tm :=
  let pp : Array (List E) × ℕ := match acc.1.findIdx? (· == t.point) with
    | some p => (acc.1, p)
    | none => (acc.1.push t.point, acc.1.size)
  (pp.1, mergeTerm acc.2 t.column pp.2 t.twist (s * t.coefficient))

/-- `combine`'s step on one relation. -/
def cOuter (ρ : E) (acc : Array (List E) × Array Tm × E × E) (r : Relation) :
    Array (List E) × Array Tm × E × E :=
  let pt := r.terms.foldl (cInner acc.2.2.2) (acc.1, acc.2.1)
  (pt.1, pt.2, acc.2.2.1 + acc.2.2.2 * r.value, acc.2.2.2 * ρ)

/-- `combine`'s `longest`. -/
def longestList (P : Array (List E)) : List ℕ := (List.range P.size).map (longestOf P)

/-- `combine`'s `kept`. -/
def keptOf (P : Array (List E)) : List ℕ :=
  (List.range P.size).filter fun p ↦ (longestList P).getD p p == p

/-- `combine`'s `renumber`. -/
def renumberOf (P : Array (List E)) (p : ℕ) : ℕ := (keptOf P).idxOf ((longestList P).getD p p)

/-- `combine`'s `merged`. -/
def mergedOf (P : Array (List E)) (T : Array Tm) : Array Tm :=
  T.foldl (fun acc x ↦ mergeTerm acc x.1 (renumberOf P x.2.1) x.2.2.1 x.2.2.2) #[]

theorem combine_eq (rels : List Relation) (c : Commitment) (ρ : E) :
    combine rels c ρ = if (mine rels c).isEmpty then none else
      some ⟨(keptOf ((mine rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).1).map
          (((mine rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).1.getD · []),
        (mergedOf ((mine rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).1
          ((mine rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).2.1).toList,
        ((mine rels c).foldl (cOuter ρ) (#[], #[], 0, 1)).2.2.1, (mine rels c).length⟩ := rfl

/-- `combinePoints`' step on one term. -/
def cpStep (P : Array (List E)) (tm : Term) : Array (List E) :=
  match P.findIdx? (· == tm.point) with
  | some _ => P
  | none => P.push tm.point

/-- `combinePoints`' step on one relation. -/
def cpOuter (P : Array (List E)) (r : Relation) : Array (List E) := r.terms.foldl cpStep P

theorem combinePoints_eq (rels : List Relation) : combinePoints rels = rels.foldl cpOuter #[] := rfl

/-- The index `combine` reads a term's point at. -/
def cIdx (P : Array (List E)) (tm : Term) : ℕ :=
  match P.findIdx? (· == tm.point) with
  | some p => p
  | none => P.size

theorem cInner_eq (s : E) (P : Array (List E)) (T : Array Tm) (t : Term) :
    cInner s (P, T) t = (cpStep P t, mergeTerm T t.column (cIdx P t) t.twist (s * t.coefficient)) := by
  cases h : P.findIdx? (· == t.point) <;> simp only [cInner, cpStep, cIdx, h]

theorem findIdx_some {P : Array (List E)} {pt : List E} {p : ℕ} (h : P.findIdx? (· == pt) = some p) :
    p < P.size ∧ P.getD p [] = pt := by
  obtain ⟨hp, hpred, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨hp, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp, Option.getD_some]
  simpa using hpred

theorem getD_mem {P : Array (List E)} {i : ℕ} (hi : i < P.size) : P.getD i [] ∈ P.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  exact Array.mem_def.mp (Array.getElem_mem hi)

theorem findIdx_of_mem {P : Array (List E)} {pt : List E} (h : pt ∈ P.toList) :
    ∃ i, P.findIdx? (· == pt) = some i := by
  cases hf : P.findIdx? (· == pt) with
  | some i => exact ⟨i, rfl⟩
  | none =>
    have := Array.findIdx?_eq_none_iff.mp hf pt (Array.mem_def.mpr h)
    simp at this

theorem push_getD (P : Array (List E)) (x : List E) (i : ℕ) :
    (P.push x).getD i [] = if i = P.size then x else P.getD i [] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.getD_eq_getD_getElem?]
  split_ifs <;> rfl

/-- `Q` extends `P`. -/
def Ext (Q P : Array (List E)) : Prop := P.size ≤ Q.size ∧ ∀ i < P.size, Q.getD i [] = P.getD i []

theorem Ext.refl (P : Array (List E)) : Ext P P := ⟨le_rfl, fun _ _ ↦ rfl⟩

theorem Ext.trans {R Q P : Array (List E)} (h1 : Ext R Q) (h2 : Ext Q P) : Ext R P :=
  ⟨h2.1.trans h1.1, fun i hi ↦ (h1.2 i (lt_of_lt_of_le hi h2.1)).trans (h2.2 i hi)⟩

theorem cpStep_ext (P : Array (List E)) (t : Term) : Ext (cpStep P t) P := by
  unfold cpStep
  split
  · exact Ext.refl P
  · refine ⟨by simp, fun i hi ↦ ?_⟩
    rw [push_getD, ite_eq_right (by omega)]

theorem cIdx_spec (P : Array (List E)) (t : Term) :
    cIdx P t < (cpStep P t).size ∧ (cpStep P t).getD (cIdx P t) [] = t.point := by
  unfold cIdx cpStep
  split
  · next p h => exact findIdx_some h
  · exact ⟨by simp, by rw [push_getD, ite_eq_left rfl]⟩

theorem mem_cpStep (P : Array (List E)) (t : Term) (x : List E) :
    x ∈ (cpStep P t).toList ↔ x ∈ P.toList ∨ x = t.point := by
  unfold cpStep
  split
  · next p h =>
    obtain ⟨hp, hpt⟩ := findIdx_some h
    refine ⟨Or.inl, fun h' ↦ h'.elim id fun hx ↦ ?_⟩
    rw [hx, ← hpt]
    exact getD_mem hp
  · simp

theorem cpFold_ext (ts : List Term) (P : Array (List E)) : Ext (ts.foldl cpStep P) P := by
  induction ts generalizing P with
  | nil => exact Ext.refl P
  | cons t ts ih => exact (ih (cpStep P t)).trans (cpStep_ext P t)

theorem mem_cpFold (ts : List Term) (P : Array (List E)) (x : List E) :
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

theorem mem_cpOuterFold (l : List Relation) (P : Array (List E)) (x : List E) :
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

/-- **`combinePoints`' points are the terms' points.** -/
theorem mem_combinePoints (rels : List Relation) (x : List E) :
    x ∈ (combinePoints rels).toList ↔ ∃ r ∈ rels, ∃ t ∈ r.terms, t.point = x := by
  rw [combinePoints_eq, mem_cpOuterFold]
  simp

theorem cInner_fold_fst (s : E) (ts : List Term) (P : Array (List E)) (T : Array Tm) :
    (ts.foldl (cInner s) (P, T)).1 = ts.foldl cpStep P := by
  induction ts generalizing P T with
  | nil => rfl
  | cons t ts ih => rw [List.foldl_cons, List.foldl_cons, cInner_eq, ih]

/-- **The inner fold's reading**, for a reading `G` of the indices that reads the final points. -/
theorem cInner_fold_rd (s : E) (F' : Column → List E → ℕ → E) (G : Column → ℕ → ℕ → E) :
    ∀ (ts : List Term) (P : Array (List E)) (T : Array Tm),
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

theorem cOuter_step (ρ : E) (P : Array (List E)) (T : Array Tm) (v s : E) (r : Relation) :
    cOuter ρ (P, T, v, s) r = ((r.terms.foldl (cInner s) (P, T)).1, (r.terms.foldl (cInner s) (P, T)).2,
      v + s * r.value, s * ρ) := rfl

theorem cOuter_fold_fst (ρ : E) : ∀ (l : List Relation) (P : Array (List E)) (T : Array Tm) (v s : E),
    (l.foldl (cOuter ρ) (P, T, v, s)).1 = l.foldl cpOuter P
  | [], _, _, _, _ => rfl
  | r :: l, P, T, v, s => by
    rw [List.foldl_cons, cOuter_step, cOuter_fold_fst ρ l, cInner_fold_fst]
    rfl

theorem cOuter_fold_val (ρ : E) : ∀ (l : List Relation) (n : ℕ) (P : Array (List E)) (T : Array Tm) (v : E),
    (l.foldl (cOuter ρ) (P, T, v, ρ ^ n)).2.2.1 = v + ((l.zipIdx n).map fun ri ↦ ρ ^ ri.2 * ri.1.value).sum
  | [], _, _, _, _ => by simp
  | r :: l, n, P, T, v => by
    rw [List.foldl_cons, cOuter_step, ← pow_succ, cOuter_fold_val ρ l (n + 1), List.zipIdx_cons,
      List.map_cons, List.sum_cons]
    ring

theorem cpOuter_fold_ext (l : List Relation) (P : Array (List E)) : Ext (l.foldl cpOuter P) P := by
  induction l generalizing P with
  | nil => exact Ext.refl P
  | cons r l ih => exact (ih (cpOuter P r)).trans (cpFold_ext r.terms P)

theorem cOuter_fold_rd (ρ : E) (F' : Column → List E → ℕ → E) (G : Column → ℕ → ℕ → E) :
    ∀ (l : List Relation) (n : ℕ) (P : Array (List E)) (T : Array Tm) (v : E),
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

/-! ### `longestOf` -/

/-- `longestOf`'s step. -/
def lStep (P : Array (List E)) (pp : List E) (best q : ℕ) : ℕ :=
  let pq := P.getD q []
  if pq.length ≥ pp.length ∧ pq.take pp.length == pp ∧ pq.length > (P.getD best []).length then q
  else best

theorem longestOf_eq (P : Array (List E)) (p : ℕ) :
    longestOf P p = (List.range P.size).foldl (lStep P (P.getD p [])) p := rfl

/-- `q` extends `pp`. -/
def Extends (pp q : List E) : Prop := pp.length ≤ q.length ∧ q.take pp.length = pp

theorem Extends.refl (pp : List E) : Extends pp pp := ⟨le_rfl, List.take_of_length_le le_rfl⟩

theorem Extends.trans {a b c : List E} (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  have : c.take a.length = (c.take b.length).take a.length := by
    rw [List.take_take, min_eq_left h1.1]
  rw [this, h2.2, h1.2]

theorem lStep_spec (P : Array (List E)) (pp : List E) (best q : ℕ) :
    (Extends pp (P.getD q []) ∧ (P.getD best []).length < (P.getD q []).length ∧ lStep P pp best q = q) ∨
      (¬(Extends pp (P.getD q []) ∧ (P.getD best []).length < (P.getD q []).length) ∧
        lStep P pp best q = best) := by
  unfold lStep Extends
  dsimp only
  split_ifs with h
  · simp only [beq_iff_eq] at h
    exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2, rfl⟩
  · refine Or.inr ⟨fun ⟨⟨a, b⟩, c⟩ ↦ h ⟨a, by simpa using b, c⟩, rfl⟩

theorem lFold_congr (P : Array (List E)) (pp : List E) : ∀ (l : List ℕ) (b1 b2 : ℕ),
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

theorem lFold_inv (P : Array (List E)) (pp : List E) : ∀ (l : List ℕ) (best : ℕ),
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

theorem longestOf_lt (P : Array (List E)) (p : ℕ) (hp : p < P.size) : longestOf P p < P.size := by
  rw [longestOf_eq]
  rcases (lFold_inv P (P.getD p []) (List.range P.size) p).2.2.2 with h | h
  · rw [h]; exact hp
  · exact List.mem_range.mp h

theorem longestOf_ext (P : Array (List E)) (p : ℕ) :
    Extends (P.getD p []) (P.getD (longestOf P p) []) := by
  rw [longestOf_eq]
  exact (lFold_inv P (P.getD p []) (List.range P.size) p).2.1 (Extends.refl _)

theorem longestOf_max (P : Array (List E)) (p : ℕ) : ∀ q < P.size, Extends (P.getD p []) (P.getD q []) →
    (P.getD q []).length ≤ (P.getD (longestOf P p) []).length := by
  intro q hq hE
  rw [longestOf_eq]
  exact (lFold_inv P (P.getD p []) (List.range P.size) p).2.2.1 q (List.mem_range.mpr hq) hE

/-- **`longestOf` is idempotent**: the longest extension has no strictly longer extension. -/
theorem longestOf_idem (P : Array (List E)) (p : ℕ) : longestOf P (longestOf P p) = longestOf P p := by
  rw [longestOf_eq P (longestOf P p)]
  apply foldl_fixed
  intro q hq
  rcases lStep_spec P (P.getD (longestOf P p) []) (longestOf P p) q with ⟨hE, hlt, _⟩ | ⟨_, h⟩
  · exfalso
    have := longestOf_max P p q (List.mem_range.mp hq) ((longestOf_ext P p).trans hE)
    omega
  · exact h

/-- `longestOf` reads only its point. -/
theorem longestOf_congr (P : Array (List E)) (i j : ℕ) (h : P.getD i [] = P.getD j []) :
    P.getD (longestOf P i) [] = P.getD (longestOf P j) [] := by
  rw [longestOf_eq, longestOf_eq, h]
  exact lFold_congr P _ _ i j h

/-- A point of `P` at index `i`, merged: its longest extension. -/
theorem merged_getD (P : Array (List E)) (i : ℕ) (hi : i < P.size) :
    P.getD (longestOf P ((P.findIdx? (· == P.getD i [])).getD 0)) [] = P.getD (longestOf P i) [] := by
  obtain ⟨j, hj⟩ := findIdx_of_mem (getD_mem hi)
  rw [hj, Option.getD_some]
  exact longestOf_congr P j i (findIdx_some hj).2

/-- **The renumbered point is the merged point.** -/
theorem renumber_getD (P : Array (List E)) (i : ℕ) (hi : i < P.size) :
    ((keptOf P).map (P.getD · [])).getD (renumberOf P i) [] = P.getD (longestOf P i) [] := by
  have hL : ∀ j < P.size, (longestList P).getD j j = longestOf P j := by
    intro j hj
    simp [longestList, List.getD_eq_getElem?_getD, hj]
  have hb := longestOf_lt P i hi
  have hmem : longestOf P i ∈ keptOf P := by
    simp only [keptOf, List.mem_filter, List.mem_range, hb, true_and, hL _ hb, longestOf_idem,
      beq_self_eq_true]
  unfold renumberOf
  rw [hL i hi]
  have hlt := List.idxOf_lt_length_iff.mpr hmem
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf]
  rfl

/-- **`combine` is the `ρ`-combination.** -/
theorem _root_.UniSound.Ids.combineEq : CombineEq := by
  intro rels c ρ hne
  have hE : ¬ (mine rels c).isEmpty = true := by simpa [List.isEmpty_iff] using hne
  rw [combine_eq, ite_eq_right hE]
  refine ⟨_, rfl, ?_, ?_⟩
  · have := cOuter_fold_val ρ (mine rels c) 0 #[] #[] 0
    rw [pow_zero, zero_add] at this
    exact this
  · intro F
    set ms := mine rels c with hms
    set res := ms.foldl (cOuter ρ) (#[], #[], 0, 1) with hres
    have hP : ms.foldl cpOuter #[] = res.1 := by rw [hres, cOuter_fold_fst]
    have hC : combinePoints ms = res.1 := (combinePoints_eq ms).trans hP
    have hres0 : res = ms.foldl (cOuter ρ) (#[], #[], 0, ρ ^ 0) := by rw [pow_zero]
    have hG : ∀ i < (ms.foldl cpOuter #[]).size, ∀ col tw,
        F col (((keptOf res.1).map (res.1.getD · [])).getD (renumberOf res.1 i) []) tw =
          F col (mergedPoint ms ((ms.foldl cpOuter #[]).getD i [])) tw := by
      intro i hi col tw
      rw [hP] at hi ⊢
      unfold mergedPoint
      rw [hC, renumber_getD _ _ hi, merged_getD _ _ hi]
    have hrd := cOuter_fold_rd ρ (fun col pt tw ↦ F col (mergedPoint ms pt) tw)
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

/-- A term's merged point: the longest of `combinePoints` extending it. -/
theorem mergedPoint_spec (rels : List Relation) (p : List E)
    (hp : ∃ r ∈ rels, ∃ tm ∈ r.terms, tm.point = p) :
    ∃ b < (combinePoints rels).size, mergedPoint rels p = (combinePoints rels).getD b [] ∧
      Extends p ((combinePoints rels).getD b []) := by
  obtain ⟨i, hi⟩ := findIdx_of_mem ((mem_combinePoints rels p).mpr hp)
  obtain ⟨hlt, hpi⟩ := findIdx_some hi
  refine ⟨longestOf (combinePoints rels) i, longestOf_lt _ _ hlt, ?_, ?_⟩
  · unfold mergedPoint
    rw [hi, Option.getD_some]
  · rw [← hpi]
    exact longestOf_ext _ _

/-- **A merged point extends the point** and is a term's point. -/
theorem _root_.UniSound.Ids.mergedPrefix : MergedPrefix := by
  intro rels p hp
  obtain ⟨b, hb, heq, hE⟩ := mergedPoint_spec rels p hp
  rw [heq]
  exact ⟨hE.2, (mem_combinePoints rels _).mp (getD_mem hb)⟩

/-- **A point no longer point extends is not merged.** -/
theorem _root_.UniSound.Ids.mergedSelf : MergedSelf := by
  intro rels p hp hno
  obtain ⟨b, hb, heq, hE⟩ := mergedPoint_spec rels p hp
  rw [heq]
  obtain ⟨r, hr, tm, htm, hpt⟩ := (mem_combinePoints rels _).mp (getD_mem hb)
  have hlen : ((combinePoints rels).getD b []).length ≤ p.length := by
    by_contra hc
    exact hno r hr tm htm (by rw [hpt]; omega) (by rw [hpt]; exact hE.2)
  exact (List.take_of_length_le hlen).symm.trans hE.2

/-! ## Weights on the cube -/

theorem zero_ne_ringTwist : (0 : ℕ) ≠ ringTwist := by
  unfold ringTwist
  omega

theorem slotView_of_ne {column : Column} (h : ∀ j, column ≠ .qflockSlot j) (point : List E) :
    slotView column point = (column, point, 0) := by
  unfold slotView
  split
  · rename_i j
    exact absurd rfl (h j)
  · rfl

theorem rowEq_eq (point : List E) (len : ℕ) (r : List E) :
    rowEq point len r = ((List.range len).map fun k ↦ 1 + point.getD k 0 + r.getD k 0).prod := by
  unfold rowEq
  rw [foldl_mul_map, one_mul]

theorem rowEq_congr {p1 p2 : List E} {len : ℕ} (r : List E) (h : ∀ k < len, p1.getD k 0 = p2.getD k 0) :
    rowEq p1 len r = rowEq p2 len r := by
  rw [rowEq_eq, rowEq_eq]
  exact congrArg List.prod (List.map_congr_left fun k hk ↦ by rw [h k (List.mem_range.mp hk)])

theorem getD_of_take {l l' : List E} {n k : ℕ} (h : l.take n = l') (hk : k < n) :
    l.getD k 0 = l'.getD k 0 := by
  rw [← h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

theorem twistPt_take (p q : List E) (tw : ℕ) (h : q.take p.length = p) :
    (twistPt q tw).take p.length = twistPt p tw := by
  rw [twistPt_eq_map, twistPt_eq_map, ← List.map_take, h]

/-- **Merging changes no column's weight** but `q_flock`'s slot view's. -/
theorem _root_.UniSound.Ids.termWExtend : TermWExtend := by
  intro L rm V col p q twist u hcol hL hq
  rw [termW_eq, termW_eq]
  unfold wSum
  by_cases htw : twist = ringTwist
  · rw [ite_eq_left htw, ite_eq_left htw]
    refine congrArg List.sum (List.map_congr_left fun b hb ↦ ?_)
    have hv := hL b hb
    have : q.take b.2.1 = p.take b.2.1 := by
      rw [← hq, List.take_take, min_eq_left hv]
    simp only [ringRow, this]
  · rw [ite_eq_right htw, ite_eq_right htw, slotView_of_ne hcol, slotView_of_ne hcol]
    refine congrArg List.sum (List.map_congr_left fun b hb ↦ ?_)
    have hv := hL b hb
    have hlen : (if (0 : ℕ) > 0 then (0 : ℕ) else b.2.1) = b.2.1 := by simp
    dsimp only
    rw [hlen, rowEq_congr (bitsE u V) fun k hk ↦
      getD_of_take (twistPt_take p q twist hq) (lt_of_lt_of_le hk hv)]

theorem bitsE_getD (u n k : ℕ) :
    (bitsE u n).getD k 0 = if k < n then (if u.testBit k then 1 else 0) else 0 := by
  unfold bitsE
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hk : k < n
  · rw [List.getElem?_range hk]
    simp [hk]
  · rw [List.getElem?_eq_none (by simpa using hk)]
    simp [hk]

theorem bitsE_length (u n : ℕ) : (bitsE u n).length = n := by simp [bitsE]

theorem bitsE_take (u n m : ℕ) (h : m ≤ n) : (bitsE u n).take m = bitsE u m := by
  unfold bitsE
  rw [← List.map_take, List.take_range, min_eq_left h]

theorem bitsE_congr (u x n : ℕ) (h : ∀ k < n, u.testBit k = x.testBit k) : bitsE u n = bitsE x n := by
  unfold bitsE
  exact List.map_congr_left fun k hk ↦ by rw [h k (List.mem_range.mp hk)]

theorem blockBase_testBit (off v V x k : ℕ) (hx : x < 2 ^ v) (hk : k < v) :
    (blockBase off v V + x).testBit k = x.testBit k := by
  unfold blockBase
  rw [mul_comm, Nat.testBit_two_pow_mul_add _ hx]
  simp [hk]

theorem list_prod_range (f : ℕ → E) (n : ℕ) :
    ((List.range n).map f).prod = ∏ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
    simp

theorem rowEq_bits (pt : List E) (v V u : ℕ) (hv : v ≤ V) : rowEq pt v (bitsE u V) = cubeEq pt v u := by
  rw [rowEq_eq, cubeEq, list_prod_range]
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  have hk' : k < V := lt_of_lt_of_le (Finset.mem_range.mp hk) hv
  rw [bitsE_getD]
  simp only [hk', ↓reduceIte]

theorem cubeEq_block (pt : List E) (off v V x : ℕ) (hx : x < 2 ^ v) :
    cubeEq pt v (blockBase off v V + x) = cubeEq pt v x := by
  unfold cubeEq
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [blockBase_testBit _ _ _ _ _ hx (Finset.mem_range.mp hk)]

theorem prod_indicator {α : Type*} (P : α → Prop) [DecidablePred P] : ∀ l : List α,
    (l.map fun k ↦ if P k then (1 : E) else 0).prod = if ∀ k ∈ l, P k then 1 else 0
  | [] => by simp
  | k :: l => by
    rw [List.map_cons, List.prod_cons, prod_indicator P l]
    by_cases hk : P k <;> by_cases hl : ∀ k ∈ l, P k <;> simp [hk, hl]

theorem bits_iff (u V v off : ℕ) (hu : u < 2 ^ V) :
    (∀ k ∈ List.range' v (V - v), off.testBit k = u.testBit k) ↔ u / 2 ^ v = off % 2 ^ V / 2 ^ v := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i + v < V
    · rw [h (i + v) (by rw [List.mem_range'_1]; omega)]
      simp [hi]
    · have : u < 2 ^ (i + v) := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow this]
      simp [hi]
  · intro h k hk
    rw [List.mem_range'_1] at hk
    have hkV : k < V := by omega
    have := congrArg (fun n ↦ n.testBit (k - v)) h
    simp only [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.sub_add_cancel hk.1] at this
    rw [this]
    simp [hkV]

/-- **The selector at a cube point**: `1` on the block's aligned range, `0` elsewhere. -/
theorem selector_bits (u V v off : ℕ) (hu : u < 2 ^ V) :
    selector (bitsE u V) v off = if u / 2 ^ v = off % 2 ^ V / 2 ^ v then 1 else 0 := by
  unfold selector
  rw [bitsE_length, foldl_mul_map, one_mul]
  have hf : ∀ k ∈ List.range' v (V - v),
      (if off.testBit k then (bitsE u V).getD k 0 else 1 + (bitsE u V).getD k 0) =
        if off.testBit k = u.testBit k then 1 else 0 := by
    intro k hk
    have hkV : k < V := by rw [List.mem_range'_1] at hk; omega
    rw [bitsE_getD]
    simp only [hkV, ↓reduceIte]
    cases off.testBit k <;> cases u.testBit k <;> simp [CharTwo.add_self_eq_zero]
  rw [List.map_congr_left hf, prod_indicator (fun k ↦ off.testBit k = u.testBit k)]
  have hiff := bits_iff u V v off hu
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

/-- **A block's sum on the cube**: the selector keeps the block's aligned range. -/
theorem block_sum (V v off : ℕ) (hv : v ≤ V) (w S : ℕ → E) :
    ∑ u ∈ range (2 ^ V), w u * selector (bitsE u V) v off * S u =
      ∑ x ∈ range (2 ^ v), w (blockBase off v V + x) * S (blockBase off v V + x) := by
  have hbase : blockBase off v V = off % 2 ^ V / 2 ^ v * 2 ^ v := rfl
  generalize hc : off % 2 ^ V / 2 ^ v = c at hbase
  have hpos : 0 < 2 ^ v := by positivity
  have h1 : ∑ u ∈ range (2 ^ V), w u * selector (bitsE u V) v off * S u =
      ∑ u ∈ (range (2 ^ V)).filter (fun u ↦ u / 2 ^ v = c), w u * S u := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    rw [selector_bits u V v off (Finset.mem_range.mp hu), hc]
    split_ifs <;> ring
  have hcl : c < 2 ^ (V - v) := by
    rw [← hc, Nat.div_lt_iff_lt_mul hpos, ← pow_add, Nat.sub_add_cancel hv]
    exact Nat.mod_lt _ (by positivity)
  have hcV : (c + 1) * 2 ^ v ≤ 2 ^ V := by
    have := Nat.mul_le_mul_right (2 ^ v) hcl
    rwa [← pow_add, Nat.sub_add_cancel hv] at this
  have h2 : (range (2 ^ V)).filter (fun u ↦ u / 2 ^ v = c) =
      (range (2 ^ v)).image (fun x ↦ c * 2 ^ v + x) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨_, huc⟩
      refine ⟨u % 2 ^ v, Nat.mod_lt _ hpos, ?_⟩
      rw [← huc, mul_comm]
      exact Nat.div_add_mod u (2 ^ v)
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · calc c * 2 ^ v + x < c * 2 ^ v + 2 ^ v := Nat.add_lt_add_left hx _
          _ = (c + 1) * 2 ^ v := by ring
          _ ≤ 2 ^ V := hcV
      · rw [mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hx, add_zero]
  rw [h1, h2, Finset.sum_image (fun x _ y _ h ↦ by simpa using h), hbase]

theorem sum_listSum {α : Type*} (s : Finset ℕ) (l : List α) (g : ℕ → α → E) (c : ℕ → E) :
    ∑ u ∈ s, (l.map (g u)).sum * c u = (l.map fun b ↦ ∑ u ∈ s, g u b * c u).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih]

/-- **A weight on the cube against a zero-extended stack**, block by block. -/
theorem cube_sum (V vars : ℕ) (C : Stk) (l : List (ℕ × ℕ × ℕ)) (hl : ∀ b ∈ l, b.2.1 ≤ V)
    (w w' : ℕ × ℕ × ℕ → ℕ → E)
    (hw : ∀ b ∈ l, ∀ x < 2 ^ b.2.1, w b (blockBase b.2.2 b.2.1 V + x) = w' b x) :
    ∑ u ∈ range (2 ^ V), (l.map fun b ↦ limbScale b.1 * (w b u * selector (bitsE u V) b.2.1 b.2.2)).sum *
        stE C vars u =
      (l.map fun b ↦ limbScale b.1 *
        ∑ x ∈ range (2 ^ b.2.1), w' b x * stE C vars (blockBase b.2.2 b.2.1 V + x)).sum := by
  rw [sum_listSum (range (2 ^ V)) l
    (fun u b ↦ limbScale b.1 * (w b u * selector (bitsE u V) b.2.1 b.2.2))]
  refine congrArg List.sum (List.map_congr_left fun b hb ↦ ?_)
  have h1 : ∑ x ∈ range (2 ^ b.2.1), w' b x * stE C vars (blockBase b.2.2 b.2.1 V + x) =
      ∑ x ∈ range (2 ^ b.2.1), w b (blockBase b.2.2 b.2.1 V + x) * stE C vars (blockBase b.2.2 b.2.1 V + x) :=
    Finset.sum_congr rfl fun x hx ↦ by rw [hw b hb x (Finset.mem_range.mp hx)]
  rw [h1, ← block_sum V b.2.1 b.2.2 (hl b hb) (w b) (stE C vars), Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ ↦ by ring

/-- **A column's term on the cube**: its claim on the column's blocks. -/
theorem _root_.UniSound.Ids.termInner : TermInner := by
  intro L rm V C col pt hcol hL
  have h : ∀ u, termW L rm V col pt 0 u = ((L.limbs col).map fun b ↦
      limbScale b.1 * (rowEq pt b.2.1 (bitsE u V) * selector (bitsE u V) b.2.1 b.2.2)).sum := by
    intro u
    rw [termW_eq, wSum, ite_eq_right zero_ne_ringTwist, slotView_of_ne hcol]
    rfl
  have hw : ∀ b ∈ L.limbs col, ∀ x < 2 ^ b.2.1,
      rowEq pt b.2.1 (bitsE (blockBase b.2.2 b.2.1 V + x) V) = cubeEq pt b.2.1 x := by
    intro b hb x hx
    rw [rowEq_bits _ _ _ _ (hL b hb), cubeEq_block _ _ _ _ _ hx]
  simp only [h]
  exact cube_sum V L.vars C (L.limbs col) hL (fun b u ↦ rowEq pt b.2.1 (bitsE u V))
    (fun b x ↦ cubeEq pt b.2.1 x) hw

/-- **`q_flock`'s slot `j` on the cube**: its claim on `q_flock`'s blocks at `(bits(j), pt)`. -/
theorem _root_.UniSound.Ids.slotInner : SlotInner := by
  intro L rm V C j pt hL
  have h : ∀ u, termW L rm V (.qflockSlot j) pt 0 u = ((L.limbs .qflock).map fun b ↦
      limbScale b.1 * (rowEq ((List.range 8).map (bitE j) ++ pt) b.2.1 (bitsE u V) *
        selector (bitsE u V) b.2.1 b.2.2)).sum := by
    intro u
    have h0 : twistPt pt 0 = pt := rfl
    rw [termW_eq, wSum, ite_eq_right zero_ne_ringTwist, h0]
    refine congrArg List.sum (List.map_congr_left fun b hb ↦ ?_)
    have hlen : ((List.range 8).map (bitE j) ++ pt).length = b.2.1 := by
      rw [(hL b hb).1]
      simp
    simp only [slotView, hlen, gt_iff_lt, ite_self]
  have hw : ∀ b ∈ L.limbs .qflock, ∀ x < 2 ^ b.2.1,
      rowEq ((List.range 8).map (bitE j) ++ pt) b.2.1 (bitsE (blockBase b.2.2 b.2.1 V + x) V) =
        cubeEq ((List.range 8).map (bitE j) ++ pt) b.2.1 x := by
    intro b hb x hx
    rw [rowEq_bits _ _ _ _ (hL b hb).2, cubeEq_block _ _ _ _ _ hx]
  simp only [h]
  exact cube_sum V L.vars C (L.limbs .qflock) (fun b hb ↦ (hL b hb).2)
    (fun b u ↦ rowEq ((List.range 8).map (bitE j) ++ pt) b.2.1 (bitsE u V))
    (fun b x ↦ cubeEq ((List.range 8).map (bitE j) ++ pt) b.2.1 x) hw

/-- **The ring-switch term on the cube**: the tower weight at the cube's points of each block. -/
theorem _root_.UniSound.Ids.ringInner : RingInner := by
  intro L map V C pt hL
  have h : ∀ u, termW L (some map) V .qflock pt ringTwist u = ((L.limbs .qflock).map fun b ↦
      limbScale b.1 * (Flock.towerWeightAt (pt.take b.2.1) (((bitsE u V).map (1 + ·)).take b.2.1) map *
        selector (bitsE u V) b.2.1 b.2.2)).sum := by
    intro u
    rw [termW_eq, wSum, ite_eq_left rfl]
    rfl
  have hw : ∀ b ∈ L.limbs .qflock, ∀ x < 2 ^ b.2.1,
      Flock.towerWeightAt (pt.take b.2.1)
          (((bitsE (blockBase b.2.2 b.2.1 V + x) V).map (1 + ·)).take b.2.1) map =
        Flock.towerWeightAt (pt.take b.2.1) ((bitsE x b.2.1).map (1 + ·)) map := by
    intro b hb x hx
    rw [← List.map_take, bitsE_take _ _ _ (hL b hb),
      bitsE_congr _ x _ fun k hk ↦ blockBase_testBit _ _ _ _ _ hx hk]
  simp only [h]
  exact cube_sum V L.vars C (L.limbs .qflock) hL
    (fun b u ↦ Flock.towerWeightAt (pt.take b.2.1) (((bitsE u V).map (1 + ·)).take b.2.1) map)
    (fun b x ↦ Flock.towerWeightAt (pt.take b.2.1) ((bitsE x b.2.1).map (1 + ·)) map) hw

end UniSound.Ids.Weights

/-! ## Axioms -/

/-- info: 'UniSound.Ids.weightAtLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.weightAtLinear

/-- info: 'UniSound.Ids.combineEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.combineEq

/-- info: 'UniSound.Ids.termInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.termInner

/-- info: 'UniSound.Ids.slotInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.slotInner

/-- info: 'UniSound.Ids.ringInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.ringInner

/-- info: 'UniSound.Ids.mergedPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.mergedPrefix

/-- info: 'UniSound.Ids.mergedSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.mergedSelf

/-- info: 'UniSound.Ids.termWExtend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.termWExtend
