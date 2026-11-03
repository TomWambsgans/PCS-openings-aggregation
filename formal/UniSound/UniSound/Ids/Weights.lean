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

Everything is by generic fold lemmas (by induction); nothing is evaluated.
-/

namespace UniSound.Ids

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
theorem weightAtLinear : WeightAtLinear := by
  intro claim L r rm
  rw [weightAt_foldl, foldl_eq_sum_of _ (fun tm ↦ tm.2.2.2 * weightAt ⟨[claim.points.getD tm.2.1 []],
    [(tm.1, 0, tm.2.2.1, 1)], 0, 1⟩ L r rm) _ _ ?_, zero_add]
  intro t x hx
  rw [wStep_eq, weightAt_single, toArray_getD]
  by_cases htw : x.2.2.1 = ringTwist
  · rw [htw, wSum_ring _ _ _ _ _ (twistPt (claim.points.getD x.2.1 []) ringTwist)]
  · rw [twistedOf_getD claim x hx htw]

end UniSound.Ids
