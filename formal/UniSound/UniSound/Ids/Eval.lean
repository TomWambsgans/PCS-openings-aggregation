-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.MainOk
import UniSound.Ids.Weights

/-!
# `DiffsEvalP`: the verifier's relations at `t`, all zero, give every identity at `t`

WIP.
-/

namespace UniSound.Ids.Eval

open LeanVM.Parameters UniStatement Finset Polynomial

/-! ## A relation under an evaluation of its terms -/

/-- **A relation holds** under `ev` (a column's value at a point): `Σ c · ev(col, pt) + value = 0`. -/
def RelHolds (ev : Column → List E → E) (r : Relation) : Prop :=
  (r.terms.map fun tm ↦ tm.coefficient * ev tm.column tm.point).sum + r.value = 0

theorem add_eq_zero_iff' {a b : E} : a + b = 0 ↔ a = b := CharTwo.add_eq_zero

/-- An `equal` relation: the column's value is the relation's. -/
theorem holds_equal {ev : Column → List E → E} {col : Column} {pt : List E} {v : E}
    (h : RelHolds ev (Relation.equal col pt v)) : ev col pt = v := by
  unfold RelHolds Relation.equal term at h
  simpa [add_eq_zero_iff'] using h

/-! ## A term's inner product on the cube is its column's polynomial at `t` -/

/-- **A column's term at a merged point** (not a slot, untwisted): the weight's inner product with the
stack is the column's polynomial at `t`, where the polynomial point's values at `t` are the point's. -/
theorem inner_colPoly (L : StackLayout) (rm : Option (List E)) (V : ℕ) (St : Stk) (col : Column)
    (p q : List E) (t : E) (P : ℕ → Polynomial E)
    (hcol : ∀ j, col ≠ .qflockSlot j) (hq : q.take p.length = p)
    (hb : ∀ b ∈ L.limbs col, b.2.1 ≤ p.length ∧ b.2.1 ≤ V)
    (hP : ∀ b ∈ L.limbs col, ∀ l < b.2.1, (P l).eval t = p.getD l 0) :
    ∑ u ∈ range (2 ^ V), termW L rm V col q 0 u * stE St L.vars u = (colPoly L V St col P).eval t := by
  rw [Finset.sum_congr rfl fun u _ ↦ by
    rw [termWExtend L rm V col p q 0 u hcol (fun b hb' ↦ (hb b hb').1) hq]]
  rw [termInner L rm V St col p hcol (fun b hb' ↦ (hb b hb').2)]
  unfold colPoly
  rw [eval_listSum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun b hbm ↦ ?_)
  simp only [Function.comp_apply, Polynomial.eval_mul, eval_C]
  rw [eval_mlP _ _ _ t p (hP b hbm)]

/-- **`q_flock`'s slot `j` at its own point `y`**: the slot's claim at `(bits(j), y)`. -/
theorem inner_slot (L : StackLayout) (rm : Option (List E)) (V : ℕ) (St : Stk) (j : ℕ) (y : List E)
    (t : E) (Y : ℕ → Polynomial E)
    (hb : ∀ b ∈ L.limbs .qflock, b.2.1 = 8 + y.length ∧ b.2.1 ≤ V)
    (hY : ∀ m < y.length, (Y m).eval t = y.getD m 0) :
    ∑ u ∈ range (2 ^ V), termW L rm V (.qflockSlot j) y 0 u * stE St L.vars u =
      (colPoly L V St .qflock fun l ↦ if l < 8 then Polynomial.C (bitE j l) else Y (l - 8)).eval t := by
  rw [slotInner L rm V St j y hb]
  unfold colPoly
  rw [eval_listSum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun b hbm ↦ ?_)
  simp only [Function.comp_apply, Polynomial.eval_mul, eval_C]
  rw [eval_mlP _ _ _ t ((List.range 8).map (bitE j) ++ y)]
  intro l hl
  rw [(hb b hbm).1] at hl
  by_cases h8 : l < 8
  · rw [ite_eq_left h8, eval_C, List.getD_append _ _ _ _ (by simpa using h8), getD_map_range _ h8]
  · rw [ite_eq_right h8, List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_range,
      hY _ (by omega)]

/-! ## Forms, tuples and `linearise` at `t` -/

/-- A monomial's value at the columns' values `colv` (degree at most two, as `formP` reads it). -/
def monoE (m : List ℕ) (colv : ℕ → E) : E :=
  match m with
  | [] => 1
  | [i] => colv i
  | [i, j] => colv i * colv j
  | _ => 0

/-- A form's value at the columns' values. -/
def formE (f : Form) (colv : ℕ → E) : E := (f.map fun mc ↦ mc.2 * monoE mc.1 colv).sum

/-- A tuple's fingerprint without `β` at the columns' values: `Σ_s weights_s · form_s`. -/
def tupleE (tuple : List Form) (weights : Array E) (colv : ℕ → E) : E :=
  ((tuple.zip (List.range tuple.length)).map fun p ↦ weights.getD p.2 0 * formE p.1 colv).sum

theorem formP_evalE (f : Form) (cols : ℕ → Polynomial E) (t : E) :
    (formP f cols).eval t = formE f fun i ↦ (cols i).eval t := by
  induction f with
  | nil => simp [formP, formE]
  | cons mc f ih =>
    unfold formP formE at *
    rw [List.map_cons, List.sum_cons, Polynomial.eval_add, ih, List.map_cons, List.sum_cons]
    congr 1
    rcases mc with ⟨m, cf⟩
    rcases m with _ | ⟨i, _ | ⟨j, _ | ⟨_, _⟩⟩⟩ <;> simp [monoE, mul_assoc]

theorem tupleP_evalE (tuple : List Form) (weights : Array E) (cols : ℕ → Polynomial E) (t : E) :
    (tupleP tuple weights cols).eval t = tupleE tuple weights fun i ↦ (cols i).eval t := by
  unfold tupleP tupleE
  rw [eval_listSum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun p _ ↦ ?_)
  simp only [Function.comp_apply, Polynomial.eval_mul, eval_C, formP_evalE]

theorem formE_addAt (colv : ℕ → E) (mono : List ℕ) (c : E) :
    ∀ f : Form, formE (f.addAt mono c) colv = formE f colv + c * monoE mono colv
  | [] => by simp [Form.addAt, formE]
  | (k, v) :: rest => by
    unfold Form.addAt
    by_cases hk : (k == mono) = true
    · rw [ite_eq_left hk]
      rw [beq_iff_eq] at hk
      subst hk
      simp only [formE, List.map_cons, List.sum_cons]
      ring
    · rw [ite_eq_right hk]
      by_cases hl : monoLt mono k = true
      · rw [ite_eq_left hl]
        simp only [formE, List.map_cons, List.sum_cons]
        ring
      · rw [ite_eq_right hl]
        have ih := formE_addAt colv mono c rest
        simp only [formE, List.map_cons, List.sum_cons] at ih ⊢
        rw [ih]
        ring

theorem formE_addScaled (colv : ℕ → E) (w : E) :
    ∀ (other f : Form), formE (f.addScaled other w) colv = formE f colv + w * formE other colv
  | [], f => by simp [Form.addScaled, formE]
  | (m, c) :: rest, f => by
    have h : f.addScaled ((m, c) :: rest) w = (f.addAt m (w * c)).addScaled rest w := rfl
    rw [h, formE_addScaled colv w rest, formE_addAt]
    simp only [formE, List.map_cons, List.sum_cons]
    ring

/-- A monomial of `f + w · other` is one of `f`'s or of `other`'s. -/
theorem mono_addAt (mono : List ℕ) (c : E) :
    ∀ (f : Form), ∀ mc ∈ f.addAt mono c, mc.1 = mono ∨ ∃ mc' ∈ f, mc'.1 = mc.1
  | [] => by simp [Form.addAt]
  | (k, v) :: rest => by
    intro mc hmc
    unfold Form.addAt at hmc
    by_cases hk : (k == mono) = true
    · rw [ite_eq_left hk] at hmc
      rcases List.mem_cons.mp hmc with rfl | h
      · exact Or.inr ⟨(k, v), List.mem_cons_self .., rfl⟩
      · exact Or.inr ⟨mc, List.mem_cons_of_mem _ h, rfl⟩
    · rw [ite_eq_right hk] at hmc
      by_cases hl : monoLt mono k = true
      · rw [ite_eq_left hl] at hmc
        rcases List.mem_cons.mp hmc with rfl | h
        · exact Or.inl rfl
        · exact Or.inr ⟨mc, h, rfl⟩
      · rw [ite_eq_right hl] at hmc
        rcases List.mem_cons.mp hmc with rfl | h
        · exact Or.inr ⟨(k, v), List.mem_cons_self .., rfl⟩
        · rcases mono_addAt mono c rest mc h with h1 | ⟨mc', h2, h3⟩
          · exact Or.inl h1
          · exact Or.inr ⟨mc', List.mem_cons_of_mem _ h2, h3⟩

theorem mono_addScaled (w : E) :
    ∀ (other f : Form), ∀ mc ∈ f.addScaled other w, (∃ mc' ∈ f, mc'.1 = mc.1) ∨ ∃ mc' ∈ other, mc'.1 = mc.1
  | [], f => fun mc hmc ↦ Or.inl ⟨mc, hmc, rfl⟩
  | (m, c) :: rest, f => by
    intro mc hmc
    have h : f.addScaled ((m, c) :: rest) w = (f.addAt m (w * c)).addScaled rest w := rfl
    rw [h] at hmc
    rcases mono_addScaled w rest _ mc hmc with ⟨mc', h1, h2⟩ | ⟨mc', h1, h2⟩
    · rcases mono_addAt m (w * c) f mc' h1 with h3 | ⟨mc'', h4, h5⟩
      · exact Or.inr ⟨(m, c), List.mem_cons_self .., h3 ▸ h2⟩
      · exact Or.inl ⟨mc'', h4, h5.trans h2⟩
    · exact Or.inr ⟨mc', List.mem_cons_of_mem _ h1, h2⟩

/-- **The difference's fingerprint** is the pull's plus the push's (tuples of one length). -/
theorem tupleE_difference (pushed pulled : List Form) (weights : Array E) (colv : ℕ → E)
    (hlen : pushed.length = pulled.length) :
    tupleE (difference pushed pulled) weights colv =
      tupleE pushed weights colv + tupleE pulled weights colv := by
  unfold tupleE difference
  have key : ∀ (a b : List Form) (n : ℕ), a.length = b.length →
      ((((a.zip b).map fun p ↦ p.1.addScaled p.2 1).zip (List.range' n (a.zip b).length)).map
          fun p ↦ weights.getD p.2 0 * formE p.1 colv).sum =
        ((a.zip (List.range' n a.length)).map fun p ↦ weights.getD p.2 0 * formE p.1 colv).sum +
          ((b.zip (List.range' n b.length)).map fun p ↦ weights.getD p.2 0 * formE p.1 colv).sum := by
    intro a b
    induction a generalizing b with
    | nil =>
      intro n h
      cases b with
      | nil => simp
      | cons => simp at h
    | cons x a ih =>
      intro n h
      cases b with
      | nil => simp at h
      | cons y b =>
        simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.range'_succ, List.sum_cons]
        rw [ih b (n + 1) (by simpa using h), formE_addScaled]
        ring
  rw [List.range_eq_range', List.range_eq_range', List.range_eq_range', List.length_map]
  exact key pushed pulled 0 hlen

/-- `addTerm` adds its coefficient's term to the terms' value. -/
theorem sum_addTerm (colv : ℕ → E) (i : ℕ) (c : E) (terms : List (ℕ × E)) :
    ((addTerm terms i c).map fun ck ↦ ck.2 * colv ck.1).sum =
      (terms.map fun ck ↦ ck.2 * colv ck.1).sum + c * colv i := by
  unfold addTerm
  split
  next k h =>
    obtain ⟨hk, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
    rw [beq_iff_eq] at hp
    rw [List.modify_eq_take_cons_drop hk]
    conv_rhs => rw [← List.take_append_drop k terms, List.drop_eq_getElem_cons hk]
    generalize terms[k] = x at hp ⊢
    obtain ⟨a, v⟩ := x
    simp only at hp
    subst hp
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    ring
  next h => simp

/-- `linearise`'s inner step, on `(known, terms)`. -/
def linStep (sent : Array (Option E)) (weight : E) (acc : E × List (ℕ × E)) (mc : List ℕ × E) :
    E × List (ℕ × E) :=
  let (known, terms) := acc
  if mc.2 = 0 then acc else
  let c := weight * mc.2
  match mc.1 with
  | [] => (known + c, terms)
  | [i] => match sent.getD i none with
    | some v => (known + c * v, terms)
    | none => (known, addTerm terms i c)
  | [i, j] => match sent.getD i none, sent.getD j none with
    | some a, some b => (known + c * a * b, terms)
    | some a, none => (known, addTerm terms j (c * a))
    | none, some b => (known, addTerm terms i (c * b))
    | none, none => (known, terms)
  | _ => acc

/-- `linearise`'s accumulator's value: what is known plus the terms at the columns' values. -/
def linVal (colv : ℕ → E) (acc : E × List (ℕ × E)) : E :=
  acc.1 + (acc.2.map fun ck ↦ ck.2 * colv ck.1).sum

/-- A degree-two monomial has a sent factor. -/
def SentFactor (sent : Array (Option E)) (m : List ℕ) : Prop :=
  ∀ i j, m = [i, j] → (sent.getD i none).isSome ∨ (sent.getD j none).isSome

theorem linVal_step (sent : Array (Option E)) (colv : ℕ → E)
    (hs : ∀ i v, sent.getD i none = some v → v = colv i) (weight : E) (acc : E × List (ℕ × E))
    (mc : List ℕ × E) (h2 : SentFactor sent mc.1) :
    linVal colv (linStep sent weight acc mc) = linVal colv acc + weight * (mc.2 * monoE mc.1 colv) := by
  obtain ⟨known, terms⟩ := acc
  obtain ⟨m, co⟩ := mc
  unfold linStep
  dsimp only
  by_cases h0 : co = 0
  · rw [ite_eq_left h0, h0]
    ring
  rw [ite_eq_right h0]
  rcases m with _ | ⟨i, _ | ⟨j, _ | ⟨k, m⟩⟩⟩
  · simp only [linVal, monoE]
    ring
  · dsimp only
    rcases hi : sent.getD i none with _ | v
    · simp only [linVal, monoE, sum_addTerm]
      ring
    · simp only [linVal, monoE, hs i v hi]
      ring
  · dsimp only
    rcases hi : sent.getD i none with _ | a <;> rcases hj : sent.getD j none with _ | b
    · rcases h2 i j rfl with h | h
      · rw [hi] at h; exact absurd h (by simp)
      · rw [hj] at h; exact absurd h (by simp)
    · simp only [linVal, monoE, sum_addTerm, hs j b hj]
      ring
    · simp only [linVal, monoE, sum_addTerm, hs i a hi]
      ring
    · simp only [linVal, monoE, hs i a hi, hs j b hj]
      ring
  · simp only [linVal, monoE]
    ring

theorem linVal_form (sent : Array (Option E)) (colv : ℕ → E)
    (hs : ∀ i v, sent.getD i none = some v → v = colv i) (weight : E) :
    ∀ (f : Form) (acc : E × List (ℕ × E)), (∀ mc ∈ f, SentFactor sent mc.1) →
      linVal colv (f.foldl (linStep sent weight) acc) = linVal colv acc + weight * formE f colv
  | [], acc, _ => by simp [formE]
  | mc :: f, acc, h => by
    rw [List.foldl_cons, linVal_form sent colv hs weight f _ fun m hm ↦ h m (List.mem_cons_of_mem _ hm),
      linVal_step sent colv hs weight acc mc (h mc (List.mem_cons_self ..))]
    simp only [formE, List.map_cons, List.sum_cons]
    ring

/-- **`linearise` at `t`**: what the sent values give plus its terms at the columns' values is the
tuple's fingerprint (every degree-two monomial having a sent factor). -/
theorem linearise_spec (tuple : List Form) (weights : Array E) (sent : Array (Option E)) (colv : ℕ → E)
    (hs : ∀ i v, sent.getD i none = some v → v = colv i)
    (h2 : ∀ f ∈ tuple, ∀ mc ∈ f, SentFactor sent mc.1) :
    linVal colv (linearise tuple weights sent) = tupleE tuple weights colv := by
  have hlin : linearise tuple weights sent = (tuple.zip (List.range tuple.length)).foldl
      (fun acc p ↦ p.1.foldl (linStep sent (weights.getD p.2 0)) acc) (0, []) := rfl
  rw [hlin]
  unfold tupleE
  have key : ∀ (l : List (Form × ℕ)) (acc : E × List (ℕ × E)), (∀ p ∈ l, ∀ mc ∈ p.1, SentFactor sent mc.1) →
      linVal colv (l.foldl (fun acc p ↦ p.1.foldl (linStep sent (weights.getD p.2 0)) acc) acc) =
        linVal colv acc + (l.map fun p ↦ weights.getD p.2 0 * formE p.1 colv).sum := by
    intro l
    induction l with
    | nil => intro acc _; simp
    | cons p l ih =>
      intro acc h
      rw [List.foldl_cons, ih _ fun q hq ↦ h q (List.mem_cons_of_mem _ hq),
        linVal_form sent colv hs _ p.1 acc (h p (List.mem_cons_self ..))]
      simp only [List.map_cons, List.sum_cons]
      ring
  rw [key _ _ fun p hp ↦ h2 p.1 (List.of_mem_zip hp).1]
  simp [linVal]

/-! ## A table's part at `t` (`tablePartOf`) -/

/-- **The tables' flushes, as `linearise` reads them**: every sent column is a column of its table, each
pull tuple has its push tuple's length, and every degree-two monomial of a flush has a sent factor. -/
def TablesLin : Prop :=
  ∀ tab ∈ tables, (∀ c ∈ sentColumns tab, c < tab.width) ∧
    ∀ fl ∈ tab.flushes.pull.zip tab.flushes.push, fl.2.length = fl.1.length ∧
      ∀ f ∈ fl.1 ++ fl.2, ∀ mc ∈ f, mc.1.length = 2 →
        mc.1.getD 0 0 ∈ sentColumns tab ∨ mc.1.getD 1 0 ∈ sentColumns tab

theorem mem_zip_range_iff {α : Type} (l : List α) (d : α) (p : α × ℕ) (hp : p ∈ l.zip (List.range l.length)) :
    p.2 < l.length ∧ l.getD p.2 d = p.1 := by
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem hp
  rw [List.length_zip, List.length_range, min_self] at hk
  rw [← he, List.getElem_zip, List.getElem_range]
  exact ⟨hk, List.getD_eq_getElem _ _ hk⟩

theorem getD_set! (A : Array (Option E)) (i c : ℕ) (v : Option E) :
    (A.set! i v).getD c none = if i = c ∧ i < A.size then v else A.getD c none := by
  unfold Array.set!
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getD_eq_getD_getElem?]
  by_cases h1 : i = c
  · subst h1
    by_cases h2 : i < A.size
    · simp [h2]
    · rw [Array.getElem?_eq_none (by omega)]
      simp [h2]
  · simp [h1]

/-- The step of `sentOf`'s fold. -/
def sentStep (vals : List E) (sent : Array (Option E)) (p : ℕ × ℕ) : Array (Option E) :=
  sent.set! p.1 (some (vals.getD p.2 0))

theorem sentOf_eq (tab : Table) (vals : List E) :
    sentOf tab vals = ((sentColumns tab).zip (List.range (sentColumns tab).length)).foldl (sentStep vals)
      (Array.replicate tab.width none) := rfl

theorem sentFold_some (vals : List E) : ∀ (l : List (ℕ × ℕ)) (A : Array (Option E)) (c : ℕ) (v : E),
    (l.foldl (sentStep vals) A).getD c none = some v →
      A.getD c none = some v ∨ ∃ p ∈ l, p.1 = c ∧ v = vals.getD p.2 0
  | [], A, c, v, h => Or.inl h
  | p :: l, A, c, v, h => by
    rw [List.foldl_cons] at h
    rcases sentFold_some vals l _ c v h with h1 | ⟨q, hq, h2, h3⟩
    · rw [sentStep, getD_set!] at h1
      split_ifs at h1 with h4
      · simp only [Option.some.injEq] at h1
        exact Or.inr ⟨p, List.mem_cons_self .., h4.1, h1.symm⟩
      · exact Or.inl h1
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h2, h3⟩

theorem sentFold_size (vals : List E) : ∀ (l : List (ℕ × ℕ)) (A : Array (Option E)),
    (l.foldl (sentStep vals) A).size = A.size
  | [], _ => rfl
  | p :: l, A => by
    rw [List.foldl_cons, sentFold_size vals l, sentStep, Array.set!, Array.size_setIfInBounds]

theorem sentFold_isSome (vals : List E) : ∀ (l : List (ℕ × ℕ)) (A : Array (Option E)) (c : ℕ),
    ((A.getD c none).isSome ∨ (∃ p ∈ l, p.1 = c) ∧ c < A.size) →
      ((l.foldl (sentStep vals) A).getD c none).isSome
  | [], A, c, h => by
    rcases h with h | ⟨⟨p, hp, _⟩, _⟩
    · exact h
    · simp at hp
  | p :: l, A, c, h => by
    rw [List.foldl_cons]
    refine sentFold_isSome vals l _ c ?_
    rw [sentStep, getD_set!, Array.set!, Array.size_setIfInBounds]
    rcases h with h | ⟨⟨q, hq, hqc⟩, hc⟩
    · left
      split_ifs <;> simp_all
    · rcases List.mem_cons.mp hq with rfl | hq'
      · left
        rw [ite_eq_left ⟨hqc, hqc ▸ hc⟩]
        rfl
      · right
        exact ⟨⟨q, hq', hqc⟩, hc⟩

/-- **The sent values are the columns' values**, where their `equal` relations hold. -/
theorem sentOf_spec (tab : Table) (vals : List E) (colv : ℕ → E)
    (h0 : ∀ p < (sentColumns tab).length, vals.getD p 0 = colv ((sentColumns tab).getD p 0)) :
    ∀ c v, (sentOf tab vals).getD c none = some v → v = colv c := by
  intro c v h
  rw [sentOf_eq] at h
  rcases sentFold_some vals _ _ c v h with h1 | ⟨p, hp, h2, h3⟩
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h1
    split_ifs at h1 <;> simp at h1
  · obtain ⟨hlt, hget⟩ := mem_zip_range_iff (sentColumns tab) 0 p hp
    rw [h3, h0 p.2 hlt, hget, h2]

theorem sentOf_isSome (tab : Table) (vals : List E) (c : ℕ) (hc : c ∈ sentColumns tab)
    (hw : c < tab.width) : ((sentOf tab vals).getD c none).isSome := by
  rw [sentOf_eq]
  refine sentFold_isSome vals _ _ c (Or.inr ⟨?_, by simpa using hw⟩)
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  refine ⟨((sentColumns tab)[k], k), ?_, rfl⟩
  have hz : k < ((sentColumns tab).zip (List.range (sentColumns tab).length)).length := by simp [hk]
  have := List.getElem_mem hz
  rwa [List.getElem_zip, List.getElem_range] at this

/-- A relation of `linearise`'s terms on a table's columns, bound to a sent value `v`: `v` is `β` plus
the tuple's value. -/
theorem holds_lin {ev : Column → List E → E} {o : ℕ} {pt : List E} {colv : ℕ → E}
    (hev : ∀ c, ev (.table o c) pt = colv c) (lin : E × List (ℕ × E)) (v beta : E)
    (h : RelHolds ev ⟨lin.2.map (fun ck ↦ term (.table o ck.1) pt ck.2), v + beta + lin.1⟩) :
    v = beta + linVal colv lin := by
  unfold RelHolds at h
  simp only [List.map_map, Function.comp_def, term, hev] at h
  rw [← add_eq_zero_iff']
  unfold linVal
  linear_combination h

theorem rels_flushStep (at_ : ℕ → Column) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) (st : TPState) (fl : List Form × List Form) :
    ∃ X, (flushStep at_ pt weights beta sent st fl).rels = st.rels ++ X := by
  unfold flushStep
  dsimp only
  split_ifs <;> simp

theorem rels_flushFold (at_ : ℕ → Column) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) : ∀ (l : List (List Form × List Form)) (st : TPState),
      ∃ X, (l.foldl (flushStep at_ pt weights beta sent) st).rels = st.rels ++ X
  | [], st => ⟨[], by simp⟩
  | fl :: l, st => by
    obtain ⟨X, hX⟩ := rels_flushStep at_ pt weights beta sent st fl
    obtain ⟨Y, hY⟩ := rels_flushFold at_ pt weights beta sent l (flushStep at_ pt weights beta sent st fl)
    exact ⟨X ++ Y, by rw [List.foldl_cons, hY, hX, List.append_assoc]⟩

/-- **One flush at `t`**: its pull and push fingerprints, computed or sent and bound. -/
theorem flushStep_spec (o : ℕ) (pt : List E) (weights : Array E) (beta : E) (sent : Array (Option E))
    (ev : Column → List E → E) (colv : ℕ → E) (hev : ∀ c, ev (.table o c) pt = colv c)
    (hs : ∀ i v, sent.getD i none = some v → v = colv i)
    (fl : List Form × List Form) (hlen : fl.2.length = fl.1.length)
    (h1 : ∀ f ∈ fl.1, ∀ mc ∈ f, SentFactor sent mc.1) (h2 : ∀ f ∈ fl.2, ∀ mc ∈ f, SentFactor sent mc.1)
    (st : TPState)
    (hh : ∀ r ∈ (flushStep (fun c ↦ .table o c) pt weights beta sent st fl).rels, RelHolds ev r) :
    (flushStep (fun c ↦ .table o c) pt weights beta sent st fl).pull =
        st.pull * (beta + tupleE fl.1 weights colv) ∧
      (flushStep (fun c ↦ .table o c) pt weights beta sent st fl).push =
        st.push * (beta + tupleE fl.2 weights colv) := by
  have hd : ∀ f ∈ difference fl.2 fl.1, ∀ mc ∈ f, SentFactor sent mc.1 := by
    intro f hf mc hmc
    unfold difference at hf
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hf
    obtain ⟨ha, hb⟩ := List.of_mem_zip hab
    rcases mono_addScaled 1 b a mc hmc with ⟨mc', h3, h4⟩ | ⟨mc', h3, h4⟩
    · rw [← h4]; exact h2 a ha mc' h3
    · rw [← h4]; exact h1 b hb mc' h3
  have lPull := linearise_spec fl.1 weights sent colv hs h1
  have lPush := linearise_spec fl.2 weights sent colv hs h2
  have lDiff := linearise_spec _ weights sent colv hs hd
  rw [tupleE_difference _ _ _ _ hlen] at lDiff
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  unfold flushStep at hh ⊢
  dsimp only at hh ⊢
  generalize linearise fl.1 weights sent = lP at hh lPull ⊢
  generalize linearise fl.2 weights sent = lQ at hh lPush ⊢
  generalize linearise (difference fl.2 fl.1) weights sent = lD at hh lDiff ⊢
  by_cases hp : (!lP.2.isEmpty) = true <;> by_cases hq : (!lD.2.isEmpty) = true <;>
    simp only [hp, hq, ↓reduceIte, Bool.false_eq_true] at hh ⊢
  · have H1 := hh ⟨lP.2.map (fun ck ↦ term (.table o ck.1) pt ck.2), st.vals.headD 0 + beta + lP.1⟩
      (by simp)
    have H2 := hh ⟨lQ.2.map (fun ck ↦ term (.table o ck.1) pt ck.2), st.vals.tail.headD 0 + beta + lQ.1⟩
      (by simp)
    rw [holds_lin hev _ _ beta H1, lPull, holds_lin hev _ _ beta H2, lPush]
    exact ⟨rfl, rfl⟩
  · have H1 := hh ⟨lP.2.map (fun ck ↦ term (.table o ck.1) pt ck.2), st.vals.headD 0 + beta + lP.1⟩
      (by simp)
    have hq' : lD.2 = [] := by simpa using hq
    have hD : lD.1 = tupleE fl.2 weights colv + tupleE fl.1 weights colv := by
      rw [← lDiff, linVal, hq']
      simp
    rw [holds_lin hev _ _ beta H1, lPull, hD]
    exact ⟨rfl, by linear_combination st.push * (tupleE fl.1 weights colv) * two⟩
  · have H2 := hh ⟨lQ.2.map (fun ck ↦ term (.table o ck.1) pt ck.2), st.vals.headD 0 + beta + lQ.1⟩
      (by simp)
    have hp' : lP.2 = [] := by simpa using hp
    have hP : lP.1 = tupleE fl.1 weights colv := by
      rw [← lPull, linVal, hp']
      simp
    rw [hP, holds_lin hev _ _ beta H2, lPush]
    exact ⟨rfl, rfl⟩
  · have hp' : lP.2 = [] := by simpa using hp
    have hq' : lD.2 = [] := by simpa using hq
    have hD : lD.1 = tupleE fl.2 weights colv + tupleE fl.1 weights colv := by
      rw [← lDiff, linVal, hq']
      simp
    have hP : lP.1 = tupleE fl.1 weights colv := by
      rw [← lPull, linVal, hp']
      simp
    rw [hD, hP]
    exact ⟨rfl, by linear_combination st.push * (tupleE fl.1 weights colv) * two⟩

theorem flushFold_spec (o : ℕ) (pt : List E) (weights : Array E) (beta : E) (sent : Array (Option E))
    (ev : Column → List E → E) (colv : ℕ → E) (hev : ∀ c, ev (.table o c) pt = colv c)
    (hs : ∀ i v, sent.getD i none = some v → v = colv i) :
    ∀ (l : List (List Form × List Form)) (st : TPState),
      (∀ fl ∈ l, fl.2.length = fl.1.length ∧ (∀ f ∈ fl.1, ∀ mc ∈ f, SentFactor sent mc.1) ∧
        ∀ f ∈ fl.2, ∀ mc ∈ f, SentFactor sent mc.1) →
      (∀ r ∈ (l.foldl (flushStep (fun c ↦ .table o c) pt weights beta sent) st).rels, RelHolds ev r) →
      (l.foldl (flushStep (fun c ↦ .table o c) pt weights beta sent) st).pull =
          st.pull * (l.map fun fl ↦ beta + tupleE fl.1 weights colv).prod ∧
        (l.foldl (flushStep (fun c ↦ .table o c) pt weights beta sent) st).push =
          st.push * (l.map fun fl ↦ beta + tupleE fl.2 weights colv).prod
  | [], st, _, _ => by simp
  | fl :: l, st, hl, hh => by
    rw [List.foldl_cons] at hh ⊢
    obtain ⟨ih1, ih2⟩ := flushFold_spec o pt weights beta sent ev colv hev hs l _
      (fun f hf ↦ hl f (List.mem_cons_of_mem _ hf)) hh
    obtain ⟨X, hX⟩ := rels_flushFold (fun c ↦ .table o c) pt weights beta sent l
      (flushStep (fun c ↦ .table o c) pt weights beta sent st fl)
    obtain ⟨hlen, h1, h2⟩ := hl fl (List.mem_cons_self ..)
    obtain ⟨s1, s2⟩ := flushStep_spec o pt weights beta sent ev colv hev hs fl hlen h1 h2 st
      (fun r hr ↦ hh r (by rw [hX]; exact List.mem_append_left _ hr))
    rw [ih1, ih2, s1, s2]
    simp only [List.map_cons, List.prod_cons]
    exact ⟨by ring, by ring⟩

theorem degree_flushFold (at_ : ℕ → Column) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) : ∀ (l : List (List Form × List Form)) (st : TPState),
      (l.foldl (flushStep at_ pt weights beta sent) st).pullDegree =
          st.pullDegree + (l.map fun fl ↦ tupleDegree fl.1).sum ∧
        (l.foldl (flushStep at_ pt weights beta sent) st).pushDegree =
          st.pushDegree + (l.map fun fl ↦ tupleDegree fl.2).sum
  | [], st => by simp
  | fl :: l, st => by
    rw [List.foldl_cons, (degree_flushFold at_ pt weights beta sent l _).1,
      (degree_flushFold at_ pt weights beta sent l _).2]
    simp only [flushStep, List.map_cons, List.sum_cons]
    exact ⟨by ring, by ring⟩

theorem tableDegrees_eq (tab : Table) :
    tableDegrees tab = (1 + ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ tupleDegree fl.1).sum,
      0 + ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ tupleDegree fl.2).sum) := by
  unfold tableDegrees
  generalize tab.flushes.pull.zip tab.flushes.push = l
  have key : ∀ (l : List (List Form × List Form)) (a b : ℕ),
      l.foldl (fun (acc : ℕ × ℕ) (p : List Form × List Form) ↦ (acc.1 + tupleDegree p.1, acc.2 + tupleDegree p.2)) (a, b) =
        (a + (l.map fun fl ↦ tupleDegree fl.1).sum, b + (l.map fun fl ↦ tupleDegree fl.2).sum) := by
    intro l
    induction l with
    | nil => intro a b; simp
    | cons p l ih =>
      intro a b
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, Prod.mk.injEq]
      exact ⟨by ring, by ring⟩
  exact key l 1 0

/-- **A table's part at `t`**: its sent values are its columns' values, its leaf's products are the
flushes' fingerprints at `t`, its degrees are `tableDegrees`. -/
theorem tablePartOf_spec (tab : Table) (hT : tab ∈ tables) (hL : TablesLin) (lh : ℕ) (weights : Array E)
    (beta : E) (w vals : List E) (ev : Column → List E → E) (colv : ℕ → E)
    (hev : ∀ c, ev (.table tab.opcode c) (w.take lh) = colv c)
    (hh : ∀ r ∈ (tablePartOf tab lh weights beta w vals).2.1, RelHolds ev r) :
    (∀ c ∈ sentColumns tab, (tablePartOf tab lh weights beta w vals).1.sent.getD c none = some (colv c)) ∧
      (tablePartOf tab lh weights beta w vals).1.pull =
        ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ beta + tupleE fl.1 weights colv).prod ∧
      (tablePartOf tab lh weights beta w vals).1.push =
        ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ beta + tupleE fl.2 weights colv).prod ∧
      (tablePartOf tab lh weights beta w vals).1.pullDegree = (tableDegrees tab).1 ∧
      (tablePartOf tab lh weights beta w vals).1.pushDegree = (tableDegrees tab).2 := by
  obtain ⟨hw, hfl⟩ := hL tab hT
  -- The `equal` relations of the sent values.
  have h0 : ∀ p < (sentColumns tab).length, vals.getD p 0 = colv ((sentColumns tab).getD p 0) := by
    intro p hp
    have hmem : Relation.equal (.table tab.opcode ((sentColumns tab).getD p 0)) (w.take lh) (vals.getD p 0) ∈
        (tablePartOf tab lh weights beta w vals).2.1 := by
      unfold tablePartOf
      dsimp only
      obtain ⟨X, hX⟩ := rels_flushFold (fun c ↦ .table tab.opcode c) (w.take lh) weights beta
        (sentOf tab vals) (tab.flushes.pull.zip tab.flushes.push)
        ⟨1, 1, 1, 0, ((sentColumns tab).zip (List.range (sentColumns tab).length)).map fun p ↦
          Relation.equal (.table tab.opcode p.1) (w.take lh) (vals.getD p.2 0), vals.drop (sentColumns tab).length⟩
      rw [hX]
      refine List.mem_append_left _ (List.mem_map.mpr ⟨((sentColumns tab).getD p 0, p), ?_, rfl⟩)
      have hz : p < ((sentColumns tab).zip (List.range (sentColumns tab).length)).length := by simp [hp]
      have := List.getElem_mem hz
      rwa [List.getElem_zip, List.getElem_range, ← List.getD_eq_getElem _ 0] at this
    rw [← holds_equal (hh _ hmem), hev]
  have hs := sentOf_spec tab vals colv h0
  have hsome : ∀ c ∈ sentColumns tab, ((sentOf tab vals).getD c none).isSome :=
    fun c hc ↦ sentOf_isSome tab vals c hc (hw c hc)
  have hSF : ∀ fl ∈ tab.flushes.pull.zip tab.flushes.push, fl.2.length = fl.1.length ∧
      (∀ f ∈ fl.1, ∀ mc ∈ f, SentFactor (sentOf tab vals) mc.1) ∧
      ∀ f ∈ fl.2, ∀ mc ∈ f, SentFactor (sentOf tab vals) mc.1 := by
    intro fl hf
    obtain ⟨hlen, hm⟩ := hfl fl hf
    have key : ∀ f ∈ fl.1 ++ fl.2, ∀ mc ∈ f, SentFactor (sentOf tab vals) mc.1 := by
      intro f hf' mc hmc i j hij
      have := hm f hf' mc hmc (by rw [hij]; rfl)
      rw [hij] at this
      rcases this with h | h
      · exact Or.inl (hsome i h)
      · exact Or.inr (hsome j h)
    exact ⟨hlen, fun f hf' ↦ key f (List.mem_append_left _ hf'),
      fun f hf' ↦ key f (List.mem_append_right _ hf')⟩
  unfold tablePartOf at hh ⊢
  dsimp only at hh ⊢
  obtain ⟨hpull, hpush⟩ := flushFold_spec tab.opcode (w.take lh) weights beta (sentOf tab vals) ev colv hev hs
    _ _ hSF hh
  obtain ⟨hd1, hd2⟩ := degree_flushFold (fun c ↦ .table tab.opcode c) (w.take lh) weights beta
    (sentOf tab vals) (tab.flushes.pull.zip tab.flushes.push)
    ⟨1, 1, 1, 0, ((sentColumns tab).zip (List.range (sentColumns tab).length)).map fun p ↦
      Relation.equal (.table tab.opcode p.1) (w.take lh) (vals.getD p.2 0), vals.drop (sentColumns tab).length⟩
  refine ⟨fun c hc ↦ ?_, by rw [hpull, one_mul], by rw [hpush, one_mul], ?_, ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hsome c hc)
    rw [hv, hs c v hv]
  · rw [hd1, tableDegrees_eq]
  · rw [hd2, tableDegrees_eq]

end UniSound.Ids.Eval
