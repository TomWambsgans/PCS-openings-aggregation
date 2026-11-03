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

/-- Every relation of a table's part is on the table's columns at `w[..h]`, untwisted. -/
theorem tablePartOf_terms (tab : Table) (lh : ℕ) (weights : Array E) (beta : E) (w vals : List E) :
    ∀ r ∈ (tablePartOf tab lh weights beta w vals).2.1, ∀ tm ∈ r.terms,
      (∃ c, tm.column = .table tab.opcode c) ∧ tm.point = w.take lh ∧ tm.twist = 0 := by
  have hstep : ∀ (st : TPState) (fl : List Form × List Form),
      ∀ r ∈ (flushStep (fun c ↦ .table tab.opcode c) (w.take lh) weights beta (sentOf tab vals) st fl).rels,
        r ∈ st.rels ∨ ∀ tm ∈ r.terms, (∃ c, tm.column = .table tab.opcode c) ∧ tm.point = w.take lh ∧
          tm.twist = 0 := by
    intro st fl r hr
    unfold flushStep at hr
    dsimp only at hr
    have key : ∀ (l : List (ℕ × E)), ∀ tm ∈ l.map (fun ck ↦ term (.table tab.opcode ck.1) (w.take lh) ck.2),
        (∃ c, tm.column = .table tab.opcode c) ∧ tm.point = w.take lh ∧ tm.twist = 0 := by
      intro l tm htm
      obtain ⟨ck, _, rfl⟩ := List.mem_map.mp htm
      exact ⟨⟨ck.1, rfl⟩, rfl, rfl⟩
    by_cases hp : (!(linearise fl.1 weights (sentOf tab vals)).2.isEmpty) = true <;>
    by_cases hq : (!(linearise (difference fl.2 fl.1) weights (sentOf tab vals)).2.isEmpty) = true <;>
      simp only [hp, hq, ↓reduceIte, Bool.false_eq_true, List.mem_append, List.mem_singleton] at hr
    · rcases hr with (hr | rfl) | rfl
      · exact Or.inl hr
      · exact Or.inr (key _)
      · exact Or.inr (key _)
    · rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr (key _)
    · rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr (key _)
    · exact Or.inl hr
  have hfold : ∀ (l : List (List Form × List Form)) (st : TPState),
      ∀ r ∈ (l.foldl (flushStep (fun c ↦ .table tab.opcode c) (w.take lh) weights beta
          (sentOf tab vals)) st).rels,
        r ∈ st.rels ∨ ∀ tm ∈ r.terms, (∃ c, tm.column = .table tab.opcode c) ∧ tm.point = w.take lh ∧
          tm.twist = 0 := by
    intro l
    induction l with
    | nil => intro st r hr; exact Or.inl hr
    | cons fl l ih =>
      intro st r hr
      rw [List.foldl_cons] at hr
      rcases ih _ r hr with h | h
      · exact hstep st fl r h
      · exact Or.inr h
  intro r hr
  unfold tablePartOf at hr
  dsimp only at hr
  rcases hfold _ _ r hr with h | h
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    intro tm htm
    simp only [Relation.equal, term, List.mem_singleton] at htm
    subst htm
    exact ⟨⟨p.1, rfl⟩, rfl, rfl⟩
  · exact h

/-! ## The tables' parts (`tablesPart`) -/

theorem tablesPart_length (S : Shape) (weights : Array E) (beta : E) (w : List E) :
    ∀ (ts : List Table) (vals : List E), (tablesPart S weights beta w ts vals).1.length = ts.length
  | [], _ => rfl
  | t :: ts, vals => by
    simp only [tablesPart, List.length_cons, tablesPart_length S weights beta w ts]

theorem tablesPart_getD (S : Shape) (weights : Array E) (beta : E) (w : List E) :
    ∀ (ts : List Table) (vals : List E) (i : ℕ) (hi : i < ts.length), ∃ vals',
      (tablesPart S weights beta w ts vals).1.getD i default =
          (tablePartOf ts[i] (S.heights.getD ts[i].opcode 0) weights beta w vals').1 ∧
        ∀ r ∈ (tablePartOf ts[i] (S.heights.getD ts[i].opcode 0) weights beta w vals').2.1,
          r ∈ (tablesPart S weights beta w ts vals).2.1
  | [], _, i, hi => by simp at hi
  | t :: ts, vals, 0, _ => ⟨vals, rfl, fun r hr ↦ List.mem_append_left _ hr⟩
  | t :: ts, vals, i + 1, hi => by
    obtain ⟨v', h1, h2⟩ := tablesPart_getD S weights beta w ts
      (tablePartOf t (S.heights.getD t.opcode 0) weights beta w vals).2.2 i (by simpa using hi)
    exact ⟨v', h1, fun r hr ↦ List.mem_append_right _ (h2 r hr)⟩

theorem tablesPart_rels (S : Shape) (weights : Array E) (beta : E) (w : List E) :
    ∀ (ts : List Table) (vals : List E), ∀ r ∈ (tablesPart S weights beta w ts vals).2.1,
      ∃ tab ∈ ts, ∃ vals', r ∈ (tablePartOf tab (S.heights.getD tab.opcode 0) weights beta w vals').2.1
  | [], _, r, hr => by simp [tablesPart] at hr
  | t :: ts, vals, r, hr => by
    simp only [tablesPart, List.mem_append] at hr
    rcases hr with hr | hr
    · exact ⟨t, List.mem_cons_self .., vals, hr⟩
    · obtain ⟨tab, htab, v', hv⟩ := tablesPart_rels S weights beta w ts _ r hr
      exact ⟨tab, List.mem_cons_of_mem _ htab, v', hv⟩

/-! ## The heap's relations (`heapRelations`), stated explicitly -/

theorem forIn_push {α γ : Type} (g : α → Relation) : ∀ (l : List α) (A : Array Relation) (B : γ)
    (f : α → Array Relation × γ → Id (ForInStep (Array Relation × γ))),
    (∀ a s, ∃ c, f a s = pure (.yield (s.1.push (g a), c))) →
    (Id.run (forIn l (A, B) f)).1.toList = A.toList ++ l.map g
  | [], A, B, f, _ => by simp
  | a :: l, A, B, f, hf => by
    obtain ⟨c, hc⟩ := hf a (A, B)
    rw [List.forIn_cons, hc]
    have := forIn_push g l (A.push (g a)) c f hf
    simp only [Id.run, pure_bind] at this ⊢
    rw [this]
    simp

/-- **A heap block's leaf relation**, as `heapRelations`' loop states it. -/
def blockRel (S : Shape) (active : List E) (parts : List TablePart)
    (memoryPull memoryPush bytecodePull bytecodePush : E) (w : List E) (x : Block × ℕ) : Relation :=
  let mixed := (List.range S.heap.h).map fun l ↦
    if l < x.1.r then w.getD l 0 + pointE (x.1.position >>> l) else pointE (x.1.position >>> l)
  let n := 2 ^ x.1.r
  let wr := w.getD x.1.r 0
  match x.1.leaves with
  | .unused => ⟨[term .heap mixed 1], 1⟩
  | .memory => ⟨[term .heap mixed memoryPull] ++
      quotientTerms (Column.leafQuotient x.2) (chunks (degree (2 * (n - 1)) n + 1)) w wr, memoryPush⟩
  | .bytecode => ⟨[term .heap mixed bytecodePull] ++
      quotientTerms (Column.leafQuotient x.2) (chunks (degree (2 * (n - 1)) n + 1)) w wr, bytecodePush⟩
  | .table t =>
    let part := parts.getD t default
    let z := active.getD t 0
    ⟨[term .heap mixed (part.pull * wr + z * z)] ++
      quotientTerms (Column.leafQuotient x.2) (chunks (degree (max part.pullDegree part.pushDegree * (n - 1) +
        (n - Shape.leastRows x.1.r)) n + 1)) w (wr * z), part.push * wr + z * z⟩

/-- **`heapRelations`' relations**: `T(t)`, the tree, the root, each block's leaf, the constraint
quotient's chunks (its `Id.run do` loop, unfolded). -/
theorem heapRelations_fst (S : Shape) (active : List E) (parts : List TablePart) (weights : Array E)
    (beta hv cv mpull mpush bpull bpush : E) (w : List E) (cc : List ℕ) :
    (heapRelations S active parts weights beta hv cv mpull mpush bpull bpush w cc).1 =
      [Relation.equal .heap (w.take S.heap.h) hv,
        ⟨[term .heap ((w.drop 1).take S.heap.h) (w.getD 1 0),
          term .heap ((w.take S.heap.h).modify 0 (· + 1)) (w.getD 1 0 * hv),
          term (.treeQuotient 0) (w.take S.heap.h) (w.getD S.heap.h 0),
          term (.treeQuotient 1) [] (w.getD S.heap.h 0 * w.getD S.heap.h 0)], 0⟩,
        ⟨[term .heap ((List.range S.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0)
          (rootInit weights beta)], rootFin S weights beta⟩] ++
      (S.heap.blocks.zip (List.range S.heap.blocks.length)).map
        (blockRel S active parts mpull mpush bpull bpush w) ++
      [⟨quotientTerms .constraintQuotient cc w 1, cv⟩] := by
  unfold heapRelations
  simp only [Id.run_bind, Id.run_pure]
  rw [Array.toList_push, forIn_push (blockRel S active parts mpull mpush bpull bpush w)]
  · simp [Relation.equal, rootInit, rootFin]
  · intro a s
    rcases a with ⟨⟨lv, r, pos⟩, i⟩
    cases lv <;> exact ⟨_, rfl⟩

/-! ## The constraint relation (`constraintRelation`), as folds -/

/-- `BLAKE2S`'s copies (the inner loop of `constraintRelation`), on (terms, power). -/
def copyStep (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E) (s : Array Term × E)
    (c : ℕ) : Array Term × E :=
  match qflockSlot (columns.getD c "") with
  | some slot => ((s.1.push (term (.table o c) (w.take r) (s.2 * lift))).push
      (term (.qflockSlot slot) y (s.2 * lift)), s.2 * gamma)
  | none => s

/-- One table's step of `constraintRelation`'s loop, on (known, terms, power, degree). -/
def crStep (shape : Shape) (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ)
    (x : Table × TablePart) : E × Array Term × E × ℕ :=
  let r := shape.heights.getD x.1.opcode 0
  let n := 2 ^ r
  let lift := vanishingRatio w r shape.constraintVars
  let s1 : E × Array Term × E × ℕ := if x.1.opcode = opJump then
      (s.1 + s.2.2.1 * lift * (x.2.sent.getD (colIdx x.1.columns "b") none).getD 0 +
          s.2.2.1 * gamma * lift * (x.2.sent.getD (colIdx x.1.columns "v_cond") none).getD 0 *
            ((x.2.sent.getD (colIdx x.1.columns "b") none).getD 0 + 1),
        s.2.1.push (term (.table x.1.opcode (colIdx x.1.columns "w")) (w.take r)
          (s.2.2.1 * lift * (x.2.sent.getD (colIdx x.1.columns "v_cond") none).getD 0)),
        s.2.2.1 * gamma * gamma, max s.2.2.2 (degree n 2))
    else s
  let s2 : E × Array Term × E × ℕ := (s1.1 + s1.2.2.1 * lift,
    s1.2.1.push (term (.inverse x.1.opcode) (w.take r)
      (s1.2.2.1 * lift * x.1.countColumns.foldl (fun acc c ↦ acc * (x.2.sent.getD c none).getD 0) 1)),
    s1.2.2.1 * gamma, max s1.2.2.2 (degree ((n - 1) * (1 + x.1.countColumns.length)) n))
  if x.1.opcode = opBlake2s then
    let inner := (List.range x.1.width).foldl
      (copyStep x.1.opcode r x.1.columns w (coordinatesAt t (coordinateFunctionals r)) lift gamma)
      (s2.2.1, s2.2.2.1)
    (s2.1, inner.1, inner.2, max s2.2.2.2 (degree (r * (n / 2)) n))
  else s2

/-- The public lines' step, on (known, terms, power). -/
def lineStep (shape : Shape) (gamma t : E) (w : List E) (s : E × Array Term × E) (x : (E × E) × ℕ) :
    E × Array Term × E :=
  (s.1 + s.2.2 * vanishingRatio w 1 shape.constraintVars * (x.1.1 + t * (x.1.1 + x.1.2)),
    s.2.1.push (term (.memory x.2) (w.take shape.logMemory) (s.2.2 * vanishingRatio w 1 shape.constraintVars)),
    s.2.2 * gamma)

/-- **`constraintRelation`, as folds.** -/
def crOf (shape : Shape) (parts : List TablePart) (publicWords : List E) (gamma t constraintValue : E)
    (w : List E) : Relation × ℕ :=
  let s := (tables.zip parts).foldl (crStep shape gamma t w) (0, #[], 1, 0)
  let s' := ((linesOf publicWords).zip (List.range 3)).foldl (lineStep shape gamma t w) (s.1, s.2.1, s.2.2.1)
  (⟨s'.2.1.toList, constraintValue * w.getD shape.constraintVars 0 + s'.1⟩,
    max s.2.2.2 (degree (2 ^ shape.logMemory) 3))

theorem forIn_id_eq_foldl' {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  rw [show f = fun a b ↦ pure (.yield (g b a)) from funext fun a ↦ funext fun b ↦ h a b]
  exact List.forIn_pure_yield_eq_foldl _ _

/-- **`constraintRelation` is its folds** (its `Id.run do` loops, unfolded). -/
theorem constraintRelation_eq (shape : Shape) (parts : List TablePart) (publicWords : List E)
    (gamma t constraintValue : E) (w : List E) :
    constraintRelation shape parts publicWords gamma t constraintValue w =
      crOf shape parts publicWords gamma t constraintValue w := by
  unfold constraintRelation crOf
  simp only [Id.run]
  rw [forIn_id_eq_foldl' _ _ _ (crStep shape gamma t w)]
  · simp only [pure_bind, List.forIn_pure_yield_eq_foldl]
    rfl
  · intro x s
    by_cases hj : x.1.opcode = opJump
    · have hb : ¬ x.1.opcode = opBlake2s := by rw [hj]; decide
      simp only [crStep, ite_eq_left hj, ite_eq_right hb]
    · by_cases hb : x.1.opcode = opBlake2s
      · simp only [crStep, ite_eq_right hj, ite_eq_left hb]
        rw [forIn_id_eq_foldl' _ _ _ (copyStep x.1.opcode (shape.heights.getD x.1.opcode 0) x.1.columns w
          (coordinatesAt t (coordinateFunctionals (shape.heights.getD x.1.opcode 0)))
          (vanishingRatio w (shape.heights.getD x.1.opcode 0) shape.constraintVars) gamma)]
        · rfl
        · intro c s'
          unfold copyStep
          rcases qflockSlot (x.1.columns.getD c "") with _ | slot <;> rfl
      · simp only [crStep, ite_eq_right hj, ite_eq_right hb]

/-! ## The constraint relation at `t` -/

/-- Terms' value under `ev`. -/
def termsVal (ev : Column → List E → E) (terms : Array Term) : E :=
  (terms.toList.map fun tm ↦ tm.coefficient * ev tm.column tm.point).sum

theorem termsVal_empty (ev : Column → List E → E) : termsVal ev #[] = 0 := by simp [termsVal]

theorem termsVal_push (ev : Column → List E → E) (terms : Array Term) (tm : Term) :
    termsVal ev (terms.push tm) = termsVal ev terms + tm.coefficient * ev tm.column tm.point := by
  simp [termsVal]

theorem powComb_append (a b : List E) (ρ : E) :
    powComb (a ++ b) ρ = powComb a ρ + ρ ^ a.length * powComb b ρ := by
  induction a with
  | nil => simp [powComb_nil]
  | cons x a ih =>
    rw [List.cons_append, powComb_cons, powComb_cons, ih, List.length_cons, pow_succ]
    ring

theorem copyFold_spec (ev : Column → List E → E) (o r : ℕ) (columns : List String) (w y : List E)
    (lift gamma : E) : ∀ (l : List ℕ) (s : Array Term × E),
      termsVal ev (l.foldl (copyStep o r columns w y lift gamma) s).1 = termsVal ev s.1 +
          s.2 * powComb (l.filterMap fun c ↦ (qflockSlot (columns.getD c "")).map fun slot ↦
            lift * (ev (.table o c) (w.take r) + ev (.qflockSlot slot) y)) gamma ∧
        (l.foldl (copyStep o r columns w y lift gamma) s).2 =
          s.2 * gamma ^ (l.filterMap fun c ↦ qflockSlot (columns.getD c "")).length
  | [], s => by simp [powComb_nil]
  | c :: l, s => by
    rw [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := copyFold_spec ev o r columns w y lift gamma l (copyStep o r columns w y lift gamma s c)
    rw [ih1, ih2]
    simp only [List.filterMap_cons]
    unfold copyStep
    rcases qflockSlot (columns.getD c "") with _ | slot
    · simp only [Option.map_none]
      trivial
    · simp only [Option.map_some, termsVal_push, term, powComb_cons, List.length_cons, pow_succ]
      exact ⟨by ring, by ring⟩

theorem lineFold_spec (S : Shape) (gamma t : E) (w : List E) (ev : Column → List E → E) :
    ∀ (l : List ((E × E) × ℕ)) (s : E × Array Term × E),
      (l.foldl (lineStep S gamma t w) s).1 + termsVal ev (l.foldl (lineStep S gamma t w) s).2.1 =
          s.1 + termsVal ev s.2.1 + s.2.2 * powComb (l.map fun x ↦ vanishingRatio w 1 S.constraintVars *
            (ev (.memory x.2) (w.take S.logMemory) + x.1.1 + t * (x.1.1 + x.1.2))) gamma ∧
        (l.foldl (lineStep S gamma t w) s).2.2 = s.2.2 * gamma ^ l.length
  | [], s => by simp [powComb_nil]
  | x :: l, s => by
    rw [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := lineFold_spec S gamma t w ev l (lineStep S gamma t w s x)
    rw [ih1, ih2]
    simp only [lineStep, termsVal_push, term, List.map_cons, powComb_cons, List.length_cons, pow_succ]
    exact ⟨by ring, by ring⟩

/-- What the constraint relation's step needs of the evaluation at a table. -/
structure CrTableOk (S : Shape) (c1 : Stk) (t : E) (w : List E) (ev : Column → List E → E)
    (tab : Table) (part : TablePart) : Prop where
  lift : vanishingRatio w (S.heights.getD tab.opcode 0) S.constraintVars =
    (liftP (S.heights.getD tab.opcode 0) S.constraintVars).eval t
  col : ∀ c, ev (.table tab.opcode c) (w.take (S.heights.getD tab.opcode 0)) =
    (c1P S c1 (.table tab.opcode c)).eval t
  inv : ev (.inverse tab.opcode) (w.take (S.heights.getD tab.opcode 0)) = (c1P S c1 (.inverse tab.opcode)).eval t
  slot : tab.opcode = opBlake2s → ∀ slot,
    ev (.qflockSlot slot) (coordinatesAt t (coordinateFunctionals (S.heights.getD tab.opcode 0))) =
      (slotP S c1 slot).eval t
  sent : ∀ c ∈ sentColumns tab, part.sent.getD c none = some ((c1P S c1 (.table tab.opcode c)).eval t)
  jumpSent : tab.opcode = opJump →
    colIdx tab.columns "b" ∈ sentColumns tab ∧ colIdx tab.columns "v_cond" ∈ sentColumns tab

theorem countColumns_sent (tab : Table) : ∀ c ∈ tab.countColumns, c ∈ sentColumns tab :=
  fun _ hc ↦ List.mem_append_left _ hc

theorem foldl_mul_getD (f : ℕ → E) (sent : Array (Option E)) :
    ∀ (l : List ℕ) (a : E), (∀ c ∈ l, sent.getD c none = some (f c)) →
      l.foldl (fun acc c ↦ acc * (sent.getD c none).getD 0) a = a * (l.map f).prod
  | [], a, _ => by simp
  | c :: l, a, h => by
    rw [List.foldl_cons, foldl_mul_getD f sent l _ fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc'),
      h c (List.mem_cons_self ..), Option.getD_some, List.map_cons, List.prod_cons, mul_assoc]

/-- **One table's step of the constraint relation at `t`**: it adds the table's constraints at `t`,
batched by the powers of `γ` from the current power. -/
theorem crStep_spec (S : Shape) (c1 : Stk) (gamma t : E) (w : List E) (ev : Column → List E → E)
    (tab : Table) (part : TablePart) (h : CrTableOk S c1 t w ev tab part) (s : E × Array Term × E × ℕ) :
    (crStep S gamma t w s (tab, part)).1 + termsVal ev (crStep S gamma t w s (tab, part)).2.1 =
        s.1 + termsVal ev s.2.1 +
          s.2.2.1 * powComb ((tableConstraintsP S c1 tab).map fun mw ↦ (mw.1 * mw.2).eval t) gamma ∧
      (crStep S gamma t w s (tab, part)).2.2.1 = s.2.2.1 * gamma ^ (tableConstraintsP S c1 tab).length := by
  have hcnt : tab.countColumns.foldl (fun acc c ↦ acc * (part.sent.getD c none).getD 0) 1 =
      (tab.countColumns.map fun c ↦ (c1P S c1 (.table tab.opcode c)).eval t).prod := by
    rw [foldl_mul_getD _ _ _ 1 fun c hc ↦ h.sent c (countColumns_sent tab c hc), one_mul]
  have hprod : ((tab.countColumns.map fun c ↦ c1P S c1 (.table tab.opcode c)).prod).eval t =
      (tab.countColumns.map fun c ↦ (c1P S c1 (.table tab.opcode c)).eval t).prod := by
    rw [eval_list_prod_of, List.map_map]
    rfl
  have hcopies := copyFold_spec ev tab.opcode (S.heights.getD tab.opcode 0) tab.columns w
    (coordinatesAt t (coordinateFunctionals (S.heights.getD tab.opcode 0)))
    ((liftP (S.heights.getD tab.opcode 0) S.constraintVars).eval t) gamma (List.range tab.width)
  unfold crStep tableConstraintsP
  dsimp only
  rw [h.lift]
  by_cases hj : tab.opcode = opJump
  · have hb : ¬ tab.opcode = opBlake2s := by rw [hj]; decide
    obtain ⟨hsb, hsv⟩ := h.jumpSent hj
    simp only [ite_eq_left hj, ite_eq_right hb, List.append_nil, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, List.length_cons, List.length_nil, powComb_cons, powComb_nil,
      termsVal_push, term, h.sent _ hsb, h.sent _ hsv, Option.getD_some, h.col, h.inv, hcnt,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, hprod]
    constructor <;> ring
  · by_cases hb : tab.opcode = opBlake2s
    · simp only [ite_eq_right hj, ite_eq_left hb, List.nil_append, List.cons_append, List.map_cons,
        List.length_cons, powComb_cons, term, hcnt, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_one, hprod]
      obtain ⟨hc1, hc2⟩ := hcopies (s.2.1.push ⟨.inverse tab.opcode, w.take (S.heights.getD tab.opcode 0), 0,
        s.2.2.1 * (liftP (S.heights.getD tab.opcode 0) S.constraintVars).eval t *
          (tab.countColumns.map fun c ↦ (c1P S c1 (.table tab.opcode c)).eval t).prod⟩, s.2.2.1 * gamma)
      rw [hc1, hc2, termsVal_push, List.map_filterMap, length_filterMap_map]
      simp only [Option.map_map, Function.comp_def, Polynomial.eval_add, h.col, h.slot hb, h.inv]
      constructor
      · ring
      · rw [pow_succ]
        ring
    · simp only [ite_eq_right hj, ite_eq_right hb, List.nil_append, List.append_nil, List.map_cons,
        List.map_nil, List.length_cons, List.length_nil, powComb_cons, powComb_nil, termsVal_push, term,
        h.inv, hcnt, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, hprod]
      constructor <;> ring

theorem crFold_spec (S : Shape) (c1 : Stk) (gamma t : E) (w : List E) (ev : Column → List E → E) :
    ∀ (L : List (Table × TablePart)) (s : E × Array Term × E × ℕ), (∀ x ∈ L, CrTableOk S c1 t w ev x.1 x.2) →
      (L.foldl (crStep S gamma t w) s).1 + termsVal ev (L.foldl (crStep S gamma t w) s).2.1 =
          s.1 + termsVal ev s.2.1 + s.2.2.1 * powComb (L.flatMap fun x ↦
            (tableConstraintsP S c1 x.1).map fun mw ↦ (mw.1 * mw.2).eval t) gamma ∧
        (L.foldl (crStep S gamma t w) s).2.2.1 = s.2.2.1 * gamma ^ (L.flatMap fun x ↦
            (tableConstraintsP S c1 x.1).map fun mw ↦ (mw.1 * mw.2).eval t).length
  | [], s, _ => by simp [powComb_nil]
  | x :: L, s, h => by
    rw [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := crFold_spec S c1 gamma t w ev L (crStep S gamma t w s x)
      fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    obtain ⟨s1, s2⟩ := crStep_spec S c1 gamma t w ev x.1 x.2 (h x (List.mem_cons_self ..)) s
    rw [ih1, ih2, s1, s2, List.flatMap_cons, powComb_append, List.length_append, pow_add, List.length_map]
    constructor <;> ring

theorem flatMap_zip_fst {α β γ : Type} (f : α → List γ) :
    ∀ (l : List α) (m : List β), l.length ≤ m.length → (l.zip m).flatMap (fun x ↦ f x.1) = l.flatMap f
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: l, b :: m, h => by
    rw [List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons,
      flatMap_zip_fst f l m (by simpa using h)]

/-- **The constraint relation at `t`**: where it holds, the batched constraints at `t` plus
`Q_W(t) w_{r_W}(t)` vanish. -/
theorem crOf_holds (S : Shape) (c1 : Stk) (parts : List TablePart) (pw : List E) (gamma t cv : E)
    (w : List E) (ev : Column → List E → E) (hlen : tables.length ≤ parts.length)
    (hok : ∀ x ∈ tables.zip parts, CrTableOk S c1 t w ev x.1 x.2)
    (hmem : ∀ k < 3, ev (.memory k) (w.take S.logMemory) = (c1P S c1 (.memory k)).eval t)
    (hlift : vanishingRatio w 1 S.constraintVars = (liftP 1 S.constraintVars).eval t)
    (hh : RelHolds ev (crOf S parts pw gamma t cv w).1) :
    powComb ((constraintsP S c1 pw).map fun mw ↦ (mw.1 * mw.2).eval t) gamma +
      cv * w.getD S.constraintVars 0 = 0 := by
  unfold RelHolds crOf at hh
  dsimp only at hh
  obtain ⟨f1, f2⟩ := crFold_spec S c1 gamma t w ev (tables.zip parts) (0, #[], 1, 0) hok
  generalize (tables.zip parts).foldl (crStep S gamma t w) (0, #[], 1, 0) = s at hh f1 f2
  obtain ⟨l1, -⟩ := lineFold_spec S gamma t w ev ((linesOf pw).zip (List.range 3)) (s.1, s.2.1, s.2.2.1)
  generalize ((linesOf pw).zip (List.range 3)).foldl (lineStep S gamma t w) (s.1, s.2.1, s.2.2.1) = s'
    at hh l1
  change termsVal ev s'.2.1 + _ = 0 at hh
  have hl : ((linesOf pw).zip (List.range 3)).map (fun x ↦ vanishingRatio w 1 S.constraintVars *
      (ev (.memory x.2) (w.take S.logMemory) + x.1.1 + t * (x.1.1 + x.1.2))) =
      (linesP S c1 pw).map fun mw ↦ (mw.1 * mw.2).eval t := by
    unfold linesP
    rw [List.map_map]
    refine List.map_congr_left fun x hx ↦ ?_
    have hx3 : x.2 < 3 := List.mem_range.mp (List.of_mem_zip hx).2
    simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, hlift, hmem x.2 hx3]
  rw [hl] at l1
  dsimp only at f1 f2
  rw [termsVal_empty] at f1
  simp only [add_zero, zero_add, one_mul] at f1 f2
  unfold constraintsP
  rw [List.map_append, powComb_append, List.map_flatMap,
    ← flatMap_zip_fst (fun tab ↦ (tableConstraintsP S c1 tab).map fun mw ↦ (mw.1 * mw.2).eval t) tables
      parts hlen]
  rw [← f1, ← f2]
  dsimp only at l1
  linear_combination hh - l1

/-! ### The constraint relation's terms -/

/-- A term of the constraint relation: untwisted, on `C1`, at a prefix of the digits or at `y`. -/
def CrPt (w y : List E) (tm : Term) : Prop :=
  tm.twist = 0 ∧ tm.column.commitment = .c1 ∧ ((∃ k, tm.point = w.take k) ∨ tm.point = y)

theorem copyFold_terms (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E) :
    ∀ (l : List ℕ) (s : Array Term × E), ∃ X,
      (l.foldl (copyStep o r columns w y lift gamma) s).1.toList = s.1.toList ++ X ∧ ∀ tm ∈ X, CrPt w y tm
  | [], s => ⟨[], by simp, by simp⟩
  | c :: l, s => by
    rw [List.foldl_cons]
    obtain ⟨X, hX, hP⟩ := copyFold_terms o r columns w y lift gamma l (copyStep o r columns w y lift gamma s c)
    rw [hX]
    unfold copyStep
    split
    · rename_i _ slot _
      refine ⟨[term (.table o c) (w.take r) (s.2 * lift), term (.qflockSlot slot) y (s.2 * lift)] ++ X,
        by simp, fun tm htm ↦ ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons] at htm
      rcases htm with rfl | rfl | htm
      · exact ⟨rfl, rfl, Or.inl ⟨r, rfl⟩⟩
      · exact ⟨rfl, rfl, Or.inr rfl⟩
      · exact hP tm htm
    · exact ⟨X, rfl, hP⟩

theorem copyFold_sub (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E)
    (l : List ℕ) (s : Array Term × E) (tm : Term) (h : tm ∈ s.1.toList) :
    tm ∈ (l.foldl (copyStep o r columns w y lift gamma) s).1.toList := by
  obtain ⟨X, hX, -⟩ := copyFold_terms o r columns w y lift gamma l s
  rw [hX]
  exact List.mem_append_left _ h

theorem copyFold_slot (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E) :
    ∀ (l : List ℕ) (s : Array Term × E) (c slot : ℕ), c ∈ l → qflockSlot (columns.getD c "") = some slot →
      ∃ tm ∈ (l.foldl (copyStep o r columns w y lift gamma) s).1.toList, tm.point = y
  | [], _, _, _, h, _ => by simp at h
  | c' :: l, s, c, slot, h, hs => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · refine ⟨term (.qflockSlot slot) y (s.2 * lift), copyFold_sub o r columns w y lift gamma l _ _ ?_, rfl⟩
      unfold copyStep
      rw [hs]
      simp
    · exact copyFold_slot o r columns w y lift gamma l _ c slot h' hs

theorem crStep_terms (S : Shape) (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ)
    (x : Table × TablePart) : ∃ X, (crStep S gamma t w s x).2.1.toList = s.2.1.toList ++ X ∧
      ∀ tm ∈ X, CrPt w (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm := by
  unfold crStep
  dsimp only
  by_cases hj : x.1.opcode = opJump
  · have hb : ¬ x.1.opcode = opBlake2s := by rw [hj]; decide
    simp only [ite_eq_left hj, ite_eq_right hb, Array.toList_push, List.append_assoc]
    refine ⟨_, rfl, fun tm htm ↦ ?_⟩
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at htm
    rcases htm with rfl | rfl <;> exact ⟨rfl, rfl, Or.inl ⟨_, rfl⟩⟩
  · by_cases hb : x.1.opcode = opBlake2s
    · simp only [ite_eq_right hj, ite_eq_left hb]
      obtain ⟨X, hX, hP⟩ := copyFold_terms _ _ _ _ _ _ _ _ _
      rw [hX, Array.toList_push, List.append_assoc]
      refine ⟨_, rfl, fun tm htm ↦ ?_⟩
      simp only [List.singleton_append, List.mem_cons] at htm
      rcases htm with rfl | htm
      · exact ⟨rfl, rfl, Or.inl ⟨_, rfl⟩⟩
      · have := hP tm htm
        rwa [hb] at this
    · simp only [ite_eq_right hj, ite_eq_right hb, Array.toList_push]
      refine ⟨_, rfl, fun tm htm ↦ ?_⟩
      simp only [List.mem_singleton] at htm
      subst htm
      exact ⟨rfl, rfl, Or.inl ⟨_, rfl⟩⟩

theorem crStep_sub (S : Shape) (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ)
    (x : Table × TablePart) (tm : Term) (h : tm ∈ s.2.1.toList) : tm ∈ (crStep S gamma t w s x).2.1.toList := by
  obtain ⟨X, hX, -⟩ := crStep_terms S gamma t w s x
  rw [hX]
  exact List.mem_append_left _ h

theorem crFold_terms (S : Shape) (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart))
    (s : E × Array Term × E × ℕ), ∀ tm ∈ (L.foldl (crStep S gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨ CrPt w (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm
  | [], _, _, h => Or.inl h
  | x :: L, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases crFold_terms S gamma t w L _ tm h with h1 | h1
    · obtain ⟨X, hX, hP⟩ := crStep_terms S gamma t w s x
      rw [hX, List.mem_append] at h1
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (hP tm h1)
    · exact Or.inr h1

theorem crFold_sub (S : Shape) (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart))
    (s : E × Array Term × E × ℕ), ∀ tm ∈ s.2.1.toList, tm ∈ (L.foldl (crStep S gamma t w) s).2.1.toList
  | [], _, _, h => h
  | x :: L, s, tm, h => by
    rw [List.foldl_cons]
    exact crFold_sub S gamma t w L _ tm (crStep_sub S gamma t w s x tm h)

theorem lineFold_terms (S : Shape) (gamma t : E) (w : List E) (y : List E) : ∀ (l : List ((E × E) × ℕ))
    (s : E × Array Term × E), ∀ tm ∈ (l.foldl (lineStep S gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨ CrPt w y tm
  | [], _, _, h => Or.inl h
  | x :: l, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases lineFold_terms S gamma t w y l _ tm h with h1 | h1
    · simp only [lineStep, Array.toList_push, List.mem_append, List.mem_singleton] at h1
      rcases h1 with h1 | rfl
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, rfl, Or.inl ⟨_, rfl⟩⟩
    · exact Or.inr h1

theorem lineFold_sub (S : Shape) (gamma t : E) (w : List E) : ∀ (l : List ((E × E) × ℕ))
    (s : E × Array Term × E), ∀ tm ∈ s.2.1.toList, tm ∈ (l.foldl (lineStep S gamma t w) s).2.1.toList
  | [], _, _, h => h
  | x :: l, s, tm, h => by
    rw [List.foldl_cons]
    exact lineFold_sub S gamma t w l _ tm (by simp [lineStep, h])

/-- **The constraint relation's terms**: untwisted, on `C1`, at prefixes of the digits or at `y`. -/
theorem crOf_terms (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E) :
    ∀ tm ∈ (crOf S parts pw gamma t cv w).1.terms,
      CrPt w (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm := by
  intro tm htm
  unfold crOf at htm
  dsimp only at htm
  rcases lineFold_terms S gamma t w _ _ _ tm htm with h | h
  · rcases crFold_terms S gamma t w _ _ tm h with h' | h'
    · simp at h'
    · exact h'
  · exact h

theorem qflockSlot_m0 : qflockSlot (blake2sColumns.getD 9 "") = some 10 := by decide

theorem tables_getD5 : (tables.getD 5 default).opcode = opBlake2s ∧
    (tables.getD 5 default).columns = blake2sColumns := ⟨rfl, rfl⟩

/-- **The constraint relation has a term at `y`** (a `BLAKE2S` copy's slot). -/
theorem crOf_slot (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E)
    (hlen : tables.length ≤ parts.length) :
    ∃ tm ∈ (crOf S parts pw gamma t cv w).1.terms,
      tm.point = coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0)) := by
  have hx : (tables.getD 5 default, parts.getD 5 default) ∈ tables.zip parts := by
    have h5 : 5 < (tables.zip parts).length := by
      rw [List.length_zip]; have : tables.length = 6 := rfl; omega
    have := List.getElem_mem h5
    rwa [List.getElem_zip, ← List.getD_eq_getElem _ default, ← List.getD_eq_getElem _ default] at this
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem hx
  have key : ∀ s : E × Array Term × E × ℕ, ∃ tm ∈ (crStep S gamma t w s
      (tables.getD 5 default, parts.getD 5 default)).2.1.toList,
      tm.point = coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0)) := by
    intro s
    have h1 : ¬ (tables.getD 5 default).opcode = opJump := by decide
    have h2 : (tables.getD 5 default).opcode = opBlake2s := rfl
    unfold crStep
    dsimp only
    simp only [ite_eq_right h1, ite_eq_left h2]
    exact copyFold_slot _ _ _ _ _ _ _ _ _ 9 10 (List.mem_range.mpr (by decide)) qflockSlot_m0
  unfold crOf
  dsimp only
  rw [hL, List.foldl_append, List.foldl_cons]
  obtain ⟨tm, htm, hp⟩ := key (L1.foldl (crStep S gamma t w) (0, #[], 1, 0))
  exact ⟨tm, lineFold_sub S gamma t w _ _ tm (crFold_sub S gamma t w L2 _ tm htm), hp⟩

/-! ## The quotients' terms -/

/-- `quotientTerms`, recursively: chunk `k` at `w[..e]`, scaled by the digits before it. -/
def qTerms (column : ℕ → Column) (w : List E) : List ℕ → ℕ → E → List Term
  | [], _, _ => []
  | e :: rest, k, sc => term (column k) (w.take e) sc :: qTerms column w rest (k + 1) (sc * w.getD e 0)

theorem quotientTerms_eq (column : ℕ → Column) (sizes : List ℕ) (w : List E) (scale : E) :
    quotientTerms column sizes w scale = qTerms column w sizes 0 scale := by
  unfold quotientTerms
  have key : ∀ (sizes : List ℕ) (k : ℕ) (A : Array Term) (sc : E),
      ((sizes.zip (List.range' k sizes.length)).foldl (fun (acc : Array Term × E) (p : ℕ × ℕ) ↦
        (acc.1.push (term (column p.2) (w.take p.1) acc.2), acc.2 * w.getD p.1 0)) (A, sc)).1.toList =
        A.toList ++ qTerms column w sizes k sc := by
    intro sizes
    induction sizes with
    | nil => intro k A sc; simp [qTerms]
    | cons e rest ih =>
      intro k A sc
      rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons, ih]
      simp [qTerms]
  rw [List.range_eq_range', key]
  simp

theorem qTerms_shift (column : ℕ → Column) (w : List E) : ∀ (l : List ℕ) (k : ℕ) (sc : E),
    qTerms column w l (k + 1) sc = qTerms (fun c ↦ column (c + 1)) w l k sc
  | [], _, _ => rfl
  | e :: rest, k, sc => by
    simp only [qTerms]
    rw [qTerms_shift column w rest (k + 1)]

theorem qTerms_mem (column : ℕ → Column) (w : List E) : ∀ (l : List ℕ) (k : ℕ) (sc : E),
    ∀ tm ∈ qTerms column w l k sc, ∃ c < l.length, tm.column = column (k + c) ∧
      tm.point = w.take (l.getD c 0) ∧ tm.twist = 0
  | [], _, _, tm, h => by simp [qTerms] at h
  | e :: rest, k, sc, tm, h => by
    simp only [qTerms, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp [term], by simp [term], rfl⟩
    · obtain ⟨c, hc, h1, h2, h3⟩ := qTerms_mem column w rest (k + 1) _ tm h
      exact ⟨c + 1, by simp; omega, by rw [h1]; ring_nf, by simpa using h2, h3⟩

theorem quotP_cons (S : Shape) (c2 : Stk) (column : ℕ → Column) (e : ℕ) (rest : List ℕ) :
    quotP S c2 column (e :: rest) =
      c2P S c2 (column 0) digitP + digitP e * quotP S c2 (fun c ↦ column (c + 1)) rest := by
  unfold quotP
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
    List.range_zero, List.map_nil, List.prod_nil, mul_one, ← List.sum_map_mul_left]
  refine congrArg (fun z ↦ c2P S c2 (column 0) digitP + z) ?_
  refine congrArg List.sum (List.map_congr_left fun c _ ↦ ?_)
  show c2P S c2 (column (c + 1)) digitP *
      ((List.range (c + 1)).map fun c' ↦ digitP ((e :: rest).getD c' 0)).prod =
    digitP e * (c2P S c2 (column (c + 1)) digitP * ((List.range c).map fun c' ↦ digitP (rest.getD c' 0)).prod)
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  have h : ((fun c' ↦ digitP ((e :: rest).getD c' 0)) ∘ Nat.succ) = fun c' ↦ digitP (rest.getD c' 0) :=
    funext fun c' ↦ by simp
  rw [h, List.getD_cons_zero]
  ring

/-- **A quotient's terms at `t`**: `scale · Q(t)`, where every chunk reads its polynomial at the digits
and the chunks' digits are the digit polynomials'. -/
theorem qTerms_val (S : Shape) (c2 : Stk) (ev : Column → List E → E) (w : List E) (t : E) :
    ∀ (column : ℕ → Column) (sizes : List ℕ) (sc : E),
      (∀ c < sizes.length, ev (column c) (w.take (sizes.getD c 0)) = (c2P S c2 (column c) digitP).eval t) →
      (∀ c < sizes.length, w.getD (sizes.getD c 0) 0 = (digitP (sizes.getD c 0)).eval t) →
      ((qTerms column w sizes 0 sc).map fun tm ↦ tm.coefficient * ev tm.column tm.point).sum =
        sc * (quotP S c2 column sizes).eval t
  | _, [], _, _, _ => by simp [qTerms, quotP]
  | column, e :: rest, sc, hev, hw => by
    simp only [qTerms, List.map_cons, List.sum_cons, term]
    rw [qTerms_shift, qTerms_val S c2 ev w t (fun c ↦ column (c + 1)) rest (sc * w.getD e 0)
      (fun c hc ↦ by simpa using hev (c + 1) (by simp; omega))
      (fun c hc ↦ by simpa using hw (c + 1) (by simp; omega)), quotP_cons]
    have h0 := hev 0 (by simp)
    have hw0 := hw 0 (by simp)
    simp only [List.getD_cons_zero] at h0 hw0
    rw [h0, hw0, Polynomial.eval_add, Polynomial.eval_mul]
    ring

/-! ## The constraint quotient's degree -/

/-- `Shape.constraintDegree`'s step. -/
def cdStep (S : Shape) (d : ℕ) (table : Table) : ℕ :=
  let r := S.heights.getD table.opcode 0
  let n := 2 ^ r
  let d := if table.opcode = opJump then max d (degree n 2) else d
  let d := max d (degree ((n - 1) * (1 + table.countColumns.length)) n)
  if table.opcode = opBlake2s then max d (degree (r * (n / 2)) n) else d

theorem crFold_deg (S : Shape) (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart))
    (s : E × Array Term × E × ℕ), (L.foldl (crStep S gamma t w) s).2.2.2 =
      (L.map Prod.fst).foldl (cdStep S) s.2.2.2
  | [], _ => rfl
  | x :: L, s => by
    rw [List.foldl_cons, crFold_deg S gamma t w L, List.map_cons, List.foldl_cons]
    congr 1
    unfold crStep cdStep
    dsimp only
    by_cases hj : x.1.opcode = opJump
    · have hb : ¬ x.1.opcode = opBlake2s := by rw [hj]; decide
      simp only [ite_eq_left hj, ite_eq_right hb]
    · by_cases hb : x.1.opcode = opBlake2s
      · simp only [ite_eq_right hj, ite_eq_left hb]
      · simp only [ite_eq_right hj, ite_eq_right hb]

/-- **The constraint relation's degree is the shape's** (`constraintDegree`), with a part per table. -/
theorem crOf_deg (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E)
    (hlen : tables.length ≤ parts.length) : (crOf S parts pw gamma t cv w).2 = S.constraintDegree := by
  unfold crOf Shape.constraintDegree
  dsimp only
  rw [crFold_deg, List.map_fst_zip hlen]
  rfl

/-! ## Small facts: digits, coordinates, lifts, `Z_act` -/

theorem digits_length (t : E) (n : ℕ) (hn : 1 ≤ n) : (digits t n).length = n := by
  unfold digits
  have key : ∀ m : ℕ, ((List.range m).foldl (fun (ws : Array E) _ ↦
      let w := ws.back?.getD t
      ws.push (w * w + w)) #[t]).size = m + 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_push, ih]
  rw [List.length_take, Array.length_toList, key]
  omega

theorem take_getD (w : List E) {k l : ℕ} (hl : l < k) : (w.take k).getD l 0 = w.getD l 0 := by
  simp [List.getD_eq_getElem?_getD, hl]

theorem sqn_eq (x : E) : ∀ m, sqn x m = x ^ (2 ^ m)
  | 0 => by simp [sqn]
  | m + 1 => by rw [sqn, sqn_eq (x * x) m, ← pow_two, ← pow_mul, pow_succ', mul_comm]

theorem zip_sum_range (g : K × E → E) (hg : ∀ x, g (0, x) = 0) (f : ℕ → E) :
    ∀ (n : ℕ) (l : List K), ((l.zip ((List.range n).map f)).map g).sum =
      ((List.range n).map fun m ↦ g (l.getD m 0, f m)).sum
  | 0, l => by simp
  | n + 1, [] => by
    simp only [List.zip_nil_left, List.map_nil, List.sum_nil, List.getD_nil, hg]
    simp
  | n + 1, a :: l => by
    rw [List.range_succ_eq_map, List.map_cons, List.zip_cons_cons, List.map_cons, List.sum_cons,
      List.map_map, zip_sum_range g hg (f ∘ Nat.succ) n l, List.map_cons, List.sum_cons, List.map_map]
    congr 1

/-- **`coordinatesAt` is the coordinate functionals' values at `t`.** -/
theorem coordinatesAt_getD (t : E) (a : Array (Array K)) (l : ℕ) (hl : l < a.size) :
    (coordinatesAt t a).getD l 0 = (yP a l).eval t := by
  unfold coordinatesAt yP
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, eval_listSum, List.map_map]
  have hrow : a.toList[l]'(by simpa using hl) = a.getD l #[] := by
    rw [Array.getElem_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl]
    rfl
  rw [hrow]
  rw [Weights.foldl_eq_sum_of _ (fun p ↦ ofK p.1 * p.2) _ 0 (fun acc p _ ↦ by
    obtain ⟨a', x⟩ := p
    by_cases h : a' = 0
    · simp [h]
    · simp [h])]
  rw [zero_add, zip_sum_range (fun p ↦ ofK p.1 * p.2) (fun x ↦ by simp) (sqn t) a.size]
  refine congrArg List.sum (List.map_congr_left fun m _ ↦ ?_)
  simp only [Function.comp_apply, Polynomial.eval_mul, eval_C, eval_pow, eval_X, sqn_eq]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem coordinatesAt_length (t : E) (a : Array (Array K)) : (coordinatesAt t a).length = a.size := by
  simp [coordinatesAt]

/-- **`vanishingRatio` is `liftP` at `t`.** -/
theorem vanishingRatio_eval (w : List E) (t : E) (r m : ℕ) (hw : ∀ j < m, w.getD j 0 = (digitP j).eval t) :
    vanishingRatio w r m = (liftP r m).eval t := by
  unfold vanishingRatio liftP
  rw [Weights.foldl_mul_map (fun j ↦ w.getD j 0 + 1), one_mul, eval_list_prod_of, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun j hj ↦ ?_)
  rw [List.mem_range'_1] at hj
  simp only [Function.comp_apply, Polynomial.eval_add, Polynomial.eval_one, hw j (by omega)]

theorem eval_foldl_mul (f : ℕ → Polynomial E) (g : ℕ → E) (t : E) :
    ∀ (l : List ℕ) (p : Polynomial E) (a : E), p.eval t = a → (∀ b ∈ l, (f b).eval t = g b) →
      (l.foldl (fun prod b ↦ prod * f b) p).eval t = l.foldl (fun prod b ↦ prod * g b) a
  | [], _, _, h, _ => h
  | b :: l, p, a, h, hf => by
    rw [List.foldl_cons, List.foldl_cons]
    exact eval_foldl_mul f g t l _ _ (by rw [Polynomial.eval_mul, h, hf b (List.mem_cons_self ..)])
      fun b' hb' ↦ hf b' (List.mem_cons_of_mem _ hb')

/-- **`activeVanishingFromBits` is `zActP` at `t`.** -/
theorem activeVanishing_eval (w bits : List E) (t : E) (r : ℕ)
    (hw : ∀ j ≤ r, w.getD j 0 = (digitP j).eval t) :
    activeVanishingFromBits w bits r = (zActP bits r).eval t := by
  unfold activeVanishingFromBits zActP
  symm
  refine eval_foldl_mul _ _ t _ _ _ ?_ fun b hb ↦ ?_
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one,
      hw r le_rfl]
  · rw [List.mem_range] at hb
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one,
      hw b hb.le]

end UniSound.Ids.Eval
