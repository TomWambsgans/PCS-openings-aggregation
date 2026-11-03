-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Arith

/-!
# The simulation: pure programs, and the tables' `linearise`

* **Pure programs** (`PHc st p Q`): from the state `st`, the program's recording is a pure step (`PStep`), its result
  and its final state satisfying `Q`. The rules: `phc_pure`, `phc_bind`, `phc_conseq`, the arithmetic operations
  (`phc_add`, `phc_mul`, `phc_const`, `phc_one`, `phc_zero`, `phc_ringWeight`: each node represents the operation's
  value), and the loops (`phc_forIn`: a `for` over a list against a `foldl` of a pure step, the lists' elements
  related; `phc_forIn_same`: the same list). Representations held at a state hold after a pure step
  (`Rp.pgrow`, `RpL.pgrow`, and the `grow` tactic).
* **The representations** of the tables' data: `RpO` (an optional value), `RpSent` (a table's sent values, an array
  of options), `RpPairs` (`linearise`'s terms: the same column, the coefficient represented).
* **`linearise`** (`linearise_phc`): the program's `linearise` is `UniStatement.linearise`, its known part and its
  terms represented, when the tuple has no more slots than there are weights.
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## Pure programs -/

/-- **A pure program's run** from `st`: a pure step, its result and its final state satisfying `Q`. -/
def PHc {α : Type} (st : RecState) (p : Prog α) (Q : α → RecState → Prop) : Prop :=
  PStep st (p.record st).2 ∧ Q (p.record st).1 (p.record st).2

theorem phc_pure {α : Type} {st : RecState} {Q : α → RecState → Prop} (a : α) (hg : Good st) (h : Q a st) :
    PHc st (pure a) Q :=
  ⟨PStep.refl st hg, h⟩

theorem phc_bind {α β : Type} {st : RecState} {p : Prog α} {k : α → Prog β} {Q : α → RecState → Prop}
    {R : β → RecState → Prop} (hp : PHc st p Q) (hk : ∀ a st', PStep st st' → Q a st' → PHc st' (k a) R) :
    PHc st (p >>= k) R := by
  unfold PHc at *
  rw [record_bind]
  obtain ⟨h3, h4⟩ := hk _ _ hp.1 hp.2
  exact ⟨hp.1.trans h3, h4⟩

theorem phc_conseq {α : Type} {st : RecState} {p : Prog α} {Q R : α → RecState → Prop} (hp : PHc st p Q)
    (h : ∀ a st', PStep st st' → Q a st' → R a st') : PHc st p R :=
  ⟨hp.1, h _ _ hp.1 hp.2⟩

section Ops

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- A representation held at `st` holds after a pure step. -/
theorem Rp.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {i : Nat} {x : E}
    (h : Rp π iv publicInput stream st i x) : Rp π iv publicInput stream st' i x :=
  Rp.grow π iv publicInput stream hg.inv.kinv hs.grows h

theorem RpL.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {is : List Nat} {xs : List E}
    (h : RpL π iv publicInput stream st is xs) : RpL π iv publicInput stream st' is xs :=
  RpL.grow π iv publicInput stream hg.inv.kinv hs.grows h

theorem phc_op (st : RecState) (hg : Good st) (o : Op) (ho : Op.Arith o) (hok : OpOK st o) :
    PHc st (Pi1.op o) fun i st' ↦
      Rp π iv publicInput stream st' i (Op.value π publicInput stream st (evalAll π iv publicInput stream st) o) :=
  op_pstep π iv publicInput stream st hg o ho hok

theorem phc_add {st : RecState} (hg : Good st) {a b : Nat} {x y : E} (ha : Rp π iv publicInput stream st a x)
    (hb : Rp π iv publicInput stream st b y) :
    PHc st (Pi1.add a b) fun i st' ↦ Rp π iv publicInput stream st' i (x + y) := by
  have h := phc_op π iv publicInput stream st hg (.add a b) trivial ⟨ha.1, hb.1⟩
  have e : Op.value π publicInput stream st (evalAll π iv publicInput stream st) (.add a b) = x + y := by
    show val π iv publicInput stream st a + val π iv publicInput stream st b = x + y
    rw [ha.2, hb.2]
  rw [e] at h
  exact h

theorem phc_mul {st : RecState} (hg : Good st) {a b : Nat} {x y : E} (ha : Rp π iv publicInput stream st a x)
    (hb : Rp π iv publicInput stream st b y) :
    PHc st (Pi1.mul a b) fun i st' ↦ Rp π iv publicInput stream st' i (x * y) := by
  have h := phc_op π iv publicInput stream st hg (.mul a b) trivial ⟨ha.1, hb.1⟩
  have e : Op.value π publicInput stream st (evalAll π iv publicInput stream st) (.mul a b) = x * y := by
    show val π iv publicInput stream st a * val π iv publicInput stream st b = x * y
    rw [ha.2, hb.2]
  rw [e] at h
  exact h

theorem phc_const {st : RecState} (hg : Good st) (x : E) :
    PHc st (Pi1.const x) fun i st' ↦ Rp π iv publicInput stream st' i x :=
  phc_op π iv publicInput stream st hg (.constant x) trivial trivial

theorem phc_one {st : RecState} (hg : Good st) : PHc st Pi1.one fun i st' ↦ Rp π iv publicInput stream st' i 1 :=
  phc_const π iv publicInput stream hg 1

theorem phc_zero {st : RecState} (hg : Good st) : PHc st Pi1.zero fun i st' ↦ Rp π iv publicInput stream st' i 0 :=
  phc_const π iv publicInput stream hg 0

theorem RpL.length {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) :
    is.length = xs.length :=
  List.Forall₂.length_eq h

theorem RpL.map_val {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) :
    is.map (valE (evalAll π iv publicInput stream st)) = xs := by
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    rw [List.map_cons, ih]
    congr 1
    exact hr.2

theorem RpL.lt {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) :
    ∀ a ∈ is, a < st.nodes.size := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hr.1
    · exact ih a ha

theorem RpL.append {st : RecState} {is js : List Nat} {xs ys : List E} (h1 : RpL π iv publicInput stream st is xs)
    (h2 : RpL π iv publicInput stream st js ys) : RpL π iv publicInput stream st (is ++ js) (xs ++ ys) :=
  List.rel_append h1 h2

theorem RpL.take {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) (n : Nat) :
    RpL π iv publicInput stream st (is.take n) (xs.take n) := by
  induction h generalizing n with
  | nil => cases n <;> exact List.Forall₂.nil
  | cons hr _ ih =>
    cases n with
    | zero => exact List.Forall₂.nil
    | succ n => exact List.Forall₂.cons hr (ih n)

theorem RpL.drop {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) (n : Nat) :
    RpL π iv publicInput stream st (is.drop n) (xs.drop n) := by
  induction h generalizing n with
  | nil => cases n <;> exact List.Forall₂.nil
  | cons hr hl ih =>
    cases n with
    | zero => exact List.Forall₂.cons hr hl
    | succ n => exact ih n

theorem RpL.getD {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) {k : Nat}
    (hk : k < is.length) : Rp π iv publicInput stream st (is.getD k 0) (xs.getD k 0) := by
  induction h generalizing k with
  | nil => simp at hk
  | cons hr _ ih =>
    cases k with
    | zero => simpa using hr
    | succ k => simpa using ih (by simpa using hk)

/-- An array's entry, represented. -/
theorem RpL.arrGetD {st : RecState} {a : Array Nat} {b : Array E}
    (h : RpL π iv publicInput stream st a.toList b.toList) {k : Nat} (hk : k < a.size) :
    Rp π iv publicInput stream st (a.getD k 0) (b.getD k 0) := by
  have e1 : a.getD k 0 = a.toList.getD k 0 := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getD_eq_getElem?_getD]
  have e2 : b.getD k 0 = b.toList.getD k 0 := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getD_eq_getElem?_getD]
  rw [e1, e2]
  exact RpL.getD π iv publicInput stream h (by simpa using hk)

theorem phc_ringWeight {st : RecState} (hg : Good st) {p o m : List Nat} {pv ov mv : List E}
    (hp : RpL π iv publicInput stream st p pv) (ho : RpL π iv publicInput stream st o ov)
    (hm : RpL π iv publicInput stream st m mv) :
    PHc st (Pi1.ringWeight p o m) fun i st' ↦
      Rp π iv publicInput stream st' i (ringWeightValue (pv ++ ov ++ mv) p.length) := by
  have hall := RpL.append π iv publicInput stream (RpL.append π iv publicInput stream hp ho) hm
  have h := phc_op π iv publicInput stream st hg (.ringWeight p o m) trivial (RpL.lt π iv publicInput stream hall)
  have e : Op.value π publicInput stream st (evalAll π iv publicInput stream st) (.ringWeight p o m) =
      ringWeightValue (pv ++ ov ++ mv) p.length := by
    show ringWeightValue ((p ++ o ++ m).map (valE (evalAll π iv publicInput stream st))) p.length = _
    rw [RpL.map_val π iv publicInput stream hall]
  rw [e] at h
  exact h

end Ops

/-- **Grow representation facts along a pure step**: `grow [h₁, …] with hg hs` replaces each `hᵢ` (an `Rp`, `RpL` or
another fact with a `pgrow` lemma) held at `st` by its form at `st'`, for `hg : Good st` and `hs : PStep st st'`. -/
syntax "grow " "[" ident,* "]" " with " term:max ppSpace term:max : tactic

/-- `grow1 h with hg hs`: one fact of `grow`. -/
syntax "grow1 " ident " with " term:max ppSpace term:max : tactic

set_option hygiene false in
macro_rules
  | `(tactic| grow1 $h:ident with $hg $hs') =>
    `(tactic| first
        | replace $h:ident := Rp.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := RpL.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := RpO.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := RpSent.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := RpPairs.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := RpTermsC.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := RpRels.pgrow _ _ _ _ $hg $hs' $h
        | replace $h:ident := RpParts.pgrow _ _ _ _ $hg $hs' $h)

macro_rules
  | `(tactic| grow [] with $_hg $_hs) => `(tactic| skip)
  | `(tactic| grow [$h:ident] with $hg $hs') => `(tactic| grow1 $h with $hg $hs')
  | `(tactic| grow [$h:ident, $hs,*] with $hg $hs') =>
    `(tactic| (grow1 $h with $hg $hs'; grow [$hs,*] with $hg $hs'))

/-! ## Loops -/

/-- **A `for` over a list against a `foldl`**: the program's list and the pure one related elementwise (`E`, kept by a
pure step), each body a pure program that yields, its accumulator related (`R`) to the pure step's. -/
theorem phc_forIn {α α' β γ : Type} (E : α → α' → RecState → Prop)
    (hEm : ∀ a a' st st', Good st → PStep st st' → E a a' st → E a a' st')
    (f : α → β → Prog (ForInStep β)) (g : γ → α' → γ) (R : β → γ → RecState → Prop)
    (hf : ∀ a a' b c st, Good st → E a a' st → R b c st →
      PHc st (f a b) fun r st' ↦ ∃ b', r = .yield b' ∧ R b' (g c a') st') :
    ∀ (lS : List α) (l : List α') (st : RecState) (init : β) (c0 : γ), Good st →
      List.Forall₂ (fun a a' ↦ E a a' st) lS l → R init c0 st →
      PHc st (forIn lS init f) fun b st' ↦ R b (l.foldl g c0) st' := by
  intro lS
  induction lS with
  | nil =>
    intro l st init c0 hg hl h0
    cases hl
    exact phc_pure init hg h0
  | cons a lS ih =>
    intro l st init c0 hg hl h0
    cases hl with
    | @cons _ a' _ l₂ hE hl' =>
      rw [List.forIn_cons]
      refine phc_bind (hf a a' init c0 st hg hE h0) fun r st' hs ⟨b', hr, hR⟩ ↦ ?_
      subst hr
      exact ih l₂ st' b' (g c0 a') hs.good (hl'.imp fun x y h ↦ hEm x y st st' hg hs h) hR

/-- **A `for` over a list against a `foldl` over the same list**, its elements satisfying `P`; the context `C` (kept
by a pure step) available to each body. -/
theorem phc_forIn_same {α β γ : Type} (P : α → Prop) (C : RecState → Prop)
    (hC : ∀ st st', Good st → PStep st st' → C st → C st')
    (f : α → β → Prog (ForInStep β)) (g : γ → α → γ) (R : β → γ → RecState → Prop)
    (hf : ∀ a b c st, Good st → P a → C st → R b c st →
      PHc st (f a b) fun r st' ↦ ∃ b', r = .yield b' ∧ R b' (g c a) st')
    (l : List α) (hl : ∀ a ∈ l, P a) (st : RecState) (init : β) (c0 : γ) (hg : Good st) (hc : C st)
    (h0 : R init c0 st) :
    PHc st (forIn l init f) fun b st' ↦ R b (l.foldl g c0) st' := by
  refine phc_forIn (fun a a' st ↦ a = a' ∧ P a ∧ C st)
    (fun _ _ st st' hg hs h ↦ ⟨h.1, h.2.1, hC st st' hg hs h.2.2⟩)
    f g R (fun a a' b c st hg hE hR ↦ ?_) l l st init c0 hg (List.forall₂_same.mpr fun a ha ↦ ⟨rfl, hl a ha, hc⟩) h0
  obtain ⟨rfl, hP, hC'⟩ := hE
  exact hf a b c st hg hP hC' hR

/-! ## The tables' data -/

section Reps

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- An optional value, represented. -/
def RpO (st : RecState) : Option Nat → Option E → Prop
  | none, none => True
  | some i, some x => Rp π iv publicInput stream st i x
  | _, _ => False

theorem RpO.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {o : Option Nat} {x : Option E}
    (h : RpO π iv publicInput stream st o x) : RpO π iv publicInput stream st' o x := by
  cases o <;> cases x <;> simp only [RpO] at h ⊢
  exact Rp.pgrow π iv publicInput stream hg hs h

/-- **A table's sent values**: an array of options, entry by entry. -/
def RpSent (st : RecState) (a : Array (Option Nat)) (b : Array (Option E)) : Prop :=
  List.Forall₂ (RpO π iv publicInput stream st) a.toList b.toList

theorem RpSent.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {a : Array (Option Nat)}
    {b : Array (Option E)} (h : RpSent π iv publicInput stream st a b) : RpSent π iv publicInput stream st' a b :=
  List.Forall₂.imp (fun _ _ h ↦ RpO.pgrow π iv publicInput stream hg hs h) h

/-- **`linearise`'s terms**: the same column, the coefficient represented. -/
def RpPairs (st : RecState) (a : List (Nat × Nat)) (b : List (Nat × E)) : Prop :=
  List.Forall₂ (fun p q ↦ p.1 = q.1 ∧ Rp π iv publicInput stream st p.2 q.2) a b

theorem RpPairs.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {a : List (Nat × Nat)}
    {b : List (Nat × E)} (h : RpPairs π iv publicInput stream st a b) : RpPairs π iv publicInput stream st' a b :=
  List.Forall₂.imp (fun _ _ h ↦ ⟨h.1, Rp.pgrow π iv publicInput stream hg hs h.2⟩) h

end Reps

/-! ## Lists -/

theorem forall₂_getElem?_getD {α β : Type} {R : α → β → Prop} {l : List α} {m : List β} (h : List.Forall₂ R l m)
    (d : α) (d' : β) (hd : R d d') (i : Nat) : R (l[i]?.getD d) (m[i]?.getD d') := by
  induction h generalizing i with
  | nil => simpa using hd
  | cons hr _ ih =>
    cases i with
    | zero => simpa using hr
    | succ i => simpa using ih i

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} {l : List α} {m : List β} (h : List.Forall₂ R l m)
    (i : Nat) (hi : i < l.length) (hj : i < m.length) : R l[i] m[i] := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hr _ ih =>
    cases i with
    | zero => exact hr
    | succ i => exact ih i (by simpa using hi) (by simpa using hj)

theorem forall₂_set_modify {α β : Type} {R : α → β → Prop} {l : List α} {m : List β} (h : List.Forall₂ R l m)
    (i : Nat) (x : α) (f : β → β) (hx : ∀ hi : i < m.length, R x (f m[i])) :
    List.Forall₂ R (l.set i x) (m.modify i f) := by
  induction h generalizing i with
  | nil => cases i <;> exact List.Forall₂.nil
  | cons hr hl ih =>
    cases i with
    | zero => exact List.Forall₂.cons (hx (by simp)) hl
    | succ i => exact List.Forall₂.cons hr (ih i fun hi ↦ hx (by simpa using hi))

theorem arr_findIdx?_toList {α : Type} (a : Array α) (p : α → Bool) : a.findIdx? p = a.toList.findIdx? p := by
  cases a
  exact List.findIdx?_toArray p _

/-! ## `linearise` -/

section Linearise

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

theorem RpSent.getD {st : RecState} {a : Array (Option Nat)} {b : Array (Option E)}
    (h : RpSent π iv publicInput stream st a b) (i : Nat) :
    RpO π iv publicInput stream st (a.getD i none) (b.getD i none) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← Array.getElem?_toList]
  exact forall₂_getElem?_getD h none none trivial i

theorem RpPairs.map_fst {st : RecState} {a : List (Nat × Nat)} {b : List (Nat × E)}
    (h : RpPairs π iv publicInput stream st a b) : a.map (·.1) = b.map (·.1) := by
  induction h with
  | nil => rfl
  | cons hr _ ih => rw [List.map_cons, List.map_cons, ih, hr.1]

/-- **`linearise`'s `add`.** -/
theorem addTermS_phc {st : RecState} (hg : Good st) {termsS : Array (Nat × Nat)} {terms : List (Nat × E)}
    (ht : RpPairs π iv publicInput stream st termsS.toList terms) (column : Nat) {cS : Nat} {c : E}
    (hc : Rp π iv publicInput stream st cS c) :
    PHc st (Pi1.addTermS termsS column cS) fun r st' ↦
      RpPairs π iv publicInput stream st' r.toList (UniStatement.addTerm terms column c) := by
  have hfind : termsS.findIdx? (fun x : Nat × Nat ↦ x.1 == column) =
      terms.findIdx? (fun x : Nat × E ↦ x.1 == column) := by
    rw [arr_findIdx?_toList]
    have h2 : termsS.toList.findIdx? (fun x : Nat × Nat ↦ x.1 == column) =
        (termsS.toList.map (·.1)).findIdx? (· == column) := by
      rw [List.findIdx?_map]
      rfl
    have h3 : terms.findIdx? (fun x : Nat × E ↦ x.1 == column) = (terms.map (·.1)).findIdx? (· == column) := by
      rw [List.findIdx?_map]
      rfl
    rw [h2, h3, RpPairs.map_fst π iv publicInput stream ht]
  have hlen : termsS.toList.length = terms.length := List.Forall₂.length_eq ht
  unfold Pi1.addTermS UniStatement.addTerm
  rw [hfind]
  cases hi : terms.findIdx? (fun x : Nat × E ↦ x.1 == column) with
  | none =>
    dsimp only
    refine phc_pure _ hg ?_
    rw [Array.toList_push]
    exact List.rel_append ht (List.Forall₂.cons ⟨rfl, hc⟩ List.Forall₂.nil)
  | some i =>
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
    have hlt' : i < termsS.toList.length := by omega
    have hget : termsS.getD i (0, 0) = termsS.toList[i]'hlt' := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hlt', Option.getD_some]
    have he := forall₂_getElem ht i hlt' hlt
    dsimp only
    rw [hget]
    refine phc_bind (phc_add π iv publicInput stream hg he.2 hc) fun v st' hs hv ↦ phc_pure _ hs.good ?_
    rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    refine forall₂_set_modify (RpPairs.pgrow π iv publicInput stream hg hs ht) i _ _ fun _ ↦ ?_
    show column = terms[i].1 ∧ Rp π iv publicInput stream st' v (terms[i].2 + c)
    simp only [beq_iff_eq] at hp
    exact ⟨hp.symm, hv⟩

/-- **`linearise`**: the program's known part and terms represent `UniStatement`'s, when the tuple has no more slots
than there are weights. -/
theorem linearise_phc {st : RecState} (hg : Good st) (tuple : List Form) {weightsS : Array Nat} {weights : Array E}
    {sentS : Array (Option Nat)} {sent : Array (Option E)}
    (hw : RpL π iv publicInput stream st weightsS.toList weights.toList)
    (hs : RpSent π iv publicInput stream st sentS sent) (hlen : tuple.length ≤ weights.size) :
    PHc st (Pi1.linearise tuple weightsS sentS) fun res st' ↦
      Rp π iv publicInput stream st' res.1 (UniStatement.linearise tuple weights sent).1 ∧
        RpPairs π iv publicInput stream st' res.2 (UniStatement.linearise tuple weights sent).2 := by
  have hsize : weightsS.size = weights.size := by
    have := RpL.length π iv publicInput stream hw
    simpa using this
  unfold Pi1.linearise UniStatement.linearise
  refine phc_bind (phc_zero π iv publicInput stream hg) fun known st1 hs1 hk ↦ ?_
  grow [hw, hs] with hg hs1
  refine phc_bind (phc_forIn_same (fun x : Form × Nat ↦ x.2 < tuple.length)
    (fun st ↦ RpL π iv publicInput stream st weightsS.toList weights.toList ∧
      RpSent π iv publicInput stream st sentS sent)
    (fun _ _ hg hs h ↦ ⟨RpL.pgrow π iv publicInput stream hg hs h.1, RpSent.pgrow π iv publicInput stream hg hs h.2⟩)
    _ _ (fun (b : Nat × Array (Nat × Nat)) (c : E × List (Nat × E)) st ↦
      Rp π iv publicInput stream st b.1 c.1 ∧ RpPairs π iv publicInput stream st b.2.toList c.2)
    ?_ _ ?_ st1 _ _ hs1.good ⟨hw, hs⟩ ⟨hk, List.Forall₂.nil⟩) fun r st2 hs2 hr ↦ phc_pure _ hs2.good hr
  · rintro ⟨form, s⟩ b c st hg hP ⟨hw, hsent⟩ hR
    have hs' : s < weightsS.size := by
      have : s < tuple.length := hP
      omega
    have hwt := RpL.arrGetD π iv publicInput stream hw hs'
    dsimp only
    rw [ite_eq_left hs']
    refine phc_bind (phc_forIn_same (fun _ ↦ True)
      (fun st ↦ Rp π iv publicInput stream st (weightsS.getD s 0) (weights.getD s 0) ∧
        RpSent π iv publicInput stream st sentS sent)
      (fun _ _ hg hs h ↦ ⟨Rp.pgrow π iv publicInput stream hg hs h.1, RpSent.pgrow π iv publicInput stream hg hs h.2⟩)
      _ _ (fun (b : Nat × Array (Nat × Nat)) (c : E × List (Nat × E)) st ↦
        Rp π iv publicInput stream st b.1 c.1 ∧ RpPairs π iv publicInput stream st b.2.toList c.2)
      ?_ form (fun _ _ ↦ trivial) st _ _ hg ⟨hwt, hsent⟩ hR) fun r st' hs hr ↦
        phc_pure _ hs.good ⟨_, rfl, hr⟩
    rintro ⟨monomial, coefficient⟩ b ⟨kn, tms⟩ st hg - ⟨hwt, hsent⟩ ⟨hkn, htm⟩
    dsimp only
    by_cases hc0 : coefficient = 0
    · simp only [ite_eq_left hc0]
      exact phc_pure _ hg ⟨_, rfl, hkn, htm⟩
    · simp only [ite_eq_right hc0]
      refine phc_bind (phc_const π iv publicInput stream hg coefficient) fun cc st1 hs1 hcc ↦ ?_
      grow [hwt, hsent, hkn, htm] with hg hs1
      refine phc_bind (phc_mul π iv publicInput stream hs1.good hwt hcc) fun cS st2 hs2 hcS ↦ ?_
      grow [hsent, hkn, htm] with hs1.good hs2
      have hg2 := hs2.good
      rcases monomial with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
      · exact phc_bind (phc_add π iv publicInput stream hg2 hkn hcS) fun _ st3 hs3 hk ↦
          phc_pure _ hs3.good ⟨_, rfl, hk, RpPairs.pgrow π iv publicInput stream hg2 hs3 htm⟩
      · dsimp only
        have ho := RpSent.getD π iv publicInput stream hsent i
        revert ho
        cases sentS.getD i none <;> cases sent.getD i none <;> intro ho <;> simp only [RpO] at ho
        · exact phc_bind (addTermS_phc π iv publicInput stream hg2 htm i hcS) fun _ st3 hs3 ht ↦
            phc_pure _ hs3.good ⟨_, rfl, Rp.pgrow π iv publicInput stream hg2 hs3 hkn, ht⟩
        · refine phc_bind (phc_mul π iv publicInput stream hg2 hcS ho) fun _ st3 hs3 hcv ↦ ?_
          exact phc_bind (phc_add π iv publicInput stream hs3.good
            (Rp.pgrow π iv publicInput stream hg2 hs3 hkn) hcv) fun _ st4 hs4 hk ↦
            phc_pure _ hs4.good ⟨_, rfl, hk, RpPairs.pgrow π iv publicInput stream hs3.good hs4
              (RpPairs.pgrow π iv publicInput stream hg2 hs3 htm)⟩
      · dsimp only
        have hoi := RpSent.getD π iv publicInput stream hsent i
        have hoj := RpSent.getD π iv publicInput stream hsent j
        revert hoi hoj
        cases sentS.getD i none <;> cases sent.getD i none <;> cases sentS.getD j none <;>
          cases sent.getD j none <;> intro hoi hoj <;> simp only [RpO] at hoi hoj
        · exact phc_pure _ hg2 ⟨_, rfl, hkn, htm⟩
        · refine phc_bind (phc_mul π iv publicInput stream hg2 hcS hoj) fun _ st3 hs3 hcb ↦ ?_
          exact phc_bind (addTermS_phc π iv publicInput stream hs3.good
            (RpPairs.pgrow π iv publicInput stream hg2 hs3 htm) i hcb) fun _ st4 hs4 ht ↦
            phc_pure _ hs4.good ⟨_, rfl, Rp.pgrow π iv publicInput stream hs3.good hs4
              (Rp.pgrow π iv publicInput stream hg2 hs3 hkn), ht⟩
        · refine phc_bind (phc_mul π iv publicInput stream hg2 hcS hoi) fun _ st3 hs3 hca ↦ ?_
          exact phc_bind (addTermS_phc π iv publicInput stream hs3.good
            (RpPairs.pgrow π iv publicInput stream hg2 hs3 htm) j hca) fun _ st4 hs4 ht ↦
            phc_pure _ hs4.good ⟨_, rfl, Rp.pgrow π iv publicInput stream hs3.good hs4
              (Rp.pgrow π iv publicInput stream hg2 hs3 hkn), ht⟩
        · refine phc_bind (phc_mul π iv publicInput stream hg2 hcS hoi) fun _ st3 hs3 hca ↦ ?_
          refine phc_bind (phc_mul π iv publicInput stream hs3.good hca
            (Rp.pgrow π iv publicInput stream hg2 hs3 hoj)) fun _ st4 hs4 hcab ↦ ?_
          have hkn4 := Rp.pgrow π iv publicInput stream hs3.good hs4 (Rp.pgrow π iv publicInput stream hg2 hs3 hkn)
          have htm4 := RpPairs.pgrow π iv publicInput stream hs3.good hs4
            (RpPairs.pgrow π iv publicInput stream hg2 hs3 htm)
          exact phc_bind (phc_add π iv publicInput stream hs4.good hkn4 hcab) fun _ st5 hs5 hk ↦
            phc_pure _ hs5.good ⟨_, rfl, hk, RpPairs.pgrow π iv publicInput stream hs4.good hs5 htm4⟩
      · exact phc_pure _ hg2 ⟨_, rfl, hkn, htm⟩
  · intro x hx
    exact List.mem_range.mp (List.of_mem_zip hx).2

end Linearise

end RecGraph.Sim
