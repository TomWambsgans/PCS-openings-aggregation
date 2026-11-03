-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The heap's leaf columns in closed form are
-- `formal/UniComplete`'s (`ProverBounds.lean`: `id_forIn_foldl`, `leafCols`, `heapRelations_snd`), the relations'
-- `formal/UniSound`'s (`Ids/Eval.lean`: `heapRelations_fst`, `blockRel`; `constraintRelation_eq`, `crOf`).
import RecGraph.Sim.Claims
import RecGraph.Sim.Pure
import RecGraph.Sim.ComposeSpec
import UniSound.Ids.Eval
import UniSound.Ids.Deployed

/-!
# The simulation: the constraint and heap relations

* `quotientTerms_phc`: a quotient's terms on its chunks.
* `heapRelations_phc`: the program's heap relations represent `UniStatement`'s (`UniSound`'s closed form,
  `heapRelations_fst`), and its leaf columns are `UniStatement`'s (`heapRelations_sndC`).
* Node `0`, the seed, is worth `0` (`rp_zero_of_seed`): an out-of-range read of a node list is `UniStatement`'s
  default.
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## `Id` loops (`UniComplete.Bounds`) -/

theorem id_forIn_foldlC {γ β δ : Type} (l : List γ) (b : β) (f : γ → β → Id (ForInStep β)) (p : β → δ)
    (g : δ → γ → δ) (hf : ∀ a s, ∃ s', f a s = .yield s' ∧ p s' = g (p s) a) :
    p (Id.run (forIn l b f)) = l.foldl g (p b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨s', hs, hp⟩ := hf a b
    rw [List.forIn_cons, hs]
    change p (Id.run (forIn l s' f)) = _
    rw [ih s', hp]
    rfl

theorem id_bind_foldlC {γ β δ α : Type} {l : List γ} {b : β} {f : γ → β → Id (ForInStep β)} {k : β → Id α}
    {P : α → Prop} (p : β → δ) (g : δ → γ → δ) (hf : ∀ a s, ∃ s', f a s = .yield s' ∧ p s' = g (p s) a)
    (hk : ∀ s, p s = l.foldl g (p b) → P (Id.run (k s))) : P (Id.run (forIn l b f >>= k)) :=
  hk _ (id_forIn_foldlC l b f p g hf)

/-- A leaf quotient's chunks as `C2`'s columns. -/
def chunkColsC (index d : ℕ) : Array (Column × ℕ × Bool) :=
  Array.map (fun (x : ℕ × ℕ) ↦ match x with | (e, chunk) => (Column.leafQuotient index chunk, e, true))
    ((chunks (d + 1)).zip (List.range (chunks (d + 1)).length)).toArray

/-- **A heap block's leaf quotient's columns**, a table's degree from its part. -/
def leafColsC (parts : List TablePart) (block : Block) (index : ℕ) : Array (Column × ℕ × Bool) :=
  match block.leaves with
  | .unused => #[]
  | .memory => chunkColsC index (degree (2 * (2 ^ block.r - 1)) (2 ^ block.r))
  | .bytecode => chunkColsC index (degree (2 * (2 ^ block.r - 1)) (2 ^ block.r))
  | .table t => chunkColsC index (degree (max (parts.getD t default).pullDegree (parts.getD t default).pushDegree *
      (2 ^ block.r - 1) + (2 ^ block.r - Shape.leastRows block.r)) (2 ^ block.r))

theorem foldl_append_toListC {α β : Type} (G : α → Array β) :
    ∀ (l : List α) (init : Array β),
      (l.foldl (fun cols x ↦ cols ++ G x) init).toList = init.toList ++ l.flatMap fun x ↦ (G x).toList
  | [], init => by simp
  | a :: l, init => by
    rw [List.foldl_cons, foldl_append_toListC G l, Array.toList_append, List.flatMap_cons, List.append_assoc]

/-- **The heap's leaf columns are the blocks'** (`UniComplete`'s `heapRelations_snd`). -/
theorem heapRelations_sndC (shape : UniStatement.Shape) (active : List E) (parts : List TablePart)
    (weights : Array E) (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : E)
    (w : List E) (constraintChunks : List ℕ) :
    (UniStatement.heapRelations shape active parts weights beta heapValue constraintValue memoryPull memoryPush
      bytecodePull bytecodePush w constraintChunks).2 =
      (shape.heap.blocks.zip (List.range shape.heap.blocks.length)).flatMap fun x ↦
        (leafColsC parts x.1 x.2).toList := by
  unfold UniStatement.heapRelations
  refine id_bind_foldlC (P := fun r : List Relation × List (Column × ℕ × Bool) ↦ r.2 = _)
    (fun s : Array Relation × Array (Column × ℕ × Bool) ↦ s.2)
    (fun cols (x : Block × ℕ) ↦ cols ++ leafColsC parts x.1 x.2) ?_ fun s hs ↦ ?_
  · intro x s
    obtain ⟨⟨leaves, r, position⟩, index⟩ := x
    cases leaves
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, Array.append_empty.symm⟩
  · show s.2.toList = _
    rw [hs, foldl_append_toListC]
    rfl

section Rel

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **Node `0`, the seed, is worth `0`**: a state value has no element. -/
theorem rp_zero_of_seed {st : RecState} (hg : Good st) (hs : st.nodes[0]? = some Node.seed) :
    Rp π iv publicInput stream st 0 0 := by
  have hi : 0 < st.nodes.size := by
    rcases Nat.eq_zero_or_pos st.nodes.size with h | h
    · rw [Array.getElem?_eq_none (by omega)] at hs
      exact absurd hs (by simp)
    · exact h
  refine ⟨hi, ?_⟩
  have h0 : st.nodes[0] = Node.seed := by
    rw [Array.getElem?_eq_getElem hi] at hs
    exact Option.some.inj hs
  show valE (evalAll π iv publicInput stream st) 0 = 0
  unfold valE
  rw [evalAll_node π iv publicInput stream st hg.inv 0 hi, h0]
  rfl

/-- **A table's part, represented**: its products represented, its degrees equal, its sent values represented. -/
def RpPart (st : RecState) (p : TablePartS) (u : TablePart) : Prop :=
  Rp π iv publicInput stream st p.pull u.pull ∧ Rp π iv publicInput stream st p.push u.push ∧
    p.pullDegree = u.pullDegree ∧ p.pushDegree = u.pushDegree ∧ RpSent π iv publicInput stream st p.sent u.sent

theorem RpO.grow {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {o : Option Nat} {x : Option E}
    (h : RpO π iv publicInput stream st o x) : RpO π iv publicInput stream st' o x := by
  cases o <;> cases x <;> simp only [RpO] at h ⊢
  exact Rp.grow π iv publicInput stream hk hgr h

theorem RpPart.grow {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {p : TablePartS} {u : TablePart}
    (h : RpPart π iv publicInput stream st p u) : RpPart π iv publicInput stream st' p u :=
  ⟨Rp.grow π iv publicInput stream hk hgr h.1, Rp.grow π iv publicInput stream hk hgr h.2.1, h.2.2.1, h.2.2.2.1,
    List.Forall₂.imp (fun _ _ h ↦ RpO.grow π iv publicInput stream hk hgr h) h.2.2.2.2⟩

theorem RpPart.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {p : TablePartS} {u : TablePart}
    (h : RpPart π iv publicInput stream st p u) : RpPart π iv publicInput stream st' p u :=
  RpPart.grow π iv publicInput stream hg.inv.kinv hs.grows h

/-- **`Relations::equal`**: one term, coefficient one. -/
theorem equalS_phcC {st : RecState} (hg : Good st) (col : Column) {pt : List Nat} {ptE : List E} {v : Nat} {vE : E}
    (hp : RpL π iv publicInput stream st pt ptE) (hv : Rp π iv publicInput stream st v vE) :
    PHc st (Pi1.equalS col pt v) fun r st' ↦ RpRel π iv publicInput stream st' r (Relation.equal col ptE vE) := by
  unfold Pi1.equalS
  exact phc_bind (phc_one π iv publicInput stream hg) fun o st1 hs1 ho ↦ phc_pure _ hs1.good
    ⟨List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hg hs1 hp, ho⟩ List.Forall₂.nil, Rp.pgrow hg hs1 hv⟩

/-- **`quotient_terms`**: a quotient's terms on its chunks, chunk `c` at `w[..e_c]`. -/
theorem quotientTerms_phc {st : RecState} (hg : Good st) (h0 : Rp π iv publicInput stream st 0 0)
    (column : ℕ → Column) (sizes : List ℕ) {w : List Nat} {wE : List E} (hw : RpL π iv publicInput stream st w wE)
    {sc : Nat} {scE : E} (hsc : Rp π iv publicInput stream st sc scE) :
    PHc st (Pi1.quotientTerms column sizes w sc) fun ts st' ↦
      RpTermsC π iv publicInput stream st' ts (UniStatement.quotientTerms column sizes wE scE) := by
  unfold Pi1.quotientTerms UniStatement.quotientTerms
  refine phc_bind (phc_forIn_same (fun _ ↦ True)
    (fun s ↦ RpL π iv publicInput stream s w wE ∧ Rp π iv publicInput stream s 0 0)
    (fun _ _ hg hs h ↦ ⟨RpL.pgrow hg hs h.1, Rp.pgrow hg hs h.2⟩) _ _
    (fun (b : Nat × Array TermS) (acc : Array Term × E) s ↦ Rp π iv publicInput stream s b.1 acc.2 ∧
      RpTermsC π iv publicInput stream s b.2.toList acc.1.toList) ?_ _ (fun _ _ ↦ trivial) st (sc, #[]) (#[], scE) hg
    ⟨hw, h0⟩ ⟨hsc, List.Forall₂.nil⟩) fun r st' hs hr ↦ phc_pure _ hs.good hr.2
  rintro ⟨e, chunk⟩ ⟨f, out⟩ ⟨outE, fE⟩ s hg _ ⟨hw, h0⟩ ⟨hf, hout⟩
  dsimp only at hf hout ⊢
  refine phc_bind (phc_mul π iv publicInput stream hg hf (RpL.getDz π iv publicInput stream hw h0 e))
    fun f' s1 hs1 hf' ↦ phc_pure _ hs1.good ⟨_, rfl, hf', ?_⟩
  rw [Array.toList_push, Array.toList_push]
  exact List.rel_append (RpTermsC.pgrow π iv publicInput stream hg hs1 hout)
    (List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hg hs1 hw) e, Rp.pgrow hg hs1 hf⟩
      List.Forall₂.nil)

theorem RpL.arrGetD0 {st : RecState} {a : Array Nat} {b : Array E}
    (h : RpL π iv publicInput stream st a.toList b.toList) (h0 : Rp π iv publicInput stream st 0 0) (k : Nat) :
    Rp π iv publicInput stream st (a.getD k 0) (b.getD k 0) := by
  have e : b.getD k 0 = b.toList.getD k 0 := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getD_eq_getElem?_getD]
  rw [e]
  exact RpL.arrGetDz π iv publicInput stream h h0 k

theorem foldl_snoc_mapC {α β : Type} (f : α → β) (l : List α) (a0 : List β) :
    l.foldl (fun a x ↦ a ++ [f x]) a0 = a0 ++ l.map f := by
  induction l generalizing a0 with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.append_assoc, List.singleton_append]

/-- **A list of nodes built one node at a time**: the program's `for k in [0:n]` pushing a node worth `f k`. -/
theorem phc_snoc_range {st : RecState} (hg : Good st) (C : RecState → Prop)
    (hC : ∀ st st', Good st → PStep st st' → C st → C st') (hc : C st) (n : ℕ) (f : ℕ → E)
    (body : ℕ → Array Nat → Prog (ForInStep (Array Nat)))
    (hb : ∀ k b s, Good s → C s → k < n →
      PHc s (body k b) fun r s' ↦ ∃ v, r = .yield (b.push v) ∧ Rp π iv publicInput stream s' v (f k)) :
    PHc st (forIn [0:n] #[] body) fun r st' ↦
      RpL π iv publicInput stream st' r.toList ((List.range n).map f) ∧ C st' := by
  rw [forIn_range, Nat.sub_zero, ← List.range_eq_range', ← List.nil_append ((List.range n).map f),
    ← foldl_snoc_mapC]
  refine phc_conseq (phc_forIn_same (fun k ↦ k < n) C hC body (fun a x ↦ a ++ [f x])
    (fun (b : Array Nat) (l : List E) s ↦ RpL π iv publicInput stream s b.toList l ∧ C s) ?_ (List.range n)
    (fun k hk ↦ List.mem_range.mp hk) st #[] [] hg hc ⟨List.Forall₂.nil, hc⟩) fun _ _ _ h ↦ h
  intro k b l s hg' hk _ ⟨hbl, hcs⟩
  refine phc_conseq (hb k b s hg' hcs hk) fun r s' hs ⟨v, hr, hv⟩ ↦ ⟨_, hr, ?_, hC s s' hg' hs hcs⟩
  rw [Array.toList_push]
  exact List.rel_append (RpL.pgrow hg' hs hbl) (List.Forall₂.cons hv List.Forall₂.nil)

/-- The heap's inputs, represented. -/
structure HeapCtx (st : RecState) (active : List Nat) (activeE : List E) (parts : List TablePartS)
    (partsE : List TablePart) (weights : Array Nat) (weightsE : Array E) (w : List Nat) (wE : List E) : Prop where
  h0 : Rp π iv publicInput stream st 0 0
  ha : RpL π iv publicInput stream st active activeE
  hp : List.Forall₂ (RpPart π iv publicInput stream st) parts partsE
  hw : RpL π iv publicInput stream st weights.toList weightsE.toList
  hwE : RpL π iv publicInput stream st w wE

theorem HeapCtx.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {active activeE parts partsE weights
    weightsE w wE} (h : HeapCtx π iv publicInput stream st active activeE parts partsE weights weightsE w wE) :
    HeapCtx π iv publicInput stream st' active activeE parts partsE weights weightsE w wE :=
  ⟨Rp.pgrow hg hs h.h0, RpL.pgrow hg hs h.ha, h.hp.imp fun _ _ h ↦ RpPart.pgrow π iv publicInput stream hg hs h,
    RpL.pgrow hg hs h.hw, RpL.pgrow hg hs h.hwE⟩

theorem forall₂_getD_partC {st : RecState} {parts : List TablePartS} {partsE : List TablePart}
    (hp : List.Forall₂ (RpPart π iv publicInput stream st) parts partsE) {t : ℕ} (ht : t < partsE.length)
    (d : TablePartS) (d' : TablePart) : RpPart π iv publicInput stream st (parts.getD t d) (partsE.getD t d') := by
  have hlen := List.Forall₂.length_eq hp
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ ht]
  exact forall₂_getElemC hp t (by omega) ht

theorem heap_foldlC {α β γ : Type} (F : γ → α) (G : γ → List β) (l : List γ) (a : List α) (b : List β) :
    l.foldl (fun (acc : List α × List β) x ↦ (acc.1 ++ [F x], acc.2 ++ G x)) (a, b) =
      (a ++ l.map F, b ++ l.flatMap G) := by
  induction l generalizing a b with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih]; simp

/-- **The heap's relations** (`heapRelations` at π1-rec3's shape): the program's represent `UniStatement`'s, and its
leaf columns are `UniStatement`'s. -/
theorem heapRelations_phc {st : RecState} (hg : Good st) {active : List Nat} {activeE : List E}
    {parts : List TablePartS} {partsE : List TablePart} {weights : Array Nat} {weightsE : Array E}
    {w : List Nat} {wE : List E}
    (hc : HeapCtx π iv publicInput stream st active activeE parts partsE weights weightsE w wE)
    (hp6 : partsE.length = 6) {beta hv cv mpl mps bpl bps : Nat} {betaE hvE cvE mplE mpsE bplE bpsE : E}
    (hbeta : Rp π iv publicInput stream st beta betaE) (hhv : Rp π iv publicInput stream st hv hvE)
    (hcv : Rp π iv publicInput stream st cv cvE) (hmpl : Rp π iv publicInput stream st mpl mplE)
    (hmps : Rp π iv publicInput stream st mps mpsE) (hbpl : Rp π iv publicInput stream st bpl bplE)
    (hbps : Rp π iv publicInput stream st bps bpsE) (cc : List ℕ) :
    PHc st (Pi1.heapRelations reference active parts weights beta hv cv mpl mps bpl bps w cc) fun a st' ↦
      RpRels π iv publicInput stream st' a.1
        (UniStatement.heapRelations reference activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE cc).1 ∧
      a.2 = (UniStatement.heapRelations reference activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE
        cc).2 := by
  rw [UniSound.Ids.Eval.heapRelations_fst, heapRelations_sndC]
  unfold Pi1.heapRelations
  dsimp only
  have hT := RpL.takeC π iv publicInput stream hc.hwE reference.heap.h
  -- `T(t)`.
  refine phc_bind (phc_one π iv publicInput stream hg) fun o st1 hs1 ho ↦ ?_
  have hc1 := HeapCtx.pgrow π iv publicInput stream hg hs1 hc
  refine phc_bind (equalS_phcC π iv publicInput stream hs1.good .heap (RpL.pgrow hg hs1 hT)
    (Rp.pgrow hg hs1 hhv)) fun r1 st2 hs2 hr1 ↦ ?_
  have hs02 := hs1.trans hs2
  -- The tree.
  refine phc_bind (phc_add π iv publicInput stream hs2.good
    (RpL.getDz π iv publicInput stream (RpL.pgrow hg hs02 hT) (Rp.pgrow hg hs02 hc.h0) 0)
    (Rp.pgrow hs1.good hs2 ho)) fun n0 st3 hs3 hn0 ↦ ?_
  have hs03 := hs02.trans hs3
  refine phc_bind (phc_mul π iv publicInput stream hs3.good
    (RpL.getDz π iv publicInput stream (RpL.pgrow hg hs03 hc.hwE) (Rp.pgrow hg hs03 hc.h0) 1)
    (Rp.pgrow hg hs03 hhv)) fun w1v st4 hs4 hw1v ↦ ?_
  have hs04 := hs03.trans hs4
  have hwh4 := RpL.getDz π iv publicInput stream (RpL.pgrow hg hs04 hc.hwE) (Rp.pgrow hg hs04 hc.h0)
    reference.heap.h
  refine phc_bind (phc_mul π iv publicInput stream hs4.good hwh4 hwh4) fun whh st5 hs5 hwhh ↦ ?_
  refine phc_bind (phc_zero π iv publicInput stream hs5.good) fun z st6 hs6 hz ↦ ?_
  have hs06 := hs04.trans (hs5.trans hs6)
  have hs36 := hs4.trans (hs5.trans hs6)
  have hr2 : RpRel π iv publicInput stream st6
      { terms := [termS .heap ((w.drop 1).take reference.heap.h) (w.getD 1 0),
          termS .heap ((w.take reference.heap.h).set 0 n0) w1v,
          termS (.treeQuotient 0) (w.take reference.heap.h) (w.getD reference.heap.h 0),
          termS (.treeQuotient 1) [] whh], value := z }
      { terms := [term .heap ((wE.drop 1).take reference.heap.h) (wE.getD 1 0),
          term .heap ((wE.take reference.heap.h).modify 0 (· + 1)) (wE.getD 1 0 * hvE),
          term (.treeQuotient 0) (wE.take reference.heap.h) (wE.getD reference.heap.h 0),
          term (.treeQuotient 1) [] (wE.getD reference.heap.h 0 * wE.getD reference.heap.h 0)], value := 0 } := by
    have hw6 := RpL.pgrow hg hs06 hc.hwE
    have h06 := Rp.pgrow hg hs06 hc.h0
    refine ⟨?_, hz⟩
    refine List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.dropC π iv publicInput stream hw6 1) _,
      RpL.getDz π iv publicInput stream hw6 h06 1⟩ ?_
    refine List.Forall₂.cons ⟨rfl, rfl, ?_, Rp.pgrow hs4.good (hs5.trans hs6) hw1v⟩ ?_
    · refine forall₂_set_modifyC (RpL.takeC π iv publicInput stream hw6 _) 0 _ _ fun hi ↦ ?_
      have := Rp.pgrow hs3.good hs36 hn0
      rw [← List.getD_eq_getElem _ 0 hi]
      exact this
    refine List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream hw6 _,
      RpL.getDz π iv publicInput stream hw6 h06 _⟩ ?_
    exact List.Forall₂.cons ⟨rfl, rfl, List.Forall₂.nil, Rp.pgrow hs5.good hs6 hwhh⟩ List.Forall₂.nil
  -- The root.
  have ho6 := Rp.pgrow hs1.good (hs2.trans (hs3.trans hs36)) ho
  refine phc_bind (phc_snoc_range π iv publicInput stream hs6.good (fun s ↦ Rp π iv publicInput stream s o 1)
    (fun _ _ hg hs h ↦ Rp.pgrow hg hs h) ho6 reference.heap.h (fun l ↦ if l = 0 then (1 : E) else 0) _ ?_)
    fun atOne st7 hs7 ⟨hatOne, ho7⟩ ↦ ?_
  · intro k b s hg' hos _
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]
      exact phc_bind (phc_pure _ hg' hos) fun v s' hs' hv ↦ phc_pure _ hs'.good ⟨v, rfl, hv⟩
    · simp only [hk, ↓reduceIte]
      exact phc_bind (phc_zero π iv publicInput stream hg') fun v s' hs' hv ↦ phc_pure _ hs'.good ⟨v, rfl, hv⟩
  have hs07 := hs06.trans hs7
  have hc7 := HeapCtx.pgrow π iv publicInput stream hg hs07 hc
  have hw07 := fun k ↦ RpL.arrGetD0 π iv publicInput stream hc7.hw hc7.h0 k
  refine phc_bind (phc_const π iv publicInput stream hs7.good sepState) fun c1 st8 hs8 hc1' ↦ ?_
  refine phc_bind (phc_mul π iv publicInput stream hs8.good (Rp.pgrow hs7.good hs8 (hw07 0)) hc1')
    fun w0s st9 hs9 hw0s ↦ ?_
  have hs79 := hs8.trans hs9
  refine phc_bind (phc_add π iv publicInput stream hs9.good (Rp.pgrow hg (hs07.trans hs79) hbeta) hw0s)
    fun i1 st10 hs10 hi1 ↦ ?_
  have hs710 := hs79.trans hs10
  refine phc_bind (phc_add π iv publicInput stream hs10.good hi1 (Rp.pgrow hs7.good hs710 (hw07 1)))
    fun i2 st11 hs11 hi2 ↦ ?_
  have hs711 := hs710.trans hs11
  refine phc_bind (phc_add π iv publicInput stream hs11.good hi2 (Rp.pgrow hs7.good hs711 (hw07 2)))
    fun init st12 hs12 hinit ↦ ?_
  refine phc_bind (phc_const π iv publicInput stream hs12.good _) fun last st13 hs13 hlast ↦ ?_
  refine phc_bind (phc_const π iv publicInput stream hs13.good sepState) fun c2 st14 hs14 hc2' ↦ ?_
  have hs714 := hs711.trans (hs12.trans (hs13.trans hs14))
  refine phc_bind (phc_mul π iv publicInput stream hs14.good (Rp.pgrow hs7.good hs714 (hw07 0)) hc2')
    fun w0s' st15 hs15 hw0s' ↦ ?_
  have hs715 := hs714.trans hs15
  refine phc_bind (phc_add π iv publicInput stream hs15.good (Rp.pgrow hg (hs07.trans hs715) hbeta) hw0s')
    fun f1 st16 hs16 hf1 ↦ ?_
  have hs716 := hs715.trans hs16
  refine phc_bind (phc_mul π iv publicInput stream hs16.good (Rp.pgrow hs7.good hs716 (hw07 1))
    (Rp.pgrow hs13.good (hs14.trans (hs15.trans hs16)) hlast)) fun w1l st17 hs17 hw1l ↦ ?_
  refine phc_bind (phc_add π iv publicInput stream hs17.good (Rp.pgrow hs16.good hs17 hf1) hw1l)
    fun f2 st18 hs18 hf2 ↦ ?_
  have hs718 := hs716.trans (hs17.trans hs18)
  refine phc_bind (phc_add π iv publicInput stream hs18.good hf2 (Rp.pgrow hs7.good hs718 (hw07 2)))
    fun fin st19 hs19 hfin ↦ ?_
  have hs719 := hs718.trans hs19
  have hs1219 := hs13.trans (hs14.trans (hs15.trans (hs16.trans (hs17.trans (hs18.trans hs19)))))
  have hr3 : RpRel π iv publicInput stream st19 { terms := [termS .heap atOne.toList init], value := fin }
      { terms := [term .heap ((List.range reference.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0)
          (UniSound.Ids.rootInit weightsE betaE)], value := UniSound.Ids.rootFin reference weightsE betaE } :=
    ⟨List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hs7.good hs719 hatOne, Rp.pgrow hs12.good hs1219 hinit⟩
      List.Forall₂.nil, hfin⟩
  have hs619 := hs7.trans hs719
  have hs019 := hs06.trans hs619
  have hc19 := HeapCtx.pgrow π iv publicInput stream hg hs019 hc
  have hpre : RpRels π iv publicInput stream st19 (#[r1, _, _] : Array RelationS).toList
      [Relation.equal .heap (wE.take reference.heap.h) hvE, _, _] :=
    List.Forall₂.cons (RpRel.pgrow π iv publicInput stream hs2.good ((hs3.trans hs36).trans hs619) hr1)
      (List.Forall₂.cons (RpRel.pgrow π iv publicInput stream hs6.good hs619 hr2) (List.Forall₂.cons hr3 List.Forall₂.nil))
  refine phc_bind (phc_forIn_same (fun x ↦ x ∈ reference.heap.blocks.zip (List.range reference.heap.blocks.length))
    (fun s ↦ HeapCtx π iv publicInput stream s active activeE parts partsE weights weightsE w wE ∧
      Rp π iv publicInput stream s o 1 ∧ Rp π iv publicInput stream s mpl mplE ∧
      Rp π iv publicInput stream s mps mpsE ∧ Rp π iv publicInput stream s bpl bplE ∧
      Rp π iv publicInput stream s bps bpsE)
    (fun _ _ hg hs h ↦ ⟨HeapCtx.pgrow π iv publicInput stream hg hs h.1, Rp.pgrow hg hs h.2.1,
      Rp.pgrow hg hs h.2.2.1, Rp.pgrow hg hs h.2.2.2.1, Rp.pgrow hg hs h.2.2.2.2.1, Rp.pgrow hg hs h.2.2.2.2.2⟩) _
    (fun (acc : List Relation × List (Column × ℕ × Bool)) (x : Block × ℕ) ↦
      (acc.1 ++ [UniSound.Ids.Eval.blockRel reference activeE partsE mplE mpsE bplE bpsE wE x],
        acc.2 ++ (leafColsC partsE x.1 x.2).toList))
    (fun (b : Array RelationS × Array (Column × ℕ × Bool)) (acc : List Relation × List (Column × ℕ × Bool)) s ↦
      RpRels π iv publicInput stream s b.1.toList acc.1 ∧ b.2.toList = acc.2) ?_ _ (fun _ h ↦ h) st19 (_, #[])
    (_, []) hs19.good ⟨hc19, Rp.pgrow hs6.good hs619 ho6, Rp.pgrow hg hs019 hmpl, Rp.pgrow hg hs019 hmps,
      Rp.pgrow hg hs019 hbpl, Rp.pgrow hg hs019 hbps⟩ ⟨hpre, rfl⟩) fun res st20 hs20 ⟨hres1, hres2⟩ ↦ ?_
  · rintro ⟨⟨leaves, r, position⟩, index⟩ ⟨R, C⟩ ⟨RE, CE⟩ s hg' hmem ⟨hcs, hos, hmpls, hmpss, hbpls, hbpss⟩ ⟨hR, hC⟩
    dsimp only at hR hC ⊢
    refine phc_bind (phc_snoc_range π iv publicInput stream hg'
      (fun s ↦ RpL π iv publicInput stream s w wE ∧ Rp π iv publicInput stream s 0 0)
      (fun _ _ hg hs h ↦ ⟨RpL.pgrow hg hs h.1, Rp.pgrow hg hs h.2⟩) ⟨hcs.hwE, hcs.h0⟩ reference.heap.h
      (fun l ↦ if l < r then wE.getD l 0 + pointE (position >>> l) else pointE (position >>> l)) _ ?_)
      fun mixed s1 hs1 ⟨hmixed, _⟩ ↦ ?_
    · intro k b s'' hg'' ⟨hw'', h0''⟩ _
      refine phc_bind (phc_const π iv publicInput stream hg'' (pointE (position >>> k))) fun c s2 hs2 hcst ↦ ?_
      by_cases hk : k < r
      · simp only [hk, ↓reduceIte]
        exact phc_bind (phc_add π iv publicInput stream hs2.good
          (RpL.getDz π iv publicInput stream (RpL.pgrow hg'' hs2 hw'') (Rp.pgrow hg'' hs2 h0'') k) hcst)
          fun v s3 hs3 hv ↦ phc_pure _ hs3.good ⟨v, rfl, hv⟩
      · simp only [hk, ↓reduceIte]
        exact phc_bind (phc_pure _ hs2.good hcst) fun v s3 hs3 hv ↦ phc_pure _ hs3.good ⟨v, rfl, hv⟩
    · cases leaves
      · -- The memory's leaves.
        dsimp only
        have h01 := Rp.pgrow hg' hs1 hcs.h0
        have hw1 := RpL.pgrow hg' hs1 hcs.hwE
        have hwr := RpL.getDz π iv publicInput stream hw1 h01 r
        rw [prog_pure_bind]
        dsimp only
        refine phc_bind (quotientTerms_phc π iv publicInput stream hs1.good h01 (Column.leafQuotient index) _ hw1 hwr)
          fun qt qs hqs hqt ↦ phc_pure _ hqs.good ⟨_, rfl, ?_, ?_⟩
        · rw [Array.toList_push]
          refine List.rel_append (RpRels.pgrow π iv publicInput stream hg' (hs1.trans hqs) hR)
            (List.Forall₂.cons ⟨?_, Rp.pgrow hs1.good hqs (Rp.pgrow hg' hs1 hmpss)⟩ List.Forall₂.nil)
          exact List.rel_append (List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hs1.good ((PStep.refl s1 hs1.good).trans hqs) hmixed,
            Rp.pgrow hs1.good hqs (Rp.pgrow hg' hs1 hmpls)⟩ List.Forall₂.nil) hqt
        · rw [Array.toList_append, hC]
          rfl
      · -- The bytecode's leaves.
        dsimp only
        have h01 := Rp.pgrow hg' hs1 hcs.h0
        have hw1 := RpL.pgrow hg' hs1 hcs.hwE
        have hwr := RpL.getDz π iv publicInput stream hw1 h01 r
        rw [prog_pure_bind]
        dsimp only
        refine phc_bind (quotientTerms_phc π iv publicInput stream hs1.good h01 (Column.leafQuotient index) _ hw1 hwr)
          fun qt qs hqs hqt ↦ phc_pure _ hqs.good ⟨_, rfl, ?_, ?_⟩
        · rw [Array.toList_push]
          refine List.rel_append (RpRels.pgrow π iv publicInput stream hg' (hs1.trans hqs) hR)
            (List.Forall₂.cons ⟨?_, Rp.pgrow hs1.good hqs (Rp.pgrow hg' hs1 hbpss)⟩ List.Forall₂.nil)
          exact List.rel_append (List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hs1.good ((PStep.refl s1 hs1.good).trans hqs) hmixed,
            Rp.pgrow hs1.good hqs (Rp.pgrow hg' hs1 hbpls)⟩ List.Forall₂.nil) hqt
        · rw [Array.toList_append, hC]
          rfl
      · -- A table's leaves.
        rename_i t
        dsimp only
        have ht6 : t < partsE.length := by
          have hb := (List.of_mem_zip hmem).1
          have := (UniSound.Ids.heapGood_reference.2.2.2.2.2 _ hb)
          rw [hp6]
          exact this.1
        have hpart := forall₂_getD_partC π iv publicInput stream (hcs.hp.imp fun _ _ h ↦
          RpPart.pgrow π iv publicInput stream hg' hs1 h) ht6 ⟨0, 0, 0, 0, #[]⟩ default
        have h01 := Rp.pgrow hg' hs1 hcs.h0
        have hw1 := RpL.pgrow hg' hs1 hcs.hwE
        have hwr := RpL.getDz π iv publicInput stream hw1 h01 r
        have hz := RpL.getDz π iv publicInput stream (RpL.pgrow hg' hs1 hcs.ha) h01 t
        rw [hpart.2.2.1, hpart.2.2.2.1]
        refine phc_bind (phc_mul π iv publicInput stream hs1.good hz hz) fun sq s2 hs2 hsq ↦ ?_
        refine phc_bind (phc_mul π iv publicInput stream hs2.good (Rp.pgrow hs1.good hs2 hpart.1)
          (Rp.pgrow hs1.good hs2 hwr)) fun pw s3 hs3 hpw ↦ ?_
        refine phc_bind (phc_add π iv publicInput stream hs3.good hpw (Rp.pgrow hs2.good hs3 hsq))
          fun pl s4 hs4 hpl ↦ ?_
        have hs14 := hs2.trans (hs3.trans hs4)
        refine phc_bind (phc_mul π iv publicInput stream hs4.good (Rp.pgrow hs1.good hs14 hpart.2.1)
          (Rp.pgrow hs1.good hs14 hwr)) fun qw s5 hs5 hqw ↦ ?_
        refine phc_bind (phc_add π iv publicInput stream hs5.good hqw
          (Rp.pgrow hs2.good (hs3.trans (hs4.trans hs5)) hsq)) fun ps s6 hs6 hps ↦ ?_
        have hs16 := hs14.trans (hs5.trans hs6)
        refine phc_bind (phc_mul π iv publicInput stream hs6.good (Rp.pgrow hs1.good hs16 hwr)
          (Rp.pgrow hs1.good hs16 hz)) fun sc s7 hs7 hsc ↦ ?_
        have hs17 := hs16.trans hs7
        rw [prog_pure_bind]
        dsimp only
        refine phc_bind (quotientTerms_phc π iv publicInput stream hs7.good (Rp.pgrow hs1.good hs17 h01) (Column.leafQuotient index) _ (RpL.pgrow hs1.good hs17 hw1) hsc)
          fun qt qs hqs hqt ↦ phc_pure _ hqs.good ⟨_, rfl, ?_, ?_⟩
        · rw [Array.toList_push]
          refine List.rel_append (RpRels.pgrow π iv publicInput stream hg' ((hs1.trans hs17).trans hqs) hR)
            (List.Forall₂.cons ⟨?_, Rp.pgrow hs7.good hqs (Rp.pgrow hs6.good hs7 hps)⟩ List.Forall₂.nil)
          exact List.rel_append (List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hs1.good (hs17.trans hqs) hmixed,
            Rp.pgrow hs7.good hqs (Rp.pgrow hs4.good (hs5.trans (hs6.trans hs7)) hpl)⟩ List.Forall₂.nil) hqt
        · rw [Array.toList_append, hC]
          rfl
      · -- An unused block.
        dsimp only
        refine phc_pure _ hs1.good ⟨_, rfl, ?_, ?_⟩
        · rw [Array.toList_push]
          exact List.rel_append (RpRels.pgrow π iv publicInput stream hg' hs1 hR)
            (List.Forall₂.cons ⟨List.Forall₂.cons ⟨rfl, rfl, hmixed, Rp.pgrow hg' hs1 hos⟩ List.Forall₂.nil,
              Rp.pgrow hg' hs1 hos⟩ List.Forall₂.nil)
        · rw [hC]
          simp [leafColsC]
  · have hc20 := HeapCtx.pgrow π iv publicInput stream hs19.good hs20 hc19
    have ho20 := Rp.pgrow hs6.good (hs619.trans hs20) ho6
    refine phc_bind (quotientTerms_phc π iv publicInput stream hs20.good hc20.h0 .constraintQuotient cc hc20.hwE ho20)
      fun qt st21 hs21 hqt ↦ phc_pure _ hs21.good ⟨?_, ?_⟩
    · rw [Array.toList_push]
      rw [heap_foldlC] at hres1
      exact List.rel_append (RpRels.pgrow π iv publicInput stream hs20.good hs21 hres1)
        (List.Forall₂.cons ⟨hqt, Rp.pgrow hg (hs019.trans (hs20.trans hs21)) hcv⟩ List.Forall₂.nil)
    · rw [heap_foldlC] at hres2
      show res.2.toList = _
      rw [hres2]
      simp

end Rel

/-! ## `Compose`'s interface: the heap -/

/-- **The parts' representation** for `Compose` (`RpPart`). -/
def partR : PartRep := fun π iv publicInput stream st p u ↦ RpPart π iv publicInput stream st p u

theorem partR_grows : PartRepGrows partR :=
  fun π iv publicInput stream _ _ _ _ hk hgr h ↦ RpPart.grow π iv publicInput stream hk hgr h

/-- **The heap's output, its shape**: `UniStatement`'s `heapRelations` at π1-rec3's shape, at some inputs (six tables'
parts and active factors, sixteen weights) and the digits `wE`. -/
def heapShape (wE : List E) (b : List Relation × List (Column × ℕ × Bool)) : Prop :=
  ∃ (activeE : List E) (partsE : List TablePart) (weightsE : Array E) (betaE hvE cvE mplE mpsE bplE bpsE : E),
    activeE.length = 6 ∧ partsE.length = 6 ∧ weightsE.size = 16 ∧
      b = UniStatement.heapRelations reference activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE
        (chunks (reference.constraintDegree + 1))

/-- **`HeapSpec`**, `Compose`'s interface for the heap's relations. -/
theorem heapSpec : HeapSpec partR heapShape := by
  intro π iv publicInput stream st active activeE parts partsE weights weightsE beta hv cv mpl mps bpl bps betaE hvE
    cvE mplE mpsE bplE bpsE w wE hg hseed ha ha6 hp hp6 hw hw16 hbeta hhv hcv hmpl hmps hbpl hbps hwE _
  have h0 := rp_zero_of_seed π iv publicInput stream hg hseed
  have h := heapRelations_phc π iv publicInput stream hg ⟨h0, ha, hp, hw, hwE⟩ hp6 hbeta hhv hcv hmpl hmps hbpl hbps
    (chunks (reference.constraintDegree + 1))
  exact ⟨h.1, h.2.1, h.2.2, activeE, partsE, weightsE, betaE, hvE, cvE, mplE, mpsE, bplE, bpsE, ha6, hp6, hw16, rfl⟩

end RecGraph.Sim
