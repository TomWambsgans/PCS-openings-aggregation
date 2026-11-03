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

end Rel

end RecGraph.Sim
