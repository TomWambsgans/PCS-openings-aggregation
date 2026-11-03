-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Witness

/-!
# The honest prover's sizes, from the shape

The prover's stream and its openings' claims have sizes that the shape bounds:

* **the values at `t`** (`atTOf`'s `values`): at most `valuesBound` scalars (`length_atT_values`): each table's
  sent columns and at most two fingerprints per flush (`length_tableValues`), the memory's three, the bytecode's
  two, `T(t)`, `Q_W(t)`;
* **the batching sumcheck's variables** (the largest of the stacks' layouts the verifier states,
  `layouts shape a.c2Columns`): at most the shape's own (`layoutsOf shape`, `batchVars_le`). `C2`'s columns from
  the walk are the shape's (`Shape.c2Columns`) but for a table's leaf quotient, whose degree comes from the
  table's part as the verifier's code computes it on the values sent (`runReader (tablePart …)`): its degrees
  are the table's (`tableDegrees`) when the read succeeds, `0` when it does not (`partDegrees_cases`), so its
  chunks fill at most the shape's words (`colWords_le`); a layout's variables depend on its words only
  (`StackLayout.vars_new`);
* **Flock's pending claim** at `t` is Flock's prover's (`atT_pending`).

The loops (`forIn` in `Id` and in the channel's `ChanM Id`) are read by their projections (`id_forIn_foldl`,
`okP_forIn_foldl`): a body that always yields and moves a projection of its state by a fixed step.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters

namespace Bounds

/-! ## Loops in `Id` -/

section IdLoops

variable {γ β δ : Type}

/-- **A loop read by a projection**: each step yields, moving the projection by `g`. -/
theorem id_forIn_foldl (l : List γ) (b : β) (f : γ → β → Id (ForInStep β)) (p : β → δ) (g : δ → γ → δ)
    (hf : ∀ a s, ∃ s', f a s = .yield s' ∧ p s' = g (p s) a) :
    p (Id.run (forIn l b f)) = l.foldl g (p b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨s', hs, hp⟩ := hf a b
    rw [List.forIn_cons, hs]
    change p (Id.run (forIn l s' f)) = _
    rw [ih s', hp]
    rfl

/-- **A loop bounded by a projection**: each step moves it by at most `c`. -/
theorem id_forIn_le (l : List γ) (b : β) (f : γ → β → Id (ForInStep β)) (p : β → ℕ) (c : ℕ)
    (hf : ∀ a s, p (f a s).value ≤ p s + c) : p (Id.run (forIn l b f)) ≤ p b + l.length * c := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    have h1 := hf a b
    rw [List.forIn_cons]
    rcases h : f a b with b' | b'
    · rw [h] at h1
      change p b' ≤ _
      simp only [ForInStep.value] at h1
      rw [List.length_cons, Nat.succ_mul]
      omega
    · rw [h] at h1
      change p (Id.run (forIn l b' f)) ≤ _
      simp only [ForInStep.value] at h1
      have := ih b'
      rw [List.length_cons, Nat.succ_mul]
      omega

/-- **A loop keeps an invariant** of its state. -/
theorem id_forIn_inv (l : List γ) (b : β) (f : γ → β → Id (ForInStep β)) (I : β → Prop) (h0 : I b)
    (hf : ∀ a s, I s → I (f a s).value) : I (Id.run (forIn l b f)) := by
  induction l generalizing b with
  | nil => exact h0
  | cons a l ih =>
    have h1 := hf a b h0
    rw [List.forIn_cons]
    rcases h : f a b with b' | b'
    · rw [h] at h1
      exact h1
    · rw [h] at h1
      exact ih b' h1

/-- **A loop keeps an invariant of the prefix done**: each step yields. -/
theorem id_forIn_prefix (l : List γ) (b : β) (f : γ → β → Id (ForInStep β)) (I : List γ → β → Prop)
    (hf : ∀ pre a s, I pre s → ∃ s', f a s = .yield s' ∧ I (pre ++ [a]) s') :
    ∀ pre, I pre b → I (pre ++ l) (Id.run (forIn l b f)) := by
  induction l generalizing b with
  | nil => intro pre h; simpa using h
  | cons a l ih =>
    intro pre h
    obtain ⟨s', hs, hI⟩ := hf pre a b h
    rw [List.forIn_cons, hs]
    change I (pre ++ a :: l) (Id.run (forIn l s' f))
    have := ih s' (pre ++ [a]) hI
    simpa using this

variable {α : Type}

/-- **A loop, then the rest**, read by a projection of the loop's state. -/
theorem id_bind_foldl {l : List γ} {b : β} {f : γ → β → Id (ForInStep β)} {k : β → Id α} {P : α → Prop}
    (p : β → δ) (g : δ → γ → δ) (hf : ∀ a s, ∃ s', f a s = .yield s' ∧ p s' = g (p s) a)
    (hk : ∀ s, p s = l.foldl g (p b) → P (Id.run (k s))) : P (Id.run (forIn l b f >>= k)) :=
  hk _ (id_forIn_foldl l b f p g hf)

/-- **A loop, then the rest**, with an invariant of the prefix done. -/
theorem id_bind_prefix {l : List γ} {b : β} {f : γ → β → Id (ForInStep β)} {k : β → Id α} {P : α → Prop}
    (I : List γ → β → Prop) (h0 : I [] b) (hf : ∀ pre a s, I pre s → ∃ s', f a s = .yield s' ∧ I (pre ++ [a]) s')
    (hk : ∀ s, I l s → P (Id.run (k s))) : P (Id.run (forIn l b f >>= k)) := by
  have := id_forIn_prefix l b f I hf [] h0
  rw [List.nil_append] at this
  exact hk _ this

end IdLoops

/-! ## Channel programs on `Id` -/

section Chan

variable {α β δ : Type}

/-- **Every successful result satisfies `P`**, from any channel. -/
def OkP (x : ChanM Id α) (P : α → Prop) : Prop :=
  ∀ c a c', Id.run (x.run.run c) = (.ok a, c') → P a

theorem okP_pure {a : α} {P : α → Prop} (h : P a) : OkP (pure a : ChanM Id α) P := by
  intro c a' c' hc
  cases hc
  exact h

theorem okP_true (x : ChanM Id α) : OkP x fun _ ↦ True := fun _ _ _ _ ↦ trivial

theorem run_bind_id (x : ChanM Id α) (f : α → ChanM Id β) (c : Chan) :
    Id.run ((x >>= f).run.run c) = match Id.run (x.run.run c) with
      | (.ok a, c1) => Id.run ((f a).run.run c1)
      | (.error e, c1) => (.error e, c1) := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases h : Id.run (x.run.run c) with ⟨_ | a, c1⟩
  · simp only [Id.run] at h ⊢
    rw [h]
    rfl
  · simp only [Id.run] at h ⊢
    rw [h]
    rfl

theorem OkP.bind {x : ChanM Id α} {f : α → ChanM Id β} {P : α → Prop} {Q : β → Prop} (hx : OkP x P)
    (hf : ∀ a, P a → OkP (f a) Q) : OkP (x >>= f) Q := by
  intro c b c' h
  rw [run_bind_id] at h
  rcases hxc : Id.run (x.run.run c) with ⟨_ | a, c1⟩
  · rw [hxc] at h
    simp at h
  · rw [hxc] at h
    exact hf a (hx c a c1 hxc) c1 b c' h

/-- **A loop read by a projection**: each step yields, moving the projection by `g`. -/
theorem okP_forIn_foldl {γ : Type} (l : List γ) (b : β) (f : γ → β → ChanM Id (ForInStep β)) (p : β → δ)
    (g : δ → γ → δ) (hf : ∀ a s, OkP (f a s) fun r ↦ ∃ s', r = .yield s' ∧ p s' = g (p s) a) :
    OkP (forIn l b f) fun r ↦ p r = l.foldl g (p b) := by
  induction l generalizing b with
  | nil => exact okP_pure rfl
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a b).bind fun r ⟨s', hr, hp⟩ ↦ ?_
    subst hr
    have := ih s'
    rw [List.foldl_cons, ← hp]
    exact this

/-- One step of a channel body's walk. -/
macro "okp_step" : tactic => `(tactic| first
  | (with_reducible refine okP_pure ?_); exact ⟨_, rfl, rfl⟩
  | with_reducible refine (okP_true _).bind fun _ _ ↦ ?_
  | dsimp only
  | split)

/-- **A table's part has the table's degrees** (`tableDegrees`), whatever it reads. -/
theorem okP_tablePart (t : Table) (r : ℕ) (weights : Array E) (beta : E) (w : List E) :
    OkP (tablePart (m := Id) t r weights beta w) fun z ↦ (z.1.pullDegree, z.1.pushDegree) = tableDegrees t := by
  unfold tablePart
  refine (okP_true _).bind fun s1 _ ↦ ?_
  refine (okP_forIn_foldl _ _ _ (fun s ↦ (s.2.2.2.1, s.2.2.2.2))
    (fun (acc : ℕ × ℕ) (x : List Form × List Form) ↦ match x with
      | (pulled, pushed) => (acc.1 + tupleDegree pulled, acc.2 + tupleDegree pushed)) ?_).bind
    fun s2 hs2 ↦ okP_pure hs2
  intro x s
  obtain ⟨pulled, pushed⟩ := x
  repeat okp_step

end Chan

/-! ## The table parts -/

/-- A part's degrees. -/
def partDegrees (p : TablePart) : ℕ × ℕ := (p.pullDegree, p.pushDegree)

/-- **A part's degrees are its table's**, or zero (a failed read: the default part). -/
def DegOK (part : TablePart) (t : Table) : Prop := partDegrees part = tableDegrees t ∨ partDegrees part = (0, 0)

theorem degOK_runReader (t : Table) (r : ℕ) (weights : Array E) (beta : E) (w : List E) (bytes : List UInt8) :
    DegOK (runReader (tablePart (m := Id) t r weights beta w) bytes).1 t := by
  unfold runReader
  rcases h : (ExceptT.run (tablePart (m := Id) t r weights beta w)).run (Chan.start default bytes.toArray) with
    ⟨_ | z, c'⟩
  · exact Or.inr rfl
  · exact Or.inl (okP_tablePart t r weights beta w _ z c' h)

section Forall₂

variable {α β : Type} {R : α → β → Prop}

theorem forall₂_snoc {l₁ : List α} {l₂ : List β} {a : α} {b : β} (h : List.Forall₂ R l₁ l₂) (hab : R a b) :
    List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem forall₂_getD {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (da : α) (db : β) (hd : R da db) :
    ∀ i, R (l₁.getD i da) (l₂.getD i db) := by
  induction h with
  | nil => intro i; simpa using hd
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

end Forall₂

/-- **The parts `atTOf` reads** (its loop over the tables): one per table, each `DegOK`. -/
def PartsOK (parts : List TablePart) : Prop := List.Forall₂ DegOK parts tables

theorem PartsOK.getD {parts : List TablePart} (h : PartsOK parts) (t : ℕ) :
    DegOK (parts.getD t default) (tables.getD t default) :=
  forall₂_getD h default default (Or.inr rfl) t

theorem PartsOK.length {parts : List TablePart} (h : PartsOK parts) : parts.length = tables.length :=
  List.Forall₂.length_eq h

/-! ## The constraint quotient's degree -/

/-- `Shape.constraintDegree`'s step. -/
def cdStep (shape : Shape) (d : ℕ) (table : Table) : ℕ :=
  let r := shape.heights.getD table.opcode 0
  let n := 2 ^ r
  let d := if table.opcode = opJump then max d (degree n 2) else d
  let d := max d (degree ((n - 1) * (1 + table.countColumns.length)) n)
  if table.opcode = opBlake2s then max d (degree (r * (n / 2)) n) else d

theorem foldl_zip_fst {α β δ : Type} (g : δ → α → δ) :
    ∀ (l : List α) (l' : List β) (d : δ), l.length ≤ l'.length →
      (l.zip l').foldl (fun d x ↦ g d x.1) d = l.foldl g d
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | a :: l, _ :: l', d, h => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    exact foldl_zip_fst g l l' _ (by simpa using h)

/-- **The constraint quotient's degree is the shape's**, whatever the parts' values (one part per table). -/
theorem constraintRelation_snd (shape : Shape) (parts : List TablePart) (h : tables.length ≤ parts.length)
    (publicWords : List E) (gamma t constraintValue : E) (w : List E) :
    (constraintRelation shape parts publicWords gamma t constraintValue w).2 = shape.constraintDegree := by
  unfold constraintRelation
  refine id_bind_foldl (P := fun r : Relation × ℕ ↦ r.2 = shape.constraintDegree)
    (fun s : E × Array Term × E × ℕ ↦ s.2.2.2) (fun d (x : Table × TablePart) ↦ cdStep shape d x.1) ?_
    fun s hs ↦ ?_
  · intro x s
    obtain ⟨table, part⟩ := x
    dsimp only
    split_ifs with hj hb hb
    · exact absurd (hj.symm.trans hb) (by decide)
    · exact ⟨_, rfl, by simp [cdStep, hj, opJump, opBlake2s]⟩
    · exact ⟨_, rfl, by simp [cdStep, hb, opJump, opBlake2s]⟩
    · exact ⟨_, rfl, by simp [cdStep, hj, hb]⟩
  · show max s.2.2.2 (degree (2 ^ shape.logMemory) 3) = shape.constraintDegree
    rw [hs]
    dsimp only
    rw [foldl_zip_fst (cdStep shape) tables parts 0 h]
    rfl

/-! ## The heap's leaf quotients' columns -/

/-- A leaf quotient's chunks' columns, at degree `d`. -/
def chunkCols (index d : ℕ) : Array (Column × ℕ × Bool) :=
  Array.map (fun (x : ℕ × ℕ) ↦ match x with | (e, chunk) => (Column.leafQuotient index chunk, e, true))
    ((chunks (d + 1)).zip (List.range (chunks (d + 1)).length)).toArray

/-- **A heap block's leaf quotient's columns**, a table's degree from its part. -/
def leafCols (parts : List TablePart) (block : Block) (index : ℕ) : Array (Column × ℕ × Bool) :=
  match block.leaves with
  | .unused => #[]
  | .memory => chunkCols index (degree (2 * (2 ^ block.r - 1)) (2 ^ block.r))
  | .bytecode => chunkCols index (degree (2 * (2 ^ block.r - 1)) (2 ^ block.r))
  | .table t => chunkCols index (degree (max (parts.getD t default).pullDegree (parts.getD t default).pushDegree *
      (2 ^ block.r - 1) + (2 ^ block.r - Shape.leastRows block.r)) (2 ^ block.r))

theorem foldl_append_toList {α β : Type} (G : α → Array β) :
    ∀ (l : List α) (init : Array β),
      (l.foldl (fun cols x ↦ cols ++ G x) init).toList = init.toList ++ l.flatMap fun x ↦ (G x).toList
  | [], init => by simp
  | a :: l, init => by
    rw [List.foldl_cons, foldl_append_toList G l, Array.toList_append, List.flatMap_cons, List.append_assoc]

/-- **The heap's leaf columns are the blocks'**, whatever the other arguments. -/
theorem heapRelations_snd (shape : Shape) (active : List E) (parts : List TablePart) (weights : Array E)
    (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : E) (w : List E)
    (constraintChunks : List ℕ) :
    (heapRelations shape active parts weights beta heapValue constraintValue memoryPull memoryPush bytecodePull
      bytecodePush w constraintChunks).2 =
      (shape.heap.blocks.zip (List.range shape.heap.blocks.length)).flatMap fun x ↦ (leafCols parts x.1 x.2).toList := by
  unfold heapRelations
  refine id_bind_foldl (P := fun r : List Relation × List (Column × ℕ × Bool) ↦ r.2 = _)
    (fun s : Array Relation × Array (Column × ℕ × Bool) ↦ s.2)
    (fun cols (x : Block × ℕ) ↦ cols ++ leafCols parts x.1 x.2) ?_ fun s hs ↦ ?_
  · intro x s
    obtain ⟨⟨leaves, r, position⟩, index⟩ := x
    cases leaves
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, Array.append_empty.symm⟩
  · show s.2.toList = _
    rw [hs, foldl_append_toList]
    rfl

/-! ## A layout's variables, from its words -/

/-- **The words a column list fills**: three blocks per `E`-valued column, one per `K`-valued. -/
def colWords (cols : List (Column × ℕ × Bool)) : ℕ := (cols.map fun x ↦ (if x.2.2 then 3 else 1) * 2 ^ x.2.1).sum

theorem colWords_append (a b : List (Column × ℕ × Bool)) : colWords (a ++ b) = colWords a + colWords b := by
  simp [colWords]

theorem colWords_flatMap {X : Type} (F : X → List (Column × ℕ × Bool)) :
    ∀ l : List X, colWords (l.flatMap F) = (l.map fun x ↦ colWords (F x)).sum
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, colWords_append, colWords_flatMap F l, List.map_cons, List.sum_cons]

theorem foldl_snd_sum {X Y : Type} (F : Y × ℕ → X → Y × ℕ) (c : X → ℕ) (hF : ∀ acc x, (F acc x).2 = acc.2 + c x) :
    ∀ (l : List X) (init : Y × ℕ), (l.foldl F init).2 = init.2 + (l.map c).sum
  | [], init => by simp
  | a :: l, init => by
    rw [List.foldl_cons, foldl_snd_sum F c hF l, hF, List.map_cons, List.sum_cons]
    omega

theorem pieces_sum : ∀ cols : List (Column × ℕ × Bool),
    ((cols.flatMap fun x ↦ (List.range (if x.2.2 then 3 else 1)).map fun limb ↦ (x.1, limb, x.2.1)).map
      fun y ↦ 2 ^ y.2.2).sum = colWords cols
  | [] => rfl
  | ⟨column, vars, eValued⟩ :: cols => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, pieces_sum cols]
    cases eValued
    · simp [colWords]
    · simp [colWords, Function.comp_def, List.map_const']
      ring

/-- **A layout's variables depend on its words only.** -/
theorem vars_new (cols : List (Column × ℕ × Bool)) :
    (StackLayout.new cols).vars = max (log2Ceil (max (colWords cols) 2)) 15 := by
  unfold StackLayout.new
  dsimp only
  rw [foldl_snd_sum (c := fun x ↦ 2 ^ x.2.2)]
  · rw [List.Perm.sum_eq (List.Perm.map _ (List.mergeSort_perm _ _)), pieces_sum cols]
    simp only [Nat.zero_add]
  · intro acc x
    rfl

theorem log2Ceil_mono {a b : ℕ} (h : a ≤ b) : log2Ceil a ≤ log2Ceil b := by
  unfold log2Ceil
  split_ifs with ha hb hb
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · have : (a - 1).log2 ≤ (b - 1).log2 := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right (by omega)
    omega

theorem vars_new_mono {cols cols' : List (Column × ℕ × Bool)} (h : colWords cols ≤ colWords cols') :
    (StackLayout.new cols).vars ≤ (StackLayout.new cols').vars := by
  rw [vars_new, vars_new]
  have := log2Ceil_mono (show max (colWords cols) 2 ≤ max (colWords cols') 2 by omega)
  omega

/-! ## The chunks -/

theorem chunks_one : chunks 1 = [0] := by decide +kernel

theorem forIn_range4 {β : Type} (b : β) (f : ℕ → β → Id (ForInStep β)) :
    forIn [:4] b f = forIn [0, 1, 2, 3] b f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- **A loop, then the rest**, with an invariant of the loop's state. -/
theorem id_bind_inv {α β γ : Type} {l : List γ} {b : β} {f : γ → β → Id (ForInStep β)} {k : β → Id α}
    {P : α → Prop} (I : β → Prop) (h0 : I b) (hf : ∀ a s, I s → I (f a s).value)
    (hk : ∀ s, I s → P (Id.run (k s))) : P (Id.run (forIn l b f >>= k)) :=
  hk _ (id_forIn_inv l b f I h0 hf)

/-- **A positive count has a chunk.** -/
theorem chunks_ne_nil {c : ℕ} (hc : 0 < c) : chunks c ≠ [] := by
  unfold chunks
  dsimp only
  rw [forIn_range4, List.forIn_cons]
  simp only [gt_iff_lt, hc, ↓reduceIte, Array.size_empty, (by decide : ¬ (0 : ℕ) = 2), false_and, pure_bind]
  refine id_bind_inv (P := fun l : List ℕ ↦ l ≠ []) (fun s : Array ℕ × ℕ ↦ 1 ≤ s.1.size) (by simp) ?_ fun s hs ↦ ?_
  · intro x st h
    split_ifs
    · show 1 ≤ (st.1.push _).size
      simp
    · show 1 ≤ (st.1.push _).size
      simp
    · exact h
  · show s.1.toList ≠ []
    intro h
    have := congrArg List.length h
    simp only [Array.length_toList, List.length_nil] at this
    omega

theorem colWords_zip_map (index : ℕ) :
    ∀ (l l' : List ℕ), l.length ≤ l'.length →
      colWords ((l.zip l').map fun (x : ℕ × ℕ) ↦ (Column.leafQuotient index x.2, x.1, true)) =
        3 * (l.map (2 ^ ·)).sum
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | e :: l, c :: l', h => by
    rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.sum_cons, ← List.singleton_append, colWords_append,
      colWords_zip_map index l l' (by simpa using h)]
    simp [colWords]
    ring

/-- A chunk list's columns fill three words per chunk word. -/
theorem colWords_chunkCols (index d : ℕ) :
    colWords (chunkCols index d).toList = 3 * ((chunks (d + 1)).map (2 ^ ·)).sum := by
  unfold chunkCols
  rw [Array.toList_map, List.toList_toArray]
  exact colWords_zip_map index _ _ (by simp)

/-! ## The walk's `C2` columns against the shape's -/

/-- **`C2`'s columns at given parts**: the heap's, the tree quotient's, the constraint quotient's chunks at the
shape's degree, each heap block's leaf quotient's (a table's at its part's degrees). -/
def c2ColumnsWith (shape : Shape) (parts : List TablePart) : List (Column × ℕ × Bool) :=
  let h := shape.heap.h
  let constraintChunks := chunks (shape.constraintDegree + 1)
  [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
    (constraintChunks.zip (List.range constraintChunks.length)).map (fun (x : ℕ × ℕ) ↦ match x with
      | (e, c) => (Column.constraintQuotient c, e, true)) ++
    (shape.heap.blocks.zip (List.range shape.heap.blocks.length)).flatMap fun x ↦ (leafCols parts x.1 x.2).toList

theorem one_le_sum_pow_aux {l : List ℕ} (hl : l ≠ []) : 1 ≤ (l.map (2 ^ ·)).sum := by
  obtain ⟨a, l, rfl⟩ : ∃ a l', l = a :: l' := by
    cases l with
    | nil => exact absurd rfl hl
    | cons a l' => exact ⟨a, l', rfl⟩
  simp only [List.map_cons, List.sum_cons]
  have := Nat.one_le_two_pow (n := a)
  omega

theorem one_le_sum_pow {l : List ℕ} (hl : l ≠ []) : 1 ≤ (l.map (2 ^ ·)).sum := one_le_sum_pow_aux hl

/-- A positive degree's chunks fill at least three words. -/
theorem three_le_colWords_chunks (index d : ℕ) :
    3 ≤ colWords (((chunks (d + 1)).zip (List.range (chunks (d + 1)).length)).map
      fun (x : ℕ × ℕ) ↦ (Column.leafQuotient index x.2, x.1, true)) := by
  rw [colWords_zip_map _ _ _ (by simp)]
  have := one_le_sum_pow (chunks_ne_nil (c := d + 1) (by omega))
  omega

/-- **The walk's `C2` columns fill at most the shape's words**: a table's leaf quotient at its table's degrees
is the shape's, at zero degrees (a failed read) one chunk of one word. -/
theorem colWords_c2ColumnsWith_le (shape : Shape) {parts : List TablePart} (hp : PartsOK parts) :
    colWords (c2ColumnsWith shape parts) ≤ colWords shape.c2Columns := by
  unfold c2ColumnsWith Shape.c2Columns
  dsimp only
  simp only [colWords_append, colWords_flatMap]
  refine Nat.add_le_add_left (List.sum_le_sum fun x _ ↦ ?_) _
  obtain ⟨⟨leaves, r, position⟩, index⟩ := x
  cases leaves with
  | memory =>
    simp only [leafCols, Shape.leafDegree]
    rw [colWords_chunkCols, colWords_zip_map _ _ _ (by simp)]
  | bytecode =>
    simp only [leafCols, Shape.leafDegree]
    rw [colWords_chunkCols, colWords_zip_map _ _ _ (by simp)]
  | unused => simp [leafCols, Shape.leafDegree, colWords]
  | table t =>
    simp only [leafCols, Shape.leafDegree]
    rcases hp.getD t with h | h
    · rw [← h]
      simp only [partDegrees]
      rw [colWords_chunkCols, colWords_zip_map _ _ _ (by simp)]
    · simp only [partDegrees, Prod.mk.injEq] at h
      rw [h.1, h.2, colWords_chunkCols, colWords_zip_map _ _ _ (by simp)]
      have h0 : degree (max 0 0 * (2 ^ r - 1) + (2 ^ r - Shape.leastRows r)) (2 ^ r) = 0 := by
        unfold degree
        simp only [max_self, Nat.zero_mul, Nat.zero_add]
        omega
      rw [h0, Nat.zero_add, chunks_one]
      exact Nat.mul_le_mul_left 3 (le_trans (by simp) (one_le_sum_pow (chunks_ne_nil (Nat.succ_pos _))))

/-- **The batching sumcheck's variables bound**: the largest of the shape's stacks' variables. -/
def batchVarsBound (shape : Shape) : ℕ := ((layoutsOf shape).map (·.2.vars)).foldl max 0

theorem batchVars_le (shape : Shape) (cols : List (Column × ℕ × Bool)) (h : colWords cols ≤ colWords shape.c2Columns) :
    ((layouts shape cols).map (·.2.vars)).foldl max 0 ≤ batchVarsBound shape := by
  have := vars_new_mono h
  simp only [batchVarsBound, layoutsOf, layouts, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  omega

/-! ## The values at `t` -/

@[simp] theorem id_pure_value {β : Type} (x : ForInStep β) : (pure x : Id (ForInStep β)).value = x.value := rfl

theorem foldl_succ {γ : Type} : ∀ (l : List γ) (n : ℕ), l.foldl (fun n (_ : γ) ↦ n + 1) n = n + l.length
  | [], n => rfl
  | _ :: l, n => by rw [List.foldl_cons, foldl_succ l, List.length_cons]; omega

/-- **A loop, then the rest**, bounded by a projection of the loop's state. -/
theorem id_bind_le {α β γ : Type} {l : List γ} {b : β} {f : γ → β → Id (ForInStep β)} {k : β → Id α}
    {P : α → Prop} (p : β → ℕ) (c : ℕ) (hf : ∀ a s, p (f a s).value ≤ p s + c)
    (hk : ∀ s, p s ≤ p b + l.length * c → P (Id.run (k s))) : P (Id.run (forIn l b f >>= k)) :=
  hk _ (id_forIn_le l b f p c hf)

/-- A table's values at `t`: its sent columns, at most two fingerprints per flush. -/
def tvBound (t : Table) : ℕ := (sentColumns t).length + 2 * (t.flushes.pull.zip t.flushes.push).length

theorem length_tableValues (table : Table) (at_ : ℕ → E) (weights : Array E) (beta : E) :
    (tableValues table at_ weights beta).length ≤ tvBound table := by
  unfold tableValues
  refine id_bind_foldl (P := fun out : List E ↦ out.length ≤ tvBound table)
    (fun s : Array (Option E) × Array E ↦ s.2.size) (fun n _ ↦ n + 1) (fun col s ↦ ⟨_, rfl, by simp⟩)
    fun s hs ↦ ?_
  refine id_bind_le (P := fun out : List E ↦ out.length ≤ tvBound table) (fun out : Array E ↦ out.size) 2 ?_
    fun out hout ↦ ?_
  · intro x st
    obtain ⟨pulled, pushed⟩ := x
    dsimp only
    split_ifs <;> simp
  · show out.toList.length ≤ _
    rw [foldl_succ] at hs
    simp only [Array.length_toList, Array.size_empty] at hs ⊢
    unfold tvBound
    omega

/-- **The values at `t`**: every table's, then seven. -/
def valuesBound : ℕ := (tables.map tvBound).sum + 7

/-- **What `atTOf` leaves**, from the shape: its `C2` columns at parts read off the tables, its values, Flock's
pending claim. -/
structure AtTFacts (tr : Trace) (flockOut : Option FlockOut) (a : AtT) : Prop where
  c2 : ∃ parts, PartsOK parts ∧ a.c2Columns = c2ColumnsWith tr.shape parts
  values : a.values.length ≤ valuesBound
  pending : a.pending = flockOut.map fun out ↦ (out.pending, out.point)

theorem atT_facts (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (flockOut : Option FlockOut) :
    AtTFacts tr flockOut (atTOf tr c2 alphas beta gamma t flockOut) := by
  rcases flockOut with _ | ⟨point, end_, pending, tabs⟩
  rotate_left
  cases end_
  all_goals
    unfold atTOf
    refine id_bind_prefix (P := AtTFacts tr _)
      (fun (pre : List Table) (s : Array E × Array Relation × Array TablePart) ↦
        List.Forall₂ DegOK s.2.2.toList pre ∧ s.1.size ≤ (pre.map tvBound).sum) ⟨List.Forall₂.nil, by simp⟩ ?_
      fun s hs ↦ ?_
    · intro pre table s hI
      refine ⟨_, rfl, ?_, ?_⟩
      · rw [Array.toList_push]
        exact forall₂_snoc hI.1 (degOK_runReader _ _ _ _ _ _)
      · simp only [Array.size_append, List.size_toArray, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil]
        have := length_tableValues table (fun c ↦ evalB ((bCoefficients (tr.shape.heights.getD table.opcode 0)
          (tr.column table.opcode c)).map ofK) (tr.shape.heights.getD table.opcode 0)
          (digits t (max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2))) (eqKernel alphas) beta
        have := hI.2
        omega
    · dsimp only
      refine ⟨⟨s.2.2.toList, hs.1, ?_⟩, ?_, rfl⟩
      · rw [constraintRelation_snd _ _ (le_of_eq (List.Forall₂.length_eq hs.1).symm), heapRelations_snd]
        rfl
      · simp only [Id.run_pure, Array.length_toList, Array.size_append, List.size_toArray, List.length_cons,
          List.length_nil]
        unfold valuesBound
        have := hs.2
        omega

/-- **The batching sumcheck's variables at `t`** are at most the shape's stacks' (`batchVarsBound`). -/
theorem batchVars_atT (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (flockOut : Option FlockOut) :
    ((layouts tr.shape (atTOf tr c2 alphas beta gamma t flockOut).c2Columns).map (·.2.vars)).foldl max 0 ≤
      batchVarsBound tr.shape := by
  obtain ⟨parts, hp, h⟩ := (atT_facts tr c2 alphas beta gamma t flockOut).c2
  rw [h]
  exact batchVars_le _ _ (colWords_c2ColumnsWith_le _ hp)

end Bounds

end UniComplete

/-- info: 'UniComplete.Bounds.batchVars_atT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Bounds.batchVars_atT

/-- info: 'UniComplete.Bounds.atT_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Bounds.atT_facts
