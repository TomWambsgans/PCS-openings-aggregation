-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's run is `formal/UniStatement`'s
-- (`UniStatement/Rec.lean`: `reduceWithFs`, `batchFs`, `runFs`; `Claims.lean`: `combine`; `Verifier.lean`:
-- `heapRelations`; `Flock.lean`: `ringEnd`).
import RecCompose.RunShape
import RecCompose.OpeningsAgree

/-!
# π1-rec3's run leaves three point openings: `Pi1RunOpenings`

**`pi1RunOpenings`**: a run of π1-rec3's verifier that returns a result has three point openings, `C1`'s, `C2`'s and
the setup's, in `commitments` order, with no bit slice. Through `reduceWithFs` with the walk (`HoldsE`):

* the walked Flock ends with the ring switch (`ringEnd`: `.ring map target`), so no bit-slice relation is made
  (`holdsE_verifyWalkedFs`), and the bit slice `combine [] .c1 1` is none;
* each commitment has a relation (`C1`: the memory's final count; `C2`: the heap's value, `heapRelations`' first,
  `heapRelations_c2`; the setup: the address), so `combine` claims on each (`combine_isSome`) and the batch is given
  the three in order (`filterMap_combine_fst`);
* the batch makes one point claim per given claim, in order, the bit slice on `C1`'s (`holdsE_batchFs_openings`; its
  values are as many as the claims, `holdsE_nextScalars_length`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-- Three point openings, `C1`'s, `C2`'s and the setup's, no bit slice. -/
def OpeningsShape (l : List (Commitment × Opening)) : Prop :=
  ∃ pt1 v1 pt2 v2 pt3 v3, l = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none), (.setup, .point pt3 v3 none)]

/-! ## The combined claims -/

theorem combine_isSome (rels : List Relation) (c : Commitment) (rho : E)
    (h : ∃ rel ∈ rels, rel.commitment = c) : (combine rels c rho).isSome := by
  obtain ⟨rel, hrel, hc⟩ := h
  unfold combine
  have hne : (rels.filter (·.commitment == c)).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff_exists_mem]
    exact ⟨rel, List.mem_filter.mpr ⟨hrel, by simp [hc]⟩⟩
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem filterMap_combine_fst (rels : List Relation) (rho : E)
    (h : ∀ c ∈ commitments, ∃ rel ∈ rels, rel.commitment = c) :
    ((commitments.filterMap fun c ↦ (combine rels c rho).map fun x ↦ (c, x)).map (·.1)) =
      [.c1, .c2, .setup] := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c1 rho (h .c1 (by simp [commitments])))
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c2 rho (h .c2 (by simp [commitments])))
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .setup rho (h .setup (by simp [commitments])))
  simp [commitments, List.filterMap, ha, hb, hd]

/-- **`heapRelations` makes a relation on `C2`**: its first, the heap's value. -/
theorem heapRelations_c2 (shape : UniStatement.Shape) (active : List E) (parts : List TablePart) (weights : Array E)
    (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : E) (w : List E)
    (constraintChunks : List ℕ) :
    ∃ rel ∈ (heapRelations shape active parts weights beta heapValue constraintValue memoryPull memoryPush
      bytecodePull bytecodePush w constraintChunks).1, rel.commitment = .c2 := by
  refine ⟨Relation.equal .heap (w.take shape.heap.h) heapValue, ?_, rfl⟩
  have inv : ∀ (l : List (Block × ℕ)) (f : Block × ℕ → Array Relation × Array (Column × ℕ × Bool) →
      Id (ForInStep (Array Relation × Array (Column × ℕ × Bool)))),
      (∀ x b, ∃ r' c', f x b = .yield (r', c') ∧ ∀ y ∈ b.1, y ∈ r') →
      ∀ b : Array Relation × Array (Column × ℕ × Bool), ∀ y ∈ b.1, y ∈ (Id.run (forIn l b f)).1 := by
    intro l f hf
    induction l with
    | nil => intro b y hy; simpa using hy
    | cons x l ih =>
      intro b y hy
      obtain ⟨r', c', hfx, hsub⟩ := hf x b
      simp only [List.forIn_cons, Id.run, hfx]
      exact ih (r', c') y (hsub y hy)
  unfold heapRelations
  dsimp only
  rw [Id.run_bind]
  simp only [Id.run_pure, Array.toList_push, List.mem_append]
  left
  rw [Array.mem_toList_iff]
  refine inv _ _ ?_ _ _ ?_
  · intro x b
    split <;> exact ⟨_, _, rfl, fun y hy ↦ Array.mem_push_of_mem _ hy⟩
  · simp

/-! ## Membership in the relations -/

theorem exists_push_of {P : Relation → Prop} {X : Array Relation} (q : Relation) (h : ∃ rel ∈ X.toList, P rel) :
    ∃ rel ∈ (X.push q).toList, P rel := by
  obtain ⟨rel, hr, hp⟩ := h
  exact ⟨rel, by simp [hr], hp⟩

theorem exists_push_self {P : Relation → Prop} (X : Array Relation) {q : Relation} (h : P q) :
    ∃ rel ∈ (X.push q).toList, P rel := ⟨q, by simp, h⟩

theorem exists_append_left {P : Relation → Prop} {X : Array Relation} (Y : Array Relation)
    (h : ∃ rel ∈ X.toList, P rel) : ∃ rel ∈ (X ++ Y).toList, P rel := by
  obtain ⟨rel, hr, hp⟩ := h
  exact ⟨rel, by simp [hr], hp⟩

theorem exists_append_list {P : Relation → Prop} (X : Array Relation) {L : List Relation}
    (h : ∃ rel ∈ L, P rel) : ∃ rel ∈ (X ++ L.toArray).toList, P rel := by
  obtain ⟨rel, hr, hp⟩ := h
  exact ⟨rel, by simp [hr], hp⟩

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem holdsE_ite {α : Type} {c : Prop} [Decidable c] {X Y : ChanM m α} {P : α → Prop} (hX : HoldsE X P)
    (hY : HoldsE Y P) : HoldsE (if c then X else Y) P := by
  split
  · exact hX
  · exact hY

theorem holdsE_mono {α : Type} {X : ChanM m α} {P P' : α → Prop} (hX : HoldsE X P) (h : ∀ a, P a → P' a) :
    HoldsE X P' := fun c ↦ holds_mono (hX c) fun _ hp a ha ↦ h a (hp a ha)

/-- **The walked Flock ends with the ring switch.** -/
theorem holdsE_verifyWalkedFs (F : KeccakState → m KeccakState) (logN : ℕ) (variant : Flock.Variant)
    (fs : FsShape) :
    HoldsE (Flock.verifyWalkedFs F logN variant fs) fun x ↦ ∃ p mp tg, x = (p, Flock.End.ring mp tg) := by
  have hr : ∀ s, HoldsE (Flock.ringEnd F variant s) fun e ↦ ∃ mp tg, e = Flock.End.ring mp tg := by
    intro s
    unfold Flock.ringEnd
    exact holdsE_bind (holdsE_true (m := m) _) fun mp _ ↦ holdsE_pure ⟨mp, _, rfl⟩
  unfold Flock.verifyWalkedFs
  exact holdsE_bind (holdsE_true (m := m) _) fun fr _ ↦ holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦
    holdsE_bind (hr _) fun e ⟨mp, tg, he⟩ ↦ holdsE_pure ⟨fr.point, mp, tg, by rw [he]⟩

/-- A loop pushing one element a step adds one element a step. -/
theorem holdsE_forIn_push {γ : Type} (f : γ → Array E → ChanM m (ForInStep (Array E)))
    (hf : ∀ x b, HoldsE (f x b) fun st ↦ ∃ y, st = .yield (b.push y)) :
    ∀ (l : List γ) (b : Array E), HoldsE (forIn l b f) fun r ↦ r.size = b.size + l.length
  | [], b => by
    simp only [List.forIn_nil, List.length_nil, Nat.add_zero]
    exact holdsE_pure rfl
  | x :: l, b => by
    rw [List.forIn_cons]
    refine holdsE_bind (hf x b) fun st ⟨y, hst⟩ ↦ ?_
    subst hst
    simp only
    refine holdsE_mono (holdsE_forIn_push f hf l (b.push y)) fun r hr ↦ ?_
    simp only [Array.size_push, List.length_cons] at hr ⊢
    omega

theorem holdsE_nextScalars_length (count : ℕ) :
    HoldsE (nextScalars (m := m) count) fun l ↦ l.length = count := by
  unfold nextScalars
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine holdsE_bind (holdsE_forIn_push _ (fun x b ↦ ?_) _ _) fun out h ↦ holdsE_pure ?_
  · exact holdsE_bind (holdsE_true (m := m) _) fun y _ ↦ holdsE_pure ⟨y, rfl⟩
  · simp only [List.size_toArray, List.length_range', Std.Legacy.Range.size] at h ⊢
    simp [h]

theorem list_three {α : Type} {l : List α} (h : l.length = 3) : ∃ a b c, l = [a, b, c] := by
  match l, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

/-- **The batch makes one point claim per given claim, in order**: given `C1`'s, `C2`'s and the setup's claims, no bit
slice and nothing pending, three point openings and no matrices' claim. -/
theorem holdsE_batchFs_openings (F : KeccakState → m KeccakState) (fs : FsShape)
    (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (hc : combined.map (·.1) = [.c1, .c2, .setup]) :
    HoldsE (batchFs F fs combined layouts none ringMap none) fun y ↦ y.2 = none ∧ OpeningsShape y.1 := by
  obtain ⟨x1, x2, x3, rfl⟩ := list_three (by simpa using congrArg List.length hc)
  obtain ⟨k1, a⟩ := x1
  obtain ⟨k2, b⟩ := x2
  obtain ⟨k3, d⟩ := x3
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hc
  obtain ⟨rfl, rfl, rfl, -⟩ := hc
  unfold batchFs
  refine holdsE_bind (holdsE_true (m := m) _) fun lambda _ ↦ ?_
  dsimp only
  split <;>
    repeat (first
      | (refine holdsE_pure ⟨rfl, ?_⟩
         obtain ⟨v1, v2, v3, rfl⟩ := list_three ‹_ = 3›
         exact ⟨_, _, _, _, _, _, rfl⟩)
      | refine holdsE_bind (holdsE_nextScalars_length (m := m) _) fun vals hv ↦ ?_
      | refine holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦ ?_)

/-- **π1-rec3's reduction** (the walk, point claims) makes three point openings, `C1`'s, `C2`'s and the setup's. -/
theorem holdsE_reduceWithFs_openings (F : KeccakState → m KeccakState) (stmt : List E) :
    HoldsE (reduceWithFs F reference stmt (.flock flockMain) .point .rec3 true) fun r ↦ OpeningsShape r.openings := by
  unfold reduceWithFs
  dsimp only
  split
  · exact holdsE_bind (holdsE_throw (m := m) _) fun _ h ↦ False.elim h
  refine holdsE_bind (holdsE_true (m := m) _) fun counts _ ↦ ?_
  refine holdsE_bind (holdsE_true (m := m) _) fun root1 _ ↦ ?_
  refine holdsE_bind (holdsE_true (m := m) _) fun alphas _ ↦ ?_
  refine holdsE_bind (holdsE_true (m := m) _) fun beta _ ↦ ?_
  refine holdsE_bind (holdsE_true (m := m) _) fun gamma _ ↦ ?_
  refine holdsE_bind (holdsE_verifyWalkedFs F _ _ _) fun fl hfl ↦ ?_
  obtain ⟨p, mp, tg, rfl⟩ := hfl
  refine holdsE_bind (holdsE_pure_eq (m := m) _) fun x hx ↦ ?_
  subst hx
  dsimp only
  repeat (first
    | refine holdsE_bind (holdsE_batchFs_openings F _ _ _ _ ?_) fun y hy ↦ ?_
    | refine holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦ ?_
    | split)
  all_goals try refine holdsE_ite ?_ ?_
  all_goals try exact holdsE_pure (‹_ ∧ OpeningsShape _›).2
  all_goals
    refine filterMap_combine_fst _ _ fun c hc ↦ ?_
    simp only [commitments, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact exists_push_of _ (exists_append_left _ (exists_push_of _ (exists_push_of _ (exists_push_of _
        (exists_push_of _ (exists_push_of _ (exists_push_self _ rfl)))))))
    · exact exists_push_of _ (exists_append_list _ (heapRelations_c2 _ _ _ _ _ _ _ _ _ _ _ _ _))
    · exact exists_push_of _ (exists_append_left _ (exists_push_of _ (exists_push_of _ (exists_push_of _
        (exists_push_of _ (exists_push_self _ rfl))))))

/-- **π1-rec3's run, over any permutation**: a result has three point openings. -/
theorem runWithFs_openings (F : KeccakState → m KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) :
    Holds (runWithFs F reference iv publicInput stream (.flock flockMain) .point .rec3 true) fun o ↦
      ∀ r, o.result = .ok r → OpeningsShape r.openings := by
  unfold runWithFs
  refine holds_bind (holds_true _) fun seed _ ↦
    holds_bind (Q := fun p ↦ ∀ a, p.1 = .ok a → OpeningsShape a.openings) ?_ fun p hp ↦ ?_
  · refine holdsE_bind (Q := fun r : Reduced ↦ OpeningsShape r.openings)
      (P := fun r : Reduced ↦ OpeningsShape r.openings) (holdsE_reduceWithFs_openings F _) (fun a ha ↦ ?_) _
    exact holdsE_bind (holdsE_true (m := m) _) fun _ _ ↦ holdsE_pure ha
  · obtain ⟨result, chan⟩ := p
    exact holds_pure hp

end Generic

/-- **`Pi1RunOpenings`**: a run of π1-rec3's verifier that returns a result has three point openings, no bit slice,
in `commitments` order. -/
theorem pi1RunOpenings : Pi1RunOpenings := by
  intro iv publicInput stream r hr
  exact holds_id (runWithFs_openings (m := Id) (fun s ↦ pure (keccakF1600 s)) iv publicInput stream) r hr

end RecCompose

/-- info: 'RecCompose.pi1RunOpenings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1RunOpenings
