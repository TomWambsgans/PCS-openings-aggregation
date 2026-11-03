-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHTree

/-!
# The heap's values (`heapValues`): the leaves at their blocks, every inner node its children's product

`heapValues` writes the used blocks' leaves into `2^h` ones, then fills the levels from the leaves up
(`heapLevel`, half `2^(h−1)`, …, `2`), then zeroes position `0`. Here, for any layout:

* `heapValues_size`: `2^h` values; **`heapValues_tree`** (`1 ≤ h`): every inner node `1 ≤ p < 2^(h−1)` is the
  product of its children (`TreeValues`, what `AlgHTree` needs);
* `heapValues_getD_leaf`: on the leaves `[2^(h−1), 2^h)` the heap is the leaves' array (`heapLeaves`).

And for a layout whose blocks fit (`LayoutOK`: in the leaves' range, aligned, pairwise disjoint):

* **`heapValues_block`**: a used block's leaf `i` is at `position + i`; **`heapValues_free`**: a leaf in no used
  block (an unused block's, in particular) is `1`.

The levels and the leaves are each a fold of `Array.set!` whose reads are never overwritten (a level reads
positions `≥ half` and writes `[half/2, half)`; distinct blocks are disjoint), proved by induction on the fold.
-/

namespace UniComplete.AlgH

open UniStatement LeanVM.Parameters
open UniComplete.Domain (ite_pos_of ite_neg_of)

/-! ### One level -/

/-- A level's step: position `a + j` becomes the product of its children. -/
def levelStep (a : ℕ) (h : Array E) (j : ℕ) : Array E :=
  h.set! (a + j) (h.getD (2 * (a + j)) 0 * h.getD (2 * (a + j) + 1) 0)

theorem levelFold_spec (heap : Array E) (a : ℕ) :
    ∀ n, a + n ≤ heap.size → ((List.range n).foldl (levelStep a) heap).size = heap.size ∧
      ∀ q, ((List.range n).foldl (levelStep a) heap).getD q 0 =
        if a ≤ q ∧ q < a + n then heap.getD (2 * q) 0 * heap.getD (2 * q + 1) 0 else heap.getD q 0
  | 0, _ => ⟨rfl, fun q ↦ by rw [ite_neg_of (by omega)]; rfl⟩
  | n + 1, hn => by
    obtain ⟨hs, hg⟩ := levelFold_spec heap a n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [levelStep, Array.size_set!, hs], fun q ↦ ?_⟩
    rw [levelStep, getD_set! _ _ _ (by rw [hs]; omega)]
    simp only [hg]
    split_ifs <;> first | omega | (subst_vars; rfl)

theorem heapLevel_eq (heap : Array E) (half : ℕ) :
    heapLevel heap half = (List.range (half / 2)).foldl (levelStep (half / 2)) heap := rfl

theorem heapLevel_size (heap : Array E) {half : ℕ} (hh : half ≤ heap.size) :
    (heapLevel heap half).size = heap.size := by
  rw [heapLevel_eq]; exact (levelFold_spec heap _ _ (by omega)).1

theorem heapLevel_getD (heap : Array E) {half : ℕ} (hh : half ≤ heap.size) (he : half % 2 = 0) (q : ℕ) :
    (heapLevel heap half).getD q 0 =
      if half / 2 ≤ q ∧ q < half then heap.getD (2 * q) 0 * heap.getD (2 * q + 1) 0 else heap.getD q 0 := by
  rw [heapLevel_eq, (levelFold_spec heap _ _ (by omega)).2, show half / 2 + half / 2 = half by omega]

/-! ### The levels -/

/-- The first `J` levels from the leaves up. -/
def levelsUpTo (L : Array E) (h J : ℕ) : Array E :=
  (List.range J).foldl (fun heap j ↦ heapLevel heap (2 ^ (h - 1 - j))) L

theorem levelsUpTo_spec (L : Array E) (h : ℕ) (hL : L.size = 2 ^ h) :
    ∀ J, J ≤ h - 1 → (levelsUpTo L h J).size = 2 ^ h ∧
      (∀ q, 2 ^ (h - 1) ≤ q → (levelsUpTo L h J).getD q 0 = L.getD q 0) ∧
      ∀ p, 2 ^ (h - 1 - J) ≤ p → p < 2 ^ (h - 1) →
        (levelsUpTo L h J).getD p 0 = (levelsUpTo L h J).getD (2 * p) 0 * (levelsUpTo L h J).getD (2 * p + 1) 0
  | 0, _ => ⟨hL, fun _ _ ↦ rfl, fun p h1 h2 ↦ by rw [Nat.sub_zero] at h1; omega⟩
  | J + 1, hJ => by
    obtain ⟨hs, hleaf, htree⟩ := levelsUpTo_spec L h hL J (by omega)
    have hdef : levelsUpTo L h (J + 1) = heapLevel (levelsUpTo L h J) (2 ^ (h - 1 - J)) := by
      rw [levelsUpTo, List.range_succ, List.foldl_append]; rfl
    have hhalf : 2 ^ (h - 1 - J) ≤ (levelsUpTo L h J).size := by
      rw [hs]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have heven : 2 ^ (h - 1 - J) % 2 = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, h - 1 - J = k + 1 := ⟨h - 2 - J, by omega⟩
      rw [hk, pow_succ]; omega
    have hdiv : 2 ^ (h - 1 - J) / 2 = 2 ^ (h - 1 - (J + 1)) := by
      obtain ⟨k, hk⟩ : ∃ k, h - 1 - J = k + 1 := ⟨h - 2 - J, by omega⟩
      rw [hk, show h - 1 - (J + 1) = k by omega, pow_succ]; omega
    have hle : 2 ^ (h - 1 - J) ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hdef]
    refine ⟨by rw [heapLevel_size _ hhalf, hs], fun q hq ↦ ?_, fun p hp1 hp2 ↦ ?_⟩
    · rw [heapLevel_getD _ hhalf heven, ite_neg_of (show ¬(2 ^ (h - 1 - J) / 2 ≤ q ∧ q < 2 ^ (h - 1 - J)) by
        omega), hleaf q hq]
    · have hcd : 2 ^ (h - 1 - J) = 2 * 2 ^ (h - 1 - (J + 1)) := by rw [← hdiv]; omega
      rw [heapLevel_getD _ hhalf heven p, heapLevel_getD _ hhalf heven (2 * p),
        heapLevel_getD _ hhalf heven (2 * p + 1), hdiv,
        ite_neg_of (show ¬(2 ^ (h - 1 - (J + 1)) ≤ 2 * p ∧ 2 * p < 2 ^ (h - 1 - J)) by omega),
        ite_neg_of (show ¬(2 ^ (h - 1 - (J + 1)) ≤ 2 * p + 1 ∧ 2 * p + 1 < 2 ^ (h - 1 - J)) by omega)]
      by_cases hp : p < 2 ^ (h - 1 - J)
      · rw [ite_pos_of ⟨hp1, hp⟩]
      · rw [ite_neg_of (by omega)]
        exact htree p (by omega) hp2

/-! ### The leaves -/

/-- Writing a block's `n` leaves at `position`. -/
def writeBlock (pos : ℕ) (vals : Array E) (h : Array E) (i : ℕ) : Array E := h.set! (pos + i) (vals.getD i 0)

theorem writeFold_spec (A : Array E) (pos : ℕ) (vals : Array E) :
    ∀ n, pos + n ≤ A.size → ((List.range n).foldl (writeBlock pos vals) A).size = A.size ∧
      ∀ q, ((List.range n).foldl (writeBlock pos vals) A).getD q 0 =
        if pos ≤ q ∧ q < pos + n then vals.getD (q - pos) 0 else A.getD q 0
  | 0, _ => ⟨rfl, fun q ↦ by rw [ite_neg_of (by omega)]; rfl⟩
  | n + 1, hn => by
    obtain ⟨hs, hg⟩ := writeFold_spec A pos vals n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [writeBlock, Array.size_set!, hs], fun q ↦ ?_⟩
    rw [writeBlock, getD_set! _ _ _ (by omega), hg]
    by_cases hq : q = pos + n
    · rw [ite_pos_of hq, ite_pos_of (by omega), hq, Nat.add_sub_cancel_left]
    · rw [ite_neg_of hq]
      by_cases hq' : pos ≤ q ∧ q < pos + n
      · rw [ite_pos_of hq', ite_pos_of (by omega)]
      · rw [ite_neg_of hq', ite_neg_of (by omega)]

/-- One block written into the heap (`heapValues`' first fold). -/
def leafStep (tr : Trace) (weights : Array E) (beta : E) (heap : Array E) (block : Block) : Array E :=
  match block.leaves with
  | .unused => heap
  | kind =>
    let values := blockLeaves tr weights beta kind
    (List.range (2 ^ block.r)).foldl (fun h i ↦ h.set! (block.position + i) (values.getD i 0)) heap

/-- **The heap's leaves**: the used blocks' leaves written into `2^h` ones. -/
def heapLeaves (tr : Trace) (weights : Array E) (beta : E) : Array E :=
  tr.shape.heap.blocks.foldl (leafStep tr weights beta) (Array.replicate (2 ^ tr.shape.heap.h) 1)

theorem heapValues_eq (tr : Trace) (weights : Array E) (beta : E) :
    heapValues tr weights beta =
      (levelsUpTo (heapLeaves tr weights beta) tr.shape.heap.h (tr.shape.heap.h - 1)).set! 0 0 := rfl

/-- A block is used. -/
def blockUsed (b : Block) : Prop := b.leaves ≠ .unused

instance (b : Block) : Decidable (blockUsed b) := inferInstanceAs (Decidable (_ ≠ _))

/-- Position `q` is one of a block's leaves. -/
def blockHolds (b : Block) (q : ℕ) : Prop := b.position ≤ q ∧ q < b.position + 2 ^ b.r

instance (b : Block) (q : ℕ) : Decidable (blockHolds b q) := inferInstanceAs (Decidable (_ ∧ _))

/-- Two blocks' leaves are disjoint. -/
def blockDisjoint (a b : Block) : Prop := a.position + 2 ^ a.r ≤ b.position ∨ b.position + 2 ^ b.r ≤ a.position

theorem leafStep_spec (tr : Trace) (weights : Array E) (beta : E) (A : Array E) (b : Block)
    (hb : b.position + 2 ^ b.r ≤ A.size) :
    (leafStep tr weights beta A b).size = A.size ∧ ∀ q, (leafStep tr weights beta A b).getD q 0 =
      if blockUsed b ∧ blockHolds b q then (blockLeaves tr weights beta b.leaves).getD (q - b.position) 0
      else A.getD q 0 := by
  unfold leafStep
  rcases hl : b.leaves with _ | _ | t | _
  all_goals first
    | exact ⟨rfl, fun q ↦ by rw [ite_neg_of (by simp [blockUsed, hl])]⟩
    | refine ⟨(writeFold_spec A b.position _ (2 ^ b.r) hb).1, fun q ↦ ?_⟩
      refine ((writeFold_spec A b.position _ (2 ^ b.r) hb).2 q).trans ?_
      simp only [blockUsed, blockHolds, hl, ne_eq, reduceCtorEq, not_false_eq_true, true_and]

theorem leavesFold_spec (tr : Trace) (weights : Array E) (beta : E) :
    ∀ (bs : List Block) (A : Array E), (∀ b ∈ bs, b.position + 2 ^ b.r ≤ A.size) → bs.Pairwise blockDisjoint →
      (bs.foldl (leafStep tr weights beta) A).size = A.size ∧
      ∀ q, (bs.foldl (leafStep tr weights beta) A).getD q 0 =
        match bs.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) with
        | some b => (blockLeaves tr weights beta b.leaves).getD (q - b.position) 0
        | none => A.getD q 0
  | [], A, _, _ => ⟨rfl, fun _ ↦ rfl⟩
  | b :: bs, A, hfit, hdis => by
    obtain ⟨hs1, hg1⟩ := leafStep_spec tr weights beta A b (hfit b (List.mem_cons_self ..))
    rw [List.pairwise_cons] at hdis
    obtain ⟨hs, hg⟩ := leavesFold_spec tr weights beta bs (leafStep tr weights beta A b)
      (fun b' hb' ↦ by rw [hs1]; exact hfit b' (List.mem_cons_of_mem _ hb')) hdis.2
    rw [List.foldl_cons]
    refine ⟨by rw [hs, hs1], fun q ↦ ?_⟩
    rw [hg q, List.find?_cons]
    by_cases hq : blockUsed b ∧ blockHolds b q
    · have hnone : bs.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) = none := by
        rw [List.find?_eq_none]
        intro b' hb' hc
        have hd := hdis.1 b' hb'
        simp only [decide_eq_true_eq] at hc
        unfold blockDisjoint at hd
        unfold blockHolds at hq hc
        omega
      rw [hnone, hg1, ite_pos_of hq, decide_eq_true hq]
    · rw [decide_eq_false hq]
      cases bs.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) with
      | some b' => rfl
      | none => rw [hg1, ite_neg_of hq]

/-! ### The heap, for a layout whose blocks fit -/

/-- **A layout whose blocks fit**: `h ≥ 1`, every block in the leaves' range `[2^(h−1), 2^h)` and aligned, the
blocks pairwise disjoint. -/
structure LayoutOK (layout : HeapLayout) : Prop where
  one_le : 1 ≤ layout.h
  lo : ∀ b ∈ layout.blocks, 2 ^ (layout.h - 1) ≤ b.position
  hi : ∀ b ∈ layout.blocks, b.position + 2 ^ b.r ≤ 2 ^ layout.h
  aligned : ∀ b ∈ layout.blocks, 2 ^ b.r ∣ b.position
  disjoint : layout.blocks.Pairwise blockDisjoint

theorem heapLeaves_size (tr : Trace) (weights : Array E) (beta : E) (hL : LayoutOK tr.shape.heap) :
    (heapLeaves tr weights beta).size = 2 ^ tr.shape.heap.h := by
  rw [heapLeaves, (leavesFold_spec tr weights beta _ _ (fun b hb ↦ by rw [Array.size_replicate]; exact hL.hi b hb)
    hL.disjoint).1, Array.size_replicate]

theorem heapLeaves_getD (tr : Trace) (weights : Array E) (beta : E) (hL : LayoutOK tr.shape.heap) (q : ℕ) :
    (heapLeaves tr weights beta).getD q 0 =
      match tr.shape.heap.blocks.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) with
      | some b => (blockLeaves tr weights beta b.leaves).getD (q - b.position) 0
      | none => (Array.replicate (2 ^ tr.shape.heap.h) (1 : E)).getD q 0 :=
  (leavesFold_spec tr weights beta _ _ (fun b hb ↦ by rw [Array.size_replicate]; exact hL.hi b hb)
    hL.disjoint).2 q

/-- **The heap has `2^h` values.** -/
theorem heapValues_size (tr : Trace) (weights : Array E) (beta : E) (hL : LayoutOK tr.shape.heap) :
    (heapValues tr weights beta).size = 2 ^ tr.shape.heap.h := by
  rw [heapValues_eq, Array.size_set!]
  exact (levelsUpTo_spec _ _ (heapLeaves_size tr weights beta hL) _ le_rfl).1

/-- **Every inner node is its children's product** (`TreeValues`). -/
theorem heapValues_tree (tr : Trace) (weights : Array E) (beta : E) (hL : LayoutOK tr.shape.heap) :
    TreeValues tr.shape.heap.h (heapValues tr weights beta) := by
  intro p hp1 hp2
  have hspec := levelsUpTo_spec _ _ (heapLeaves_size tr weights beta hL) _ le_rfl
  have hsz : 0 < (levelsUpTo (heapLeaves tr weights beta) tr.shape.heap.h (tr.shape.heap.h - 1)).size := by
    rw [hspec.1]; exact Nat.two_pow_pos _
  rw [heapValues_eq, getD_set! _ _ _ hsz, getD_set! _ _ _ hsz, getD_set! _ _ _ hsz, ite_neg_of (by omega),
    ite_neg_of (by omega), ite_neg_of (by omega)]
  exact hspec.2.2 p (by rw [Nat.sub_self, pow_zero]; exact hp1) hp2

/-- **On the leaves the heap is `heapLeaves`.** -/
theorem heapValues_getD_leaf (tr : Trace) (weights : Array E) (beta : E) (hL : LayoutOK tr.shape.heap) {q : ℕ}
    (hq : 2 ^ (tr.shape.heap.h - 1) ≤ q) : (heapValues tr weights beta).getD q 0 = (heapLeaves tr weights beta).getD q 0 := by
  have hspec := levelsUpTo_spec _ _ (heapLeaves_size tr weights beta hL) _ le_rfl
  have hsz : 0 < (levelsUpTo (heapLeaves tr weights beta) tr.shape.heap.h (tr.shape.heap.h - 1)).size := by
    rw [hspec.1]; exact Nat.two_pow_pos _
  have h1 : 1 ≤ 2 ^ (tr.shape.heap.h - 1) := Nat.one_le_two_pow
  rw [heapValues_eq, getD_set! _ _ _ hsz, ite_neg_of (by omega), hspec.2.1 q hq]

/-- **A used block's leaf `i` is at `position + i`.** -/
theorem heapValues_block (tr : Trace) (weights : Array E) (beta : E) (hL : LayoutOK tr.shape.heap) {b : Block}
    (hb : b ∈ tr.shape.heap.blocks) (hu : blockUsed b) {i : ℕ} (hi : i < 2 ^ b.r) :
    (heapValues tr weights beta).getD (b.position + i) 0 = (blockLeaves tr weights beta b.leaves).getD i 0 := by
  rw [heapValues_getD_leaf tr weights beta hL (by have := hL.lo b hb; omega), heapLeaves_getD tr weights beta hL]
  have hfind : tr.shape.heap.blocks.find? (fun b' ↦ decide (blockUsed b' ∧ blockHolds b' (b.position + i))) = some b := by
    have hex : ∃ b' ∈ tr.shape.heap.blocks, (decide (blockUsed b' ∧ blockHolds b' (b.position + i))) = true :=
      ⟨b, hb, decide_eq_true ⟨hu, by unfold blockHolds; omega⟩⟩
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex)
    have hmem := List.mem_of_find?_eq_some hb'
    have hp := List.find?_some hb'
    simp only [decide_eq_true_eq] at hp
    rw [hb']
    by_contra hne
    have hne' : b' ≠ b := fun h ↦ hne (by rw [h])
    have hsymm : Std.Symm blockDisjoint := ⟨fun a c h ↦ by unfold blockDisjoint at h ⊢; omega⟩
    have hd := hL.disjoint.forall hmem hb hne'
    unfold blockDisjoint at hd
    unfold blockHolds at hp
    omega
  rw [hfind]
  simp only [Nat.add_sub_cancel_left]

/-- **A leaf in no used block is `1`.** -/
theorem heapValues_free (tr : Trace) (weights : Array E) (beta : E) (hL : LayoutOK tr.shape.heap) {q : ℕ}
    (hq1 : 2 ^ (tr.shape.heap.h - 1) ≤ q) (hq2 : q < 2 ^ tr.shape.heap.h)
    (hfree : ∀ b ∈ tr.shape.heap.blocks, blockUsed b → ¬ blockHolds b q) : (heapValues tr weights beta).getD q 0 = 1 := by
  rw [heapValues_getD_leaf tr weights beta hL hq1, heapLeaves_getD tr weights beta hL]
  have hnone : tr.shape.heap.blocks.find? (fun b ↦ decide (blockUsed b ∧ blockHolds b q)) = none := by
    rw [List.find?_eq_none]
    intro b hb hc
    simp only [decide_eq_true_eq] at hc
    exact hfree b hb hc.1 hc.2
  rw [hnone]
  simp [Array.getD_eq_getD_getElem?, hq2]

end UniComplete.AlgH
