-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHHeap

/-!
# The heap's layout fits (`HeapLayout.new`, milestone 4)

`HeapLayout.new lm lb heights` sorts the used blocks (the memory's, the bytecode's, each table's) largest first,
lays them end to end from `base = 2^d` (`d = ⌈log₂ Σ 2^r⌉`), then covers the rest of `[base, 2 base)` with
unused blocks (`unusedBlocks`). Here:

* `heapLayout_new_eq`: the layout is `placeFrom base 0 sorted ++ unusedBlocks base total`, `h = d + 1`;
* `placeFrom_spec`: blocks of sizes sorted largest first, laid from an offset every size divides, are aligned,
  pairwise disjoint, and fill `[base + off, base + off + Σ 2^r)`;
* `unusedBlocks_spec`: every unused block is aligned, in `[base + total, 2 base)`, and they are pairwise disjoint
  (the loops' invariants; `trailingZeros_dvd`: `2^tz(n) ∣ n`; the inner loop's `65` steps shrink the block until
  it fits, `shrink_spec`);
* **`layoutOK_new`**: the layout fits (`LayoutOK`), and **`used_perm`**: its used blocks' `(leaves, r)` are a
  permutation of the used list (so the memory's block has `r = lm`, the bytecode's `lb`, table `t`'s its height).

No hypothesis on the sizes: the facts hold at every shape.
-/

namespace UniComplete.AlgH

open UniStatement LeanVM.Parameters
open UniComplete.Domain (ite_pos_of ite_neg_of)

/-! ### The used blocks -/

/-- The used blocks' `(leaves, r)`, in `HeapLayout.new`'s order before sorting. -/
def usedList (lm lb : ℕ) (hs : List ℕ) : List (Leaves × ℕ) :=
  [(.memory, lm), (.bytecode, lb)] ++ (List.range hs.length).map fun t ↦ (.table t, hs.getD t 0)

/-- `HeapLayout.new`'s order: larger first, ties by `Leaves.order`. -/
def layLe (a b : Leaves × ℕ) : Bool := b.2 < a.2 || (a.2 == b.2 && a.1.order ≤ b.1.order)

/-- The used blocks, sorted. -/
def laySorted (lm lb : ℕ) (hs : List ℕ) : List (Leaves × ℕ) := (usedList lm lb hs).mergeSort layLe

/-- Their leaves' count. -/
def layTotal (lm lb : ℕ) (hs : List ℕ) : ℕ := ((laySorted lm lb hs).map fun p ↦ 2 ^ p.2).sum

/-- Blocks laid end to end from `base + off`. -/
def placeFrom (base : ℕ) : ℕ → List (Leaves × ℕ) → List Block
  | _, [] => []
  | off, (l, r) :: rest => ⟨l, r, base + off⟩ :: placeFrom base (off + 2 ^ r) rest

theorem foldl_place (base : ℕ) (f : Array Block × ℕ → Leaves × ℕ → Array Block × ℕ)
    (hf : ∀ acc l r, f acc (l, r) = (acc.1.push ⟨l, r, base + acc.2⟩, acc.2 + 2 ^ r)) :
    ∀ (xs : List (Leaves × ℕ)) (acc : Array Block) (off : ℕ),
      (xs.foldl f (acc, off)).1.toList = acc.toList ++ placeFrom base off xs ∧
        (xs.foldl f (acc, off)).2 = off + (xs.map fun p ↦ 2 ^ p.2).sum
  | [], acc, off => by simp [placeFrom]
  | (l, r) :: rest, acc, off => by
    rw [List.foldl_cons, hf]
    obtain ⟨h1, h2⟩ := foldl_place base f hf rest (acc.push ⟨l, r, base + off⟩) (off + 2 ^ r)
    refine ⟨?_, ?_⟩
    · rw [h1, Array.toList_push, placeFrom, List.append_assoc, List.singleton_append]
    · rw [h2, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem heapLayout_new_eq (lm lb : ℕ) (hs : List ℕ) :
    HeapLayout.new lm lb hs = ⟨log2Ceil (layTotal lm lb hs) + 1,
      placeFrom (2 ^ log2Ceil (layTotal lm lb hs)) 0 (laySorted lm lb hs) ++
        unusedBlocks (2 ^ log2Ceil (layTotal lm lb hs)) (layTotal lm lb hs)⟩ := by
  have hp := foldl_place (2 ^ log2Ceil (layTotal lm lb hs))
    (fun (acc : Array Block × ℕ) (x : Leaves × ℕ) ↦
      (acc.1.push ⟨x.1, x.2, 2 ^ log2Ceil (layTotal lm lb hs) + acc.2⟩, acc.2 + 2 ^ x.2))
    (fun _ _ _ ↦ rfl) (laySorted lm lb hs) #[] 0
  rw [Array.toList_empty, List.nil_append, Nat.zero_add] at hp
  have e : HeapLayout.new lm lb hs = ⟨log2Ceil (layTotal lm lb hs) + 1,
      (List.foldl (fun (acc : Array Block × ℕ) (x : Leaves × ℕ) ↦
        (acc.1.push ⟨x.1, x.2, 2 ^ log2Ceil (layTotal lm lb hs) + acc.2⟩, acc.2 + 2 ^ x.2))
        (#[], 0) (laySorted lm lb hs)).1.toList ++
      unusedBlocks (2 ^ log2Ceil (layTotal lm lb hs))
        (List.foldl (fun (acc : Array Block × ℕ) (x : Leaves × ℕ) ↦
          (acc.1.push ⟨x.1, x.2, 2 ^ log2Ceil (layTotal lm lb hs) + acc.2⟩, acc.2 + 2 ^ x.2))
          (#[], 0) (laySorted lm lb hs)).2⟩ := rfl
  rw [e, hp.1, hp.2]
  rfl

/-! ### Laid end to end, largest first -/

theorem placeFrom_map (base : ℕ) : ∀ (off : ℕ) (xs : List (Leaves × ℕ)),
    (placeFrom base off xs).map (fun b ↦ (b.leaves, b.r)) = xs
  | _, [] => rfl
  | off, (l, r) :: rest => by rw [placeFrom, List.map_cons, placeFrom_map base (off + 2 ^ r) rest]

theorem placeFrom_spec (base : ℕ) : ∀ (xs : List (Leaves × ℕ)) (off : ℕ),
    xs.Pairwise (fun a b ↦ b.2 ≤ a.2) → (∀ p ∈ xs, 2 ^ p.2 ∣ base + off) →
      (∀ b ∈ placeFrom base off xs, base + off ≤ b.position ∧
        b.position + 2 ^ b.r ≤ base + off + (xs.map fun p ↦ 2 ^ p.2).sum ∧ 2 ^ b.r ∣ b.position) ∧
      (placeFrom base off xs).Pairwise blockDisjoint
  | [], _, _, _ => ⟨fun b hb ↦ absurd hb List.not_mem_nil, List.Pairwise.nil⟩
  | (l, r) :: rest, off, hs, hd => by
    rw [List.pairwise_cons] at hs
    have hd' : ∀ p ∈ rest, 2 ^ p.2 ∣ base + (off + 2 ^ r) := fun p hp ↦ by
      rw [← Nat.add_assoc]
      exact dvd_add (hd p (List.mem_cons_of_mem _ hp)) (Nat.pow_dvd_pow 2 (hs.1 p hp))
    obtain ⟨ih1, ih2⟩ := placeFrom_spec base rest (off + 2 ^ r) hs.2 hd'
    rw [placeFrom]
    refine ⟨fun b hb ↦ ?_, List.pairwise_cons.mpr ⟨fun b hb ↦ ?_, ih2⟩⟩
    · rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · refine ⟨le_rfl, ?_, hd (l, r) (List.mem_cons_self ..)⟩
        simp only [List.map_cons, List.sum_cons]
        omega
      · obtain ⟨a1, a2, a3⟩ := ih1 b hb
        refine ⟨by have := Nat.le_add_right (base + off) (2 ^ r); omega, ?_, a3⟩
        simp only [List.map_cons, List.sum_cons]
        omega
    · obtain ⟨a1, -, -⟩ := ih1 b hb
      unfold blockDisjoint
      left
      show base + off + 2 ^ r ≤ b.position
      omega

/-! ### `trailingZeros` -/

theorem trailingZeros_le (n : ℕ) : trailingZeros n ≤ 64 := by
  unfold trailingZeros
  split_ifs
  · exact le_rfl
  · rcases h : (List.range 64).find? (fun k ↦ n.testBit k) with _ | k
    · simp
    · have := List.mem_of_find?_eq_some h
      simp only [Option.getD_some]
      exact (List.mem_range.mp this).le

theorem testBit_lt_trailingZeros (n : ℕ) {j : ℕ} (hj : j < trailingZeros n) : n.testBit j = false := by
  unfold trailingZeros at hj
  split_ifs at hj with h0
  · rw [h0, Nat.zero_testBit]
  · rcases h : (List.range 64).find? (fun k ↦ n.testBit k) with _ | k
    · rw [h, Option.getD_none] at hj
      have := List.find?_eq_none.mp h j (List.mem_range.mpr hj)
      simpa using this
    · rw [h, Option.getD_some] at hj
      obtain ⟨-, i, hi, hik, hbefore⟩ := List.find?_eq_some_iff_getElem.mp h
      rw [List.getElem_range] at hik
      subst hik
      have := hbefore j hj
      rw [List.getElem_range] at this
      simpa using this

/-- **`2^tz(n) ∣ n`.** -/
theorem trailingZeros_dvd (n : ℕ) : 2 ^ trailingZeros n ∣ n := by
  refine Nat.dvd_of_mod_eq_zero (Nat.eq_of_testBit_eq fun j ↦ ?_)
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hj : j < trailingZeros n
  · rw [testBit_lt_trailingZeros n hj]; simp
  · simp [hj]

/-! ### The unused blocks -/

/-- The inner loop's step: shrink the block while it does not fit. -/
def shrinkBody (base off : ℕ) : ℕ → ℕ → Id (ForInStep ℕ) := fun _ r ↦
  if off + 2 ^ r > base then pure (ForInStep.yield (r - 1)) else pure (ForInStep.yield r)

/-- The inner loop's result. -/
def shrinkRun (base off : ℕ) (L : List ℕ) (r : ℕ) : ℕ := Id.run (forIn L r (shrinkBody base off))

theorem shrinkRun_cons (base off x : ℕ) (L : List ℕ) (r : ℕ) :
    shrinkRun base off (x :: L) r = shrinkRun base off L (if off + 2 ^ r > base then r - 1 else r) := by
  unfold shrinkRun
  rw [List.forIn_cons]
  unfold shrinkBody
  split_ifs <;> rfl

theorem shrink_spec (base off : ℕ) (hoff : off < base) :
    ∀ (L : List ℕ) (r : ℕ), shrinkRun base off L r ≤ r ∧
      (off + 2 ^ r ≤ base → shrinkRun base off L r = r) ∧
      (off + 2 ^ shrinkRun base off L r ≤ base ∨ (L.length ≤ r ∧ shrinkRun base off L r = r - L.length))
  | [], r => ⟨le_rfl, fun _ ↦ rfl, Or.inr ⟨Nat.zero_le _, rfl⟩⟩
  | x :: L, r => by
    rw [shrinkRun_cons]
    by_cases hc : off + 2 ^ r > base
    · rw [ite_pos_of hc]
      obtain ⟨i1, i2, i3⟩ := shrink_spec base off hoff L (r - 1)
      have hr : 1 ≤ r := by
        by_contra h0
        have : r = 0 := by omega
        subst this
        simp at hc
        omega
      refine ⟨by omega, fun h ↦ absurd h (by omega), ?_⟩
      rcases i3 with i3 | ⟨i3, i4⟩
      · exact Or.inl i3
      · right
        simp only [List.length_cons]
        omega
    · rw [ite_neg_of hc]
      obtain ⟨i1, i2, -⟩ := shrink_spec base off hoff L r
      have hfit : off + 2 ^ r ≤ base := by omega
      exact ⟨i1, fun _ ↦ i2 hfit, Or.inl (by rw [i2 hfit]; exact hfit)⟩

/-- **The shrunk block fits** after `65` steps (`tz ≤ 64`). -/
theorem shrinkRun_fits (base off : ℕ) (hoff : off < base) (L : List ℕ) (hL : 64 < L.length) :
    off + 2 ^ shrinkRun base off L (trailingZeros off) ≤ base ∧
      shrinkRun base off L (trailingZeros off) ≤ trailingZeros off := by
  obtain ⟨i1, -, i3⟩ := shrink_spec base off hoff L (trailingZeros off)
  refine ⟨?_, i1⟩
  rcases i3 with i3 | ⟨i3, -⟩
  · exact i3
  · have := trailingZeros_le off
    omega

/-- The outer loop's step. -/
def outerBody (base : ℕ) (L65 : List ℕ) : ℕ → Array Block × ℕ → Id (ForInStep (Array Block × ℕ)) :=
  fun _ s ↦
    if s.2 < base then do
      let r ← forIn L65 (trailingZeros s.2) (shrinkBody base s.2)
      pure (ForInStep.yield (s.1.push ⟨.unused, r, base + s.2⟩, s.2 + 2 ^ r))
    else pure (ForInStep.yield (s.1, s.2))

/-- The outer loop's invariant. -/
structure UInv (d off0 : ℕ) (s : Array Block × ℕ) : Prop where
  off_ge : off0 ≤ s.2
  off_le : s.2 ≤ 2 ^ d
  blocks : ∀ b ∈ s.1.toList, b.leaves = .unused ∧ 2 ^ d + off0 ≤ b.position ∧
    b.position + 2 ^ b.r ≤ 2 ^ d + s.2 ∧ 2 ^ b.r ∣ b.position
  disj : s.1.toList.Pairwise blockDisjoint

theorem outer_inv (d off0 : ℕ) (L65 : List ℕ) (hL : 64 < L65.length) :
    ∀ (L : List ℕ) (s : Array Block × ℕ), UInv d off0 s →
      UInv d off0 (Id.run (forIn L s (outerBody (2 ^ d) L65)))
  | [], s, hs => hs
  | x :: L, s, hs => by
    unfold Id.run
    rw [List.forIn_cons]
    by_cases hc : s.2 < 2 ^ d
    · have hstep : outerBody (2 ^ d) L65 x s = pure (ForInStep.yield
          (s.1.push ⟨.unused, shrinkRun (2 ^ d) s.2 L65 (trailingZeros s.2), 2 ^ d + s.2⟩,
            s.2 + 2 ^ shrinkRun (2 ^ d) s.2 L65 (trailingZeros s.2))) := by
        unfold outerBody
        rw [ite_pos_of hc]
        rfl
      rw [hstep]
      refine outer_inv d off0 L65 hL L _ ?_
      obtain ⟨hfit, hle⟩ := shrinkRun_fits (2 ^ d) s.2 hc L65 hL
      set r := shrinkRun (2 ^ d) s.2 L65 (trailingZeros s.2)
      have hrd : 2 ^ r ∣ 2 ^ d := by
        refine Nat.pow_dvd_pow 2 ?_
        by_contra hlt
        have : 2 ^ (d + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega
      have hro : 2 ^ r ∣ s.2 := (Nat.pow_dvd_pow 2 hle).trans (trailingZeros_dvd s.2)
      refine ⟨by have := hs.off_ge; omega, hfit, fun b hb ↦ ?_, ?_⟩
      · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · obtain ⟨b1, b2, b3, b4⟩ := hs.blocks b hb
          exact ⟨b1, b2, by omega, b4⟩
        · refine ⟨rfl, ?_, ?_, dvd_add hrd hro⟩
          · show 2 ^ d + off0 ≤ 2 ^ d + s.2
            have := hs.off_ge; omega
          · show 2 ^ d + s.2 + 2 ^ r ≤ 2 ^ d + (s.2 + 2 ^ r)
            omega
      · rw [Array.toList_push, List.pairwise_append]
        refine ⟨hs.disj, List.pairwise_singleton _ _, fun a ha b hb ↦ ?_⟩
        rw [List.mem_singleton] at hb
        subst hb
        obtain ⟨-, -, a3, -⟩ := hs.blocks a ha
        left
        exact a3
    · have hstep : outerBody (2 ^ d) L65 x s = pure (ForInStep.yield (s.1, s.2)) := by
        unfold outerBody
        rw [ite_neg_of hc]
      rw [hstep]
      exact outer_inv d off0 L65 hL L _ hs

theorem unusedBlocks_eq (base off : ℕ) :
    unusedBlocks base off = (Id.run (forIn (List.range' 0 (Std.Legacy.Range.size [:2 * (Nat.log2 base + 1) + 2]))
      (#[], off) (outerBody base (List.range' 0 (Std.Legacy.Range.size [:65]))))).1.toList := by
  unfold unusedBlocks
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- **The unused blocks are aligned, in `[base + off, 2 base)`, pairwise disjoint** (`base = 2^d`). -/
theorem unusedBlocks_spec (d off : ℕ) (hoff : off ≤ 2 ^ d) :
    (∀ b ∈ unusedBlocks (2 ^ d) off, b.leaves = .unused ∧ 2 ^ d + off ≤ b.position ∧
      b.position + 2 ^ b.r ≤ 2 ^ (d + 1) ∧ 2 ^ b.r ∣ b.position) ∧
    (unusedBlocks (2 ^ d) off).Pairwise blockDisjoint := by
  have h65 : 64 < (List.range' 0 (Std.Legacy.Range.size [:65])).length := by
    rw [List.length_range']; decide
  have hinv := outer_inv d off _ h65 (List.range' 0 (Std.Legacy.Range.size [:2 * (Nat.log2 (2 ^ d) + 1) + 2]))
    (#[], off) ⟨le_rfl, hoff, fun b hb ↦ absurd hb List.not_mem_nil, List.Pairwise.nil⟩
  rw [unusedBlocks_eq]
  refine ⟨fun b hb ↦ ?_, hinv.disj⟩
  obtain ⟨b1, b2, b3, b4⟩ := hinv.blocks b hb
  have := hinv.off_le
  refine ⟨b1, b2, ?_, b4⟩
  rw [pow_succ]
  omega

/-! ### The layout -/

theorem le_two_pow_log2Ceil (n : ℕ) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil
  split_ifs with h
  · simp only [pow_zero]; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

theorem laySorted_pairwise (lm lb : ℕ) (hs : List ℕ) :
    (laySorted lm lb hs).Pairwise (fun a b ↦ b.2 ≤ a.2) := by
  have hp := List.pairwise_mergeSort (le := layLe) (fun a b c h1 h2 ↦ by
      unfold layLe at *
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
      omega)
    (fun a b ↦ by
      unfold layLe
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      omega) (usedList lm lb hs)
  refine hp.imp fun {a b} h ↦ ?_
  unfold layLe at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

theorem usedList_not_unused (lm lb : ℕ) (hs : List ℕ) : ∀ p ∈ usedList lm lb hs, p.1 ≠ .unused := by
  intro p hp
  unfold usedList at hp
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map, List.mem_range] at hp
  rcases hp with rfl | rfl | ⟨t, _, rfl⟩ <;> simp

/-- **`HeapLayout.new`'s blocks fit.** -/
theorem layoutOK_new (lm lb : ℕ) (hs : List ℕ) : LayoutOK (HeapLayout.new lm lb hs) := by
  rw [heapLayout_new_eq]
  have hT : layTotal lm lb hs ≤ 2 ^ log2Ceil (layTotal lm lb hs) := le_two_pow_log2Ceil _
  have hsum : ((laySorted lm lb hs).map fun p ↦ 2 ^ p.2).sum = layTotal lm lb hs := rfl
  generalize log2Ceil (layTotal lm lb hs) = d at hT ⊢
  have hdiv : ∀ p ∈ laySorted lm lb hs, 2 ^ p.2 ∣ 2 ^ d + 0 := by
    intro p hp
    rw [Nat.add_zero]
    refine Nat.pow_dvd_pow 2 ?_
    have hle : 2 ^ p.2 ≤ ((laySorted lm lb hs).map fun p ↦ 2 ^ p.2).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩)
    by_contra hlt
    have : 2 ^ (d + 1) ≤ 2 ^ p.2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this
    have := Nat.one_le_two_pow (n := d)
    omega
  obtain ⟨hp1, hp2⟩ := placeFrom_spec (2 ^ d) (laySorted lm lb hs) 0 (laySorted_pairwise lm lb hs) hdiv
  obtain ⟨hu1, hu2⟩ := unusedBlocks_spec d (layTotal lm lb hs) hT
  have hd1 : d + 1 - 1 = d := Nat.add_sub_cancel d 1
  have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
  refine ⟨by dsimp only; omega, fun b hb ↦ ?_, fun b hb ↦ ?_, fun b hb ↦ ?_, ?_⟩
  · dsimp only
    rw [hd1]
    rcases List.mem_append.mp hb with hb | hb
    · have := (hp1 b hb).1; omega
    · have := (hu1 b hb).2.1; omega
  · dsimp only
    rcases List.mem_append.mp hb with hb | hb
    · have := (hp1 b hb).2.1
      omega
    · exact (hu1 b hb).2.2.1
  · rcases List.mem_append.mp hb with hb | hb
    · exact (hp1 b hb).2.2
    · exact (hu1 b hb).2.2.2
  · show (placeFrom (2 ^ d) 0 (laySorted lm lb hs) ++ unusedBlocks (2 ^ d) (layTotal lm lb hs)).Pairwise
      blockDisjoint
    rw [List.pairwise_append]
    refine ⟨hp2, hu2, fun a ha b hb ↦ ?_⟩
    have := (hp1 a ha).2.1
    have := (hu1 b hb).2.1
    left
    omega

/-- **The used blocks are the used list** (as `(leaves, r)`, up to order). -/
theorem used_perm (lm lb : ℕ) (hs : List ℕ) :
    (((HeapLayout.new lm lb hs).blocks.filter fun b ↦ decide (blockUsed b)).map fun b ↦ (b.leaves, b.r)).Perm
      (usedList lm lb hs) := by
  rw [heapLayout_new_eq]
  show (((placeFrom _ 0 (laySorted lm lb hs) ++ unusedBlocks _ _).filter fun b ↦ decide (blockUsed b)).map
    fun b ↦ (b.leaves, b.r)).Perm (usedList lm lb hs)
  have hT : layTotal lm lb hs ≤ 2 ^ log2Ceil (layTotal lm lb hs) := le_two_pow_log2Ceil _
  rw [List.filter_append]
  have hu : (unusedBlocks (2 ^ log2Ceil (layTotal lm lb hs)) (layTotal lm lb hs)).filter
      (fun b ↦ decide (blockUsed b)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb
    have := ((unusedBlocks_spec _ _ hT).1 b hb).1
    simp [blockUsed, this]
  have hp : (placeFrom (2 ^ log2Ceil (layTotal lm lb hs)) 0 (laySorted lm lb hs)).filter
      (fun b ↦ decide (blockUsed b)) = placeFrom (2 ^ log2Ceil (layTotal lm lb hs)) 0 (laySorted lm lb hs) := by
    rw [List.filter_eq_self]
    intro b hb
    have hmem : (b.leaves, b.r) ∈ laySorted lm lb hs := by
      rw [← placeFrom_map (2 ^ log2Ceil (layTotal lm lb hs)) 0 (laySorted lm lb hs)]
      exact List.mem_map_of_mem hb
    exact decide_eq_true (usedList_not_unused lm lb hs _ ((List.mergeSort_perm _ _).mem_iff.mp hmem))
  rw [hu, hp, List.append_nil, placeFrom_map]
  exact List.mergeSort_perm _ _

end UniComplete.AlgH
