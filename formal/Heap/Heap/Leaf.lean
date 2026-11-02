-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Heap.Tree
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Two

/-!
# Leaves, blocks and the root

SPEC §5.2: a leaf is a ratio, the product of a row's push fingerprints over the product of its
pull fingerprints, checked in cross-multiplied form, `leaf · P = P'` (`P` the pulls' product,
`P'` the pushes'). Hence:

* **`prod_leaves_mul`**: the leaves' product times the pulls' product is the pushes' product,
  with no hypothesis; **`prod_leaves_eq_div`**: when no pull fingerprint is zero, the leaves'
  product is the pushes' over the pulls'.
* The leaves come in **blocks** (`LeafBlock`), `2^r` consecutive leaves each with its push and pull
  tuples, laid end to end (`LeavesHold`, `total`): a table's block has its executed rows'
  tuples and nothing on its padding rows (`LeafBlock.ofRows`, whose leaf identity is `leaf = 1`
  there, `leafHolds_ofRows`), a pair of boundary blocks has one tuple on each side per row, and an
  unused block has none (`leaf = 1`).
* **`heap_prod_eq`**: the tree identity, every block's leaf identity and the root identity
  `T(1) · fp(init) = fp(fin)` give `Π_{push} fp · fp(init) = Π_{pull} fp · fp(fin)`, the state
  boundary included, by multiplications only: **no fingerprint need be nonzero**. A zero pull
  fingerprint on a row makes, by that row's leaf identity, a push fingerprint of that row zero, so
  both products are zero.

Generic in the commutative monoid of the values and the type of the tuples.
-/

namespace Heap

open Finset

/-! ## The leaf lemma -/

section LeafLemma

variable {M : Type*} [CommMonoid M] {ι : Type*}

/-- **The leaf lemma, multiplied out.** If every leaf satisfies `leaf · P = P'`, the leaves'
product times the pulls' product is the pushes' product. -/
theorem prod_leaves_mul (s : Finset ι) (leaf P P' : ι → M) (h : ∀ k ∈ s, leaf k * P k = P' k) :
    (∏ k ∈ s, leaf k) * ∏ k ∈ s, P k = ∏ k ∈ s, P' k := by
  rw [← prod_mul_distrib]
  exact prod_congr rfl h

end LeafLemma

/-- **The leaf lemma.** If every leaf satisfies `leaf · P = P'`, where `P` is the product of the
row's pull fingerprints and `P'` of its push fingerprints, and no pull fingerprint is zero, then the
leaves' product is the push fingerprints' product over the pull fingerprints'. -/
theorem prod_leaves_eq_div {K : Type*} [Field K] {ι : Type*} (s : Finset ι) (leaf : ι → K)
    (pull push : ι → List K) (h : ∀ k ∈ s, leaf k * (pull k).prod = (push k).prod)
    (hnz : ∀ k ∈ s, ∀ d ∈ pull k, d ≠ 0) :
    ∏ k ∈ s, leaf k = (∏ k ∈ s, (push k).prod) / ∏ k ∈ s, (pull k).prod := by
  have hP : ∏ k ∈ s, (pull k).prod ≠ 0 :=
    prod_ne_zero_iff.mpr fun k hk ↦ List.prod_ne_zero fun h0 ↦ hnz k hk 0 h0 rfl
  rw [eq_div_iff hP]
  exact prod_leaves_mul s leaf (fun k ↦ (pull k).prod) (fun k ↦ (push k).prod) h

/-! ## Blocks of leaves -/

/-- **A block of leaves**: `2^r` consecutive leaves; leaf `k` has the push tuples `push k` and
the pull tuples `pull k`. -/
structure LeafBlock (τ : Type*) where
  /-- The block's variables: `2^r` leaves. -/
  r : ℕ
  /-- The push tuples of leaf `k`. -/
  push : ℕ → List τ
  /-- The pull tuples of leaf `k`. -/
  pull : ℕ → List τ

namespace LeafBlock

variable {τ : Type*}

/-- The number of leaves of a block. -/
abbrev size (b : LeafBlock τ) : ℕ := 2 ^ b.r

/-- Every push tuple of a block, leaf by leaf. -/
def pushes (b : LeafBlock τ) : List τ := (List.range b.size).flatMap b.push

/-- Every pull tuple of a block, leaf by leaf. -/
def pulls (b : LeafBlock τ) : List τ := (List.range b.size).flatMap b.pull

/-- **A table's block**: `2^r` rows, the first `rows` of them executed with their tuples, the
others padding rows with none. -/
def ofRows (r rows : ℕ) (push pull : ℕ → List τ) : LeafBlock τ where
  r := r
  push k := if k < rows then push k else []
  pull k := if k < rows then pull k else []

/-- **A pair of boundary blocks**: `2^r` rows, row `k` pushing `push k` and pulling `pull k`
(the memory's seed and finalize tuples of cell `k`, or the bytecode's of instruction `k`). -/
def pair (r : ℕ) (push pull : ℕ → τ) : LeafBlock τ where
  r := r
  push k := [push k]
  pull k := [pull k]

/-- **An unused block**: `2^r` leaves with no tuple. -/
def unused (r : ℕ) : LeafBlock τ where
  r := r
  push _ := []
  pull _ := []

theorem flatMap_range_ite (m rows : ℕ) (h : rows ≤ m) (g : ℕ → List τ) :
    (List.range m).flatMap (fun k ↦ if k < rows then g k else []) =
      (List.range rows).flatMap g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  have h2 : (List.range d).flatMap (fun x ↦ if rows + x < rows then g (rows + x) else []) = [] :=
    List.flatMap_eq_nil_iff.mpr fun x _ ↦ by simp
  rw [h2, List.append_nil]
  exact List.flatMap_congr fun k hk ↦ by simp [List.mem_range.mp hk]

/-- A table's block pushes exactly its executed rows' tuples. -/
theorem pushes_ofRows {r rows : ℕ} (h : rows ≤ 2 ^ r) (push pull : ℕ → List τ) :
    (ofRows r rows push pull).pushes = (List.range rows).flatMap push :=
  flatMap_range_ite _ _ h push

/-- A table's block pulls exactly its executed rows' tuples. -/
theorem pulls_ofRows {r rows : ℕ} (h : rows ≤ 2 ^ r) (push pull : ℕ → List τ) :
    (ofRows r rows push pull).pulls = (List.range rows).flatMap pull :=
  flatMap_range_ite _ _ h pull

theorem pushes_pair (r : ℕ) (push pull : ℕ → τ) :
    (pair r push pull).pushes = (List.range (2 ^ r)).map push :=
  List.map_eq_flatMap.symm

theorem pulls_pair (r : ℕ) (push pull : ℕ → τ) :
    (pair r push pull).pulls = (List.range (2 ^ r)).map pull :=
  List.map_eq_flatMap.symm

theorem pushes_unused (r : ℕ) : (unused r : LeafBlock τ).pushes = [] := by
  simp [pushes, unused]

theorem pulls_unused (r : ℕ) : (unused r : LeafBlock τ).pulls = [] := by
  simp [pulls, unused]

end LeafBlock

variable {τ : Type*} {M : Type*} [CommMonoid M]

/-- The product of the fingerprints of a list of tuples. -/
def fpProd (fp : τ → M) (l : List τ) : M := (l.map fp).prod

theorem fpProd_append (fp : τ → M) (l₁ l₂ : List τ) :
    fpProd fp (l₁ ++ l₂) = fpProd fp l₁ * fpProd fp l₂ := by
  simp [fpProd]

theorem fpProd_flatMap_range (fp : τ → M) (g : ℕ → List τ) :
    ∀ m, fpProd fp ((List.range m).flatMap g) = ∏ k ∈ range m, fpProd fp (g k)
  | 0 => by simp [fpProd]
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, fpProd_append, fpProd_flatMap_range fp g m,
      prod_range_succ]
    simp [fpProd]

theorem fpProd_flatMap (fp : τ → M) {α : Type*} (g : α → List τ) :
    ∀ l : List α, fpProd fp (l.flatMap g) = (l.map fun a ↦ fpProd fp (g a)).prod
  | [] => by simp [fpProd]
  | a :: l => by rw [List.flatMap_cons, fpProd_append, fpProd_flatMap fp g l]; simp

theorem LeafBlock.fpProd_pushes (fp : τ → M) (b : LeafBlock τ) :
    fpProd fp b.pushes = ∏ k ∈ range b.size, fpProd fp (b.push k) :=
  fpProd_flatMap_range fp b.push _

theorem LeafBlock.fpProd_pulls (fp : τ → M) (b : LeafBlock τ) :
    fpProd fp b.pulls = ∏ k ∈ range b.size, fpProd fp (b.pull k) :=
  fpProd_flatMap_range fp b.pull _

/-- **A block's leaf identity** at offset `o`: leaf `k` at position `o + k`, `leaf · P = P'`. -/
def LeafBlock.Holds (fp : τ → M) (T : ℕ → M) (o : ℕ) (b : LeafBlock τ) : Prop :=
  ∀ k < b.size, T (o + k) * fpProd fp (b.pull k) = fpProd fp (b.push k)

/-- **A table block's leaf identity, row by row**: an executed row's leaf is its pushes over its
pulls, a padding row's leaf is `1` (`(R·P + P')·Z_pad + (R + 1)·Z_act = Q·w_r`,
`verifier.rs`, at commit `56ea040` of `leanvm-univariate`). -/
theorem LeafBlock.holds_ofRows_iff (fp : τ → M) (T : ℕ → M) (o r rows : ℕ)
    (push pull : ℕ → List τ) :
    (ofRows r rows push pull).Holds fp T o ↔
      (∀ k < 2 ^ r, k < rows → T (o + k) * fpProd fp (pull k) = fpProd fp (push k)) ∧
        (∀ k < 2 ^ r, rows ≤ k → T (o + k) = 1) := by
  constructor
  · intro h
    refine ⟨fun k hk hkr ↦ ?_, fun k hk hkr ↦ ?_⟩
    · have := h k hk
      simpa [ofRows, hkr] using this
    · have := h k hk
      simpa [ofRows, not_lt.mpr hkr, fpProd] using this
  · rintro ⟨h1, h2⟩ k hk
    by_cases hkr : k < rows
    · simpa [ofRows, hkr] using h1 k hk hkr
    · simpa [ofRows, hkr, fpProd] using h2 k hk (not_lt.mp hkr)

/-- **The padded leaf identity, row by row** (`verifier.rs` at `leanvm-univariate` `56ea040`):
where `(R·P + P')·Z_pad + (R + 1)·Z_act = 0` (the identity on `V_r`, where `Q·w_r` vanishes), an
executed row (`Z_act = 0 ≠ Z_pad`) has `R·P = P'` and a padding row (`Z_pad = 0 ≠ Z_act`) has
`R = 1`: the two clauses of `LeafBlock.holds_ofRows_iff`. -/
theorem leaf_of_padded {K : Type*} [Field K] [CharP K 2] {R P P' Zact Zpad : K}
    (h : (R * P + P') * Zpad + (R + 1) * Zact = 0) :
    (Zact = 0 → Zpad ≠ 0 → R * P = P') ∧ (Zpad = 0 → Zact ≠ 0 → R = 1) := by
  constructor
  · intro ha hp
    rw [ha, mul_zero, add_zero] at h
    exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hp)
  · intro hp ha
    rw [hp, mul_zero, zero_add] at h
    exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h).resolve_right ha)

/-- The leaves of the blocks laid end to end. -/
def total (bs : List (LeafBlock τ)) : ℕ := (bs.map LeafBlock.size).sum

/-- **Every block's leaf identity**, the blocks laid end to end from position `o`. -/
def LeavesHold (fp : τ → M) (T : ℕ → M) : ℕ → List (LeafBlock τ) → Prop
  | _, [] => True
  | o, b :: bs => b.Holds fp T o ∧ LeavesHold fp T (o + b.size) bs

/-- **The blocks are aligned** from position `o`: each block's first position is a multiple of
its size, so that a block of `2^r` leaves at position `a` is the coset `ω_a + V_r`
(`Heap.omega_add_of_dvd`), where the verifier reads it through the heap's restriction (SPEC §2,
"restriction to a coset"). -/
def AlignedFrom : ℕ → List (LeafBlock τ) → Prop
  | _, [] => True
  | o, b :: bs => 2 ^ b.r ∣ o ∧ AlignedFrom (o + b.size) bs

/-- **Largest first is aligned** (`heap.rs`, `HeapLayout::new`): blocks sorted by size, largest
first, from a position every block's size divides, are aligned. -/
theorem alignedFrom_of_sorted :
    ∀ (bs : List (LeafBlock τ)) (o : ℕ), bs.Pairwise (fun a b ↦ b.r ≤ a.r) →
      (∀ b ∈ bs, 2 ^ b.r ∣ o) → AlignedFrom o bs
  | [], _, _, _ => trivial
  | b :: bs, o, hs, hd => by
    rw [List.pairwise_cons] at hs
    refine ⟨hd b (List.mem_cons_self ..), alignedFrom_of_sorted bs _ hs.2 fun b' hb' ↦ ?_⟩
    exact dvd_add (hd b' (List.mem_cons_of_mem _ hb'))
      (Nat.pow_dvd_pow 2 (hs.1 b' hb'))

/-- Every push tuple of the blocks. -/
def allPush (bs : List (LeafBlock τ)) : List τ := bs.flatMap LeafBlock.pushes

/-- Every pull tuple of the blocks. -/
def allPull (bs : List (LeafBlock τ)) : List τ := bs.flatMap LeafBlock.pulls

/-- **The blocks' leaves, multiplied out**: the leaves `[o, o + total)` times every pull
fingerprint is every push fingerprint. -/
theorem prod_leaves_mul_blocks (fp : τ → M) (T : ℕ → M) :
    ∀ (bs : List (LeafBlock τ)) (o : ℕ), LeavesHold fp T o bs →
      (∏ i ∈ Ico o (o + total bs), T i) * fpProd fp (allPull bs) = fpProd fp (allPush bs)
  | [], o, _ => by simp [total, allPull, allPush, fpProd]
  | b :: bs, o, ⟨hb, hbs⟩ => by
    have ih := prod_leaves_mul_blocks fp T bs (o + b.size) hbs
    have htot : total (b :: bs) = b.size + total bs := by simp [total]
    rw [htot, ← add_assoc, ← prod_Ico_consecutive _ (Nat.le_add_right o b.size)
      (Nat.le_add_right _ _)]
    simp only [allPull, allPush, List.flatMap_cons] at ih ⊢
    rw [fpProd_append, fpProd_append, ← ih, LeafBlock.fpProd_pulls, LeafBlock.fpProd_pushes,
      prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
    have hblock := prod_leaves_mul (range b.size) (fun k ↦ T (o + k))
      (fun k ↦ fpProd fp (b.pull k)) (fun k ↦ fpProd fp (b.push k))
      (fun k hk ↦ hb k (mem_range.mp hk))
    rw [← hblock]
    ac_rfl

/-- **The heap holds**: the tree identity on positions, every block's leaf identity, the blocks
laid end to end from the first leaf `2^(n-1)`, and the root identity `T(1)·fp(init) = fp(fin)`
(SPEC §5.2: `init` the state boundary's push, `fin` its pull). -/
structure HeapHolds (n : ℕ) (bs : List (LeafBlock τ)) (init fin : τ) (fp : τ → M) (T : ℕ → M) :
    Prop where
  tree : TreeHolds n T
  leaves : LeavesHold fp T (2 ^ (n - 1)) bs
  root : T 1 * fp init = fp fin

/-- The heap's push tuples: the blocks', then the state boundary's push. -/
def heapPush (bs : List (LeafBlock τ)) (init : τ) : List τ := allPush bs ++ [init]

/-- The heap's pull tuples: the blocks', then the state boundary's pull. -/
def heapPull (bs : List (LeafBlock τ)) (fin : τ) : List τ := allPull bs ++ [fin]

/-- **The heap's products are equal.** If the blocks fill the `2^(n-1)` leaves and the heap
holds, the push fingerprints' product equals the pull fingerprints' product, the state boundary
included. No fingerprint need be nonzero. -/
theorem heap_prod_eq {n : ℕ} (hn : 1 ≤ n) {bs : List (LeafBlock τ)} (hbs : total bs = 2 ^ (n - 1))
    {init fin : τ} {fp : τ → M} {T : ℕ → M} (h : HeapHolds n bs init fin fp T) :
    fpProd fp (heapPush bs init) = fpProd fp (heapPull bs fin) := by
  have hleaves := prod_leaves_mul_blocks fp T bs _ h.leaves
  have hend : 2 ^ (n - 1) + total bs = 2 ^ n := by
    rw [hbs, ← two_mul, ← pow_succ', Nat.sub_add_cancel hn]
  rw [hend, ← root_eq_prod_leaves hn h.tree] at hleaves
  rw [heapPush, heapPull, fpProd_append, fpProd_append, ← hleaves]
  simp only [fpProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← h.root]
  ac_rfl

end Heap
