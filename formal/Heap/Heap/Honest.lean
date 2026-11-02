-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Heap.Bus

/-!
# The heap is not vacuous: the honest heap

Soundness bounds the challenges at which **some** heap holds (`HeapData.Sat`); this file checks
that the honest prover has one, so that the bound is not about an empty event. For any leaf values,
`heapOf` fills the internal nodes with the products of their children (`treeHolds_heapOf`); with
the leaves `leafOf`, each a row's push fingerprints over its pull fingerprints, every block's leaf
identity holds when no pull fingerprint vanishes (`leavesHold_leafOf`); and then the root identity
holds exactly when the products are equal, which a balanced bus gives (**`HeapData.sat_of_perm`**).

The honest prover's only failure is a challenge `β` at which a pull fingerprint vanishes: at most
one `β` per pull tuple for each `α`. That is completeness's concern, not this library's.
-/

namespace Heap

open Finset LeanVM.Parameters

variable {M : Type*} [CommMonoid M]

/-- **The heap of given leaves**: a leaf `2^(n-1) ≤ i < 2^n` holds `leaf i`, an internal node
`1 ≤ i < 2^(n-1)` the product of its children, every other position `1`. -/
def heapOf (n : ℕ) (leaf : ℕ → M) (i : ℕ) : M :=
  if i = 0 ∨ 2 ^ n ≤ i then 1
  else if 2 ^ (n - 1) ≤ i then leaf i
  else heapOf n leaf (2 * i) * heapOf n leaf (2 * i + 1)
termination_by 2 ^ n - i
decreasing_by all_goals omega

theorem heapOf_leaf {n : ℕ} (leaf : ℕ → M) {i : ℕ} (h1 : 2 ^ (n - 1) ≤ i) (h2 : i < 2 ^ n)
    (h0 : i ≠ 0) : heapOf n leaf i = leaf i := by
  rw [heapOf, ite_eq_right (by omega), ite_eq_left h1]

theorem heapOf_node {n : ℕ} (leaf : ℕ → M) {i : ℕ} (h0 : i ≠ 0) (h1 : i < 2 ^ (n - 1))
    (hn : 1 ≤ n) : heapOf n leaf i = heapOf n leaf (2 * i) * heapOf n leaf (2 * i + 1) := by
  have : 2 ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [heapOf, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The heap of given leaves meets the tree identity. -/
theorem treeHolds_heapOf {n : ℕ} (hn : 1 ≤ n) (leaf : ℕ → M) : TreeHolds n (heapOf n leaf) := by
  intro i hi2 hi
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
  have hp : i >>> 1 = i / 2 := Nat.shiftRight_one i
  rw [hp, heapOf_node leaf (by omega) (by omega) hn]
  rcases Nat.even_or_odd i with ⟨p, hp2⟩ | ⟨p, hp2⟩
  · have hi' : i = 2 * p := by omega
    subst hi'
    rw [two_mul_xor_one, show 2 * p / 2 = p by omega]
  · have hi' : i = 2 * p + 1 := by omega
    subst hi'
    have hx : (2 * p + 1) ^^^ 1 = 2 * p := by
      rw [← two_mul_xor_one, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hx, show (2 * p + 1) / 2 = p by omega, mul_comm]

variable {τ : Type*} {F : Type*} [Field F]

/-- **The honest leaves**: leaf `o + k` of a block at `o` is row `k`'s push fingerprints over its
pull fingerprints; past the blocks, `1`. -/
def leafOf (fp : τ → F) : ℕ → List (LeafBlock τ) → ℕ → F
  | _, [], _ => 1
  | o, b :: bs, i =>
    if o ≤ i ∧ i < o + b.size then fpProd fp (b.push (i - o)) / fpProd fp (b.pull (i - o))
    else leafOf fp (o + b.size) bs i

theorem fpProd_ne_zero (fp : τ → F) {l : List τ} (h : ∀ t ∈ l, fp t ≠ 0) : fpProd fp l ≠ 0 := by
  unfold fpProd
  refine List.prod_ne_zero fun h0 ↦ ?_
  obtain ⟨t, ht, h0⟩ := List.mem_map.mp h0
  exact h t ht h0

/-- **The honest leaves hold**: a heap agreeing with `leafOf` on the blocks' positions meets every
block's leaf identity, when no pull fingerprint vanishes. -/
theorem leavesHold_leafOf (fp : τ → F) (T : ℕ → F) :
    ∀ (bs : List (LeafBlock τ)) (o : ℕ), (∀ t ∈ allPull bs, fp t ≠ 0) →
      (∀ i, o ≤ i → i < o + total bs → T i = leafOf fp o bs i) → LeavesHold fp T o bs
  | [], _, _, _ => trivial
  | b :: bs, o, hnz, hT => by
    have htot : total (b :: bs) = b.size + total bs := by simp [total]
    refine ⟨fun k hk ↦ ?_, leavesHold_leafOf fp T bs (o + b.size) (fun t ht ↦ hnz t ?_)
      fun i hi1 hi2 ↦ ?_⟩
    · rw [hT (o + k) (by omega) (by omega), leafOf, ite_eq_left ⟨by omega, by omega⟩,
        Nat.add_sub_cancel_left]
      refine div_mul_cancel₀ _ (fpProd_ne_zero fp fun t ht ↦ hnz t ?_)
      simp only [allPull, List.flatMap_cons, List.mem_append]
      exact Or.inl (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ht⟩)
    · simp only [allPull, List.flatMap_cons, List.mem_append] at ht ⊢
      exact Or.inr ht
    · rw [hT i (by omega) (by omega), leafOf, ite_eq_right (by omega)]

/-- **The honest heap holds** at `(α, β)`: if the layout is well formed, its push and pull tuples
are permutations of each other, and no pull fingerprint of the blocks vanishes at `(α, β)`. -/
theorem HeapData.sat_of_perm (D : HeapData) (hD : D.WellFormed) (hp : D.pushes.Perm D.pulls)
    {α : Fin 4 → E} {β : E} (hnz : ∀ t ∈ allPull D.blocks, fp α β t ≠ 0) : D.Sat α β := by
  have hn := hD.depth
  have hpow : 2 ^ (D.n - 1) + total D.blocks = 2 ^ D.n := by
    rw [hD.fills, ← two_mul, ← pow_succ', Nat.sub_add_cancel hn]
  set leaf := leafOf (fp α β) (2 ^ (D.n - 1)) D.blocks
  refine ⟨heapOf D.n leaf, treeHolds_heapOf hn leaf, ?_, ?_⟩
  · refine leavesHold_leafOf (fp α β) _ D.blocks _ hnz fun i hi1 hi2 ↦ ?_
    exact heapOf_leaf leaf hi1 (by omega) (by have := Nat.one_le_two_pow (n := D.n - 1); omega)
  · -- The root is the leaves' product, the pushes' over the pulls'.
    have hleaves := prod_leaves_mul_blocks (fp α β) (heapOf D.n leaf) D.blocks _
      (leavesHold_leafOf (fp α β) _ D.blocks _ hnz fun i hi1 hi2 ↦
        heapOf_leaf leaf hi1 (by omega) (by have := Nat.one_le_two_pow (n := D.n - 1); omega))
    rw [hpow, ← root_eq_prod_leaves hn (treeHolds_heapOf hn leaf)] at hleaves
    have hprod := hp.map (fp α β) |>.prod_eq
    simp only [HeapData.pushes, HeapData.pulls, heapPush, heapPull, List.map_append,
      List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hprod
    have hP : fpProd (fp α β) (allPull D.blocks) ≠ 0 := fpProd_ne_zero _ hnz
    apply mul_right_cancel₀ hP
    rw [mul_right_comm, hleaves]
    unfold fpProd
    rw [hprod, mul_comm]

end Heap
