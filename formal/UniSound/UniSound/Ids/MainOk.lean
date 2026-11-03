-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Leaves

/-!
# `MainOfPolysP`: the identities as polynomials give the heap and the constraint vectors

`mainOfPolys`: where every polynomial of `polysOf` is zero (so the counts are in range: out of range the
list is the constant `1`), the heap read off `C1` holds at `(α, β)` with `T` the committed heap at the
points (`heapT`: the tree `tree_of_treeP`, every block's leaves laid end to end at the heap's positions
`leavesHold_of`, the root `root_of_rootP`), and the constraint vectors vanish on `V_{r_W}`
(`cvec_of_wP`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

/-- Blocks laid end to end, each holding at its position, hold. -/
theorem leavesHold_of {τ M : Type} [CommMonoid M] (fp : τ → M) (T : ℕ → M) :
    ∀ (bs : List (Heap.LeafBlock τ)) (o : ℕ) (pos : ℕ → ℕ),
      (∀ i < bs.length, pos i = o + ((bs.take i).map Heap.LeafBlock.size).sum) →
      (∀ i (h : i < bs.length), (bs[i]).Holds fp T (pos i)) → Heap.LeavesHold fp T o bs
  | [], _, _, _, _ => trivial
  | b :: bs, o, pos, hp, hh => by
    refine ⟨?_, leavesHold_of fp T bs (o + b.size) (fun i ↦ pos (i + 1)) (fun i hi ↦ ?_) (fun i hi ↦ ?_)⟩
    · have h0 := hh 0 (by simp)
      rw [hp 0 (by simp)] at h0
      simpa using h0
    · rw [hp (i + 1) (by simp; omega)]
      simp [List.take_succ_cons, add_assoc]
    · exact hh (i + 1) (by simp; omega)

theorem sum_take_succ_le (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (l.take i).sum + l[i] ≤ l.sum := by
  have h1 : (l.take (i + 1)).sum = (l.take i).sum + l[i] := by
    rw [List.take_add_one, List.sum_append]
    simp [List.getElem?_eq_getElem hi]
  rw [← h1]
  exact List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ ↦ Nat.zero_le _)

theorem mem_zip_range {α : Type} (l : List α) (i : ℕ) (hi : i < l.length) :
    (l[i], i) ∈ l.zip (List.range l.length) := by
  have hz : i < (l.zip (List.range l.length)).length := by simp [hi]
  have := List.getElem_mem hz
  rwa [List.getElem_zip, List.getElem_range] at this

/-- **The identities as polynomials give the heap and the constraint vectors.** -/
theorem mainOfPolys (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (hr : HeapReading D) :
    MainOfPolysP D Fl := by
  intro s c1 ch fd c2 hP
  by_cases hfit : CountsFit D.shape s.2
  swap
  · exfalso
    exact one_ne_zero (hP 1 (by unfold polysOf; rw [ite_eq_right hfit]; exact List.mem_singleton_self _))
  have hpol : polysOf D Fl s c1 ch fd c2 =
      [treeP D.shape c2, rootP D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch),
        wP D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0)] ++
      (D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)).map fun bi ↦
        blockP D.shape c1 c2 (stackFor D c1 c2 .setup) s.2 (alphasOf ch) (betaOf ch) bi.1 bi.2 := by
    unfold polysOf; rw [ite_eq_left hfit]
  have htree : treeP D.shape c2 = 0 := hP _ (by rw [hpol]; simp)
  have hroot : rootP D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch) = 0 := hP _ (by rw [hpol]; simp)
  have hW : wP D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0) = 0 :=
    hP _ (by rw [hpol]; simp)
  have hblk : ∀ i (hi : i < D.shape.heap.blocks.length),
      blockP D.shape c1 c2 (stackFor D c1 c2 .setup) s.2 (alphasOf ch) (betaOf ch)
        D.shape.heap.blocks[i] i = 0 := fun i hi ↦
    hP _ (by
      rw [hpol]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, mem_zip_range _ i hi, rfl⟩))
  have hg := hr.heap
  refine ⟨⟨heapT D.shape c2, ⟨tree_of_treeP D.shape c2 hr.c1.beta hg.1 hg.2.1 htree, ?_, ?_⟩⟩,
    cvec_of_wP D hr.c1 hr.hB2 c1 c2 s (gammaOf ch) _ hfit hW⟩
  · -- the leaves
    show Heap.LeavesHold _ _ (2 ^ (D.shape.heap.h - 1)) (D.shape.heap.blocks.map (blockK D c1 s.2))
    refine leavesHold_of _ _ _ _ (fun i ↦ (D.shape.heap.blocks.getD i default).position) (fun i hi ↦ ?_)
      (fun i hi ↦ ?_)
    · rw [List.length_map] at hi
      rw [hg.2.2.2.1 i hi, ← List.map_take, List.map_map]
      congr 2
      refine List.map_congr_left fun b _ ↦ ?_
      simp [Heap.LeafBlock.size, blockK_r]
    · rw [List.length_map] at hi
      rw [List.getElem_map, List.getD_eq_getElem _ _ hi]
      have hb : D.shape.heap.blocks[i] ∈ D.shape.heap.blocks := List.getElem_mem hi
      have h1 := hg.2.2.2.1 i hi
      rw [List.getD_eq_getElem _ _ hi] at h1
      have h2 := sum_take_succ_le (D.shape.heap.blocks.map fun b ↦ 2 ^ b.r) i (by simpa using hi)
      rw [← List.map_take, List.getElem_map, hg.2.2.1] at h2
      have h3 : 2 ^ (D.shape.heap.h - 1) + 2 ^ (D.shape.heap.h - 1) ≤ 2 ^ 24 := by
        rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hg.1]
        exact Nat.pow_le_pow_right (by norm_num) hg.2.1
      have hP := hblk i hi
      generalize D.shape.heap.blocks[i] = b at hb h1 h2 hP ⊢
      have hal := hg.2.2.2.2.1 b hb
      have hpos : b.position + 2 ^ b.r ≤ 2 ^ 24 := by rw [h1]; omega
      have hkind := hg.2.2.2.2.2 b hb
      rcases hlv : b.leaves with _ | _ | t | _
      · rw [hlv] at hkind
        exact memHolds D hr c1 c2 s ch b i hlv hkind hal hpos hP
      · rw [hlv] at hkind
        have hlb : D.shape.logBytecode ≤ 24 := by
          have : 2 ^ b.r ≤ 2 ^ 24 := by omega
          rw [← hkind]
          exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
        exact bcHolds D hr c1 c2 s ch b i hlv hkind hal hpos hlb hP
      · rw [hlv] at hkind
        exact tableHolds D hr c1 c2 s ch b i hfit t hlv hkind.1 hkind.2 hal hpos hP
      · exact unusedHolds D hr c1 c2 s ch b i hlv hal hpos hP
  · -- the root
    show heapT D.shape c2 1 * Heap.fp _ _ initK = Heap.fp _ _ (finK D)
    rw [fp_initK hr.eqk, fp_finK hr.eqk hr.gpowK D]
    exact root_of_rootP D.shape c2 hr.c1.beta _ _ hroot

end UniSound.Ids
