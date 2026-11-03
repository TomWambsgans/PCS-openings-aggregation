-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHEval

/-!
# The leaf quotients divide exactly and fit their chunks (milestone 4)

For an honest trace (`TraceHonest`) and bus challenges at which no fingerprint the heap divides by vanishes
(`¬ BadFp`), every used heap block's leaf numerator (`leafNumerator`, `R` the polynomial of the block's leaves on
`V_r`) vanishes on `V_r`, so `w_r` divides it, and its quotient fits the verifier's chunks `chunks (d + 1)`,
`d` the block's `Shape.leafDegree`:

* **the memory, the bytecode** (`memoryLeafNumerator_eval`, `bytecodeLeafNumerator_eval`): each leaf is
  `D_init / D_fin`, so `R D_fin + D_init` vanishes on `V_r` (`D_fin ≠ 0`: `¬ BadFp`); degree `≤ 2(n − 1)`, the
  quotient `≤ n − 2` (`natDegree_memoryLeafNumerator_le`, …);
* **a table** (`tableLeafNumerator_eval`): `(R P + P') Z_pad + (R + 1) Z_act`: on an active row `Z_act = 0` and
  `R = P'/P`; on a padding row `Z_pad = 0` and `R = 1`. Its degree is `≤ max(M(n − 1) + (n − rows), (n − 1) + rows)`,
  `M = max(pullDegree, pushDegree)`; under `RowsFit` (`leastRows r ≤ rows ≤ 2^r`) this is
  `≤ M(n − 1) + (n − leastRows r)` because every table has at least two flushes (`M ≥ 3`, so
  `leastRows r ≤ (M − 1)(n − 1)` at every height, `r = 0, 1, 2` included);
* `le_sum_chunks`: `chunks count` covers `count` coefficients (the loop's invariant).

Hence (**`leafNumerator_dvd`**, **`leafQuotient_fits`**) at every used block of every honest run with `RowsFit`:
**no honest run fails to fit** (the full table, `rows = 2^r`, and `rows = leastRows r` included).

The heights are at most `28` here (`tr.shape.heap.h ≤ 28`, the statement's transform; at a deployable shape
`C2`'s `2^28` words bound them lower).
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

theorem getD_ofFn_lt {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem getD_ofFn_ge {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) {i : ℕ} (hi : n ≤ i) :
    (Array.ofFn f).getD i d = d := by
  simp [Array.getD_eq_getD_getElem?, show ¬ i < n by omega]

/-! ### `chunks` covers its count -/

/-- `chunks`' loop body. -/
def chunksBody : ℕ → Array ℕ × ℕ → Id (ForInStep (Array ℕ × ℕ)) := fun _ s ↦
  if s.2 > 0 then
    if s.1.size = 2 ∧ s.2 ≠ 2 ^ s.2.log2 then pure (ForInStep.yield (s.1.push (s.2.log2 + 1), 0))
    else pure (ForInStep.yield (s.1.push s.2.log2, s.2 - 2 ^ s.2.log2))
  else pure (ForInStep.yield (s.1, s.2))

theorem chunks_eq (c : ℕ) :
    chunks c = (Id.run (forIn (List.range' 0 (Std.Legacy.Range.size [:4])) ((#[] : Array ℕ), c) chunksBody)).1.toList := by
  unfold chunks
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- `chunks`' invariant after `j` steps. -/
structure CInv (count j : ℕ) (s : Array ℕ × ℕ) : Prop where
  cover : count ≤ (s.1.toList.map (2 ^ ·)).sum + s.2
  size : s.2 = 0 ∨ s.1.size = j
  done : 3 ≤ j → s.2 = 0

theorem chunks_inv (count : ℕ) :
    ∀ (L : List ℕ) (j : ℕ) (s : Array ℕ × ℕ), CInv count j s →
      CInv count (j + L.length) (Id.run (forIn L s chunksBody))
  | [], j, s, h => h
  | x :: L, j, s, h => by
    unfold Id.run
    rw [List.forIn_cons, List.length_cons, show j + (L.length + 1) = (j + 1) + L.length by ring]
    by_cases h0 : s.2 > 0
    · have hsz : s.1.size = j := h.size.resolve_left (by omega)
      have hj : j < 3 := by by_contra hj; have := h.done (by omega); omega
      have hlog := Nat.log2_self_le (n := s.2) (by omega)
      by_cases hc : s.1.size = 2 ∧ s.2 ≠ 2 ^ s.2.log2
      · have hstep : chunksBody x s = pure (ForInStep.yield (s.1.push (s.2.log2 + 1), 0)) := by
          unfold chunksBody; rw [ite_pos_of h0, ite_pos_of hc]
        rw [hstep]
        refine chunks_inv count L (j + 1) _ ⟨?_, Or.inl rfl, fun _ ↦ rfl⟩
        have hlt := Nat.lt_log2_self (n := s.2)
        have := h.cover
        simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil]
        omega
      · have hstep : chunksBody x s = pure (ForInStep.yield (s.1.push s.2.log2, s.2 - 2 ^ s.2.log2)) := by
          unfold chunksBody; rw [ite_pos_of h0, ite_neg_of hc]
        rw [hstep]
        refine chunks_inv count L (j + 1) _ ⟨?_, Or.inr (by rw [Array.size_push, hsz]), fun h3 ↦ ?_⟩
        · have := h.cover
          simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.sum_append,
            List.sum_cons, List.sum_nil]
          omega
        · have hj2 : j = 2 := by omega
          have : s.2 = 2 ^ s.2.log2 := by
            by_contra hne; exact hc ⟨by omega, hne⟩
          show s.2 - 2 ^ s.2.log2 = 0
          omega
    · have hstep : chunksBody x s = pure (ForInStep.yield (s.1, s.2)) := by
        unfold chunksBody; rw [ite_neg_of h0]
      rw [hstep]
      exact chunks_inv count L (j + 1) _ ⟨h.cover, Or.inl (by omega), fun _ ↦ by omega⟩

/-- **`chunks count` covers `count` coefficients.** -/
theorem le_sum_chunks (count : ℕ) : count ≤ ((chunks count).map (2 ^ ·)).sum := by
  have h := chunks_inv count (List.range' 0 (Std.Legacy.Range.size [:4])) 0 ((#[] : Array ℕ), count)
    ⟨by simp, Or.inr rfl, fun h ↦ absurd h (by omega)⟩
  have hlen : (List.range' 0 (Std.Legacy.Range.size [:4])).length = 4 := by rw [List.length_range']; rfl
  rw [hlen] at h
  have := h.cover
  rw [h.done (by omega), Nat.add_zero] at this
  rw [chunks_eq]
  exact this

/-- **A quotient fits its chunks** when its degree is at most `d`: `deg < Σ 2^e`, `e ∈ chunks (d + 1)`. -/
theorem fits_of_le {q : E[X]} {d : ℕ} (h : q.natDegree ≤ d) : q.natDegree < ((chunks (d + 1)).map (2 ^ ·)).sum :=
  lt_of_lt_of_le (Nat.lt_succ_of_le h) (le_sum_chunks (d + 1))

/-- The quotient by `w_r` of a numerator of degree `≤ D` has degree `≤ D − 2^r`. -/
theorem natDegree_divM_le {N : Poly} {r D : ℕ} (h : (tp N).natDegree ≤ D) :
    (tp (divM N (wPoly r))).natDegree ≤ D - 2 ^ r := by
  rw [tp_divM _ _ (by rw [tp_wPoly]; exact wP_monic r), tp_wPoly, natDegree_divByMonic _ (wP_monic r),
    wP_natDegree]
  omega

/-- **An exact quotient**: `N = w_r · (N /ₘ w_r)` when `N` vanishes on `V_r`. -/
theorem eq_mul_divM {N : Poly} {r : ℕ} (hr : r ≤ 32) (h : ∀ i < 2 ^ r, (tp N).eval (pointE i) = 0) :
    tp N = wP r * tp (divM N (wPoly r)) := by
  rw [tp_divM _ _ (by rw [tp_wPoly]; exact wP_monic r), tp_wPoly]
  exact eq_mul_divByMonic_of_dvd (wP_monic r) (wP_dvd_of_eval hr h)

/-! ### The memory's leaves -/

section Honest

variable {tr : Trace} (hon : TraceHonest tr) {alphas : List E} {beta : E} (hbad : ¬ BadFp tr alphas beta)
include hon

/-- A memory cell's pull fingerprint `D_fin`. -/
def memFin (tr : Trace) (weights : Array E) (beta : E) (i : ℕ) : E :=
  memoryFp weights beta (ofK (LeanVM.Parameters.gpow i)) (ofK ((tr.memory.getD 3 #[]).getD i 0))
    ((List.range 3).map fun k ↦ ofK ((tr.memory.getD k #[]).getD i 0))

/-- A memory cell's push fingerprint `D_init`. -/
def memInit (tr : Trace) (weights : Array E) (beta : E) (i : ℕ) : E :=
  memoryFp weights beta (ofK (LeanVM.Parameters.gpow i)) 1
    ((List.range 3).map fun k ↦ ofK ((tr.memory.getD k #[]).getD i 0))

omit hon in
theorem memoryLeaves_getD (weights : Array E) (beta : E) {i : ℕ} (hi : i < 2 ^ tr.shape.logMemory) :
    (memoryLeaves tr weights beta).getD i 0 = memInit tr weights beta i * (memFin tr weights beta i)⁻¹ := by
  unfold memoryLeaves
  rw [getD_ofFn_lt _ _ hi]
  rfl

omit hon in
theorem memoryLeaves_size (weights : Array E) (beta : E) :
    (memoryLeaves tr weights beta).size = 2 ^ tr.shape.logMemory := Array.size_ofFn

omit hon in
include hbad in
theorem memFin_ne_zero {i : ℕ} (hi : i < 2 ^ tr.shape.logMemory) : memFin tr (eqKernel alphas) beta i ≠ 0 := by
  intro h0
  apply hbad
  refine ⟨memoryTuple tr i (ofK ((tr.memory.getD 3 #[]).getD i 0)), ?_, ?_⟩
  · unfold dividedTuples
    refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  · rw [← memoryFp_eq_fpOf]; exact h0

theorem ev_memory_col (h28 : tr.shape.logMemory ≤ 28) {k i : ℕ} (hk : k < 4) (hi : i < 2 ^ tr.shape.logMemory) :
    ev (pointE i) (colPolyK tr.shape.logMemory (tr.memory.getD k #[])) = ofK ((tr.memory.getD k #[]).getD i 0) := by
  rw [ev_apply, eval_colPolyK h28 (hon.memorySize.2 k hk) hi]

omit hon in
theorem ev_address (h28 : tr.shape.logMemory ≤ 28) {i : ℕ} (hi : i < 2 ^ tr.shape.logMemory) :
    ev (pointE i) (colPolyK tr.shape.logMemory (addressColumn tr.shape.logMemory)) =
      ofK (LeanVM.Parameters.gpow i) := by
  rw [ev_apply, eval_colPolyK h28 (by rw [addressColumn, Array.size_ofFn]) hi, addressColumn, getD_ofFn_lt _ _ hi]

theorem ev_limbs (h28 : tr.shape.logMemory ≤ 28) {i : ℕ} (hi : i < 2 ^ tr.shape.logMemory) :
    ((List.range 3).map fun k ↦ colPolyK tr.shape.logMemory (tr.memory.getD k #[])).map (ev (pointE i)) =
      (List.range 3).map fun k ↦ ofK ((tr.memory.getD k #[]).getD i 0) := by
  rw [List.map_map]
  refine List.map_congr_left fun k hk ↦ ?_
  exact ev_memory_col hon h28 (by have := List.mem_range.mp hk; omega) hi

include hbad in
/-- **The memory's leaf numerator vanishes on `V_lm`.** -/
theorem memoryLeafNumerator_eval (h28 : tr.shape.logMemory ≤ 28) {i : ℕ} (hi : i < 2 ^ tr.shape.logMemory) :
    (tp (memoryLeafNumerator tr (eqKernel alphas) beta (ofNovel tr.shape.logMemory
      (novelOfValuesE tr.shape.logMemory (memoryLeaves tr (eqKernel alphas) beta))))).eval (pointE i) = 0 := by
  rw [← ev_apply]
  unfold memoryLeafNumerator
  simp only [map_add, map_mul, ev_memoryFpP, map_one]
  rw [ev_apply (pointE i) (ofNovel _ _), eval_ofNovel_novelOfValuesE h28 (memoryLeaves_size _ _) hi,
    memoryLeaves_getD _ _ hi, ev_address h28 hi, ev_memory_col hon h28 (by norm_num) hi, ev_limbs hon h28 hi]
  have hne := memFin_ne_zero hbad hi
  unfold memFin at hne
  unfold memInit memFin
  rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, CharTwo.add_self_eq_zero]

omit hon in
theorem natDegree_memoryFpP_le (weights : Array E) (beta : E) (address count : Poly) (limbs : List Poly) (n : ℕ)
    (ha : (tp address).natDegree ≤ n) (hc : (tp count).natDegree ≤ n) (hl : ∀ p ∈ limbs, (tp p).natDegree ≤ n) :
    (tp (memoryFpP weights beta address count limbs)).natDegree ≤ n := by
  unfold memoryFpP
  refine natDegree_foldl_add_le (fun k ↦ pC (weights.getD (3 + k) 0) * limbs.getD k 0) n _ (fun k _ ↦ ?_) _ ?_
  · rw [tp_mul, tp_C]
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [List.getD_eq_getElem?_getD]
    rcases h : limbs[k]? with _ | p
    · rw [Option.getD_none, tp_zero, natDegree_zero]; exact Nat.zero_le _
    · rw [Option.getD_some]; exact hl p (List.mem_of_getElem? h)
  · rw [tp_add, tp_add, tp_mul, tp_mul, tp_C, tp_C, tp_C]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · rw [natDegree_C]; exact Nat.zero_le _
    · exact (natDegree_C_mul_le _ _).trans ha
    · exact (natDegree_C_mul_le _ _).trans hc

omit hon in
/-- The memory's leaf numerator has degree `≤ 2 (2^lm − 1)`. -/
theorem natDegree_memoryLeafNumerator_le (weights : Array E) (beta : E) (rPoly : Poly)
    (hR : (tp rPoly).natDegree ≤ 2 ^ tr.shape.logMemory - 1) :
    (tp (memoryLeafNumerator tr weights beta rPoly)).natDegree ≤ 2 * (2 ^ tr.shape.logMemory - 1) := by
  unfold memoryLeafNumerator
  dsimp only
  set n := 2 ^ tr.shape.logMemory - 1
  have hcol : ∀ v : Array K, (tp (colPolyK tr.shape.logMemory v)).natDegree ≤ n := fun v ↦ by
    have := natDegree_colPolyK_lt tr.shape.logMemory v; omega
  have hl : ∀ p ∈ (List.range 3).map (fun k ↦ colPolyK tr.shape.logMemory (tr.memory.getD k #[])),
      (tp p).natDegree ≤ n := by
    intro p hp
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
    exact hcol _
  have h1 := natDegree_memoryFpP_le weights beta (colPolyK tr.shape.logMemory (addressColumn tr.shape.logMemory))
    (colPolyK tr.shape.logMemory (tr.memory.getD 3 #[])) _ n (hcol _) (hcol _) hl
  have h2 := natDegree_memoryFpP_le weights beta (colPolyK tr.shape.logMemory (addressColumn tr.shape.logMemory))
    1 _ n (hcol _) (by rw [tp_one, natDegree_one]; exact Nat.zero_le _) hl
  rw [tp_add, tp_mul]
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_mul_le).trans (by omega)) (by omega))

/-! ### The bytecode's leaves -/

/-- An instruction's pull fingerprint. -/
def bcFin (tr : Trace) (weights : Array E) (beta : E) (i : ℕ) : E :=
  bytecodeFp weights beta fun s ↦ bytecodeSlot tr i s (ofK (tr.bytecodeFinal.getD i 0))

/-- An instruction's push fingerprint. -/
def bcInit (tr : Trace) (weights : Array E) (beta : E) (i : ℕ) : E :=
  bytecodeFp weights beta fun s ↦ bytecodeSlot tr i s 1

omit hon in
theorem bytecodeLeaves_getD (weights : Array E) (beta : E) {i : ℕ} (hi : i < 2 ^ tr.shape.logBytecode) :
    (bytecodeLeaves tr weights beta).getD i 0 = bcInit tr weights beta i * (bcFin tr weights beta i)⁻¹ := by
  unfold bytecodeLeaves
  rw [getD_ofFn_lt _ _ hi]
  rfl

omit hon in
theorem bytecodeLeaves_size (weights : Array E) (beta : E) :
    (bytecodeLeaves tr weights beta).size = 2 ^ tr.shape.logBytecode := Array.size_ofFn

omit hon in
include hbad in
theorem bcFin_ne_zero {i : ℕ} (hi : i < 2 ^ tr.shape.logBytecode) : bcFin tr (eqKernel alphas) beta i ≠ 0 := by
  intro h0
  apply hbad
  refine ⟨bytecodeTuple tr i (ofK (tr.bytecodeFinal.getD i 0)), ?_, ?_⟩
  · unfold dividedTuples
    exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · rw [← bytecodeFp_eq_fpOf]; exact h0

omit hon in
theorem bytecodeFp_congr (weights : Array E) (beta : E) {f g : ℕ → E} (h : ∀ s < 16, f s = g s) :
    bytecodeFp weights beta f = bytecodeFp weights beta g := by
  unfold bytecodeFp
  rw [foldl_add_eq, foldl_add_eq, List.map_congr_left fun s hs ↦ by rw [h s (List.mem_range.mp hs)]]

/-- The bytecode's slot polynomials (`bytecodeLeafNumerator`'s `slot`). -/
def bcSlotP (tr : Trace) (c : Poly) (s : ℕ) : Poly :=
  if s = 2 then c else (Array.ofFn (n := 16) fun s ↦ colPolyK tr.shape.logBytecode (tr.slots.getD s.val #[])).getD s 0

theorem ev_bcSlotP (h28 : tr.shape.logBytecode ≤ 28) {i : ℕ} (hi : i < 2 ^ tr.shape.logBytecode) (c : Poly)
    {s : ℕ} (hs : s < 16) : ev (pointE i) (bcSlotP tr c s) = bytecodeSlot tr i s (ev (pointE i) c) := by
  unfold bcSlotP bytecodeSlot
  by_cases h2 : s = 2
  · rw [ite_pos_of h2, ite_pos_of h2]
  · rw [ite_neg_of h2, ite_neg_of h2, getD_ofFn_lt _ _ hs, ev_apply, eval_colPolyK h28 (hon.slotsSize.2 s hs) hi]

include hbad in
/-- **The bytecode's leaf numerator vanishes on `V_lb`.** -/
theorem bytecodeLeafNumerator_eval (h28 : tr.shape.logBytecode ≤ 28) {i : ℕ} (hi : i < 2 ^ tr.shape.logBytecode) :
    (tp (bytecodeLeafNumerator tr (eqKernel alphas) beta (ofNovel tr.shape.logBytecode
      (novelOfValuesE tr.shape.logBytecode (bytecodeLeaves tr (eqKernel alphas) beta))))).eval (pointE i) = 0 := by
  rw [← ev_apply]
  unfold bytecodeLeafNumerator
  dsimp only
  simp only [map_add, map_mul, ev_bytecodeFpP]
  have e1 : (bytecodeFp (eqKernel alphas) beta fun s ↦ ev (pointE i) (bcSlotP tr
      (colPolyK tr.shape.logBytecode tr.bytecodeFinal) s)) = bcFin tr (eqKernel alphas) beta i := by
    refine bytecodeFp_congr _ _ fun s hs ↦ ?_
    rw [ev_bcSlotP hon h28 hi _ hs, ev_apply, eval_colPolyK h28 hon.bytecodeSize hi]
  have e2 : (bytecodeFp (eqKernel alphas) beta fun s ↦ ev (pointE i) (bcSlotP tr 1 s)) =
      bcInit tr (eqKernel alphas) beta i := by
    refine bytecodeFp_congr _ _ fun s hs ↦ ?_
    rw [ev_bcSlotP hon h28 hi _ hs, map_one]
  unfold bcSlotP at e1 e2
  rw [e1, e2, ev_apply (pointE i) (ofNovel _ _), eval_ofNovel_novelOfValuesE h28 (bytecodeLeaves_size _ _) hi,
    bytecodeLeaves_getD _ _ hi, mul_assoc, inv_mul_cancel₀ (bcFin_ne_zero hbad hi), mul_one,
    CharTwo.add_self_eq_zero]

omit hon in
theorem natDegree_bytecodeFpP_le (weights : Array E) (beta : E) (slot : ℕ → Poly) (n : ℕ)
    (hs : ∀ s, (tp (slot s)).natDegree ≤ n) : (tp (bytecodeFpP weights beta slot)).natDegree ≤ n := by
  unfold bytecodeFpP
  refine natDegree_foldl_add_le (fun s ↦ pC (weights.getD s 0) * slot s) n _ (fun s _ ↦ ?_) _ ?_
  · rw [tp_mul, tp_C]; exact (natDegree_C_mul_le _ _).trans (hs s)
  · rw [tp_C, natDegree_C]; exact Nat.zero_le _

omit hon in
/-- The bytecode's leaf numerator has degree `≤ 2 (2^lb − 1)`. -/
theorem natDegree_bytecodeLeafNumerator_le (weights : Array E) (beta : E) (rPoly : Poly)
    (hR : (tp rPoly).natDegree ≤ 2 ^ tr.shape.logBytecode - 1) :
    (tp (bytecodeLeafNumerator tr weights beta rPoly)).natDegree ≤ 2 * (2 ^ tr.shape.logBytecode - 1) := by
  unfold bytecodeLeafNumerator
  dsimp only
  set n := 2 ^ tr.shape.logBytecode - 1
  have hcol : ∀ v : Array K, (tp (colPolyK tr.shape.logBytecode v)).natDegree ≤ n := fun v ↦ by
    have := natDegree_colPolyK_lt tr.shape.logBytecode v; omega
  have hslot : ∀ c : Poly, (tp c).natDegree ≤ n → ∀ s, (tp (if s = 2 then c else
      (Array.ofFn (n := 16) fun s ↦ colPolyK tr.shape.logBytecode (tr.slots.getD s.val #[])).getD s 0)).natDegree ≤ n := by
    intro c hc s
    split_ifs
    · exact hc
    · by_cases hs : s < 16
      · rw [getD_ofFn_lt _ _ hs]; exact hcol _
      · rw [getD_ofFn_ge _ _ (by omega), tp_zero, natDegree_zero]; exact Nat.zero_le _
  have h1 := natDegree_bytecodeFpP_le weights beta _ n (hslot _ (hcol tr.bytecodeFinal))
  have h2 := natDegree_bytecodeFpP_le weights beta _ n (hslot 1 (by rw [tp_one, natDegree_one]; exact Nat.zero_le _))
  rw [tp_add, tp_mul]
  exact (natDegree_add_le _ _).trans (max_le ((natDegree_mul_le).trans (by omega)) (by omega))

end Honest

end UniComplete.AlgH
