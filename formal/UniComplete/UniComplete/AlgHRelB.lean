-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHRel

/-!
# The blocks' values at `t` (milestone 4)

The memory's, the bytecode's and a table's fingerprints the verifier computes at `t` from the values sent are the
prover's polynomials at `t` (`atMemoryPull_eq`, `atMemoryPush_eq`, `atBytecodePull_eq`, `atBytecodePush_eq`,
`part_pull_eq`, `part_push_eq`), and a table's `Z_act(t)` read from its count's bits is `Z_act` at `t`
(`atActive_getD`). Every chunk of a leaf quotient is read inside the digits `w` (`leafChunk_lt`: its size is at most
`log₂ (d + 1) < r + 5`, since every tuple has degree at most `2` and at most `15` flushes, `tables_bounds`).
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

/-! ### The memory and the bytecode at `t` -/

theorem memoryFp_count (weights : Array E) (beta a c : E) (l : List E) :
    memoryFp weights beta a 1 l = memoryFp weights beta a c l + weights.getD 2 0 * (1 + c) := by
  unfold memoryFp
  rw [foldl_add_eq, foldl_add_eq]
  linear_combination (-(weights.getD 2 0 * c)) * Domain.two_eq_zero_E

theorem bytecodeFp_count (weights : Array E) (beta : E) (f : ℕ → E) (c : E) :
    bytecodeFp weights beta (fun s ↦ if s = 2 then 1 else f s) =
      bytecodeFp weights beta (fun s ↦ if s = 2 then c else f s) + weights.getD 2 0 * (1 + c) := by
  unfold bytecodeFp
  rw [foldl_add_eq, foldl_add_eq, range16]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [show (0 : ℕ) ≠ 2 by decide, show (1 : ℕ) ≠ 2 by decide, show (3 : ℕ) ≠ 2 by decide,
    show (4 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 2 by decide,
    show (8 : ℕ) ≠ 2 by decide, show (9 : ℕ) ≠ 2 by decide, show (10 : ℕ) ≠ 2 by decide,
    show (11 : ℕ) ≠ 2 by decide, show (12 : ℕ) ≠ 2 by decide, show (13 : ℕ) ≠ 2 by decide,
    show (14 : ℕ) ≠ 2 by decide, show (15 : ℕ) ≠ 2 by decide, ↓reduceIte]
  linear_combination (-(weights.getD 2 0 * c)) * Domain.two_eq_zero_E

section Honest

variable {tr : Trace} (hon : TraceHonest tr) {alphas : List E} {beta gamma : E}
include hon

theorem atMem_eq {k : ℕ} (hk : k < 4) (t : E) {n : ℕ} (hn : tr.shape.logMemory ≤ n) :
    AlgC.atMem tr (digits t n) k = ev t (colPolyK tr.shape.logMemory (tr.memory.getD k #[])) := by
  rw [ev_eq_pEval]
  exact AlgC.evalB_bCoefficients _ n _ (hon.memorySize.2 k hk) hn t

omit hon in
theorem atAddress_eq (t : E) {n : ℕ} (hn : tr.shape.logMemory ≤ n) :
    AlgC.atAddress tr (digits t n) = ev t (colPolyK tr.shape.logMemory (addressColumn tr.shape.logMemory)) := by
  rw [ev_eq_pEval]
  exact AlgC.evalB_bCoefficients _ n _ (by rw [addressColumn, Array.size_ofFn]) hn t

theorem atMemoryPull_eq (weights : Array E) (beta t : E) {n : ℕ} (hn : tr.shape.logMemory ≤ n) :
    AlgC.atMemoryPull tr weights beta (digits t n) =
      ev t (memoryFpP weights beta (colPolyK tr.shape.logMemory (addressColumn tr.shape.logMemory))
        (colPolyK tr.shape.logMemory (tr.memory.getD 3 #[]))
        ((List.range 3).map fun k ↦ colPolyK tr.shape.logMemory (tr.memory.getD k #[]))) := by
  rw [ev_memoryFpP, AlgC.atMemoryPull, atAddress_eq t hn, atMem_eq hon (by norm_num) t hn, List.map_map]
  congr 1
  refine List.map_congr_left fun k hk ↦ ?_
  exact atMem_eq hon (by have := List.mem_range.mp hk; omega) t hn

theorem atMemoryPush_eq (weights : Array E) (beta t : E) {n : ℕ} (hn : tr.shape.logMemory ≤ n) :
    AlgC.atMemoryPush tr weights beta (digits t n) =
      ev t (memoryFpP weights beta (colPolyK tr.shape.logMemory (addressColumn tr.shape.logMemory)) 1
        ((List.range 3).map fun k ↦ colPolyK tr.shape.logMemory (tr.memory.getD k #[]))) := by
  rw [AlgC.atMemoryPush, atMemoryPull_eq hon weights beta t hn, ev_memoryFpP, ev_memoryFpP, map_one,
    memoryFp_count _ _ _ (ev t (colPolyK tr.shape.logMemory (tr.memory.getD 3 #[]))),
    atMem_eq hon (by norm_num) t hn]

theorem atBytecodeFinal_eq (t : E) {n : ℕ} (hn : tr.shape.logBytecode ≤ n) :
    AlgC.atBytecodeFinal tr (digits t n) = ev t (colPolyK tr.shape.logBytecode tr.bytecodeFinal) := by
  rw [ev_eq_pEval]
  exact AlgC.evalB_bCoefficients _ n _ hon.bytecodeSize hn t

theorem atSlot_eq {s : ℕ} (hs : s < 16) (t : E) {n : ℕ} (hn : tr.shape.logBytecode ≤ n) :
    AlgC.atSlot tr (digits t n) s = ev t (colPolyK tr.shape.logBytecode (tr.slots.getD s #[])) := by
  rw [ev_eq_pEval]
  exact AlgC.evalB_bCoefficients _ n _ (hon.slotsSize.2 s hs) hn t

theorem ev_bcSlotP_t (t : E) {n : ℕ} (hn : tr.shape.logBytecode ≤ n) (c : Poly) {s : ℕ} (hs : s < 16) :
    ev t (bcSlotP tr c s) = if s = 2 then ev t c else AlgC.atSlot tr (digits t n) s := by
  unfold bcSlotP
  by_cases h2 : s = 2
  · rw [ite_pos_of h2, ite_pos_of h2]
  · rw [ite_neg_of h2, ite_neg_of h2, getD_ofFn_lt _ _ hs, atSlot_eq hon hs t hn]

theorem atBytecodePull_eq (weights : Array E) (beta t : E) {n : ℕ} (hn : tr.shape.logBytecode ≤ n) :
    AlgC.atBytecodePull tr weights beta (digits t n) =
      ev t (bytecodeFpP weights beta (bcSlotP tr (colPolyK tr.shape.logBytecode tr.bytecodeFinal))) := by
  rw [ev_bytecodeFpP, AlgC.atBytecodePull]
  refine bytecodeFp_congr _ _ fun s hs ↦ ?_
  rw [ev_bcSlotP_t hon t hn _ hs, atBytecodeFinal_eq hon t hn]

theorem atBytecodePush_eq (weights : Array E) (beta t : E) {n : ℕ} (hn : tr.shape.logBytecode ≤ n) :
    AlgC.atBytecodePush tr weights beta (digits t n) =
      ev t (bytecodeFpP weights beta (bcSlotP tr 1)) := by
  rw [AlgC.atBytecodePush, AlgC.atBytecodePull, ev_bytecodeFpP]
  have e1 : (bytecodeFp weights beta fun s ↦ ev t (bcSlotP tr 1 s)) =
      bytecodeFp weights beta (fun s ↦ if s = 2 then 1 else AlgC.atSlot tr (digits t n) s) := by
    refine bytecodeFp_congr _ _ fun s hs ↦ ?_
    rw [ev_bcSlotP_t hon t hn _ hs, map_one]
  rw [e1, bytecodeFp_count _ _ _ (AlgC.atBytecodeFinal tr (digits t n))]


/-! ### A table at `t` -/

omit hon in
theorem tables_getD_mem {t : ℕ} (ht : t < 6) : tables.getD t default ∈ tables := by
  rw [List.getD_eq_getElem _ _ (by rw [tables_length]; exact ht)]
  exact List.getElem_mem _

omit hon in
theorem foldl_zip_fst (pulls pushes : List (List Form)) (h : pulls.length ≤ pushes.length) (g : List Form → E) :
    ((pulls.zip pushes).map fun p ↦ g p.1).foldl (· * ·) 1 = pulls.foldl (fun acc tuple ↦ acc * g tuple) 1 := by
  rw [show (fun p : List Form × List Form ↦ g p.1) = g ∘ Prod.fst from rfl, ← List.map_map, List.map_fst_zip h,
    List.foldl_map]

omit hon in
theorem foldl_zip_snd (pulls pushes : List (List Form)) (h : pushes.length ≤ pulls.length) (g : List Form → E) :
    ((pulls.zip pushes).map fun p ↦ g p.2).foldl (· * ·) 1 = pushes.foldl (fun acc tuple ↦ acc * g tuple) 1 := by
  rw [show (fun p : List Form × List Form ↦ g p.2) = g ∘ Prod.snd from rfl, ← List.map_map, List.map_snd_zip h,
    List.foldl_map]

theorem part_pull_eq {t : ℕ} (ht : t < 6) (x : E) {n : ℕ} (hn : tr.height t ≤ n) (weights : Array E) (beta : E) :
    ((AlgC.atParts tr weights beta (digits x n)).getD t default).pull =
      ev x ((tables.getD t default).flushes.pull.foldl
        (fun acc tuple ↦ acc * fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0) 1) := by
  rw [atParts_getD _ _ _ _ ht, AlgC.atPart, AlgC.tablePartOf_pull (tables_getD_mem ht),
    foldl_zip_fst _ _ (tables_facts t ht).2.2.1.le
      (fun tu ↦ fpE tu weights beta (AlgC.atColumn tr (digits x n) (tables.getD t default))), ev_foldl_mul, map_one]
  simp only [ev_fpP]
  refine congrArg (fun f ↦ List.foldl f 1 _) (funext fun acc ↦ funext fun tuple ↦ ?_)
  congr 2
  funext c
  exact atColumn_eq hon ht x hn c

theorem part_push_eq {t : ℕ} (ht : t < 6) (x : E) {n : ℕ} (hn : tr.height t ≤ n) (weights : Array E) (beta : E) :
    ((AlgC.atParts tr weights beta (digits x n)).getD t default).push =
      ev x ((tables.getD t default).flushes.push.foldl
        (fun acc tuple ↦ acc * fpP tuple weights beta fun c ↦ (tablePolys tr t).getD c 0) 1) := by
  rw [atParts_getD _ _ _ _ ht, AlgC.atPart, AlgC.tablePartOf_push (tables_getD_mem ht),
    foldl_zip_snd _ _ (tables_facts t ht).2.2.1.ge
      (fun tu ↦ fpE tu weights beta (AlgC.atColumn tr (digits x n) (tables.getD t default))), ev_foldl_mul, map_one]
  simp only [ev_fpP]
  refine congrArg (fun f ↦ List.foldl f 1 _) (funext fun acc ↦ funext fun tuple ↦ ?_)
  congr 2
  funext c
  exact atColumn_eq hon ht x hn c

theorem atActive_getD {t : ℕ} (ht : t < 6) (x : E) {n : ℕ} (hn : tr.height t + 1 ≤ n) :
    (AlgC.atActive tr (digits x n)).getD t 0 = (Domain.zActP (tr.rows.getD t 0) (tr.height t)).eval x := by
  have hr6 : t < tr.rows.length := by rw [hon.rowsFit.1]; exact ht
  have hh6 : t < tr.shape.heights.length := by rw [hon.valid.1]; exact ht
  rw [AlgC.atActive, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_zip]
  dsimp only
  rw [← List.getD_eq_getElem tr.rows 0 hr6, ← List.getD_eq_getElem tr.shape.heights 0 hh6]
  exact Domain.activeVanishingFromBits_eq ((hon.rowsFit.2 t ht).2) hn x

end Honest


/-! ### The chunks are read inside the digits -/

set_option maxRecDepth 8000 in
/-- **The tables' flushes, bounded** (structural, by the kernel): at most `15` flushes, every monomial of degree at
most `2`. -/
theorem tables_bounds : ∀ t < 6, (tables.getD t default).flushes.pull.length ≤ 15 ∧
    (tables.getD t default).flushes.push.length ≤ 15 ∧
    ∀ tu ∈ (tables.getD t default).flushes.pull ++ (tables.getD t default).flushes.push, ∀ f ∈ tu, ∀ mc ∈ f,
      mc.1.length ≤ 2 := by
  decide +kernel

theorem formDeg_le (B : ℕ) : ∀ (f : Form) (d : ℕ), (∀ mc ∈ f, mc.1.length ≤ B) → formDeg d f ≤ max d B
  | [], d, _ => le_max_left _ _
  | mc :: f, d, h => by
    unfold formDeg
    rw [List.foldl_cons]
    have ih := formDeg_le B f (if mc.2 = 0 then d else max d mc.1.length) fun m hm ↦ h m (List.mem_cons_of_mem _ hm)
    unfold formDeg at ih
    refine ih.trans ?_
    have := h mc (List.mem_cons_self ..)
    split_ifs <;> omega

theorem foldl_formDeg_le (B : ℕ) : ∀ (tuple : List Form) (d : ℕ), (∀ f ∈ tuple, ∀ mc ∈ f, mc.1.length ≤ B) →
    tuple.foldl formDeg d ≤ max d B
  | [], d, _ => le_max_left _ _
  | f :: tuple, d, h => by
    rw [List.foldl_cons]
    have h1 := formDeg_le B f d (h f (List.mem_cons_self ..))
    have h2 := foldl_formDeg_le B tuple (formDeg d f) fun g hg ↦ h g (List.mem_cons_of_mem _ hg)
    omega

theorem tupleDegree_le_two {tuple : List Form} (h : ∀ f ∈ tuple, ∀ mc ∈ f, mc.1.length ≤ 2) : tupleDegree tuple ≤ 2 := by
  rw [tupleDegree_eq]
  have := foldl_formDeg_le 2 tuple 0 h
  omega

theorem sum_tupleDegree_le {l : List (List Form)} (h : ∀ tu ∈ l, ∀ f ∈ tu, ∀ mc ∈ f, mc.1.length ≤ 2) :
    (l.map tupleDegree).sum ≤ 2 * l.length := by
  induction l with
  | nil => simp
  | cons tu l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := tupleDegree_le_two (h tu (List.mem_cons_self ..))
    have h2 := ih fun tu' htu ↦ h tu' (List.mem_cons_of_mem _ htu)
    omega

/-- **A table's leaf degrees are at most `31`.** -/
theorem tableDegrees_le {t : ℕ} (ht : t < 6) :
    max (tableDegrees (tables.getD t default)).1 (tableDegrees (tables.getD t default)).2 ≤ 31 := by
  rw [tableDegrees_eq ht]
  obtain ⟨h1, h2, h3⟩ := tables_bounds t ht
  have e1 := sum_tupleDegree_le fun tu htu ↦ h3 tu (List.mem_append_left _ htu)
  have e2 := sum_tupleDegree_le fun tu htu ↦ h3 tu (List.mem_append_right _ htu)
  dsimp only
  omega

theorem le_foldl_max : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨le_rfl, fun _ h ↦ absurd h List.not_mem_nil⟩
  | y :: l, a => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := le_foldl_max l (max a y)
    refine ⟨le_trans (le_max_left _ _) h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right _ _) h1
    · exact h2 x hx

theorem height_le_constraintVars {tr : Trace} (hon : TraceHonest tr) {t : ℕ} (ht : t < 6) :
    tr.height t ≤ tr.shape.constraintVars := by
  refine (le_foldl_max _ 0).2 _ (List.mem_append_left _ ?_)
  rw [Trace.height, List.getD_eq_getElem _ _ (by rw [hon.valid.1]; exact ht)]
  exact List.getElem_mem _

theorem chunks_lt {d k : ℕ} (h : d + 1 < 2 ^ k) : ∀ e ∈ chunks (d + 1), e < k := by
  intro e he
  have := (AlgC.chunks_spec (n := d + 1) (by omega)).2.2 e he
  have := (Nat.log2_lt (n := d + 1) (by omega)).mpr h
  omega

end UniComplete.AlgH
