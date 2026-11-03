-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses `formal/Heap` (`tableTuples`,
-- `rows_perm_tableTuples`, `perm_flatMap_map_comm`, `flushTuples_eq_opcode`) and `formal/Lv42` (leanerVM `mumbai`
-- f0393df4, MIT OR Apache-2.0): `boundaryTuples_push`, `boundaryTuples_pull` (`Protocol/LeanIsa/Bus.lean`).
import UniComplete.MappingTrace
import Heap.LeanIsa

/-!
# The bus of the placed trace is Lv42's (milestone 4)

The PIOP's pushed and pulled tuples (`pushTuples`, `pullTuples`, as `List E`) are Lv42's (`M3Instance.tuples`, as
`Vector K 16`), each in `E` (`phi`), up to order:

* **A table's tuples** (`tablePart_perm`): the PIOP's, flush by flush over the active rows (`activeRows`), are its
  executed rows moved by `rowPosition` (`activeRows_perm`), each row's tuples Lv42's (`rowBridge`, the placed
  cells being Lv42's at the executed rows, `cell_executed`), so Lv42's `tableTuples` (`Heap.rows_perm_tableTuples`).
* **The boundary** (`memoryTuple_eq`, `bytecodeTuple_eq`, `stateTuple_eq`): the memory's cells, the bytecode's
  instructions and the state are Lv42's boundary blocks (`boundaryTuples_push`, `_pull`) slot by slot: `SEP_MEM =
  g`, the address `g^i`, the count, the limbs; `SEP_BYTECODE = g^2` (the setup's slot `0` is `K.ofBits 4 = g^2`),
  the pc, the count, the entry; `SEP_STATE = 1` and `prog.finalPc = g^(2^lb − 1)`.
* **`bus_perm`**: the two sides are a permutation of Lv42's two sides in `E`, so Lv42's `Balanced` (a permutation
  of `K`-tuples) gives the PIOP's.
-/

namespace UniComplete.Mapping

open UniStatement LeanVM.Parameters LeanVM.Protocol
open Lv42.Protocol Lv42.Protocol.LeanIsa Lv42.Arithmetization

variable (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)

/-! ### The active rows -/

/-- **The active rows are the executed rows moved by `rowPosition`.** -/
theorem activeRows_perm (hfit : D.shape.RowsFit rows) (t : Fin 6) :
    (activeRows (honestTrace D input rows q) t).Perm
      ((List.range (rows.getD t 0)).map (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0))) := by
  have hcnt := count_le D rows hfit t t.isLt
  set h := D.shape.heights.getD t 0
  set count := rows.getD t 0
  have hnd : ((List.range count).map (rowPosition count h)).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy ↦ ?_) List.nodup_range
    exact Domain.rowPosition_injOn hcnt
      (Set.mem_Iio.mpr (lt_of_lt_of_le (List.mem_range.mp hx) hcnt))
      (Set.mem_Iio.mpr (lt_of_lt_of_le (List.mem_range.mp hy) hcnt)) hxy
  refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd).mpr fun i ↦ ?_
  show i ∈ (List.range (2 ^ h)).filter (fun i ↦ isActive i count h) ↔ _
  simp only [List.mem_filter, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨hi, ha⟩
    obtain ⟨x, hx, rfl⟩ := (Domain.rowPosition_bijOn hcnt).surjOn (Set.mem_Iio.mpr hi)
    rw [Domain.isActive_rowPosition hcnt (Set.mem_Iio.mp hx), decide_eq_true_eq] at ha
    exact ⟨x, ha, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Domain.rowPosition_lt hcnt (lt_of_lt_of_le hx hcnt), ?_⟩
    rw [Domain.isActive_rowPosition hcnt (lt_of_lt_of_le hx hcnt), decide_eq_true_eq]
    exact hx

/-! ### A table's tuples -/

/-- An executed row of Lv42's table `t` is in its height. -/
theorem lt_tau (hfit : D.shape.RowsFit rows) (t : Fin 6) {x : ℕ} (hx : x < rows.getD t 0) :
    x < 2 ^ (D.inst rows).τ (opIdx t) := by
  show x < 2 ^ (D.sizes rows).τ t
  rw [tau_eq D rows hfit t]
  exact lt_of_lt_of_le hx (count_le D rows hfit t t.isLt)

/-- **The placed cells of an executed row are Lv42's**: at the PIOP's row `rowPosition x`, `x` executed, the
trace's cells are Lv42's row `x` (`0` past the width). -/
theorem cell_executed (hfit : D.shape.RowsFit rows) (t : Fin 6) {x : ℕ} (hx : x < rows.getD t 0) :
    (fun c ↦ (honestTrace D input rows q).cell t c
        (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x)) =
      rowE ((D.inst rows).row q (opIdx t) ⟨x, lt_tau D rows hfit t hx⟩) := by
  funext c
  have hxh : x < 2 ^ D.shape.heights.getD t 0 := lt_of_lt_of_le hx (count_le D rows hfit t t.isLt)
  rw [Trace.cell, rowE]
  by_cases hc : c < (tables.getD t default).width
  · have hc' : c < (D.inst rows).width (opIdx t) := by
      have := tables_width t
      show c < width (opIdx t)
      omega
    rw [cell_rowPosition D input rows q hfit t hc hxh, Domain.ite_neg_of (fun h ↦ h.2 hx), mdif_pos hc',
      lv42TableCell_eq D rows q t hc' (lt_tau D rows hfit t hx)]
  · have hc' : ¬ c < (D.inst rows).width (opIdx t) := by
      have := tables_width t
      show ¬ c < width (opIdx t)
      omega
    rw [column_of_ge D input rows q t (by omega), mdif_neg hc']
    exact ofKZero

/-- An executed row's tuples, the PIOP's, are Lv42's. -/
theorem rowTuples_phi (hfit : D.shape.RowsFit rows) (t : Fin 6) (side : Side) {x : ℕ}
    (hx : x < rows.getD t 0) :
    ((sideForms t side).map fun tuple ↦ tupleAt tuple fun c ↦ (honestTrace D input rows q).cell t c
        (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x)) =
      (Heap.rowTuples (D.inst rows) q (opIdx t) side x).map phi := by
  rw [cell_executed D input rows q hfit t hx]
  refine (rowBridge t side ((D.inst rows).row q (opIdx t) ⟨x, lt_tau D rows hfit t hx⟩)).trans ?_
  unfold Heap.rowTuples
  rw [mdif_pos (lt_tau D rows hfit t hx)]
  rfl

/-- **A table's tuples are Lv42's**: the PIOP's tuples of either side of table `t` (over its active rows) are a
permutation of Lv42's (over its executed rows), in `E`. -/
theorem tablePart_perm (hfit : D.shape.RowsFit rows) (t : Fin 6) (side : Side) :
    ((sideForms t side).flatMap fun tuple ↦ (activeRows (honestTrace D input rows q) t).map fun i ↦
        tupleAt tuple ((honestTrace D input rows q).cell t · i)).Perm
      ((Heap.tableTuples (D.inst rows) q (opIdx t) side).map phi) := by
  refine (Heap.perm_flatMap_map_comm _ _ _).trans ?_
  refine ((activeRows_perm D input rows q hfit t).flatMap_right _).trans ?_
  rw [List.flatMap_map, List.flatMap_congr fun x hx ↦
    rowTuples_phi D input rows q hfit t side (List.mem_range.mp hx), ← List.map_flatMap]
  have hrows : (D.inst rows).rows (opIdx t) = rows.getD t 0 := rfl
  have h := (Heap.rows_perm_tableTuples (D.inst rows) q (opIdx t) side).map phi
  rw [hrows] at h
  exact h

/-- **The tables' tuples are Lv42's flushes**, on either side. -/
theorem tables_perm (hfit : D.shape.RowsFit rows) (side : Side) :
    ((List.range 6).flatMap fun t ↦ (sideForms t side).flatMap fun tuple ↦
        (activeRows (honestTrace D input rows q) t).map fun i ↦
          tupleAt tuple ((honestTrace D input rows q).cell t · i)).Perm
      (((D.inst rows).flushTuples q side).map phi) := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map,
    Heap.LeanIsa.flushTuples_eq_opcode Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) q side,
    List.map_flatMap]
  exact List.Perm.flatMap_left _ fun t _ ↦ tablePart_perm D input rows q hfit t side

/-! ### The boundary -/

/-- A memory column's cell is Lv42's. -/
theorem memory_cell {k : ℕ} (hk : k < 4) {x : ℕ} (hx : x < 2 ^ D.shape.logMemory) :
    ((honestTrace D input rows q).memory.getD k #[]).getD x 0 =
      cell Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) q (memCol ⟨k, hk⟩) ⟨x, hx⟩ :=
  (memory_getD D input rows q hk hx).trans (lv42Cell_eq D rows q _ hx)

/-- A setup slot of instruction `x`: the slot `s < 16`, `0` past them. -/
theorem slot_cell {x : ℕ} (hx : x < 2 ^ D.prog.logSize) (s : ℕ) :
    ((honestTrace D input rows q).slots.getD s #[]).getD x 0 =
      if s < 16 then tupleSlot D.prog ⟨x, hx⟩ s else 0 := by
  have hx' : x < 2 ^ D.shape.logBytecode := by rw [D.logBytecode_eq]; exact hx
  split_ifs with hs
  · exact slots_getD D input rows q hs hx'
  · rw [List.getD_eq_default _ _ (by rw [slots_length]; omega)]
    rfl

set_option linter.unusedSimpArgs false in
/-- **A memory cell's tuple is Lv42's memory tuple**, at any count. -/
theorem memoryTuple_eq {x : ℕ} (hx : x < 2 ^ D.shape.logMemory) (c : K) :
    memoryTuple (honestTrace D input rows q) x (ofK c) =
      phi (tupleOf (LeanVM.Parameters.gpow 1) (#[LeanVM.Parameters.gpow x, c] ++
        (memLimbs Blake2sFlock.blake2sFlockSpec (D.sizes rows) q ⟨x, hx⟩).toArray)) := by
  rw [phi_tupleOf _ _ (by simp [memLimbs])]
  simp only [memoryTuple, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.singleton_append, memory_cell D input rows q (by norm_num : 0 < 4) hx,
    memory_cell D input rows q (by norm_num : 1 < 4) hx, memory_cell D input rows q (by norm_num : 2 < 4) hx,
    memLimbs, sepMem_eq, pow_one, Array.toList_append, List.toList_toArray, List.size_toArray,
    Array.size_append, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.append_assoc,
    LeanVM.Parameters.gpow]
  rfl

set_option linter.unusedSimpArgs false in
/-- **An instruction's tuple is Lv42's bytecode tuple**, at any count: the setup's slots are `SEP_BYTECODE`, the
pc, then the entry. -/
theorem bytecodeTuple_eq {x : ℕ} (hx : x < 2 ^ D.prog.logSize) (c : K) :
    bytecodeTuple (honestTrace D input rows q) x (ofK c) =
      phi (tupleOf (LeanVM.Parameters.gpow 2) (#[LeanVM.Parameters.gpow x, c] ++
        (entryList (prog := D.prog) ⟨x, hx⟩).toArray)) := by
  rw [phi_tupleOf _ _ (by simp [entryList])]
  simp only [bytecodeTuple, bytecodeSlot, slot_cell D input rows q hx, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.singleton_append]
  simp [tupleSlot, entryList, List.finRange_succ, ofBits_four, ofKZero]

/-- The state's initial tuple is Lv42's. -/
theorem stateTuple_push : stateTuple 1 = phi (tupleOf (LeanVM.Parameters.gpow 0) #[1, 1]) := by
  rw [phi_tupleOf _ _ (by simp)]
  simp [stateTuple, sepState_eq]

/-- The state's final tuple is Lv42's: `g^(2^lb − 1)` is `prog.finalPc`. -/
theorem stateTuple_pull :
    stateTuple (UniStatement.gpow (2 ^ D.shape.logBytecode - 1)) =
      phi (tupleOf (LeanVM.Parameters.gpow 0) #[D.prog.finalPc, 1]) := by
  rw [phi_tupleOf _ _ (by simp)]
  simp [stateTuple, sepState_eq, gpow_eq, Lv42.Semantics.Program.finalPc, D.logBytecode_eq, ofKPow]

/-- The memory's tuples, at counts `cnt`. -/
theorem memory_map (cnt : ℕ → K) (c : Fin (2 ^ (D.sizes rows).logMem) → K) (hc : ∀ x, c x = cnt x) :
    (List.range (2 ^ (honestTrace D input rows q).shape.logMemory)).map
        (fun i ↦ memoryTuple (honestTrace D input rows q) i (ofK (cnt i))) =
      ((List.finRange (2 ^ (D.sizes rows).logMem)).map fun x ↦
        tupleOf (LeanVM.Parameters.gpow 1) (#[LeanVM.Parameters.gpow x.val, c x] ++
          (memLimbs Blake2sFlock.blake2sFlockSpec (D.sizes rows) q x).toArray)).map phi := by
  rw [List.map_map]
  show (List.range (2 ^ (D.sizes rows).logMem)).map _ = _
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun x _ ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, memoryTuple_eq D input rows q x.isLt, hc]

/-- The bytecode's tuples, at counts `cnt`. -/
theorem bytecode_map (cnt : ℕ → K) (c : Fin (2 ^ D.prog.logSize) → K) (hc : ∀ x, c x = cnt x) :
    (List.range (2 ^ (honestTrace D input rows q).shape.logBytecode)).map
        (fun i ↦ bytecodeTuple (honestTrace D input rows q) i (ofK (cnt i))) =
      ((List.finRange (2 ^ D.prog.logSize)).map fun i ↦
        tupleOf (LeanVM.Parameters.gpow 2) (#[LeanVM.Parameters.gpow i.val, c i] ++
          (entryList i).toArray)).map phi := by
  rw [honestTrace_shape, D.logBytecode_eq, List.map_map, ← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun x _ ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, bytecodeTuple_eq D input rows q x.isLt, hc]

/-! ### The two sides -/

/-- Lv42's pushed boundary tuples are the PIOP's: the state's initial tuple, the memory's and the bytecode's at
count `1`. -/
theorem boundary_push_eq :
    ((D.inst rows).boundaryTuples q .push).map phi =
      [stateTuple 1] ++
        (List.range (2 ^ (honestTrace D input rows q).shape.logMemory)).map
          (fun i ↦ memoryTuple (honestTrace D input rows q) i 1) ++
        (List.range (2 ^ (honestTrace D input rows q).shape.logBytecode)).map
          (fun i ↦ bytecodeTuple (honestTrace D input rows q) i 1) := by
  have hm := memory_map D input rows q (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ rfl)
  have hb := bytecode_map D input rows q (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ rfl)
  simp only [ofKOne] at hm hb
  rw [boundaryTuples_push, List.map_append, List.map_append, List.map_singleton]
  congr 1
  congr 1
  all_goals first | exact hm.symm | exact hb.symm

/-- Lv42's pulled boundary tuples are the PIOP's: the state's final tuple, the memory's and the bytecode's at
their final counts. -/
theorem boundary_pull_eq :
    ((D.inst rows).boundaryTuples q .pull).map phi =
      [stateTuple (UniStatement.gpow (2 ^ (honestTrace D input rows q).shape.logBytecode - 1))] ++
        (List.range (2 ^ (honestTrace D input rows q).shape.logMemory)).map (fun i ↦
          memoryTuple (honestTrace D input rows q) i
            (ofK (((honestTrace D input rows q).memory.getD 3 #[]).getD i 0))) ++
        (List.range (2 ^ (honestTrace D input rows q).shape.logBytecode)).map (fun i ↦
          bytecodeTuple (honestTrace D input rows q) i
            (ofK ((honestTrace D input rows q).bytecodeFinal.getD i 0))) := by
  have hm := memory_map D input rows q
    (fun i ↦ ((honestTrace D input rows q).memory.getD 3 #[]).getD i 0)
    (fun x ↦ cell Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) q (memCol 3) x)
    (fun x ↦ (memory_cell D input rows q (by norm_num : 3 < 4) x.isLt).symm)
  have hb := bytecode_map D input rows q (fun i ↦ (honestTrace D input rows q).bytecodeFinal.getD i 0)
    (fun x ↦ cell Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) q bfcntCol x)
    (fun x ↦ ((bytecodeFinal_getD D input rows q (by rw [D.logBytecode_eq]; exact x.isLt)).trans
      (lv42Cell_eq D rows q _ x.isLt)).symm)
  rw [boundaryTuples_pull, List.map_append, List.map_append, List.map_singleton]
  congr 1
  congr 1
  all_goals first | exact hm.symm | exact hb.symm | exact congrArg (· :: []) (stateTuple_pull D).symm

/-- **The pushed tuples are Lv42's**, in `E`. -/
theorem push_perm (hfit : D.shape.RowsFit rows) :
    (pushTuples (honestTrace D input rows q)).Perm (((D.inst rows).tuples q .push).map phi) := by
  have hA := tables_perm D input rows q hfit .push
  simp only [sideForms] at hA
  rw [M3Instance.tuples, List.map_append, boundary_push_eq D input rows q]
  unfold pushTuples
  simp only [List.append_assoc, List.singleton_append]
  refine hA.append ?_
  rw [← List.append_assoc]
  exact List.perm_append_singleton _ _

/-- **The pulled tuples are Lv42's**, in `E`. -/
theorem pull_perm (hfit : D.shape.RowsFit rows) :
    (pullTuples (honestTrace D input rows q)).Perm (((D.inst rows).tuples q .pull).map phi) := by
  have hA := tables_perm D input rows q hfit .pull
  simp only [sideForms] at hA
  rw [M3Instance.tuples, List.map_append, boundary_pull_eq D input rows q]
  unfold pullTuples dividedTuples
  simp only [List.append_assoc, List.singleton_append]
  refine hA.append ?_
  rw [← List.append_assoc]
  exact List.perm_append_singleton _ _

/-- **The bus balances**: Lv42's `Balanced`, carried by `phi`, is the PIOP's. -/
theorem bus_perm (hfit : D.shape.RowsFit rows) (hbal : (D.inst rows).Balanced q) :
    (pushTuples (honestTrace D input rows q)).Perm (pullTuples (honestTrace D input rows q)) :=
  (push_perm D input rows q hfit).trans ((hbal.map phi).trans (pull_perm D input rows q hfit).symm)

end UniComplete.Mapping
