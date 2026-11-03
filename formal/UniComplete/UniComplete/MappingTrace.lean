-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses `formal/Lv42` (leanerVM `mumbai` f0393df4,
-- MIT OR Apache-2.0): `column_limb`, `slotLimbs_flockColumn` (`Protocol/LeanIsa/Read.lean`).
import UniComplete.MappingRows

/-!
# The placed trace's cells (milestone 4)

What `honestTrace D input rows q` holds, cell by cell, under `RowsFit`:

* **The heights** (`tau_eq`): Lv42's `τ_t = ⌈log₂ rows_t⌉` is the shape's `h_t` (`leastRows h ≤ rows ≤ 2^h`:
  `2^(h−1) < rows ≤ 2^h`, or `h = 0` and `rows ≤ 1`).
* **Scattering** (`foldl_set_getD`, `scatter_getD`): writing value `x` at `f x` for every `x` of a duplicate-free
  list, `f` injective on it, leaves `value x` at `f x`; so `scatter r (rowPosition count r) value` holds
  Lv42's row `x` at `rowPosition count r x`.
* **The cells** (`column_eq`, `cell_rowPosition`, `memory_getD`, `bytecodeFinal_getD`, `slots_getD`,
  `qflock_getD`): a table's column `c` at the PIOP's row `rowPosition x` is Lv42's cell `x` of column
  `⟨opIdx t, c⟩` (`lv42TableCell`), but `1` on a counter column at a padding row (`x ≥ count`); the memory's,
  the bytecode's final counts', the setup slots', and `q_flock`'s word `j + 256 · rowPosition x` is
  Lv42's `QFLOCK` word `j + 256 x`.
* **Lv42's cells** (`lv42TableCell_eq`, `lv42Cell_eq`, `limb_eq_flock`): `lv42Cell` is Lv42's `column`;
  `BLAKE2S`'s limb `k` at row `x` is `QFLOCK`'s word `slot k + 256 x` (Lv42's strided layout).
-/

namespace UniComplete.Mapping

open UniStatement LeanVM.Parameters LeanVM.Protocol
open Lv42.Protocol Lv42.Protocol.LeanIsa Lv42.Arithmetization

/-- `dif_pos`, which this Mathlib deprecates. -/
theorem mdif_pos {α : Sort*} {c : Prop} [Decidable c] {t : c → α} {e : ¬ c → α} (h : c) :
    dite c t e = t h := by
  simp [h]

/-- `dif_neg`, which this Mathlib deprecates. -/
theorem mdif_neg {α : Sort*} {c : Prop} [Decidable c] {t : c → α} {e : ¬ c → α} (h : ¬ c) :
    dite c t e = e h := by
  simp [h]

/-! ### The heights -/

/-- **Lv42's height is the shape's**, under `RowsFit`. -/
theorem tau_eq (D : Deployment) (rows : List ℕ) (hfit : D.shape.RowsFit rows) (t : Fin 6) :
    (D.sizes rows).τ t = D.shape.heights.getD t 0 := by
  obtain ⟨-, hfit⟩ := hfit
  obtain ⟨hlo, hhi⟩ := hfit t t.isLt
  have hcap : D.shape.capacityRows.getD t 0 = Shape.leastRows (D.shape.heights.getD t 0) :=
    List.getD_map D.shape.heights 0 Shape.leastRows
  rw [hcap] at hlo
  show Nat.clog 2 (rows.getD t 0) = _
  set h := D.shape.heights.getD t 0
  apply le_antisymm (Nat.clog_le_of_le_pow hhi)
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · have hl : Shape.leastRows h = 2 ^ (h - 1) + 1 := by simp [Shape.leastRows, hpos.ne']
    rw [hl] at hlo
    have := (Nat.lt_clog_iff_pow_lt (b := 2) (by norm_num) (x := rows.getD t 0) (y := h - 1)).mpr
      (by omega)
    omega

/-- A table's rows fit its height. -/
theorem count_le (D : Deployment) (rows : List ℕ) (hfit : D.shape.RowsFit rows) (t : ℕ) (ht : t < 6) :
    rows.getD t 0 ≤ 2 ^ D.shape.heights.getD t 0 :=
  (hfit.2 t ht).2

/-! ### Scattering -/

theorem foldl_set_size {α : Type} (f : ℕ → ℕ) (val : ℕ → α) :
    ∀ (L : List ℕ) (a : Array α), (L.foldl (fun a y ↦ a.set! (f y) (val y)) a).size = a.size
  | [], _ => rfl
  | y :: L, a => by
    rw [List.foldl_cons, foldl_set_size f val L, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem foldl_set_getD_of_ne {α : Type} (f : ℕ → ℕ) (val : ℕ → α) (p : ℕ) (d : α) :
    ∀ (L : List ℕ) (a : Array α), (∀ y ∈ L, f y ≠ p) →
      (L.foldl (fun a y ↦ a.set! (f y) (val y)) a).getD p d = a.getD p d
  | [], _, _ => rfl
  | y :: L, a, h => by
    rw [List.foldl_cons, foldl_set_getD_of_ne f val p d L _ fun z hz ↦ h z (List.mem_cons_of_mem _ hz),
      Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, ite_eq_right_of_eq_false _ _ (eq_false (h y List.mem_cons_self))]

/-- **Writing `val x` at `f x` for every `x` of a list** leaves `val x` at `f x`, `f` injective on the list. -/
theorem foldl_set_getD {α : Type} (f : ℕ → ℕ) (val : ℕ → α) (d : α) :
    ∀ (L : List ℕ) (a : Array α), L.Nodup → ∀ x ∈ L, (∀ y ∈ L, f y = f x → y = x) → f x < a.size →
      (L.foldl (fun a y ↦ a.set! (f y) (val y)) a).getD (f x) d = val x
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | y :: L, a, hnd, x, hx, hinj, hs => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hxL
    · rw [foldl_set_getD_of_ne f val _ d L _ fun z hz hzx ↦ (List.nodup_cons.mp hnd).1
          (hinj z (List.mem_cons_of_mem _ hz) hzx ▸ hz),
        Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
        ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true hs)]
      rfl
    · exact foldl_set_getD f val d L _ (List.nodup_cons.mp hnd).2 x hxL
        (fun z hz ↦ hinj z (List.mem_cons_of_mem _ hz))
        (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hs)

theorem scatter_size (r : ℕ) (pos : ℕ → ℕ) (value : ℕ → K) : (scatter r pos value).size = 2 ^ r := by
  rw [scatter, foldl_set_size, Array.size_replicate]

/-- **A scattered column holds value `x` at `pos x`**, `pos` a bijection of `[0, 2^r)`. -/
theorem scatter_getD (r : ℕ) (pos : ℕ → ℕ) (value : ℕ → K) (hinj : Set.InjOn pos (Set.Iio (2 ^ r)))
    (hlt : ∀ x < 2 ^ r, pos x < 2 ^ r) {x : ℕ} (hx : x < 2 ^ r) :
    (scatter r pos value).getD (pos x) 0 = value x :=
  foldl_set_getD pos value 0 _ _ List.nodup_range x (List.mem_range.mpr hx)
    (fun y hy h ↦ hinj (Set.mem_Iio.mpr (List.mem_range.mp hy)) (Set.mem_Iio.mpr hx) h)
    (by rw [Array.size_replicate]; exact hlt x hx)

/-! ### The cells of the placed trace -/

variable (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)

/-- Table `t`'s columns in the placed trace (`honestTrace`'s `table`). -/
def tableCols (t : Fin 6) : List (Array K) :=
  let r := D.shape.heights.getD t.val 0
  let count := rows.getD t.val 0
  let counters := (tables.getD t.val default).countColumns
  (List.range (tables.getD t.val default).width).map fun i ↦
    let placed := scatter r (rowPosition count r) (lv42TableCell D rows q t i)
    if i ∈ counters then
      Array.ofFn (n := 2 ^ r) fun p ↦ if isActive p.val count r then placed.getD p.val 0 else 1
    else placed

theorem honestTrace_tables : (honestTrace D input rows q).tables = (List.finRange 6).map (tableCols D rows q) :=
  rfl

theorem honestTrace_shape : (honestTrace D input rows q).shape = D.shape := rfl

theorem honestTrace_rows : (honestTrace D input rows q).rows = rows := rfl

theorem honestTrace_height (t : ℕ) : (honestTrace D input rows q).height t = D.shape.heights.getD t 0 := rfl

theorem tables_getD (t : Fin 6) :
    (honestTrace D input rows q).tables.getD t [] = tableCols D rows q t := by
  rw [honestTrace_tables, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  rfl

/-- Column `c` of table `t` (`c` below the width). -/
theorem column_eq (t : Fin 6) {c : ℕ} (hc : c < (tables.getD t default).width) :
    (honestTrace D input rows q).column t c =
      if c ∈ (tables.getD t default).countColumns then
        Array.ofFn (n := 2 ^ D.shape.heights.getD t 0) fun p ↦
          if isActive p.val (rows.getD t 0) (D.shape.heights.getD t 0) then
            (scatter (D.shape.heights.getD t 0) (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0))
              (lv42TableCell D rows q t c)).getD p.val 0
          else 1
      else scatter (D.shape.heights.getD t 0) (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0))
        (lv42TableCell D rows q t c) := by
  rw [Trace.column, tables_getD, tableCols, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map,
    List.getElem_range]

theorem column_size (t : Fin 6) {c : ℕ} (hc : c < (tables.getD t default).width) :
    ((honestTrace D input rows q).column t c).size = 2 ^ D.shape.heights.getD t 0 := by
  rw [column_eq D input rows q t hc]
  split_ifs
  · exact Array.size_ofFn
  · exact scatter_size _ _ _

/-- A column past its table's width is empty. -/
theorem column_of_ge (t : Fin 6) {c : ℕ} (hc : (tables.getD t default).width ≤ c) :
    (honestTrace D input rows q).column t c = #[] := by
  rw [Trace.column, tables_getD, tableCols, List.getD_eq_default _ _ (by simpa using hc)]

/-- **The placed cell**: column `c` of table `t` at the PIOP's row `rowPosition x` is Lv42's cell `x`, but `1`
on a counter column at a padding row. -/
theorem cell_rowPosition (hfit : D.shape.RowsFit rows) (t : Fin 6) {c : ℕ}
    (hc : c < (tables.getD t default).width) {x : ℕ} (hx : x < 2 ^ D.shape.heights.getD t 0) :
    ((honestTrace D input rows q).column t c).getD
        (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x) 0 =
      if c ∈ (tables.getD t default).countColumns ∧ ¬ x < rows.getD t 0 then 1
      else lv42TableCell D rows q t c x := by
  have hcnt := count_le D rows hfit t t.isLt
  have hlt := Domain.rowPosition_lt hcnt hx
  have hs := scatter_getD (D.shape.heights.getD t 0) (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0))
    (lv42TableCell D rows q t c) (Domain.rowPosition_injOn hcnt)
    (fun y hy ↦ Domain.rowPosition_lt hcnt hy) hx
  have hact := Domain.isActive_rowPosition hcnt hx
  rw [column_eq D input rows q t hc]
  split_ifs with h1 h2 h2
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hlt, Option.getD_some]
    simp only [hact, decide_eq_false h2.2, Bool.false_eq_true, ite_false]
  · have hx' : x < rows.getD t 0 := by
      by_contra hn
      exact h2 ⟨h1, hn⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hlt, Option.getD_some]
    simp only [hact, decide_eq_true hx', ite_true]
    exact hs
  · exact absurd h2.1 h1
  · exact hs

/-- `lv42Cell` is Lv42's column. -/
theorem lv42Cell_eq (c : Col) {x : ℕ} (hx : x < 2 ^ kappa D.prog (D.sizes rows) c) :
    lv42Cell D rows q c x = ((D.inst rows).column q c).values.get ⟨x, hx⟩ := by
  rw [lv42Cell, mdif_pos hx]
  rfl

/-- `lv42TableCell` is Lv42's row. -/
theorem lv42TableCell_eq (t : Fin 6) {c : ℕ} (hc : c < width (opIdx t)) {x : ℕ}
    (hx : x < 2 ^ (D.inst rows).τ (opIdx t)) :
    lv42TableCell D rows q t c x = (D.inst rows).row q (opIdx t) ⟨x, hx⟩ ⟨c, hc⟩ := by
  rw [lv42TableCell, mdif_pos hc]
  exact lv42Cell_eq D rows q ⟨opIdx t, ⟨c, hc⟩⟩ hx

/-! ### The memory, the bytecode, the slots, `q_flock` -/

theorem memory_length : (honestTrace D input rows q).memory.length = 4 := by
  simp [honestTrace]

theorem memory_getD_arr {k : ℕ} (hk : k < 4) :
    (honestTrace D input rows q).memory.getD k #[] =
      Array.ofFn (n := 2 ^ D.shape.logMemory) fun x ↦ lv42Cell D rows q (memCol ⟨k, hk⟩) x.val := by
  simp only [honestTrace]
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]
  congr 1
  funext x
  rw [mdif_pos hk]

theorem memory_getD {k : ℕ} (hk : k < 4) {x : ℕ} (hx : x < 2 ^ D.shape.logMemory) :
    ((honestTrace D input rows q).memory.getD k #[]).getD x 0 = lv42Cell D rows q (memCol ⟨k, hk⟩) x := by
  rw [memory_getD_arr D input rows q hk, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hx,
    Option.getD_some]

theorem bytecodeFinal_eq : (honestTrace D input rows q).bytecodeFinal =
    Array.ofFn (n := 2 ^ D.shape.logBytecode) fun x ↦ lv42Cell D rows q bfcntCol x.val := rfl

theorem bytecodeFinal_getD {x : ℕ} (hx : x < 2 ^ D.shape.logBytecode) :
    (honestTrace D input rows q).bytecodeFinal.getD x 0 = lv42Cell D rows q bfcntCol x := by
  rw [bytecodeFinal_eq, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hx, Option.getD_some]

theorem slots_length : (honestTrace D input rows q).slots.length = 16 := by
  simp [honestTrace]

theorem slots_getD_arr {s : ℕ} (hs : s < 16) :
    (honestTrace D input rows q).slots.getD s #[] =
      Array.ofFn (n := 2 ^ D.shape.logBytecode) fun i ↦
        if h : i.val < 2 ^ D.prog.logSize then tupleSlot D.prog ⟨i.val, h⟩ s else 0 := by
  simp only [honestTrace]
  rw [List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map, List.getElem_range]

theorem slots_getD {s : ℕ} (hs : s < 16) {i : ℕ} (hi : i < 2 ^ D.shape.logBytecode) :
    ((honestTrace D input rows q).slots.getD s #[]).getD i 0 =
      tupleSlot D.prog ⟨i, by rw [← D.logBytecode_eq]; exact hi⟩ s := by
  rw [slots_getD_arr D input rows q hs, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hi,
    Option.getD_some, mdif_pos (by rw [← D.logBytecode_eq]; exact hi)]

theorem qflock_eq : (honestTrace D input rows q).qflock =
    (List.range (2 ^ (D.shape.heights.getD 5 0 + 8))).foldl (fun a word ↦
      a.set! (word % 256 + 256 * rowPosition (rows.getD 5 0) (D.shape.heights.getD 5 0) (word / 256))
        (lv42Cell D rows q flockCol word)) (Array.replicate (2 ^ (D.shape.heights.getD 5 0 + 8)) 0) := rfl

theorem qflock_size : (honestTrace D input rows q).qflock.size = 2 ^ (D.shape.heights.getD 5 0 + 8) := by
  rw [qflock_eq, foldl_set_size, Array.size_replicate]

/-- **`q_flock`'s instances are Lv42's, moved by `rowPosition`**: word `j + 256 · rowPosition x` is Lv42's
`QFLOCK` word `j + 256 x`. -/
theorem qflock_getD (hfit : D.shape.RowsFit rows) {j : ℕ} (hj : j < 256) {x : ℕ}
    (hx : x < 2 ^ D.shape.heights.getD 5 0) :
    (honestTrace D input rows q).qflock.getD
        (j + 256 * rowPosition (rows.getD 5 0) (D.shape.heights.getD 5 0) x) 0 =
      lv42Cell D rows q flockCol (j + 256 * x) := by
  have hcnt := count_le D rows hfit 5 (by norm_num)
  set hB := D.shape.heights.getD 5 0
  set f : ℕ → ℕ := fun word ↦ word % 256 + 256 * rowPosition (rows.getD 5 0) hB (word / 256)
  have hpow : 2 ^ (hB + 8) = 256 * 2 ^ hB := by rw [pow_add]; norm_num; ring
  have hw : j + 256 * x < 2 ^ (hB + 8) := by rw [hpow]; omega
  have hfw : f (j + 256 * x) = j + 256 * rowPosition (rows.getD 5 0) hB x := by
    simp only [f]
    congr 2
    · omega
    · congr 1
      omega
  rw [← hfw, qflock_eq]
  refine foldl_set_getD f _ 0 _ _ List.nodup_range _ (List.mem_range.mpr hw) (fun y hy hfy ↦ ?_) ?_
  · have hy' := List.mem_range.mp hy
    have hyq : y / 256 < 2 ^ hB := by rw [hpow] at hy'; omega
    have hwq : (j + 256 * x) / 256 < 2 ^ hB := by omega
    simp only [f] at hfy
    have hmod : y % 256 = (j + 256 * x) % 256 := by omega
    have hpos : rowPosition (rows.getD 5 0) hB (y / 256) =
        rowPosition (rows.getD 5 0) hB ((j + 256 * x) / 256) := by omega
    have hdiv := Domain.rowPosition_injOn hcnt (Set.mem_Iio.mpr hyq) (Set.mem_Iio.mpr hwq) hpos
    omega
  · rw [Array.size_replicate, hfw, hpow]
    have := Domain.rowPosition_lt hcnt hx
    omega

/-! ### `BLAKE2S`'s limbs are `QFLOCK`'s slots -/

/-- **Limb `k` of `BLAKE2S` at row `x` is `QFLOCK`'s word `slot k + 256 x`** (Lv42's strided layout). -/
theorem limb_eq_flock (k : Fin 18) {x : ℕ} (hx : x < 2 ^ (D.sizes rows).τ 5) :
    lv42Cell D rows q (limbCol k) x =
      lv42Cell D rows q flockCol ((Blake2sFlock.blake2sFlockSpec.slot k).val + 256 * x) := by
  have hw : (Blake2sFlock.blake2sFlockSpec.slot k).val + 256 * x < 2 ^ kappa D.prog (D.sizes rows) flockCol := by
    show _ < 2 ^ (8 + (D.sizes rows).τ 5)
    have := (Blake2sFlock.blake2sFlockSpec.slot k).isLt
    rw [pow_add]
    norm_num
    omega
  rw [lv42Cell_eq D rows q _ hx, lv42Cell_eq D rows q _ hw]
  have h1 := column_limb Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) q k ⟨x, hx⟩
  have h2 := column_committed Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) q flockCol
    not_isLimb_flockCol ⟨_, hw⟩
  refine h1.trans (Eq.trans ?_ h2.symm)
  simp only [cubeIndex_val]
  rfl

end UniComplete.Mapping
