-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses `formal/Lv42` (leanerVM `mumbai` f0393df4,
-- MIT OR Apache-2.0): `M3Honest`, `padRow_of_not_isLimb` (`Protocol/LeanIsa/Complete.lean`).
import UniComplete.MappingBus

/-!
# The honest prover's placed trace is honest (milestone 4, the mapping)

**`honestTrace_honest`**: for a deployment `D`, row counts that fit its shape (`RowsFit`) and a stack `q` of Lv42's
layout with `M3Honest` (`D.HonestRelation`), the placed trace `honestTrace D input rows q` has every property the
algebra needs (`TraceHonest`), each read off one clause of Lv42's relation:

| `TraceHonest` | from |
|---|---|
| sizes, the setup's fixed slots | `honestTrace`'s construction (`MappingTrace`), `tupleSlot` |
| `jump` | `ConstraintsVanish` at the executed rows (`jump_constraints`), `PaddingHonest` (`padRow` zero) |
| `counters` | `CountsNonzero` at the executed rows (`countColumns_eq`), `1` at the padding rows |
| `copies` | Lv42's strided layout (`limb_eq_flock`), `q_flock`'s placement (`qflock_getD`) |
| `publicLines` | `PublicLinesHold` (`publicK` is `publicInputOf`'s word) |
| `bus` | `Balanced` (`bus_perm`: the tuples are Lv42's in `E`, `phi` injective) |
| `flock` | `aux` (Flock's R1CS on `QFLOCK`), block by block: `q_flock`'s block `rowPosition x` is `QFLOCK`'s `x` |

Under `RowsFit` Lv42's height `⌈log₂ rows⌉` is the shape's (`tau_eq`), so the placed rows are Lv42's rows.

**`badFp_card`**: for every `α`, at most `(dividedTuples tr).length` challenges `β` are bad (`BadFp`: one root of
each divided fingerprint, linear in `β`). **`dividedTuples_length`**: that length is
`Σ_t pulls_t · |activeRows t| + 2^lm + 2^lb`; under `RowsFit` it is `dividedBound` of the shape and the row counts
(`Σ_t pulls_t · rows_t + 2^lm + 2^lb`, `pulls = [5, 5, 3, 5, 5, 11]`), at most `capBound` of the shape
(`rows_t ≤ 2^h_t`); the reference shape's (`UniStatement.reference`) is `10,878,976 < 2^24`.
-/

namespace UniComplete.Mapping

open UniStatement LeanVM.Parameters LeanVM.Protocol
open Lv42.Protocol Lv42.Protocol.LeanIsa Lv42.Arithmetization

variable (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)

/-! ### Rows -/

/-- Every PIOP row of table `t` is `rowPosition x` of a Lv42 row `x` in the height. -/
theorem exists_rowPosition (hfit : D.shape.RowsFit rows) {t : ℕ} (ht : t < 6) {i : ℕ}
    (hi : i < 2 ^ D.shape.heights.getD t 0) :
    ∃ x < 2 ^ D.shape.heights.getD t 0, rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x = i := by
  obtain ⟨x, hx, hxi⟩ := (Domain.rowPosition_bijOn (count_le D rows hfit t ht)).surjOn (Set.mem_Iio.mpr hi)
  exact ⟨x, Set.mem_Iio.mp hx, hxi⟩

/-- `cell_rowPosition` at a table index in `ℕ`. -/
theorem cell_rowPosition' (hfit : D.shape.RowsFit rows) (t : ℕ) (ht : t < 6) {c : ℕ}
    (hc : c < (tables.getD t default).width) {x : ℕ} (hx : x < 2 ^ D.shape.heights.getD t 0) :
    ((honestTrace D input rows q).column t c).getD
        (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x) 0 =
      if c ∈ (tables.getD t default).countColumns ∧ ¬ x < rows.getD t 0 then 1
      else lv42TableCell D rows q ⟨t, ht⟩ c x :=
  cell_rowPosition D input rows q hfit ⟨t, ht⟩ hc hx

/-- Lv42's height of table `t` is the shape's. -/
theorem tau_opIdx (hfit : D.shape.RowsFit rows) (t : ℕ) (ht : t < 6) :
    (D.inst rows).τ (opIdx ⟨t, ht⟩) = D.shape.heights.getD t 0 :=
  tau_eq D rows hfit ⟨t, ht⟩

/-- A cell of Lv42's table `t` at a row `x` in the height: the executed row's, or the padding row's. -/
theorem lv42TableCell_cases (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) (t : ℕ)
    (ht : t < 6) {c : ℕ} (hc : c < width (opIdx ⟨t, ht⟩)) {x : ℕ} (hx : x < 2 ^ D.shape.heights.getD t 0) :
    lv42TableCell D rows q ⟨t, ht⟩ c x =
      if x < rows.getD t 0 then (D.inst rows).row q (opIdx ⟨t, ht⟩) ⟨x, by rw [tau_opIdx D rows hfit]; exact hx⟩
        ⟨c, hc⟩
      else padRow (opIdx ⟨t, ht⟩) ⟨c, hc⟩ := by
  have hxt : x < 2 ^ (D.inst rows).τ (opIdx ⟨t, ht⟩) := by rw [tau_opIdx D rows hfit]; exact hx
  rw [lv42TableCell_eq D rows q ⟨t, ht⟩ hc hxt]
  split_ifs with hxc
  · rfl
  · exact congrFun (hrel.2 (opIdx ⟨t, ht⟩) ⟨x, hxt⟩ (not_lt.mp hxc)) ⟨c, hc⟩

/-! ### The fields of `TraceHonest` -/

theorem honest_tablesSize : (honestTrace D input rows q).tables.length = 6 ∧
    ∀ t < 6, ((honestTrace D input rows q).tables.getD t []).length = (tables.getD t default).width ∧
      ∀ c < (tables.getD t default).width,
        ((honestTrace D input rows q).column t c).size = 2 ^ (honestTrace D input rows q).height t := by
  refine ⟨by simp [honestTrace_tables], fun t ht ↦ ⟨?_, fun c hc ↦ ?_⟩⟩
  · rw [tables_getD D input rows q ⟨t, ht⟩, tableCols]
    simp
  · exact column_size D input rows q ⟨t, ht⟩ hc

theorem honest_memorySize : (honestTrace D input rows q).memory.length = 4 ∧
    ∀ k < 4, ((honestTrace D input rows q).memory.getD k #[]).size =
      2 ^ (honestTrace D input rows q).shape.logMemory :=
  ⟨memory_length D input rows q, fun k hk ↦ by rw [memory_getD_arr D input rows q hk]; exact Array.size_ofFn⟩

theorem honest_slotsSize : (honestTrace D input rows q).slots.length = 16 ∧
    ∀ s < 16, ((honestTrace D input rows q).slots.getD s #[]).size =
      2 ^ (honestTrace D input rows q).shape.logBytecode :=
  ⟨slots_length D input rows q, fun s hs ↦ by rw [slots_getD_arr D input rows q hs]; exact Array.size_ofFn⟩

theorem honest_slotsFixed : ∀ i < 2 ^ (honestTrace D input rows q).shape.logBytecode,
    ((honestTrace D input rows q).slots.getD 0 #[]).getD i 0 = K.ofBits 4 ∧
      ((honestTrace D input rows q).slots.getD 1 #[]).getD i 0 = LeanVM.Parameters.gpow i ∧
      ((honestTrace D input rows q).slots.getD 2 #[]).getD i 0 = 0 := by
  intro i hi
  rw [slots_getD D input rows q (by norm_num) hi, slots_getD D input rows q (by norm_num) hi,
    slots_getD D input rows q (by norm_num) hi]
  simp [tupleSlot]

/-- **`JUMP`'s constraints on every row**: the executed rows' are Lv42's residuals, the padding rows are zero. -/
theorem honest_jump (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) :
    ∀ i < 2 ^ (honestTrace D input rows q).height opJump,
      let col (n : String) : K := ((honestTrace D input rows q).column opJump (colIdx jumpColumns n)).getD i 0
      col "b" + col "v_cond" * col "w" = 0 ∧ col "v_cond" * (col "b" + 1) = 0 := by
  intro i hi
  show ((honestTrace D input rows q).column 4 13).getD i 0 +
      ((honestTrace D input rows q).column 4 5).getD i 0 * ((honestTrace D input rows q).column 4 12).getD i 0 = 0 ∧
    ((honestTrace D input rows q).column 4 5).getD i 0 * (((honestTrace D input rows q).column 4 13).getD i 0 + 1)
      = 0
  obtain ⟨x, hx, rfl⟩ := exists_rowPosition D rows hfit (by norm_num : 4 < 6) hi
  have hcell : ∀ c, c = 5 ∨ c = 12 ∨ c = 13 →
      ((honestTrace D input rows q).column 4 c).getD
          (rowPosition (rows.getD 4 0) (D.shape.heights.getD 4 0) x) 0 =
        lv42TableCell D rows q ⟨4, by norm_num⟩ c x := by
    rintro c (rfl | rfl | rfl) <;>
      exact (cell_rowPosition' D input rows q hfit 4 (by norm_num) (by decide +kernel) hx).trans
        (Domain.ite_neg_of fun h ↦ absurd h.1 (by decide +kernel))
  rw [hcell 5 (by simp), hcell 12 (by simp), hcell 13 (by simp)]
  by_cases hxc : x < rows.getD 4 0
  · have hxt : x < 2 ^ (D.inst rows).τ (opIdx ⟨4, by norm_num⟩) := by
      rw [tau_opIdx D rows hfit 4 (by norm_num)]
      exact hx
    exact jump_constraints ((D.inst rows).row q (opIdx ⟨4, by norm_num⟩) ⟨x, hxt⟩)
      (fun c ↦ lv42TableCell D rows q ⟨4, by norm_num⟩ c x)
      (fun i ↦ (lv42TableCell_eq D rows q ⟨4, by norm_num⟩ i.isLt hxt).symm)
      (fun C hC ↦ hrel.1.1 (opIdx ⟨4, by norm_num⟩) C hC ⟨x, hxt⟩)
  · rw [lv42TableCell_cases D input rows q hfit hrel 4 (by norm_num) (c := 5) (by decide +kernel) hx,
      lv42TableCell_cases D input rows q hfit hrel 4 (by norm_num) (c := 12) (by decide +kernel) hx,
      lv42TableCell_cases D input rows q hfit hrel 4 (by norm_num) (c := 13) (by decide +kernel) hx]
    simp only [hxc, ite_false]
    have h0 : ∀ c (hc : c < width (opIdx ⟨4, by norm_num⟩)), padRow (opIdx ⟨4, by norm_num⟩) ⟨c, hc⟩ = 0 :=
      fun c hc ↦ padRow_of_not_isLimb ⟨4, by norm_num⟩ ⟨c, hc⟩ fun h ↦
        absurd (congrArg Fin.val h.1) (by simp [opIdx])
    rw [h0, h0, h0]
    simp

/-- A product of nonzero factors is nonzero. -/
theorem foldl_mul_ne_zero (f : ℕ → K) :
    ∀ (l : List ℕ) (acc : K), acc ≠ 0 → (∀ c ∈ l, f c ≠ 0) → l.foldl (fun acc c ↦ acc * f c) acc ≠ 0
  | [], _, h, _ => h
  | c :: l, acc, h, hf => by
    rw [List.foldl_cons]
    exact foldl_mul_ne_zero f l _ (mul_ne_zero h (hf c List.mem_cons_self))
      fun d hd ↦ hf d (List.mem_cons_of_mem _ hd)

/-- **Every counter is nonzero on every row**: Lv42's `CountsNonzero` on the executed rows, `1` on the
padding rows. -/
theorem honest_counters (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) :
    ∀ t < 6, ∀ i < 2 ^ (honestTrace D input rows q).height t,
      (tables.getD t default).countColumns.foldl
        (fun acc c ↦ acc * ((honestTrace D input rows q).column t c).getD i 0) 1 ≠ 0 := by
  intro t ht i hi
  obtain ⟨x, hx, rfl⟩ := exists_rowPosition D rows hfit ht hi
  refine foldl_mul_ne_zero _ _ _ one_ne_zero fun c hcm ↦ ?_
  have hcw : c < (tables.getD t default).width := by
    have := hcm
    simp only [Table.countColumns, List.mem_filter, List.mem_range] at this
    exact this.1
  rw [cell_rowPosition' D input rows q hfit t ht hcw hx]
  split_ifs with h1
  · exact one_ne_zero
  · have hxc : x < rows.getD t 0 := by
      by_contra hn
      exact h1 ⟨hcm, hn⟩
    have hc' : c < width (opIdx ⟨t, ht⟩) := by
      have h := tables_width ⟨t, ht⟩
      have h' : (tables.getD t default).width = width (opIdx ⟨t, ht⟩) := h
      omega
    rw [lv42TableCell_cases D input rows q hfit hrel t ht hc' hx]
    simp only [hxc, ite_true]
    have hcnt : (tables.getD t default).countColumns = (counts (opIdx ⟨t, ht⟩)).map Fin.val :=
      countColumns_eq ⟨t, ht⟩
    rw [hcnt] at hcm
    obtain ⟨k, hk, hkc⟩ := List.mem_map.mp hcm
    have hkk : k = ⟨c, hc'⟩ := Fin.ext hkc
    subst hkk
    exact hrel.1.2.2.1 (opIdx ⟨t, ht⟩) _ hk _ hxc

/-- `BLAKE2S`'s limb columns are not counters. -/
theorem limb_not_counter : ∀ c : Fin 37, 9 ≤ c.val → c.val < 27 →
    c.val ∉ (tables.getD 5 default).countColumns := by
  decide +kernel

/-- **`BLAKE2S`'s limbs are `q_flock`'s slots**, row by row. -/
theorem honest_copies (hfit : D.shape.RowsFit rows) :
    ∀ i < 2 ^ (honestTrace D input rows q).height opBlake2s, ∀ c < blake2sColumns.length, ∀ slot,
      qflockSlot (blake2sColumns.getD c "") = some slot →
        ((honestTrace D input rows q).column opBlake2s c).getD i 0 =
          (honestTrace D input rows q).qflock.getD (slot + 256 * i) 0 := by
  intro i hi c hc slot hslot
  have hc37 : c < 37 := hc
  obtain ⟨⟨h9, h27⟩, rfl⟩ := qflockSlot_eq ⟨c, hc37⟩ slot hslot
  have h9' : 9 ≤ c := h9
  have h27' : c < 27 := h27
  obtain ⟨k, rfl⟩ : ∃ k, c = 9 + k := ⟨c - 9, by omega⟩
  have hk : k < 18 := by omega
  have hkk : (⟨9 + k - 9, by omega⟩ : Fin 18) = ⟨k, hk⟩ := Fin.ext (by simp)
  rw [hkk]
  show ((honestTrace D input rows q).column 5 (9 + k)).getD i 0 = _
  obtain ⟨x, hx, rfl⟩ := exists_rowPosition D rows hfit (by norm_num : 5 < 6) hi
  have hcw : 9 + k < (tables.getD 5 default).width := by
    show 9 + k < 37
    omega
  rw [cell_rowPosition' D input rows q hfit 5 (by norm_num) hcw hx,
    Domain.ite_neg_of fun h ↦ limb_not_counter ⟨9 + k, hc37⟩ h9 h27 h.1,
    qflock_getD D input rows q hfit (Blake2sFlock.blake2sFlockSpec.slot ⟨k, hk⟩).isLt hx]
  have hxt : x < 2 ^ (D.sizes rows).τ 5 := by
    rw [tau_eq D rows hfit 5]
    exact hx
  rw [lv42TableCell, mdif_pos (show 9 + k < width (opIdx ⟨5, by norm_num⟩) from (show 9 + k < width (opIdx 5) by rw [width_blake2s]; omega))]
  exact limb_eq_flock D rows q ⟨k, hk⟩ hxt

/-- **The public lines**: Lv42's `PublicLinesHold`, the words `publicInputOf`'s, the verifier's. -/
theorem honest_publicLines (hrel : D.HonestRelation rows input q) :
    let tr := honestTrace D input rows q
    (tr.memory.getD 0 #[]).getD 0 0 = publicK tr 0 ∧ (tr.memory.getD 0 #[]).getD 1 0 = publicK tr 2 ∧
      (tr.memory.getD 1 #[]).getD 0 0 = publicK tr 1 ∧ (tr.memory.getD 1 #[]).getD 1 0 = publicK tr 3 ∧
      (tr.memory.getD 2 #[]).getD 0 0 = 0 ∧ (tr.memory.getD 2 #[]).getD 1 0 = 0 := by
  intro tr
  have h0 : 0 < 2 ^ D.shape.logMemory := Nat.two_pow_pos _
  have h1 : 1 < 2 ^ D.shape.logMemory := Nat.one_lt_two_pow D.logMemory_pos.ne'
  have hl := hrel.1.2.2.2.1
  have l0 := hl _ (List.mem_cons_self)
  have l1 := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have l2 := hl _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (memory_cell D input rows q (by norm_num) h0).trans l0.1
  · exact (memory_cell D input rows q (by norm_num) h1).trans l0.2
  · exact (memory_cell D input rows q (by norm_num) h0).trans l1.1
  · exact (memory_cell D input rows q (by norm_num) h1).trans l1.2
  · exact (memory_cell D input rows q (by norm_num) h0).trans l2.1
  · exact (memory_cell D input rows q (by norm_num) h1).trans l2.2

/-- Two columns whose blocks `t` and `t'` agree cell by cell have the same Boolean block. -/
theorem batchBlock_bitTable_eq {κ κ' : ℕ} (c : Column (Lv42.Parameters.Flock.kIn + κ))
    (c' : Column (Lv42.Parameters.Flock.kIn + κ')) (t : Fin (2 ^ κ)) (t' : Fin (2 ^ κ'))
    (h : ∀ jin : Fin (2 ^ Lv42.Parameters.Flock.kIn), c.values.get (cubeIndex jin t) = c'.values.get (cubeIndex jin t')) :
    BlockR1CS.batchBlock (bitTable c) t = BlockR1CS.batchBlock (bitTable c') t' := by
  apply Vector.ext
  intro j hj
  simp only [BlockR1CS.batchBlock, bitTable, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta, h]

/-- **Flock's R1CS holds of `q_flock`**, block by block: block `rowPosition x` is Lv42's `QFLOCK` block `x`. -/
theorem honest_flock (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) :
    BlockR1CS.BatchHolds Blake2sFlock.blake2sFlockSpec.r1cs Lv42.Parameters.Flock.constPos
      (bitTable (qflockColumn (honestTrace D input rows q))) := by
  have haux := hrel.1.2.2.2.2 (flockRegion D.prog (D.sizes rows) Blake2sFlock.blake2sFlockSpec) rfl
  intro t
  have hB := tau_eq D rows hfit 5
  obtain ⟨x, hx, hxt⟩ := exists_rowPosition D rows hfit (by norm_num : 5 < 6) t.isLt
  have hxτ : x < 2 ^ (D.sizes rows).τ 5 := by rw [hB]; exact hx
  have hblock : BlockR1CS.batchBlock (bitTable (qflockColumn (honestTrace D input rows q))) t =
      BlockR1CS.batchBlock (bitTable ((D.inst rows).flockColumn
        (flockRegion D.prog (D.sizes rows) Blake2sFlock.blake2sFlockSpec) q)) ⟨x, hxτ⟩ := by
    refine batchBlock_bitTable_eq _ _ _ _ fun jin ↦ ?_
    have hw : jin.val + 256 * x < 2 ^ kappa D.prog (D.sizes rows) flockCol := by
      show _ < 2 ^ (8 + (D.sizes rows).τ 5)
      have := jin.isLt
      rw [pow_add]
      norm_num at this ⊢
      omega
    have hq := qflock_getD D input rows q hfit jin.isLt hx
    rw [hxt] at hq
    simp only [qflockColumn, Vector.get_ofFn, cubeIndex_val]
    rw [show 2 ^ Lv42.Parameters.Flock.kIn * t.val = 256 * t.val from rfl, hq, lv42Cell_eq D rows q _ hw]
    simp only [Lv42.Protocol.M3Instance.flockColumn, Vector.get_eq_getElem, Vector.getElem_cast]
    rfl
  rw [hblock]
  exact haux ⟨x, hxτ⟩

/-! ### The mapping's theorem -/

/-- **The honest prover's placed trace is honest**: from Lv42's `M3Honest` stack at row counts that fit the
shape, `honestTrace` has every property of `TraceHonest`. -/
theorem honestTrace_honest (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) :
    TraceHonest (honestTrace D input rows q) where
  valid := D.valid
  rowsFit := hfit
  tablesSize := honest_tablesSize D input rows q
  memorySize := honest_memorySize D input rows q
  bytecodeSize := by rw [bytecodeFinal_eq]; exact Array.size_ofFn
  qflockSize := qflock_size D input rows q
  slotsSize := honest_slotsSize D input rows q
  slotsFixed := honest_slotsFixed D input rows q
  publicSize := by simp [honestTrace]
  jump := honest_jump D input rows q hfit hrel
  counters := honest_counters D input rows q hfit hrel
  copies := honest_copies D input rows q hfit
  publicLines := honest_publicLines D input rows q hrel
  bus := bus_perm D input rows q hfit hrel.1.2.1
  flock := honest_flock D input rows q hfit hrel

/-! ### The bad bus challenges -/

/-- A fingerprint is its challenge plus its weighted sum. -/
theorem fpOf_eq (weights : Array E) (beta : E) (tau : List E) : fpOf weights beta tau = beta + fpOf weights 0 tau := by
  simp only [fpOf]
  rw [foldl_add_shift (fun s ↦ weights.getD s 0 * tau.getD s 0), foldl_add_shift (fun s ↦ weights.getD s 0 *
    tau.getD s 0), zero_add]

/-- **At most one bad challenge per divided tuple**: for every `α`, the `β` that make some divided fingerprint
vanish are at most `(dividedTuples tr).length`. -/
theorem badFp_card (tr : Trace) (alphas : List E) [Fintype E] [DecidablePred (BadFp tr alphas)] :
    (Finset.univ.filter (BadFp tr alphas)).card ≤ (dividedTuples tr).length := by
  classical
  refine (Finset.card_le_card (t := ((dividedTuples tr).map fun tau ↦
    -fpOf (eqKernel alphas) 0 tau).toFinset) fun beta hb ↦ ?_).trans ((List.toFinset_card_le _).trans_eq (List.length_map _))
  obtain ⟨tau, htau, h0⟩ := (Finset.mem_filter.mp hb).2
  rw [fpOf_eq] at h0
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨tau, htau, (neg_eq_of_add_eq_zero_left h0)⟩

/-- The pulls of each table: `[5, 5, 3, 5, 5, 11]`. -/
def pulls (t : ℕ) : ℕ := (tables.getD t default).flushes.pull.length

theorem pulls_eq : (List.range 6).map pulls = [5, 5, 3, 5, 5, 11] := by decide +kernel

/-- **The number of divided tuples**: each table's pulls over its active rows, the memory's cells, the
bytecode's instructions. -/
theorem dividedTuples_length (tr : Trace) :
    (dividedTuples tr).length =
      ((List.range 6).map fun t ↦ pulls t * (activeRows tr t).length).sum +
        2 ^ tr.shape.logMemory + 2 ^ tr.shape.logBytecode := by
  simp only [dividedTuples, List.length_append, List.length_flatMap, List.length_map, List.length_range,
    List.map_const', List.sum_replicate, smul_eq_mul, pulls]

/-- A table's active rows are its row count, when it fits its height. -/
theorem activeRows_length (tr : Trace) (t : ℕ) (h : tr.rows.getD t 0 ≤ 2 ^ tr.height t) :
    (activeRows tr t).length = tr.rows.getD t 0 := by
  have hnd : ((List.range (tr.rows.getD t 0)).map (rowPosition (tr.rows.getD t 0) (tr.height t))).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy ↦ ?_) List.nodup_range
    exact Domain.rowPosition_injOn h (Set.mem_Iio.mpr (lt_of_lt_of_le (List.mem_range.mp hx) h))
      (Set.mem_Iio.mpr (lt_of_lt_of_le (List.mem_range.mp hy) h)) hxy
  have hp : (activeRows tr t).Perm
      ((List.range (tr.rows.getD t 0)).map (rowPosition (tr.rows.getD t 0) (tr.height t))) := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd).mpr fun i ↦ ?_
    show i ∈ (List.range _).filter _ ↔ _
    simp only [List.mem_filter, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨hi, ha⟩
      obtain ⟨x, hx, rfl⟩ := (Domain.rowPosition_bijOn h).surjOn (Set.mem_Iio.mpr hi)
      rw [Domain.isActive_rowPosition h (Set.mem_Iio.mp hx), decide_eq_true_eq] at ha
      exact ⟨x, ha, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Domain.rowPosition_lt h (lt_of_lt_of_le hx h), ?_⟩
      rw [Domain.isActive_rowPosition h (lt_of_lt_of_le hx h), decide_eq_true_eq]
      exact hx
  rw [hp.length_eq, List.length_map, List.length_range]

/-- **The divided tuples' bound from the row counts**: `Σ_t pulls_t · rows_t + 2^lm + 2^lb`. -/
def dividedBound (shape : UniStatement.Shape) (rows : List ℕ) : ℕ :=
  ((List.range 6).map fun t ↦ pulls t * rows.getD t 0).sum + 2 ^ shape.logMemory + 2 ^ shape.logBytecode

/-- The divided tuples' bound of a shape: every table full. -/
def capBound (shape : UniStatement.Shape) : ℕ := dividedBound shape ((List.range 6).map fun t ↦ 2 ^ shape.heights.getD t 0)

/-- **Under `RowsFit`, the divided tuples are `dividedBound`.** -/
theorem dividedTuples_length_eq (tr : Trace) (h : tr.shape.RowsFit tr.rows) :
    (dividedTuples tr).length = dividedBound tr.shape tr.rows := by
  rw [dividedTuples_length, dividedBound]
  congr 3
  refine List.map_congr_left fun t ht ↦ ?_
  rw [activeRows_length tr t (h.2 t (List.mem_range.mp ht)).2]

/-- **`dividedBound` is at most `capBound`**, under `RowsFit`. -/
theorem dividedBound_le (shape : UniStatement.Shape) (rows : List ℕ) (h : shape.RowsFit rows) :
    dividedBound shape rows ≤ capBound shape := by
  unfold capBound dividedBound
  have hs : ((List.range 6).map fun t ↦ pulls t * rows.getD t 0).sum ≤
      ((List.range 6).map fun t ↦
        pulls t * ((List.range 6).map fun t ↦ 2 ^ shape.heights.getD t 0).getD t 0).sum := by
    refine List.sum_le_sum fun t ht ↦ Nat.mul_le_mul_left _ ?_
    have hi := List.mem_range.mp ht
    rw [List.getD_eq_getElem ((List.range 6).map fun t ↦ 2 ^ shape.heights.getD t 0) 0 (by simpa using hi), List.getElem_map, List.getElem_range]
    exact (h.2 t hi).2
  omega

/-- The reference shape's bound: `10,878,976 < 2^24`. -/
theorem capBound_reference : capBound UniStatement.reference = 10878976 := by decide +kernel

/-- **The bad challenges of an honest trace**, at most `capBound` of its shape. -/
theorem badFp_card_honest (tr : Trace) (h : TraceHonest tr) (alphas : List E) [Fintype E]
    [DecidablePred (BadFp tr alphas)] :
    (Finset.univ.filter (BadFp tr alphas)).card ≤ capBound tr.shape :=
  (badFp_card tr alphas).trans
    ((dividedTuples_length_eq tr h.rowsFit).le.trans (dividedBound_le tr.shape tr.rows h.rowsFit))

end UniComplete.Mapping

/-- info: 'UniComplete.Mapping.honestTrace_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.honestTrace_honest

/-- info: 'UniComplete.Mapping.badFp_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.badFp_card

/-- info: 'UniComplete.Mapping.dividedTuples_length_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.dividedTuples_length_eq

/-- info: 'UniComplete.Mapping.dividedBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.dividedBound_le

/-- info: 'UniComplete.Mapping.capBound_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.capBound_reference

/-- info: 'UniComplete.Mapping.badFp_card_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.badFp_card_honest

/-- info: 'UniComplete.Mapping.rowBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.rowBridge

/-- info: 'UniComplete.Mapping.bus_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.bus_perm

/-- info: 'UniComplete.Mapping.tau_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Mapping.tau_eq
