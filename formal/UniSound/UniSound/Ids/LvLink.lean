-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The reading lemmas follow `formal/Lv42`'s
-- `LeanIsa/Complete.lean` (`column_stackOf`, `stackColumn_get`); `rowPosition`'s loop is read as
-- `formal/UniComplete`'s `DomainPositions.lean` reads it (`walk`).
import UniSound.Ids.Bridges
import Lv42.Protocol.LeanIsa.Complete
import Lv42.Arithmetization.Completeness.Satisfied

/-!
# Lv42's relation on `C1`'s Lv42 stack, from the verifier's checks on `C1`

The bridges of `Bridges.lean` about Lv42 (`LvReadBack`, `LvConstraints`, `LvAux`, `LvBusCount`),
proved for every deployment:

* **`rowPosition` stays in its table** (`rowPosition_lt`): Lv42's row `x < 2^⌈log₂ count⌉` sits at
  `C1`'s row `rowPosition count r x < 2^r`, whatever the count (no range check is needed): a non-full
  table's loop only returns rows below `2^r`, and a full one is the identity on `x < 2^r`.
* **Reading** (`lvReadBack`, `limb_lv42Stack`, `table_lv42Stack`, `mem_lv42Stack`,
  `flock_lv42Stack`): a committed column of `lv42Stack` read back through Lv42's layout is
  `lv42Column`'s (Lv42's `column_committed`, then the stack's block is its column, as Lv42's
  `column_stackOf`); a `BLAKE2S` limb `k` at row `x` is `QFLOCK`'s cell `cubeIndex (slot k) x`.
-/

namespace UniSound.Ids

/-! ## `JUMP`'s constraints at a row -/

section JumpRow

open Lv42.Parameters Lv42.Semantics Lv42.Arithmetization LeanVM.Parameters
open Air.Flat (Component)

/-- The `JUMP` table has fourteen columns. -/
theorem jump_width : (Lv42.Protocol.LeanIsa.opcodeComponent 4).width = 14 := by decide +kernel

/-- A `JUMP` row has twelve columns before its two local witnesses. -/
theorem jumpRow_size : size JumpRow = 12 := rfl

/-- **`JUMP`'s Clean constraints hold at a row of fourteen cells** whose cells `13, 5, 12`
(`b`, `v_cond`, `w`, as `jumpColumns` names them) satisfy `b + v_cond·w = 0` and `v_cond·(b + 1) = 0`
(Lv42's `jump_constraints_iff`, the row read by its cells). -/
theorem jump_constraintsHold (row : Fin (Lv42.Protocol.LeanIsa.opcodeComponent 4).width → K)
    (data : ProverData K)
    (h1 : row ⟨13, by rw [jump_width]; omega⟩ + row ⟨5, by rw [jump_width]; omega⟩ *
      row ⟨12, by rw [jump_width]; omega⟩ = 0)
    (h2 : row ⟨5, by rw [jump_width]; omega⟩ * (row ⟨13, by rw [jump_width]; omega⟩ + 1) = 0) :
    (⟨jumpTable⟩ : Component K).operations.ConstraintsHold
      (Environment.fromArray (Array.ofFn row) data) := by
  rw [Component.constraintsHold_iff, Component.rowOperations_mk]
  have hget : ∀ (i : ℕ) (hi : i < 14), (Environment.fromArray (Array.ofFn row) data).get i =
      row ⟨i, by rw [jump_width]; exact hi⟩ := by
    intro i hi
    show ((Array.ofFn row)[i]?).getD 0 = _
    rw [Array.getElem?_ofFn]
    simp [jump_width, hi]
  have hv : (eval (Environment.fromArray (Array.ofFn row) data)
      (varFromOffset JumpRow 0 : Var JumpRow K)).vcond =
        (Environment.fromArray (Array.ofFn row) data).get 5 := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm]
  refine (jump_constraints_iff (varFromOffset JumpRow 0) (Environment.fromArray (Array.ofFn row) data)
    (size JumpRow) _ rfl ((Environment.fromArray (Array.ofFn row) data).get 12)
    ((Environment.fromArray (Array.ofFn row) data).get 13) (by rw [jumpRow_size])
    (by rw [jumpRow_size])).mpr ?_
  rw [hv, hget 5 (by omega), hget 12 (by omega), hget 13 (by omega)]
  exact ⟨h1, h2⟩

end JumpRow

open LeanVM.Parameters UniStatement
open Lv42.Protocol.LeanIsa (Col IsLimb kappa blocks stackOrder leanIsaμ blockOf flockCol limbCol memCol
  opIdx opcodeTable opcodeComponent)
open Lv42.Protocol.Blake2sFlock (blake2sFlockSpec)
open Lv42.Semantics (Program)

/-! ## `rowPosition` stays in its table -/

private theorem ite_neg_of' {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by
  simp [h]

/-- `rowPosition`'s loop as a recursion over the bits `bs` (`r − 1, …, 0`), its state `(answer, y)`. -/
def rpWalk (count r : ℕ) (v : Bool) : List ℕ → ℕ → Option ℕ × ℕ
  | [], y => (none, y)
  | b :: bs, y =>
    if count.testBit b = v then
      if y < 2 ^ b then (some (2 ^ r - 2 ^ (b + 1) + y), y) else rpWalk count r v bs (y - 2 ^ b)
    else rpWalk count r v bs y

/-- An answer of the walk over bits below `r` is below `2^r`. -/
theorem rpWalk_lt (count r : ℕ) (v : Bool) : ∀ (bs : List ℕ) (y p : ℕ), (∀ b ∈ bs, b < r) →
    (rpWalk count r v bs y).1 = some p → p < 2 ^ r
  | [], y, p, _, h => by simp [rpWalk] at h
  | b :: bs, y, p, hb, h => by
    have hbr : b < r := hb b (List.mem_cons_self ..)
    have hbs : ∀ b' ∈ bs, b' < r := fun b' hb' ↦ hb b' (List.mem_cons_of_mem _ hb')
    rw [rpWalk] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h
      subst h
      have h3 : 2 ^ (b + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hbr
      have h4 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ, mul_comm]
      omega
    · exact rpWalk_lt count r v bs _ p hbs h
    · exact rpWalk_lt count r v bs _ p hbs h

/-- **The `for` loop of `rowPosition` is `rpWalk`** over the reversed indices. -/
theorem forIn_rpWalk (count r : ℕ) (v : Bool) (F : ℕ → Option ℕ × ℕ → Id (ForInStep (Option ℕ × ℕ)))
    (hF : ∀ i s, F i s = if (count.testBit (r - 1 - i) == v) = true then
        (if s.2 < 2 ^ (r - 1 - i) then pure (ForInStep.done (some (2 ^ r - 2 ^ (r - 1 - i + 1) + s.2), s.2))
          else pure (ForInStep.yield (none, s.2 - 2 ^ (r - 1 - i))))
        else pure (ForInStep.yield (none, s.2)))
    (L : List ℕ) (y : ℕ) :
    forIn L ((none : Option ℕ), y) F =
      (rpWalk count r v (L.map fun i ↦ r - 1 - i) y : Id (Option ℕ × ℕ)) := by
  induction L generalizing y with
  | nil => rfl
  | cons i L ih =>
    rw [List.forIn_cons, hF, List.map_cons, rpWalk]
    simp only [beq_iff_eq]
    split_ifs with h1 h2
    · rfl
    · exact ih _
    · exact ih _

private theorem range'_map_reverse' (r : ℕ) :
    (List.range' 0 r).map (fun i ↦ r - 1 - i) = (List.range r).reverse := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range', List.getElem_reverse, List.getElem_range,
      List.length_range]
    omega

/-- **`rowPosition` of a non-full table**, by its loop. -/
theorem rowPosition_of_ne' {count r : ℕ} (hf : count ≠ 2 ^ r) (x : ℕ) :
    rowPosition count r x =
      ((rpWalk count r (decide (x < count)) (List.range r).reverse
        (if x < count then x else x - count)).1).getD (2 ^ r - 1) := by
  unfold rowPosition
  simp only [Id.run, ite_neg_of' hf]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_rpWalk count r (decide (x < count)) _ (fun _ _ ↦ rfl)]
  have hsize : (Std.Legacy.Range.mk 0 r 1 (by omega)).size = r := by
    simp [Std.Legacy.Range.size]
  have hL := range'_map_reverse' r
  simp only [decide_eq_true_eq]
  rw [hsize, hL]
  rcases rpWalk count r (decide (x < count)) (List.range r).reverse (if x < count then x else x - count) with
    ⟨_ | v, y'⟩ <;> rfl

theorem rowPosition_full' (r x : ℕ) : rowPosition (2 ^ r) r x = x := by
  unfold rowPosition
  simp only [Id.run]
  rfl

/-- A non-full table's `rowPosition` is below `2^r`, at every `x`. -/
theorem rowPosition_lt_of_ne {count r : ℕ} (hf : count ≠ 2 ^ r) (x : ℕ) : rowPosition count r x < 2 ^ r := by
  rw [rowPosition_of_ne' hf]
  cases h : (rpWalk count r (decide (x < count)) (List.range r).reverse
      (if x < count then x else x - count)).1 with
  | none => exact Nat.sub_lt (Nat.two_pow_pos r) one_pos
  | some p =>
    exact rpWalk_lt count r _ _ _ p (fun b hb ↦ List.mem_range.mp (List.mem_reverse.mp hb)) h

/-- **`rowPosition` stays in its table**: Lv42's row `x < 2^⌈log₂ count⌉` is `C1`'s row
`rowPosition count r x < 2^r`, whatever `count` (for `count ≠ 2^r` at every `x`; for `count = 2^r` the
identity on `x < 2^r`). -/
theorem rowPosition_lt {count r x : ℕ} (hx : x < 2 ^ Nat.clog 2 count) : rowPosition count r x < 2 ^ r := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [rowPosition_full']
    rwa [Nat.clog_pow 2 r (by norm_num)] at hx
  · exact rowPosition_lt_of_ne hf x

/-! ## Reading `C1`'s Lv42 stack -/

section Read

variable (prog : Program) (s : Lv42.Protocol.LeanIsa.Sizes) (shape : UniStatement.Shape) (stack : ℕ → K)

/-- A cell of a stack inside a block's window is the block's cell (`LeanIsa.Complete`'s private
`stackColumn_get`). -/
private theorem stackColumn_get' (t : (blocks prog s).Tables K) (b : Fin (blocks prog s).n)
    (x : Fin (2 ^ (blocks prog s).size b)) :
    ((blocks prog s).stackColumn t (leanIsaμ prog s)).values[x.val + (blocks prog s).offset b]'(by
      have := (blocks prog s).offset_add_pow_le_total b
      have := Lv42.Protocol.LeanIsa.blocks_fits prog s
      have := x.isLt
      omega) = (t b)[x] := by
  rw [← (blocks prog s).unstack_getElem (Lv42.Protocol.LeanIsa.blocks_fits prog s) _ b x.isLt]
  exact congrArg (·[x]) ((blocks prog s).unstack_stackAt t (Lv42.Protocol.LeanIsa.blocks_fits prog s) 0 b)

private theorem lv42Column_congr {c c' : Col} (h : c' = c) (x : Fin (2 ^ kappa prog s c')) :
    (lv42Column prog s shape stack c')[x] =
      (lv42Column prog s shape stack c)[(Fin.cast (by rw [h]) x : Fin (2 ^ kappa prog s c))] := by
  subst h
  rfl

/-- **A committed column of `C1`'s Lv42 stack is `lv42Column`'s.** -/
theorem column_lv42Stack (c : Col) (h : ¬ IsLimb c) (x : Fin (2 ^ kappa prog s c)) :
    ((Lv42.Protocol.leanIsaInstance blake2sFlockSpec prog s).column (lv42Stack prog s shape stack) c).values.get x =
      (lv42Column prog s shape stack c).get x := by
  refine (Lv42.Protocol.LeanIsa.column_committed _ prog s _ c h x).trans ?_
  have hsz := Lv42.Protocol.LeanIsa.size_blockOf prog s c h
  have hx : x.val < 2 ^ (blocks prog s).size (blockOf c h) := by rw [hsz]; exact x.isLt
  refine (stackColumn_get' prog s _ (blockOf c h) ⟨x.val, hx⟩).trans ?_
  exact lv42Column_congr prog s shape stack (Lv42.Protocol.LeanIsa.stackOrder_blockOf prog s c h) _

/-- **A `BLAKE2S` limb of `C1`'s Lv42 stack** at row `x` is `lv42Column`'s `QFLOCK` at
`cubeIndex (slot k) x`. -/
theorem limb_lv42Stack (k : Fin 18) (x : Fin (2 ^ s.τ 5)) :
    ((Lv42.Protocol.leanIsaInstance blake2sFlockSpec prog s).column (lv42Stack prog s shape stack)
        (limbCol k)).values.get x =
      (lv42Column prog s shape stack flockCol).get
        (LeanVM.Protocol.cubeIndex (k := 8) (blake2sFlockSpec.slot k) x) :=
  (Lv42.Protocol.LeanIsa.column_limb _ prog s _ k x).trans
    ((Lv42.Protocol.LeanIsa.column_committed _ prog s _ flockCol
        Lv42.Protocol.LeanIsa.not_isLimb_flockCol
        (LeanVM.Protocol.cubeIndex (blake2sFlockSpec.slot k) x)).symm.trans
      (column_lv42Stack prog s shape stack flockCol Lv42.Protocol.LeanIsa.not_isLimb_flockCol _))

/-- An opcode table's committed cell: `C1`'s value at `rowPosition`. -/
theorem table_lv42Stack (j : Fin 6) (i : Fin (Lv42.Protocol.LeanIsa.width (opIdx j)))
    (h : ¬ IsLimb ⟨opIdx j, i⟩) (x : Fin (2 ^ kappa prog s ⟨opIdx j, i⟩)) :
    ((Lv42.Protocol.leanIsaInstance blake2sFlockSpec prog s).column (lv42Stack prog s shape stack)
        ⟨opIdx j, i⟩).values.get x =
      basisValue (c1Block (c1Layout shape) stack (.table j.val i.val)) (shape.heights.getD j.val 0)
        (rowPosition (s.rows j) (shape.heights.getD j.val 0) x.val) := by
  refine (column_lv42Stack prog s shape stack ⟨opIdx j, i⟩ h x).trans ?_
  exact Vector.get_ofFn _ _

/-- A memory column's cell: `C1`'s value. -/
theorem mem_lv42Stack (k : Fin 4) (x : Fin (2 ^ s.logMem)) :
    ((Lv42.Protocol.leanIsaInstance blake2sFlockSpec prog s).column (lv42Stack prog s shape stack)
        (memCol k)).values.get x =
      basisValue (c1Block (c1Layout shape) stack (.memory k.val)) s.logMem x.val := by
  refine (column_lv42Stack prog s shape stack (memCol k) (fun hk ↦ by
    have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this) x).trans ?_
  exact Vector.get_ofFn _ _

/-- `QFLOCK`'s cell: `q_flock`'s word at the instance's `rowPosition`. -/
theorem flock_lv42Stack (x : Fin (2 ^ (8 + s.τ 5))) :
    ((Lv42.Protocol.leanIsaInstance blake2sFlockSpec prog s).column (lv42Stack prog s shape stack)
        flockCol).values.get x =
      (c1Block (c1Layout shape) stack .qflock).getD
        (x.val % 256 + 256 * rowPosition (s.rows 5) (shape.heights.getD 5 0) (x.val / 256)) 0 := by
  refine (column_lv42Stack prog s shape stack flockCol Lv42.Protocol.LeanIsa.not_isLimb_flockCol x).trans ?_
  exact Vector.get_ofFn _ _

end Read

/-- **Lv42's columns of `C1`'s Lv42 stack are `lv42Column`'s.** -/
theorem lvReadBack (D : Deployment) : LvReadBack D := fun rows c col hcol x ↦
  column_lv42Stack D.prog (D.sizes rows) D.shape c col hcol x

/-! ## The tables agree -/

/-- **Lv42's count columns are the verifier's** (`Table.countColumns`, the names starting `cnt`), table
by table and in order: the coordinate-`1` variables of the memory and bytecode pulls. -/
theorem counts_eq : ∀ j : Fin 6,
    (opcodeTable j).count.map (·.val) = (tables.getD j.val default).countColumns := by
  decide +kernel

/-- `BLAKE2S`'s count columns are past its limbs. -/
theorem counts_past_limbs : ∀ j : Fin 6, ∀ k ∈ (opcodeTable j).count, j = 5 → 27 ≤ k.val := by
  decide +kernel

/-- A count column is committed (not a `BLAKE2S` limb). -/
theorem counts_not_limb (j : Fin 6) (k : Fin (opcodeTable j).width) (hk : k ∈ (opcodeTable j).count) :
    ¬ IsLimb ⟨opIdx j, k⟩ := fun hl ↦ by
  have h5 : j = 5 := Fin.ext (by have := congrArg Fin.val hl.1; simp [opIdx] at this; omega)
  have h27 := counts_past_limbs j k hk h5
  have hk27 : k.val < 27 := hl.2.2
  omega

/-- **The tables' widths agree**: Lv42's opcode components and the verifier's tables. -/
theorem widths_eq : ∀ j : Fin 6, (opcodeComponent j).width = (tables.getD j.val default).width := by
  decide +kernel

/-- **`JUMP`'s columns**: `b`, `v_cond`, `w` are columns `13, 5, 12`, Lv42's `JumpRow` order with its
witnesses `w, b` last. -/
theorem jump_idx : colIdx jumpColumns "b" = 13 ∧ colIdx jumpColumns "v_cond" = 5 ∧
    colIdx jumpColumns "w" = 12 := by decide

/-- **The limbs' slots agree**: `BLAKE2S`'s column `9 + k` (`blake2sColumns`) is `q_flock`'s slot
`qflockSlot` of its name, Lv42's `blake2sFlockSpec.slot k`. -/
theorem slots_agree : ∀ k : Fin 18,
    qflockSlot (blake2sColumns.getD (9 + k.val) "") = some (blake2sFlockSpec.slot k).val := by
  decide +kernel

/-! ## The constraints, the counts, the public lines -/

section Constraints

variable (D : Deployment) (rows : List ℕ) (c : Stk)

/-- A row of an opcode table of `C1`'s Lv42 stack: `C1`'s values at `rowPosition`. -/
theorem row_lv42Stack (j : Fin 6) (x : Fin (2 ^ (D.sizes rows).τ j))
    (i : Fin (Lv42.Protocol.LeanIsa.width (opIdx j))) (h : ¬ IsLimb ⟨opIdx j, i⟩) :
    (D.inst rows).row (lv42Stack D.prog (D.sizes rows) D.shape c) (opIdx j) x i =
      c1Val D c (.table j.val i.val) (D.shape.heights.getD j.val 0)
        (rowPosition (rows.getD j.val 0) (D.shape.heights.getD j.val 0) x.val) :=
  table_lv42Stack D.prog (D.sizes rows) D.shape c j i h x

/-- **`ConstraintsVanish`** from `JUMP`'s two constraints on every row of `C1` (the other tables have
none, `opcode_constraints_nil`). -/
theorem constraintsVanish_lv42Stack (hjump : ∀ x < 2 ^ D.shape.heights.getD opJump 0,
      c1Val D c (.table opJump 13) (D.shape.heights.getD opJump 0) x +
          c1Val D c (.table opJump 5) (D.shape.heights.getD opJump 0) x *
            c1Val D c (.table opJump 12) (D.shape.heights.getD opJump 0) x = 0 ∧
        c1Val D c (.table opJump 5) (D.shape.heights.getD opJump 0) x *
          (c1Val D c (.table opJump 13) (D.shape.heights.getD opJump 0) x + 1) = 0) :
    (D.inst rows).ConstraintsVanish (lv42Stack D.prog (D.sizes rows) D.shape c) := by
  intro j C hC x
  rcases j with ⟨_ | _ | _ | j, hj⟩
  · exact absurd hC List.not_mem_nil
  · exact absurd hC List.not_mem_nil
  · exact absurd hC List.not_mem_nil
  · have h9 : (D.inst rows).ntab = 9 := rfl
    have hj6 : j < 6 := by omega
    by_cases h4 : j = 4
    · subst h4
      have hpos : rowPosition (rows.getD 4 0) (D.shape.heights.getD opJump 0) x.val <
          2 ^ D.shape.heights.getD opJump 0 := rowPosition_lt (count := rows.getD 4 0) x.isLt
      obtain ⟨h1, h2⟩ := hjump _ hpos
      let row : Fin (opcodeComponent 4).width → K := fun i ↦
        c1Val D c (.table 4 i.val) (D.shape.heights.getD 4 0)
          (rowPosition (rows.getD 4 0) (D.shape.heights.getD 4 0) x.val)
      have hrow : (D.inst rows).row (lv42Stack D.prog (D.sizes rows) D.shape c) ⟨4 + 3, hj⟩ x = row := by
        funext i
        exact row_lv42Stack D rows c 4 x i (fun hl ↦ by have := congrArg Fin.val hl.1; simp [opIdx] at this)
      rw [hrow]
      have hl := List.isEmpty_iff.mp (Lv42.Protocol.LeanIsa.opcode_lookups 4)
      exact (LeanVM.Protocol.toM3_constraints_iff (opcodeComponent 4) Lv42.Arithmetization.channelSep
        Lv42.Arithmetization.channelDir Lv42.Protocol.LeanIsa.counted hl row (fun _ _ ↦ #[])).mpr
          (jump_constraintsHold row _ h1 h2) C hC
    · exact absurd (List.length_pos_of_mem hC) (by
        change ¬ 0 < (opcodeTable ⟨j, hj6⟩).constraints.length
        rw [Lv42.Protocol.LeanIsa.opcode_constraints_nil ⟨j, hj6⟩ (fun h ↦ h4 (congrArg Fin.val h))]
        omega)

/-- **`CountsNonzero`** from the counters' inverse `z·Πc = 1` on every row of `C1`: every count column of
Lv42 is a counter of the verifier's (`counts_eq`), and a factor of a product `1` is nonzero. -/
theorem countsNonzero_lv42Stack (hcnt : ∀ o < 6, ∀ x < 2 ^ D.shape.heights.getD o 0,
    c1Val D c (.inverse o) (D.shape.heights.getD o 0) x *
      ((tables.getD o default).countColumns.map fun j ↦
        c1Val D c (.table o j) (D.shape.heights.getD o 0) x).prod = 1) :
    (D.inst rows).CountsNonzero (lv42Stack D.prog (D.sizes rows) D.shape c) := by
  intro j i hi x _hx
  rcases j with ⟨_ | _ | _ | j, hj⟩
  · exact absurd hi List.not_mem_nil
  · exact absurd hi List.not_mem_nil
  · exact absurd hi List.not_mem_nil
  · have h9 : (D.inst rows).ntab = 9 := rfl
    have hj6 : j < 6 := by omega
    have hmem : i.val ∈ (tables.getD j default).countColumns := by
      rw [← counts_eq ⟨j, hj6⟩]
      exact List.mem_map_of_mem hi
    refine (table_lv42Stack D.prog (D.sizes rows) D.shape c ⟨j, hj6⟩ i
      (counts_not_limb ⟨j, hj6⟩ i hi) x).trans_ne ?_
    intro h0
    have hc := hcnt j hj6 _ (rowPosition_lt (count := rows.getD j 0) x.isLt)
    rw [List.prod_eq_zero (List.mem_map.mpr ⟨i.val, hmem, h0⟩), mul_zero] at hc
    exact zero_ne_one hc

/-- `E`'s zero has a zero base limb. -/
theorem toK_zero : toK (0 : E) = 0 := by
  show (0 : E).limb 0 = 0
  simpa using limb_ofK (0 : K) 0

/-- **`PublicLinesHold`** from the public lines on `C1`: `MEM_LO`'s cells `0, 1` are the words `0, 2`,
`MEM_HI`'s the words `1, 3`, `MEM_TOP`'s zero (`linesOf (publicWordsOf ·)` against `publicInputOf`,
both the calldata's big-endian words). -/
theorem publicLinesHold_lv42Stack (bytes : List UInt8) (hlines : ∀ k < 3,
    c1Val D c (.memory k) D.shape.logMemory 0 = toK ((linesOf (publicWordsOf bytes)).getD k (0, 0)).1 ∧
      c1Val D c (.memory k) D.shape.logMemory 1 = toK ((linesOf (publicWordsOf bytes)).getD k (0, 0)).2) :
    (D.inst rows).PublicLinesHold (publicInputOf bytes) (lv42Stack D.prog (D.sizes rows) D.shape c) := by
  intro l hl
  have hls : ((D.inst rows).publicLines (publicInputOf bytes)).toList =
      [⟨memCol 0, (publicInputOf bytes).lanes 0, (publicInputOf bytes).lanes 2, false,
          (D.sizes rows).logMem_pos⟩,
        ⟨memCol 1, (publicInputOf bytes).lanes 1, (publicInputOf bytes).lanes 3, false,
          (D.sizes rows).logMem_pos⟩,
        ⟨memCol 2, 0, 0, false, (D.sizes rows).logMem_pos⟩] := rfl
  rw [hls] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  have hm : ∀ (k : Fin 4) (x : ℕ) (hx : x < 2 ^ (D.sizes rows).logMem),
      ((D.inst rows).column (lv42Stack D.prog (D.sizes rows) D.shape c) (memCol k)).values.get ⟨x, hx⟩ =
        c1Val D c (.memory k.val) D.shape.logMemory x :=
    fun k x hx ↦ mem_lv42Stack D.prog (D.sizes rows) D.shape c k ⟨x, hx⟩
  rcases hl with rfl | rfl | rfl
  · refine ⟨(hm 0 0 _).trans ((hlines 0 (by norm_num)).1.trans ?_),
      (hm 0 1 _).trans ((hlines 0 (by norm_num)).2.trans ?_)⟩ <;>
      simp [linesOf, publicWordsOf, publicInputOf, toK, eK, eNew]
  · refine ⟨(hm 1 0 _).trans ((hlines 1 (by norm_num)).1.trans ?_),
      (hm 1 1 _).trans ((hlines 1 (by norm_num)).2.trans ?_)⟩ <;>
      simp [linesOf, publicWordsOf, publicInputOf, toK, eK, eNew]
  · refine ⟨(hm 2 0 _).trans ((hlines 2 (by norm_num)).1.trans ?_),
      (hm 2 1 _).trans ((hlines 2 (by norm_num)).2.trans ?_)⟩ <;>
      simp [linesOf, toK_zero]

end Constraints

/-- **The constraints on `C1`'s rows are Lv42's** `ConstraintsVanish`, `CountsNonzero`,
`PublicLinesHold` of `C1`'s Lv42 stack (the counts' range is not needed: `rowPosition_lt`). -/
theorem lvConstraints (D : Deployment) : LvConstraints D := by
  intro s c _ hR
  obtain ⟨hb, hv, hw⟩ := jump_idx
  refine ⟨constraintsVanish_lv42Stack D s.2 c fun x hx ↦ ?_, countsNonzero_lv42Stack D s.2 c hR.counters,
    publicLinesHold_lv42Stack D s.2 c s.1.toList hR.lines⟩
  have h := hR.jump x hx
  rw [hb, hv, hw] at h
  exact h

/-! ## Axioms -/

/-- info: 'UniSound.Ids.lvReadBack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lvReadBack

/-- info: 'UniSound.Ids.limb_lv42Stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms limb_lv42Stack

/-- info: 'UniSound.Ids.lvConstraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lvConstraints

/-- info: 'UniSound.Ids.slots_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slots_agree

end UniSound.Ids
