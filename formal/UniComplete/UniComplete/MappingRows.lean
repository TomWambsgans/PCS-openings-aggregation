-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses `formal/Lv42` (leanerVM `mumbai` f0393df4,
-- MIT OR Apache-2.0): the six tables' sends in closed form (`xor_sends_gen` … `blake2s_sends_gen`,
-- `Arithmetization/Completeness/Messages.lean`).
import UniComplete.MappingBasic

/-!
# The six tables' flushes are Lv42's (milestone 4)

`layout.rs`'s tables (`UniStatement.tables`: each a list of push and pull tuples of `Form`s) and Lv42's
(`LeanIsa.flushes`: Clean's components as polynomials) flush the same tuples on every row: what the differential
runner's `lv42Bridge` tests on random rows, here for every row.

* **The forms with their indices** (`flushes_xor` … `flushes_blake2s`, by `rfl`): each table's flushes, its column
  names resolved (`colIdx`), as the builders of `layout.rs` build them.
* **The bridges** (`bridge_xor` … `bridge_blake2s`): at a row of cells `v` (Lv42's typed row read off them, by
  Clean's `valueFromOffset`), the PIOP's tuples of either side (`sideForms j side`, the forms at the cells) are, in
  order, the tuples the table's Clean component emits on that side (`tuplesOn`), each in `E` (`phi`). Per table:
  Lv42's sends in closed form (`Completeness.Messages`), the bus's view of the six channels (`nameView`), the forms
  term by term (`formE_*`), then a ring identity per slot.
-/

namespace UniComplete.Mapping

open UniStatement LeanVM.Parameters LeanVM.Protocol
open Lv42.Protocol Lv42.Protocol.LeanIsa Lv42.Arithmetization

/-- **The PIOP's tuples of a side** of table `j`. -/
def sideForms (j : ℕ) : Side → List (List Form)
  | .push => (tables.getD j default).flushes.push
  | .pull => (tables.getD j default).flushes.pull

/-! ### The forms with their indices -/

/-- `XOR`'s flushes (`flushes_arith(OP_XOR, false)`), its columns resolved. -/
theorem flushes_xor : (tables.getD 0 default).flushes =
    (((((({ push := [], pull := [] } : Flushes).stateStep 0 1).bytecode 0 14 opXor
      [col 2 0, col 3 0, col 4 0, constant 0, constant 0]).memoryCols (prod 1 2 0) 11 [5, 6, 7]).memoryCols
        (prod 1 3 0) 12 [8, 9, 10]).memory (prod 1 4 0) 13
          [(col 5 0).add (col 8 0), (col 6 0).add (col 9 0), (col 7 0).add (col 10 0)]) := rfl

/-- `MUL_NATIVE`'s flushes (`flushes_arith(OP_MUL, true)`): the tower product's three lanes. -/
theorem flushes_mul : (tables.getD 1 default).flushes =
    (((((({ push := [], pull := [] } : Flushes).stateStep 0 1).bytecode 0 14 opMul
      [col 2 0, col 3 0, col 4 0, constant 0, constant 0]).memoryCols (prod 1 2 0) 11 [5, 6, 7]).memoryCols
        (prod 1 3 0) 12 [8, 9, 10]).memory (prod 1 4 0) 13
          [Form.sum [prod 5 8 0, prod 6 10 0, prod 7 9 0],
            Form.sum [prod 5 9 0, prod 6 8 0, prod 6 10 0, prod 7 9 0, prod 7 10 0],
            Form.sum [prod 5 10 0, prod 6 9 0, prod 7 8 0, prod 7 10 0]]) := rfl

/-- `SET_CONSTANT`'s flushes (`flushes_set()`). -/
theorem flushes_set : (tables.getD 2 default).flushes =
    (((({ push := [], pull := [] } : Flushes).stateStep 0 1).bytecode 0 7 opSet
      [col 2 0, col 3 0, col 4 0, col 5 0, constant 0]).memoryCols (prod 1 2 0) 6 [3, 4, 5]) := rfl

/-- `DEREF`'s flushes (`flushes_deref()`). -/
theorem flushes_deref : (tables.getD 3 default).flushes =
    ((((((({ push := [], pull := [] } : Flushes).stateStep 0 1).bytecode 0 14 opDeref
      [col 2 0, col 3 0, col 4 0, col 5 0, col 6 0]).memoryCols (prod 1 2 0) 11 [7]).memory (prod 7 3 0) 12
        [Form.sum [col 8 0, prod 5 8 0, prod 6 8 0, prod 5 0 2, prod 6 1 0],
          Form.sum [col 9 0, prod 5 9 0, prod 6 9 0], Form.sum [col 10 0, prod 5 10 0, prod 6 10 0]]).memoryCols
      (prod 1 4 0) 13 [8, 9, 10])) := rfl

/-- `JUMP`'s flushes (`flushes_jump()`). -/
theorem flushes_jump : (tables.getD 4 default).flushes =
    (((((({ push := [], pull := [] } : Flushes).stateDerived 0 1
      (((prod 13 6 0).add (prod 13 0 1)).add (col 0 1)) (((prod 13 7 0).add (prod 13 1 0)).add (col 1 0))).bytecode
        0 11 opJump [col 2 0, col 3 0, col 4 0, constant 0, constant 0]).memoryCols (prod 1 2 0) 8 [5]).memoryCols
          (prod 1 3 0) 9 [6]).memoryCols (prod 1 4 0) 10 [7]) := rfl

/-- `BLAKE2S`'s flushes (`flushes_blake2s()`): the nine cells, two limbs each. -/
theorem flushes_blake2s : (tables.getD 5 default).flushes =
    (((((((((((({ push := [], pull := [] } : Flushes).stateStep 0 1).bytecode 0 36 opBlake2s
      [col 2 0, col 3 0, col 4 0, col 5 0, col 6 0, col 7 0, col 8 0]).memoryCols (prod 1 2 0) 27
        [9, 10]).memoryCols (prod 1 3 0) 28 [11, 12]).memoryCols (prod 1 4 0) 29 [13, 14]).memoryCols
          (prod 1 5 0) 30 [15, 16]).memoryCols (prod 1 6 0) 31 [21, 22]).memoryCols (prod 1 6 1) 32
            [23, 24]).memoryCols (prod 1 7 0) 33 [17, 18]).memoryCols (prod 1 7 1) 34 [19, 20]).memoryCols
              (prod 1 8 0) 35 [25, 26]) := rfl

/-! ### The bridge, table by table -/

/-- `ofK` is the algebra map (by definition). -/
theorem ofK_eq_algebraMap (x : K) : ofK x = algebraMap K E x := rfl

/-- A product of two columns in reverse order. -/
theorem formE_prod_ge (col' : ℕ → E) (a b e : ℕ) (h : b ≤ a) :
    formE (prod a b e) col' = ofK g ^ e * (col' b * col' a) := by
  rw [formE_prod, min_eq_right h, max_eq_left h]

/-- The normal form of the two sides of a table's bridge, then a ring identity per slot. -/
macro "bridge_norm" : tactic => `(tactic| (
  simp only [Flushes.stateStep, Flushes.stateDerived, Flushes.pair, Flushes.bytecode, Flushes.counted,
    Flushes.memoryCols, Flushes.memory, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    List.foldl_cons, List.foldl_nil, List.append_assoc, List.filter_cons, List.filter_nil,
    nameView_statePush, nameView_statePull, nameView_memPush, nameView_memPull, nameView_bytecodePush,
    nameView_bytecodePull, decide_true, decide_false, reduceCtorEq, ite_true, ite_false, Bool.false_eq_true]
  simp only [tupleAt_eq, phi_tupleOf, List.length_cons, List.length_nil, List.size_toArray, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceLeDiff, List.toList_toArray]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, formE_constant, formE_col,
    formE_prod_le, formE_prod_ge, formE_add, formE_sum, List.sum_cons, List.sum_nil, sepState_eq, sepMem_eq,
    sepBytecode_eq, gpow_eq, opXor, opMul, opSet, opDeref, opJump, opBlake2s, Lv42.Parameters.Opcode.code,
    LeanVM.Parameters.gpow, ofK_eq_algebraMap, map_add, map_mul, map_pow, map_one, map_zero,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, pow_zero,
    pow_one, one_mul, mul_one, add_zero, zero_add, Nat.reduceLeDiff]
  try simp only [List.cons.injEq, and_true, true_and, List.replicate_succ, List.replicate_zero]
  all_goals (try and_intros)
  all_goals first | ring1 | (ring_nf; simp only [map_one]; ring1) | (ring_nf; simp only [map_one]; done)))

set_option linter.unusedSimpArgs false

/-- **`XOR`'s bridge.** -/
theorem bridge_xor (v : ℕ → K) (data : ProverData K) (side : Side) :
    (sideForms 0 side).map (tupleAt · fun c ↦ ofK (v c)) =
      (tuplesOn ((opcodeComponent 0).operations.interactionValues
        (Environment.fromArray (Array.ofFn fun i : Fin 15 ↦ v i) data)) side).map phi := by
  have hx : Eval.eval (Environment.fromArray (Array.ofFn fun i : Fin 15 ↦ v i) data)
      (varFromOffset XorRow 0 : Var XorRow K) =
      (⟨v 0, v 1, v 2, v 3, v 4, #v[v 5, v 6, v 7], #v[v 8, v 9, v 10], v 11, v 12, v 13, v 14⟩ :
        XorRow K) := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn]
  rw [tuplesOn_eq, Air.Flat.Component.interactionsValues_eq,
    show (opcodeComponent 0).rowOperations = (xorTable.main (varFromOffset XorRow 0)).operations
      (size XorRow) from rfl, xor_sends_gen _ _ _ _ hx]
  cases side <;> simp only [sideForms, flushes_xor] <;> bridge_norm

/-- **`MUL_NATIVE`'s bridge.** -/
theorem bridge_mul (v : ℕ → K) (data : ProverData K) (side : Side) :
    (sideForms 1 side).map (tupleAt · fun c ↦ ofK (v c)) =
      (tuplesOn ((opcodeComponent 1).operations.interactionValues
        (Environment.fromArray (Array.ofFn fun i : Fin 15 ↦ v i) data)) side).map phi := by
  have hx : Eval.eval (Environment.fromArray (Array.ofFn fun i : Fin 15 ↦ v i) data)
      (varFromOffset MulRow 0 : Var MulRow K) =
      (⟨v 0, v 1, v 2, v 3, v 4, #v[v 5, v 6, v 7], #v[v 8, v 9, v 10], v 11, v 12, v 13, v 14⟩ :
        MulRow K) := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn]
  rw [tuplesOn_eq, Air.Flat.Component.interactionsValues_eq,
    show (opcodeComponent 1).rowOperations = (mulTable.main (varFromOffset MulRow 0)).operations
      (size MulRow) from rfl, mul_sends_gen _ _ _ _ hx]
  cases side <;> simp only [sideForms, flushes_mul] <;> bridge_norm

/-- **`SET_CONSTANT`'s bridge.** -/
theorem bridge_set (v : ℕ → K) (data : ProverData K) (side : Side) :
    (sideForms 2 side).map (tupleAt · fun c ↦ ofK (v c)) =
      (tuplesOn ((opcodeComponent 2).operations.interactionValues
        (Environment.fromArray (Array.ofFn fun i : Fin 8 ↦ v i) data)) side).map phi := by
  have hx : Eval.eval (Environment.fromArray (Array.ofFn fun i : Fin 8 ↦ v i) data)
      (varFromOffset SetRow 0 : Var SetRow K) =
      (⟨v 0, v 1, v 2, #v[v 3, v 4, v 5], v 6, v 7⟩ : SetRow K) := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn]
  rw [tuplesOn_eq, Air.Flat.Component.interactionsValues_eq,
    show (opcodeComponent 2).rowOperations = (setTable.main (varFromOffset SetRow 0)).operations
      (size SetRow) from rfl, set_sends_gen _ _ _ _ hx]
  cases side <;> simp only [sideForms, flushes_set] <;> bridge_norm

/-- **`DEREF`'s bridge.** -/
theorem bridge_deref (v : ℕ → K) (data : ProverData K) (side : Side) :
    (sideForms 3 side).map (tupleAt · fun c ↦ ofK (v c)) =
      (tuplesOn ((opcodeComponent 3).operations.interactionValues
        (Environment.fromArray (Array.ofFn fun i : Fin 15 ↦ v i) data)) side).map phi := by
  have hx : Eval.eval (Environment.fromArray (Array.ofFn fun i : Fin 15 ↦ v i) data)
      (varFromOffset DerefRow 0 : Var DerefRow K) =
      (⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, #v[v 8, v 9, v 10], v 11, v 12, v 13, v 14⟩ :
        DerefRow K) := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn]
  rw [tuplesOn_eq, Air.Flat.Component.interactionsValues_eq,
    show (opcodeComponent 3).rowOperations = (derefTable.main (varFromOffset DerefRow 0)).operations
      (size DerefRow) from rfl, deref_sends_gen _ _ _ _ hx]
  cases side <;> simp only [sideForms, flushes_deref] <;> bridge_norm

/-- **`JUMP`'s bridge**: the pushed successor reads the indicator `b`, cell `13`. -/
theorem bridge_jump (v : ℕ → K) (data : ProverData K) (side : Side) :
    (sideForms 4 side).map (tupleAt · fun c ↦ ofK (v c)) =
      (tuplesOn ((opcodeComponent 4).operations.interactionValues
        (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) data)) side).map phi := by
  have hx : Eval.eval (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) data)
      (varFromOffset JumpRow 0 : Var JumpRow K) =
      (⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11⟩ : JumpRow K) := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn]
  have hb : (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) data).get (size JumpRow + 1) =
      v 13 := by
    show ((Array.ofFn fun i : Fin 14 ↦ v i)[13]?).getD 0 = v 13
    simp
  rw [tuplesOn_eq, Air.Flat.Component.interactionsValues_eq,
    show (opcodeComponent 4).rowOperations = (jumpTable.main (varFromOffset JumpRow 0)).operations
      (size JumpRow) from rfl, jump_sends_gen _ _ _ _ hx _ hb]
  cases side <;> simp only [sideForms, flushes_jump] <;> bridge_norm

/-- **`BLAKE2S`'s bridge.** -/
theorem bridge_blake2s (v : ℕ → K) (data : ProverData K) (side : Side) :
    (sideForms 5 side).map (tupleAt · fun c ↦ ofK (v c)) =
      (tuplesOn ((opcodeComponent 5).operations.interactionValues
        (Environment.fromArray (Array.ofFn fun i : Fin 37 ↦ v i) data)) side).map phi := by
  have hx : Eval.eval (Environment.fromArray (Array.ofFn fun i : Fin 37 ↦ v i) data)
      (varFromOffset Blake2sRow 0 : Var Blake2sRow K) =
      (⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, #v[v 9, v 10], #v[v 11, v 12], #v[v 13, v 14],
        #v[v 15, v 16], #v[v 17, v 18], #v[v 19, v 20], #v[v 21, v 22], #v[v 23, v 24], #v[v 25, v 26],
        v 27, v 28, v 29, v 30, v 31, v 32, v 33, v 34, v 35, v 36⟩ : Blake2sRow K) := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn]
  rw [tuplesOn_eq, Air.Flat.Component.interactionsValues_eq,
    show (opcodeComponent 5).rowOperations = (blake2sTable.main (varFromOffset Blake2sRow 0)).operations
      (size Blake2sRow) from rfl, blake2s_sends_gen _ _ _ _ hx]
  cases side <;> simp only [sideForms, flushes_blake2s] <;> bridge_norm

set_option linter.unusedSimpArgs true

/-! ### Every table, every row -/

/-- The cells of a row as a function of the index (`0` past the width). -/
def cellsOf {n : ℕ} (r : Fin n → K) (c : ℕ) : K := if h : c < n then r ⟨c, h⟩ else 0

theorem cellsOf_apply {n : ℕ} (r : Fin n → K) (i : Fin n) : cellsOf r i = r i := by
  simp [cellsOf, i.isLt]

theorem rowE_eq {n : ℕ} (r : Fin n → K) : rowE r = fun c ↦ ofK (cellsOf r c) := by
  funext c
  unfold rowE cellsOf
  split_ifs
  · rfl
  · exact ofKZero.symm

theorem ofFn_cellsOf {n : ℕ} (r : Fin n → K) : Array.ofFn r = Array.ofFn fun i : Fin n ↦ cellsOf r i :=
  congrArg Array.ofFn (funext fun i ↦ (cellsOf_apply r i).symm)

/-- **The PIOP's tuples of a table at a row are Lv42's**, side by side and in order: on a row `r` of opcode
table `j`, the forms of either side at the row's cells are Lv42's flush polynomials of that side at `r`, each
in `E`. -/
theorem rowBridge (j : Fin 6) (side : Side) (r : Fin (width (opIdx j)) → K) :
    (sideForms j side).map (tupleAt · (rowE r)) =
      (((flushes (opIdx j)).filter fun f ↦ decide (f.1 = side)).map fun f ↦ f.2.map fun P ↦ P.eval r).map
        phi := by
  rw [flushesEval_eq j r (fun _ _ ↦ #[]) side, rowE_eq, ofFn_cellsOf]
  fin_cases j
  · exact bridge_xor (cellsOf r) _ side
  · exact bridge_mul (cellsOf r) _ side
  · exact bridge_set (cellsOf r) _ side
  · exact bridge_deref (cellsOf r) _ side
  · exact bridge_jump (cellsOf r) _ side
  · exact bridge_blake2s (cellsOf r) _ side

/-! ### Widths, counters, `JUMP`'s constraints, `BLAKE2S`'s slots -/

/-- The PIOP's widths are Lv42's. -/
theorem tables_width : ∀ t : Fin 6, (tables.getD t default).width = width (opIdx t) := by decide +kernel

/-- **The PIOP's counter columns are Lv42's count columns** (`Table::count_columns`, the names `cnt…`; Lv42's
the coordinate-`1` variables of the memory and bytecode pulls). -/
theorem countColumns_eq :
    ∀ t : Fin 6, (tables.getD t default).countColumns = (counts (opIdx t)).map Fin.val := by decide +kernel

/-- **`JUMP`'s constraints** at a row are its two residuals `b + v_cond · w` (`b` cell `13`, `v_cond` cell `5`,
`w` cell `12`) and `v_cond · (b + 1)`. -/
theorem jump_constraints (r : Fin (width (opIdx 4)) → K) (v : ℕ → K) (hv : ∀ i, r i = v i)
    (h : ∀ C ∈ LeanIsa.constraints (opIdx 4), C.eval r = 0) :
    v 13 + v 5 * v 12 = 0 ∧ v 5 * (v 13 + 1) = 0 := by
  obtain rfl : r = fun i : Fin (width (opIdx 4)) ↦ v i.val := funext hv
  have hl := List.isEmpty_iff.mp (opcode_lookups 4)
  have hc : (⟨jumpTable⟩ : Air.Flat.Component K).operations.ConstraintsHold
      (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) fun _ _ ↦ #[]) :=
    (toM3_constraints_iff (opcodeComponent 4) channelSep channelDir counted hl _ (fun _ _ ↦ #[])).mp h
  have hx : Eval.eval (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) fun _ _ ↦ #[])
      (varFromOffset JumpRow 0 : Var JumpRow K) =
      (⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11⟩ : JumpRow K) := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn]
  have hw : (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) fun _ _ ↦ #[]).get
      (size JumpRow) = v 12 := by
    show ((Array.ofFn fun i : Fin 14 ↦ v i)[size JumpRow]?).getD 0 = v 12
    rw [show size JumpRow = 12 from rfl]
    simp
  have hb : (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) fun _ _ ↦ #[]).get
      (size JumpRow + 1) = v 13 := by
    show ((Array.ofFn fun i : Fin 14 ↦ v i)[size JumpRow + 1]?).getD 0 = v 13
    rw [show size JumpRow + 1 = 13 from rfl]
    simp
  rw [Air.Flat.Component.constraintsHold_iff, Air.Flat.Component.rowOperations_mk] at hc
  exact (jump_constraints_iff _ _ (size JumpRow) _ hx _ _ hw hb).mp hc

/-- **`BLAKE2S`'s limb columns are Flock's slots**: a column of `BLAKE2S` with a `q_flock` slot
(`qflockSlot`) is limb `c − 9` (`9 ≤ c < 27`), and its slot is Flock's (`blake2sFlockSpec.slot`). -/
theorem qflockSlot_eq : ∀ c : Fin 37, ∀ s ∈ qflockSlot (blake2sColumns.getD c ""),
    ∃ h : 9 ≤ c.val ∧ c.val < 27,
      s = (Blake2sFlock.blake2sFlockSpec.slot ⟨c.val - 9, by omega⟩).val := by
  decide +kernel

end UniComplete.Mapping
