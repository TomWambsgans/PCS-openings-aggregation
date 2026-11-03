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

/-! ## Axioms -/

/-- info: 'UniSound.Ids.lvReadBack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lvReadBack

/-- info: 'UniSound.Ids.limb_lv42Stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms limb_lv42Stack

end UniSound.Ids
