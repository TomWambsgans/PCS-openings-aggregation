-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Reduce
import Implementation.Calldata

/-!
# The graph's leaves are the model's chain

On the calldata of a statement's 64 bytes, two roots and five values (`calldataOf`), the graph's
leaves hold (`leafVals_calldataOf`): the statement's four 16-byte halves read big-endian
(`statement::halves`), the challenges of the model's Keccak-256 chain (`QuotientRpm.Wire.verifyWith`:
the seed `H(tag ‖ index root ‖ statement)`, then `H(state ‖ root words)`, `H(state)`, `H(state)`,
`H(state ‖ root words)`, `H(state ‖ value words)`, each challenge the state's `stateLimbs`), and
the five values.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open QuotientRpm Program Emitted

/-- The statement's half `k`: bytes `16 k .. 16 k + 16`, big-endian (`statement::halves`). -/
def halfOf (sb : Vector UInt8 64) (k : Nat) : Nat := beNat ((sb.toList.drop (16 * k)).take 16)

section Chain

variable (H : List UInt8 → Vector UInt8 32) (idx : Bytes32) (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)

/-- The model's chain (`Wire.verifyWith`), the roots it absorbs given: the seed. -/
def st0 : Bytes32 := H (tag ++ idx.toList ++ sb.toList)
/-- After the witness table's root: `α`. -/
def st1 : Bytes32 := H ((st0 H idx sb).toList ++ rootWords r₁)
/-- `β`. -/
def st2 : Bytes32 := H (st1 H idx sb r₁).toList
/-- `γ`. -/
def st3 : Bytes32 := H (st2 H idx sb r₁).toList
/-- After the quotient table's root: `t`. -/
def st4 : Bytes32 := H ((st3 H idx sb r₁).toList ++ rootWords r₂)
/-- After the five values: `ρ`. -/
def st5 (ws : List UInt8) : Bytes32 := H ((st4 H idx sb r₁ r₂).toList ++ ws)

variable {F : Type} [Field F] (limbs : F ≃ Limbs)

/-- **The leaves the model's chain gives**, for values `x0 .. x4` (`a_0 .. a_3`, `next`). -/
noncomputable def modelVals (x0 x1 x2 x3 x4 : F) : Vals F where
  s k := elem limbs (halfOf sb k)
  α := limbs.symm (stateLimbs (st1 H idx sb r₁))
  β := limbs.symm (stateLimbs (st2 H idx sb r₁))
  γ := limbs.symm (stateLimbs (st3 H idx sb r₁))
  t := limbs.symm (stateLimbs (st4 H idx sb r₁ r₂))
  a := ![x0, x1, x2, x3]
  next := x4
  ρ := limbs.symm (stateLimbs (st5 H idx sb r₁ r₂
    ([x0, x1, x2, x3, x4].flatMap fun x => scalarWord (limbs x))))

end Chain

/-! ## Words of calldata -/

theorem cdWord_eq (D : List UInt8) : cdWord D 0 = beNat ((D ++ List.replicate 32 0).take 32) := by
  unfold cdWord
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Nat.zero_add, List.getD_eq_getElem?_getD,
    List.getElem_take]
  by_cases hj : j < D.length
  · rw [List.getElem?_eq_getElem hj, List.getElem_append_left hj]; rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem_append_right (by omega),
      List.getElem_replicate]
    rfl

theorem cdWord_shift (A D : List UInt8) (o : Nat) (h : A.length = o) :
    cdWord (A ++ D) o = cdWord D 0 := by
  unfold cdWord
  congr 1
  refine List.map_congr_left fun j _ => ?_
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  congr 2
  omega

theorem cdWord_head (B C : List UInt8) (hB : B.length = 32) : cdWord (B ++ C) 0 = beNat B := by
  rw [cdWord_eq, List.append_assoc, List.take_left' hB]

theorem cdWord_scalar (B C : List UInt8) (hB : B.length = 24) :
    cdWord (B ++ C) 0 >>> 64 = beNat B := by
  rw [cdWord_eq, List.append_assoc, List.take_append,
    List.take_of_length_le (by omega), hB]
  have hl : ((C ++ List.replicate 32 0).take (32 - 24)).length = 8 := by simp
  have hlt := beNat_lt ((C ++ List.replicate 32 0).take (32 - 24))
  rw [hl] at hlt
  rw [beNat_append, hl, Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 64 = 256 ^ 8 by norm_num,
    Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]

theorem cdWord_slice (cd : List UInt8) (o : Nat) (h : o + 32 ≤ cd.length) :
    cdWord cd o = beNat ((cd.drop o).take 32) := by
  conv_lhs => rw [← List.take_append_drop o cd]
  rw [cdWord_shift _ _ o (by simp; omega), cdWord_eq, List.take_append_of_le_length (by simp; omega)]

section Leaves

variable {F : Type} [Field F] [CharP F 2] {limbs : F ≃ Limbs}
variable (H : List UInt8 → Vector UInt8 32) (idx : Bytes32) (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)
  (x0 x1 x2 x3 x4 : F)

theorem calldataOf_eq : calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4] =
    bytesOf selector ++ (sb.toList ++ (rootBytes r₁ ++ (rootBytes r₂ ++
      (scalarBytes (limbs x0) ++ (scalarBytes (limbs x1) ++ (scalarBytes (limbs x2) ++
        (scalarBytes (limbs x3) ++ scalarBytes (limbs x4)))))))) := by
  simp [calldataOf, List.append_assoc]

theorem length_selector : (bytesOf selector).length = 4 := rfl

example : (List.drop 4 (calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4])).take 32 = sb.toList.take 32 := by
  rw [calldataOf_eq]
  simp [List.drop_append, List.take_append, length_selector]

end Leaves

end Implementation
