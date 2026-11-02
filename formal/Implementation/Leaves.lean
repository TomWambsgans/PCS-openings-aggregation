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

theorem selector_eq : bytesOf selector = [0xde, 0x12, 0xc6, 0x40] := rfl

theorem length_calldataOf : (calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4]).length = 252 := by
  rw [calldataOf_eq]; simp [length_selector]

theorem cdWord_drop (cd : List UInt8) (o : Nat) (h : o ≤ cd.length) :
    cdWord cd o = cdWord (cd.drop o) 0 := by
  conv_lhs => rw [← List.take_append_drop o cd]
  exact cdWord_shift _ _ o (by simp; omega)

theorem drop_stmt (j : Nat) (hj : j < 2) :
    ((calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4]).drop (4 + 32 * j)).take 32 =
      (sb.toList.drop (32 * j)).take 16 ++ (sb.toList.drop (32 * j + 16)).take 16 := by
  rw [calldataOf_eq]
  have e : (sb.toList.drop (32 * j)).take 16 ++ (sb.toList.drop (32 * j + 16)).take 16 =
      (sb.toList.drop (32 * j)).take 32 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, List.take_add, List.drop_drop]
  rw [e]
  interval_cases j <;> simp [List.drop_append, selector_eq, List.take_append]

theorem drop_root (j : Nat) (hj : j < 2) :
    ((calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4]).drop (4 + 64 + 32 * j)).take 32 =
      rootBytes ([r₁, r₂].getD j r₁) := by
  rw [calldataOf_eq]
  interval_cases j <;> simp [List.drop_append, selector_eq, List.take_append]

theorem drop_input (i : Nat) (hi : i < 5) :
    ∃ rest, (calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4]).drop (4 + 128 + 24 * i) =
      scalarBytes (limbs ([x0, x1, x2, x3, x4].getD i x0)) ++ rest := by
  rw [calldataOf_eq]
  interval_cases i <;> simp [List.drop_append, selector_eq, List.drop_eq_nil_of_le, Vector.length_toList, length_rootBytes]

theorem drop_seed : ((calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4]).drop 4).take 64 = sb.toList := by
  rw [calldataOf_eq, List.drop_left' length_selector, List.take_left' (by simp)]

end Leaves



/-! ## The leaves' values -/

theorem node_leaves : nodes[0]? = some .seed ∧ nodes[2]? = some (.statement 0) ∧
    nodes[3]? = some (.statement 1) ∧ nodes[4]? = some (.statement 2) ∧
    nodes[5]? = some (.statement 3) ∧ nodes[6]? = some (.root 0) ∧ nodes[7]? = some (.root 1) ∧
    nodes[8]? = some (.hash 0 [6, 7]) ∧ nodes[9]? = some (.low 8) ∧
    nodes[10]? = some (.hash 8 []) ∧ nodes[11]? = some (.low 10) ∧
    nodes[12]? = some (.hash 10 []) ∧ nodes[13]? = some (.low 12) ∧
    nodes[14]? = some (.root 2) ∧ nodes[15]? = some (.root 3) ∧
    nodes[16]? = some (.hash 12 [14, 15]) ∧ nodes[17]? = some (.low 16) ∧
    nodes[18]? = some (.input 0) ∧ nodes[19]? = some (.input 1) ∧ nodes[20]? = some (.input 2) ∧
    nodes[21]? = some (.input 3) ∧ nodes[22]? = some (.input 4) ∧
    nodes[23]? = some (.hash 16 [18, 19, 20, 21, 22]) ∧ nodes[24]? = some (.low 23) := by
  decide +kernel

section LeafVals

variable {F : Type} [Field F] [CharP F 2] {limbs : F ≃ Limbs}
variable (H : List UInt8 → Vector UInt8 32) (idx : Bytes32) (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)
  (x0 x1 x2 x3 x4 : F)

local notation "CD" => calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4]
local notation "VALS" => values H idx.toList (calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4])

theorem vals_stmt (k : Nat) (hk : k < 4) (h : nodes[2 + k]? = some (.statement k)) :
    (VALS).getD (2 + k) 0 = halfOf sb k := by
  rw [values_statement _ _ _ h, cdWord_slice _ _ (by rw [length_calldataOf]; omega),
    drop_stmt sb r₁ r₂ x0 x1 x2 x3 x4 (k / 2) (by omega), half_beNat _ _ (by simp; omega)
      (by simp; omega), halfOf]
  split_ifs with h2
  · rw [show 16 * k = 32 * (k / 2) by omega]
  · rw [show 16 * k = 32 * (k / 2) + 16 by omega]

theorem vals_root (k : Nat) (hk : k < 4) (n : Nat) (h : nodes[n]? = some (.root k)) :
    (VALS).getD n 0 = if k % 2 = 0 then beNat (([r₁, r₂].getD (k / 2) r₁).toList.take 16).reverse
      else beNat (([r₁, r₂].getD (k / 2) r₁).toList.drop 16).reverse := by
  have hl := ([r₁, r₂].getD (k / 2) r₁).length_toList
  rw [values_root _ _ _ h, cdWord_slice _ _ (by rw [length_calldataOf]; omega),
    drop_root sb r₁ r₂ x0 x1 x2 x3 x4 (k / 2) (by omega), rootBytes,
    half_beNat _ _ (by simp [hl]) (by simp [hl])]

theorem vals_input (i : Nat) (hi : i < 5) (n : Nat) (h : nodes[n]? = some (.input i)) :
    (VALS).getD n 0 = limbsNat (limbs ([x0, x1, x2, x3, x4].getD i x0)) := by
  obtain ⟨rest, hrest⟩ := drop_input sb r₁ r₂ x0 x1 x2 x3 x4 (limbs := limbs) i hi
  rw [values_input _ _ _ h, cdWord_drop _ _ (by rw [length_calldataOf]; omega), hrest,
    cdWord_scalar _ _ (length_scalarBytes _), beNat_scalarBytes]

theorem beBytes_state (st : Bytes32) : beBytes 32 (beNat st.toList) = st.toList := by
  have := beBytes_beNat st.toList
  rwa [st.length_toList] at this

theorem beBytes_half (l : List UInt8) (hl : l.length = 16) :
    beBytes 32 (beNat l) = List.replicate 16 0 ++ l := by
  have := beBytes_pad 16 l
  rwa [hl] at this

theorem rootWords_vals (r : Bytes32) :
    beBytes 32 (beNat (r.toList.take 16).reverse) ++ beBytes 32 (beNat (r.toList.drop 16).reverse) =
      rootWords r := by
  have hl := r.length_toList
  rw [beBytes_half _ (by simp [hl]), beBytes_half _ (by simp [hl]), rootWords_eq]
  simp

theorem vals_seed : (VALS).getD 0 0 = beNat (st0 H idx sb).toList := by
  rw [values_seed _ _ _ node_leaves.1, drop_seed]
  rfl

theorem vals_roots : (VALS).getD 6 0 = beNat (r₁.toList.take 16).reverse ∧
    (VALS).getD 7 0 = beNat (r₁.toList.drop 16).reverse ∧
    (VALS).getD 14 0 = beNat (r₂.toList.take 16).reverse ∧
    (VALS).getD 15 0 = beNat (r₂.toList.drop 16).reverse := by
  have hn := node_leaves
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vals_root H idx sb r₁ r₂ x0 x1 x2 x3 x4 0 (by norm_num) 6 hn.2.2.2.2.2.1]; rfl
  · rw [vals_root H idx sb r₁ r₂ x0 x1 x2 x3 x4 1 (by norm_num) 7 hn.2.2.2.2.2.2.1]; rfl
  · rw [vals_root H idx sb r₁ r₂ x0 x1 x2 x3 x4 2 (by norm_num) 14
      hn.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl
  · rw [vals_root H idx sb r₁ r₂ x0 x1 x2 x3 x4 3 (by norm_num) 15
      hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl

theorem vals_st1 : (VALS).getD 8 0 = beNat (st1 H idx sb r₁).toList := by
  have hn := node_leaves
  have hr := vals_roots H idx sb r₁ r₂ x0 x1 x2 x3 x4 (limbs := limbs)
  rw [values_hash _ _ _ hn.2.2.2.2.2.2.2.1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [vals_seed, beBytes_state, hr.1, hr.2.1, rootWords_vals]
  rfl

theorem vals_st2 : (VALS).getD 10 0 = beNat (st2 H idx sb r₁).toList := by
  have hn := node_leaves
  rw [values_hash _ _ _ hn.2.2.2.2.2.2.2.2.2.1]
  simp only [List.flatMap_nil, List.append_nil]
  rw [vals_st1, beBytes_state]
  rfl

theorem vals_st3 : (VALS).getD 12 0 = beNat (st3 H idx sb r₁).toList := by
  have hn := node_leaves
  rw [values_hash _ _ _ hn.2.2.2.2.2.2.2.2.2.2.2.1]
  simp only [List.flatMap_nil, List.append_nil]
  rw [vals_st2, beBytes_state]
  rfl

theorem vals_st4 : (VALS).getD 16 0 = beNat (st4 H idx sb r₁ r₂).toList := by
  have hn := node_leaves
  have hr := vals_roots H idx sb r₁ r₂ x0 x1 x2 x3 x4 (limbs := limbs)
  rw [values_hash _ _ _ hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [vals_st3, beBytes_state, hr.2.2.1, hr.2.2.2, rootWords_vals]
  rfl

theorem vals_inputs : ∀ i < 5, (VALS).getD (18 + i) 0 =
    limbsNat (limbs ([x0, x1, x2, x3, x4].getD i x0)) := by
  have hn := node_leaves
  intro i hi
  interval_cases i
  · exact vals_input H idx sb r₁ r₂ x0 x1 x2 x3 x4 0 (by norm_num) 18 hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact vals_input H idx sb r₁ r₂ x0 x1 x2 x3 x4 1 (by norm_num) 19
      hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact vals_input H idx sb r₁ r₂ x0 x1 x2 x3 x4 2 (by norm_num) 20
      hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact vals_input H idx sb r₁ r₂ x0 x1 x2 x3 x4 3 (by norm_num) 21
      hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact vals_input H idx sb r₁ r₂ x0 x1 x2 x3 x4 4 (by norm_num) 22
      hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem beBytes_limbs (l : Limbs) : beBytes 32 (limbsNat l) = scalarWord l := by
  rw [← beNat_scalarBytes, show 32 = 8 + (scalarBytes l).length by simp, beBytes_pad,
    scalarWord_eq]

theorem vals_st5 : (VALS).getD 23 0 = beNat (st5 H idx sb r₁ r₂
    ([x0, x1, x2, x3, x4].flatMap fun x => scalarWord (limbs x))).toList := by
  have hn := node_leaves
  have hi := vals_inputs H idx sb r₁ r₂ x0 x1 x2 x3 x4 (limbs := limbs)
  rw [values_hash _ _ _ hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [vals_st4, beBytes_state, hi 0 (by norm_num), hi 1 (by norm_num), hi 2 (by norm_num),
    hi 3 (by norm_num), hi 4 (by norm_num)]
  simp only [beBytes_limbs]
  rfl

theorem elem_low {k a : Nat} (h : nodes[k]? = some (.low a)) (st : Bytes32)
    (ha : (VALS).getD a 0 = beNat st.toList) :
    elem limbs ((VALS).getD k 0) = limbs.symm (stateLimbs st) := by
  rw [values_low _ _ _ h, ha, elem, natLimbs_state]

variable (hF : IsF192 limbs)

/-- **The graph's leaves on `calldataOf` are the model's chain**: the statement's halves, the
challenges of `Wire.verifyWith`'s chain with the roots `r₁`, `r₂`, and the five values. -/
theorem leafVals_calldataOf :
    leafVals limbs H idx.toList (calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4]) =
      modelVals H idx sb r₁ r₂ limbs x0 x1 x2 x3 x4 := by
  have hn := node_leaves
  have hi := vals_inputs H idx sb r₁ r₂ x0 x1 x2 x3 x4 (limbs := limbs)
  have hs : ∀ k : Fin 4, val limbs H idx.toList (calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4])
      (2 + k) = elem limbs (halfOf sb k) := fun k => by
    rw [val, vals_stmt H idx sb r₁ r₂ x0 x1 x2 x3 x4 k k.2]
    fin_cases k
    · exact hn.2.1
    · exact hn.2.2.1
    · exact hn.2.2.2.1
    · exact hn.2.2.2.2.1
  have ha : ∀ k : Fin 4, val limbs H idx.toList (calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4])
      (18 + k) = ![x0, x1, x2, x3] k := fun k => by
    rw [val, hi k (by omega)]
    fin_cases k <;> exact elem_word _
  simp only [leafVals, modelVals, Vals.mk.injEq]
  refine ⟨funext hs, ?_, ?_, ?_, ?_, funext ha, ?_, ?_⟩
  · exact elem_low H idx sb r₁ r₂ x0 x1 x2 x3 x4 hn.2.2.2.2.2.2.2.2.1 _ (vals_st1 ..)
  · exact elem_low H idx sb r₁ r₂ x0 x1 x2 x3 x4 hn.2.2.2.2.2.2.2.2.2.2.1 _ (vals_st2 ..)
  · exact elem_low H idx sb r₁ r₂ x0 x1 x2 x3 x4 hn.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (vals_st3 ..)
  · exact elem_low H idx sb r₁ r₂ x0 x1 x2 x3 x4 hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (vals_st4 ..)
  · rw [val, hi 4 (by norm_num)]; exact elem_word _
  · exact elem_low H idx sb r₁ r₂ x0 x1 x2 x3 x4
      hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (vals_st5 ..)

end LeafVals

end Implementation
