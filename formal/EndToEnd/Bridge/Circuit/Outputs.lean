-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit.Secret

/-!
# The computation: outputs, cells, input bits

* `outputs_eq`: the statement's `Circuit.outputs` (its `for` loops) is F0b's `Circuit.outputs` (its
  folds) of the circuit read by `circuitTr`, for input bits at least as many as the inputs;
  `membership_outputs`: for `membership 22` and F0b's `membership`.
* `cells_eq`: the statement's `Circuit.cells` is the cell bits (`cellBitC`, what each cell of F0b's
  circuit reads under F0b's outputs) as `0`/`1` of `K`; `membership_cells`.
* `membershipInputs_eq`: the statement's input bits of a secret (`membershipInputs`) are F0b's
  (`Secret.inputs`) of the same secret (`secretTr`); `membershipInputs_length`.
* `secretOfInputs_membershipInputs`: the statement's `secretOfInputs` inverts `membershipInputs`.
-/

namespace Bridge.Circuit

/-! ## Outputs -/

theorem readSrc_eq (v : Array Bool) (s : PcsQuotient.Src) :
    PcsQuotient.readSrc v s = PcsCircuit.readBit v (srcTr s) := by
  cases s <;> rfl

theorem rows_getD_map (rows : Array PcsQuotient.Row) (r : ℕ) :
    (rows.map rowTr).getD r .idle = rowTr (rows.getD r PcsQuotient.idle) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases rows[r]? <;> rfl

theorem zip_eq_map_range (ins : Array ℕ) (bits : List Bool) (h : ins.size ≤ bits.length) :
    ins.toList.zip bits = (List.range ins.size).map fun k => (ins.getD k 0, bits.toArray.getD k false) := by
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [List.length_zip, Array.length_toList] at h1
  simp only [List.getElem_zip, Array.getElem_toList, List.getElem_map, List.getElem_range,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show k < ins.size by omega),
    Option.getD_some, List.getElem?_toArray, List.getElem?_eq_getElem (show k < bits.length by omega)]

/-- **The outputs**: the statement's `Circuit.outputs` is F0b's of the circuit read by `circuitTr`. -/
theorem outputs_eq (c : PcsQuotient.Circuit) (bits : List Bool) (h : c.inputs.size ≤ bits.length) :
    PcsQuotient.Circuit.outputs c bits = PcsCircuit.Circuit.outputs (circuitTr c) bits.toArray := by
  unfold PcsQuotient.Circuit.outputs PcsCircuit.Circuit.outputs
  simp only [List.forIn_pure_yield_eq_foldl, Id.run_bind, Id.run_pure]
  simp only [circuitTr, Array.size_map]
  rw [zip_eq_map_range _ _ h, List.foldl_map]
  congr 1
  funext v r
  rw [rows_getD_map]
  simp only [rowTr, readSrc_eq, PcsQuotient.gateBits, PcsCircuit.gateBits, PcsQuotient.publicRows,
    PcsCircuit.publicRows]

/-! ## Cells -/

/-- What cell `i` of F0b's circuit `c` holds under the outputs `v`: role `X`, `Y`, `C` of row
`i / 4` reads its source, role `V` is the row's output. -/
def cellBitC (c : PcsCircuit.Circuit) (v : Array Bool) (i : ℕ) : Bool :=
  let row := c.rows.getD (i / 4) .idle
  match i % 4 with
  | 0 => PcsCircuit.readBit v row.x
  | 1 => PcsCircuit.readBit v row.y
  | 2 => PcsCircuit.readBit v row.c
  | _ => v.getD (i / 4) false

/-- **The cells**: the statement's `Circuit.cells` are F0b's cell bits as `0`/`1`. -/
theorem cells_eq (c : PcsQuotient.Circuit) (bits : List Bool) (h : c.inputs.size ≤ bits.length) :
    PcsQuotient.Circuit.cells c bits = Array.ofFn (n := 4 * c.rows.size) fun i =>
      if cellBitC (circuitTr c) (PcsCircuit.Circuit.outputs (circuitTr c) bits.toArray) i.val then 1
      else 0 := by
  unfold PcsQuotient.Circuit.cells
  rw [outputs_eq c bits h]
  dsimp only
  congr 1
  funext i
  have hrow : (circuitTr c).rows.getD (i.val / 4) .idle = rowTr (c.rows.getD (i.val / 4) PcsQuotient.idle) :=
    rows_getD_map _ _
  unfold cellBitC
  simp only [hrow, rowTr, ← readSrc_eq]
  rcases Nat.lt_or_ge (i.val % 4) 3 with h3 | h3
  · interval_cases (i.val % 4) <;> rfl
  · have : i.val % 4 = 3 := by omega
    simp only [this]

/-! ## The membership circuit -/

theorem pc_inputs_size' : PcsCircuit.membership.inputs.size = 8480 := pc_inputs_size

/-! ## Input bits of a secret -/

/-- A statement secret as F0b's. -/
def secretTr (w : PcsQuotient.Secret) : PcsCircuit.Secret where
  x := w.x.toList
  siblings := w.siblings.toList.map Vector.toList
  directions := PcsCircuit.bitsToNat w.directions.toList

theorem bits_eq (b : PcsQuotient.Bytes32) :
    ((List.range 256).map fun i => decide ((b.toList.getD (i / 8) 0 >>> (i % 8).toUInt8) &&& 1 = 1)) =
      PcsCircuit.bytesBits b.toList := by
  unfold PcsCircuit.bytesBits
  refine List.map_congr_left fun i _ => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact u8_bit _ _ (Nat.mod_lt _ (by norm_num))

theorem secretTr_siblings (w : PcsQuotient.Secret) (i : Fin PcsQuotient.depth) :
    (secretTr w).siblings.getD i [] = w.siblings[i].toList := by
  simp [secretTr, List.getD_eq_getElem?_getD]

theorem secretTr_directions (w : PcsQuotient.Secret) (i : Fin PcsQuotient.depth) :
    (secretTr w).directions.testBit i = w.directions[i] := by
  simp [secretTr, PcsCircuit.bitsToNat_testBit, List.getD_eq_getElem?_getD]

/-- **The input bits of a secret**: the statement's `membershipInputs` is F0b's `Secret.inputs`. -/
theorem membershipInputs_eq (w : PcsQuotient.Secret) :
    PcsQuotient.membershipInputs w = (secretTr w).inputs.toList := by
  unfold PcsQuotient.membershipInputs PcsCircuit.Secret.inputs
  simp only [List.toList_toArray]
  rw [bits_eq]
  congr 1
  have hr : List.range PcsCircuit.depth = (List.finRange PcsQuotient.depth).map Fin.val :=
    (finRange_map_val 32).symm
  rw [hr]
  simp only [List.flatMap, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  rw [bits_eq, secretTr_siblings, secretTr_directions]

theorem membershipInputs_length (w : PcsQuotient.Secret) :
    (PcsQuotient.membershipInputs w).length = 8480 := by
  simp [PcsQuotient.membershipInputs, PcsQuotient.depth]

/-- The statement's cells of a secret on `membership 22` are F0b's cell bits of its computation. -/
theorem membership_cells (w : PcsQuotient.Secret) :
    PcsQuotient.Circuit.cells (PcsQuotient.membership 22) (PcsQuotient.membershipInputs w) =
      Array.ofFn (n := 4 * (PcsQuotient.membership 22).rows.size) fun i =>
        if cellBitC PcsCircuit.membership
          (PcsCircuit.Circuit.outputs PcsCircuit.membership (secretTr w).inputs) i.val then 1 else 0 := by
  have hin : (PcsQuotient.membership 22).inputs.size ≤ (PcsQuotient.membershipInputs w).length := by
    rw [membership_inputs, pc_inputs_size', membershipInputs_length]
  rw [cells_eq _ _ hin, membership_eq, membershipInputs_eq, Array.toArray_toList]

/-- The statement's outputs of a secret on `membership 22` are F0b's. -/
theorem membership_outputs (w : PcsQuotient.Secret) :
    PcsQuotient.Circuit.outputs (PcsQuotient.membership 22) (PcsQuotient.membershipInputs w) =
      PcsCircuit.Circuit.outputs PcsCircuit.membership (secretTr w).inputs := by
  have hin : (PcsQuotient.membership 22).inputs.size ≤ (PcsQuotient.membershipInputs w).length := by
    rw [membership_inputs, pc_inputs_size', membershipInputs_length]
  rw [outputs_eq _ _ hin, membership_eq, membershipInputs_eq, Array.toArray_toList]

/-! ## `secretOfInputs` inverts `membershipInputs` -/

theorem byteOfBits_testBit_self (b : UInt8) : PcsCircuit.byteOfBits (fun t => b.toNat.testBit t) = b := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · rw [PcsCircuit.byteOfBits_testBit _ _ ht]
  · have h1 : (PcsCircuit.byteOfBits fun t => b.toNat.testBit t).toNat < 2 ^ 8 := UInt8.toNat_lt _
    have h2 : b.toNat < 2 ^ 8 := UInt8.toNat_lt _
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem bytesOfBits_bits (b : PcsQuotient.Bytes32) (f : ℕ → Bool)
    (hf : ∀ t < 256, f t = (b.toList.getD (t / 8) 0).toNat.testBit (t % 8)) :
    PcsCircuit.bytesOfBits f = b.toList := by
  unfold PcsCircuit.bytesOfBits
  apply List.ext_getElem (by simp)
  intro p h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  rw [byteOfBits_congr (g := fun t => (b.toList.getD p 0).toNat.testBit t) fun t ht => by
    rw [hf _ (by omega)]
    congr 3 <;> omega]
  rw [byteOfBits_testBit_self, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]
  rfl

theorem length_flatMap_range (g : ℕ → List Bool) (m : ℕ) (hg : ∀ j, (g j).length = m) :
    ∀ n, ((List.range n).flatMap g).length = m * n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range g m hg n]
    simp [hg]
    ring

theorem getD_flatMap_range (g : ℕ → List Bool) (m : ℕ) (hg : ∀ j, (g j).length = m) :
    ∀ n i t, i < n → t < m → ((List.range n).flatMap g).getD (m * i + t) false = (g i).getD t false
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, t, hi, ht => by
    rw [List.range_succ, List.flatMap_append]
    have hl := length_flatMap_range g m hg n
    rcases Nat.lt_or_ge i n with hin | hin
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith)]
      exact getD_flatMap_range g m hg n i t hin ht
    · have hi' : i = n := by omega
      subst hi'
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      congr 1
      omega

/-- Bit `256 + 257 i + t` of a secret's input bits: bit `t` of the `i`-th sibling, or the `i`-th
direction at `t = 256`. -/
theorem membershipInputs_level (w : PcsQuotient.Secret) (i : Fin PcsQuotient.depth) (t : ℕ)
    (ht : t < 257) :
    (PcsQuotient.membershipInputs w).getD (256 + 257 * i.val + t) false =
      (PcsCircuit.bytesBits w.siblings[i].toList ++ [w.directions[i]]).getD t false := by
  rw [membershipInputs_eq]
  simp only [PcsCircuit.Secret.inputs, List.toList_toArray]
  rw [List.getD_append_right _ _ _ _ (by simp [PcsCircuit.bytesBits]; omega)]
  have hlen : (PcsCircuit.bytesBits (secretTr w).x).length = 256 := by simp [PcsCircuit.bytesBits]
  rw [hlen, show 256 + 257 * i.val + t - 256 = 257 * i.val + t by omega]
  rw [getD_flatMap_range _ 257 (fun j => by simp [PcsCircuit.bytesBits]) PcsCircuit.depth i t i.isLt ht]
  rw [secretTr_siblings, secretTr_directions]

theorem membershipInputs_x (w : PcsQuotient.Secret) (t : ℕ) (ht : t < 256) :
    (PcsQuotient.membershipInputs w).getD t false =
      (w.x.toList.getD (t / 8) 0).toNat.testBit (t % 8) := by
  rw [membershipInputs_eq]
  simp only [PcsCircuit.Secret.inputs, List.toList_toArray]
  rw [List.getD_append _ _ _ _ (by simp [PcsCircuit.bytesBits]; omega)]
  simp [PcsCircuit.bytesBits, List.getD_eq_getElem?_getD, ht, secretTr]

/-- **`secretOfInputs` inverts `membershipInputs`**. -/
theorem secretOfInputs_membershipInputs (w : PcsQuotient.Secret) :
    PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs w) = w := by
  obtain ⟨x, sib, dir⟩ := w
  have hx : (PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs ⟨x, sib, dir⟩)).x = x := by
    apply Vector.toList_inj.mp
    rw [secretOfInputs_x]
    exact bytesOfBits_bits x _ fun t ht => membershipInputs_x _ t ht
  have hs : ∀ i : Fin PcsQuotient.depth,
      (PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs ⟨x, sib, dir⟩)).siblings[i] = sib[i] := by
    intro i
    apply Vector.toList_inj.mp
    rw [secretOfInputs_siblings]
    refine bytesOfBits_bits sib[i] _ fun t ht => ?_
    rw [membershipInputs_level _ i t (by omega), List.getD_append _ _ _ _ (by
      simp [PcsCircuit.bytesBits]; omega)]
    simp [PcsCircuit.bytesBits, List.getD_eq_getElem?_getD, ht]
  have hd : ∀ i : Fin PcsQuotient.depth,
      (PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs ⟨x, sib, dir⟩)).directions[i] = dir[i] := by
    intro i
    rw [secretOfInputs_directions, membershipInputs_level _ i 256 (by omega),
      List.getD_append_right _ _ _ _ (by simp [PcsCircuit.bytesBits])]
    simp [PcsCircuit.bytesBits]
  cases h : PcsQuotient.secretOfInputs (PcsQuotient.membershipInputs ⟨x, sib, dir⟩) with
  | mk x' sib' dir' =>
    rw [h] at hx hs hd
    simp only at hx hs hd
    subst hx
    congr 1
    · exact Vector.ext fun i hi => hs ⟨i, hi⟩
    · exact Vector.ext fun i hi => hd ⟨i, hi⟩

/-! ## Axioms -/

/-- info: 'Bridge.Circuit.outputs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Circuit.outputs_eq

/-- info: 'Bridge.Circuit.cells_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Circuit.cells_eq

/-- info: 'Bridge.Circuit.membershipInputs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Circuit.membershipInputs_eq

/-- info: 'Bridge.Circuit.membership_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Circuit.membership_outputs

/-- info: 'Bridge.Circuit.membership_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Circuit.membership_cells

/-- info: 'Bridge.Circuit.secretOfInputs_membershipInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Circuit.secretOfInputs_membershipInputs

end Bridge.Circuit
