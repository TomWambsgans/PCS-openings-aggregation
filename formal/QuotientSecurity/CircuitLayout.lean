-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Circuit
import QuotientSecurity.PublicWeight

/-!
# How `quotient::circuit` lays a circuit on the cells

`Builder::finish` numbers the rows `0, 1, …` and the cells of row `r` `4 r + role`, the roles
`X, Y, C, V`; an instance names a cell by 24 bits, the low one first (`cellBits`: bits 0 and 1
the role, the others the row). This file writes the circuit's side in the instance's terms:

* the circuit on bits: `Src.bval`, `chiBits`, `ChiCircuit.SatisfiesBits` (`bits_determined`: a
  loop-free circuit's bits are fixed by its input bits), and `ChiCircuit.map`, a circuit on
  renamed rows;
* the numbering: `cellOf n` is cell `n`, `rowCell r role` the cell of role `role` of row `r`
  (`rowCell_eq_cellOf`: cell `4 r + role`);
* the public cells: bit `j` of word `J` is the `X` (even `j`) or `Y` (odd `j`) cell of row
  `64 J + j / 2` (`pubCell`, cell `256 J + 4 (j / 2) + j % 2`); public word `J` reads these 128
  cells and no other when the coordinates' weights give the roles `C, V` the weight zero
  (`sum_regionWeight`), and with `coordinate_weight`'s weights it gives bit `j` the weight
  `bit_weight(j)` (`regionWeight_coordWeight`);
* the statement: `statement::halves` as field elements, and the eight words
  `(y0, y1, root0, root1, 1, 0, 0, 0)` (`statementWords`);
* the hypotheses on a circuit and a wiring that `Pinning.lean` and `soundness_circuit` use:
  `Laid`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace QuotientSecurity

/-! ## The circuit on bits -/

section Bits

variable {ρ ρ' : Type*}

/-- A bit as a field element. -/
def bitF {F : Type*} [Zero F] [One F] (b : Bool) : F := if b then 1 else 0

/-- The bit a cell reads, the rows' outputs being `v`. -/
def Src.bval (v : ρ → Bool) : Src ρ → Bool
  | .zero => false
  | .one => true
  | .row r => v r

/-- The χ gate on bits, `x ⊕ (c ∧ ¬y)` (`quotient::circuit::gate_bits`). -/
def chiBits (x y c : Bool) : Bool := xor x (c && !y)

/-- **`v` is a computation of `C`**: every row's bit is the gate on the bits it reads. An input
row reads its own output three times, and `chiBits v v v = v`: its bit is free, and
`bits_determined` shows the input bits fix every other. -/
def ChiCircuit.SatisfiesBits (C : ChiCircuit ρ) (v : ρ → Bool) : Prop :=
  ∀ r, v r = chiBits ((C.x r).bval v) ((C.y r).bval v) ((C.c r).bval v)

/-- **A loop-free circuit's computation is fixed by its input bits.** -/
theorem ChiCircuit.bits_determined (C : ChiCircuit ρ) (v v' : ρ → Bool)
    (hv : C.SatisfiesBits v) (hv' : C.SatisfiesBits v') (hin : ∀ r, C.isInput r → v r = v' r) :
    v = v' := by
  funext r
  induction hn : C.rank r using Nat.strong_induction_on generalizing r with
  | _ n ih =>
    by_cases hi : C.isInput r
    · exact hin r hi
    · have hsrc : ∀ s : Src ρ, (∀ r', s = .row r' → C.rank r' < C.rank r) →
          s.bval v = s.bval v' := by
        intro s hs
        cases s with
        | zero => rfl
        | one => rfl
        | row r' => exact ih _ (hn ▸ hs r' rfl) r' rfl
      rw [hv r, hv' r, hsrc (C.x r) fun r' h => C.hOrder r hi r' (Or.inl h),
        hsrc (C.y r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inl h)),
        hsrc (C.c r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inr h))]

/-- A source with its row renamed. -/
def Src.map (e : ρ → ρ') : Src ρ → Src ρ'
  | .zero => .zero
  | .one => .one
  | .row r => .row (e r)

theorem Src.map_eq_row (e : ρ ≃ ρ') (s : Src ρ) (r' : ρ') (h : s.map e = .row r') :
    s = .row (e.symm r') := by
  cases s with
  | zero => cases h
  | one => cases h
  | row r =>
    cases h
    simp

/-- **A circuit on renamed rows**: row `e r` reads what row `r` reads, renamed. -/
def ChiCircuit.map (e : ρ ≃ ρ') (C : ChiCircuit ρ) : ChiCircuit ρ' where
  x t := (C.x (e.symm t)).map e
  y t := (C.y (e.symm t)).map e
  c t := (C.c (e.symm t)).map e
  rank t := C.rank (e.symm t)
  isInput t := C.isInput (e.symm t)
  hInput t h := by
    obtain ⟨hx, hy, hc⟩ := C.hInput _ h
    simp [hx, hy, hc, Src.map]
  hOrder t h t' hs := by
    refine C.hOrder _ h _ ?_
    rcases hs with hs | hs | hs
    · exact Or.inl (Src.map_eq_row e _ _ hs)
    · exact Or.inr (Or.inl (Src.map_eq_row e _ _ hs))
    · exact Or.inr (Or.inr (Src.map_eq_row e _ _ hs))

theorem ChiCircuit.map_x (e : ρ ≃ ρ') (C : ChiCircuit ρ) (r : ρ) :
    (C.map e).x (e r) = (C.x r).map e := by simp [ChiCircuit.map]

theorem ChiCircuit.map_y (e : ρ ≃ ρ') (C : ChiCircuit ρ) (r : ρ) :
    (C.map e).y (e r) = (C.y r).map e := by simp [ChiCircuit.map]

theorem ChiCircuit.map_c (e : ρ ≃ ρ') (C : ChiCircuit ρ) (r : ρ) :
    (C.map e).c (e r) = (C.c r).map e := by simp [ChiCircuit.map]

theorem ChiCircuit.map_isInput (e : ρ ≃ ρ') (C : ChiCircuit ρ) (r : ρ) :
    (C.map e).isInput (e r) ↔ C.isInput r := by simp [ChiCircuit.map]

variable {F : Type*} [Field F] [CharP F 2]

theorem bitF_isBit (b : Bool) : IsBit (bitF b : F) := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A bit of the field is the bit `z = 1`. -/
theorem eq_bitF_of_isBit [DecidableEq F] {z : F} (h : IsBit z) : z = bitF (decide (z = 1)) := by
  rcases h with rfl | rfl
  · simp [bitF]
  · simp [bitF]

theorem bitF_injective : Function.Injective (bitF : Bool → F) := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitF]

/-- In characteristic 2, `bitF` sends `xor` to `+`. -/
theorem bitF_xor (a b : Bool) : (bitF (xor a b) : F) = bitF a + bitF b := by
  have one : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  cases a <;> cases b <;> simp [bitF, one]

/-- **The gate on bits is `chiBits`.** -/
theorem gate_bitF (a b c d : Bool) :
    gate (bitF a : F) (bitF b) (bitF c) (bitF d) = 0 ↔ d = chiBits a b c := by
  rw [gate_eq, CharTwo.add_eq_zero]
  have one : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have h : chiOf (bitF a : F) (bitF b) (bitF c) = bitF (chiBits a b c) := by
    cases a <;> cases b <;> cases c <;> simp [chiOf, chiBits, bitF, one]
  rw [h]
  exact bitF_injective.eq_iff

theorem Src.val_bitF (v : ρ → Bool) (s : Src ρ) :
    s.val (fun r => (bitF (v r) : F)) = bitF (s.bval v) := by
  cases s <;> rfl

end Bits

/-! ## The numbering of cells and rows -/

section Numbering

/-- **Cell `n`** of `quotient::circuit`, by its bits, the low one first. -/
def cellOf (n : ℕ) : Fin (22 + 2) → Bool := fun k => n.testBit k

/-- **Row `r`**, by its bits, the low one first. -/
def rowBits (r : Fin (2 ^ 22)) : Fin 22 → Bool := fun k => (r : ℕ).testBit k

/-- **The cell of role `role`** (`X, Y, C, V`) of row `r`. -/
def rowCell (r : Fin (2 ^ 22)) (role : Fin 4) : Fin (22 + 2) → Bool := cellBits (rowBits r, role)

/-- The cell of role `role` of row `r` is cell `4 r + role`, as `quotient::circuit` numbers it. -/
theorem rowCell_eq_cellOf (r : Fin (2 ^ 22)) (role : Fin 4) :
    rowCell r role = cellOf (4 * r + role) := by
  have hb : (4 * (r : ℕ) + role) = 2 ^ 2 * r + role := by norm_num
  funext k
  unfold cellOf
  rw [hb, Nat.testBit_two_pow_mul_add _ (lt_of_lt_of_eq role.isLt (by norm_num))]
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp only [Fin.val_zero, Nat.ofNat_pos, ite_true]
    fin_cases role <;> rfl
  · simp only [Fin.val_succ, Fin.val_zero]
    rw [ite_eq_left (by norm_num)]
    fin_cases role <;> rfl
  · simp only [Fin.val_succ]
    rw [ite_eq_right (by omega)]
    rfl

theorem cellOf_inj {n n' : ℕ} (hn : n < 2 ^ (22 + 2)) (hn' : n' < 2 ^ (22 + 2))
    (h : cellOf n = cellOf n') : n = n' := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < 22 + 2
  · exact congrFun h ⟨i, hi⟩
  · have hle : 2 ^ (22 + 2) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn hle),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn' hle)]

/-- Every cell has a number. -/
theorem exists_cellOf (x : Fin (22 + 2) → Bool) : ∃ n < 2 ^ (22 + 2), cellOf n = x := by
  have hbij : Function.Bijective fun n : Fin (2 ^ (22 + 2)) => cellOf n := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun a b h => ?_, ?_⟩
    · exact Fin.ext (cellOf_inj a.isLt b.isLt h)
    · simp
  obtain ⟨n, hn⟩ := hbij.2 x
  exact ⟨n, n.isLt, hn⟩

theorem rowBits_injective : Function.Injective rowBits := by
  intro r r' h
  refine Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)
  by_cases hi : i < 22
  · exact congrFun h ⟨i, hi⟩
  · have hle : 2 ^ 22 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt hle),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r'.isLt hle)]

/-- The rows, by their numbers. -/
noncomputable def rowEquiv : Fin (2 ^ 22) ≃ (Fin 22 → Bool) :=
  Equiv.ofBijective rowBits
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨rowBits_injective, by simp⟩)

theorem rowEquiv_apply (r : Fin (2 ^ 22)) : rowEquiv r = rowBits r := rfl

end Numbering

/-! ## The public cells -/

section Public

/-- **The row holding bit `j` of public word `J`**: row `64 J + j / 2` (`Builder::finish`). -/
def pubRow (J : Fin 8) (j : Fin 128) : Fin (2 ^ 22) :=
  ⟨64 * J + j / 2, by have := J.isLt; have := j.isLt; simp only [Nat.reducePow]; omega⟩

/-- Its role: `X` for an even `j`, `Y` for an odd. -/
def pubRole (j : Fin 128) : Fin 4 := if (j : ℕ) % 2 = 0 then 0 else 1

/-- **The cell holding bit `j` of public word `J`.** -/
def pubCell (J : Fin 8) (j : Fin 128) : Fin (22 + 2) → Bool := rowCell (pubRow J j) (pubRole j)

/-- What the cell of bit `j` of public word `J` reads in `C`. -/
def ChiCircuit.pubSrc (C : ChiCircuit (Fin (2 ^ 22))) (J : Fin 8) (j : Fin 128) :
    Src (Fin (2 ^ 22)) :=
  if (j : ℕ) % 2 = 0 then C.x (pubRow J j) else C.y (pubRow J j)

/-- Bit `j` of public word `J` in the computation `v`. -/
def ChiCircuit.pubBit (C : ChiCircuit (Fin (2 ^ 22))) (v : Fin (2 ^ 22) → Bool) (J : Fin 8)
    (j : Fin 128) : Bool :=
  (C.pubSrc J j).bval v

theorem pubCell_eq_cellOf (J : Fin 8) (j : Fin 128) :
    pubCell J j = cellOf (256 * J + 4 * (j / 2) + j % 2) := by
  rw [pubCell, rowCell_eq_cellOf]
  congr 1
  have hr : ((pubRole j : Fin 4) : ℕ) = j % 2 := by
    unfold pubRole
    split_ifs with h
    · simp [h]
    · simp; omega
  simp only [pubRow, hr]
  ring

theorem pubCell_lt (J : Fin 8) (j : Fin 128) : 256 * (J : ℕ) + 4 * (j / 2) + j % 2 < 2 ^ 11 := by
  have := J.isLt; have := j.isLt; simp only [Nat.reducePow]; omega

theorem pubCell_injective (J : Fin 8) : Function.Injective (pubCell J) := by
  intro j j' h
  rw [pubCell_eq_cellOf, pubCell_eq_cellOf] at h
  have := cellOf_inj (lt_of_lt_of_le (pubCell_lt J j) (by norm_num))
    (lt_of_lt_of_le (pubCell_lt J j') (by norm_num)) h
  exact Fin.ext (by omega)

theorem bitAt_cellOf (n k : ℕ) (hk : k < 22 + 2) : bitAt (cellOf n) k = n.testBit k := by
  simp [bitAt, hk, cellOf]

/-- A cell's weight in word `J`, by its number: nonzero only below `2^11` and in the word's
block of 256 cells. -/
theorem regionWeight_cellOf {F : Type*} [Field F] (c : ℕ → F) (J : Fin 8) (n : ℕ)
    (hn : n < 2 ^ (22 + 2)) :
    regionWeight c J (cellOf n)
      = if n < 2 ^ 11 ∧ n / 256 = J then
          ∏ k ∈ range 8, (if n.testBit k then c k else 1) else 0 := by
  have hreg : (∀ j : Fin (22 + 2), 11 ≤ (j : ℕ) → cellOf n j = false) ↔ n < 2 ^ 11 := by
    constructor
    · intro h
      refine Nat.lt_pow_two_of_testBit n fun i hi => ?_
      by_cases hi' : i < 22 + 2
      · exact h ⟨i, hi'⟩ hi
      · exact Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
    · intro h j hj
      exact Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hj))
  have hword : n < 2 ^ 11 → (wordOf (cellOf n) = J ↔ n / 256 = J) := by
    intro h
    rw [Fin.ext_iff]
    show (n.testBit 8).toNat + 2 * (n.testBit 9).toNat + 4 * (n.testBit 10).toNat = _ ↔ _
    rw [Nat.toNat_testBit, Nat.toNat_testBit, Nat.toNat_testBit]
    simp only [Nat.reducePow] at h ⊢
    omega
  unfold regionWeight
  have hprod : ∏ k ∈ range 8, (if bitAt (cellOf n) k then c k else 1)
      = ∏ k ∈ range 8, (if n.testBit k then c k else 1) :=
    prod_congr rfl fun k hk => by
      rw [bitAt_cellOf n k (by have := mem_range.mp hk; omega)]
  rw [hprod]
  refine if_congr ⟨fun h => ⟨hreg.mp h.1, (hword (hreg.mp h.1)).mp h.2⟩,
    fun h => ⟨hreg.mpr h.1, (hword h.1).mpr h.2⟩⟩ rfl rfl

/-- **Word `J` reads only its 128 cells** when the coordinates give the roles `C, V` the weight
zero: a cell of nonzero weight is the cell of some bit of the word. -/
theorem exists_pubCell {F : Type*} [Field F] (c : ℕ → F) (hc1 : c 1 = 0) (J : Fin 8)
    (x : Fin (22 + 2) → Bool) (hx : regionWeight c J x ≠ 0) : ∃ j, x = pubCell J j := by
  obtain ⟨n, hn, rfl⟩ := exists_cellOf x
  rw [regionWeight_cellOf c J n hn] at hx
  split_ifs at hx with h
  swap
  · exact absurd rfl hx
  have h1 : n.testBit 1 = false := by
    by_contra h1
    refine hx (prod_eq_zero (mem_range.mpr (show 1 < 8 by norm_num)) ?_)
    rw [ite_eq_left (by simpa using h1), hc1]
  have h1' := Nat.toNat_testBit n 1
  rw [h1] at h1'
  obtain ⟨h11, hJ⟩ := h
  simp only [Nat.reducePow, Bool.toNat_false] at h11 h1'
  refine ⟨⟨n % 2 + 2 * (n % 256 / 4), by omega⟩, ?_⟩
  rw [pubCell_eq_cellOf]
  congr 1
  simp only
  omega

/-- **The weighted sum of word `J` is over its 128 cells.** -/
theorem sum_regionWeight {F : Type*} [Field F] [DecidableEq F] (c : ℕ → F) (hc1 : c 1 = 0)
    (J : Fin 8) (w : (Fin (22 + 2) → Bool) → F) :
    ∑ x, regionWeight c J x * w x = ∑ j : Fin 128, regionWeight c J (pubCell J j) * w (pubCell J j) := by
  classical
  have himg : ∑ x ∈ univ.image (pubCell J), regionWeight c J x * w x
      = ∑ j : Fin 128, regionWeight c J (pubCell J j) * w (pubCell J j) :=
    sum_image fun a _ b _ h => pubCell_injective J h
  rw [← himg]
  refine (sum_subset (subset_univ _) fun x _ hx => ?_).symm
  by_contra h
  obtain ⟨j, rfl⟩ := exists_pubCell c hc1 J x (left_ne_zero_of_mul h)
  exact hx (mem_image_of_mem _ (mem_univ j))

end Public

/-! ## The weights of the bits -/

section Weights

variable {F : Type*} [Field F]

/-- **The weight of bit `j` of a public word** (`quotient::protocol::bit_weight`):
`F192::new(1 << j, 0, 0)` for `j < 64` and `F192::new(0, 1 << (j - 64), 0)` above, that is
`x^j` and `Y x^(j - 64)`, `x` the generator of the base field `GF(2^64)`'s polynomial basis and
`Y` the extension's. The sum of a word's bits, each with its weight, is the element it reads as. -/
def bitWeight (x Y : F) (j : ℕ) : F := if j < 64 then x ^ j else Y * x ^ (j - 64)

/-- **The weight of coordinate `k < 8` of the public region** (`quotient::protocol::
coordinate_weight`), what the instance's `c k` is in the deployed circuit: bit 0 of a cell picks
bit 1 of the word, bit 1 picks the roles `C, V` (weight zero), bit `k ≥ 2` bit `2^(k - 1)`. -/
def coordWeight (x Y : F) (k : ℕ) : F :=
  if k = 0 then bitWeight x Y 1 else if k = 1 then 0 else bitWeight x Y (2 ^ (k - 1))

theorem coordWeight_one (x Y : F) : coordWeight x Y 1 = 0 := by simp [coordWeight]

theorem bitWeight_zero (x Y : F) : bitWeight x Y 0 = 1 := by simp [bitWeight]

private theorem ite_testBit (n k : ℕ) (a : F) :
    (if n.testBit k then a else 1) = a ^ (n / 2 ^ k % 2) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]

private theorem pub_bits (J j n : ℕ) (hj : j < 128) (hn : n = 256 * J + 4 * (j / 2) + j % 2) :
    n / 2 ^ 0 % 2 = j % 2 ∧ n / 2 ^ 1 % 2 = 0 ∧ n / 2 ^ 2 % 2 = j / 2 % 2 ∧
      n / 2 ^ 3 % 2 = j / 4 % 2 ∧ n / 2 ^ 4 % 2 = j / 8 % 2 ∧ n / 2 ^ 5 % 2 = j / 16 % 2 ∧
      n / 2 ^ 6 % 2 = j / 32 % 2 ∧ n / 2 ^ 7 % 2 = j / 64 := by
  simp only [Nat.reducePow, Nat.div_one]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem low_bits : ∀ i : Fin 128, (i : ℕ) % 2 + 2 * ((i : ℕ) / 2 % 2) + 4 * ((i : ℕ) / 4 % 2)
    + 8 * ((i : ℕ) / 8 % 2) + 16 * ((i : ℕ) / 16 % 2) + 32 * ((i : ℕ) / 32 % 2) = (i : ℕ) % 64 := by
  decide

/-- The weight of bit `j` of word `J`: the product of the weights of its cell's set bits
below 8. -/
theorem regionWeight_pubCell (c : ℕ → F) (J : Fin 8) (j : Fin 128) :
    regionWeight c J (pubCell J j)
      = ∏ k ∈ range 8,
          (if (256 * (J : ℕ) + 4 * ((j : ℕ) / 2) + (j : ℕ) % 2).testBit k then c k else 1) := by
  have hlt := pubCell_lt J j
  have hw : (256 * (J : ℕ) + 4 * (j / 2) + j % 2) / 256 = J := by
    have := j.isLt; omega
  rw [pubCell_eq_cellOf, regionWeight_cellOf _ J _ (lt_of_lt_of_le hlt (by norm_num)),
    ite_eq_left ⟨hlt, hw⟩]

private theorem prod_coordWeight (x Y : F) (J : Fin 8) (j : Fin 128) :
    (∏ k ∈ range 8, if (256 * (J : ℕ) + 4 * ((j : ℕ) / 2) + (j : ℕ) % 2).testBit k = true
      then coordWeight x Y k else 1) = bitWeight x Y j := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := pub_bits J j _ j.isLt rfl
  rw [prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ,
    prod_range_succ, prod_range_succ, prod_range_succ, prod_range_zero, one_mul]
  rw [ite_testBit, ite_testBit, ite_testBit, ite_testBit, ite_testBit, ite_testBit, ite_testBit,
    ite_testBit]
  have c0 : coordWeight x Y 0 = x := by simp [coordWeight, bitWeight]
  have c2 : coordWeight x Y 2 = x ^ 2 := by simp [coordWeight, bitWeight]
  have c3 : coordWeight x Y 3 = x ^ 4 := by simp [coordWeight, bitWeight]
  have c4 : coordWeight x Y 4 = x ^ 8 := by simp [coordWeight, bitWeight]
  have c5 : coordWeight x Y 5 = x ^ 16 := by simp [coordWeight, bitWeight]
  have c6 : coordWeight x Y 6 = x ^ 32 := by simp [coordWeight, bitWeight]
  have c7 : coordWeight x Y 7 = Y := by simp [coordWeight, bitWeight]
  rw [c0, coordWeight_one, c2, c3, c4, c5, c6, c7, b0, b1, b2, b3, b4, b5, b6, b7, pow_zero,
    mul_one, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
    ← pow_add, ← pow_add, ← pow_add, low_bits j]
  -- `omega` with the eight facts above in context is very slow.
  clear b0 b1 b2 b3 b4 b5 b6 b7
  have hj := j.isLt
  unfold bitWeight
  by_cases h : (j : ℕ) < 64
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, ite_eq_left h, pow_zero, mul_one]
  · have h1 : (j : ℕ) / 64 = 1 := by omega
    have h2 : (j : ℕ) % 64 = j - 64 := by omega
    rw [ite_eq_right h, h1, h2, pow_one]
    exact mul_comm _ _

/-- **Bit `j` of word `J` has the weight `bit_weight(j)`** under `coordinate_weight`'s weights. -/
theorem regionWeight_coordWeight (x Y : F) (J : Fin 8) (j : Fin 128) :
    regionWeight (coordWeight x Y) J (pubCell J j) = bitWeight x Y j := by
  rw [regionWeight_pubCell, prod_coordWeight]

/-- The weights of a word's 128 bits sum to `(1 + Y) (1 + x + … + x^63)`. -/
theorem sum_bitWeight (x Y : F) :
    ∑ j : Fin 128, bitWeight x Y j = (1 + Y) * ∑ i ∈ range 64, x ^ i := by
  rw [Fin.sum_univ_eq_sum_range (fun j => bitWeight x Y j) 128,
    show 128 = 64 + 64 by norm_num, sum_range_add, add_mul, one_mul, mul_sum]
  refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) (sum_congr rfl fun i _ => ?_)
  · simp [bitWeight, mem_range.mp hi]
  · simp [bitWeight]

/-- **The weights of a word's bits do not sum to zero** when `x ≠ 1` and `Y ≠ 1`: in
characteristic 2, `(1 + x + … + x^63)(x - 1) = x^64 - 1 = (x - 1)^64`. -/
theorem sum_bitWeight_ne_zero [CharP F 2] {x Y : F} (hx : x ≠ 1) (hY : Y ≠ 1) :
    ∑ j : Fin 128, bitWeight x Y j ≠ 0 := by
  rw [sum_bitWeight]
  refine mul_ne_zero (fun h => hY ?_) fun h => hx ?_
  · exact (CharTwo.add_eq_zero.mp h).symm
  · have hg := geom_sum_mul x 64
    rw [h, zero_mul, show (64 : ℕ) = 2 ^ 6 by norm_num, ← one_pow (2 ^ 6),
      ← sub_pow_char_pow (p := 2)] at hg
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hg.symm)

/-- **The bit weights are independent over `GF(2)`**: a nonempty set of them does not sum to
zero. It holds of `F192`'s `x^j`, `Y x^j` (`1, x, …, x^63` a basis of `GF(2^64)` over `GF(2)`,
and `1, Y` independent over `GF(2^64)`); here it is a hypothesis on `x` and `Y`. -/
def BitWeightsIndependent (x Y : F) : Prop :=
  ∀ a : Fin 128 → Bool, ∑ j : Fin 128, bitWeight x Y j * bitF (a j) = 0 → ∀ j, a j = false

/-- With independent weights, a word's value gives its bits. -/
theorem BitWeightsIndependent.eq [CharP F 2] {x Y : F} (h : BitWeightsIndependent x Y)
    {a b : Fin 128 → Bool}
    (hab : ∑ j : Fin 128, bitWeight x Y j * bitF (a j) = ∑ j : Fin 128, bitWeight x Y j * bitF (b j)) :
    a = b := by
  have hx := h (fun j => xor (a j) (b j)) (by
    simp only [bitF_xor, mul_add, sum_add_distrib, hab]
    exact CharTwo.add_self_eq_zero _)
  funext j
  have := hx j
  cases ha : a j <;> cases hb : b j <;> simp_all

theorem BitWeightsIndependent.ne_one [CharP F 2] {x Y : F} (h : BitWeightsIndependent x Y) :
    x ≠ 1 ∧ Y ≠ 1 := by
  have two : ∀ i k : Fin 128, i ≠ k → bitWeight x Y i + bitWeight x Y k = 0 → False := by
    intro i k hik hs
    have := h (fun j => decide (j = i ∨ j = k)) (by
      rw [sum_eq_add_of_mem i k (mem_univ _) (mem_univ _) hik fun c _ hc => by
        simp [bitF, hc.1, hc.2]]
      simpa [bitF, hik, Ne.symm hik] using hs) i
    simp at this
  refine ⟨fun hx => two 0 1 (by decide) ?_, fun hY => two 0 64 (by decide) ?_⟩
  · simp [bitWeight, hx, CharTwo.add_self_eq_zero]
  · simp [bitWeight, hY, CharTwo.add_self_eq_zero]

end Weights

/-! ## The statement -/

section Statement

variable {F : Type*} [Field F]

/-- Byte `i` of 32, as a number (zero past the end). -/
def byteAt (b : Fin 32 → UInt8) (i : ℕ) : ℕ := if h : i < 32 then (b ⟨i, h⟩).toNat else 0

/-- `u128::from_be_bytes` of half `h` of 32 bytes: byte `16 h + t` is the digit of `256^(15 - t)`. -/
def halfValue (b : Fin 32 → UInt8) (h : Fin 2) : ℕ :=
  ∑ t ∈ range 16, byteAt b (16 * h + t) * 256 ^ (15 - t)

/-- An element of `GF(2^64)` given as a `u64` in the polynomial basis: bit `i` is the coefficient
of `x^i`. -/
def limb (x : F) (n : ℕ) : F := ∑ i : Fin 64, if n.testBit i then x ^ (i : ℕ) else 0

/-- **`statement::halves`**, one half: `F192::new(v as u64, (v >> 64) as u64, 0)`, `v` the half
read big-endian; the element `c0 + c1 Y` with `c0`, `c1` its low and high 64 bits. -/
def half (x Y : F) (b : Fin 32 → UInt8) (h : Fin 2) : F :=
  limb x (halfValue b h % 2 ^ 64) + Y * limb x (halfValue b h / 2 ^ 64 % 2 ^ 64)

/-- `Statement::halves`: `y` then `root`, each as its two halves. -/
def halves (x Y : F) (y root : Fin 32 → UInt8) : Fin 4 → F :=
  ![half x Y y 0, half x Y y 1, half x Y root 0, half x Y root 1]

/-- **The eight public words of the statement `(y, root)`**: its four halves, then `1, 0, 0, 0`,
the words the verifier's target adds (`reduce`'s `target`; `membership_target`). -/
def statementWords (x Y : F) (y root : Fin 32 → UInt8) : Fin 8 → F :=
  ![halves x Y y root 0, halves x Y y root 1, halves x Y y root 2, halves x Y y root 3, 1, 0, 0, 0]

/-- Its words 4 to 7 are `(1, 0, 0, 0)`. -/
theorem statementWords_high (x Y : F) (y root : Fin 32 → UInt8) :
    statementWords x Y y root 4 = 1 ∧ statementWords x Y y root 5 = 0 ∧
      statementWords x Y y root 6 = 0 ∧ statementWords x Y y root 7 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Its words 0 to 3 are the halves. -/
theorem statementWords_low (x Y : F) (y root : Fin 32 → UInt8) (J : Fin 4) :
    statementWords x Y y root (Fin.castLE (by norm_num) J) = halves x Y y root J := by
  fin_cases J <;> rfl

/-- It is the form `membership_target` reads. -/
theorem statementWords_eq (x Y : F) (y root : Fin 32 → UInt8) :
    statementWords x Y y root = ![halves x Y y root 0, halves x Y y root 1, halves x Y y root 2,
      halves x Y y root 3, 1, 0, 0, 0] := rfl

/-- **Bit `j` of word `J < 4` of the statement**: bit `j % 8` of byte `16 h + 15 - j / 8` of `y`
(words 0, 1) or `root` (words 2, 3), `h = J % 2` (`circuit::public_words`). -/
def statementBit (y root : Fin 32 → UInt8) (J : Fin 4) (j : Fin 128) : Bool :=
  (byteAt (if (J : ℕ) < 2 then y else root) (16 * (J % 2) + 15 - j / 8)).testBit (j % 8)

theorem byteAt_lt (b : Fin 32 → UInt8) (i : ℕ) : byteAt b i < 2 ^ 8 := by
  unfold byteAt
  split_ifs
  · exact UInt8.toNat_lt _
  · norm_num

/-- The bits of a number written in base 256. -/
theorem testBit_sum_bytes (D : ℕ → ℕ) (hD : ∀ s, D s < 2 ^ 8) :
    ∀ (n j : ℕ), j < 8 * n →
      (∑ s ∈ range n, D s * 256 ^ s).testBit j = (D (j / 8)).testBit (j % 8) := by
  intro n
  induction n generalizing D with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have hsum : ∑ s ∈ range (n + 1), D s * 256 ^ s
        = 2 ^ 8 * ∑ s ∈ range n, D (s + 1) * 256 ^ s + D 0 := by
      rw [sum_range_succ', mul_sum]
      congr 1
      · exact sum_congr rfl fun s _ => by ring
      · simp
    rw [hsum, Nat.testBit_two_pow_mul_add _ (hD 0)]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [ih (fun s => D (s + 1)) (fun s => hD _) (j - 8) (by omega)]
      have e1 : (j - 8) / 8 + 1 = j / 8 := by omega
      have e2 : (j - 8) % 8 = j % 8 := by omega
      simp only [e1, e2]

/-- **The bits of a half**: bit `j` of `u128::from_be_bytes` of half `h` is bit `j % 8` of byte
`16 h + 15 - j / 8`. -/
theorem testBit_halfValue (b : Fin 32 → UInt8) (h : Fin 2) (j : ℕ) (hj : j < 128) :
    (halfValue b h).testBit j = (byteAt b (16 * h + 15 - j / 8)).testBit (j % 8) := by
  have hv : halfValue b h = ∑ s ∈ range 16, byteAt b (16 * h + 15 - s) * 256 ^ s := by
    unfold halfValue
    rw [← sum_range_reflect]
    refine sum_congr rfl fun s hs => ?_
    have := mem_range.mp hs
    congr 2 <;> omega
  rw [hv, testBit_sum_bytes (fun s => byteAt b (16 * h + 15 - s)) (fun s => byteAt_lt _ _) 16 j
    (by omega)]

/-- A limb is the sum of its bits' weights. -/
theorem limb_eq (x : F) (n : ℕ) :
    limb x n = ∑ i ∈ range 64, x ^ i * bitF (n.testBit i) := by
  unfold limb
  rw [Fin.sum_univ_eq_sum_range (fun i => if n.testBit i then x ^ i else 0) 64]
  exact sum_congr rfl fun i _ => by cases n.testBit i <;> simp [bitF]

/-- **A half is the sum of its 128 bits, each with its weight.** -/
theorem half_eq_sum (x Y : F) (b : Fin 32 → UInt8) (h : Fin 2) :
    half x Y b h = ∑ j : Fin 128, bitWeight x Y j * bitF ((halfValue b h).testBit j) := by
  unfold half
  rw [limb_eq, limb_eq, Fin.sum_univ_eq_sum_range (fun j => bitWeight x Y j *
    bitF ((halfValue b h).testBit j)) 128, show 128 = 64 + 64 by norm_num, sum_range_add, mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun i hi => ?_
    have hi := mem_range.mp hi
    have t : (halfValue b h % 2 ^ 64).testBit i = (halfValue b h).testBit i := by
      rw [Nat.testBit_mod_two_pow]
      simp [hi]
    rw [t]
    simp [bitWeight, hi]
  · refine sum_congr rfl fun i hi => ?_
    have hi := mem_range.mp hi
    have t : (halfValue b h / 2 ^ 64 % 2 ^ 64).testBit i = (halfValue b h).testBit (64 + i) := by
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, add_comm]
      simp [hi]
    rw [t]
    simp [bitWeight, mul_assoc]

/-- **A word of the statement is the sum of its bits, each with its weight.** -/
theorem halves_eq_sum (x Y : F) (y root : Fin 32 → UInt8) (J : Fin 4) :
    halves x Y y root J = ∑ j : Fin 128, bitWeight x Y j * bitF (statementBit y root J j) := by
  have hJ : halves x Y y root J = half x Y (if (J : ℕ) < 2 then y else root) ⟨J % 2, by omega⟩ := by
    fin_cases J <;> rfl
  rw [hJ, half_eq_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [testBit_halfValue _ _ _ j.isLt]
  rfl

end Statement

/-! ## A circuit laid on the cells -/

section Laid

/-- **The zero's anchor**: bit 0 of word 5, the `X` cell of row 320 (`circuit.rs`'s
`zero_anchor`). -/
def zeroCell : Fin (22 + 2) → Bool := pubCell 5 0

/-- **The one's anchor**: bit 0 of word 4, the `X` cell of row 256 (`one_anchor`). -/
def oneCell : Fin (22 + 2) → Bool := pubCell 4 0

/-- The cell whose cycle carries what a cell reads: a constant's anchor, or the row's `V` cell. -/
def anchor : Src (Fin (2 ^ 22)) → Fin (22 + 2) → Bool
  | .zero => zeroCell
  | .one => oneCell
  | .row r => rowCell r 3

/-- `cell` is on the cycle of the wiring `σ` through the anchor of `s`. -/
def Reads (σ : Equiv.Perm (Fin (22 + 2) → Bool)) (cell : Fin (22 + 2) → Bool)
    (s : Src (Fin (2 ^ 22))) : Prop :=
  ∃ n : ℕ, (σ ^ n) cell = anchor s

/-- **The circuit `C` laid on the cells by the wiring `σ`**, as `Builder::finish` lays it and
`membership_is_a_wired_loop_free_circuit` tests it. `C` is loop-free by its type (`ChiCircuit`:
an input row reads its own output in `X`, `Y` and `C`; every other row reads constants or rows of
lower rank), its rows are numbered as in `quotient::circuit`, and:

* `reads`: every `X`, `Y`, `C` cell is on the cycle of what it reads: the `V` cell of the row it
  reads, or the constant's anchor, `zeroCell` (bit 0 of word 5) or `oneCell` (bit 0 of word 4);
* `word5`: the 128 bits of public word 5 read the zero, so they are all on the zero's cycle;
* `word4_one`, `word4`: bit 0 of public word 4 reads the one (the one's anchor reads the one) and
  its other 127 bits the zero.

What soundness does not need, and Rust also tests, is what makes an honest proof exist: the zero
and one cycles distinct, no `V` cell on them, a cycle being exactly a source and its readers, the
public rows ranked last and words 0 to 3 reading computed rows. -/
structure Laid (σ : Equiv.Perm (Fin (22 + 2) → Bool)) (C : ChiCircuit (Fin (2 ^ 22))) : Prop where
  reads : ∀ r, Reads σ (rowCell r 0) (C.x r) ∧ Reads σ (rowCell r 1) (C.y r) ∧
    Reads σ (rowCell r 2) (C.c r)
  word5 : ∀ j, C.pubSrc 5 j = .zero
  word4_one : C.pubSrc 4 0 = .one
  word4 : ∀ j, j ≠ 0 → C.pubSrc 4 j = .zero

/-- The cell of bit `j` of public word `J` is on the cycle of what it reads. -/
theorem Laid.reads_pub {σ : Equiv.Perm (Fin (22 + 2) → Bool)} {C : ChiCircuit (Fin (2 ^ 22))}
    (hC : Laid σ C) (J : Fin 8) (j : Fin 128) : Reads σ (pubCell J j) (C.pubSrc J j) := by
  unfold pubCell pubRole ChiCircuit.pubSrc
  split_ifs
  · exact (hC.reads _).1
  · exact (hC.reads _).2.1

variable {F : Type*} [Field F] [CharP F 2]

/-- **The cells `w` hold `C`'s computation `v`**: `v` satisfies every gate of `C` on bits (so it is
`C`'s computation on its input bits, `bits_determined`), each `X`, `Y`, `C` cell holds the bit
it reads and each `V` cell its row's bit. -/
def ChiCircuit.Computes (C : ChiCircuit (Fin (2 ^ 22))) (w : (Fin (22 + 2) → Bool) → F)
    (v : Fin (2 ^ 22) → Bool) : Prop :=
  C.SatisfiesBits v ∧ ∀ r, w (rowCell r 0) = bitF ((C.x r).bval v) ∧
    w (rowCell r 1) = bitF ((C.y r).bval v) ∧ w (rowCell r 2) = bitF ((C.c r).bval v) ∧
    w (rowCell r 3) = bitF (v r)

/-- Public word `J` of the computation `v`, as a field element: its bits with their weights. -/
def ChiCircuit.pubWord (C : ChiCircuit (Fin (2 ^ 22))) (x Y : F) (v : Fin (2 ^ 22) → Bool)
    (J : Fin 8) : F :=
  ∑ j : Fin 128, bitWeight x Y j * bitF (C.pubBit v J j)

/-- **The cells `w` prove the statement `(y, root)` in `C`**: they hold a computation of `C`
whose public words 0 to 3 are the statement's halves. -/
def ChiCircuit.Proves (C : ChiCircuit (Fin (2 ^ 22))) (x Y : F) (w : (Fin (22 + 2) → Bool) → F)
    (y root : Fin 32 → UInt8) : Prop :=
  ∃ v, C.Computes w v ∧ ∀ J : Fin 4, C.pubWord x Y v (Fin.castLE (by norm_num) J) = halves x Y y root J

/-- **The same, bit by bit**: the computation's public bits are the statement's bytes' bits, as
`circuit::public_words` reads them. -/
def ChiCircuit.ProvesBits (C : ChiCircuit (Fin (2 ^ 22))) (w : (Fin (22 + 2) → Bool) → F)
    (y root : Fin 32 → UInt8) : Prop :=
  ∃ v, C.Computes w v ∧
    ∀ (J : Fin 4) (j : Fin 128), C.pubBit v (Fin.castLE (by norm_num) J) j = statementBit y root J j

/-- With independent bit weights, proving the statement's words is proving its bits. -/
theorem ChiCircuit.Proves.bits {C : ChiCircuit (Fin (2 ^ 22))} {x Y : F}
    (hind : BitWeightsIndependent x Y) {w : (Fin (22 + 2) → Bool) → F} {y root : Fin 32 → UInt8}
    (h : C.Proves x Y w y root) : C.ProvesBits w y root := by
  obtain ⟨v, hv, hw⟩ := h
  refine ⟨v, hv, fun J => ?_⟩
  have := hw J
  rw [ChiCircuit.pubWord, halves_eq_sum] at this
  exact congrFun (hind.eq this)

end Laid

end QuotientSecurity
