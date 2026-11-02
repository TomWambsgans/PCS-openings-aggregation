-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.DomainPoly
import UniComplete.DomainCount
import UniComplete.DomainPositions

/-!
# The active rows' vanishing polynomials (milestone 4, the domain facts; iteration 2, F1b)

For a height-`r` table (`r ≤ 31`) with `count ≤ 2^r` active rows, the verifier reads the vanishing
polynomial of the active rows at `t` from the count's bits (`activeVanishingFromBits`, the bits as
`countBits` returns them: `(List.range (r + 1)).map fun b ↦ intBits count b 1`). Here it is a polynomial:

* `zActP count r`: `wP r` for a full table, else `Π_{b < r, bit b of count} (wP b + cosetOffset r b)`;
  `activeVanishingFromBits_eq`: the verifier's value at the digits of `t` is `(zActP count r).eval t`
  (`n ≥ r + 1` digits; in characteristic two `1 + c·(w + K + 1)` is `w + K` at `c = 1` and `1` at `c = 0`);
* `zActP_monic`, `zActP_natDegree` (`= count`), `zActP_eval_pointE_eq_zero_iff`: at `ω_i`, `i < 2^r`, it
  vanishes exactly on the active rows (`isActive`);
* `zActP_eq_linProd`: it is `Π_{j ∈ activePositions} (X − ω_j)`; hence `zActP_dvd` (`zActP ∣ wP r`) and
  `zPadP count r := wP r /ₘ zActP count r`, the padding rows' polynomial `Π_{j ∉ activePositions} (X − ω_j)`
  (`zPadP_eq_linProd`), of degree `2^r − count` (`zPadP_natDegree`), vanishing at `ω_i` exactly on the inactive
  rows (`zPadP_eval_pointE_eq_zero_iff`), and `zActP · zPadP = wP r` (`zActP_mul_zPadP`).
-/

namespace UniComplete.Domain

open LeanVM.Parameters UniStatement Finset Polynomial

/-- **The active rows' vanishing polynomial**: `w_r` for a full table, else the product over the count's set
bits `b < r` of `w_b + K_b`, `K_b = cosetOffset r b` (bit `b`'s coset is `{x : w_b(x) = K_b}`). -/
noncomputable def zActP (count r : ℕ) : E[X] :=
  if count = 2 ^ r then wP r
  else ∏ b ∈ (range r).filter (fun b ↦ count.testBit b = true), (wP b + C (cosetOffset r b))

/-- **The padding rows' vanishing polynomial**: `w_r / Z_act`. -/
noncomputable def zPadP (count r : ℕ) : E[X] := wP r /ₘ zActP count r

/-! ### The verifier's value -/

theorem bits_getD (count r : ℕ) {b : ℕ} (hb : b ≤ r) :
    ((List.range (r + 1)).map fun b ↦ intBits count b 1).getD b 0 = if count.testBit b then 1 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
    Option.getD_some, intBits_one]

/-- **The verifier's `Z_act(t)` is `zActP` at `t`** (`r ≤ 31`, `count ≤ 2^r`, `n ≥ r + 1` digits). -/
theorem activeVanishingFromBits_eq {count r n : ℕ} (hc : count ≤ 2 ^ r) (hn : r + 1 ≤ n) (t : E) :
    activeVanishingFromBits (digits t n) ((List.range (r + 1)).map fun b ↦ intBits count b 1) r =
      (zActP count r).eval t := by
  unfold activeVanishingFromBits
  rw [foldl_mul_eq_prod, prod_map_range, bits_getD count r le_rfl, ← wP_eval_digits t (by omega)]
  have hfac : ∀ b ∈ range r, (1 + ((List.range (r + 1)).map fun b ↦ intBits count b 1).getD b 0 *
      ((digits t n).getD b 0 + (cosetOffset r b + 1))) =
      if count.testBit b = true then (wP b).eval t + cosetOffset r b else 1 := by
    intro b hb
    rw [Finset.mem_range] at hb
    rw [bits_getD count r hb.le, ← wP_eval_digits t (by omega)]
    split_ifs
    · linear_combination two_eq_zero_E
    · ring
  rw [Finset.prod_congr rfl hfac]
  unfold zActP
  by_cases hf : count = 2 ^ r
  · subst hf
    have hone : ∀ b ∈ range r,
        (if (2 ^ r).testBit b = true then (wP b).eval t + cosetOffset r b else 1) = 1 := by
      intro b hb
      have hbr : r ≠ b := by rw [Finset.mem_range] at hb; omega
      simp only [Nat.testBit_two_pow_of_ne hbr, Bool.false_eq_true, ite_false]
    rw [ite_pos_of rfl, Nat.testBit_two_pow_self, Finset.prod_congr rfl hone, Finset.prod_const_one,
      mul_one, ite_pos_of rfl]
    linear_combination two_eq_zero_E
  · rw [ite_neg_of hf, Nat.testBit_eq_false_of_lt (lt_of_le_of_ne hc hf), Polynomial.eval_prod,
      Finset.prod_filter]
    simp only [Bool.false_eq_true, ite_false, zero_mul, add_zero, one_mul, Polynomial.eval_add,
      Polynomial.eval_C]

/-! ### Degree and roots -/

theorem wP_add_C_monic (b : ℕ) (k : E) : (wP b + C k).Monic := by
  refine (wP_monic b).add_of_left (lt_of_le_of_lt degree_C_le ?_)
  exact natDegree_pos_iff_degree_pos.mp (by rw [wP_natDegree]; exact Nat.two_pow_pos b)

/-- The sum of the set bits below `r`, as a `Finset` sum. -/
theorem sum_filter_bits (n r : ℕ) : ∑ b ∈ (range r).filter (fun b ↦ n.testBit b = true), 2 ^ b = n % 2 ^ r := by
  rw [Finset.sum_filter, ← sum_bits_true n r]
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

/-- **`Z_act` is monic.** -/
theorem zActP_monic (count r : ℕ) : (zActP count r).Monic := by
  unfold zActP
  split_ifs
  · exact wP_monic r
  · exact monic_prod_of_monic _ _ fun b _ ↦ wP_add_C_monic b _

/-- **`Z_act` has degree `count`.** -/
theorem zActP_natDegree {count r : ℕ} (hc : count ≤ 2 ^ r) : (zActP count r).natDegree = count := by
  unfold zActP
  split_ifs with hf
  · rw [wP_natDegree, hf]
  · rw [natDegree_prod_of_monic _ _ fun b _ ↦ wP_add_C_monic b _]
    simp only [natDegree_add_C, wP_natDegree]
    rw [sum_filter_bits, Nat.mod_eq_of_lt (lt_of_le_of_ne hc hf)]

/-- **Row `i`'s gap test is a coset test on the digits**: `ω_{i >> b} = K_b` exactly when `i` is in bit `b`'s
coset, `b < r`, `i < 2^r`. -/
theorem shift_eq_coset_iff {r b i : ℕ} (hb : b < r) (hi : i < 2 ^ r) :
    i >>> b = 2 ^ (r - b) - 2 ↔ 2 ^ r - 2 ^ (b + 1) ≤ i ∧ i < 2 ^ r - 2 ^ b := by
  have hP : 0 < 2 ^ b := Nat.two_pow_pos b
  have hQ : 2 ≤ 2 ^ (r - b) :=
    le_trans (le_of_eq (pow_one 2).symm) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hN : 2 ^ r = 2 ^ (r - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hb.le]
  have e1 := two_pow_succ' b
  have h2 : 2 ^ (b + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hb
  have hlo : (2 ^ (r - b) - 2) * 2 ^ b = 2 ^ r - 2 ^ (b + 1) := by rw [Nat.sub_mul, ← hN, e1]
  have hhi : (2 ^ (r - b) - 2 + 1) * 2 ^ b = 2 ^ r - 2 ^ b := by
    rw [Nat.add_mul, hlo, one_mul]
    omega
  rw [Nat.shiftRight_eq_div_pow]
  constructor
  · intro h
    have h1 := Nat.div_mul_le_self i (2 ^ b)
    have h3 := Nat.lt_div_mul_add (a := i) hP
    rw [h, hlo] at h1
    rw [h] at h3
    have h4 : (2 ^ (r - b) - 2) * 2 ^ b + 2 ^ b = 2 ^ r - 2 ^ b := by rw [← hhi, Nat.add_mul, one_mul]
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h3⟩
    exact Nat.div_eq_of_lt_le (by rw [hlo]; exact h1) (by rw [hhi]; exact h3)

/-- **`Z_act` vanishes at `ω_i` exactly on the active rows** (`i < 2^r`). -/
theorem zActP_eval_pointE_eq_zero_iff {count r i : ℕ} (hr : r ≤ 31) (hi : i < 2 ^ r) :
    (zActP count r).eval (pointE i) = 0 ↔ isActive i count r = true := by
  have h31 : 2 ^ r ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) hr
  have hi32 : i < 2 ^ 32 := by omega
  unfold zActP
  by_cases hf : count = 2 ^ r
  · rw [ite_pos_of hf, wP_eval_pointE r hi32, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hi, pointE_zero]
    unfold isActive
    rw [ite_pos_of hf]
    simp
  · rw [ite_neg_of hf, isActive_iff_exists hi hf, eval_prod, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_filter, Finset.mem_range, Polynomial.eval_add, Polynomial.eval_C]
    refine exists_congr fun b ↦ ?_
    constructor
    · rintro ⟨⟨hb, hbit⟩, h⟩
      rw [wP_eval_pointE b hi32, cosetOffset, CharTwo.add_eq_zero] at h
      have hs : i >>> b < 2 ^ 32 := lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hi32
      have hk : 2 ^ (r - b) - 2 < 2 ^ 32 :=
        lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by norm_num))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact ⟨hb, hbit, (shift_eq_coset_iff hb hi).mp (pointE_injOn hs hk h)⟩
    · rintro ⟨hb, hbit, hmem⟩
      refine ⟨⟨hb, hbit⟩, ?_⟩
      rw [wP_eval_pointE b hi32, cosetOffset, (shift_eq_coset_iff hb hi).mpr hmem, CharTwo.add_eq_zero]

/-! ### Products of linear factors -/

theorem activePositions_toFinset_card {count r : ℕ} (hc : count ≤ 2 ^ r) :
    (activePositions count r).toFinset.card = count := by
  rw [List.toFinset_card_of_nodup (activePositions_nodup count r), activePositions_length hc]

theorem activePositions_toFinset_subset (count r : ℕ) :
    (activePositions count r).toFinset ⊆ range (2 ^ r) := fun _ hj ↦
  Finset.mem_range.mpr (lt_of_mem_activePositions (List.mem_toFinset.mp hj))

/-- **`Z_act = Π_{j ∈ activePositions} (X − ω_j)`.** -/
theorem zActP_eq_linProd {count r : ℕ} (hr : r ≤ 31) (hc : count ≤ 2 ^ r) :
    zActP count r = linProd (activePositions count r).toFinset := by
  have h31 : 2 ^ r ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) hr
  refine eq_linProd (zActP_monic count r) (by rw [zActP_natDegree hc, activePositions_toFinset_card hc])
    (fun _ hj ↦ ?_) fun _ hj ↦ ?_
  · have := lt_of_mem_activePositions (List.mem_toFinset.mp hj)
    omega
  · have hlt := lt_of_mem_activePositions (List.mem_toFinset.mp hj)
    exact (zActP_eval_pointE_eq_zero_iff hr hlt).mpr
      ((mem_activePositions_iff hlt).mp (List.mem_toFinset.mp hj))

/-- **`Z_act ∣ w_r`.** -/
theorem zActP_dvd {count r : ℕ} (hr : r ≤ 31) (hc : count ≤ 2 ^ r) : zActP count r ∣ wP r := by
  rw [zActP_eq_linProd hr hc, wP_eq_linProd (by omega)]
  exact linProd_dvd (activePositions_toFinset_subset count r)

/-- **`Z_pad = Π_{j < 2^r, j ∉ activePositions} (X − ω_j)`.** -/
theorem zPadP_eq_linProd {count r : ℕ} (hr : r ≤ 31) (hc : count ≤ 2 ^ r) :
    zPadP count r = linProd (range (2 ^ r) \ (activePositions count r).toFinset) := by
  rw [zPadP, zActP_eq_linProd hr hc, wP_eq_linProd (by omega),
    linProd_divByMonic (activePositions_toFinset_subset count r)]

/-- **`Z_act · Z_pad = w_r`.** -/
theorem zActP_mul_zPadP {count r : ℕ} (hr : r ≤ 31) (hc : count ≤ 2 ^ r) :
    zActP count r * zPadP count r = wP r := by
  rw [zPadP_eq_linProd hr hc, zActP_eq_linProd hr hc, wP_eq_linProd (by omega), linProd, linProd, linProd,
    mul_comm, Finset.prod_sdiff (activePositions_toFinset_subset count r)]

theorem zPadP_monic {count r : ℕ} (hr : r ≤ 31) (hc : count ≤ 2 ^ r) : (zPadP count r).Monic := by
  rw [zPadP_eq_linProd hr hc]
  exact linProd_monic _

/-- **`Z_pad` has degree `2^r − count`.** -/
theorem zPadP_natDegree {count r : ℕ} (hr : r ≤ 31) (hc : count ≤ 2 ^ r) :
    (zPadP count r).natDegree = 2 ^ r - count := by
  rw [zPadP_eq_linProd hr hc, linProd_natDegree,
    Finset.card_sdiff_of_subset (activePositions_toFinset_subset count r), Finset.card_range,
    activePositions_toFinset_card hc]

/-- **`Z_pad` vanishes at `ω_i` exactly on the inactive rows** (`i < 2^r`). -/
theorem zPadP_eval_pointE_eq_zero_iff {count r i : ℕ} (hr : r ≤ 31) (hc : count ≤ 2 ^ r) (hi : i < 2 ^ r) :
    (zPadP count r).eval (pointE i) = 0 ↔ isActive i count r = false := by
  have h31 : 2 ^ r ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) hr
  rw [zPadP_eq_linProd hr hc, linProd_eval_pointE_eq_zero_iff (fun _ hj ↦ ?_) (by omega), Finset.mem_sdiff,
    List.mem_toFinset, mem_activePositions_iff hi, Finset.mem_range]
  · simp [hi]
  · have := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
    omega

end UniComplete.Domain

/-- info: 'UniComplete.Domain.activeVanishingFromBits_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.activeVanishingFromBits_eq

/-- info: 'UniComplete.Domain.zActP_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.zActP_monic

/-- info: 'UniComplete.Domain.zActP_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.zActP_natDegree

/-- info: 'UniComplete.Domain.zActP_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.zActP_dvd

/-- info: 'UniComplete.Domain.zPadP_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.zPadP_natDegree

/-- info: 'UniComplete.Domain.zActP_eval_pointE_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.zActP_eval_pointE_eq_zero_iff

/-- info: 'UniComplete.Domain.zPadP_eval_pointE_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.zPadP_eval_pointE_eq_zero_iff

/-- info: 'UniComplete.Domain.zActP_mul_zPadP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.zActP_mul_zPadP
