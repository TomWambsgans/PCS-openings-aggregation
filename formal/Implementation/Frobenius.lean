-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Semantics

/-!
# The Frobenius node is `x^(2^64)`

`frobE` (`F192::frobenius`, the graph's `frob` node) is `x ↦ x^(2^64)` in any field whose limbs are
`F192`'s (`frobOK`): the elements of one limb, `K`, are closed under products, so each nonzero one
has order dividing `2^64 - 1` (`base_pow`); `y^(2^64) = y^2` and `y^4 = y^2 + y` are computed; and
an element is `c0 + c1 y + c2 y^2` with its limbs in `K`.
-/

set_option linter.unusedSectionVars false

namespace Implementation

/-! ## Carry-less products by `0` and `1` -/

theorem foldl_fixed (f : Nat → Nat → Nat) (hf : ∀ acc i, f acc i = acc) :
    ∀ (l : List Nat) (acc : Nat), l.foldl f acc = acc
  | [], _ => rfl
  | i :: l, acc => by rw [List.foldl_cons, hf, foldl_fixed f hf l]

theorem clmul_zero_left (b : Nat) : clmul 0 b = 0 :=
  foldl_fixed _ (fun acc i => by simp) _ 0

theorem clmul_zero_right (a : Nat) : clmul a 0 = 0 :=
  foldl_fixed _ (fun acc i => by simp) _ 0

theorem clmul_one_aux (c : Nat) : ∀ n, (List.range n).foldl
    (fun acc i => if c.testBit i then acc ^^^ (1 <<< i) else acc) 0 = c % 2 ^ n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, clmul_one_aux c n, List.foldl_cons, List.foldl_nil]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    split_ifs with hn
    · rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.one_shiftLeft, Nat.testBit_two_pow]
      rcases lt_trichotomy j n with h | rfl | h
      · simp [h, show j < n + 1 by omega, show n ≠ j by omega]
      · simp [hn]
      · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega, show n ≠ j by omega]
    · rw [Nat.testBit_mod_two_pow]
      rcases lt_trichotomy j n with h | rfl | h
      · simp [h, show j < n + 1 by omega]
      · simp [hn]
      · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega]

theorem clmul_one_right {c : Nat} (hc : c < B64) : clmul c 1 = c := by
  rw [clmul, clmul_one_aux, Nat.mod_eq_of_lt (show c < 2 ^ 64 from hc)]

theorem reduce64_small {c : Nat} (hc : c < B64) : reduce64 c = c := by
  have h1 : c >>> 64 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hc
  simp [reduce64, h1, Nat.mod_eq_of_lt hc]

theorem limb_small {c : Nat} (hc : c < B64) : limb c 0 = c ∧ limb c 1 = 0 ∧ limb c 2 = 0 := by
  simp only [limb_eq]
  norm_num
  unfold B64 at hc
  omega

/-- A product of two elements of one limb. -/
theorem mulE_small {c d : Nat} (hc : c < B64) (hd : d < B64) : mulE c d = reduce64 (clmul c d) := by
  obtain ⟨c0, c1, c2⟩ := limb_small hc
  obtain ⟨d0, d1, d2⟩ := limb_small hd
  simp only [mulE, c0, c1, c2, d0, d1, d2, clmul_zero_left, clmul_zero_right, Nat.xor_zero,
    Nat.zero_xor, show reduce64 0 = 0 by decide, ofLimbs]
  simp

/-- The product of a limb and `y`. -/
theorem mulE_Y {c : Nat} (hc : c < B64) : mulE c B64 = B64 * c := by
  obtain ⟨c0, c1, c2⟩ := limb_small hc
  have y0 : limb B64 0 = 0 := by decide
  have y1 : limb B64 1 = 1 := by decide
  have y2 : limb B64 2 = 0 := by decide
  simp only [mulE, c0, c1, c2, y0, y1, y2, clmul_zero_left, clmul_zero_right, Nat.xor_zero,
    Nat.zero_xor, clmul_one_right hc, reduce64_small hc, show reduce64 0 = 0 by decide, ofLimbs]
  ring

/-- The product of a limb and `y^2`. -/
theorem mulE_Y2 {c : Nat} (hc : c < B64) : mulE c (B64 * B64) = B64 * B64 * c := by
  obtain ⟨c0, c1, c2⟩ := limb_small hc
  have y0 : limb (B64 * B64) 0 = 0 := by decide
  have y1 : limb (B64 * B64) 1 = 0 := by decide
  have y2 : limb (B64 * B64) 2 = 1 := by decide
  simp only [mulE, c0, c1, c2, y0, y1, y2, clmul_zero_left, clmul_zero_right, Nat.xor_zero,
    Nat.zero_xor, clmul_one_right hc, reduce64_small hc, show reduce64 0 = 0 by decide, ofLimbs]
  ring

theorem ofLimbs_xor {c0 c1 c2 : Nat} (h0 : c0 < B64) (h1 : c1 < B64) (h2 : c2 < B64) :
    ofLimbs c0 c1 c2 = c0 ^^^ (B64 * c1) ^^^ (B64 * B64 * c2) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have e : ofLimbs c0 c1 c2 = 2 ^ 64 * (c1 + 2 ^ 64 * c2) + c0 := by
    unfold ofLimbs B64; ring
  rw [e, Nat.testBit_two_pow_mul_add _ (show c0 < 2 ^ 64 from h0), Nat.testBit_xor, Nat.testBit_xor,
    show B64 * c1 = 2 ^ 64 * c1 from rfl, show B64 * B64 * c2 = 2 ^ 128 * c2 by unfold B64; ring,
    Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul]
  have hc1 : c1 + 2 ^ 64 * c2 = 2 ^ 64 * c2 + c1 := by ring
  by_cases hj : j < 64
  · simp [hj, show ¬ 128 ≤ j by omega, show ¬ 64 ≤ j by omega]
  · rw [if_neg hj, hc1, Nat.testBit_two_pow_mul_add _ (show c1 < 2 ^ 64 from h1),
      Nat.testBit_lt_two_pow
      (show c0 < 2 ^ j from lt_of_lt_of_le (show c0 < 2 ^ 64 from h0) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    by_cases hj2 : j - 64 < 64
    · simp [hj2, show 64 ≤ j by omega, show ¬ 128 ≤ j by omega]
    · rw [if_neg hj2, Nat.testBit_lt_two_pow (show c1 < 2 ^ (j - 64) from
        lt_of_lt_of_le (show c1 < 2 ^ 64 from h1) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp [show 64 ≤ j by omega, show 128 ≤ j by omega, show j - 64 - 64 = j - 128 by omega]

/-! ## In the field -/

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {limbs : F ≃ QuotientRpm.Limbs}
variable (hF : IsF192 limbs)
include hF

theorem elem_injOn {c d : Nat} (hc : c < B192) (hd : d < B192) (h : elem limbs c = elem limbs d) :
    c = d := by
  have := congrArg (word limbs) h
  rwa [word_elem, word_elem, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at this

/-- **A nonzero element of one limb has order dividing `2^64 - 1`.** -/
theorem base_pow {c : Nat} (hc : c < B64) : elem limbs c ^ 2 ^ 64 = elem limbs c := by
  classical
  set S : Finset F := ((Finset.range B64).image (elem limbs)).erase 0 with hS
  have hB : B64 < B192 := by decide
  have hcard0 : ((Finset.range B64).image (elem limbs)).card = B64 := by
    rw [Finset.card_image_of_injOn (fun a ha b hb h => elem_injOn hF
      (lt_trans (Finset.mem_range.mp ha) hB) (lt_trans (Finset.mem_range.mp hb) hB) h)]
    simp
  have h0mem : (0 : F) ∈ (Finset.range B64).image (elem limbs) :=
    Finset.mem_image.mpr ⟨0, by simp, elem_zero hF⟩
  have hcard : S.card = 2 ^ 64 - 1 := by
    rw [hS, Finset.card_erase_of_mem h0mem, hcard0]; rfl
  have hclosed : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    obtain ⟨ha0, ha⟩ := Finset.mem_erase.mp ha
    obtain ⟨hb0, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_erase.mpr ⟨mul_ne_zero ha0 hb0, Finset.mem_image.mpr ⟨mulE x y, ?_, ?_⟩⟩
    · rw [mulE_small (Finset.mem_range.mp hx) (Finset.mem_range.mp hy), Finset.mem_range]
      exact reduce64_lt _
    · exact elem_mulE hF x y
  by_cases hz : elem limbs c = 0
  · rw [hz]; simp
  · have hs : elem limbs c ∈ S := Finset.mem_erase.mpr ⟨hz, Finset.mem_image.mpr ⟨c, by simpa, rfl⟩⟩
    have himage : S.image (elem limbs c * ·) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro u hu
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
        exact hclosed _ hs _ hv
      · rw [Finset.card_image_of_injective _ (mul_right_injective₀ hz)]
    have hprod : ∏ u ∈ S, (elem limbs c * u) = ∏ u ∈ S, u := by
      have := Finset.prod_image (s := S) (g := (elem limbs c * ·)) (f := fun v => v)
        (fun a _ b _ h => mul_right_injective₀ hz h)
      rw [himage] at this
      exact this.symm
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard] at hprod
    have hP : ∏ u ∈ S, u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun u hu => (Finset.mem_erase.mp hu).1
    have h1 : elem limbs c ^ (2 ^ 64 - 1) = 1 := by
      have := mul_right_cancel₀ hP (hprod.trans (one_mul _).symm)
      exact this
    calc elem limbs c ^ 2 ^ 64 = elem limbs c ^ (2 ^ 64 - 1) * elem limbs c := by
          rw [← pow_succ]; norm_num
      _ = elem limbs c := by rw [h1, one_mul]

/-- `x ↦ x^(2^n)` on numbers. -/
def sqIter : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => let y := sqIter n x; mulE y y

theorem elem_sqIter (n x : Nat) : elem limbs (sqIter n x) = elem limbs x ^ 2 ^ n := by
  induction n with
  | zero => simp [sqIter]
  | succ n ih => rw [sqIter, elem_mulE hF, ih, ← pow_add, pow_succ, mul_two]

omit hF in
theorem Y_facts : sqIter 64 B64 = mulE B64 B64 ∧ mulE B64 B64 = B64 * B64 ∧
    mulE (B64 * B64) (B64 * B64) = (B64 * B64) ^^^ B64 := by
  decide +kernel

/-- **The Frobenius is `x^(2^64)`.** -/
theorem frobOK : FrobOK limbs := by
  intro x
  obtain ⟨hY, hY2, hY4⟩ := Y_facts
  set Y := elem limbs B64
  have hY2' : elem limbs (B64 * B64) = Y ^ 2 := by rw [← hY2, elem_mulE hF, pow_two]
  have hpow : Y ^ 2 ^ 64 = Y ^ 2 := by rw [← elem_sqIter hF, hY, elem_mulE hF, pow_two]
  have hY4' : Y ^ 2 * Y ^ 2 = Y ^ 2 + Y := by
    rw [← hY2', ← elem_mulE hF, hY4, elem_xor hF]
  have dec : ∀ {c0 c1 c2 : Nat}, c0 < B64 → c1 < B64 → c2 < B64 →
      elem limbs (ofLimbs c0 c1 c2) = elem limbs c0 + elem limbs c1 * Y + elem limbs c2 * Y ^ 2 := by
    intro c0 c1 c2 h0 h1 h2
    rw [ofLimbs_xor h0 h1 h2, elem_xor hF, elem_xor hF, ← mulE_Y h1, ← mulE_Y2 h2, elem_mulE hF,
      elem_mulE hF, hY2']
  have l0 := limb_lt x 0
  have l1 := limb_lt x 1
  have l2 := limb_lt x 2
  have hx : elem limbs x = elem limbs (limb x 0) + elem limbs (limb x 1) * Y +
      elem limbs (limb x 2) * Y ^ 2 := by
    rw [← dec l0 l1 l2, ofLimbs_limb, elem_mod]
  rw [frobE, dec l0 l2 (Nat.xor_lt_two_pow (n := 64) l1 l2), elem_xor hF, hx]
  have hfrob : ∀ a b : F, (a + b) ^ 2 ^ 64 = a ^ 2 ^ 64 + b ^ 2 ^ 64 := fun a b =>
    add_pow_char_pow a b 2 64
  rw [hfrob, hfrob, mul_pow, mul_pow, base_pow hF l0, base_pow hF l1, base_pow hF l2, hpow,
    ← pow_mul, show 2 * 2 ^ 64 = 2 ^ 64 * 2 by ring, pow_mul, hpow, ← pow_mul,
    show 2 * 2 = 2 + 2 by rfl, pow_add, hY4']
  ring

end Implementation
