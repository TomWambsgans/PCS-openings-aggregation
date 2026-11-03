-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The bound's form is `formal/UniSound/UniSound/Fs128.lean`'s
-- `uniBound128` (the openings once, the chain without the tag, the seed's pair, the permutation), its proof in bits
-- that file's `uniBound128_le_bits`.
import RecCompose.Basic
import RecPiop.Numbers
import WhirBridge.Sound

/-!
# π2's bound, `ε2`, in bits

**`pi2Bound Q`**, for an adversary of `Q` calls of `π` and `π⁻¹` (`N = pi2N Q = 2^33 + Q` bounds every count: the
setup's Keccak-256 calls, π1's three trees and π2's of `2^25` words, below `2^27`, twice; the chain's; the three
openings'):

```
N (ε + 5 N / 2^256) + N (e2 + 8 N / 2^256) + 2 N² / 2^256 + (2^81 + Q)² / 2^508,
ε = 269 · 2^-137 = 2^-128.93,   e2 = 9952 · 3564 · (5 · 2^24 − 1) / 2^192 = 2^-140.60
```

* **the openings, once for all three** (`Compose.prEvent_doomF_le`, `WhirBridge.largeShapes`: `W` of `2^24` words, the
  setup `2^25`, `Q` `2^28`), at the exact certified per-group bound `ε` (`WhirBridge.εExact`);
* **the chain** (`Compose.knowledgeSoundness_listChainU_closed128`): the rounds' largest error times its lists
  (`Compose.maxErrK`), `e2`, the identity at `t` over `L_W L_Q` (`RecPiop.bits_t`; the copy argument's `L_W`-term is
  `2^-153.13`, `ρ`'s `2^-163.01`: `pi2_rounds_le`), and the collisions;
* **the seed's pair** (`Compose.prEvent_pairTr_le`: π2's seed `name ‖ iv ‖ input`, its IV an answer);
* the random permutation, as `uniBound128`'s.

At `Q = 2^64` it is `2^-64.93` (`EndToEnd/Review/RecSoundnessNumbers.py`, exact rationals: the openings `2^-64.93`,
the chain's rounds `2^-76.60`, the collisions `2^-125`, the pair `2^-127`): **`pi2Bound_le_bits`**, at most `2^-64` for
`Q ≤ 2^64`, i.e. at least 128 bits as `Q / ε2`.
-/

namespace RecCompose

open LeanVM.Parameters LeanVM.Protocol Finset
open scoped ENNReal

/-- `N`: every count of the bound at `Q` adversary calls. -/
def pi2N (Q : ℕ) : ℕ := 2 ^ 33 + Q

/-- **π2's rounds' largest error times its lists**: the identity at `t`, `L_W L_Q (5 N − 1)/|E|` at `N = 2^24`. -/
noncomputable def pi2RoundErr : ℝ≥0∞ :=
  ((9952 * 3564 * (5 * 2 ^ 24 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

/-- **π2's bound** `ε2` at `Q` adversary calls. -/
noncomputable def pi2Bound (Q : ℕ) : ℝ≥0∞ :=
  (pi2N Q : ℝ≥0∞) * (269 * (2 : ℝ≥0∞)⁻¹ ^ 137 + ((5 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (pi2N Q : ℝ≥0∞) * (pi2RoundErr + ((8 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((2 * pi2N Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

/-! ## π2's rounds, times their lists -/

theorem card_E_eq : Fintype.card E = 2 ^ 192 := LeanVM.Protocol.card_E

/-- **Each of π2's rounds' errors, times the lists of the roots before it, is at most `pi2RoundErr`** (`RecPiop.err` at
`N = 2^24`, rows of `16`, the ports' `d_j` summing to `3`): the copy argument over `L_W`, the identity at `t` and `W`'s
fold at `ρ` over `L_W L_Q`. -/
theorem pi2_rounds_le (G : RecPiop.Circuit E) (hN : G.logN = 24) (hW : G.logW = 4) (d : ℕ → ℕ)
    (hd : ∑ j ∈ range G.nP, d j = 3) :
    ((9952 : ℕ) : ℝ≥0∞) * RecPiop.err G d 0 ≤ pi2RoundErr ∧
      ((9952 * 3564 : ℕ) : ℝ≥0∞) * RecPiop.err G d 1 ≤ pi2RoundErr ∧
      ((9952 * 3564 : ℕ) : ℝ≥0∞) * RecPiop.err G d 2 ≤ pi2RoundErr := by
  have hE : (Fintype.card E : ℝ≥0∞) ≠ 0 := by rw [card_E_eq]; positivity
  have hEt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have key : ∀ a b : ℕ, a * b ≤ 9952 * 3564 * (5 * 2 ^ 24 - 1) →
      (a : ℝ≥0∞) * ((b : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) ≤ pi2RoundErr := by
    intro a b hab
    unfold pi2RoundErr
    rw [← mul_div_assoc, ← Nat.cast_mul]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr hab) _
  have hNv : G.N = 2 ^ 24 := RecPiop.N_of_logN hN
  refine ⟨?_, ?_, ?_⟩
  · unfold RecPiop.err
    rw [ite_eq_left rfl, hNv, hd]
    exact key _ _ (by norm_num)
  · unfold RecPiop.err
    rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_eq_left rfl, hNv]
    exact key _ _ le_rfl
  · unfold RecPiop.err
    rw [ite_eq_right (by decide : (2 : ℕ) ≠ 0), ite_eq_right (by decide : (2 : ℕ) ≠ 1), hW]
    exact key _ _ (by norm_num)

/-! ## The bound in bits -/

section Bits

theorem d256 (a b : ℕ) :
    (a : ℝ≥0∞) * ((b : ℝ≥0∞) / 2 ^ 256) = ((a * b : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [← mul_div_assoc, Nat.cast_mul]

theorem a256 (a b : ℕ) :
    (a : ℝ≥0∞) / 2 ^ 256 + (b : ℝ≥0∞) / 2 ^ 256 = ((a + b : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [ENNReal.div_add_div_same, Nat.cast_add]

theorem le256 {a b : ℕ} (h : a ≤ b) : (a : ℝ≥0∞) / 2 ^ 256 ≤ (b : ℝ≥0∞) / 2 ^ 256 :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

/-- `269 · 2^-137` over `2^256`. -/
theorem eps128_eq : (269 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 137 = ((269 * 2 ^ 119 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_div_assoc, show (256 : ℕ) = 119 + 137 from rfl, WhirBridge.two_pow_div_two_pow]

/-- `pi2RoundErr` over `2^256`. -/
theorem pi2RoundErr_eq : pi2RoundErr = ((9952 * 3564 * (5 * 2 ^ 24 - 1) * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold pi2RoundErr
  rw [card_E_eq]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (256 : ℕ) = 192 + 64 from rfl, pow_add,
    ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

/-- **π2's bound in bits**: at most `2^-64` for an adversary of at most `2^64` calls of `π` and `π⁻¹` (`2^-64.93` at
`2^64`), i.e. at least `128` bits as `Q / ε2`. -/
theorem pi2Bound_le_bits (Q : ℕ) (hQ : Q ≤ 2 ^ 64) : pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  unfold pi2Bound
  rw [pi2RoundErr_eq, eps128_eq]
  have hN : pi2N Q ≤ 18446744082299486208 := by
    unfold pi2N
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    have : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
    omega
  set X : ℕ := 18446744082299486208 with hX
  have b1 : (pi2N Q : ℝ≥0∞) * (((269 * 2 ^ 119 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
      ((5 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤ ((X * (269 * 2 ^ 119 + 5 * X) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [a256, d256]
    exact le256 (Nat.mul_le_mul hN (by omega))
  have b2 : (pi2N Q : ℝ≥0∞) * (((9952 * 3564 * (5 * 2 ^ 24 - 1) * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
      ((8 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤
      ((X * (9952 * 3564 * (5 * 2 ^ 24 - 1) * 2 ^ 64 + 8 * X) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [a256, d256]
    exact le256 (Nat.mul_le_mul hN (by omega))
  have b3 : ((2 * pi2N Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 * X ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
    le256 (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hN 2))
  have b4 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have hq : (2 ^ 81 + Q) ^ 2 ≤ 2 ^ 164 := by
      have h82 : 2 ^ 81 + Q ≤ 2 ^ 82 := by
        have : (2 : ℕ) ^ 82 = 2 ^ 81 + 2 ^ 81 := by norm_num
        have h64 : (2 : ℕ) ^ 64 ≤ 2 ^ 81 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      calc (2 ^ 81 + Q) ^ 2 ≤ (2 ^ 82) ^ 2 := Nat.pow_le_pow_left h82 2
        _ = 2 ^ 164 := by norm_num
    rw [← Nat.cast_pow]
    calc (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 508 ≤ ((2 ^ 164 : ℕ) : ℝ≥0∞) / 2 ^ 508 :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr hq) _
      _ = (2 : ℝ≥0∞)⁻¹ ^ 344 := by
          rw [Nat.cast_pow, Nat.cast_ofNat, show (508 : ℕ) = 164 + 344 from rfl, WhirBridge.two_pow_div_two_pow]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 :=
          pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) (by norm_num)
      _ = ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [Nat.cast_one, one_div, ENNReal.inv_pow]
  refine (add_le_add (add_le_add (add_le_add b1 b2) b3) b4).trans ?_
  rw [a256, a256, a256]
  calc _ ≤ ((2 ^ 192 : ℕ) : ℝ≥0∞) / 2 ^ 256 := le256 (by rw [hX]; norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 64 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 192 + 64 from rfl, WhirBridge.two_pow_div_two_pow]

end Bits

end RecCompose

/-- info: 'RecCompose.pi2Bound_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Bound_le_bits

/-- info: 'RecCompose.pi2_rounds_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2_rounds_le
