-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Copied from `formal/FlockSound` (branch `lean-uni-code`,
-- commit b3047c9, `FlockSoundUni/Transcription.lean`: the skip's nodes and weights; branch `lean-flock-sound`,
-- `FlockSound/Fields.lean`: `phi8_xor`, `phi8_ne_zero`, `phi8_injOn`, ported there from leanerVM `mumbai` f0393df4,
-- MIT OR Apache-2.0), unchanged but for the namespace and the linter options.
import UniComplete.FlockProverSum
import Mathlib.LinearAlgebra.Lagrange

/-!
# The univariate skip is complete: `SkipComplete k` for `k ≤ 6`

**`skipComplete`**: the verifier's start of the zerocheck, `lagrange_interpolate(2^(k+1), 0^(2^k) ++ coset, z)` of the
prover's coset values, is the skip polynomial's value `Σ_b eq(r, b) (Â B̂ + Ẑ)(z, b)` whenever `Az ∘ Bz + z` vanishes
everywhere. The skip polynomial `P(X) = Σ_b eq(r, b) (Â_b(X) B̂_b(X) + Ẑ_b(X))`, `Â_b(X) = Σ_x A(x + 2^k b) L_x(X)` over
the Lagrange basis of the nodes `φ(0..2^k)` (`hatT`), has degree `< 2^(k+1)`; it vanishes on `φ(0..2^k)` (the R1CS)
and is the coset values on `φ(2^k..2^(k+1))`, so the interpolation over the `2^(k+1)` distinct nodes is `P(z)`
(Mathlib's `Lagrange.eq_interpolate`).

Copied (cited above): `phi` is `F_2`-linear and injective below `128` (`phi_xor`, `phi_injOn`, through `φ_8`; one
kernel check over the 127 nonzero bytes, `phi8_ne_zero`, as in `formal/FlockSound`), every node's denominator is the
window's (`windowDenominator_eq`), and the code's `lagrangeWeights` are the Lagrange basis at the point
(`lagrangeWeights_getD`).
-/

namespace UniComplete.FlockP.Skip

open UniStatement LeanVM.Parameters Finset Polynomial

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

theorem sub_eq_add_E (a b : E) : a - b = a + b := CharTwo.sub_eq_add a b

theorem ofLane_zero : K.ofLane 0 = 0 := rfl

theorem ofLane_xor (a b : UInt64) : K.ofLane (a ^^^ b) = K.ofLane a + K.ofLane b := by
  simp only [K.ofLane, BF64.add_def, BF64.toBitVec_ofBitVec, UInt64.toBitVec_xor]

theorem eK_eq (c : UInt64) : eK c = ofK (K.ofLane c) := Tower.eK_eq c

/-! ## `φ_8` (Fields.lean) -/

/-- `φ_8` is additive in its byte: it sums the basis images of the set bits. -/
theorem phi8_xor (a b : ℕ) : Lv42.Parameters.Flock.phi8 (a ^^^ b) = Lv42.Parameters.Flock.phi8 a + Lv42.Parameters.Flock.phi8 b := by
  simp only [Lv42.Parameters.Flock.phi8, ← Finset.sum_add_distrib, Nat.testBit_xor]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases a.testBit i <;> cases b.testBit i <;> simp [← two_mul, CharTwo.two_eq_zero]

/-- The nonzero bytes below `128` have nonzero images: a kernel check. -/
theorem phi8_ne_zero : ∀ b : Fin 128, b ≠ 0 → Lv42.Parameters.Flock.phi8 b ≠ 0 := by decide +kernel

/-- `φ_8` is injective on the bytes below `128`. -/
theorem phi8_injOn {a b : ℕ} (ha : a < 128) (hb : b < 128) (h : Lv42.Parameters.Flock.phi8 a = Lv42.Parameters.Flock.phi8 b) :
    a = b := by
  have hx : a ^^^ b < 128 := Nat.xor_lt_two_pow (n := 7) ha hb
  by_contra hne
  have hz : Lv42.Parameters.Flock.phi8 (a ^^^ b) = 0 := by
    rw [phi8_xor, h, CharTwo.add_self_eq_zero]
  refine phi8_ne_zero ⟨a ^^^ b, hx⟩ (fun h0 ↦ hne ?_) hz
  have h0' : a ^^^ b = 0 := congrArg Fin.val h0
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  have := congrArg (·.testBit i) h0'
  simpa [Nat.testBit_xor] using this



/-! ## The skip's nodes and weights (Transcription.lean) -/

theorem tx_foldl_mul_range' (f : ℕ → E) : ∀ (m s : ℕ) (a : E),
    (List.range' s m).foldl (fun acc k ↦ acc * f k) a = a * ∏ k ∈ range m, f (s + k)
  | 0, s, a => by simp
  | m + 1, s, a => by
    rw [List.range'_succ, List.foldl_cons, tx_foldl_mul_range' f m (s + 1), Finset.prod_range_succ']
    simp only [add_zero]
    rw [Finset.prod_congr rfl fun k _ ↦ show f (s + 1 + k) = f (s + (k + 1)) by congr 1; omega]
    ring

theorem tx_ofLane_phiFold (v : ℕ) : ∀ n : ℕ,
    K.ofLane ((List.range n).foldl (fun acc bit ↦
      if v.testBit bit then acc ^^^ UniStatement.Flock.phiBasis.getD bit 0 else acc) 0) =
      ∑ b ∈ range n, if v.testBit b then K.ofLane (UniStatement.Flock.phiBasis.getD b 0) else 0
  | 0 => by simp [ofLane_zero]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ,
      ← tx_ofLane_phiFold v n]
    split_ifs <;> simp [ofLane_xor]

/-- **`phi` is `φ_8`**: the code's `UInt64` xor of the basis words is the sum in `K`. -/
theorem phi_eq (v : ℕ) : UniStatement.Flock.phi v = ofK (Lv42.Parameters.Flock.phi8 v) := by
  rw [UniStatement.Flock.phi, eK_eq, tx_ofLane_phiFold, Lv42.Parameters.Flock.phi8, ← Fin.sum_univ_eq_sum_range]
  refine congrArg ofK (Finset.sum_congr rfl fun i _ ↦ ?_)
  by_cases h : v.testBit i
  · simp only [h, ↓reduceIte]
    fin_cases i <;> rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem tx_ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-- **`phi` is `F_2`-linear.** -/
theorem phi_xor (a b : ℕ) : UniStatement.Flock.phi (a ^^^ b) = UniStatement.Flock.phi a + UniStatement.Flock.phi b := by
  rw [phi_eq, phi_eq, phi_eq, phi8_xor, tx_ofK_add]

/-- **The nodes `φ(0), …, φ(2^n − 1)` are an `F_2`-subspace**: the sum of two is the node of the xor
of their indices, again below `2^n`. -/
theorem phi_add_mem {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a ^^^ b < 2 ^ n ∧ UniStatement.Flock.phi a + UniStatement.Flock.phi b = UniStatement.Flock.phi (a ^^^ b) :=
  ⟨Nat.xor_lt_two_pow ha hb, (phi_xor a b).symm⟩

/-- The nodes below `128` are distinct (`phi8_injOn`). -/
theorem phi_injOn {a b : ℕ} (ha : a < 128) (hb : b < 128) (h : UniStatement.Flock.phi a = UniStatement.Flock.phi b) : a = b := by
  rw [phi_eq, phi_eq] at h
  exact phi8_injOn ha hb (ofK_injective h)

theorem tx_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have h' : a ^^^ (a ^^^ b) = a ^^^ 0 := by rw [h]
  rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero, eq_comm] at h'

/-- Every node's denominator `Π_{j ≠ i} (φ_i − φ_j)` is the window's `Π_{t ≠ 0} φ_t`: `j ↦ i xor j`. -/
theorem tx_prod_window {n i : ℕ} (hi : i < 2 ^ n) :
    ∏ j ∈ (range (2 ^ n)).erase i, (UniStatement.Flock.phi i - UniStatement.Flock.phi j) =
      ∏ t ∈ range (2 ^ n - 1), UniStatement.Flock.phi (1 + t) := by
  have hne : ∀ j, j ≠ i → i ^^^ j ≠ 0 := fun j hj h ↦ hj (tx_xor_eq_zero h).symm
  refine Finset.prod_nbij' (fun j ↦ (i ^^^ j) - 1) (fun t ↦ i ^^^ (t + 1)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj ⊢
    have h1 := Nat.xor_lt_two_pow hi hj.2
    have h2 := hne j hj.1
    omega
  · intro t ht
    simp only [Finset.mem_erase, Finset.mem_range] at ht ⊢
    refine ⟨fun h ↦ ?_, Nat.xor_lt_two_pow hi (by omega)⟩
    have h' : i ^^^ (i ^^^ (t + 1)) = i ^^^ i := by rw [h]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h'
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have h2 := hne j hj.1
    show i ^^^ ((i ^^^ j) - 1 + 1) = j
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h2), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro t _
    show (i ^^^ (i ^^^ (t + 1))) - 1 = t
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.add_sub_cancel]
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have h2 := hne j hj.1
    rw [sub_eq_add_E, ← phi_xor, Nat.add_sub_cancel' (Nat.one_le_iff_ne_zero.mpr h2)]

/-- **The window denominator** is every node's denominator. -/
theorem windowDenominator_eq {n i : ℕ} (hi : i < 2 ^ n) :
    UniStatement.Flock.windowDenominator (2 ^ n) =
      (∏ j ∈ (range (2 ^ n)).erase i, (UniStatement.Flock.phi i - UniStatement.Flock.phi j))⁻¹ := by
  rw [tx_prod_window hi, UniStatement.Flock.windowDenominator, tx_foldl_mul_range', one_mul]

/-- Prefix products pushed one by one. -/
theorem tx_foldl_push (d : ℕ → E) : ∀ n : ℕ,
    (List.range n).foldl (fun acc i ↦ acc.push (acc.back?.getD 1 * d i)) #[1] =
      ((List.range (n + 1)).map fun t ↦ ∏ j ∈ range t, d j).toArray
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, tx_foldl_push d n, List.foldl_cons, List.foldl_nil,
      @List.range_succ (n + 1), List.map_append]
    simp [Finset.prod_range_succ, List.getLast?_range]

theorem lagrangeWeights_length (count : ℕ) (pt : E) :
    (UniStatement.Flock.lagrangeWeights count pt).length = count := by
  simp [UniStatement.Flock.lagrangeWeights]

theorem tx_lagrangeWeights_getD {count i : ℕ} (hi : i < count) (pt : E) :
    (UniStatement.Flock.lagrangeWeights count pt).getD i 0 =
      (∏ j ∈ range i, (pt + UniStatement.Flock.phi j)) *
        (∏ j ∈ range (count - 1 - i), (pt + UniStatement.Flock.phi (count - 1 - j))) * UniStatement.Flock.windowDenominator count := by
  simp only [UniStatement.Flock.lagrangeWeights]
  simp only [tx_foldl_push]
  simp [List.getD_eq_getElem?_getD, hi, Array.getD_eq_getD_getElem?]
  left
  rw [List.getElem?_range (by omega), Option.map_some, Option.getD_some]
  congr 1
  · refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    simp [Array.getElem?_ofFn, show x < count by omega]
  · rw [show count - (i + 1) = count - 1 - i by omega]
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    simp [Array.getElem?_ofFn, show count - 1 - x < count by omega]

/-- `Π_{j ∈ [0, N) \ {i}} f j` as the prefix before `i` and the suffix after. -/
theorem tx_prod_erase (f : ℕ → E) {N i : ℕ} (hi : i < N) :
    ∏ j ∈ (range N).erase i, f j = (∏ j ∈ range i, f j) * ∏ j ∈ range (N - 1 - i), f (i + 1 + j) := by
  have hmem : i ∈ range N := Finset.mem_range.mpr hi
  have h1 := Finset.mul_prod_erase (range N) (fun j ↦ if j = i then 1 else f j) hmem
  simp only [if_true, one_mul] at h1
  rw [Finset.prod_congr rfl fun j hj ↦ show f j = (if j = i then 1 else f j) by
    rw [if_neg (Finset.ne_of_mem_erase hj)], h1]
  rw [show N = i + 1 + (N - 1 - i) by omega, Finset.prod_range_add, Finset.prod_range_succ, if_pos rfl,
    mul_one, show i + 1 + (N - 1 - i) - 1 - i = N - 1 - i by omega]
  congr 1
  · exact Finset.prod_congr rfl fun j hj ↦ by rw [if_neg (by rw [Finset.mem_range] at hj; omega)]
  · exact Finset.prod_congr rfl fun j _ ↦ by rw [if_neg (by omega)]

/-- **The code's weight at node `i`** is the Lagrange basis polynomial's value:
`Π_{j ≠ i} (z − φ_j) / (φ_i − φ_j)` over the nodes `φ(0), …, φ(2^n − 1)`. -/
theorem lagrangeWeights_getD {n i : ℕ} (hi : i < 2 ^ n) (z : E) :
    (UniStatement.Flock.lagrangeWeights (2 ^ n) z).getD i 0 =
      ∏ j ∈ (range (2 ^ n)).erase i, (UniStatement.Flock.phi i - UniStatement.Flock.phi j)⁻¹ * (z - UniStatement.Flock.phi j) := by
  rw [tx_lagrangeWeights_getD hi, windowDenominator_eq hi, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, tx_prod_erase (fun j ↦ z - UniStatement.Flock.phi j) hi]
  have hB : ∏ j ∈ range (2 ^ n - 1 - i), (z + UniStatement.Flock.phi (2 ^ n - 1 - j)) =
      ∏ j ∈ range (2 ^ n - 1 - i), (z - UniStatement.Flock.phi (i + 1 + j)) := by
    rw [← Finset.prod_range_reflect (fun j ↦ z - UniStatement.Flock.phi (i + 1 + j))]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [sub_eq_add_E]
    congr 2
    omega
  rw [hB]
  simp only [sub_eq_add_E]
  ring


/-! ## The skip polynomial -/

open UniStatement.Flock (phi lagrangeWeights lagrangeInterpolate)

theorem phi_injOn_range {m : ℕ} (hm : m ≤ 7) : Set.InjOn phi (range (2 ^ m) : Set ℕ) := by
  intro a ha b hb h
  have h128 : 2 ^ m ≤ 128 := (Nat.pow_le_pow_right (by norm_num) hm).trans (by norm_num)
  exact phi_injOn (lt_of_lt_of_le (mem_range.mp ha) h128) (lt_of_lt_of_le (mem_range.mp hb) h128) h

/-- **The code's weights are Mathlib's Lagrange basis** over the nodes `φ(0..2^n)`. -/
theorem basis_eval {n i : ℕ} (hi : i < 2 ^ n) (z : E) :
    (Lagrange.basis (range (2 ^ n)) phi i).eval z = (lagrangeWeights (2 ^ n) z).getD i 0 := by
  rw [lagrangeWeights_getD hi, Lagrange.basis, Polynomial.eval_prod]
  refine prod_congr rfl fun j _ ↦ ?_
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]

/-- `Â_b(X) = Σ_x T(x + 2^k b) L_x(X)`: the table's univariate extension over the skip's nodes. -/
noncomputable def hatT (k : ℕ) (T : Array E) (b : ℕ) : E[X] :=
  ∑ x ∈ range (2 ^ k), C (T.getD (x + 2 ^ k * b) 0) * Lagrange.basis (range (2 ^ k)) phi x

theorem hatT_eval (k : ℕ) (T : Array E) (b : ℕ) (y : E) :
    (hatT k T b).eval y = ∑ x ∈ range (2 ^ k), (lagrangeWeights (2 ^ k) y).getD x 0 * T.getD (x + 2 ^ k * b) 0 := by
  rw [hatT, Polynomial.eval_finsetSum]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, basis_eval (mem_range.mp hx), mul_comm]

theorem hatT_node (k : ℕ) (hk : k ≤ 6) (T : Array E) (b : ℕ) {i : ℕ} (hi : i < 2 ^ k) :
    (hatT k T b).eval (phi i) = T.getD (i + 2 ^ k * b) 0 := by
  rw [hatT, Polynomial.eval_finsetSum, sum_eq_single i]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.eval_basis_self (phi_injOn_range (by omega)) (mem_range.mpr hi), mul_one]
  · intro x _ hx
    rw [Polynomial.eval_mul, Lagrange.eval_basis_of_ne hx (mem_range.mpr hi), mul_zero]
  · intro h; exact absurd (mem_range.mpr hi) h

theorem hatT_natDegree (k : ℕ) (hk : k ≤ 6) (T : Array E) (b : ℕ) : (hatT k T b).natDegree ≤ 2 ^ k - 1 := by
  rw [hatT]
  refine natDegree_sum_le_of_forall_le _ _ fun x hx ↦ ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [Lagrange.natDegree_basis (phi_injOn_range (by omega)) hx, card_range]

/-- **The skip polynomial** `P(X) = Σ_b eq(r, b) (Â_b B̂_b + Ẑ_b)(X)`. -/
noncomputable def skipPoly (k : ℕ) (r : List E) (wit : Wit) : E[X] :=
  ∑ b ∈ range (2 ^ r.length), C (eqB r b) * (hatT k wit.a b * hatT k wit.b b + hatT k wit.c b)

theorem skipPoly_eval (k : ℕ) (r : List E) (wit : Wit) (y : E) :
    (skipPoly k r wit).eval y = ∑ b ∈ range (2 ^ r.length), eqB r b *
      ((hatT k wit.a b).eval y * (hatT k wit.b b).eval y + (hatT k wit.c b).eval y) := by
  rw [skipPoly, Polynomial.eval_finsetSum]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_mul]

theorem skipPoly_degree (k : ℕ) (hk : k ≤ 6) (r : List E) (wit : Wit) :
    (skipPoly k r wit).degree < (range (2 ^ (k + 1))).card := by
  rw [card_range]
  refine lt_of_le_of_lt (degree_le_natDegree) ?_
  have hle : (skipPoly k r wit).natDegree ≤ 2 * (2 ^ k - 1) := by
    rw [skipPoly]
    refine natDegree_sum_le_of_forall_le _ _ fun b _ ↦ ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_mul_le).trans ?_
      have h1 := hatT_natDegree k hk wit.a b
      have h2 := hatT_natDegree k hk wit.b b
      omega
    · have := hatT_natDegree k hk wit.c b
      omega
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact_mod_cast (show (skipPoly k r wit).natDegree < 2 ^ (k + 1) by rw [pow_succ]; omega)

/-- **The univariate skip is complete** at `k ≤ 6` skip variables. -/
theorem skipComplete (k : ℕ) (hk : k ≤ 6) : SkipComplete k := by
  intro r wit z ha hb hc hR
  have hsz : ∀ (T : Array E), T.size = 2 ^ (k + r.length) → T.size / 2 ^ k = 2 ^ r.length := fun T h ↦ by
    rw [h, pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)]
  have hidx : ∀ i < 2 ^ k, ∀ b < 2 ^ r.length, i + 2 ^ k * b < 2 ^ (k + r.length) := fun i hi b hb ↦ by
    rw [pow_add]
    calc i + 2 ^ k * b < 2 ^ k + 2 ^ k * b := by omega
      _ = 2 ^ k * (b + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ r.length := Nat.mul_le_mul_left _ hb
  -- P at any point: the tables at the skip's point.
  have hPeval : ∀ y, (skipPoly k r wit).eval y = ∑ b ∈ range (2 ^ r.length), eqB r b *
      ((skipFold k (lagrangeWeights (2 ^ k) y) wit.a).getD b 0 * (skipFold k (lagrangeWeights (2 ^ k) y) wit.b).getD b 0 +
        (skipFold k (lagrangeWeights (2 ^ k) y) wit.c).getD b 0) := by
    intro y
    rw [skipPoly_eval]
    refine sum_congr rfl fun b hbm ↦ ?_
    have hb' := mem_range.mp hbm
    rw [hatT_eval, hatT_eval, hatT_eval, skipFold_getD k _ wit.a (by rw [hsz _ ha]; exact hb'),
      skipFold_getD k _ wit.b (by rw [hsz _ hb]; exact hb'), skipFold_getD k _ wit.c (by rw [hsz _ hc]; exact hb')]
  -- P vanishes on the skip's domain.
  have hzero : ∀ i < 2 ^ k, (skipPoly k r wit).eval (phi i) = 0 := by
    intro i hi
    rw [skipPoly_eval]
    refine sum_eq_zero fun b hbm ↦ ?_
    rw [hatT_node k hk wit.a b hi, hatT_node k hk wit.b b hi, hatT_node k hk wit.c b hi,
      hR _ (hidx i hi b (mem_range.mp hbm)), mul_zero]
  -- P is the coset values on the coset.
  have hcoset : ∀ i < 2 ^ k, (cosetValues k r wit).getD i 0 = (skipPoly k r wit).eval (phi (2 ^ k + i)) := by
    intro i hi
    rw [hPeval, cosetValues, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    simp only
    rw [sumTo_eq, eqKernel_size]
    exact sum_congr rfl fun b hbm ↦ by rw [eqKernel_getD _ (mem_range.mp hbm)]
  -- The interpolation over the `2^(k+1)` nodes.
  have hinterp := Lagrange.eq_interpolate (phi_injOn_range (m := k + 1) (by omega)) (skipPoly_degree k hk r wit)
  have hcosetlen : (cosetValues k r wit).length = 2 ^ k := by simp [cosetValues]
  have hdl : (lagrangeWeights (2 ^ (k + 1)) z).length = (List.replicate (2 ^ k) (0 : E) ++ cosetValues k r wit).length := by
    rw [lagrangeWeights_length, List.length_append, List.length_replicate, hcosetlen, pow_succ]
    ring
  rw [lagrangeInterpolate, dot_eq _ _ hdl, lagrangeWeights_length, ← hPeval z]
  conv_rhs => rw [hinterp, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  have hL : (List.replicate (2 ^ k) (0 : E) ++ cosetValues k r wit).getD i 0 = (skipPoly k r wit).eval (phi i) := by
    by_cases h : i < 2 ^ k
    · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp only [h, ite_true, Option.getD_some]
      exact (hzero i h).symm
    · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_replicate,
        hcoset (i - 2 ^ k) (by rw [pow_succ] at hi'; omega), show 2 ^ k + (i - 2 ^ k) = i by omega]
  rw [hL, Polynomial.eval_mul, Polynomial.eval_C, basis_eval hi']
  ring

end UniComplete.FlockP.Skip
