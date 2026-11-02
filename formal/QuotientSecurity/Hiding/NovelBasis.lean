-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Interp

/-!
# Condition (Q) for WHIR's novel basis, as deployed

leanVM's WHIR commits each lane of `2^ℓ` words with the additive NTT in the Lin–Chung–Han novel
polynomial basis (`crates/pcs/src/ntt/additive_ntt_f64.rs`, `AdditiveNttF64::standard(ℓ + 1)`), at
rate `1/2`: row `q` of the level-0 codeword (`q < 2^(ℓ+1)`) holds each lane's `Σ_y T(y)·X_y(K(q))`,
`K(q)` the element of `K = GF(2^64)` whose 64 bits are those of `q`. The verifier states the same code
(`crates/verifier/src/whir.rs`): `subspace_roots` computes `W_k(v_k)` for the subspace polynomials

  `W_0 = X`,  `W_{k+1} = W_k^2 + W_k(v_k)·W_k`,  `v_k = K(2^k)` (the basis `1, x, x², …`),

and `induced_weight` weighs a query `q` by `Π_k (1 + p_k (1 + Ŵ_k(K(q))))`, `Ŵ_k = W_k / W_k(v_k)`:
the multilinear extension in `y` of `X_y = Π_{k : bit k of y} Ŵ_k` (`novel_mle`). This file
transcribes that code (`subW`, `subRoot`, `novel`) and proves what condition (Q) needs of it:

* `Words`: the field's representation, `K(a ⊕ b) = K(a) + K(b)` and distinct 64-bit words
  distinct elements (the binary field's addition is XOR of the words);
* `subW_monic`: `W_k` is monic of degree `2^k`; `subW_eval_add` (characteristic 2): it is additive;
  `subW_eval_word`: it vanishes at `K(q)`, `q < 2^k`; `subRoot_ne_zero`: so `W_k(v_k) ≠ 0` (else
  `W_k` would have `2^(k+1)` roots);
* `novel_natDegree`: **`X_y` has degree `y`**, the hypothesis of `Interp.lean`'s
  `firstEval_surjective_of_degrees`;
* `novel_firstEval_surjective`: **condition (Q)** for the deployed encoding (`novelEnc`) with the
  first piece's entries below the gadget, `first = [0, D)`, `D = 2^LOG_PIECE − GADGET = 247`, at any
  `|Q| ≤ D` distinct positions; `novel_unopened`: with `|Q| < D`, the vector behind an unopened row;
* `whirQueries0`: level 0 of `WHIR_QUERIES` at rate `1/2` (`whir.rs:20-25`; mumbai's `queryTable`,
  checked equal in `formal/WhirBridge`), at most `225`; `deployed_queries`: `223`/`224` for the
  witness table (`log_n = log_rows + 3`), `224`/`225` for the quotient table (`log_n = log_rows + 6`),
  at every supported `17 ≤ log_rows ≤ 22`; `deployed_Q`: (Q) at the positions a level-0 opening
  samples (`sample_queries`, `config.queries[0]` of them, repeats allowed). No deeper level opens a row
  of the first commitment: level `i ≥ 1` opens its own (`transcript.merkle(current_root, …)` after
  `current_root = next_root`), and the first commitment takes no out-of-domain sample.
-/

namespace QuotientSecurity.Hiding

open Finset Polynomial

set_option linter.unusedSectionVars false

/-! ### The field's words -/

/-- `K = GF(2^64)` as `whir.rs` represents it: `K(q)` (`word q`), the element whose 64 bits are
those of `q` (`K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, bit `i` the coefficient of `x^i`).
Addition is the words' XOR, and distinct 64-bit words are distinct elements. -/
structure Words (K : Type) [Field K] where
  word : ℕ → K
  word_xor : ∀ a b, word (a ^^^ b) = word a + word b
  word_inj : ∀ a b, a < 2 ^ 64 → b < 2 ^ 64 → word a = word b → a = b

theorem two_pow_add_eq_xor {k q : ℕ} (hq : q < 2 ^ k) : 2 ^ k + q = 2 ^ k ^^^ q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy i k with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]
    simp [h.ne']
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hq]
    simp
  · have hk : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 2 ^ k + q < 2 ^ i := by rw [pow_succ] at hk; omega
    have h2 : q < 2 ^ i := by rw [pow_succ] at hk; omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [h.ne]

variable {K : Type} [Field K]

namespace Words

variable (w : Words K)

/-- The subspaces' basis `v_k = K(2^k)` (`subspace_roots`'s `K(1 << i)`; the NTT's `x^k`). -/
def v (k : ℕ) : K := w.word (2 ^ k)

theorem word_zero : w.word 0 = 0 := by
  have h := w.word_xor 0 0
  simpa using h

theorem word_two_pow_add {k q : ℕ} (hq : q < 2 ^ k) : w.word (2 ^ k + q) = w.v k + w.word q := by
  rw [two_pow_add_eq_xor hq, w.word_xor]
  rfl

end Words

/-! ### The subspace polynomials and the novel basis (`whir.rs`, `subspace_roots`, `induced_weight`) -/

/-- The subspace polynomials as `subspace_roots` and `induced_weight` compute them:
`W_0 = X`, `W_{k+1} = W_k^2 + W_k(v_k)·W_k` (`basis.square() + roots[k] * basis`). -/
noncomputable def subW (v : ℕ → K) : ℕ → K[X]
  | 0 => X
  | k + 1 => subW v k ^ 2 + C ((subW v k).eval (v k)) * subW v k

/-- `roots[k] = W_k(v_k)`, the normalizer of `W_k` (`subspace_roots`). -/
noncomputable def subRoot (v : ℕ → K) (k : ℕ) : K := (subW v k).eval (v k)

theorem subW_zero (v : ℕ → K) : subW v 0 = X := rfl

theorem subW_succ (v : ℕ → K) (k : ℕ) :
    subW v (k + 1) = subW v k ^ 2 + C (subRoot v k) * subW v k := rfl

/-- The verifier's recurrence on values (`basis = basis.square() + roots[k] * basis`). -/
theorem subW_succ_eval (v : ℕ → K) (k : ℕ) (x : K) :
    (subW v (k + 1)).eval x = (subW v k).eval x ^ 2 + subRoot v k * (subW v k).eval x := by
  simp [subW_succ]

/-- `W_k` is monic of degree `2^k`. -/
theorem subW_monic (v : ℕ → K) : ∀ k, (subW v k).Monic ∧ (subW v k).natDegree = 2 ^ k
  | 0 => ⟨monic_X, by simp [subW_zero]⟩
  | k + 1 => by
    obtain ⟨hm, hd⟩ := subW_monic v k
    have hsq : (subW v k ^ 2).Monic := hm.pow 2
    have hsqd : (subW v k ^ 2).natDegree = 2 ^ (k + 1) := by
      rw [hm.natDegree_pow, hd, pow_succ, mul_comm]
    have hlt : (C (subRoot v k) * subW v k).degree < (subW v k ^ 2).degree := by
      refine degree_lt_degree (lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_)
      rw [hd, hsqd]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [subW_succ]
    exact ⟨hsq.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hsqd]⟩

theorem subW_ne_zero (v : ℕ → K) (k : ℕ) : subW v k ≠ 0 := (subW_monic v k).1.ne_zero

variable [CharP K 2]

/-- In characteristic 2, `W_k` is additive. -/
theorem subW_eval_add (v : ℕ → K) : ∀ k (a b : K),
    (subW v k).eval (a + b) = (subW v k).eval a + (subW v k).eval b
  | 0, a, b => by simp [subW_zero]
  | k + 1, a, b => by
    rw [subW_succ_eval, subW_succ_eval, subW_succ_eval, subW_eval_add v k a b, CharTwo.add_sq]
    ring

/-- `W_k` vanishes on the subspace `{K(q) : q < 2^k}`. -/
theorem subW_eval_word (w : Words K) : ∀ k q, q < 2 ^ k → (subW w.v k).eval (w.word q) = 0
  | 0, q, hq => by
    have : q = 0 := by simpa using hq
    subst this
    simp [subW_zero, w.word_zero]
  | k + 1, q, hq => by
    rw [subW_succ_eval]
    by_cases h : q < 2 ^ k
    · rw [subW_eval_word w k q h]
      ring
    · obtain ⟨q', rfl⟩ : ∃ q', q = 2 ^ k + q' := ⟨q - 2 ^ k, by omega⟩
      have hq' : q' < 2 ^ k := by rw [pow_succ] at hq; omega
      rw [w.word_two_pow_add hq', subW_eval_add, subW_eval_word w k q' hq', add_zero]
      change subRoot w.v k ^ 2 + subRoot w.v k * subRoot w.v k = 0
      rw [sq]
      exact CharTwo.add_self_eq_zero _

/-- **The normalizers are nonzero**: `W_k(v_k) = 0` would make `W_k`, of degree `2^k`, vanish on the
`2^(k+1)` distinct points `K(q)`, `q < 2^(k+1)`. -/
theorem subRoot_ne_zero (w : Words K) {k : ℕ} (hk : k < 64) : subRoot w.v k ≠ 0 := by
  classical
  intro h0
  have hvan : ∀ q < 2 ^ (k + 1), (subW w.v k).eval (w.word q) = 0 := by
    intro q hq
    by_cases h : q < 2 ^ k
    · exact subW_eval_word w k q h
    · obtain ⟨q', rfl⟩ : ∃ q', q = 2 ^ k + q' := ⟨q - 2 ^ k, by omega⟩
      have hq' : q' < 2 ^ k := by rw [pow_succ] at hq; omega
      rw [w.word_two_pow_add hq', subW_eval_add, subW_eval_word w k q' hq', add_zero]
      exact h0
  have h64 : 2 ^ (k + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  set Z := (range (2 ^ (k + 1))).image w.word
  have hZ : Z.card = 2 ^ (k + 1) := by
    rw [card_image_of_injOn, card_range]
    intro a ha b hb hab
    exact w.word_inj a b (lt_of_lt_of_le (mem_range.mp ha) h64)
      (lt_of_lt_of_le (mem_range.mp hb) h64) hab
  have hsub : Z.val ⊆ (subW w.v k).roots := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := mem_image.mp (Finset.mem_val.mp ha)
    rw [mem_roots (subW_ne_zero w.v k)]
    exact hvan q (mem_range.mp hq)
  have hle := card_le_degree_of_subset_roots hsub
  rw [hZ, (subW_monic w.v k).2] at hle
  have : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

omit [CharP K 2] in
/-- The novel basis polynomial `X_y = Π_{k < n, bit k of y} W_k / W_k(v_k)`. -/
noncomputable def novel (v : ℕ → K) (n y : ℕ) : K[X] :=
  ∏ k ∈ (range n).filter (fun k => y.testBit k), C (subRoot v k)⁻¹ * subW v k

/-- The bits of `y < 2^n` sum to `y`. -/
theorem sum_testBit : ∀ (n y : ℕ), y < 2 ^ n →
    ∑ k ∈ (range n).filter (fun k => y.testBit k), 2 ^ k = y
  | 0, y, hy => by
    have : y = 0 := by simpa using hy
    simp [this]
  | n + 1, y, hy => by
    have ih := sum_testBit n (y / 2) (by rw [pow_succ] at hy; omega)
    rw [sum_filter] at ih ⊢
    rw [sum_range_succ']
    have hs : ∑ k ∈ range n, (if y.testBit (k + 1) then 2 ^ (k + 1) else 0)
        = 2 * ∑ k ∈ range n, (if (y / 2).testBit k then 2 ^ k else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [Nat.testBit_div_two]
      split_ifs <;> ring
    rw [hs, ih, Nat.testBit_zero]
    by_cases h : y % 2 = 1
    · simp [h]
      omega
    · simp [h]
      omega

/-- **`X_y` has degree `y`** (and is not zero), for `y < 2^n`, `n ≤ 64`. -/
theorem novel_natDegree (w : Words K) {n y : ℕ} (hn : n ≤ 64) (hy : y < 2 ^ n) :
    (novel w.v n y).natDegree = y ∧ novel w.v n y ≠ 0 := by
  have hf : ∀ k ∈ (range n).filter (fun k => y.testBit k),
      C (subRoot w.v k)⁻¹ * subW w.v k ≠ 0 := by
    intro k hk
    have hk64 : k < 64 := lt_of_lt_of_le (mem_range.mp (mem_filter.mp hk).1) hn
    exact mul_ne_zero (C_ne_zero.mpr (inv_ne_zero (subRoot_ne_zero w hk64))) (subW_ne_zero _ _)
  refine ⟨?_, prod_ne_zero_iff.mpr hf⟩
  unfold novel
  rw [natDegree_prod _ _ hf]
  conv_rhs => rw [← sum_testBit n y hy]
  refine sum_congr rfl fun k hk => ?_
  have hk64 : k < 64 := lt_of_lt_of_le (mem_range.mp (mem_filter.mp hk).1) hn
  rw [natDegree_C_mul (inv_ne_zero (subRoot_ne_zero w hk64)), (subW_monic _ _).2]

/-! ### The verifier's induced weight is the novel basis's -/

omit [CharP K 2] in
/-- `Σ_{y < 2^n} Π_{k<n} (bit k of y ? p_k : 1 − p_k) · Π_{k<n, bit k of y} a_k = Π_{k<n} (1 − p_k +
p_k a_k)`: a product's multilinear extension. -/
theorem sum_eq_prod_bits {R : Type} [CommRing R] (p a : ℕ → R) : ∀ n,
    ∑ y ∈ range (2 ^ n), (∏ k ∈ range n, if y.testBit k then p k else 1 - p k) *
      ∏ k ∈ (range n).filter (fun k => y.testBit k), a k = ∏ k ∈ range n, (1 - p k + p k * a k)
  | 0 => by simp
  | n + 1 => by
    set T : ℕ → R := fun y => (∏ k ∈ range n, if y.testBit k then p k else 1 - p k) *
      ∏ k ∈ (range n).filter (fun k => y.testBit k), a k with hT
    have h1 : ∀ y ∈ range (2 ^ n), (∏ k ∈ range (n + 1), if y.testBit k then p k else 1 - p k) *
        ∏ k ∈ (range (n + 1)).filter (fun k => y.testBit k), a k = (1 - p n) * T y := by
      intro y hy
      have hb : y.testBit n = false := Nat.testBit_lt_two_pow (mem_range.mp hy)
      rw [prod_range_succ, range_add_one, filter_insert]
      simp only [hb, Bool.false_eq_true, ite_false, hT]
      ring
    have h2 : ∀ y ∈ range (2 ^ n),
        (∏ k ∈ range (n + 1), if (2 ^ n + y).testBit k then p k else 1 - p k) *
          ∏ k ∈ (range (n + 1)).filter (fun k => (2 ^ n + y).testBit k), a k =
        (p n * a n) * T y := by
      intro y hy
      have hb : (2 ^ n + y).testBit n = true := by
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (mem_range.mp hy)]
        rfl
      have hlow : ∀ k ∈ range n, (2 ^ n + y).testBit k = y.testBit k :=
        fun k hk => Nat.testBit_two_pow_add_gt (mem_range.mp hk) y
      rw [prod_range_succ, range_add_one, filter_insert]
      simp only [hb, ite_true]
      rw [prod_insert (by simp), prod_congr rfl fun k hk => by rw [hlow k hk],
        filter_congr fun k hk => by rw [hlow k hk]]
      ring
    rw [pow_succ, mul_two, sum_range_add, sum_congr rfl h1, sum_congr rfl h2, ← mul_sum, ← mul_sum,
      ← add_mul, sum_eq_prod_bits p a n, prod_range_succ]
    ring

omit [CharP K 2] in
/-- **`induced_weight` is the novel basis's** (`whir.rs`): at a point `x` (`K(q)` for a query `q`),
the multilinear extension in `y` of `X_y(x)` at a point `p` of `E^n` is
`Π_k (1 + p_k (1 + W_k(x) · W_k(v_k)⁻¹))`, the verifier's `product *= ONE + challenge * (K(1) + basis
* inverses[coordinate])` (characteristic 2: `1 − p = 1 + p`, `eq(p, y) = Π_k (bit k of y ? p_k :
1 + p_k)`). -/
theorem novel_mle {E : Type} [Field E] [Algebra K E] (h2E : (2 : E) = 0) (v : ℕ → K) (n : ℕ)
    (x : K) (p : ℕ → E) :
    ∑ y ∈ range (2 ^ n), (∏ k ∈ range n, if y.testBit k then p k else 1 + p k) *
        algebraMap K E ((novel v n y).eval x) =
      ∏ k ∈ range n, (1 + p k * (1 + algebraMap K E ((subW v k).eval x * (subRoot v k)⁻¹))) := by
  have hneg : ∀ z : E, 1 + z = 1 - z := by
    intro z
    have : z + z = 0 := by rw [← two_mul, h2E, zero_mul]
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left this]
  have hev : ∀ y, algebraMap K E ((novel v n y).eval x) =
      ∏ k ∈ (range n).filter (fun k => y.testBit k),
        algebraMap K E ((subW v k).eval x * (subRoot v k)⁻¹) := by
    intro y
    simp only [novel, eval_prod, eval_mul, eval_C, map_prod]
    refine prod_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hf : ∀ y : ℕ, (∏ k ∈ range n, if y.testBit k then p k else 1 + p k) =
      ∏ k ∈ range n, if y.testBit k then p k else 1 - p k :=
    fun y => prod_congr rfl fun k _ => by rw [hneg]
  simp only [hev, hf]
  rw [sum_eq_prod_bits p (fun k => algebraMap K E ((subW v k).eval x * (subRoot v k)⁻¹)) n]
  refine prod_congr rfl fun k _ => ?_
  rw [← hneg (p k)]
  ring

/-! ### Condition (Q) for the deployed encoding -/

/-- `D = 2^LOG_PIECE − GADGET = 247`: the first piece's entries below the gadget. -/
def freeEntries : ℕ := 247

/-- The entries `0 .. D` of a lane of `2^ℓ` (the layout's `first`). -/
def firstFree (ℓ : ℕ) : Finset (Fin (2 ^ ℓ)) := univ.filter fun y : Fin (2 ^ ℓ) => (y : ℕ) < 247

omit [CharP K 2] in
/-- **The deployed encoding** of a lane of `2^ℓ` entries at the opened positions `pos x`: entry
`y`'s novel basis polynomial at `K(pos x)`, so that a lane `T` reads `Σ_y T(y) X_y(K(q))` at row `q`
(`rowsMap`). -/
noncomputable def novelEnc (w : Words K) (ℓ : ℕ) {Q : Type} (pos : Q → ℕ) : Q → Fin (2 ^ ℓ) → K :=
  fun x y => (novel w.v ℓ y).eval (w.word (pos x))

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- **Condition (Q), deployed.** At `|Q| ≤ D` distinct positions of the level-0 domain of a lane of
`2^ℓ` words (`8 ≤ ℓ ≤ 63`), the first piece's entries below the gadget take the lanes' codewords
anywhere. -/
theorem novel_firstEval_surjective (w : Words K) {ℓ : ℕ} (hℓ8 : 8 ≤ ℓ) (hℓ : ℓ + 1 ≤ 64)
    (pos : Q → ℕ) (hpos : ∀ x, pos x < 2 ^ (ℓ + 1)) (hinj : Function.Injective pos)
    (hQ : Fintype.card Q ≤ freeEntries) :
    Function.Surjective (firstEval (novelEnc w ℓ pos) (firstFree ℓ)) := by
  have hm : 247 ≤ 2 ^ ℓ :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hℓ8 : 2 ^ 8 ≤ 2 ^ ℓ)
  have h64 : 2 ^ (ℓ + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hℓ
  have hpt : Function.Injective fun x => w.word (pos x) := by
    intro x x' h
    exact hinj (w.word_inj _ _ (lt_of_lt_of_le (hpos x) h64) (lt_of_lt_of_le (hpos x') h64) h)
  exact firstEval_surjective_of_degrees (m := 247) hm (fun y : Fin (2 ^ ℓ) => novel w.v ℓ y)
    (fun y => (novel_natDegree w (by omega) y.isLt).1)
    (fun y => (novel_natDegree w (by omega) y.isLt).2) _ hpt hQ

/-- **The vector behind an unopened row, deployed.** With `|Q| < D`, some first-piece vector below
the gadget is `0` on every opened row's codeword and `1` at any other position `q₀`. -/
theorem novel_unopened (w : Words K) {ℓ : ℕ} (hℓ8 : 8 ≤ ℓ) (hℓ : ℓ + 1 ≤ 64)
    (pos : Q → ℕ) (hpos : ∀ x, pos x < 2 ^ (ℓ + 1)) (hinj : Function.Injective pos)
    (hQ : Fintype.card Q < freeEntries) (q₀ : ℕ) (hq₀ : q₀ < 2 ^ (ℓ + 1)) (hq₀Q : ∀ x, pos x ≠ q₀) :
    ∃ u : Fin (2 ^ ℓ) → K, (∀ y : Fin (2 ^ ℓ), ¬ (y : ℕ) < freeEntries → u y = 0) ∧
      (∀ x, ∑ y, novelEnc w ℓ pos x y * u y = 0) ∧
      ∑ y : Fin (2 ^ ℓ), (novel w.v ℓ y).eval (w.word q₀) * u y = 1 := by
  have hm : 247 ≤ 2 ^ ℓ :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hℓ8 : 2 ^ 8 ≤ 2 ^ ℓ)
  have h64 : 2 ^ (ℓ + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hℓ
  have hpt : Function.Injective fun x => w.word (pos x) := by
    intro x x' h
    exact hinj (w.word_inj _ _ (lt_of_lt_of_le (hpos x) h64) (lt_of_lt_of_le (hpos x') h64) h)
  have hx₀ : ∀ x, w.word (pos x) ≠ w.word q₀ := fun x h =>
    hq₀Q x (w.word_inj _ _ (lt_of_lt_of_le (hpos x) h64) (lt_of_lt_of_le hq₀ h64) h)
  exact exists_unopened_vector (m := 247) hm (fun y : Fin (2 ^ ℓ) => novel w.v ℓ y)
    (fun y => (novel_natDegree w (by omega) y.isLt).1)
    (fun y => (novel_natDegree w (by omega) y.isLt).2) _ hpt hQ _ hx₀

/-! ### The positions a level-0 opening reads (`whir.rs`) -/

/-- Level 0 of `WHIR_QUERIES` at rate `1/2` (`crates/verifier/src/whir.rs:20-25`, its first row's
first entries; mumbai's `queryTable`): the queries of the first commitment for `log_n = 15 .. 28`
(`0` outside the window, where `derive_config` rejects). -/
def whirQueries0 (logN : ℕ) : ℕ :=
  if 15 ≤ logN then
    [222, 223, 223, 223, 223, 223, 223, 224, 224, 224, 224, 224, 225, 225].getD (logN - 15) 0
  else 0

/-- At most `225` queries at any size. -/
theorem whirQueries0_le (logN : ℕ) : whirQueries0 logN ≤ 225 := by
  unfold whirQueries0
  split_ifs
  · generalize logN - 15 = i
    rcases Nat.lt_or_ge i 14 with h | h
    · interval_cases i <;> decide
    · rw [List.getD_eq_default _ _ (by simpa using h)]
      norm_num
  · norm_num

/-- **At our shapes**: the witness table (`log_n = log_rows + 3`) opens `223` or `224` positions of
its first commitment, the quotient table (`log_n = log_rows + 6`) `224` or `225`, at every supported
`17 ≤ log_rows ≤ 22`; all below `D = 247`. -/
theorem deployed_queries : ∀ r, 17 ≤ r → r ≤ 22 →
    223 ≤ whirQueries0 (r + 3) ∧ whirQueries0 (r + 3) ≤ 224 ∧
      224 ≤ whirQueries0 (r + 6) ∧ whirQueries0 (r + 6) ≤ 225 ∧ 225 < freeEntries := by
  intro r h1 h2
  interval_cases r <;> decide

/-- **Condition (Q) at a level-0 opening.** The first commitment of a stack of `2^logN` words
(`15 ≤ logN ≤ 28`, lanes of `ℓ = logN − 6` words) is opened at the positions `qs` that
`sample_queries` draws (`whirQueries0 logN` of them, repeats allowed); on the set `Q` of the distinct
ones, the first piece below the gadget takes the lanes' codewords anywhere, and an unopened position
keeps a vector of its own. -/
theorem deployed_Q (w : Words K) (logN : ℕ) (h1 : 15 ≤ logN) (h2 : logN ≤ 28)
    (qs : Fin (whirQueries0 logN) → Fin (2 ^ (logN - 6 + 1))) :
    let S : Finset ℕ := univ.image fun i => (qs i : ℕ)
    Function.Surjective (firstEval (novelEnc w (logN - 6) (Subtype.val : S → ℕ))
        (firstFree (logN - 6))) ∧
      ∀ q₀ < 2 ^ (logN - 6 + 1), q₀ ∉ S →
        ∃ u : Fin (2 ^ (logN - 6)) → K, (∀ y : Fin (2 ^ (logN - 6)), ¬ (y : ℕ) < freeEntries → u y = 0) ∧
          (∀ x, ∑ y, novelEnc w (logN - 6) (Subtype.val : S → ℕ) x y * u y = 0) ∧
          ∑ y : Fin (2 ^ (logN - 6)), (novel w.v (logN - 6) y).eval (w.word q₀) * u y = 1 := by
  intro S
  have hS : Fintype.card S < freeEntries := by
    rw [Fintype.card_coe]
    calc S.card ≤ (univ : Finset (Fin (whirQueries0 logN))).card := card_image_le
      _ = whirQueries0 logN := by rw [card_univ, Fintype.card_fin]
      _ ≤ 225 := whirQueries0_le logN
      _ < freeEntries := by decide
  have hpos : ∀ x : S, (x : ℕ) < 2 ^ (logN - 6 + 1) := by
    intro x
    obtain ⟨i, -, hi⟩ := mem_image.mp x.2
    rw [← hi]
    exact (qs i).isLt
  refine ⟨novel_firstEval_surjective w (by omega) (by omega) _ hpos Subtype.val_injective hS.le,
    fun q₀ hq₀ hq₀S => novel_unopened w (by omega) (by omega) _ hpos Subtype.val_injective hS q₀ hq₀
      fun x h => hq₀S (h ▸ x.2)⟩

end QuotientSecurity.Hiding
