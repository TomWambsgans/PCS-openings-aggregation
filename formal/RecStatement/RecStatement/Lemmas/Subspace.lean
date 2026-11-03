-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The blocks' vanishing polynomials are
-- `crates/leanvm_rec/src/pi2/circuit.rs`'s (`coset_constants`, `vanishing`, `pair_constants`) and
-- `crates/leanvm_rec/src/pi2/verifier.rs`'s (`normalised_constants`, `Ẑ_s`); the indicator is
-- `formal/RecPiop`'s (`RecPiop.Indicator`).
import RecStatement.Core
import RecPiop.Vanishing

/-!
# The indicators' closed form

`PI2.md` §2 step 3: the verifier evaluates pair `p`'s indicator at `t` as
`I_p(t) = w_m(t) / (Ẑ_s(t) + Ẑ_s(c_p))`, `s` the block's rows' log, `c_p` the pair's first point, and
`Ẑ_s = Z_{U_s} / Π_{j<s} e_j` the normalised vanishing polynomial of `U_s = span(β_r, …, β_{r+s−1})`
(`r` the rows' log), by the recursion `Ẑ_{s+1} = Ẑ_s + c_s Ẑ_s²` (`zHat`). This file proves it is
`RecPiop`'s indicator (`RecPiop.Circuit.ind`, the normalised product over the other positions of `V_m`):

* `zEval b s`: `Z_{U_s}` by its recursion `Z_0(x) = x`, `Z_{s+1} = Z_s² + e_s Z_s`, `e_s = Z_s(b_s)`
  (`zConst`, `coset_constants`); it is additive (`zEval_add`), and with the constants
  `c_s = Π_{j<s} e_j / e_s` (`NormConsts`, `normalised_constants`) `Ẑ_s = Z_s / Π_{j<s} e_j`
  (`zHat_eq_zEval`);
* as a polynomial (`zrec`) it is `Π_{u<2^s} (X + ω(u·2^r))` for an `ω` additive in the bits
  (`zrec_eq_prod`), additive under translation (`zrec_comp`), its derivative the constant
  `Π_{j<s} e_j` (`derivative_zrec`, characteristic two);
* a pair's positions are `c_p ⊕ (u·2^r)`, `u < 2^s` (`inPair_eq_image`), so
  `Z_V = (Z_s + Z_s(c_p)) · Π_{j ∉ p} (X + ω_j)`; at `t` this is the indicator's numerator, and
  differentiating at `c_p` (`Z_V = w_m`, whose derivative is `1` on a Cantor basis,
  `derivative_digitPoly`) its normaliser `1 / Π_{j<s} e_j`: **`ind_eval_closed`**.
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Polynomial Finset QuotientSecurity RecPiop

variable {F : Type} [Field F] [CharP F 2]

/-! ## The recursion -/

/-- `Z_{U_s}(x)` by its recursion, `b_j` the subspace's basis. -/
def zEval (b : ℕ → F) : ℕ → F → F
  | 0, x => x
  | s + 1, x => zEval b s x * zEval b s x + zEval b s (b s) * zEval b s x

/-- `e_s = Z_{U_s}(b_s)` (`coset_constants`). -/
def zConst (b : ℕ → F) (s : ℕ) : F := zEval b s (b s)

/-- The blocks' basis: `b_j = ω(2^(r+j))` (`β_{r+j}` on a Cantor basis). -/
def blockBasis (ω : ℕ → F) (r j : ℕ) : F := ω (2 ^ (r + j))

/-- The normalised recursion's constants (`normalised_constants`): `c_s = Π_{j<s} e_j / e_s` for `s < count`. -/
def NormConsts (b : ℕ → F) (c : List F) (count : ℕ) : Prop :=
  ∀ s < count, c.getD s 0 = (∏ j ∈ range s, zConst b j) / zConst b s

/-- **`Z_{U_s}` is additive.** -/
theorem zEval_add (b : ℕ → F) (s : ℕ) (x y : F) :
    zEval b s (x + y) = zEval b s x + zEval b s y := by
  induction s generalizing x y with
  | zero => rfl
  | succ s ih =>
    have two : (2 : F) = 0 := CharTwo.two_eq_zero
    simp only [zEval]
    rw [ih]
    linear_combination (zEval b s x * zEval b s y) * two

/-- **The normalised recursion** `Ẑ_{s+1} = Ẑ_s + c_s Ẑ_s²` computes `Z_{U_s} / Π_{j<s} e_j`. -/
theorem zHat_eq_zEval (b : ℕ → F) (c : List F) {s : ℕ} (hc : NormConsts b c s)
    (he : ∀ j < s, zConst b j ≠ 0) (x : F) :
    zHat c s x = zEval b s x / ∏ j ∈ range s, zConst b j := by
  induction s with
  | zero => simp [zHat, zEval]
  | succ s ih =>
    have hE : ∏ j ∈ range s, zConst b j ≠ 0 :=
      prod_ne_zero_iff.mpr fun j hj => he j (by rw [mem_range] at hj; omega)
    have he' : zConst b s ≠ 0 := he s (by omega)
    rw [zHat, ih (fun k hk => hc k (by omega)) (fun j hj => he j (by omega)), hc s (by omega),
      prod_range_succ]
    simp only [zEval]
    unfold zConst at he' ⊢
    field_simp
    ring

/-! ## As a polynomial -/

/-- `Z_{U_s}` as a polynomial. -/
noncomputable def zrec (b : ℕ → F) : ℕ → F[X]
  | 0 => X
  | s + 1 => zrec b s ^ 2 + C (zConst b s) * zrec b s

theorem zrec_eval (b : ℕ → F) (s : ℕ) (x : F) : (zrec b s).eval x = zEval b s x := by
  induction s generalizing x with
  | zero => simp [zrec, zEval]
  | succ s ih =>
    simp only [zrec, zEval, eval_add, eval_pow, eval_mul, eval_C, ih]
    unfold zConst
    ring

/-- **`Z_{U_s}` is additive under translation**: `Z(X + y) = Z(X) + Z(y)`. -/
theorem zrec_comp (b : ℕ → F) (s : ℕ) (y : F) :
    (zrec b s).comp (X + C y) = zrec b s + C (zEval b s y) := by
  induction s with
  | zero => simp [zrec, zEval]
  | succ s ih =>
    have two : (2 : F[X]) = 0 := CharTwo.two_eq_zero
    rw [zrec, add_comp, mul_comp, pow_comp, C_comp, ih]
    simp only [zEval, C_add, C_mul]
    unfold zConst
    linear_combination (zrec b s * C (zEval b s y)) * two

/-- **The derivative of `Z_{U_s}`** is the constant `Π_{j<s} e_j` (characteristic two). -/
theorem derivative_zrec (b : ℕ → F) (s : ℕ) :
    derivative (zrec b s) = C (∏ j ∈ range s, zConst b j) := by
  induction s with
  | zero => simp [zrec]
  | succ s ih =>
    have two : C (2 : F) = 0 := by rw [CharTwo.two_eq_zero, C_0]
    rw [zrec, derivative_add, derivative_sq, derivative_mul, derivative_C, ih, two, prod_range_succ,
      C_mul]
    ring

/-- Adding a multiple of `2^m` to a number below `2^m` is the bits' xor. -/
theorem add_eq_xor_of_dvd {a b m : ℕ} (ha : 2 ^ m ∣ a) (hb : b < 2 ^ m) : a + b = a ^^^ b := by
  obtain ⟨q, rfl⟩ := ha
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hmod : (2 ^ m * q ^^^ b) % 2 ^ m = b := by
    rw [Nat.xor_mod_two_pow, Nat.mul_mod_right, Nat.mod_eq_of_lt hb, Nat.zero_xor]
  have hdiv : (2 ^ m * q ^^^ b) / 2 ^ m = q := by
    rw [Nat.xor_div_two_pow, Nat.mul_div_cancel_left q hpos, Nat.div_eq_of_lt hb, Nat.xor_zero]
  have h1 : (2 ^ m * q + b) % 2 ^ m = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have h2 : (2 ^ m * q + b) / 2 ^ m = q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, zero_add]
  calc 2 ^ m * q + b = 2 ^ m * ((2 ^ m * q + b) / 2 ^ m) + (2 ^ m * q + b) % 2 ^ m :=
        (Nat.div_add_mod _ _).symm
    _ = 2 ^ m * ((2 ^ m * q ^^^ b) / 2 ^ m) + (2 ^ m * q ^^^ b) % 2 ^ m := by
        rw [h1, h2, hdiv, hmod]
    _ = 2 ^ m * q ^^^ b := Nat.div_add_mod _ _

theorem omega_zero_of_xor {ω : ℕ → F} (hx : ∀ a b, ω (a ^^^ b) = ω a + ω b) : ω 0 = 0 := by
  have h := hx 0 0
  rw [Nat.xor_self, CharTwo.add_self_eq_zero] at h
  exact h

/-- **`Z_{U_s} = Π_{u<2^s} (X + ω(u·2^r))`** for an `ω` additive in the bits, `U_s`'s basis
`ω(2^(r+j))`. -/
theorem zrec_eq_prod {ω : ℕ → F} (hx : ∀ a b, ω (a ^^^ b) = ω a + ω b) (r s : ℕ) :
    zrec (blockBasis ω r) s = ∏ u ∈ range (2 ^ s), (X + C (ω (u * 2 ^ r))) := by
  induction s with
  | zero => simp [zrec, omega_zero_of_xor hx]
  | succ s ih =>
    rw [pow_succ, mul_two, prod_range_add, ← ih]
    have hshift : ∀ u ∈ range (2 ^ s), X + C (ω ((2 ^ s + u) * 2 ^ r)) =
        (X + C (ω (u * 2 ^ r))).comp (X + C (blockBasis ω r s)) := by
      intro u hu
      rw [mem_range] at hu
      have hlt : u * 2 ^ r < 2 ^ (r + s) := by
        rw [pow_add, mul_comm (2 ^ r)]
        exact Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos r)
      have e : (2 ^ s + u) * 2 ^ r = 2 ^ (r + s) ^^^ (u * 2 ^ r) := by
        rw [add_mul, ← pow_add, add_comm s r]
        exact add_eq_xor_of_dvd (dvd_refl _) hlt
      rw [e, hx, add_comp, X_comp, C_comp, blockBasis, C_add]
      ring
    rw [prod_congr rfl hshift, ← Polynomial.prod_comp, ← ih, zrec_comp, zrec]
    unfold zConst
    ring

/-! ## The pairs' positions -/

/-- A pair's position: `(row + u)·W + k = c_p ⊕ (u·2^r)`, the row aligned to the block. -/
theorem pair_position_xor {row s r u k : ℕ} (hrow : 2 ^ s ∣ row) (hu : u < 2 ^ s) (hk : k < 2 ^ r) :
    (row + u) * 2 ^ r + k = (row * 2 ^ r + k) ^^^ (u * 2 ^ r) := by
  have hlt : u * 2 ^ r < 2 ^ (s + r) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos r)
  have hdvd : 2 ^ (s + r) ∣ row * 2 ^ r := by
    rw [pow_add]
    exact Nat.mul_dvd_mul_right hrow _
  have e1 : (row + u) * 2 ^ r = row * 2 ^ r ^^^ u * 2 ^ r := by
    rw [add_mul]
    exact add_eq_xor_of_dvd hdvd hlt
  have e2 : (row + u) * 2 ^ r + k = (row + u) * 2 ^ r ^^^ k :=
    add_eq_xor_of_dvd (Dvd.intro_left _ rfl) hk
  have e3 : row * 2 ^ r + k = row * 2 ^ r ^^^ k := add_eq_xor_of_dvd (Dvd.intro_left _ rfl) hk
  rw [e2, e1, e3, Nat.xor_assoc, Nat.xor_comm (u * 2 ^ r) k, ← Nat.xor_assoc]

variable [DecidableEq F] {G : RecPiop.Circuit F}

/-- **A pair's positions** are `(row + u)·W + k`, `u < 2^s`. -/
theorem inPair_eq_image (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) :
    (range G.N).filter (fun i => G.InPair p i) =
      (range (2 ^ p.1.logRows)).image fun u => (p.1.row + u) * G.W + p.2 := by
  obtain ⟨hb, hk, -⟩ := RecPiop.Circuit.mem_pairs.mp hp
  have hW : 0 < G.W := Nat.two_pow_pos _
  have hr := hV.in_range _ hb
  ext i
  rw [mem_filter, mem_image]
  constructor
  · intro ⟨_, hin⟩
    unfold RecPiop.Circuit.InPair RecPiop.Circuit.Covers at hin
    obtain ⟨-, ⟨hc1, hc2⟩, hmod⟩ := hin
    refine ⟨i / G.W - p.1.row, mem_range.mpr (by omega), ?_⟩
    have : p.1.row + (i / G.W - p.1.row) = i / G.W := by omega
    rw [this, ← hmod]
    exact Nat.div_add_mod' i G.W
  · rintro ⟨u, hu, rfl⟩
    rw [mem_range] at hu
    have hdiv : ((p.1.row + u) * G.W + p.2) / G.W = p.1.row + u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hk, zero_add]
    have hlt : (p.1.row + u) * G.W + p.2 < G.N := by
      rw [RecPiop.Circuit.N_eq hV]
      have : p.1.row + u + 1 ≤ G.rows := by omega
      nlinarith
    refine ⟨mem_range.mpr hlt, ?_⟩
    unfold RecPiop.Circuit.InPair RecPiop.Circuit.Covers
    refine ⟨hlt, ⟨?_, ?_⟩, ?_⟩
    · rw [hdiv]; omega
    · rw [hdiv]; omega
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

/-- The parametrisation is injective. -/
theorem pair_param_injOn {p : Block × ℕ} :
    Set.InjOn (fun u => (p.1.row + u) * G.W + p.2) (range (2 ^ p.1.logRows) : Set ℕ) := by
  intro u _ v _ h
  have hW : 0 < G.W := Nat.two_pow_pos _
  simp only at h
  have : (p.1.row + u) * G.W = (p.1.row + v) * G.W := by omega
  have := Nat.eq_of_mul_eq_mul_right hW this
  omega

/-- **A pair's product is `Z_{U_s}` translated to its first point**:
`Π_{j ∈ p} (X + ω_j) = Z_s(X) + Z_s(c_p)`. -/
theorem pair_prod {ω : ℕ → F} (hx : ∀ a a', ω (a ^^^ a') = ω a + ω a') (hV : G.Valid)
    {p : Block × ℕ} (hp : p ∈ G.pairs) :
    ∏ i ∈ (range G.N).filter (fun i => G.InPair p i), (X + C (ω i)) =
      zrec (blockBasis ω G.logW) p.1.logRows +
        C (zEval (blockBasis ω G.logW) p.1.logRows (ω (G.pairBase p))) := by
  obtain ⟨hb, hk, -⟩ := RecPiop.Circuit.mem_pairs.mp hp
  have hal : 2 ^ p.1.logRows ∣ p.1.row := hV.aligned _ hb
  rw [inPair_eq_image hV hp, prod_image pair_param_injOn, ← zrec_comp, zrec_eq_prod hx,
    Polynomial.prod_comp]
  refine prod_congr rfl fun u hu => ?_
  rw [mem_range] at hu
  have hpos : (p.1.row + u) * G.W + p.2 = G.pairBase p ^^^ (u * 2 ^ G.logW) :=
    pair_position_xor hal hu hk
  show X + C (ω ((p.1.row + u) * G.W + p.2)) = _
  rw [hpos, hx, add_comp, X_comp, C_comp, C_add]
  ring

/-- **The derivative of `w_m` is `1`** (characteristic two: `(s ∘ f)' = (2f + 1) f'`). -/
theorem derivative_digitPoly : ∀ k : ℕ, derivative (digitPoly k : F[X]) = 1
  | 0 => by simp [digitPoly]
  | k + 1 => by
    have two : C (2 : F) = 0 := by rw [CharTwo.two_eq_zero, C_0]
    rw [digitPoly, derivative_comp, derivative_digitPoly k, one_mul, derivative_add, derivative_X_pow,
      derivative_X]
    simp [two]

/-- **The indicators' closed form** (`PI2.md` §2 step 3): at `t ∉ V_m`,
`I_p(t) = w_m(t)/(Ẑ_s(t) + Ẑ_s(c_p))`. -/
theorem ind_eval_closed {n : ℕ} (B : CantorBasis F n) (hn : G.logN ≤ n)
    (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) {c : List F}
    (hc : NormConsts (blockBasis (Heap.omega B) G.logW) c p.1.logRows) {t : F}
    (ht : sq^[G.logN] t ≠ 0) :
    zHat c p.1.logRows t + zHat c p.1.logRows (Heap.omega B (G.pairBase p)) ≠ 0 ∧
    (G.ind (Heap.omega B) p).eval t =
      sq^[G.logN] t / (zHat c p.1.logRows t + zHat c p.1.logRows (Heap.omega B (G.pairBase p))) := by
  have hx : ∀ a a', Heap.omega B (a ^^^ a') = Heap.omega B a + Heap.omega B a' := Heap.omega_xor B
  -- `w_m = Z_V = (Z_s + Z_s(c_p)) · Π_{j ∉ p} (X + ω_j)`.
  have hZ : (digitPoly G.logN : F[X]) =
      (zrec (blockBasis (Heap.omega B) G.logW) p.1.logRows +
        C (zEval (blockBasis (Heap.omega B) G.logW) p.1.logRows (Heap.omega B (G.pairBase p)))) *
      ∏ i ∈ G.compl p, (X + C (Heap.omega B i)) := by
    rw [← RecPiop.Circuit.zV_eq_digitPoly G B hn, RecPiop.Circuit.zV, ← pair_prod hx hV hp]
    exact (prod_filter_mul_prod_filter_not (range G.N) (fun i => G.InPair p i) _).symm
  have hind : (G.ind (Heap.omega B) p).eval t =
      ((∏ i ∈ G.compl p, (X + C (Heap.omega B i))).eval (Heap.omega B (G.pairBase p)))⁻¹ *
        (∏ i ∈ G.compl p, (X + C (Heap.omega B i))).eval t := by
    unfold RecPiop.Circuit.ind
    simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
  generalize (∏ i ∈ G.compl p, (X + C (Heap.omega B i))) = Q at hZ hind
  generalize blockBasis (Heap.omega B) G.logW = b at hZ hc
  generalize Heap.omega B (G.pairBase p) = z at hZ hind ⊢
  generalize p.1.logRows = s at hZ hc ⊢
  rw [hind]
  -- At `t`: `w_m(t) = (Z_s(t) + Z_s(c_p)) Q(t)`.
  have hat : sq^[G.logN] t = (zEval b s t + zEval b s z) * Q.eval t := by
    rw [← digitPoly_eval, hZ, eval_mul, eval_add, eval_C, zrec_eval]
  -- Differentiating at `c_p`: `1 = E_s Q(c_p)`.
  have hder : (∏ j ∈ range s, zConst b j) * Q.eval z = 1 := by
    have h := congrArg (fun f : F[X] => (derivative f).eval z) hZ
    simp only [derivative_digitPoly, eval_one, derivative_mul, derivative_add, derivative_C, add_zero,
      derivative_zrec, eval_add, eval_mul, eval_C, zrec_eval, CharTwo.add_self_eq_zero, zero_mul] at h
    exact h.symm
  have hE : (∏ j ∈ range s, zConst b j) ≠ 0 := left_ne_zero_of_mul_eq_one hder
  have he : ∀ j < s, zConst b j ≠ 0 := fun j hj => (prod_ne_zero_iff.mp hE) j (mem_range.mpr hj)
  have hQc : Q.eval z = (∏ j ∈ range s, zConst b j)⁻¹ := eq_inv_of_mul_eq_one_right hder
  have hA : zEval b s t + zEval b s z ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hat
    exact ht hat
  have hsum : zHat c s t + zHat c s z = (zEval b s t + zEval b s z) / ∏ j ∈ range s, zConst b j := by
    rw [zHat_eq_zEval b c hc he, zHat_eq_zEval b c hc he, add_div]
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact div_ne_zero hA hE
  · rw [hQc, inv_inv, hsum, hat]
    field_simp

end RecStatement
