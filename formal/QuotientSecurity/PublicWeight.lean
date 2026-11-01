-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/PublicWeight.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Concrete

/-!
# The public weight, as the verifier evaluates it

The Rust verifier computes the public weight at the challenge as a product: one factor
`1 + w_k` for each digit past the public region, which selects the region, and one factor
`1 + x_k (1 + μ_k)` for each coordinate `x_k` of the region, a combination of digits that is the
`k`-th bit of a cell there. This file shows that product is a public weight for the words it
encodes, of the degree `knowledgeSoundness_ofCantor` asks.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]
variable {N : ℕ} (B : CantorBasis F N) {m R : ℕ} (b : ℕ → F)

/-! ## Coordinates of the region -/

/-- Coordinate `k` of the region: `sum_j b (j - k) w_j` over the region's digits from `k` on. -/
noncomputable def coordPoly (R k : ℕ) : F[X] := ∑ j ∈ Finset.Ico k R, C (b (j - k)) * digitPoly j

theorem coordPoly_eval (k : ℕ) (t : F) :
    (coordPoly b R k).eval t = ∑ j ∈ Finset.Ico k R, b (j - k) * sq^[j] t := by
  simp [coordPoly, eval_finsetSum, digitPoly_eval]

/-- On a basis vector of the region, coordinate `k` is one at the `k`-th and zero elsewhere, when
`b` inverts the basis: `b 0 = 1` and `sum_e b e * beta (d - e) = 0`, the recurrence
`quotient::domain::coordinates` computes. -/
theorem coord_basis (hR : R ≤ N) (hb0 : b 0 = 1)
    (hb : ∀ d, 1 ≤ d → d < R → ∑ e ∈ Finset.range (d + 1), b e * B.β (d - e) = 0)
    (i k : ℕ) (hi : i < R) :
    ∑ j ∈ Finset.Ico k R, b (j - k) * sq^[j] (B.β i) = if i = k then 1 else 0 := by
  have h1 : ∀ j, sq^[j] (B.β i) = if j ≤ i then B.β (i - j) else 0 := fun j =>
    B.iterate j i (by omega)
  simp only [h1]
  have h2 : ∑ j ∈ Finset.Ico k R, b (j - k) * (if j ≤ i then B.β (i - j) else 0)
      = ∑ j ∈ Finset.Ico k (i + 1), b (j - k) * B.β (i - j) := by
    refine (Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega)) fun j hj hj' => ?_).symm.trans
      (Finset.sum_congr rfl fun j hj => ?_)
    · have := Finset.mem_Ico.mp hj
      have hji : ¬ j ≤ i := fun h => hj' (Finset.mem_Ico.mpr ⟨this.1, by omega⟩)
      rw [if_neg hji, mul_zero]
    · have := Finset.mem_Ico.mp hj
      rw [if_pos (by omega)]
  rw [h2, Finset.sum_Ico_eq_sum_range]
  by_cases hik : i = k
  · subst hik
    simp [hb0, B.zero]
  · rw [if_neg hik]
    by_cases hlt : i < k
    · have : i + 1 - k = 0 := by omega
      rw [this]
      simp
    · have hd := hb (i - k) (by omega) (by omega)
      rw [show i + 1 - k = i - k + 1 by omega]
      refine (Finset.sum_congr rfl fun e _ => ?_).trans hd
      rw [Nat.add_sub_cancel_left, Nat.sub_add_eq]

/-- **A coordinate is a bit**, on the cells of the region. -/
theorem coordPoly_point (hm : m ≤ N) (hRm : R ≤ m) (hb0 : b 0 = 1)
    (hb : ∀ d, 1 ≤ d → d < R → ∑ e ∈ Finset.range (d + 1), b e * B.β (d - e) = 0)
    (x : Fin m → Bool) (hx : ∀ j : Fin m, R ≤ (j : ℕ) → x j = false) (k : Fin m) :
    (coordPoly b R k).eval (B.point x) = if x k then 1 else 0 := by
  rw [coordPoly_eval]
  unfold CantorBasis.point
  simp only [sq_iterate_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ i : Fin m, ∑ j ∈ Finset.Ico (k : ℕ) R, b (j - k) * sq^[j] (if x i then B.β i else 0)
      = if x i = true ∧ i = k then 1 else 0 := by
    intro i
    by_cases hxi : x i = true
    · have hiR : (i : ℕ) < R := by
        by_contra h
        rw [hx i (by omega)] at hxi
        exact Bool.false_ne_true hxi
      simp only [hxi, ite_true, true_and]
      rw [coord_basis B b (hRm.trans hm) hb0 hb i k hiR]
      simp [Fin.ext_iff]
    · simp [hxi, sq_iterate_zero]
  simp only [hterm]
  rw [Finset.sum_eq_single k (fun i _ hik => by simp [hik]) fun h => absurd (Finset.mem_univ k) h]
  simp

/-! ## The region's selector -/

/-- One on the cells whose bits from `R` on are zero, zero on the other cells. -/
noncomputable def hiPoly (R m : ℕ) : F[X] := ∏ j ∈ Finset.Ico R m, (1 + digitPoly j)

theorem hiPoly_point (hm : m ≤ N) (x : Fin m → Bool) [Decidable (∀ j : Fin m, R ≤ (j : ℕ) → x j = false)] :
    (hiPoly R m : F[X]).eval (B.point x)
      = if ∀ j : Fin m, R ≤ (j : ℕ) → x j = false then 1 else 0 := by
  rw [hiPoly, eval_prod]
  simp only [eval_add, eval_one, digitPoly_eval]
  split_ifs with h
  · refine Finset.prod_eq_one fun j hj => ?_
    have hjR := (Finset.mem_Ico.mp hj).1
    have : sq^[j] (B.point x) = 0 := by
      unfold CantorBasis.point
      rw [sq_iterate_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hxi : x i = true
      · have hiR : (i : ℕ) < R := by
          by_contra h'
          rw [h i (by omega)] at hxi
          exact Bool.false_ne_true hxi
        rw [if_pos hxi, B.iterate _ _ (lt_of_lt_of_le i.2 hm), if_neg (by omega)]
      · rw [if_neg hxi, sq_iterate_zero]
    rw [this, add_zero]
  · push_neg at h
    obtain ⟨j0, hj0, hxj0⟩ := h
    have hS : (univ.filter fun j : Fin m => x j = true).Nonempty :=
      ⟨j0, by simpa using hxj0⟩
    set i := (univ.filter fun j : Fin m => x j = true).max' hS with hi
    have hmem := Finset.max'_mem _ hS
    rw [← hi, Finset.mem_filter] at hmem
    have hRi : R ≤ (i : ℕ) := hj0.trans (Finset.le_max' _ j0 (by simpa using hxj0))
    have habove : B.above i x = 0 := by
      unfold CantorBasis.above
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      rintro ⟨hij, hxj⟩
      exact absurd (Finset.le_max' _ j (by simpa using hxj)) (not_le.mpr hij)
    refine Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨hRi, i.2⟩) ?_
    rw [B.digit_eq hm i x, habove, hmem.2]
    simp [CharTwo.add_self_eq_zero]

/-! ## The product -/

variable (μ : ℕ → F → F)

/-- The public weight as a product: the region's selector, and `1 + x_k (1 + μ_k)` for each
coordinate of the region. -/
noncomputable def pubProd (R m : ℕ) (γ : F) : F[X] :=
  hiPoly R m * ∏ k ∈ Finset.range R, (1 + coordPoly b R k * C (1 + μ k γ))

/-- Bit `k` of a cell. -/
def bitAt (x : Fin m → Bool) (k : ℕ) : Bool := if h : k < m then x ⟨k, h⟩ else false

/-- **On a cell, the product is the product of the weights of its set bits**, in the region, and
zero off it. -/
theorem pubProd_point (hm : m ≤ N) (hRm : R ≤ m) (hb0 : b 0 = 1)
    (hb : ∀ d, 1 ≤ d → d < R → ∑ e ∈ Finset.range (d + 1), b e * B.β (d - e) = 0)
    (γ : F) (x : Fin m → Bool) [Decidable (∀ j : Fin m, R ≤ (j : ℕ) → x j = false)] :
    (pubProd b μ R m γ).eval (B.point x)
      = if ∀ j : Fin m, R ≤ (j : ℕ) → x j = false
        then ∏ k ∈ Finset.range R, (if bitAt x k then μ k γ else 1) else 0 := by
  rw [pubProd, eval_mul, hiPoly_point B hm x]
  split_ifs with h
  · rw [one_mul, eval_prod]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkm : k < m := lt_of_lt_of_le (Finset.mem_range.mp hk) hRm
    have hc := coordPoly_point B b hm hRm hb0 hb x h ⟨k, hkm⟩
    simp only at hc
    rw [eval_add, eval_one, eval_mul, eval_C, hc, bitAt, dif_pos hkm]
    cases x ⟨k, hkm⟩
    · simp
    · simp only [ite_true, one_mul]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · rw [zero_mul]

theorem natDegree_coordPoly_le (k : ℕ) : (coordPoly b R k).natDegree ≤ 2 ^ (R - 1) := by
  unfold coordPoly
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_digitPoly_le _).trans ?_)
  exact Nat.pow_le_pow_right (by norm_num) (by have := Finset.mem_Ico.mp hj; omega)

theorem natDegree_pubProd_le (γ : F) :
    (pubProd b μ R m γ).natDegree ≤ ∑ j ∈ Finset.Ico R m, 2 ^ j + R * 2 ^ (R - 1) := by
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact natDegree_add_le_of_degree_le (by simp) (natDegree_digitPoly_le j)
  · refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => 2 ^ (R - 1)) fun k _ => ?_).trans (by simp)
    exact natDegree_add_le_of_degree_le (by simp)
      ((natDegree_mul_C_le _ _).trans (natDegree_coordPoly_le b k))

/-! ## Words given by weights -/

/-- A public word: a weighted sum of cells. -/
def weightedSum {ι : Type*} [Fintype ι] (wt : ι → F) : (ι → F) →ₗ[F] F :=
  ∑ x, wt x • LinearMap.proj x

theorem weightedSum_apply {ι : Type*} [Fintype ι] (wt w : ι → F) :
    weightedSum wt w = ∑ x, wt x * w x := by
  simp [weightedSum, LinearMap.sum_apply]

/-- A polynomial whose value on each cell is the sum of the words' weights there, each times its
power of `γ`, is a public weight for those words. -/
theorem hPub_of_weights {words : ℕ} (pub : F → F[X]) (wt : Fin words → (Fin m → Bool) → F)
    (h : ∀ γ x, (pub γ).eval (B.point x) = ∑ J : Fin words, γ ^ (J : ℕ) * wt J x) :
    ∀ (γ : F) (w : (Fin m → Bool) → F), ∑ x, (pub γ).eval (B.point x) * w x
      = ∑ J : Fin words, γ ^ (J : ℕ) * weightedSum (wt J) w := by
  intro γ w
  simp only [h, weightedSum_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun x _ => by ring

/-! ## The layout of `quotient::protocol`

A region of `2^11` cells: coordinates 0 to 7 choose a bit of a word and carry constant weights
(coordinate 1 the weight zero, so only the `X` and `Y` cells count), coordinates 8 to 10 choose
one of eight words and carry `γ`, `γ^2`, `γ^4`. -/

section Membership

variable (c : ℕ → F)

/-- The weight of coordinate `k`. -/
def regionMu (k : ℕ) (γ : F) : F := if k < 8 then c k else γ ^ (2 ^ (k - 8))

/-- The word a cell of the region belongs to. -/
def wordOf (x : Fin (22 + 2) → Bool) : Fin 8 :=
  ⟨(x 8).toNat + 2 * (x 9).toNat + 4 * (x 10).toNat, by
    cases x 8 <;> cases x 9 <;> cases x 10 <;> decide⟩

/-- The weight of a cell in word `J`: the product of the weights of its set bits below 8, on the
cells of the region that belong to the word. -/
def regionWeight (J : Fin 8) (x : Fin (22 + 2) → Bool) : F :=
  if (∀ j : Fin (22 + 2), 11 ≤ (j : ℕ) → x j = false) ∧ wordOf x = J
  then ∏ k ∈ Finset.range 8, (if bitAt x k then c k else 1) else 0

theorem region_weights (γ : F) (x : Fin (22 + 2) → Bool) :
    (if ∀ j : Fin (22 + 2), 11 ≤ (j : ℕ) → x j = false
      then ∏ k ∈ Finset.range 11, (if bitAt x k then regionMu c k γ else 1) else 0)
      = ∑ J : Fin 8, γ ^ (J : ℕ) * regionWeight c J x := by
  by_cases h : ∀ j : Fin (22 + 2), 11 ≤ (j : ℕ) → x j = false
  · rw [if_pos h]
    have hw : ∀ J, regionWeight c J x = if wordOf x = J
        then ∏ k ∈ Finset.range 8, (if bitAt x k then c k else 1) else 0 := fun J => by
      unfold regionWeight
      by_cases hJ : wordOf x = J
      · rw [if_pos ⟨h, hJ⟩, if_pos hJ]
      · rw [if_neg (fun h' => hJ h'.2), if_neg hJ]
    simp only [hw]
    rw [Finset.sum_eq_single (wordOf x) (fun J _ hJ => by rw [if_neg (Ne.symm hJ), mul_zero])
      fun h' => absurd (Finset.mem_univ _) h']
    rw [if_pos rfl, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    have h8 : ∏ k ∈ Finset.range 8, (if bitAt x k then regionMu c k γ else 1)
        = ∏ k ∈ Finset.range 8, (if bitAt x k then c k else 1) :=
      Finset.prod_congr rfl fun k hk => by rw [regionMu, if_pos (Finset.mem_range.mp hk)]
    have b8 : bitAt x 8 = x 8 := rfl
    have b9 : bitAt x 9 = x 9 := rfl
    have b10 : bitAt x 10 = x 10 := rfl
    rw [h8, b8, b9, b10]
    cases h8' : x 8 <;> cases h9' : x 9 <;> cases h10' : x 10 <;>
      simp [wordOf, regionMu, h8', h9', h10'] <;> ring
  · simp [h, regionWeight]

/-- **The verifier's product is a public weight** for the eight words of the region. -/
theorem membershipPub_hPub (hm : 22 + 2 ≤ N) (hb0 : b 0 = 1)
    (hb : ∀ d, 1 ≤ d → d < 11 → ∑ e ∈ Finset.range (d + 1), b e * B.β (d - e) = 0) :
    ∀ (γ : F) (w : (Fin (22 + 2) → Bool) → F),
      ∑ x, (pubProd b (regionMu c) 11 (22 + 2) γ).eval (B.point x) * w x
        = ∑ J : Fin 8, γ ^ (J : ℕ) * weightedSum (regionWeight c J) w :=
  hPub_of_weights B _ _ fun γ x => by
    rw [pubProd_point B b _ hm (by norm_num) hb0 hb, region_weights]

/-- Its degree is the one `knowledgeSoundness_ofCantor` asks. -/
theorem natDegree_membershipPub_le (γ : F) :
    (pubProd b (regionMu c) 11 (22 + 2) γ).natDegree ≤ 2 ^ 24 + 9 * 2 ^ 10 :=
  (natDegree_pubProd_le b _ γ).trans (by decide)

end Membership

/-! ## The theorem at the verifier's own polynomials -/

section Sizes

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {N : ℕ} (B : CantorBasis F N) (hm : 22 + 2 ≤ N)
  (σ : Equiv.Perm (Fin (22 + 2) → Bool)) (b c : ℕ → F) (hb0 : b 0 = 1)
  (hb : ∀ d, 1 ≤ d → d < 11 → ∑ e ∈ Finset.range (d + 1), b e * B.β (d - e) = 0)

/-- The parameters of `quotient::protocol`: the cells of a Cantor basis, a wiring, the eight public
words of the region, and the public weight the verifier evaluates. -/
noncomputable def membershipParams : Params F :=
  Params.ofCantor B hm σ 8 (fun J => weightedSum (regionWeight c J))
    (pubProd b (regionMu c) 11 (22 + 2)) (membershipPub_hPub B b c hm hb0 hb)

omit [Fintype F] [SampleableType F] in
theorem membershipParams_wordSum (J : Fin 8)
    (w : (membershipParams B hm σ b c hb0 hb).T × Fin 4 → F) :
    (membershipParams B hm σ b c hb0 hb).wordSum J w
      = ∑ x, regionWeight c J x * w (cantorCells (n := 22) B hm x) := by
  exact weightedSum_apply (regionWeight c J) (LinearMap.funLeft F F (cantorCells (n := 22) B hm) w)

noncomputable def membershipBounds : (membershipParams B hm σ b c hb0 hb).Bounds :=
  Params.ofCantorBounds B hm σ 8 _ _ (membershipPub_hPub B b c hm hb0 hb) _
    (natDegree_membershipPub_le b c)

open OracleComp OracleSpec in
/-- **128 bits for `quotient::protocol`.** Over a field of `2^192` elements, with the cells, the
public weight and the public words of the verifier, an adversary making `Q` queries wins with
probability at most `(Q + 3) / 2^128`. What is left of the circuit is its wiring, any permutation
of the cells. -/
theorem knowledgeSoundness_membership (hq : Fintype.card F = 2 ^ 192)
    (adv : OracleComp (ofFn (Answer (membershipParams B hm σ b c hb0 hb)
      (membershipBounds B hm σ b c hb0 hb)))
      (Proof (membershipParams B hm σ b c hb0 hb) (membershipBounds B hm σ b c hb0 hb)))
    (Q : ℕ) (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experiment adv)).run' ∅}[
        r.2 = true ∧ ¬ (membershipParams B hm σ b c hb0 hb).Sat r.1.stmt
          ((membershipParams B hm σ b c hb0 hb).cells r.1.g.1)]
      ≤ ((Q + 3 : ℕ) : ENNReal) * (((1 / 2 ^ 128 : NNReal) : NNReal) : ENNReal) :=
  knowledgeSoundness_ofCantor B hm σ _ _ (membershipPub_hPub B b c hm hb0 hb)
    (natDegree_membershipPub_le b c) hq adv Q hQ

omit [Fintype F] [SampleableType F] in
/-- The verifier's target: the statement's four words, then the words `(1, 0, 0, 0)`. -/
theorem membership_target (s : Fin 4 → F) (γ : F) :
    (membershipParams B hm σ b c hb0 hb).target ![s 0, s 1, s 2, s 3, 1, 0, 0, 0] γ
      = s 0 + γ * s 1 + γ ^ 2 * (s 2 + γ * s 3) + γ ^ 4 := by
  show ∑ J : Fin 8, γ ^ (J : ℕ) * (![s 0, s 1, s 2, s 3, 1, 0, 0, 0] : Fin 8 → F) J = _
  simp [Fin.sum_univ_eight]
  ring

end Sizes

/-! ## The constants that invert a basis -/

/-- `b 0 = 1`, `b d = sum_{e < d} b e * beta (d - e)`: what `quotient::domain::coordinates`
computes. -/
noncomputable def invSeq {F : Type} [Field F] (β : ℕ → F) : ℕ → F
  | 0 => 1
  | d + 1 => ∑ e : Fin (d + 1), invSeq β e * β (d + 1 - e)
decreasing_by exact e.2

theorem invSeq_zero {F : Type} [Field F] (β : ℕ → F) : invSeq β 0 = 1 := by rw [invSeq]

theorem invSeq_sum {F : Type} [Field F] [CharP F 2] (β : ℕ → F) (h0 : β 0 = 1) (d : ℕ)
    (hd : 1 ≤ d) : ∑ e ∈ Finset.range (d + 1), invSeq β e * β (d - e) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [Finset.sum_range_succ, Nat.sub_self, h0, mul_one]
  conv_lhs => rw [invSeq]
  rw [Fin.sum_univ_eq_sum_range (fun e => invSeq β e * β (k + 1 - e)) (k + 1)]
  exact CharTwo.add_self_eq_zero _

/-- The size of the instance (`2^22` rows, cells named by 24 bits), as an opaque proof: the
unifier need not look inside it. -/
theorem le24 : 22 + 2 ≤ 22 + 2 := Nat.le_refl _

end QuotientSecurity
