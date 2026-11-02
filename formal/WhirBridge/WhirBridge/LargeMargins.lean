/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

The list factors a protocol committing stacks of `2^24 ..= 2^28` words pays: WHIR takes no
out-of-domain sample at level 0, so a root binds to the up to `L₀` candidates of its Johnson list
(`candidates_large`) and every challenge drawn before the claims that pin a candidate is
union-bounded over the lists of the roots before it. In the style of `formal/Compose`
(`Compose/Bits.lean`, `listFactor`), this repository.
-/
import WhirBridge.LargeParams

/-!
# The margins after the lists

`largeList μ = L₀` at `μ = 24, 25, 26, 27, 28`: `9952, 7908, 6296, 4473, 3564`
(`2^13.28, 2^12.95, 2^12.62, 2^12.13, 2^11.80`), so at most `9952 < 2^13.3` per root
(`largeList_le`).

* **The batching challenge** of one opening with `J` claims escapes with probability at most
  `(J − 1) · L₀ / 2^192` (`eBatch_large`): `2^-165.4` for `J ≤ 2^14`.
* **After root 1** a challenge whose bad set has at most `d` elements per candidate is bad for
  some candidate with probability at most `L₁ · d / 2^192`; **after root 2**, at most
  `L₁ L₂ · d / 2^192` (`ncard_bad_pairs_le`, the count; `union_one_root_le`,
  `union_two_roots_le`, `union_three_roots_le`, the numbers): `L₁ ≤ 2^14`, `L₁ L₂ ≤ 9952² < 2^27`,
  `L₁ L₂ L₃ ≤ 9952³ < 2^40`, so a challenge bad on at most `2^k` values per candidate (a
  degree-`2^k` identity) keeps `178 − k`, `165 − k`, `152 − k` bits after the union over one, two,
  three roots (`149`, `136`, `123` at `k = 29`).
* `largeList_pairs`: `L₁ L₂` ranges over `[3564², 9952²] = [2^23.60, 2^26.56]` at the shapes'
  pairs.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open scoped ENNReal

/-- At most `9952` candidates per root at these shapes. -/
theorem largeList_le : ∀ μ, largeMin ≤ μ → μ ≤ largeMax → largeList μ ≤ 9952 := by
  decide +kernel

/-- `9952 ≤ 2^14`, `9952² ≤ 2^27`, `9952³ ≤ 2^40`. -/
theorem largeList_pow_le : 9952 ≤ 2 ^ 14 ∧ 9952 * 9952 ≤ 2 ^ 27 ∧ 9952 * 9952 * 9952 ≤ 2 ^ 40 := by
  decide

theorem largeList_pair_le {μ₁ μ₂ : ℕ} (h1 : largeMin ≤ μ₁) (h1' : μ₁ ≤ largeMax)
    (h2 : largeMin ≤ μ₂) (h2' : μ₂ ≤ largeMax) : largeList μ₁ * largeList μ₂ ≤ 2 ^ 27 :=
  (Nat.mul_le_mul (largeList_le μ₁ h1 h1') (largeList_le μ₂ h2 h2')).trans largeList_pow_le.2.1

theorem largeList_triple_le {μ₁ μ₂ μ₃ : ℕ} (h1 : largeMin ≤ μ₁) (h1' : μ₁ ≤ largeMax)
    (h2 : largeMin ≤ μ₂) (h2' : μ₂ ≤ largeMax) (h3 : largeMin ≤ μ₃) (h3' : μ₃ ≤ largeMax) :
    largeList μ₁ * largeList μ₂ * largeList μ₃ ≤ 2 ^ 40 :=
  (Nat.mul_le_mul (Nat.mul_le_mul (largeList_le μ₁ h1 h1') (largeList_le μ₂ h2 h2'))
    (largeList_le μ₃ h3 h3')).trans largeList_pow_le.2.2

/-! ## One opening's batching challenge -/

/-- **The batching challenge at these shapes**: `(J − 1) · L₀ / 2^192`, `L₀` the shape's own
list (sharper than `eBatch_le`'s `2^18`). -/
theorem eBatch_large {μ : ℕ} (h1 : largeMin ≤ μ) (h2 : μ ≤ largeMax) (J : ℕ) :
    eBatch J (code₀ μ logInvRate) ≤ (((J - 1) * largeList μ : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by
  rw [eBatch, card_E_ennreal]
  exact ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.mul_le_mul_left _ (listMax_large h1 h2))) _

/-- With at most `2^14` claims in the opening: at most `2^-164`. -/
theorem eBatch_large_le {μ : ℕ} (h1 : largeMin ≤ μ) (h2 : μ ≤ largeMax) {J : ℕ}
    (hJ : J ≤ 2 ^ 14) : eBatch J (code₀ μ logInvRate) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 := by
  refine (eBatch_large h1 h2 J).trans ?_
  have h : (J - 1) * largeList μ ≤ 2 ^ 28 :=
    calc (J - 1) * largeList μ ≤ 2 ^ 14 * 2 ^ 14 :=
          Nat.mul_le_mul (by omega) ((largeList_le μ h1 h2).trans largeList_pow_le.1)
      _ = 2 ^ 28 := by norm_num
  calc ((((J - 1) * largeList μ : ℕ) : ℝ≥0∞)) / (2 : ℝ≥0∞) ^ 192
      ≤ ((2 ^ 28 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ 164 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, show (192 : ℕ) = 28 + 164 from rfl, two_pow_div_two_pow]

/-! ## The union over the lists -/

/-- **The union bound over two roots' lists, as a count**: if for every pair of candidates (`q₁`
of root 1's list `C₁`, `q₂` of root 2's `C₂`) at most `d` challenges are bad, then at most
`|C₁| · |C₂| · d` challenges are bad for some pair. -/
theorem ncard_bad_pairs_le {α β γ : Type} {C₁ : Set α} {C₂ : Set β} (h₁ : C₁.Finite)
    (h₂ : C₂.Finite) (B : α → β → Set γ) {d : ℕ}
    (hB : ∀ q₁ ∈ C₁, ∀ q₂ ∈ C₂, (B q₁ q₂).Finite ∧ (B q₁ q₂).ncard ≤ d) :
    {x | ∃ q₁ ∈ C₁, ∃ q₂ ∈ C₂, x ∈ B q₁ q₂}.ncard ≤ C₁.ncard * C₂.ncard * d := by
  classical
  let F : α × β → Finset γ := fun p ↦
    if h : (B p.1 p.2).Finite then h.toFinset else ∅
  let S : Finset γ := (h₁.toFinset ×ˢ h₂.toFinset).biUnion F
  have hsub : {x | ∃ q₁ ∈ C₁, ∃ q₂ ∈ C₂, x ∈ B q₁ q₂} ⊆ (S : Set γ) := by
    rintro x ⟨q₁, hq₁, q₂, hq₂, hx⟩
    simp only [S, Finset.coe_biUnion, Finset.coe_product, Set.Finite.coe_toFinset, Set.mem_iUnion,
      Set.mem_prod, exists_prop, Prod.exists]
    refine ⟨q₁, q₂, ⟨hq₁, hq₂⟩, ?_⟩
    simp only [F, dif_pos (hB q₁ hq₁ q₂ hq₂).1, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hx
  have hcard : ∀ p ∈ h₁.toFinset ×ˢ h₂.toFinset, (F p).card ≤ d := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    have hb := hB p.1 ((Set.Finite.mem_toFinset h₁).1 hp1) p.2 ((Set.Finite.mem_toFinset h₂).1 hp2)
    simp only [F, dif_pos hb.1]
    rw [← Set.ncard_eq_toFinset_card _ hb.1]
    exact hb.2
  calc {x | ∃ q₁ ∈ C₁, ∃ q₂ ∈ C₂, x ∈ B q₁ q₂}.ncard ≤ (S : Set γ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet S)
    _ = S.card := Set.ncard_coe_finset S
    _ ≤ ∑ p ∈ h₁.toFinset ×ˢ h₂.toFinset, (F p).card := Finset.card_biUnion_le
    _ ≤ (h₁.toFinset ×ˢ h₂.toFinset).card * d := Finset.sum_le_card_nsmul _ _ _ hcard
    _ = C₁.ncard * C₂.ncard * d := by
        rw [Finset.card_product, ← Set.ncard_eq_toFinset_card _ h₁,
          ← Set.ncard_eq_toFinset_card _ h₂]

/-- **The candidates of two roots at these shapes**: at most `L₁ L₂ · d` challenges are bad for
some pair of candidates, `L_i = largeList μ_i`. -/
theorem ncard_bad_candidates_le {μ₁ μ₂ : ℕ} (h1 : largeMin ≤ μ₁) (h1' : μ₁ ≤ largeMax)
    (h2 : largeMin ≤ μ₂) (h2' : μ₂ ≤ largeMax) (W₁ W₂ : Word) {γ : Type}
    (B : Column μ₁ → Column μ₂ → Set γ) {d : ℕ}
    (hB : ∀ q₁ q₂, (B q₁ q₂).Finite ∧ (B q₁ q₂).ncard ≤ d) :
    {x | ∃ q₁ ∈ Candidates μ₁ logInvRate (code₀ μ₁ logInvRate).thr W₁,
        ∃ q₂ ∈ Candidates μ₂ logInvRate (code₀ μ₂ logInvRate).thr W₂, x ∈ B q₁ q₂}.ncard ≤
      largeList μ₁ * largeList μ₂ * d := by
  refine (ncard_bad_pairs_le (candidates_large h1 h1' W₁).1 (candidates_large h2 h2' W₂).1 B
    fun q₁ _ q₂ _ ↦ hB q₁ q₂).trans ?_
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul (candidates_large h1 h1' W₁).2 (candidates_large h2 h2' W₂).2)

/-! ## The numbers -/

/-- `n / 2^192 ≤ 2^-(192 − m)` for `n ≤ 2^m`. -/
theorem div_two_pow_192_le {n m : ℕ} (hn : n ≤ 2 ^ m) (hm : m ≤ 192) :
    ((n : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ (192 - m) := by
  calc ((n : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 ≤ ((2 ^ m : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by
        gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ (192 - m) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (192 : ℕ) = m + (192 - m) by omega,
          two_pow_div_two_pow, Nat.add_sub_cancel_left]

/-- **After one root**: a challenge bad for at most `d ≤ 2^k` values per candidate is bad for some
candidate with probability at most `L₁ d / 2^192 ≤ 2^-(178 − k)`. -/
theorem union_one_root_le {μ₁ : ℕ} (h1 : largeMin ≤ μ₁) (h1' : μ₁ ≤ largeMax) {d k : ℕ}
    (hd : d ≤ 2 ^ k) (hk : k ≤ 178) :
    ((largeList μ₁ * d : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ (178 - k) := by
  have h : largeList μ₁ * d ≤ 2 ^ (14 + k) := by
    rw [pow_add]
    exact Nat.mul_le_mul ((largeList_le μ₁ h1 h1').trans largeList_pow_le.1) hd
  have := div_two_pow_192_le h (by omega)
  rwa [show 192 - (14 + k) = 178 - k by omega] at this

/-- **After two roots**: `L₁ L₂ d / 2^192 ≤ 2^-(165 − k)` for `d ≤ 2^k` (`L₁ L₂ ≤ 9952² < 2^27`). -/
theorem union_two_roots_le {μ₁ μ₂ : ℕ} (h1 : largeMin ≤ μ₁) (h1' : μ₁ ≤ largeMax)
    (h2 : largeMin ≤ μ₂) (h2' : μ₂ ≤ largeMax) {d k : ℕ} (hd : d ≤ 2 ^ k) (hk : k ≤ 165) :
    ((largeList μ₁ * largeList μ₂ * d : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 ≤
      (2 : ℝ≥0∞)⁻¹ ^ (165 - k) := by
  have h : largeList μ₁ * largeList μ₂ * d ≤ 2 ^ (27 + k) := by
    rw [pow_add]
    exact Nat.mul_le_mul (largeList_pair_le h1 h1' h2 h2') hd
  have := div_two_pow_192_le h (by omega)
  rwa [show 192 - (27 + k) = 165 - k by omega] at this

/-- **After three roots**: `L₁ L₂ L₃ d / 2^192 ≤ 2^-(152 − k)` (`L₁ L₂ L₃ ≤ 9952³ < 2^40`). -/
theorem union_three_roots_le {μ₁ μ₂ μ₃ : ℕ} (h1 : largeMin ≤ μ₁) (h1' : μ₁ ≤ largeMax)
    (h2 : largeMin ≤ μ₂) (h2' : μ₂ ≤ largeMax) (h3 : largeMin ≤ μ₃) (h3' : μ₃ ≤ largeMax)
    {d k : ℕ} (hd : d ≤ 2 ^ k) (hk : k ≤ 152) :
    ((largeList μ₁ * largeList μ₂ * largeList μ₃ * d : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 ≤
      (2 : ℝ≥0∞)⁻¹ ^ (152 - k) := by
  have h : largeList μ₁ * largeList μ₂ * largeList μ₃ * d ≤ 2 ^ (40 + k) := by
    rw [pow_add]
    exact Nat.mul_le_mul (largeList_triple_le h1 h1' h2 h2' h3 h3') hd
  have := div_two_pow_192_le h (by omega)
  rwa [show 192 - (40 + k) = 152 - k by omega] at this

/-- The products of the lists at every pair of shapes (`L₁ L₂`, decided): from `3564² =
12,702,096` (`2^23.60`, two roots of `2^28`) to `9952² = 99,042,304` (`2^26.56`, two of
`2^24`). -/
theorem largeList_pairs :
    ∀ μ₁, largeMin ≤ μ₁ → μ₁ ≤ largeMax → ∀ μ₂, largeMin ≤ μ₂ → μ₂ ≤ largeMax →
      12702096 ≤ largeList μ₁ * largeList μ₂ ∧ largeList μ₁ * largeList μ₂ ≤ 99042304 := by
  decide +kernel

end WhirBridge
