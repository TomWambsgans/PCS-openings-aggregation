-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Joint

/-!
# The challenges at which the simulator's tables are built

The simulator's tables (`Builder.lean`) are solved for on a few fixed entries; the solve needs
(`RankGood`) `ρ ≠ 1`, and `ρ` or the row of `t` (`t⁴ + t`, `rowOf`) outside `K`: the witness claim's
weights there are `R·(1, ρ, ρ²)` or, when `ρ ∈ K`, `R'·(1, s, s²)` with `s` the row of `t`.

* **`goodB`**: the joint model's good challenges (`good`) at which, also, `RankGood` holds;
* `card_row_mem_le`: at most `4|K|` points have their row in `K` (`t⁴ + t = a` has at most four roots);
* `prob_not_rankGood_le`: for uniform challenges `RankGood` fails with probability at most
  `(|E| + 4|K|²)/|E|²` (`ρ = 1`, or `ρ` and the row of `t`, independent, both in `K`);
* **`joint_hgoodB_bits`**: `goodB` fails with probability at most `2^-165` at our sizes: F1's
  `3·2^24/2^192 < 2^-166`, each opening's `< 2^-188`, `RankGood`'s `2^-192 + 2^-254 < 2^-188`, the
  same bound as `joint_hgood_bits`'s.
-/

open OracleComp Polynomial Module QuotientSecurity QuotientSecurity.Hiding Finset
open QuotientZk.Joint

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]

/-- **The builder's challenges** (`Builder.lean`): `ρ ≠ 1`, and `ρ` or the row of `t` outside `K`. -/
def RankGood (t ρ : E) : Prop :=
  ρ ≠ 1 ∧ (ρ ∈ Set.range (algebraMap K E) → rowOf t ∉ Set.range (algebraMap K E))

section Good

variable {Γ₁ Γ₂ Γw : Type} [DecidableEq E] [CharP E 2] [Fintype E]

/-- **The good challenges with the builder's**: the joint model's (`good`) and `RankGood`. -/
def goodB (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (c : Chal E Γ₁ Γ₂ Γw) : Prop :=
  good P gK van c ∧ RankGood (K := K) c.1.1.2 c.1.2

end Good

/-! ## How often `RankGood` fails -/

section Prob

variable [Fintype K] [Fintype E] [DecidableEq E]

open Classical in
/-- **At most `4|K|` points have their row in `K`**: `t⁴ + t = a` has at most four roots. -/
theorem card_row_mem_le :
    (univ.filter fun t : E => rowOf t ∈ Set.range (algebraMap K E)).card ≤ 4 * Fintype.card K := by
  set R : Finset E := univ.image (algebraMap K E)
  have hdeg : ∀ a : E, (X ^ 4 + (X - C a) : E[X]).natDegree = 4 := fun a => by
    rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_sub_C, degree_X_pow]; norm_num),
      natDegree_X_pow]
  have hne : ∀ a : E, (X ^ 4 + (X - C a) : E[X]) ≠ 0 := fun a h => by
    have := hdeg a
    rw [h, natDegree_zero] at this
    exact absurd this (by norm_num)
  have hsub : (univ.filter fun t : E => rowOf t ∈ Set.range (algebraMap K E)) ⊆
      R.biUnion fun a => (X ^ 4 + (X - C a) : E[X]).roots.toFinset := by
    intro t ht
    obtain ⟨k, hk⟩ := (mem_filter.mp ht).2
    refine mem_biUnion.mpr ⟨algebraMap K E k, mem_image_of_mem _ (mem_univ k), ?_⟩
    rw [Multiset.mem_toFinset, mem_roots (hne _), IsRoot.def, eval_add, eval_sub, eval_pow,
      eval_X, eval_C, hk]
    simp [rowOf]
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ a ∈ R, (X ^ 4 + (X - C a) : E[X]).roots.toFinset.card := card_biUnion_le
    _ ≤ ∑ _a ∈ R, 4 := sum_le_sum fun a _ =>
        (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (hdeg a).le)
    _ = R.card * 4 := by rw [sum_const, smul_eq_mul]
    _ ≤ 4 * Fintype.card K := by
        rw [mul_comm]
        gcongr
        exact card_image_le.trans_eq (card_univ)

variable [SampleableType E] {Γ₁ Γ₂ Γw : Type} [SampleableType Γ₁] [SampleableType Γ₂]
  [SampleableType Γw]

open Classical in
/-- **`RankGood` fails rarely**: for uniform challenges, with probability at most
`(|E| + 4|K|²)/|E|²` (`ρ = 1`; or `ρ ∈ K` and the row of `t` in `K`, independently). -/
theorem prob_not_rankGood_le :
    Pr{let c ← $ᵗ (Chal E Γ₁ Γ₂ Γw)}[¬ RankGood (K := K) c.1.1.2 c.1.2] ≤
      ((Fintype.card E + 4 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
        ((Fintype.card E ^ 2 : ℕ) : ENNReal) := by
  refine le_trans (le_of_eq (prEvent_uniform_fst (A := ((E × E × E) × E) × E)
    (fun x => ¬ RankGood (K := K) x.1.2 x.2))) ?_
  rw [SampleableType.prEvent_uniformSample]
  set R : Finset E := univ.image (algebraMap K E)
  set T : Finset E := univ.filter fun t : E => rowOf t ∈ Set.range (algebraMap K E)
  have hR : ∀ x ∈ Set.range (algebraMap K E), x ∈ R := by
    rintro _ ⟨k, rfl⟩
    exact mem_image_of_mem _ (mem_univ k)
  have hsub : (univ.filter fun x : ((E × E × E) × E) × E => ¬ RankGood (K := K) x.1.2 x.2) ⊆
      (univ ×ˢ ({1} : Finset E)) ∪ ((univ ×ˢ T) ×ˢ R) := by
    intro x hx
    have h := (mem_filter.mp hx).2
    unfold RankGood at h
    by_cases h1 : x.2 = 1
    · exact mem_union_left _ (mem_product.mpr ⟨mem_univ _, mem_singleton.mpr h1⟩)
    · have h2 : x.2 ∈ Set.range (algebraMap K E) ∧ rowOf x.1.2 ∈ Set.range (algebraMap K E) := by
        by_contra hc
        exact h ⟨h1, fun hρ hrow => hc ⟨hρ, hrow⟩⟩
      exact mem_union_right _ (mem_product.mpr ⟨mem_product.mpr ⟨mem_univ _,
        mem_filter.mpr ⟨mem_univ _, h2.2⟩⟩, hR _ h2.1⟩)
  have hle := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_product, card_product, card_product, card_univ, card_univ, card_singleton] at hle
  have hT := card_row_mem_le (K := K) (E := E)
  have hRc : R.card ≤ Fintype.card K := card_image_le.trans_eq card_univ
  have hE : 0 < Fintype.card E := Fintype.card_pos
  have hcard : Fintype.card (((E × E × E) × E) × E) = Fintype.card E ^ 5 := by
    simp only [Fintype.card_prod]
    ring
  have hcard3 : Fintype.card (E × E × E) = Fintype.card E ^ 3 := by
    simp only [Fintype.card_prod]
    ring
  have hcard4 : Fintype.card ((E × E × E) × E) = Fintype.card E ^ 4 := by
    simp only [Fintype.card_prod]
    ring
  rw [hcard]
  rw [hcard4, hcard3] at hle
  refine HiddenLayout.natCast_div_le_natCast_div (Nat.pow_pos hE) (Nat.pow_pos hE) ?_
  calc (univ.filter fun x : ((E × E × E) × E) × E => ¬ RankGood (K := K) x.1.2 x.2).card *
        Fintype.card E ^ 2
      ≤ (Fintype.card E ^ 4 * 1 + Fintype.card E ^ 3 * T.card * R.card) * Fintype.card E ^ 2 :=
        Nat.mul_le_mul_right _ hle
    _ ≤ (Fintype.card E ^ 4 * 1 + Fintype.card E ^ 3 * (4 * Fintype.card K) * Fintype.card K) *
          Fintype.card E ^ 2 := by gcongr
    _ = (Fintype.card E + 4 * Fintype.card K ^ 2) * Fintype.card E ^ 5 := by ring

variable [CharP E 2] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]
  [Fintype Γ₁] [Fintype Γ₂]

/-- **`εhv` with the builder's challenges** at our sizes: `goodB` fails with probability at most
`2^-165` (`joint_hgood`'s `3·2^24/2^192 + 2·(13·2^-192 + 3·2^-256)`, and `RankGood`'s
`2^-192 + 2^-254`). -/
theorem joint_hgoodB_bits (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22) :
    Pr{let c ← $ᵗ (Chal E Γ₁ Γ₂ Γw)}[¬ goodB P gK van c] ≤ 1 / 2 ^ 165 := by
  refine (prEvent_not_and_le _ _ _).trans ?_
  refine (add_le_add (joint_hgood P gK van hvan0) (prob_not_rankGood_le (K := K))).trans ?_
  have ho : ((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
        ((Fintype.card E ^ 2 : ℕ) : ENNReal) + 1 / (Fintype.card E : ENNReal) ≤ 1 / 2 ^ 188 := by
    rw [hq, hK]
    exact Gadget.goodCh_bound_le
  have hr : ((Fintype.card E + 4 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
      ((Fintype.card E ^ 2 : ℕ) : ENNReal) ≤ 1 / 2 ^ 188 := by
    rw [hq, hK]
    have h := HiddenLayout.natCast_div_le_natCast_div (a := 2 ^ 192 + 4 * (2 ^ 64) ^ 2)
      (b := (2 ^ 192) ^ 2) (c := 1) (d := 2 ^ 188) (by positivity) (by positivity) (by norm_num)
    convert h using 1
    norm_num
  have hz := zkError_le_166 P hq hN van hdeg
  have h3 : (1 : ENNReal) / 2 ^ 188 + 1 / 2 ^ 188 + 1 / 2 ^ 188 ≤ 1 / 2 ^ 166 := by
    rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
    have h := HiddenLayout.natCast_div_le_natCast_div (a := 3) (b := 2 ^ 188) (c := 1)
      (d := 2 ^ 166) (by positivity) (by positivity) (by norm_num)
    convert h using 1 <;> norm_num
  have h1 : (1 : ENNReal) / 2 ^ 166 + 1 / 2 ^ 166 ≤ 1 / 2 ^ 165 := by
    rw [ENNReal.div_add_div_same]
    have h := HiddenLayout.natCast_div_le_natCast_div (a := 2) (b := 2 ^ 166) (c := 1)
      (d := 2 ^ 165) (by positivity) (by positivity) (by norm_num)
    convert h using 1 <;> norm_num
  calc _ ≤ (1 : ENNReal) / 2 ^ 166 + (1 / 2 ^ 188 + 1 / 2 ^ 188) + 1 / 2 ^ 188 := by gcongr
    _ = 1 / 2 ^ 166 + (1 / 2 ^ 188 + 1 / 2 ^ 188 + 1 / 2 ^ 188) := by rw [add_assoc]
    _ ≤ 1 / 2 ^ 166 + 1 / 2 ^ 166 := by gcongr
    _ ≤ 1 / 2 ^ 165 := h1

end Prob

end QuotientZk.Instance
