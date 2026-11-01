-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Span

/-!
# Condition (S) with four random lanes: a bound near `2^-127`

`Span.card_not_linearIndependent_le` gets `|K|^2/|E|` (`2^-128 · 2^64`) from one fold weight
falling into the plane of two others. With a fourth lane, (S) fails only if **two** weights fall
into that plane, and they do so through two different coordinates `a` and `c`, independently:
`(|K|^2/|E|)^2`. The other ways to fail are a coordinate in `{0, 1}` or the plane itself being a
line (two weights `K`-proportional, `|K|/|E|`). `card_not_span_four_le`: at most
`((2n + |K| + 1)·|E| + |K|^4)·|E|^(n-2)` challenges `φ ∈ E^n`, a fraction below
`(2n + |K| + 1)/|E| + |K|^4/|E|^2`, that is `2^-128 + 2^-128 + 2n·2^-192` at `|K| = 2^64`,
`|E| = 2^192`.

The lanes `r0, rA, rB, rC` need: a coordinate `b` where `r0, rB` differ; a coordinate `a` where
`rA` alone differs from the others; a coordinate `c ≠ a` where `rC` alone does.
-/

namespace QuotientSecurity.Hiding

open Finset

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E] [Fintype K] [Fintype E] [DecidableEq E]

/-- The double count behind `card_mul_le_of_fiber`. -/
theorem card_mul_le_sum_fiber {n : ℕ} (a : Fin n) (S : Finset (Fin n → E)) :
    S.card * Fintype.card E ≤
      ∑ φ : Fin n → E, (univ.filter fun t => Function.update φ a t ∈ S).card := by
  classical
  set P := univ.filter fun p : (Fin n → E) × E => Function.update p.1 a p.2 ∈ S
  have hinj : (S ×ˢ (univ : Finset E)).card ≤ P.card := by
    refine Finset.card_le_card_of_injOn (fun q => (Function.update q.1 a q.2, q.1 a)) ?_ ?_
    · intro q hq
      obtain ⟨hq1, -⟩ := mem_product.mp hq
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      simpa using hq1
    · intro q _ q' _ hqq
      simp only [Prod.mk.injEq] at hqq
      obtain ⟨h1, h2⟩ := hqq
      have e1 : q.1 = q'.1 := by
        have := congrArg (fun φ => Function.update φ a (q.1 a)) h1
        simp only [Function.update_idem, Function.update_eq_self] at this
        rw [this, h2, Function.update_eq_self]
      have e2 : q.2 = q'.2 := by
        have := congrFun h1 a
        simpa using this
      exact Prod.ext e1 e2
  have hP : P.card = ∑ φ : Fin n → E, (univ.filter fun t => Function.update φ a t ∈ S).card := by
    rw [card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun φ _ => ?_
    rw [card_filter]
  rw [card_product, card_univ] at hinj
  exact hP ▸ hinj

/-- Challenges with a coordinate in `{0, 1}`. -/
theorem card_not_avoid_mul_le {n : ℕ} :
    (univ.filter fun φ : Fin n → E => ¬ ∀ i, φ i ≠ 0 ∧ φ i ≠ 1).card * Fintype.card E
      ≤ (2 * n) * Fintype.card E ^ n := by
  classical
  have hZsub : (univ.filter fun φ : Fin n → E => ¬ ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) ⊆
      univ.biUnion fun i : Fin n => univ.filter fun φ : Fin n → E => φ i = 0 ∨ φ i = 1 := by
    intro φ hφ
    have := (mem_filter.mp hφ).2
    simp only [not_forall, not_and_or, not_not] at this
    obtain ⟨i, hi⟩ := this
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have hi : ∀ i : Fin n, (univ.filter fun φ : Fin n → E => φ i = 0 ∨ φ i = 1).card *
      Fintype.card E ≤ 2 * Fintype.card E ^ n := by
    intro i
    refine card_mul_le_of_fiber i _ 2 fun φ => ?_
    calc (univ.filter fun t => Function.update φ i t ∈
          univ.filter fun φ : Fin n → E => φ i = 0 ∨ φ i = 1).card
        = (univ.filter fun t : E => t = 0 ∨ t = 1).card := by
          congr 1
          ext t
          simp
      _ ≤ ({0, 1} : Finset E).card := by
          refine card_le_card fun t ht => ?_
          rcases (mem_filter.mp ht).2 with h | h <;> simp [h]
      _ ≤ 2 := card_le_two
  calc _ ≤ (univ.biUnion fun i : Fin n =>
          univ.filter fun φ : Fin n → E => φ i = 0 ∨ φ i = 1).card * Fintype.card E :=
        Nat.mul_le_mul_right _ (card_le_card hZsub)
    _ ≤ (∑ i : Fin n, (univ.filter fun φ : Fin n → E => φ i = 0 ∨ φ i = 1).card) *
          Fintype.card E := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ i : Fin n, (univ.filter fun φ : Fin n → E => φ i = 0 ∨ φ i = 1).card *
          Fintype.card E := sum_mul _ _ _
    _ ≤ ∑ _i : Fin n, 2 * Fintype.card E ^ n := sum_le_sum fun i _ => hi i
    _ = (2 * n) * Fintype.card E ^ n := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        ring

/-- The ratio of the two factors of one coordinate. -/
noncomputable def ratioF (u : Bool) (t : E) : E := eqFactor (!u) t / eqFactor u t

theorem eqFactor_ne_zero (u : Bool) {t : E} (h0 : t ≠ 0) (h1 : t ≠ 1) : eqFactor u t ≠ 0 := by
  cases u
  · exact sub_ne_zero.mpr (Ne.symm h1)
  · exact h0

theorem ratioF_injOn (u : Bool) : Set.InjOn (ratioF (E := E) u) {t | t ≠ 0 ∧ t ≠ 1} := by
  intro t ht s hs h
  have ht1 : (1 : E) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht.2)
  have hs1 : (1 : E) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2)
  cases u
  · simp only [ratioF, eqFactor, Bool.not_false, ite_true, Bool.false_eq_true, ite_false] at h
    rw [div_eq_div_iff ht1 hs1] at h
    linear_combination h
  · simp only [ratioF, eqFactor, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at h
    rw [div_eq_div_iff ht.1 hs.1] at h
    linear_combination -h

/-- Membership in the span of a pair, by coefficients. -/
theorem mem_span_range_pair {x y v : E} :
    v ∈ Submodule.span K (Set.range ![x, y]) ↔ ∃ α β : K, α • x + β • y = v := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g 0, g 1, by simpa [Fin.sum_univ_two] using hg⟩
  · rintro ⟨α, β, h⟩
    exact ⟨![α, β], by simpa [Fin.sum_univ_two] using h⟩

open Classical in
/-- At most `|K|^2` values `t ∉ {0, 1}` put `ratioF u t · Q` in a plane. -/
theorem card_ratio_mem_le (u : Bool) (Q : E) (hQ : Q ≠ 0) (x y : E)
    (hind : LinearIndependent K ![x, y]) :
    (univ.filter fun t : E => (t ≠ 0 ∧ t ≠ 1) ∧
        ratioF u t * Q ∈ Submodule.span K (Set.range ![x, y])).card ≤ Fintype.card K ^ 2 := by
  classical
  set V := Submodule.span K (Set.range ![x, y])
  have hT : (univ.filter fun s : E => Q * s ∈ V).card = Fintype.card K ^ 2 := by
    rw [card_filter_mul_mem Q hQ V, card_filter_mem_span ![x, y] hind]
  rw [← hT]
  refine Finset.card_le_card_of_injOn (ratioF u) ?_ ?_
  · intro t ht
    obtain ⟨-, -, hm⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rwa [mul_comm]
  · intro t ht s hs h
    exact ratioF_injOn u (mem_filter.mp ht).2.1 (mem_filter.mp hs).2.1 h

/-- `eq` with the two coordinates `a, c` split off. -/
theorem eqW_split {n : ℕ} (φ : Fin n → E) (r : Fin n → Bool) {a c : Fin n} (hac : a ≠ c) :
    eqW φ r = eqFactor (r a) (φ a) * eqFactor (r c) (φ c) *
      ∏ i ∈ (univ.erase a).erase c, eqFactor (r i) (φ i) := by
  have hc : c ∈ univ.erase a := mem_erase.mpr ⟨Ne.symm hac, mem_univ _⟩
  rw [eqW_eq_mul_prod_erase φ r a, ← mul_prod_erase _ _ hc, mul_assoc]

open Classical in
/-- **Condition (S) fails rarely, four lanes.** -/
theorem card_not_span_four_le [FiniteDimensional K E] (h3 : Module.finrank K E = 3) {n : ℕ}
    (r0 rA rB rC : Fin n → Bool) (a b c : Fin n) (hac : a ≠ c) (hb : r0 b ≠ rB b)
    (haB : rB a = r0 a) (haC : rC a = r0 a) (haA : rA a = !r0 a)
    (hcB : rB c = r0 c) (hcA : rA c = r0 c) (hcC : rC c = !r0 c) :
    (univ.filter fun φ : Fin n → E =>
        Submodule.span K (Set.range ![eqW φ r0, eqW φ rA, eqW φ rB, eqW φ rC]) ≠ ⊤).card
        * Fintype.card E ^ 2
      ≤ ((2 * n + Fintype.card K + 1) * Fintype.card E + Fintype.card K ^ 4) *
          Fintype.card E ^ n := by
  set avoid : (Fin n → E) → Prop := fun φ => ∀ i, φ i ≠ 0 ∧ φ i ≠ 1 with havoid
  set Q : (Fin n → Bool) → (Fin n → E) → E :=
    fun r φ => ∏ i ∈ (univ.erase a).erase c, eqFactor (r i) (φ i) with hQdef
  set V : (Fin n → E) → Submodule K E :=
    fun φ => Submodule.span K (Set.range ![Q r0 φ, Q rB φ]) with hVdef
  set PA : (Fin n → E) → Prop := fun φ => ratioF (r0 a) (φ a) * Q rA φ ∈ V φ with hPA
  set PC : (Fin n → E) → Prop := fun φ => ratioF (r0 c) (φ c) * Q rC φ ∈ V φ with hPC
  set Z := univ.filter fun φ : Fin n → E => ¬ avoid φ
  set B0 := univ.filter fun φ : Fin n → E =>
    avoid φ ∧ ¬ LinearIndependent K ![eqW φ r0, eqW φ rB]
  set B2 := univ.filter fun φ : Fin n → E =>
    avoid φ ∧ LinearIndependent K ![Q r0 φ, Q rB φ] ∧ PA φ ∧ PC φ
  -- The factors off `a, c` do not see `a` or `c`.
  have hQa : ∀ r φ t, Q r (Function.update φ a t) = Q r φ := fun r φ t =>
    prod_erase_update _ φ r a (by simp) t
  have hQc : ∀ r φ t, Q r (Function.update φ c t) = Q r φ := fun r φ t =>
    prod_erase_update _ φ r c (by simp) t
  have hQne : ∀ r φ, (∀ i, i ≠ a → i ≠ c → φ i ≠ 0 ∧ φ i ≠ 1) → Q r φ ≠ 0 := by
    intro r φ h
    refine prod_ne_zero_iff.mpr fun i hi => ?_
    obtain ⟨hic, hi'⟩ := mem_erase.mp hi
    obtain ⟨hia, -⟩ := mem_erase.mp hi'
    exact eqFactor_ne_zero _ (h i hia hic).1 (h i hia hic).2
  -- Where every coordinate avoids `0, 1`, the four weights are the `Q`s times nonzero factors.
  have hsub : (univ.filter fun φ : Fin n → E =>
      Submodule.span K (Set.range ![eqW φ r0, eqW φ rA, eqW φ rB, eqW φ rC]) ≠ ⊤)
      ⊆ Z ∪ B0 ∪ B2 := by
    intro φ hφ
    have hspan := (mem_filter.mp hφ).2
    by_cases hav : avoid φ
    swap
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hav⟩))
    by_cases h0B : LinearIndependent K ![eqW φ r0, eqW φ rB]
    swap
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hav, h0B⟩))
    refine mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hav, ?_, ?_, ?_⟩)
    all_goals
      set ga := eqFactor (r0 a) (φ a)
      set gc := eqFactor (r0 c) (φ c)
      have hga : ga ≠ 0 := eqFactor_ne_zero _ (hav a).1 (hav a).2
      have hgc : gc ≠ 0 := eqFactor_ne_zero _ (hav c).1 (hav c).2
      have e0 : eqW φ r0 = ga * gc * Q r0 φ := eqW_split φ r0 hac
      have eB : eqW φ rB = ga * gc * Q rB φ := by rw [eqW_split φ rB hac, haB, hcB]
    · -- the plane of `Q r0, Q rB` is a plane
      rw [LinearIndependent.pair_iff] at h0B ⊢
      intro s t hst
      refine h0B s t ?_
      rw [e0, eB, Algebra.smul_def, Algebra.smul_def]
      rw [Algebra.smul_def, Algebra.smul_def] at hst
      linear_combination (ga * gc) * hst
    -- if a fourth weight leaves the plane of `r0, rB`, three weights span `E`
    all_goals
      have hout : ∀ v ∈ Set.range ![eqW φ r0, eqW φ rA, eqW φ rB, eqW φ rC],
          v ∈ Submodule.span K (Set.range ![eqW φ r0, eqW φ rB]) := by
        intro v hv
        by_contra hnot
        apply hspan
        have hli : LinearIndependent K (Fin.cons v ![eqW φ r0, eqW φ rB] : Fin 3 → E) :=
          linearIndependent_finCons.mpr ⟨h0B, hnot⟩
        have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h3])
        rw [eq_top_iff, ← htop]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        obtain ⟨j, rfl⟩ := hv
        fin_cases i
        · exact ⟨j, rfl⟩
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
    · -- `rA` in the plane: `PA`
      obtain ⟨α, β, hαβ⟩ := mem_span_range_pair.mp (hout (eqW φ rA) ⟨1, rfl⟩)
      have eA : eqW φ rA = eqFactor (!r0 a) (φ a) * gc * Q rA φ := by
        rw [eqW_split φ rA hac, haA, hcA]
      refine mem_span_range_pair.mpr ⟨α, β, ?_⟩
      rw [e0, eB, eA, Algebra.smul_def, Algebra.smul_def] at hαβ
      rw [Algebra.smul_def, Algebra.smul_def]
      show _ = eqFactor (!r0 a) (φ a) / ga * Q rA φ
      apply mul_left_cancel₀ (mul_ne_zero hga hgc)
      rw [show ga * gc * (eqFactor (!r0 a) (φ a) / ga * Q rA φ)
          = eqFactor (!r0 a) (φ a) * gc * Q rA φ by field_simp]
      linear_combination hαβ
    · -- `rC` in the plane: `PC`
      obtain ⟨α, β, hαβ⟩ := mem_span_range_pair.mp (hout (eqW φ rC) ⟨3, rfl⟩)
      have eC : eqW φ rC = ga * eqFactor (!r0 c) (φ c) * Q rC φ := by
        rw [eqW_split φ rC hac, haC, hcC]
      refine mem_span_range_pair.mpr ⟨α, β, ?_⟩
      rw [e0, eB, eC, Algebra.smul_def, Algebra.smul_def] at hαβ
      rw [Algebra.smul_def, Algebra.smul_def]
      show _ = eqFactor (!r0 c) (φ c) / gc * Q rC φ
      apply mul_left_cancel₀ (mul_ne_zero hga hgc)
      rw [show ga * gc * (eqFactor (!r0 c) (φ c) / gc * Q rC φ)
          = ga * eqFactor (!r0 c) (φ c) * Q rC φ by field_simp]
      linear_combination hαβ
  -- `Z`
  have hZ : Z.card * Fintype.card E ≤ (2 * n) * Fintype.card E ^ n := card_not_avoid_mul_le
  -- `B0`: the ratio of `r0` and `rB` in `K`, through the coordinate `b`.
  have hB0 : B0.card * Fintype.card E ≤ (Fintype.card K + 1) * Fintype.card E ^ n := by
    refine card_mul_le_of_fiber b _ _ fun φ => ?_
    set P : (Fin n → Bool) → E := fun r => ∏ i ∈ univ.erase b, eqFactor (r i) (φ i)
    have hP : ∀ r t, eqW (Function.update φ b t) r = eqFactor (r b) t * P r := by
      intro r t
      rw [eqW_eq_mul_prod_erase _ r b, Function.update_self]
      exact congrArg _ (prod_erase_update _ φ r b (by simp) t)
    by_cases hav : ∀ i, i ≠ b → φ i ≠ 0 ∧ φ i ≠ 1
    · have hPne : ∀ r, P r ≠ 0 := fun r => prod_ne_zero_iff.mpr fun i hi =>
        eqFactor_ne_zero _ (hav i (mem_erase.mp hi).1).1 (hav i (mem_erase.mp hi).1).2
      calc (univ.filter fun t => Function.update φ b t ∈ B0).card
          ≤ (univ.filter fun t : E => ¬ LinearIndependent K
              ![eqFactor (r0 b) t * P r0, eqFactor (rB b) t * P rB]).card := by
            refine card_le_card fun t ht => ?_
            have := (mem_filter.mp (mem_filter.mp ht).2).2.2
            rw [hP, hP] at this
            exact mem_filter.mpr ⟨mem_univ _, this⟩
        _ ≤ Fintype.card K + 1 := card_bad_pair' _ _ hb _ _ (hPne r0) (hPne rB)
    · push Not at hav
      obtain ⟨i, hib, hi⟩ := hav
      have : (univ.filter fun t => Function.update φ b t ∈ B0) = ∅ := by
        refine filter_eq_empty_iff.mpr fun t _ ht => ?_
        have hav' := ((mem_filter.mp ht).2).1 i
        rw [Function.update_of_ne hib] at hav'
        by_cases h0 : φ i = 0
        · exact hav'.1 h0
        · exact hav'.2 (hi h0)
      rw [this, card_empty]
      exact Nat.zero_le _
  -- `B2`: `rA` into the plane through `a`, and `rC` through `c`.
  set PC' := univ.filter fun φ : Fin n → E =>
    (∀ i, i ≠ a → φ i ≠ 0 ∧ φ i ≠ 1) ∧ LinearIndependent K ![Q r0 φ, Q rB φ] ∧ PC φ
  have hfibA : ∀ φ : Fin n → E, (univ.filter fun t => Function.update φ a t ∈ B2).card
      ≤ Fintype.card K ^ 2 * (if φ ∈ PC' then 1 else 0) := by
    intro φ
    by_cases hφ : φ ∈ PC'
    · obtain ⟨hav, hind, -⟩ := (mem_filter.mp hφ).2
      rw [if_pos hφ, mul_one]
      calc (univ.filter fun t => Function.update φ a t ∈ B2).card
          ≤ (univ.filter fun t : E => (t ≠ 0 ∧ t ≠ 1) ∧
              ratioF (r0 a) t * Q rA φ ∈ Submodule.span K (Set.range ![Q r0 φ, Q rB φ])).card := by
            refine card_le_card fun t ht => ?_
            obtain ⟨hav', -, hA, -⟩ := (mem_filter.mp (mem_filter.mp ht).2).2
            refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
            · simpa using hav' a
            · have := hA
              simp only [PA, V, hQa, Function.update_self] at this
              exact this
        _ ≤ Fintype.card K ^ 2 :=
            card_ratio_mem_le _ _ (hQne rA φ fun i hia _ => hav i hia) _ _ hind
    · rw [if_neg hφ, mul_zero, Nat.le_zero, card_eq_zero]
      refine filter_eq_empty_iff.mpr fun t _ ht => hφ ?_
      obtain ⟨hav', hind', -, hC⟩ := (mem_filter.mp ht).2
      refine mem_filter.mpr ⟨mem_univ _, fun i hia => ?_, ?_, ?_⟩
      · have := hav' i
        rwa [Function.update_of_ne hia] at this
      · simpa only [hQa] using hind'
      · have := hC
        simp only [PC, V, hQa] at this
        rwa [Function.update_of_ne (Ne.symm hac)] at this
  have hPC' : PC'.card * Fintype.card E ≤ Fintype.card K ^ 2 * Fintype.card E ^ n := by
    refine card_mul_le_of_fiber c _ _ fun φ => ?_
    by_cases hgood : (∀ i, i ≠ a → i ≠ c → φ i ≠ 0 ∧ φ i ≠ 1) ∧
        LinearIndependent K ![Q r0 φ, Q rB φ]
    · calc (univ.filter fun t => Function.update φ c t ∈ PC').card
          ≤ (univ.filter fun t : E => (t ≠ 0 ∧ t ≠ 1) ∧
              ratioF (r0 c) t * Q rC φ ∈ Submodule.span K (Set.range ![Q r0 φ, Q rB φ])).card := by
            refine card_le_card fun t ht => ?_
            obtain ⟨hav', -, hC⟩ := (mem_filter.mp (mem_filter.mp ht).2).2
            refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
            · simpa using hav' c (Ne.symm hac)
            · have := hC
              simp only [PC, V, hQc, Function.update_self] at this
              exact this
        _ ≤ Fintype.card K ^ 2 :=
            card_ratio_mem_le _ _ (hQne rC φ hgood.1) _ _ hgood.2
    · have : (univ.filter fun t => Function.update φ c t ∈ PC') = ∅ := by
        refine filter_eq_empty_iff.mpr fun t _ ht => hgood ?_
        obtain ⟨hav', hind', -⟩ := (mem_filter.mp ht).2
        refine ⟨fun i hia hic => ?_, by simpa only [hQc] using hind'⟩
        have := hav' i hia
        rwa [Function.update_of_ne hic] at this
      rw [this, card_empty]
      exact Nat.zero_le _
  have hB2 : B2.card * Fintype.card E ^ 2 ≤ Fintype.card K ^ 4 * Fintype.card E ^ n := by
    have h1 := card_mul_le_sum_fiber a B2
    have h2 : ∑ φ : Fin n → E, (univ.filter fun t => Function.update φ a t ∈ B2).card
        ≤ Fintype.card K ^ 2 * PC'.card := by
      calc _ ≤ ∑ φ : Fin n → E, Fintype.card K ^ 2 * (if φ ∈ PC' then 1 else 0) :=
            sum_le_sum fun φ _ => hfibA φ
        _ = Fintype.card K ^ 2 * PC'.card := by
            rw [← mul_sum, sum_boole]
            simp
    calc B2.card * Fintype.card E ^ 2 = (B2.card * Fintype.card E) * Fintype.card E := by ring
      _ ≤ (Fintype.card K ^ 2 * PC'.card) * Fintype.card E :=
          Nat.mul_le_mul_right _ (h1.trans h2)
      _ = Fintype.card K ^ 2 * (PC'.card * Fintype.card E) := by ring
      _ ≤ Fintype.card K ^ 2 * (Fintype.card K ^ 2 * Fintype.card E ^ n) :=
          Nat.mul_le_mul_left _ hPC'
      _ = Fintype.card K ^ 4 * Fintype.card E ^ n := by ring
  calc _ ≤ (Z ∪ B0 ∪ B2).card * Fintype.card E ^ 2 := Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (Z.card + B0.card + B2.card) * Fintype.card E ^ 2 := by
        refine Nat.mul_le_mul_right _ ?_
        calc (Z ∪ B0 ∪ B2).card ≤ (Z ∪ B0).card + B2.card := card_union_le _ _
          _ ≤ Z.card + B0.card + B2.card := by
              have := card_union_le Z B0
              omega
    _ = (Z.card * Fintype.card E) * Fintype.card E + (B0.card * Fintype.card E) * Fintype.card E
          + B2.card * Fintype.card E ^ 2 := by ring
    _ ≤ ((2 * n) * Fintype.card E ^ n) * Fintype.card E
          + ((Fintype.card K + 1) * Fintype.card E ^ n) * Fintype.card E
          + Fintype.card K ^ 4 * Fintype.card E ^ n := by
        gcongr
    _ = _ := by ring

end QuotientSecurity.Hiding
