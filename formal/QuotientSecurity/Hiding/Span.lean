-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Rounds

/-!
# Condition (S): three random lanes' fold weights span `E`, but for few challenges

Lane `r` weighs `eq(φ, r) = Π_i (r_i ? φ_i : 1 - φ_i)` in the first fold. Condition (S) of
`HIDING.md` asks that the random lanes' weights span `E` over `K`; with `[E : K] = 3` it is enough
that three of them are `K`-linearly independent. This file bounds the challenges `φ ∈ E^n` where
three lanes `r1, r2, r3` are not: if a coordinate `a` has `r1_a = r3_a ≠ r2_a` and another `b` has
`r1_b ≠ r3_b`, at most `(|K|^2 + |K| + 2n + 2)·|E|^(n-1)` of them (`card_not_linearIndependent_le`),
a fraction below `(|K|^2 + |K| + 2n + 2)/|E|`: `2^-64` and a bit at `|K| = 2^64`, `|E| = 2^192`.

The count is by fibers. Once the other coordinates are fixed, `φ_b` must put the ratio of `r1` and
`r3` in a line over `K` (`|K| + 1` values: `card_bad_pair`), and `φ_a` must put `r2` in the plane of
`r1` and `r3` (`|K|^2 + 1` values: `card_bad_triple`), unless a coordinate is `0` or `1`.
-/

namespace QuotientSecurity.Hiding

open Finset

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E] [Fintype K] [Fintype E] [DecidableEq E]

/-- The members `α • x + β • y` of the span of a pair. -/
theorem mem_span_pair' (x y : E) (α β : K) :
    α • x + β • y ∈ Submodule.span K (Set.range ![x, y]) :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- The elements `s` with `c * s` in a `K`-subspace `V` are as many as `V`'s, for `c ≠ 0`. -/
theorem card_filter_mul_mem (c : E) (hc : c ≠ 0) (V : Submodule K E) [DecidablePred (· ∈ V)] :
    (univ.filter fun s : E => c * s ∈ V).card = (univ.filter fun v : E => v ∈ V).card := by
  refine Finset.card_bij (fun s _ => c * s) (fun s hs => by simpa using hs) ?_ ?_
  · intro s _ s' _ h
    exact mul_left_cancel₀ hc h
  · intro v hv
    refine ⟨c⁻¹ * v, by simpa [mul_inv_cancel_left₀ hc] using hv, ?_⟩
    rw [mul_inv_cancel_left₀ hc]

/-- A `K`-subspace spanned by `m` independent vectors has `|K|^m` elements. -/
theorem card_filter_mem_span {m : ℕ} (v : Fin m → E) (hv : LinearIndependent K v)
    [DecidablePred (· ∈ Submodule.span K (Set.range v))] :
    (univ.filter fun x : E => x ∈ Submodule.span K (Set.range v)).card = Fintype.card K ^ m := by
  classical
  have h1 : (univ.filter fun x : E => x ∈ Submodule.span K (Set.range v)).card
      = Fintype.card (Submodule.span K (Set.range v)) := by
    rw [Fintype.card_subtype]
  rw [h1, Module.card_eq_pow_finrank (K := K), finrank_span_eq_card hv, Fintype.card_fin]

/-- `t ↦ t / (1 - t)` is injective away from `1`. -/
theorem div_one_sub_injOn : Set.InjOn (fun t : E => t / (1 - t)) {t | t ≠ 1} := by
  intro t ht s hs h
  have ht' : (1 : E) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hs' : (1 : E) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  simp only at h
  rw [div_eq_div_iff ht' hs'] at h
  linear_combination h

/-- A finset is at most one more than itself without one element. -/
theorem card_le_card_erase_add_one' {α : Type} [DecidableEq α] (s : Finset α) (a : α) :
    s.card ≤ (s.erase a).card + 1 := by
  have := Finset.pred_card_le_card_erase (s := s) (a := a)
  omega

open Classical in
/-- **The third weight.** If `A1, A3` are independent and `A2 ≠ 0`, at most `|K|^2 + 1` values `t`
make `(1-t)·A1, t·A2, (1-t)·A3` dependent: `t / (1 - t)` must put `A2` in the plane of the others. -/
theorem card_bad_triple (A1 A2 A3 : E) (hind : LinearIndependent K ![A1, A3]) (hA2 : A2 ≠ 0) :
    (univ.filter fun t : E =>
        ¬ LinearIndependent K ![(1 - t) * A1, t * A2, (1 - t) * A3]).card
      ≤ Fintype.card K ^ 2 + 1 := by
  classical
  set V := Submodule.span K (Set.range ![A1, A3])
  set bad := univ.filter fun t : E => ¬ LinearIndependent K ![(1 - t) * A1, t * A2, (1 - t) * A3]
  set T := univ.filter fun s : E => A2 * s ∈ V
  have hT : T.card = Fintype.card K ^ 2 := by
    rw [card_filter_mul_mem A2 hA2 V, card_filter_mem_span ![A1, A3] hind]
  have hmap : ∀ t ∈ bad.erase 1, t / (1 - t) ∈ T := by
    intro t ht
    obtain ⟨ht1, htb⟩ := mem_erase.mp ht
    have hbad := (mem_filter.mp htb).2
    rw [Fintype.not_linearIndependent_iff] at hbad
    obtain ⟨c, hc, i, hi⟩ := hbad
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Algebra.smul_def] at hc
    have h1t : (1 : E) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    have hc1 : c 1 ≠ 0 := by
      intro hc1
      rw [hc1, map_zero, zero_mul, add_zero] at hc
      have hpair : c 0 • A1 + c 2 • A3 = 0 := by
        have : (1 - t) * (algebraMap K E (c 0) * A1 + algebraMap K E (c 2) * A3) = 0 := by
          linear_combination hc
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h1t
        · simpa [Algebra.smul_def] using h
      obtain ⟨h0, h2⟩ := LinearIndependent.pair_iff.mp hind _ _ hpair
      fin_cases i <;> simp_all
    have ha1 : algebraMap K E (c 1) ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (algebraMap K E).injective]
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have heq : A2 * (t / (1 - t))
        = (-(c 1)⁻¹ * c 0) • A1 + (-(c 1)⁻¹ * c 2) • A3 := by
      simp only [Algebra.smul_def, map_mul, map_neg, map_inv₀]
      field_simp
      linear_combination hc
    rw [heq]
    exact mem_span_pair' A1 A3 _ _
  have hinj : Set.InjOn (fun t : E => t / (1 - t)) (bad.erase 1 : Set E) :=
    div_one_sub_injOn.mono fun t ht => (mem_erase.mp ht).1
  have := Finset.card_le_card_of_injOn _ hmap hinj
  calc bad.card ≤ (bad.erase 1).card + 1 := card_le_card_erase_add_one' _ _
    _ ≤ T.card + 1 := by omega
    _ = _ := by rw [hT]

open Classical in
/-- **The second weight.** If `B1, B3 ≠ 0`, at most `|K| + 1` values `t` make `(1-t)·B1, t·B3`
dependent: `t / (1 - t)` must put `B3` on the line of `B1`. -/
theorem card_bad_pair (B1 B3 : E) (h1 : B1 ≠ 0) (h3 : B3 ≠ 0) :
    (univ.filter fun t : E => ¬ LinearIndependent K ![(1 - t) * B1, t * B3]).card
      ≤ Fintype.card K + 1 := by
  classical
  set V := Submodule.span K (Set.range ![B1])
  set bad := univ.filter fun t : E => ¬ LinearIndependent K ![(1 - t) * B1, t * B3]
  set T := univ.filter fun s : E => B3 * s ∈ V
  have hind : LinearIndependent K ![B1] := by
    rw [linearIndependent_unique_iff]
    simpa using h1
  have hT : T.card = Fintype.card K := by
    rw [card_filter_mul_mem B3 h3 V, card_filter_mem_span ![B1] hind, pow_one]
  have hmap : ∀ t ∈ bad.erase 1, t / (1 - t) ∈ T := by
    intro t ht
    obtain ⟨ht1, htb⟩ := mem_erase.mp ht
    have hbad := (mem_filter.mp htb).2
    rw [LinearIndependent.pair_iff] at hbad
    push Not at hbad
    obtain ⟨α, β, hαβ, hne⟩ := hbad
    simp only [Algebra.smul_def] at hαβ
    have h1t : (1 : E) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    have hβ : β ≠ 0 := by
      intro hβ
      rw [hβ, map_zero, zero_mul, add_zero] at hαβ
      have hα : α = 0 := by
        rcases mul_eq_zero.mp hαβ with h | h
        · exact (map_eq_zero_iff _ (algebraMap K E).injective).mp h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' h1t
          · exact absurd h' h1
      exact hne hα hβ
    have hb : algebraMap K E β ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (algebraMap K E).injective]
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have heq : B3 * (t / (1 - t)) = (-β⁻¹ * α) • B1 := by
      simp only [Algebra.smul_def, map_mul, map_neg, map_inv₀]
      field_simp
      linear_combination hαβ
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  have hinj : Set.InjOn (fun t : E => t / (1 - t)) (bad.erase 1 : Set E) :=
    div_one_sub_injOn.mono fun t ht => (mem_erase.mp ht).1
  have := Finset.card_le_card_of_injOn _ hmap hinj
  calc bad.card ≤ (bad.erase 1).card + 1 := card_le_card_erase_add_one' _ _
    _ ≤ T.card + 1 := by omega
    _ = _ := by rw [hT]

/-- A predicate's count is unchanged by the substitution `t ↦ 1 - t`. -/
theorem card_filter_one_sub (P : E → Prop) [DecidablePred P] :
    (univ.filter fun t : E => P (1 - t)).card = (univ.filter P).card := by
  refine Finset.card_bij (fun t _ => 1 - t) (fun t ht => by simpa using ht) ?_ ?_
  · intro t _ s _ h
    simpa using h
  · intro s hs
    exact ⟨1 - s, by simpa using hs, by ring⟩

/-! ### Fibers -/

/-- **Counting by fibers.** If every line through the coordinate `a` meets `S` in at most `B`
points, then `|S| ≤ B·|E|^(n-1)`. -/
theorem card_mul_le_of_fiber {n : ℕ} (a : Fin n) (S : Finset (Fin n → E)) (B : ℕ)
    (h : ∀ φ : Fin n → E, (univ.filter fun t => Function.update φ a t ∈ S).card ≤ B) :
    S.card * Fintype.card E ≤ B * Fintype.card E ^ n := by
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
  have hsum : ∑ φ : Fin n → E, (univ.filter fun t => Function.update φ a t ∈ S).card
      ≤ ∑ _φ : Fin n → E, B := sum_le_sum fun φ _ => h φ
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul] at hsum
  rw [card_product, card_univ] at hinj
  calc S.card * Fintype.card E ≤ P.card := hinj
    _ ≤ Fintype.card E ^ n * B := hP ▸ hsum
    _ = B * Fintype.card E ^ n := mul_comm _ _

/-! ### The lanes' weights -/

/-- One coordinate's factor of `eq`. -/
def eqFactor (c : Bool) (t : E) : E := if c then t else 1 - t

theorem eqW_eq_mul_prod_erase {n : ℕ} (φ : Fin n → E) (r : Fin n → Bool) (a : Fin n) :
    eqW φ r = eqFactor (r a) (φ a) * ∏ i ∈ univ.erase a, eqFactor (r i) (φ i) :=
  (mul_prod_erase univ (fun i => eqFactor (r i) (φ i)) (mem_univ a)).symm

theorem prod_erase_update {n : ℕ} (s : Finset (Fin n)) (φ : Fin n → E) (r : Fin n → Bool)
    (a : Fin n) (ha : a ∉ s) (t : E) :
    ∏ i ∈ s, eqFactor (r i) (Function.update φ a t i) = ∏ i ∈ s, eqFactor (r i) (φ i) := by
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by rintro rfl; exact ha hi)]

theorem prod_ne_zero_of_avoid {n : ℕ} (s : Finset (Fin n)) (φ : Fin n → E) (r : Fin n → Bool)
    (h : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) : ∏ i ∈ s, eqFactor (r i) (φ i) ≠ 0 := by
  refine prod_ne_zero_iff.mpr fun i _ => ?_
  unfold eqFactor
  split_ifs
  · exact (h i).1
  · exact sub_ne_zero.mpr (Ne.symm (h i).2)

open Classical in
/-- The values `t` at which the pattern `eqFactor u t, eqFactor (!u) t` makes a triple dependent. -/
theorem card_bad_triple' (u : Bool) (A1 A2 A3 : E) (hind : LinearIndependent K ![A1, A3])
    (hA2 : A2 ≠ 0) :
    (univ.filter fun t : E => ¬ LinearIndependent K
        ![eqFactor u t * A1, eqFactor (!u) t * A2, eqFactor u t * A3]).card
      ≤ Fintype.card K ^ 2 + 1 := by
  classical
  cases u
  · simpa [eqFactor] using card_bad_triple (K := K) A1 A2 A3 hind hA2
  · rw [← card_filter_one_sub]
    simpa [eqFactor] using card_bad_triple (K := K) A1 A2 A3 hind hA2

open Classical in
/-- The values `t` at which two different factors make a pair dependent. -/
theorem card_bad_pair' (u v : Bool) (huv : u ≠ v) (B1 B3 : E) (h1 : B1 ≠ 0) (h3 : B3 ≠ 0) :
    (univ.filter fun t : E => ¬ LinearIndependent K ![eqFactor u t * B1, eqFactor v t * B3]).card
      ≤ Fintype.card K + 1 := by
  classical
  cases u <;> cases v
  · exact absurd rfl huv
  · simpa [eqFactor] using card_bad_pair (K := K) B1 B3 h1 h3
  · have hsymm : ∀ t : E, LinearIndependent K ![eqFactor true t * B1, eqFactor false t * B3]
        ↔ LinearIndependent K ![(1 - t) * B3, t * B1] := fun t => by
      rw [LinearIndependent.pair_symm_iff]
      simp [eqFactor]
    simp only [hsymm]
    exact card_bad_pair (K := K) B3 B1 h3 h1
  · exact absurd rfl huv

open Classical in
/-- **Condition (S) fails rarely.** Lanes `r1, r2, r3` with a coordinate `a` where `r1, r3` agree
and `r2` does not, and a coordinate `b` where `r1, r3` differ: their fold weights are dependent for
at most `(|K|^2 + |K| + 2n + 2)·|E|^(n-1)` challenges `φ`. -/
theorem card_not_linearIndependent_le {n : ℕ} (r1 r2 r3 : Fin n → Bool) (a b : Fin n)
    (hab : a ≠ b) (ha : r1 a = r3 a) (ha' : r2 a = !r1 a) (hb : r1 b ≠ r3 b) :
    (univ.filter fun φ : Fin n → E =>
        ¬ LinearIndependent K ![eqW φ r1, eqW φ r2, eqW φ r3]).card * Fintype.card E
      ≤ (Fintype.card K ^ 2 + Fintype.card K + 2 * n + 2) * Fintype.card E ^ n := by
  classical
  set avoid : (Fin n → E) → Prop := fun φ => ∀ i, φ i ≠ 0 ∧ φ i ≠ 1
  set Pr : (Fin n → Bool) → (Fin n → E) → E := fun r φ => ∏ i ∈ univ.erase a, eqFactor (r i) (φ i)
  set Z := univ.filter fun φ : Fin n → E => ¬ avoid φ
  set Bb := univ.filter fun φ : Fin n → E => avoid φ ∧ ¬ LinearIndependent K ![Pr r1 φ, Pr r3 φ]
  set Ba := univ.filter fun φ : Fin n → E => avoid φ ∧ LinearIndependent K ![Pr r1 φ, Pr r3 φ] ∧
    ¬ LinearIndependent K ![eqW φ r1, eqW φ r2, eqW φ r3]
  have hsub : (univ.filter fun φ : Fin n → E =>
      ¬ LinearIndependent K ![eqW φ r1, eqW φ r2, eqW φ r3]) ⊆ Z ∪ Bb ∪ Ba := by
    intro φ hφ
    have hd := (mem_filter.mp hφ).2
    by_cases hav : avoid φ
    · by_cases hp : LinearIndependent K ![Pr r1 φ, Pr r3 φ]
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hav, hp, hd⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hav, hp⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hav⟩))
  -- The coordinates that are `0` or `1`.
  have hZ : Z.card * Fintype.card E ≤ (2 * n) * Fintype.card E ^ n := by
    have hZsub : Z ⊆ univ.biUnion fun i : Fin n =>
        univ.filter fun φ : Fin n → E => φ i = 0 ∨ φ i = 1 := by
      intro φ hφ
      have := (mem_filter.mp hφ).2
      simp only [avoid, not_forall, not_and_or, not_not] at this
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
    calc Z.card * Fintype.card E
        ≤ (univ.biUnion fun i : Fin n =>
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
  -- `φ_b` puts the ratio of `r1` and `r3` (off `a`) on a line.
  have hBb : Bb.card * Fintype.card E ≤ (Fintype.card K + 1) * Fintype.card E ^ n := by
    refine card_mul_le_of_fiber b _ _ fun φ => ?_
    have hbmem : b ∈ univ.erase a := mem_erase.mpr ⟨Ne.symm hab, mem_univ _⟩
    set Q : (Fin n → Bool) → E := fun r => ∏ i ∈ (univ.erase a).erase b, eqFactor (r i) (φ i)
    have hPr : ∀ r t, Pr r (Function.update φ b t) = eqFactor (r b) t * Q r := by
      intro r t
      simp only [Pr]
      rw [← mul_prod_erase _ _ hbmem, Function.update_self,
        prod_erase_update _ φ r b (by simp) t]
    by_cases hav : ∀ i, i ≠ b → φ i ≠ 0 ∧ φ i ≠ 1
    · have hQ : ∀ r, Q r ≠ 0 := fun r => prod_ne_zero_iff.mpr fun i hi => by
        have hib : i ≠ b := (mem_erase.mp hi).1
        unfold eqFactor
        split_ifs
        · exact (hav i hib).1
        · exact sub_ne_zero.mpr (Ne.symm (hav i hib).2)
      calc (univ.filter fun t => Function.update φ b t ∈ Bb).card
          ≤ (univ.filter fun t : E => ¬ LinearIndependent K
              ![eqFactor (r1 b) t * Q r1, eqFactor (r3 b) t * Q r3]).card := by
            refine card_le_card fun t ht => ?_
            have := (mem_filter.mp (mem_filter.mp ht).2).2.2
            rw [hPr, hPr] at this
            exact mem_filter.mpr ⟨mem_univ _, this⟩
        _ ≤ Fintype.card K + 1 := card_bad_pair' _ _ hb _ _ (hQ r1) (hQ r3)
    · push Not at hav
      obtain ⟨i, hib, hi⟩ := hav
      have : (univ.filter fun t => Function.update φ b t ∈ Bb) = ∅ := by
        refine filter_eq_empty_iff.mpr fun t _ ht => ?_
        have hav' := ((mem_filter.mp ht).2).1 i
        rw [Function.update_of_ne hib] at hav'
        by_cases h0 : φ i = 0
        · exact hav'.1 h0
        · exact hav'.2 (hi h0)
      rw [this, card_empty]
      exact Nat.zero_le _
  -- `φ_a` puts `r2` in the plane of `r1` and `r3`.
  have hBa : Ba.card * Fintype.card E ≤ (Fintype.card K ^ 2 + 1) * Fintype.card E ^ n := by
    refine card_mul_le_of_fiber a _ _ fun φ => ?_
    have hPr : ∀ r t, Pr r (Function.update φ a t) = Pr r φ := fun r t =>
      prod_erase_update _ φ r a (by simp) t
    have heqW : ∀ r t, eqW (Function.update φ a t) r = eqFactor (r a) t * Pr r φ := by
      intro r t
      rw [eqW_eq_mul_prod_erase _ r a, Function.update_self]
      exact congrArg _ (hPr r t)
    by_cases hgood : LinearIndependent K ![Pr r1 φ, Pr r3 φ] ∧ Pr r2 φ ≠ 0
    · calc (univ.filter fun t => Function.update φ a t ∈ Ba).card
          ≤ (univ.filter fun t : E => ¬ LinearIndependent K
              ![eqFactor (r1 a) t * Pr r1 φ, eqFactor (!(r1 a)) t * Pr r2 φ,
                eqFactor (r1 a) t * Pr r3 φ]).card := by
            refine card_le_card fun t ht => ?_
            have := (mem_filter.mp (mem_filter.mp ht).2).2.2.2
            rw [heqW, heqW, heqW, ← ha, ha'] at this
            exact mem_filter.mpr ⟨mem_univ _, this⟩
        _ ≤ Fintype.card K ^ 2 + 1 := card_bad_triple' _ _ _ _ hgood.1 hgood.2
    · have : (univ.filter fun t => Function.update φ a t ∈ Ba) = ∅ := by
        refine filter_eq_empty_iff.mpr fun t _ ht => ?_
        obtain ⟨hav, hp, -⟩ := (mem_filter.mp ht).2
        rw [hPr, hPr] at hp
        refine hgood ⟨hp, ?_⟩
        rw [← hPr r2 t]
        exact prod_ne_zero_of_avoid _ _ r2 hav
      rw [this, card_empty]
      exact Nat.zero_le _
  calc _ ≤ (Z ∪ Bb ∪ Ba).card * Fintype.card E := Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (Z.card + Bb.card + Ba.card) * Fintype.card E := by
        refine Nat.mul_le_mul_right _ ?_
        calc (Z ∪ Bb ∪ Ba).card ≤ (Z ∪ Bb).card + Ba.card := card_union_le _ _
          _ ≤ Z.card + Bb.card + Ba.card := by
              have := card_union_le Z Bb
              omega
    _ = Z.card * Fintype.card E + Bb.card * Fintype.card E + Ba.card * Fintype.card E := by
        ring
    _ ≤ (2 * n) * Fintype.card E ^ n + (Fintype.card K + 1) * Fintype.card E ^ n +
          (Fintype.card K ^ 2 + 1) * Fintype.card E ^ n := by
        gcongr
    _ = (Fintype.card K ^ 2 + Fintype.card K + 2 * n + 2) * Fintype.card E ^ n := by ring

/-- Three independent weights span `E` when `[E : K] = 3`. -/
theorem span_eq_top_of_three [FiniteDimensional K E] (h3 : Module.finrank K E = 3)
    {x y z : E} (h : LinearIndependent K ![x, y, z]) :
    Submodule.span K (Set.range ![x, y, z]) = ⊤ :=
  h.span_eq_top_of_card_eq_finrank' (by simp [h3])

end QuotientSecurity.Hiding
