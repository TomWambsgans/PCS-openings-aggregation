-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.GadgetTheorem
import QuotientZk.JointCore

/-!
# The secret tables' openings in the joint view (F3 with the gadget)

A secret table is opened on a `GadgetLayout` stack `stackD d + stackR r` (the table `d`, the padding
`r` uniform). The opening proves its `m` claims and **the gadget as one more claim, of value zero**
(`claimsW`), batched by the powers of its challenge `λ` (`powers`: the gadget's is `λ^m`). Its view
up to the first fold is F3's `viewMap` (`levelMap`).

The per-opening theorem is `GadgetLayout.view_evalDistEq` (`Hiding/GadgetTheorem.lean`): at every
challenge `(λ, φ)` with `λ ≠ 0`, no coordinate of `φ` in `{0, 1}` and at most one of `φ₀, φ₁, φ₂` in
`K` (`GoodCh`), two tables with the same claims (the gadget's included) give the same distribution
of views; conditions (S) and (R) are proven there. Here:

* `claimsW_stackD_eq`: the table's part weighs nothing in the gadget's claim, so tables with the
  same `m` claims have the same claims with the gadget;
* `view_evalDistEq_of_good`: `GadgetLayout.view_evalDistEq` in the joint argument's terms, under
  **(Q)**, **`WeightsFit`** and the layout's lanes (`Placed`, `hA`, `hlow`, `hcube`, `hrand`);
* `prob_not_goodCh_le`, `goodCh_bound_le`: `GoodCh` fails with probability at most
  `(12·|E| + 3·|K|²)/|E|² + 1/|E|`, below `2^-188` at `|K| = 2^64`, `|E| = 2^192`.
-/

namespace QuotientZk.Joint.Gadget

open Finset OracleComp QuotientSecurity.Hiding

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q]
  [DecidableEq Q]

/-- The gadget's lanes as deployed (`opening::gadget_lanes`): pattern 0 on lane indices `0`, `31`,
pattern 1 on `1`, `30`, the overflow lane on `32`; distinct lanes at distinct indices. -/
structure Placed (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) : Prop where
  inj : Function.Injective pos
  a0 : pos (L.pairA 0) = lane 0
  b0 : pos (L.pairB 0) = lane 31
  a1 : pos (L.pairA 1) = lane 1
  b1 : pos (L.pairB 1) = lane 30
  ov : pos L.ov = lane 32

/-- The claims with the gadget as the last. -/
abbrev claimsW (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) {m : ℕ}
    (Wc : Fin m → ι → Y → E) (β : Fin 3 → E) : Fin (m + 1) → ι → Y → E :=
  GadgetLayout.withGadget Wc (L.gadgetW pos β)

/-- The batching powers `λ^c` of the claims, then the gadget's `λ^m`. -/
def powers (m : ℕ) (lam : E) : Fin (m + 1) → E :=
  Fin.snoc (fun c : Fin m => lam ^ (c : ℕ)) (lam ^ m)

/-- **The opening's view up to the first fold**: the lane rounds of the batched weight (the claims
and the gadget), the folded table, the opened rows. -/
def levelMap (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (β : Fin 3 → E) (lam : Fin (m + 1) → E) (φ : Fin 6 → E) (enc : Q → Y → K) :
    (ι → Y → K) →ₗ[K] (Fin 6 → E × E) × (Y → E) × (Q → ι → K) :=
  viewMap (roundsMap pos φ (HiddenLayout.combinedW pos (claimsW L pos Wc β) lam))
    (HiddenLayout.foldW pos φ) enc

/-- The challenges at which the opening hides: `φ` avoids `{0, 1}` coordinatewise, at most one of
`φ₀, φ₁, φ₂` lies in `K`, and the batching challenge `λ` is not zero. -/
def GoodCh (φ : Fin 6 → E) (lam : E) : Prop :=
  ((∀ i, φ i ≠ 0 ∧ φ i ≠ 1) ∧ ¬ TwoInK (K := K) φ) ∧ lam ≠ 0

section Lemmas

variable (L : GadgetLayout ι Y)

theorem not_atGadget_of_first {y : Y} (hy : y ∈ L.first) : ¬ L.AtGadget y := by
  rintro ⟨p, i, h⟩
  exact L.gent_first p i (h ▸ hy)

theorem stackD_apply (d : ι → Y → K) (l : ι) (y : Y) :
    L.stackD d l y = if L.randPos l y then 0 else d l y := rfl

/-- The gadget's weight is zero off its entries. -/
theorem gadgetW_eq_zero (pos : ι → (Fin 6 → Bool)) (β : Fin 3 → E) {l : ι} {y : Y}
    (hy : ¬ L.AtGadget y) : L.gadgetW pos β l y = 0 := by
  unfold GadgetLayout.gadgetW
  refine sum_eq_zero fun p _ => sum_eq_zero fun i _ => ?_
  rw [if_neg]
  intro h
  exact hy ⟨p, i, h⟩

/-- The batched weights vanish on the first pieces below the gadget. -/
theorem combinedW_first (pos : ι → (Fin 6 → Bool)) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (hW : L.WeightsFit Wc) (β : Fin 3 → E) (lam : Fin (m + 1) → E) :
    ∀ b, ∀ y ∈ L.first, HiddenLayout.combinedW pos (claimsW L pos Wc β) lam b y = 0 := by
  intro b y hy
  have hc : ∀ (c : Fin (m + 1)) l, claimsW L pos Wc β c l y = 0 := by
    intro c l
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_last]
      exact gadgetW_eq_zero L pos β (not_atGadget_of_first L hy)
    · simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_castSucc]
      exact hW.first i l y hy
  simp [HiddenLayout.combinedW, hc]

/-- The table's part weighs nothing in the gadget's claim. -/
theorem claim_last_stackD (pos : ι → (Fin 6 → Bool)) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (β : Fin 3 → E) (d : ι → Y → K) :
    HiddenLayout.claimsMap (K := K) (claimsW L pos Wc β) (L.stackD d) (Fin.last m) = 0 := by
  show ∑ l, ∑ y, claimsW L pos Wc β (Fin.last m) l y * algebraMap K E (L.stackD d l y) = 0
  simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_last]
  refine sum_eq_zero fun l _ => sum_eq_zero fun y _ => ?_
  by_cases hg : L.AtGadget y
  · rw [stackD_apply, if_pos (show L.randPos l y from Or.inr (Or.inl hg))]
    simp
  · rw [gadgetW_eq_zero L pos β hg, zero_mul]

/-- Two tables with the same claims have the same claims with the gadget. -/
theorem claimsW_stackD_eq (pos : ι → (Fin 6 → Bool)) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (β : Fin 3 → E) {d d' : ι → Y → K}
    (hd : HiddenLayout.claimsMap (K := K) Wc (L.stackD d) =
      HiddenLayout.claimsMap Wc (L.stackD d')) :
    HiddenLayout.claimsMap (K := K) (claimsW L pos Wc β) (L.stackD d) =
      HiddenLayout.claimsMap (claimsW L pos Wc β) (L.stackD d') := by
  funext c
  refine Fin.lastCases ?_ (fun i => ?_) c
  · rw [claim_last_stackD L pos Wc β d, claim_last_stackD L pos Wc β d']
  · show ∑ l, ∑ y, claimsW L pos Wc β (Fin.castSucc i) l y * algebraMap K E (L.stackD d l y) =
      ∑ l, ∑ y, claimsW L pos Wc β (Fin.castSucc i) l y * algebraMap K E (L.stackD d' l y)
    simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_castSucc]
    exact congrFun hd i

/-- **The opening hides its table at every good challenge** (`GadgetLayout.view_evalDistEq`), under
**(Q)** `hQ`, **`WeightsFit`** `hW` and the layout's lanes. -/
theorem view_evalDistEq_of_good [CharP E 2] [FiniteDimensional K E] [SampleableType (ι → Y → K)]
    (h3 : Module.finrank K E = 3) (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos)
    (hA : ∀ p, ¬ L.isRand (L.pairA p))
    (hlow : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range pos)
    (hcube : ∀ l : Fin 64, 32 ≤ (l : ℕ) → (l : ℕ) < 40 → lane l ∈ Set.range pos)
    (hrand : ∀ b ∈ cube true, b ≠ lane 32 → ∃ r, pos r = b ∧ L.isRand r)
    {m : ℕ} (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (β : Module.Basis (Fin 3) K E)
    (enc : Q → Y → K) (hQ : Function.Surjective (firstEval enc L.first)) (lam : E)
    (φ : Fin 6 → E) (hg : GoodCh (K := K) φ lam)
    {O : Type} (g : (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → O) {d d' : ι → Y → K}
    (hd : HiddenLayout.claimsMap (K := K) Wc (L.stackD d) =
      HiddenLayout.claimsMap Wc (L.stackD d')) :
    (fun r => g (levelMap L pos Wc β (powers m lam) φ enc (L.stackD d + L.stackR r))) <$>
        ($ᵗ (ι → Y → K))
      =ᵈ (fun r => g (levelMap L pos Wc β (powers m lam) φ enc (L.stackD d' + L.stackR r))) <$>
        ($ᵗ (ι → Y → K)) := by
  have h2K : (2 : K) = 0 :=
    (algebraMap K E).injective (by rw [map_ofNat, map_zero]; exact CharTwo.two_eq_zero)
  exact L.view_evalDistEq h3 h2K pos hP.inj Wc hW β enc hQ hA hP.a0 hP.b0 hP.a1 hP.b1 hP.ov hlow
    hcube hrand (fun c : Fin m => lam ^ (c : ℕ)) (lam ^ m) (pow_ne_zero _ hg.2) φ hg.1.1 hg.1.2 g
    (claimsW_stackD_eq L pos Wc β hd)

end Lemmas

open Classical in
/-- **The bad challenges of one opening**: for uniform `((λ, ·), φ)`, `GoodCh` fails with
probability at most `(12·|E| + 3·|K|²)/|E|² + 1/|E|`. -/
theorem prob_not_goodCh_le [Fintype K] [Fintype E] [DecidableEq E] [SampleableType E]
    {Γ : Type} [SampleableType Γ] [Fintype Γ] :
    Pr{let x ← $ᵗ ((E × Γ) × (Fin 6 → E))}[¬ GoodCh (K := K) x.2 x.1.1]
      ≤ ((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
          ((Fintype.card E ^ 2 : ℕ) : ENNReal) + 1 / (Fintype.card E : ENNReal) := by
  refine (prEvent_not_and_le _ (fun x : (E × Γ) × (Fin 6 → E) =>
    (∀ i, x.2 i ≠ 0 ∧ x.2 i ≠ 1) ∧ ¬ TwoInK (K := K) x.2) (fun x => x.1.1 ≠ 0)).trans
    (add_le_add (prob_not_solvable_le (K := K) (Γ := E × Γ)) (le_of_eq ?_))
  simp only [not_not]
  rw [prEvent_uniform_fst (fun y : E × Γ => y.1 = 0), prEvent_uniform_fst (fun e : E => e = 0),
    SampleableType.prEvent_uniformSample, Finset.filter_eq' Finset.univ (0 : E)]
  simp

/-- At `|K| = 2^64`, `|E| = 2^192`: one opening's bad challenges have probability at most
`13·2^-192 + 3·2^-256 ≤ 2^-188`. -/
theorem goodCh_bound_le :
    (((2 * 6 * 2 ^ 192 + 3 * (2 ^ 64) ^ 2 : ℕ) : ENNReal) / (((2 ^ 192) ^ 2 : ℕ) : ENNReal) +
      1 / ((2 ^ 192 : ℕ) : ENNReal)) ≤ 1 / 2 ^ 188 := by
  have h1 := HiddenLayout.natCast_div_le_natCast_div (a := 2 * 6 * 2 ^ 192 + 3 * (2 ^ 64) ^ 2)
    (b := (2 ^ 192) ^ 2) (c := 15) (d := 2 ^ 192) (by positivity) (by positivity) (by norm_num)
  calc (((2 * 6 * 2 ^ 192 + 3 * (2 ^ 64) ^ 2 : ℕ) : ENNReal) / (((2 ^ 192) ^ 2 : ℕ) : ENNReal) +
        1 / ((2 ^ 192 : ℕ) : ENNReal))
      ≤ ((15 : ℕ) : ENNReal) / ((2 ^ 192 : ℕ) : ENNReal) +
          ((1 : ℕ) : ENNReal) / ((2 ^ 192 : ℕ) : ENNReal) := by
        gcongr
        simp
    _ = ((16 : ℕ) : ENNReal) / ((2 ^ 192 : ℕ) : ENNReal) := by
        rw [ENNReal.div_add_div_same]
        norm_num
    _ ≤ 1 / 2 ^ 188 := by
        have h := HiddenLayout.natCast_div_le_natCast_div (a := 16) (b := 2 ^ 192) (c := 1)
          (d := 2 ^ 188) (by positivity) (by positivity) (by norm_num)
        refine h.trans (le_of_eq ?_)
        norm_num

end QuotientZk.Joint.Gadget
