-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.GadgetLayout
import QuotientSecurity.Hiding.Solve
import QuotientZk.JointCore

/-!
# The openings of the hidden tables with the gadget (F3, `HIDING.md` since the gadget)

A secret table is opened on a `GadgetLayout` stack: `stackD d + stackR r`, the table `d` and the
padding `r`, uniform. The opening proves the `m` claims `Wc` and **the gadget as one more claim, of
value zero** (`withGadget Wc (gadgetW pos β)`, batched with the powers `lam` of the challenge `λ`,
the gadget's being `λ^m`). Its view up to the first fold is F3's `viewMap`: the six lane rounds of
the batched weight, the folded table `f¹`, the opened rows (`levelMap`); what WHIR shows after the
first fold is a function of `f¹` and the challenges (`g`).

`view_evalDistEq`: two tables with the same `m` claims give the same distribution of views, under

* **(Q)** `hQ`: the codeword of the entries below the gadget, at the opened positions, takes every
  value;
* **(S)** `FoldSpans`: random lanes (none a pair's first lane) whose fold weights span `E` over `K`;
* **(R)** `GadgetLayout.RoundsReached` with the gadget as the last claim;
* **`WeightsFit`**: the claims weigh nothing of the randomness or of the gadget's entries;
* the gadget's lanes as deployed (`Placed`: pairs `(0, 31)`, `(1, 30)`, overflow lane `32`) and
  characteristic 2, so that the padding meets the gadget's zero claim (`gadget_claim_stackR`).

It is `Model.level0_view_evalDistEq` (`HIDING.md`'s steps 1 and 2) for this layout. The claims of the
table's part include the gadget's, zero for every table (`claim_last_stackD`).

`prob_not_foldSpans_le`: (S) fails with probability at most `((2·6 + |K| + 1)|E| + |K|^4)/|E|^2`
for four random lanes in the pattern of `card_not_span_four_le`; the deployed random lanes
`35, 34, 33, 39` are (`deployed_lane_pattern`). At `|K| = 2^64`, `|E| = 2^192`: `≤ 3/2^128`.
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

/-- **The opening's view up to the first fold**: the lane rounds of the batched weight (the claims
and the gadget), the folded table, the opened rows. -/
def levelMap (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (β : Fin 3 → E) (lam : Fin (m + 1) → E) (φ : Fin 6 → E) (enc : Q → Y → K) :
    (ι → Y → K) →ₗ[K] (Fin 6 → E × E) × (Y → E) × (Q → ι → K) :=
  viewMap (roundsMap pos φ (HiddenLayout.combinedW pos (claimsW L pos Wc β) lam))
    (HiddenLayout.foldW pos φ) enc

/-- **Condition (S)** for the gadget layout: random lanes, none a pair's first lane, whose fold
weights span `E` over `K`. -/
def FoldSpans (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) (φ : Fin 6 → E) : Prop :=
  ∃ (p : ℕ) (r : Fin p → ι), (∀ i, L.isRand (r i) ∧ ∀ q, r i ≠ L.pairA q) ∧
    Submodule.span K (Set.range fun i => HiddenLayout.foldW pos φ (r i)) = ⊤

section Lemmas

variable (L : GadgetLayout ι Y)

theorem not_atGadget_of_first {y : Y} (hy : y ∈ L.first) : ¬ L.AtGadget y := by
  rintro ⟨p, i, h⟩
  exact L.gent_first p i (h ▸ hy)

theorem atGadget_gent (p i : Fin 3) : L.AtGadget (L.gent p i) := ⟨p, i, rfl⟩

theorem not_atPat_gent {p p' : Fin 3} (i : Fin 3) (h : p ≠ p') : ¬ L.AtPat p' (L.gent p i) := by
  rintro ⟨i', hi'⟩
  exact h (L.gent_inj p' i' p i hi').1.symm

theorem stackR_apply (r : ι → Y → K) (l : ι) (y : Y) :
    L.stackR r l y = if L.randPos l y ∧ ¬ L.ZeroAt l y then r (L.copyOf y l) y else 0 := rfl

theorem stackD_apply (d : ι → Y → K) (l : ι) (y : Y) :
    L.stackD d l y = if L.randPos l y then 0 else d l y := rfl

theorem copyOf_eq_self {y : Y} {l : ι} (h0 : ¬ (L.AtPat 0 y ∧ l = L.pairB 0))
    (h1 : ¬ (L.AtPat 1 y ∧ l = L.pairB 1)) : L.copyOf y l = l := by
  unfold GadgetLayout.copyOf
  rw [if_neg h0, if_neg h1]

/-- The gadget's weight is zero off its entries. -/
theorem gadgetW_eq_zero (pos : ι → (Fin 6 → Bool)) (β : Fin 3 → E) {l : ι} {y : Y}
    (hy : ¬ L.AtGadget y) : L.gadgetW pos β l y = 0 := by
  unfold GadgetLayout.gadgetW
  refine sum_eq_zero fun p _ => sum_eq_zero fun i _ => ?_
  rw [if_neg]
  intro h
  exact hy ⟨p, i, h⟩

/-- The batched weights vanish on the first pieces below the gadget. -/
theorem claimsW_first (pos : ι → (Fin 6 → Bool)) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (hW : L.WeightsFit Wc) (β : Fin 3 → E) (c : Fin (m + 1)) (l : ι) {y : Y} (hy : y ∈ L.first) :
    claimsW L pos Wc β c l y = 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) c
  · simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_last]
    exact gadgetW_eq_zero L pos β (not_atGadget_of_first L hy)
  · simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_castSucc]
    exact hW.first i l y hy

theorem combinedW_first (pos : ι → (Fin 6 → Bool)) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (hW : L.WeightsFit Wc) (β : Fin 3 → E) (lam : Fin (m + 1) → E) :
    ∀ b, ∀ y ∈ L.first, HiddenLayout.combinedW pos (claimsW L pos Wc β) lam b y = 0 := by
  intro b y hy
  simp [HiddenLayout.combinedW, claimsW_first L pos Wc hW β _ _ hy]

/-- The randomness covers every stack that is zero but below the gadget. -/
theorem onFirst_mem_range (T : ι → Y → K) (hT : OnFirst L.first T) :
    T ∈ LinearMap.range (L.stackR (K := K)) := by
  refine ⟨T, ?_⟩
  funext l y
  rw [stackR_apply]
  by_cases hy : y ∈ L.first
  · have hg := not_atGadget_of_first L hy
    have hz : ¬ L.ZeroAt l y := fun h => hg ⟨2, h.1⟩
    have hc : L.copyOf y l = l :=
      copyOf_eq_self L (fun h => hg ⟨0, h.1⟩) (fun h => hg ⟨1, h.1⟩)
    rw [if_pos (show L.randPos l y ∧ ¬ L.ZeroAt l y from ⟨Or.inl hy, hz⟩), hc]
  · rw [hT l y hy]
    split_ifs
    · exact hT _ y hy
    · rfl

/-- A change at one entry on random lanes, none a pair's first lane, is a change of the
randomness. -/
theorem column_mem_range (y : Y) (k : ι → K)
    (hk : ∀ l, k l ≠ 0 → L.isRand l ∧ ∀ q, l ≠ L.pairA q) :
    (fun l y' => if y' = y then k l else 0) ∈ LinearMap.range (L.stackR (K := K)) := by
  refine ⟨fun l y' => if y' = y then k l else 0, ?_⟩
  funext l y'
  rw [stackR_apply]
  by_cases hyy : y' = y
  · subst hyy
    simp only [ite_true]
    by_cases hkl : k l = 0
    · rw [hkl]
      split_ifs
      · -- the copied lane carries no change either
        have hpa : ∀ q, k (L.pairA q) = 0 := fun q => by
          by_contra hne
          exact (hk _ hne).2 q rfl
        unfold GadgetLayout.copyOf
        split_ifs
        · exact hpa 0
        · exact hpa 1
        · exact hkl
      · rfl
    · obtain ⟨hr, -⟩ := hk l hkl
      have hov : l ≠ L.ov := fun h => L.not_rand_ov (h ▸ hr)
      have hz : ¬ L.ZeroAt l y' := fun h => hov h.2
      have hb : ∀ p, l ≠ L.pairB p := fun p h => L.not_rand_pairB p (h ▸ hr)
      have hc : L.copyOf y' l = l := copyOf_eq_self L (fun h => hb 0 h.2) (fun h => hb 1 h.2)
      rw [if_pos (show L.randPos l y' ∧ ¬ L.ZeroAt l y' from ⟨Or.inr (Or.inr (Or.inl hr)), hz⟩), hc]
  · simp [hyy]

/-- (S) lets the randomness at any entry past the first pieces move `f¹` anywhere. -/
theorem foldSpans_moves (pos : ι → (Fin 6 → Bool)) (φ : Fin 6 → E)
    (hS : FoldSpans (K := K) L pos φ) :
    ∀ y ∉ L.first, ∀ e : E, ∃ ρ ∈ LinearMap.range (L.stackR (K := K)),
      OnColumn y ρ ∧ foldMap (HiddenLayout.foldW pos φ) ρ y = e := by
  classical
  obtain ⟨p, r, hr, htop⟩ := hS
  intro y _ e
  have he : e ∈ Submodule.span K (Set.range fun i => HiddenLayout.foldW pos φ (r i)) :=
    htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp he
  set kv : ι → K := fun l => ∑ i, if r i = l then c i else 0
  have hk : ∀ l, kv l ≠ 0 → L.isRand l ∧ ∀ q, l ≠ L.pairA q := by
    intro l hl
    by_contra hno
    apply hl
    refine sum_eq_zero fun i _ => ?_
    have : r i ≠ l := fun h => hno (h ▸ hr i)
    simp [this]
  refine ⟨_, column_mem_range L y kv hk, ?_, ?_⟩
  · intro l y' hy'
    simp [hy']
  · show ∑ l, HiddenLayout.foldW pos φ l * algebraMap K E (if y = y then kv l else 0) = e
    simp only [ite_true, kv, map_sum, mul_sum]
    rw [sum_comm, ← hc]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single (r i)]
    · simp [Algebra.smul_def, mul_comm]
    · intro l _ hl
      simp [Ne.symm hl]
    · simp

/-- A sum against the unit table of an index held by exactly one lane. -/
theorem sum_unitCol (pos : ι → (Fin 6 → Bool)) (hinj : Function.Injective pos) (a : ι)
    (b : Fin 6 → Bool) (hab : pos a = b) (f : ι → E) :
    ∑ l, unitCol (E := E) b (pos l) * f l = f a := by
  rw [sum_eq_single a]
  · simp [unitCol, hab]
  · intro l _ hl
    have : pos l ≠ b := fun h => hl (hinj (h.trans hab.symm))
    simp [unitCol, this]
  · simp

/-- **The padding meets the gadget's zero claim** (characteristic 2): at each of the gadget's
entries, a pair's two lanes hold the same value and the overflow lane holds zero. -/
theorem pattern_sum_zero [CharP E 2] (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos)
    (r : ι → Y → K) (p i : Fin 3) :
    ∑ l, patE (E := E) p (pos l) * algebraMap K E (L.stackR r l (L.gent p i)) = 0 := by
  have hpair : ∀ (q : Fin 2) (pp : Fin 3), (pp : ℕ) = q →
      L.stackR r (L.pairB q) (L.gent pp i) = L.stackR r (L.pairA q) (L.gent pp i) := by
    intro q pp hq
    have hg := atGadget_gent L pp i
    have hz : ∀ l, ¬ L.ZeroAt l (L.gent pp i) := fun l h =>
      not_atPat_gent L i (p := pp) (p' := 2) (by
        intro h2; subst h2; fin_cases q <;> simp_all) h.1
    rw [stackR_apply, stackR_apply,
      if_pos (show L.randPos (L.pairB q) (L.gent pp i) ∧ ¬ L.ZeroAt (L.pairB q) (L.gent pp i)
        from ⟨Or.inr (Or.inl hg), hz _⟩),
      if_pos (show L.randPos (L.pairA q) (L.gent pp i) ∧ ¬ L.ZeroAt (L.pairA q) (L.gent pp i)
        from ⟨Or.inr (Or.inl hg), hz _⟩)]
    congr 1
    fin_cases q
    · have hpp : pp = 0 := Fin.ext (by simpa using hq)
      subst hpp
      have h1 : ¬ L.AtPat 1 (L.gent 0 i) := not_atPat_gent L i (by decide)
      unfold GadgetLayout.copyOf
      rw [if_pos ⟨⟨i, rfl⟩, rfl⟩, if_neg fun h => L.pairA_ne_pairB 0 h.2, if_neg fun h => h1 h.1]
      rfl
    · have hpp : pp = 1 := Fin.ext (by simpa using hq)
      subst hpp
      have h0 : ¬ L.AtPat 0 (L.gent 1 i) := not_atPat_gent L i (by decide)
      unfold GadgetLayout.copyOf
      rw [if_neg fun h => h0 h.1, if_pos ⟨⟨i, rfl⟩, rfl⟩, if_neg fun h => h0 h.1,
        if_neg fun h => L.pairA_ne_pairB 1 h.2]
      rfl
  have hsplit : ∀ (a b : ι) (f : ι → E), pos a = lane 0 ∨ True →
      ∑ l, (unitCol (E := E) (pos a) (pos l) + unitCol (pos b) (pos l)) * f l = f a + f b := by
    intro a b f _
    rw [← sum_unitCol pos hP.inj a (pos a) rfl f, ← sum_unitCol pos hP.inj b (pos b) rfl f,
      ← sum_add_distrib]
    exact sum_congr rfl fun l _ => add_mul _ _ _
  fin_cases p
  · have hpat : ∀ x, patE (E := E) 0 x = unitCol (pos (L.pairA 0)) x + unitCol (pos (L.pairB 0)) x := by
      intro x
      simp [patE, pattern0, pairCol, flipC_lane0, hP.a0, hP.b0]
    simp only [Fin.zero_eta, Fin.isValue]
    simp_rw [hpat]
    rw [hsplit _ _ _ (Or.inr trivial), hpair 0 0 rfl]
    exact CharTwo.add_self_eq_zero _
  · have hpat : ∀ x, patE (E := E) 1 x = unitCol (pos (L.pairA 1)) x + unitCol (pos (L.pairB 1)) x := by
      intro x
      simp [patE, pattern1, pairCol, flipC_lane1, hP.a1, hP.b1]
    simp only [Fin.mk_one, Fin.isValue]
    simp_rw [hpat]
    rw [hsplit _ _ _ (Or.inr trivial), hpair 1 1 rfl]
    exact CharTwo.add_self_eq_zero _
  · have hpat : ∀ x, patE (E := E) 2 x = unitCol (pos L.ov) x := by
      intro x
      simp [patE, pattern2, hP.ov]
    simp only [Fin.reduceFinMk, Fin.isValue]
    simp_rw [hpat]
    rw [sum_unitCol pos hP.inj L.ov _ rfl, stackR_apply, if_neg]
    · simp
    · rintro ⟨-, hz⟩
      exact hz ⟨⟨i, rfl⟩, rfl⟩

theorem gadget_claim_stackR [CharP E 2] (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos)
    (β : Fin 3 → E) (r : ι → Y → K) :
    ∑ l, ∑ y, L.gadgetW pos β l y * algebraMap K E (L.stackR r l y) = 0 := by
  set z : ι → Y → E := fun l y => algebraMap K E (L.stackR r l y) with hz
  have hexp : ∀ l y, L.gadgetW pos β l y * z l y =
      ∑ p, ∑ i, if L.gent p i = y then β i * (patE p (pos l) * z l y) else 0 := by
    intro l y
    simp only [GadgetLayout.gadgetW, sum_mul]
    refine sum_congr rfl fun p _ => sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hcol : ∀ l, ∑ y, ∑ p, ∑ i, (if L.gent p i = y then β i * (patE p (pos l) * z l y) else 0)
      = ∑ p, ∑ i, β i * (patE p (pos l) * z l (L.gent p i)) := by
    intro l
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_ite_eq]
    simp
  calc ∑ l, ∑ y, L.gadgetW pos β l y * algebraMap K E (L.stackR r l y)
      = ∑ l, ∑ p, ∑ i, β i * (patE p (pos l) * z l (L.gent p i)) := by
        refine sum_congr rfl fun l _ => ?_
        rw [← hcol l]
        exact sum_congr rfl fun y _ => hexp l y
    _ = ∑ p, ∑ i, β i * ∑ l, patE p (pos l) * z l (L.gent p i) := by
        rw [sum_comm]
        refine sum_congr rfl fun p _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
    _ = 0 := sum_eq_zero fun p _ => sum_eq_zero fun i _ => by
        rw [show (∑ l, patE p (pos l) * z l (L.gent p i)) = 0 from pattern_sum_zero L pos hP r p i,
          mul_zero]

/-- **The randomness weighs nothing in the claims, the gadget's included.** -/
theorem claims_stackR [CharP E 2] (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos) {m : ℕ}
    (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (β : Fin 3 → E) (r : ι → Y → K) :
    HiddenLayout.claimsMap (K := K) (claimsW L pos Wc β) (L.stackR r) = 0 := by
  funext c
  show ∑ l, ∑ y, claimsW L pos Wc β c l y * algebraMap K E (L.stackR r l y) = 0
  refine Fin.lastCases ?_ (fun i => ?_) c
  · simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_last]
    exact gadget_claim_stackR L pos hP β r
  · simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_castSucc]
    refine sum_eq_zero fun l _ => sum_eq_zero fun y _ => ?_
    rw [stackR_apply]
    split_ifs with h
    · obtain ⟨hr, -⟩ := h
      have hw : Wc i l y = 0 := by
        rcases hr with hy | hg | hrl | ⟨rfl, hh⟩
        · exact hW.first i l y hy
        · exact hW.gadget i l y hg
        · exact hW.rand i l y hrl
        · exact hW.off_held i y hh
      rw [hw, zero_mul]
    · simp

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
    (hd : HiddenLayout.claimsMap (K := K) Wc (L.stackD d) = HiddenLayout.claimsMap Wc (L.stackD d')) :
    HiddenLayout.claimsMap (K := K) (claimsW L pos Wc β) (L.stackD d) =
      HiddenLayout.claimsMap (claimsW L pos Wc β) (L.stackD d') := by
  funext c
  refine Fin.lastCases ?_ (fun i => ?_) c
  · rw [claim_last_stackD L pos Wc β d, claim_last_stackD L pos Wc β d']
  · show ∑ l, ∑ y, claimsW L pos Wc β (Fin.castSucc i) l y * algebraMap K E (L.stackD d l y) =
      ∑ l, ∑ y, claimsW L pos Wc β (Fin.castSucc i) l y * algebraMap K E (L.stackD d' l y)
    simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_castSucc]
    exact congrFun hd i

end Lemmas

/-! ## The theorem -/

/-- **F3 for the gadget layout.** At challenges `(λ, φ)` meeting (S) and (R), with (Q) and
`WeightsFit`, the opening's view of two tables with the same claims, and anything computed from it
and the challenges, are identically distributed. -/
theorem view_evalDistEq [CharP E 2] [SampleableType (ι → Y → K)] (L : GadgetLayout ι Y)
    (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (hW : L.WeightsFit Wc) (β : Fin 3 → E) (enc : Q → Y → K)
    (hQ : Function.Surjective (firstEval enc L.first)) (lam : Fin (m + 1) → E) (φ : Fin 6 → E)
    (hS : FoldSpans (K := K) L pos φ)
    (hR : L.RoundsReached (K := K) pos (claimsW L pos Wc β) lam φ)
    {O : Type} (g : (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → O) {d d' : ι → Y → K}
    (hd : HiddenLayout.claimsMap (K := K) Wc (L.stackD d) =
      HiddenLayout.claimsMap Wc (L.stackD d')) :
    (fun r => g (levelMap L pos Wc β lam φ enc (L.stackD d + L.stackR r))) <$> ($ᵗ (ι → Y → K))
      =ᵈ (fun r => g (levelMap L pos Wc β lam φ enc (L.stackD d' + L.stackR r))) <$>
        ($ᵗ (ι → Y → K)) := by
  have hWb := combinedW_first L pos Wc hW β lam
  refine level0_view_evalDistEq (HiddenLayout.foldW pos φ) enc L.first
    (roundsMap pos φ (HiddenLayout.combinedW pos (claimsW L pos Wc β) lam))
    (HiddenLayout.claimsMap (claimsW L pos Wc β)) L.stackD L.stackR
    (LinearMap.ker (lastMap (K := K) φ))
    (fun T hT => onFirst_mem_range L T hT)
    (fun T hT => roundsMap_eq_zero pos φ _ L.first hWb T hT)
    (claims_stackR L pos hP Wc hW β) hQ (foldSpans_moves L pos φ hS) ?_ hR
    (claimsW_stackD_eq L pos Wc β hd) g
  intro T hT hfold
  refine roundsMap_mem_ker pos φ _ L.first hWb T ?_ hfold
  rw [HiddenLayout.ip_combinedW pos hP.inj, hT]
  simp

/-- The opening hides its table given its claims, in the joint argument's form (`Hides`), at every
challenge meeting (S) and (R). -/
theorem hides [CharP E 2] [SampleableType (ι → Y → K)] {Ch O : Type} (L : GadgetLayout ι Y)
    (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos) {m : ℕ} (Wc : Ch → Fin m → ι → Y → E)
    (β : Fin 3 → E) (enc : Ch → Q → Y → K) (lam : Ch → Fin (m + 1) → E) (φ : Ch → Fin 6 → E)
    (g : Ch → (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → O) (c : Ch)
    (hW : L.WeightsFit (Wc c)) (hQ : Function.Surjective (firstEval (enc c) L.first))
    (hS : FoldSpans (K := K) L pos (φ c))
    (hR : L.RoundsReached (K := K) pos (claimsW L pos (Wc c) β) (lam c) (φ c)) :
    Hides (fun c d (r : ι → Y → K) =>
        g c (levelMap L pos (Wc c) β (lam c) (φ c) (enc c) (L.stackD d + L.stackR r)))
      (fun c d => HiddenLayout.claimsMap (K := K) (Wc c) (L.stackD d)) c := by
  intro d d' hd
  exact view_evalDistEq L pos hP (Wc c) hW β (enc c) hQ (lam c) (φ c) hS hR (g c) hd

/-! ## Condition (S) fails rarely -/

theorem foldSpans_of_four (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) (φ : Fin 6 → E)
    (r0 rA rB rC : ι)
    (hr : ∀ i, L.isRand (![r0, rA, rB, rC] i) ∧ ∀ q, ![r0, rA, rB, rC] i ≠ L.pairA q)
    (h : Submodule.span K (Set.range
      ![eqW φ (pos r0), eqW φ (pos rA), eqW φ (pos rB), eqW φ (pos rC)]) = ⊤) :
    FoldSpans (K := K) L pos φ := by
  refine ⟨4, ![r0, rA, rB, rC], hr, ?_⟩
  convert h using 3
  funext i
  fin_cases i <;> rfl

open Classical in
/-- **(S) fails rarely for uniform challenges**: four random lanes with the coordinate pattern of
`card_not_span_four_le`. -/
theorem prob_not_foldSpans_le [Fintype K] [Fintype E] [DecidableEq E] [SampleableType E]
    [FiniteDimensional K E] (h3 : Module.finrank K E = 3) {Γ : Type} [SampleableType Γ]
    [Fintype Γ] (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) (r0 rA rB rC : ι)
    (hr : ∀ i, L.isRand (![r0, rA, rB, rC] i) ∧ ∀ q, ![r0, rA, rB, rC] i ≠ L.pairA q)
    (a b c : Fin 6) (hac : a ≠ c) (hb : pos r0 b ≠ pos rB b)
    (haB : pos rB a = pos r0 a) (haC : pos rC a = pos r0 a) (haA : pos rA a = !pos r0 a)
    (hcB : pos rB c = pos r0 c) (hcA : pos rA c = pos r0 c) (hcC : pos rC c = !pos r0 c) :
    Pr{let x ← $ᵗ (Γ × (Fin 6 → E))}[¬ FoldSpans (K := K) L pos x.2]
      ≤ (((2 * 6 + Fintype.card K + 1) * Fintype.card E + Fintype.card K ^ 4 : ℕ) : ENNReal) /
          ((Fintype.card E ^ 2 : ℕ) : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample]
  set bad := univ.filter fun φ : Fin 6 → E => Submodule.span K (Set.range
    ![eqW φ (pos r0), eqW φ (pos rA), eqW φ (pos rB), eqW φ (pos rC)]) ≠ ⊤
  have hsub : (univ.filter fun x : Γ × (Fin 6 → E) => ¬ FoldSpans (K := K) L pos x.2)
      ⊆ (univ : Finset Γ) ×ˢ bad := by
    intro x hx
    refine mem_product.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, fun htop => ?_⟩⟩
    exact (mem_filter.mp hx).2 (foldSpans_of_four L pos x.2 r0 rA rB rC hr htop)
  have hcard := card_not_span_four_le (K := K) h3 (pos r0) (pos rA) (pos rB) (pos rC) a b c hac
    hb haB haC haA hcB hcA hcC
  have hle := card_le_card hsub
  rw [card_product, card_univ] at hle
  have hE : 0 < Fintype.card E := Fintype.card_pos
  have hΓ : 0 < Fintype.card Γ := Fintype.card_pos
  have hcardT : Fintype.card (Γ × (Fin 6 → E)) = Fintype.card Γ * Fintype.card E ^ 6 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [hcardT]
  refine HiddenLayout.natCast_div_le_natCast_div (Nat.mul_pos hΓ (Nat.pow_pos hE))
    (Nat.pow_pos hE) ?_
  calc (univ.filter fun x : Γ × (Fin 6 → E) => ¬ FoldSpans (K := K) L pos x.2).card *
        Fintype.card E ^ 2
      ≤ (Fintype.card Γ * bad.card) * Fintype.card E ^ 2 := Nat.mul_le_mul_right _ hle
    _ = Fintype.card Γ * (bad.card * Fintype.card E ^ 2) := by ring
    _ ≤ Fintype.card Γ * (((2 * 6 + Fintype.card K + 1) * Fintype.card E +
          Fintype.card K ^ 4) * Fintype.card E ^ 6) := Nat.mul_le_mul_left _ hcard
    _ = _ := by ring

/-- At `|K| = 2^64`, `|E| = 2^192`, (S)'s bound is at most `3/2^128` (it is `2^-127 + 13·2^-192`). -/
theorem foldSpans_bound_le :
    (((2 * 6 + 2 ^ 64 + 1) * 2 ^ 192 + (2 ^ 64) ^ 4 : ℕ) : ENNReal) / (((2 ^ 192) ^ 2 : ℕ) : ENNReal)
      ≤ 3 / 2 ^ 128 := by
  have h := HiddenLayout.natCast_div_le_natCast_div (a := (2 * 6 + 2 ^ 64 + 1) * 2 ^ 192 + (2 ^ 64) ^ 4)
    (b := (2 ^ 192) ^ 2) (c := 3) (d := 2 ^ 128) (by positivity) (by positivity) (by norm_num)
  refine h.trans (le_of_eq ?_)
  norm_num

/-- The deployed random lanes `35, 34, 33, 39` (of the cube `32 .. 40`) have the pattern of
`prob_not_foldSpans_le` at `a, b, c = 0, 1, 2`. -/
theorem deployed_lane_pattern :
    laneBits 35 1 ≠ laneBits 33 1 ∧
    laneBits 33 0 = laneBits 35 0 ∧ laneBits 39 0 = laneBits 35 0 ∧ laneBits 34 0 = !laneBits 35 0 ∧
    laneBits 33 2 = laneBits 35 2 ∧ laneBits 34 2 = laneBits 35 2 ∧ laneBits 39 2 = !laneBits 35 2 := by
  decide

/-! ## (S) and (R) for every good challenge (`GadgetLayout.roundsReached`, `Solve.lean`)

The gadget makes (R) hold for every challenge outside a small explicit set (`HIDING.md`, "Condition
(R) for every challenge"): `GoodCh φ λ` — no coordinate of `φ` in `{0, 1}`, at most one of
`φ₀, φ₁, φ₂` in `K` (`¬ TwoInK`), and `λ ≠ 0` (the gadget's scale `λ^m`). There, with the lower half
of the lane indices and the cube `32 .. 40` on the stack (`hlow`, `hrand`), (S) holds by the cube
lemma (`span_cube_erase`) and (R) by `GadgetLayout.roundsReached` (`hsolve_of_cube`), so the
opening hides its table (`view_evalDistEq_of_good`) under (Q) and `WeightsFit` alone. -/

/-- The challenges at which the gadget layout's opening hides: `φ` avoids `{0, 1}` coordinatewise,
at most one of `φ₀, φ₁, φ₂` lies in `K`, and the batching challenge `λ` is not zero. -/
def GoodCh (φ : Fin 6 → E) (lam : E) : Prop :=
  ((∀ i, φ i ≠ 0 ∧ φ i ≠ 1) ∧ ¬ TwoInK (K := K) φ) ∧ lam ≠ 0

/-- The batching powers `λ^c`, the gadget's `λ^m` the last. -/
def powers (m : ℕ) (lam : E) : Fin (m + 1) → E := fun c => lam ^ (c : ℕ)

section Good

variable (L : GadgetLayout ι Y)

/-- (S) from a span of fold weights of random lanes, none a pair's first lane. -/
theorem foldSpans_of_span (pos : ι → (Fin 6 → Bool)) (φ : Fin 6 → E) (R : Finset ι)
    (hR : ∀ l ∈ R, L.isRand l ∧ ∀ q, l ≠ L.pairA q)
    (h : Submodule.span K ((fun l => HiddenLayout.foldW pos φ l) '' (R : Set ι)) = ⊤) :
    FoldSpans (K := K) L pos φ := by
  refine ⟨R.card, fun i => (R.equivFin.symm i : ι), fun i => hR _ (R.equivFin.symm i).2, ?_⟩
  rw [← h]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, (R.equivFin.symm i).2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨R.equivFin ⟨l, hl⟩, ?_⟩
    simp

/-- **(S) outside the bad set**: the random lanes `33 .. 40` span by the cube lemma. -/
theorem foldSpans_of_good [FiniteDimensional K E] (h3 : Module.finrank K E = 3)
    (pos : ι → (Fin 6 → Bool))
    (hrand : ∀ b ∈ cube true, b ≠ lane 32 → ∃ l, pos l = b ∧ L.isRand l ∧ ∀ q, l ≠ L.pairA q)
    (φ : Fin 6 → E) (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (hK : ¬ TwoInK (K := K) φ) :
    FoldSpans (K := K) L pos φ := by
  classical
  set R := univ.filter fun l : ι => L.isRand l ∧ ∀ q, l ≠ L.pairA q
  refine foldSpans_of_span L pos φ R (fun l hl => (mem_filter.mp hl).2) ?_
  rw [eq_top_iff, ← span_cube_erase h3 φ hφ hK]
  refine Submodule.span_mono ?_
  rintro _ ⟨b, ⟨hb, hb32⟩, rfl⟩
  obtain ⟨l, hpl, hr, ha⟩ := hrand b hb hb32
  exact ⟨l, by simp [R, hr, ha], by simp [HiddenLayout.foldW, hpl]⟩

/-- The gadget's patterns sit on lanes of the stack. -/
theorem patE_mem_range (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos) (p : Fin 3)
    (b : Fin 6 → Bool) (hb : patE (E := E) p b ≠ 0) : b ∈ Set.range pos := by
  fin_cases p
  · by_cases h0 : b = lane 0
    · exact ⟨L.pairA 0, hP.a0.trans h0.symm⟩
    by_cases h31 : b = lane 31
    · exact ⟨L.pairB 0, hP.b0.trans h31.symm⟩
    exact absurd (by simp [patE, pattern0, pairCol, flipC_lane0, unitCol, h0, h31]) hb
  · by_cases h1 : b = lane 1
    · exact ⟨L.pairA 1, hP.a1.trans h1.symm⟩
    by_cases h30 : b = lane 30
    · exact ⟨L.pairB 1, hP.b1.trans h30.symm⟩
    exact absurd (by simp [patE, pattern1, pairCol, flipC_lane1, unitCol, h1, h30]) hb
  · by_cases h32 : b = lane 32
    · exact ⟨L.ov, hP.ov.trans h32.symm⟩
    exact absurd (by simp [patE, pattern2, unitCol, h32]) hb

/-- At the gadget's entries, the batched weight is the gadget's, scaled by its power. -/
theorem combinedW_gent (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos) {m : ℕ}
    (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (β : Fin 3 → E) (lam : Fin (m + 1) → E)
    (p i : Fin 3) (b : Fin 6 → Bool) :
    HiddenLayout.combinedW pos (claimsW L pos Wc β) lam b (L.gent p i) =
      lam (Fin.last m) * β i * patE p b := by
  have hG : ∀ l, L.gadgetW pos β l (L.gent p i) = β i * patE p (pos l) := by
    intro l
    unfold GadgetLayout.gadgetW
    rw [sum_eq_single p, sum_eq_single i]
    · simp
    · intro i' _ hi'
      rw [if_neg]
      intro h
      exact hi' (L.gent_inj p i' p i h).2
    · simp
    · intro p' _ hp'
      refine sum_eq_zero fun i' _ => ?_
      rw [if_neg]
      intro h
      exact hp' (L.gent_inj p' i' p i h).1
    · simp
  have hc : ∀ l, ∑ c, lam c * claimsW L pos Wc β c l (L.gent p i) =
      lam (Fin.last m) * (β i * patE p (pos l)) := by
    intro l
    rw [Fin.sum_univ_castSucc]
    simp only [claimsW, GadgetLayout.withGadget, Fin.snoc_castSucc, Fin.snoc_last, hG]
    rw [sum_eq_zero fun j _ => by rw [hW.gadget j l _ (atGadget_gent L p i), mul_zero], zero_add]
  simp only [HiddenLayout.combinedW, hc]
  by_cases hb : b ∈ Set.range pos
  · obtain ⟨l₀, rfl⟩ := hb
    rw [sum_eq_single l₀]
    · simp [mul_assoc]
    · intro l _ hl
      simp [hP.inj.ne hl]
    · simp
  · have hz : patE (E := E) p b = 0 := by
      by_contra h
      exact hb (patE_mem_range L pos hP p b h)
    rw [hz, mul_zero]
    refine sum_eq_zero fun l _ => ?_
    have : pos l ≠ b := fun h => hb ⟨l, h⟩
    simp [this]

/-- **(R) outside the bad set**, from `GadgetLayout.roundsReached` and the cube lemma. -/
theorem roundsReached_of_good [CharP E 2] [FiniteDimensional K E] (h3 : Module.finrank K E = 3)
    (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos)
    (hlow : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range pos)
    (hrand : ∀ b ∈ cube true, b ≠ lane 32 → ∃ l, pos l = b ∧ L.isRand l ∧ ∀ q, l ≠ L.pairA q)
    {m : ℕ} (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (β : Module.Basis (Fin 3) K E)
    (lam : Fin (m + 1) → E) (hμ : lam (Fin.last m) ≠ 0) (φ : Fin 6 → E)
    (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (hK : ¬ TwoInK (K := K) φ) :
    L.RoundsReached (K := K) pos (claimsW L pos Wc β) lam φ := by
  have h2K : (2 : K) = 0 := (algebraMap K E).injective (by rw [map_ofNat, map_zero]; exact CharTwo.two_eq_zero)
  have hup : cube true ⊆ Set.range pos := by
    intro b hb
    by_cases h32 : b = lane 32
    · exact ⟨L.ov, hP.ov.trans h32.symm⟩
    · obtain ⟨l, hl, -⟩ := hrand b hb h32
      exact ⟨l, hl⟩
  have h33 : lane 33 ∈ Set.range pos := hup ⟨by decide, by decide, by decide⟩
  refine L.roundsReached h2K pos hP.inj (claimsW L pos Wc β) lam φ (lam (Fin.last m)) hμ β
    (fun p i b => combinedW_gent L pos hP Wc hW β lam p i b) hP.a0 hP.b0 hP.a1 hP.b1 hP.ov hlow
    h33 hφ (by simp [CharTwo.two_eq_zero]) (hsolve_of_cube h3 φ hφ hK _ hup hlow)

/-- **The gadget layout's opening hides its table at every good challenge**, under (Q) and
`WeightsFit` (and the layout's lanes): (S) and (R) are discharged. -/
theorem view_evalDistEq_of_good [CharP E 2] [FiniteDimensional K E] [SampleableType (ι → Y → K)]
    (h3 : Module.finrank K E = 3) (pos : ι → (Fin 6 → Bool)) (hP : Placed L pos)
    (hlow : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range pos)
    (hrand : ∀ b ∈ cube true, b ≠ lane 32 → ∃ l, pos l = b ∧ L.isRand l ∧ ∀ q, l ≠ L.pairA q)
    {m : ℕ} (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (β : Module.Basis (Fin 3) K E)
    (enc : Q → Y → K) (hQ : Function.Surjective (firstEval enc L.first)) (lam : E)
    (φ : Fin 6 → E) (hg : GoodCh (K := K) φ lam)
    {O : Type} (g : (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → O) {d d' : ι → Y → K}
    (hd : HiddenLayout.claimsMap (K := K) Wc (L.stackD d) =
      HiddenLayout.claimsMap Wc (L.stackD d')) :
    (fun r => g (levelMap L pos Wc β (powers m lam) φ enc (L.stackD d + L.stackR r))) <$>
        ($ᵗ (ι → Y → K))
      =ᵈ (fun r => g (levelMap L pos Wc β (powers m lam) φ enc (L.stackD d' + L.stackR r))) <$>
        ($ᵗ (ι → Y → K)) :=
  view_evalDistEq L pos hP Wc hW β enc hQ (powers m lam) φ
    (foldSpans_of_good L h3 pos hrand φ hg.1.1 hg.1.2)
    (roundsReached_of_good L h3 pos hP hlow hrand Wc hW β (powers m lam)
      (pow_ne_zero _ hg.2) φ hg.1.1 hg.1.2) g hd

end Good

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
