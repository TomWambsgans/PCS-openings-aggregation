-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Gadget

/-!
# The hidden layouts with the gadget (`opening::Layout::hidden` since the gadget)

`crates/quotient/HIDING.md`, "The layout". A stack has lanes `ι` at lane indices `pos l` and
entries `Y`. Its unknowns:

* the entries `first` (every lane's first piece below the gadget, `0 .. D`) are uniform in every lane;
* the **gadget's entries** `gent p i` (pattern `p`, entry `i`) are uniform in every lane, but pattern
  `p < 2`'s second lane `pairB p` holds its first lane `pairA p`'s value there, and the overflow lane
  `ov` holds zero at pattern 2's;
* the **random lanes** (`isRand`) are uniform;
* the **overflow lane** holds the table at the entries `held`, and is uniform elsewhere;
* every other entry is the table's.

The stack is `stackD d + stackR r`, `r` uniform. The claims weigh the table's entries; the **gadget**
is one more claim, of value zero, with weight `gadgetW β` (`β i` on pattern `p`'s lanes at its entry
`i`), which `stackR` meets in characteristic 2 (a pair holds one value twice, the overflow lane zero).
-/

namespace QuotientSecurity.Hiding

open Finset

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

/-- A hidden layout with the gadget. -/
structure GadgetLayout (ι Y : Type) where
  isRand : ι → Prop
  [decRand : DecidablePred isRand]
  /-- The overflow lane (pattern 2's lane). -/
  ov : ι
  /-- The weightless random entries of every lane: the first piece below the gadget. -/
  first : Finset Y
  /-- The overflow lane's table entries. -/
  held : Finset Y
  /-- The gadget's entries: pattern `p`, entry `i`. -/
  gent : Fin 3 → Fin 3 → Y
  /-- Patterns 0 and 1: the lane holding the pair's value, and the lane copying it. -/
  pairA : Fin 2 → ι
  pairB : Fin 2 → ι
  gent_inj : ∀ p i p' i', gent p i = gent p' i' → p = p' ∧ i = i'
  gent_first : ∀ p i, gent p i ∉ first
  gent_held : ∀ p i, gent p i ∉ held
  held_first : Disjoint held first
  not_rand_ov : ¬ isRand ov
  not_rand_pairB : ∀ p, ¬ isRand (pairB p)
  pairB_ne_ov : ∀ p, pairB p ≠ ov
  pairA_ne_pairB : ∀ p, pairA p ≠ pairB p

attribute [instance] GadgetLayout.decRand

namespace GadgetLayout

variable (L : GadgetLayout ι Y)

/-- Entry `y` is one of pattern `p`'s. -/
def AtPat (p : Fin 3) (y : Y) : Prop := ∃ i, L.gent p i = y

instance (p : Fin 3) (y : Y) : Decidable (L.AtPat p y) := by
  unfold AtPat; infer_instance

/-- Entry `y` is one of the gadget's. -/
def AtGadget (y : Y) : Prop := ∃ p, L.AtPat p y

instance (y : Y) : Decidable (L.AtGadget y) := by
  unfold AtGadget; infer_instance

/-- The stack's random entries (before the gadget's copies and zeros). -/
def randPos (l : ι) (y : Y) : Prop :=
  y ∈ L.first ∨ L.AtGadget y ∨ L.isRand l ∨ (l = L.ov ∧ y ∉ L.held)

instance (l : ι) (y : Y) : Decidable (L.randPos l y) := by
  unfold randPos; infer_instance

/-- The lane whose random value entry `y` of lane `l` holds: a pair's second lane copies its first at
the pair's entries. -/
def copyOf (y : Y) (l : ι) : ι :=
  if L.AtPat 0 y ∧ l = L.pairB 0 then L.pairA 0
  else if L.AtPat 1 y ∧ l = L.pairB 1 then L.pairA 1 else l

/-- The overflow lane is zero at pattern 2's entries. -/
def ZeroAt (l : ι) (y : Y) : Prop := L.AtPat 2 y ∧ l = L.ov

instance (l : ι) (y : Y) : Decidable (L.ZeroAt l y) := by
  unfold ZeroAt; infer_instance

/-- The randomness's part of the stack. -/
def stackR : (ι → Y → K) →ₗ[K] (ι → Y → K) where
  toFun r l y := if L.randPos l y ∧ ¬ L.ZeroAt l y then r (L.copyOf y l) y else 0
  map_add' r r' := by
    funext l y
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c r := by
    funext l y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The table's part of the stack. -/
def stackD : (ι → Y → K) →ₗ[K] (ι → Y → K) where
  toFun d l y := if L.randPos l y then 0 else d l y
  map_add' d d' := by
    funext l y
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c d := by
    funext l y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The gadget's weight: `β i` times pattern `p`'s lanes (by lane index) at its entry `i`. -/
def gadgetW (pos : ι → (Fin 6 → Bool)) (β : Fin 3 → E) : ι → Y → E := fun l y =>
  ∑ p : Fin 3, ∑ i : Fin 3, if L.gent p i = y then β i * patE p (pos l) else 0

/-- The weights a design's claims put: nothing on the first pieces, at the gadget's entries, on the
random lanes, nor on the overflow lane off `held`. -/
structure WeightsFit {m : ℕ} (Wc : Fin m → ι → Y → E) : Prop where
  first : ∀ c l, ∀ y ∈ L.first, Wc c l y = 0
  gadget : ∀ c l y, L.AtGadget y → Wc c l y = 0
  rand : ∀ c l y, L.isRand l → Wc c l y = 0
  off_held : ∀ c y, y ∉ L.held → Wc c L.ov y = 0

/-- The claims with the gadget as the last, of value zero. -/
def withGadget {m : ℕ} (Wc : Fin m → ι → Y → E) (G : ι → Y → E) : Fin (m + 1) → ι → Y → E :=
  Fin.snoc Wc G

/-- **Condition (R)** for a layout with the gadget: through the lane rounds, the changes of the
randomness that keep `f¹` span the round values whose last running claim is unchanged. -/
def RoundsReached {m : ℕ} (pos : ι → (Fin 6 → Bool)) (Wc : Fin m → ι → Y → E) (lam : Fin m → E)
    (φ : Fin 6 → E) : Prop :=
  LinearMap.ker (lastMap (K := K) φ) ≤ Submodule.span K
    (roundsMap pos φ (HiddenLayout.combinedW pos Wc lam) ''
      kerMoves (HiddenLayout.foldW pos φ) L.first (LinearMap.range (L.stackR (K := K))))

end GadgetLayout

/-! ### Condition (R), discharged -/

theorem sum_pos_eq {pos : ι → (Fin 6 → Bool)} (hpos : Function.Injective pos) {M : Type}
    [AddCommMonoid M] (g : (Fin 6 → Bool) → M) (hg : ∀ b, b ∉ Set.range pos → g b = 0) :
    ∑ l, g (pos l) = ∑ b, g b := by
  classical
  rw [← sum_image (fun a _ b _ h => hpos h)]
  refine sum_subset (subset_univ _) fun b _ hb => hg b ?_
  rintro ⟨l, rfl⟩
  exact hb (mem_image_of_mem _ (mem_univ l))

theorem lift_column {pos : ι → (Fin 6 → Bool)} (hpos : Function.Injective pos) (f : (Fin 6 → Bool) → K)
    (hf : ∀ b, b ∉ Set.range pos → f b = 0) (y : Y) (b : Fin 6 → Bool) :
    lift (E := E) pos (fun l y' => if y' = y then f (pos l) else 0) b y = algebraMap K E (f b) := by
  simp only [lift, ite_true]
  by_cases hb : b ∈ Set.range pos
  · obtain ⟨l₀, rfl⟩ := hb
    rw [sum_eq_single l₀]
    · simp
    · intro l _ hl
      simp [hpos.ne hl]
    · simp
  · rw [hf b hb, map_zero]
    refine sum_eq_zero fun l _ => ?_
    have : pos l ≠ b := fun h => hb ⟨l, h⟩
    simp [this]

theorem colIp_unit_left {k : ℕ} (a : Fin k → Bool) (t : Col E k) : colIp (unitCol a) t = t a := by
  simp only [colIp, unitCol, ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq']
  simp

namespace GadgetLayout

variable (L : GadgetLayout ι Y)

theorem atPat_gent {p q : Fin 3} {i : Fin 3} (h : L.AtPat q (L.gent p i)) : q = p := by
  obtain ⟨i', hi'⟩ := h
  exact (L.gent_inj q i' p i hi').1

theorem atGadget_gent (p i : Fin 3) : L.AtGadget (L.gent p i) := ⟨p, i, rfl⟩

/-- **Condition (R) holds** for a layout with the gadget, for every challenge with no coordinate in
`{0, 1}` and `2 φ₀ ≠ 1`, every nonzero scale `μ` of the gadget, every basis `β` of `E` over `K`,
whatever the claims (`hWg`: the combined weight at the gadget's entries is the gadget's), given the
lanes the argument uses and the solvers' span (`hsolve`). `K` has characteristic 2. -/
theorem roundsReached {m : ℕ} (h2K : (2 : K) = 0) (pos : ι → (Fin 6 → Bool))
    (hpos : Function.Injective pos) (Wc : Fin m → ι → Y → E) (lam : Fin m → E) (φ : Fin 6 → E)
    (μ : E) (hμ : μ ≠ 0) (β : Module.Basis (Fin 3) K E)
    (hWg : ∀ p i b, HiddenLayout.combinedW pos Wc lam b (L.gent p i) = μ * β i * patE p b)
    (hA0 : pos (L.pairA 0) = lane 0) (hB0 : pos (L.pairB 0) = lane 31)
    (hA1 : pos (L.pairA 1) = lane 1) (hB1 : pos (L.pairB 1) = lane 30) (hov : pos L.ov = lane 32)
    (hlow : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range pos)
    (h33 : lane 33 ∈ Set.range pos) (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (h2 : 2 * φ 0 ≠ 1)
    (hsolve : ∀ (p : Fin 3) (e : E), ∃ s : (Fin 6 → Bool) → K, OnOther p (ofK (E := E) s) ∧
      (∀ b, b ∉ Set.range pos → s b = 0) ∧ (∑ b, eqW φ b * algebraMap K E (s b)) = e) :
    L.RoundsReached (K := K) pos Wc lam φ := by
  refine (column_reach φ hφ h2 μ hμ β (Set.range pos) hlow h33 hsolve).trans (Submodule.span_mono ?_)
  rintro x ⟨p, i, c, s, hcs, hc, hs, hip, hf, rfl⟩
  set f : (Fin 6 → Bool) → K := c + s
  have hfS : ∀ b, b ∉ Set.range pos → f b = 0 := fun b hb => by
    simp [f, (hcs b hb).1, (hcs b hb).2]
  set y := L.gent p i
  set T : ι → Y → K := fun l y' => if y' = y then f (pos l) else 0
  -- What the pattern's claim and the halves give: the pair's lanes agree, the overflow lane is zero.
  have hsep : (Lower (patE (E := E) p) ∧ Upper (ofK (E := E) s)) ∨
      (Upper (patE (E := E) p) ∧ Lower (ofK (E := E) s)) := sep_of p hs
  have hs0 : ∀ b, patE (E := E) p b ≠ 0 → s b = 0 := by
    intro b hb
    rcases hsep with ⟨hw, ht⟩ | ⟨hw, ht⟩ <;> cases hlast : b (Fin.last 5)
    · exact (algebraMap K E).injective (by simpa [ofK] using ht b hlast)
    · exact absurd (hw b hlast) hb
    · exact absurd (hw b hlast) hb
    · exact (algebraMap K E).injective (by simpa [ofK] using ht b hlast)
  have hf0 : p = 0 → f (lane 0) = f (lane 31) := by
    rintro rfl
    have h := hip
    simp only [patE, pattern0, pairCol, colIp_add_left, colIp_smul_left, colIp_unit_left, one_mul,
      flipC_lane0, ofK, ← map_add] at h
    have hc' : c (lane 31) = c (lane 0) := by
      have h' := (algebraMap K E).injective (h.trans (map_zero _).symm)
      linear_combination h' - c (lane 0) * h2K
    have h0 : s (lane 0) = 0 := hs0 _ (by
      simp [patE, pattern0, pairCol, unitCol, flipC_lane0, show lane 0 ≠ lane 31 by decide])
    have h31 : s (lane 31) = 0 := hs0 _ (by
      simp [patE, pattern0, pairCol, unitCol, flipC_lane0, show lane 31 ≠ lane 0 by decide])
    simp [f, hc', h0, h31]
  have hf1 : p = 1 → f (lane 1) = f (lane 30) := by
    rintro rfl
    have h := hip
    simp only [patE, pattern1, pairCol, colIp_add_left, colIp_smul_left, colIp_unit_left, one_mul,
      flipC_lane1, ofK, ← map_add] at h
    have hc' : c (lane 30) = c (lane 1) := by
      have h' := (algebraMap K E).injective (h.trans (map_zero _).symm)
      linear_combination h' - c (lane 1) * h2K
    have h1 : s (lane 1) = 0 := hs0 _ (by
      simp [patE, pattern1, pairCol, unitCol, flipC_lane1, show lane 1 ≠ lane 30 by decide])
    have h30 : s (lane 30) = 0 := hs0 _ (by
      simp [patE, pattern1, pairCol, unitCol, flipC_lane1, show lane 30 ≠ lane 1 by decide])
    simp [f, hc', h1, h30]
  have hf2 : p = 2 → f (lane 32) = 0 := by
    rintro rfl
    have h := hip
    simp only [patE, pattern2, colIp_unit_left, ofK] at h
    have hc' : c (lane 32) = 0 := (algebraMap K E).injective (h.trans (map_zero _).symm)
    have h32 : s (lane 32) = 0 := hs0 _ (by simp [patE, pattern2, unitCol])
    simp [f, hc', h32]
  refine ⟨T, ⟨⟨T, ?_⟩, y, L.gent_first p i, fun l y' hy' => by simp [T, hy'], ?_⟩, ?_⟩
  · -- `T` is a change of the randomness: it keeps the pairs' copies and the overflow lane's zeros.
    funext l y'
    show (if L.randPos l y' ∧ ¬ L.ZeroAt l y' then T (L.copyOf y' l) y' else 0) = T l y'
    by_cases hy : y' = y
    · subst hy
      have hr : L.randPos l y := Or.inr (Or.inl (L.atGadget_gent p i))
      by_cases hz : L.ZeroAt l y
      · have hp := L.atPat_gent hz.1
        have hl : l = L.ov := hz.2
        have hnz : ¬ (L.randPos l y ∧ ¬ L.ZeroAt l y) := fun h => h.2 hz
        rw [if_neg hnz]
        simp only [T, ite_true, hl, hov, hf2 hp.symm]
      · simp only [hr, hz, not_false_eq_true, and_self, ite_true, T]
        unfold copyOf
        split_ifs with h0 h1
        · obtain ⟨hp, rfl⟩ := h0
          rw [hA0, hB0, hf0 (L.atPat_gent hp).symm]
        · obtain ⟨hp, rfl⟩ := h1
          rw [hA1, hB1, hf1 (L.atPat_gent hp).symm]
        · rfl
    · simp [T, hy]
  · -- `T` keeps `f¹` at its entry.
    show ∑ l, HiddenLayout.foldW pos φ l * algebraMap K E (T l y) = 0
    simp only [T, ite_true, HiddenLayout.foldW]
    rw [sum_pos_eq hpos (fun b => eqW φ b * algebraMap K E (f b)) (fun b hb => by simp [hfS b hb])]
    simpa [f] using hf
  · -- Its rounds are the move's.
    show laneRounds 6 φ (HiddenLayout.combinedW pos Wc lam) (lift pos T) = _
    rw [laneRounds_column 6 φ _ (lift pos T) y (fun b y' hy' => by simp [lift, T, hy'])]
    have hw : (fun b (_ : Unit) => HiddenLayout.combinedW pos Wc lam b y) = (μ * β i) • toT (patE p) := by
      funext b u
      simp [hWg, toT, y, mul_assoc]
    have ht : (fun b (_ : Unit) => lift (E := E) pos T b y) = toT (ofK f) := by
      funext b u
      simp only [toT, ofK, T]
      exact lift_column hpos f hfS y b
    rw [hw, ht, laneRounds_smul_left]
    rfl

end GadgetLayout

/-! ### The randomness, the claims, and `HIDING.md`'s theorem for the gadget layouts -/

namespace GadgetLayout

open OracleComp

variable (L : GadgetLayout ι Y)

theorem not_atPat_of_first {p : Fin 3} {y : Y} (hy : y ∈ L.first) : ¬ L.AtPat p y := by
  rintro ⟨i, rfl⟩
  exact L.gent_first p i hy

/-- The randomness covers every stack that is zero but on the first pieces. -/
theorem onFirst_mem_range (T : ι → Y → K) (hT : OnFirst L.first T) :
    T ∈ LinearMap.range (L.stackR (K := K)) := by
  refine ⟨T, ?_⟩
  funext l y
  show (if L.randPos l y ∧ ¬ L.ZeroAt l y then T (L.copyOf y l) y else 0) = T l y
  by_cases hy : y ∈ L.first
  · have hz : ¬ L.ZeroAt l y := fun h => L.not_atPat_of_first hy h.1
    have hc : L.copyOf y l = l := by
      simp [copyOf, L.not_atPat_of_first hy]
    rw [if_pos ⟨Or.inl hy, hz⟩, hc]
  · rw [hT l y hy]
    split_ifs
    · exact hT _ y hy
    · rfl

/-- A change at one entry on random lanes is a change of the randomness. -/
theorem column_mem_range (hA : ∀ p, ¬ L.isRand (L.pairA p)) (y : Y) (k : ι → K)
    (hk : ∀ l, k l ≠ 0 → L.isRand l) :
    (fun l y' => if y' = y then k l else 0) ∈ LinearMap.range (L.stackR (K := K)) := by
  refine ⟨fun l y' => if y' = y then k l else 0, ?_⟩
  funext l y'
  show (if L.randPos l y' ∧ ¬ L.ZeroAt l y' then
      (if y' = y then k (L.copyOf y' l) else 0) else 0) = if y' = y then k l else 0
  by_cases hy : y' = y
  · simp only [hy, ite_true]
    by_cases hkl : k l = 0
    · rw [hkl]
      split_ifs
      · unfold copyOf
        split_ifs with h0 h1
        · by_contra hne; exact hA 0 (hk _ hne)
        · by_contra hne; exact hA 1 (hk _ hne)
        · exact hkl
      · rfl
    · have hr := hk l hkl
      have hz : ¬ L.ZeroAt l y := fun h => L.not_rand_ov (h.2 ▸ hr)
      have hc : L.copyOf y l = l := by
        unfold copyOf
        have h0 : l ≠ L.pairB 0 := fun h => L.not_rand_pairB 0 (h ▸ hr)
        have h1 : l ≠ L.pairB 1 := fun h => L.not_rand_pairB 1 (h ▸ hr)
        simp [h0, h1]
      rw [if_pos ⟨Or.inr (Or.inr (Or.inl hr)), hz⟩, hc]
  · simp [hy]

/-- **Condition (S)** for a layout with the gadget: random lanes whose fold weights span `E`. -/
def FoldSpans (pos : ι → (Fin 6 → Bool)) (φ : Fin 6 → E) : Prop :=
  ∃ (p : ℕ) (r : Fin p → ι), (∀ i, L.isRand (r i)) ∧
    Submodule.span K (Set.range fun i => HiddenLayout.foldW pos φ (r i)) = ⊤

/-- (S) lets the randomness at any entry past the first piece move `f¹` anywhere. -/
theorem foldSpans_moves (hA : ∀ p, ¬ L.isRand (L.pairA p)) (pos : ι → (Fin 6 → Bool))
    (φ : Fin 6 → E) (hS : L.FoldSpans (K := K) pos φ) :
    ∀ y ∉ L.first, ∀ e : E, ∃ ρ ∈ LinearMap.range (L.stackR (K := K)),
      OnColumn y ρ ∧ foldMap (HiddenLayout.foldW pos φ) ρ y = e := by
  classical
  obtain ⟨p, r, hr, htop⟩ := hS
  intro y _ e
  have he : e ∈ Submodule.span K (Set.range fun i => HiddenLayout.foldW pos φ (r i)) :=
    htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp he
  set kv : ι → K := fun l => ∑ i, if r i = l then c i else 0
  have hk : ∀ l, kv l ≠ 0 → L.isRand l := by
    intro l hl
    by_contra hno
    apply hl
    refine sum_eq_zero fun i _ => ?_
    have : r i ≠ l := fun h => hno (h ▸ hr i)
    simp [this]
  refine ⟨_, L.column_mem_range hA y kv hk, ?_, ?_⟩
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

end GadgetLayout

end QuotientSecurity.Hiding
