-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Core

/-!
# The level-0 view of a WHIR opening, and why it hides the table

A committed **stack** is `K`-valued, `ι` lanes of entries `Y` (`T l y`). Up to and including its
first fold, a WHIR opening shows three families of `K`-linear forms of the stack (`viewMap`):

* **(V1)** the lane rounds (`rounds`, any `K`-linear map; `Hiding.Rounds` gives WHIR's);
* **(V2)** the folded table `f¹(y) = Σ_l ε_l T_l(y)` (`foldMap`), `ε_l ∈ E` the lane fold weights;
* **(V3)** the opened rows: every lane's codeword at each opened position `x ∈ Q`,
  `Σ_y enc x y · T_l(y)` (`rowsMap`).

Everything WHIR shows later is a function of `f¹` and the challenges, so this is the whole view.

The entries `first ⊆ Y` (each lane's first piece) are random in every lane and carry no weight. The
randomness spans a subspace `rand` of stacks. **`level0_hides`**: under

* **(Q)** the first piece's codeword at `Q` takes every value (`|Q| ≤ |first|` for a polynomial code
  whose first piece is the polynomials of degree below `|first|`),
* **(S)** at each entry past the first piece, the randomness there moves `f¹` anywhere in `E`,
* **(H)** a change keeping the claims and `f¹` (past the first piece) moves the rounds inside `H`
  (for WHIR's rounds, `H` is where the last running claim is unchanged: `Rounds.roundsMap_mem_ker`),
* **(R)** the randomness that keeps `f¹` spans `H` through the rounds,

every change `Δ` of the stack that keeps the claims is cancelled, in the whole view, by a change of
the randomness. With `Core.hiding_of_mem_range` the view of two tables with the same claims is then
identically distributed (`level0_view_evalDistEq`). This is the argument of `crates/quotient/HIDING.md`
("Why it hides", steps 1 and 2), for an arbitrary layout.
-/

namespace QuotientSecurity.Hiding

open Finset

section Model

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q]
  [DecidableEq Q]

/-- **(V2)** The folded table `f¹(y) = Σ_l ε_l T_l(y)`. -/
def foldMap (ε : ι → E) : (ι → Y → K) →ₗ[K] (Y → E) where
  toFun T y := ∑ l, ε l * algebraMap K E (T l y)
  map_add' T T' := by
    funext y
    simp [mul_add, sum_add_distrib]
  map_smul' c T := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, mul_sum, Algebra.smul_def]
    refine sum_congr rfl fun l _ => ?_
    ring

/-- A lane's codeword at the opened positions. -/
def encMap (enc : Q → Y → K) : (Y → K) →ₗ[K] (Q → K) where
  toFun z x := ∑ y, enc x y * z y
  map_add' z z' := by
    funext x
    simp [mul_add, sum_add_distrib]
  map_smul' c z := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    ring

/-- **(V3)** The opened rows: at `x ∈ Q`, every lane's codeword. -/
def rowsMap (enc : Q → Y → K) : (ι → Y → K) →ₗ[K] (Q → ι → K) where
  toFun T x l := encMap enc (T l) x
  map_add' T T' := by
    funext x l
    simp
  map_smul' c T := by
    funext x l
    simp

/-- The codeword at the opened positions of a lane whose entries past the first piece are zero. -/
def firstEval (enc : Q → Y → K) (first : Finset Y) : (Y → K) →ₗ[K] (Q → K) where
  toFun z x := ∑ y ∈ first, enc x y * z y
  map_add' z z' := by
    funext x
    simp [mul_add, sum_add_distrib]
  map_smul' c z := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    ring

/-- The view up to the first fold: (V1), (V2), (V3). -/
def viewMap {Rd : Type} [AddCommGroup Rd] [Module K Rd] (rounds : (ι → Y → K) →ₗ[K] Rd)
    (ε : ι → E) (enc : Q → Y → K) : (ι → Y → K) →ₗ[K] Rd × (Y → E) × (Q → ι → K) :=
  rounds.prod ((foldMap ε).prod (rowsMap enc))

/-- A stack that is zero past the first piece. -/
def OnFirst (first : Finset Y) (T : ι → Y → K) : Prop := ∀ l, ∀ y ∉ first, T l y = 0

/-- A stack that is zero but at entry `y`. -/
def OnColumn (y : Y) (T : ι → Y → K) : Prop := ∀ l y', y' ≠ y → T l y' = 0

/-- The changes of the randomness at one entry past the first piece that keep `f¹`. -/
def kerMoves (ε : ι → E) (first : Finset Y) (rand : Submodule K (ι → Y → K)) :
    Set (ι → Y → K) :=
  {ρ | ρ ∈ rand ∧ ∃ y ∉ first, OnColumn y ρ ∧ foldMap (K := K) ε ρ y = 0}

/-- The stacks that are zero on the first piece. -/
def offFirst (first : Finset Y) : Submodule K (ι → Y → K) where
  carrier := {T | ∀ l, ∀ y ∈ first, T l y = 0}
  add_mem' ha hb l y hy := by simp [ha l y hy, hb l y hy]
  zero_mem' l y _ := rfl
  smul_mem' c T hT l y hy := by simp [hT l y hy]

/-- A `K`-linear map applied lane by lane commutes with the fold: if the lanes `Z` fold to zero at
every entry, so do the lanes `Φ (Z l)`. -/
theorem fold_linearMap_eq_zero (ε : ι → E) (Φ : (Y → K) →ₗ[K] (Y → K)) (Z : ι → Y → K)
    (hZ : ∀ y', ∑ l, ε l * algebraMap K E (Z l y') = 0) (y : Y) :
    ∑ l, ε l * algebraMap K E (Φ (Z l) y) = 0 := by
  have hΦ : ∀ z : Y → K, Φ z y = ∑ y', z y' * Φ (fun j => if y' = j then 1 else 0) y := by
    intro z
    have h1 := congrArg (fun w => Φ w y) (pi_eq_sum_univ z)
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    exact h1
  set m : Y → K := fun y' => Φ (fun j => if y' = j then 1 else 0) y with hm
  have hl : ∀ l, ε l * algebraMap K E (Φ (Z l) y)
      = ∑ y', ε l * algebraMap K E (Z l y') * algebraMap K E (m y') := by
    intro l
    rw [hΦ (Z l), map_sum, mul_sum]
    refine sum_congr rfl fun y' _ => ?_
    rw [map_mul, mul_assoc]
  rw [sum_congr rfl fun l _ => hl l, sum_comm]
  refine sum_eq_zero fun y' _ => ?_
  rw [← sum_mul, hZ y', zero_mul]

/-- **The level-0 view hides the table, linearly.** Every change of the stack that keeps the claims
is cancelled in the view (rounds, folded table, opened rows) by a change of the randomness. -/
theorem level0_hides {Rd Cl : Type} [AddCommGroup Rd] [Module K Rd] [AddCommGroup Cl]
    [Module K Cl] (ε : ι → E) (enc : Q → Y → K) (first : Finset Y)
    (rounds : (ι → Y → K) →ₗ[K] Rd) (claims : (ι → Y → K) →ₗ[K] Cl)
    (rand : Submodule K (ι → Y → K)) (H : Submodule K Rd)
    (hfirst : ∀ T, OnFirst first T → T ∈ rand)
    (hrounds_first : ∀ T, OnFirst first T → rounds T = 0)
    (hclaims : ∀ ρ ∈ rand, claims ρ = 0)
    (hQ : Function.Surjective (firstEval enc first))
    (hS : ∀ y ∉ first, ∀ e : E, ∃ ρ ∈ rand, OnColumn y ρ ∧ foldMap ε ρ y = e)
    (hH : ∀ T, claims T = 0 → (∀ y ∉ first, foldMap ε T y = 0) → rounds T ∈ H)
    (hR : H ≤ Submodule.span K (rounds '' kerMoves ε first rand))
    (Δ : ι → Y → K) (hΔ : claims Δ = 0) :
    ∃ ρ ∈ rand, viewMap rounds ε enc (Δ + ρ) = 0 := by
  classical
  -- Step 0: cancel the change on the first pieces, which are random.
  set ρ0 : ι → Y → K := fun l y => if y ∈ first then -Δ l y else 0 with hρ0
  have hρ0r : ρ0 ∈ rand := hfirst _ fun l y hy => by simp [ρ0, hy]
  set Δ0 := Δ + ρ0 with hΔ0def
  have hΔ0 : ∀ l, ∀ y ∈ first, Δ0 l y = 0 := fun l y hy => by simp [Δ0, ρ0, hy]
  -- Step 1: at each entry past the first piece, cancel the change of `f¹` (condition (S)).
  have hS' : ∀ y, y ∉ first → ∃ ρ ∈ rand, OnColumn y ρ ∧ foldMap ε ρ y = -foldMap ε Δ0 y :=
    fun y hy => hS y hy _
  choose! σ hσr hσc hσf using hS'
  set ρ1 : ι → Y → K := ∑ y ∈ univ.filter (· ∉ first), σ y with hρ1def
  have hρ1r : ρ1 ∈ rand := rand.sum_mem fun y hy => hσr y (mem_filter.mp hy).2
  have hρ1first : ∀ l, ∀ y ∈ first, ρ1 l y = 0 := by
    intro l y hy
    simp only [ρ1, Finset.sum_apply]
    refine sum_eq_zero fun y' hy' => ?_
    have hy'f : y' ∉ first := (mem_filter.mp hy').2
    exact hσc y' hy'f l y fun h => hy'f (h ▸ hy)
  have hρ1fold : ∀ y ∉ first, foldMap ε ρ1 y = foldMap ε (σ y) y := by
    intro y hy
    simp only [ρ1, map_sum, Finset.sum_apply]
    rw [sum_eq_single_of_mem y (mem_filter.mpr ⟨mem_univ _, hy⟩)]
    intro y' hy' hne
    show ∑ l, ε l * algebraMap K E (σ y' l y) = 0
    refine sum_eq_zero fun l _ => ?_
    rw [hσc y' (mem_filter.mp hy').2 l y fun h => hne h.symm, map_zero, mul_zero]
  set Δ1 := Δ0 + ρ1 with hΔ1def
  have hΔ1fold : ∀ y ∉ first, foldMap ε Δ1 y = 0 := by
    intro y hy
    rw [hΔ1def, map_add, Pi.add_apply, hρ1fold y hy, hσf y hy, add_neg_cancel]
  have hΔ1claims : claims Δ1 = 0 := by
    rw [hΔ1def, hΔ0def, map_add, map_add, hΔ, hclaims _ hρ0r, hclaims _ hρ1r, add_zero, add_zero]
  -- Step 2: the change left on the rounds lies in `H` (condition (H)), which the randomness
  -- keeping `f¹` spans (condition (R)).
  have hmem : rounds Δ1 ∈ Submodule.span K (rounds '' kerMoves ε first rand) :=
    hR (hH _ hΔ1claims hΔ1fold)
  rw [Submodule.span_image] at hmem
  obtain ⟨κ, hκ, hκeq⟩ := Submodule.mem_map.mp hmem
  have hkG : kerMoves ε first rand ⊆
      (rand ⊓ LinearMap.ker (foldMap (K := K) ε) ⊓ offFirst first : Submodule K (ι → Y → K)) := by
    rintro ρ ⟨hρr, y, hy, hcol, hf⟩
    refine ⟨⟨hρr, ?_⟩, ?_⟩
    · change foldMap (K := K) ε ρ = 0
      funext y'
      by_cases hy' : y' = y
      · rw [hy', hf, Pi.zero_apply]
      · show ∑ l, ε l * algebraMap K E (ρ l y') = 0
        simp [hcol _ y' hy']
    · intro l y' hy'
      exact hcol l y' fun h => hy (h ▸ hy')
  have hκG := Submodule.span_le.mpr hkG hκ
  obtain ⟨⟨hκr, hκf'⟩, hκ1⟩ := hκG
  have hκf : foldMap (K := K) ε κ = 0 := hκf'
  set Δ2 := Δ1 - κ with hΔ2def
  have hΔ2rounds : rounds Δ2 = 0 := by rw [hΔ2def, map_sub, hκeq, sub_self]
  have hΔ2first : ∀ l, ∀ y ∈ first, Δ2 l y = 0 := by
    intro l y hy
    simp only [Δ2, Δ1, Pi.sub_apply, Pi.add_apply]
    rw [hΔ0 l y hy, hρ1first l y hy, hκ1 l y hy]
    simp
  have hΔ2fold : ∀ y, foldMap ε Δ2 y = 0 := by
    intro y
    by_cases hy : y ∈ first
    · show ∑ l, ε l * algebraMap K E (Δ2 l y) = 0
      simp [hΔ2first _ y hy]
    · rw [hΔ2def, map_sub, Pi.sub_apply, hΔ1fold y hy, hκf, Pi.zero_apply, sub_zero]
  -- Step 3: the opened rows, by a change of the first pieces (condition (Q)); it keeps `f¹`.
  obtain ⟨N, hN⟩ := (firstEval enc first).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hQ)
  set Φ : (Y → K) →ₗ[K] (Y → K) := N ∘ₗ encMap enc with hΦ
  set ρ3 : ι → Y → K := fun l y => if y ∈ first then -(Φ (Δ2 l)) y else 0 with hρ3
  have hρ3on : OnFirst first ρ3 := fun l y hy => by simp [ρ3, hy]
  have hρ3r : ρ3 ∈ rand := hfirst _ hρ3on
  refine ⟨ρ0 + ρ1 - κ + ρ3, rand.add_mem (rand.sub_mem (rand.add_mem hρ0r hρ1r) hκr) hρ3r, ?_⟩
  have hsum : Δ + (ρ0 + ρ1 - κ + ρ3) = Δ2 + ρ3 := by
    rw [hΔ2def, hΔ1def, hΔ0def]
    abel
  rw [hsum]
  simp only [viewMap, LinearMap.prod_apply, Function.prod, map_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- (V1)
    show rounds Δ2 + rounds ρ3 = 0
    rw [hΔ2rounds, hrounds_first _ hρ3on, add_zero]
  · -- (V2)
    funext y
    show foldMap ε Δ2 y + foldMap ε ρ3 y = 0
    rw [hΔ2fold y, zero_add]
    show ∑ l, ε l * algebraMap K E (ρ3 l y) = 0
    by_cases hy : y ∈ first
    · simp only [ρ3, hy, ite_true, map_neg, mul_neg, sum_neg_distrib, neg_eq_zero]
      exact fold_linearMap_eq_zero ε Φ Δ2 hΔ2fold y
    · simp [ρ3, hy]
  · -- (V3)
    funext x l
    show encMap enc (Δ2 l) x + encMap enc (ρ3 l) x = 0
    have hfe : firstEval enc first (N (encMap enc (Δ2 l))) = encMap enc (Δ2 l) := by
      have := congrArg (fun f => f (encMap enc (Δ2 l))) hN
      simpa using this
    have h3 : encMap enc (ρ3 l) x = -firstEval enc first (N (encMap enc (Δ2 l))) x := by
      show ∑ y, enc x y * ρ3 l y = -∑ y ∈ first, enc x y * N (encMap enc (Δ2 l)) y
      simp only [ρ3, mul_ite, mul_zero, mul_neg]
      rw [← sum_filter, sum_neg_distrib, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rfl
    rw [h3, hfe, add_neg_cancel]

/-- The randomness reaches every view a change keeping the claims reaches. -/
theorem level0_mem_map {Rd Cl : Type} [AddCommGroup Rd] [Module K Rd] [AddCommGroup Cl]
    [Module K Cl] (ε : ι → E) (enc : Q → Y → K) (first : Finset Y)
    (rounds : (ι → Y → K) →ₗ[K] Rd) (claims : (ι → Y → K) →ₗ[K] Cl)
    (rand : Submodule K (ι → Y → K)) (H : Submodule K Rd)
    (hfirst : ∀ T, OnFirst first T → T ∈ rand)
    (hrounds_first : ∀ T, OnFirst first T → rounds T = 0)
    (hclaims : ∀ ρ ∈ rand, claims ρ = 0)
    (hQ : Function.Surjective (firstEval enc first))
    (hS : ∀ y ∉ first, ∀ e : E, ∃ ρ ∈ rand, OnColumn y ρ ∧ foldMap ε ρ y = e)
    (hH : ∀ T, claims T = 0 → (∀ y ∉ first, foldMap ε T y = 0) → rounds T ∈ H)
    (hR : H ≤ Submodule.span K (rounds '' kerMoves ε first rand))
    (Δ : ι → Y → K) (hΔ : claims Δ = 0) :
    viewMap rounds ε enc Δ ∈ rand.map (viewMap rounds ε enc) := by
  obtain ⟨ρ, hρ, h0⟩ := level0_hides ε enc first rounds claims rand H hfirst hrounds_first hclaims
    hQ hS hH hR Δ hΔ
  refine ⟨-ρ, rand.neg_mem hρ, ?_⟩
  rw [map_add] at h0
  rw [map_neg]
  exact (neg_eq_of_add_eq_zero_left h0)

/-- **The level-0 view of two tables with the same claims is identically distributed.** The stack
is `S_D d + S_R r`: the table `d`'s part and the randomness `r`'s, `r` uniform. The randomness's
part spans `rand`, weighs nothing in the claims, and the claims of the stack are the table's. Then
the conditions of `level0_hides` make the view, and anything computed from it, independent of the
table given its claims. -/
theorem level0_view_evalDistEq {Rd Cl D R O : Type} [AddCommGroup Rd] [Module K Rd]
    [AddCommGroup Cl] [Module K Cl] [AddCommGroup D] [Module K D] [AddCommGroup R] [Module K R]
    [SampleableType R] (ε : ι → E) (enc : Q → Y → K) (first : Finset Y)
    (rounds : (ι → Y → K) →ₗ[K] Rd) (claims : (ι → Y → K) →ₗ[K] Cl)
    (SD : D →ₗ[K] (ι → Y → K)) (SR : R →ₗ[K] (ι → Y → K)) (H : Submodule K Rd)
    (hfirst : ∀ T, OnFirst first T → T ∈ LinearMap.range SR)
    (hrounds_first : ∀ T, OnFirst first T → rounds T = 0)
    (hclaims : ∀ r, claims (SR r) = 0)
    (hQ : Function.Surjective (firstEval enc first))
    (hS : ∀ y ∉ first, ∀ e : E, ∃ ρ ∈ LinearMap.range SR, OnColumn y ρ ∧ foldMap ε ρ y = e)
    (hH : ∀ T, claims T = 0 → (∀ y ∉ first, foldMap ε T y = 0) → rounds T ∈ H)
    (hR : H ≤ Submodule.span K (rounds '' kerMoves ε first (LinearMap.range SR)))
    {d d' : D} (hd : claims (SD d) = claims (SD d')) (g : Rd × (Y → E) × (Q → ι → K) → O) :
    (fun r => g (viewMap rounds ε enc (SD d + SR r))) <$> ($ᵗ R)
      =ᵈ (fun r => g (viewMap rounds ε enc (SD d' + SR r))) <$> ($ᵗ R) := by
  have hcl : ∀ ρ ∈ LinearMap.range SR, claims ρ = 0 := by
    rintro _ ⟨r, rfl⟩
    exact hclaims r
  have h := hiding_of_mem_range_map (viewMap rounds ε enc ∘ₗ SD) (viewMap rounds ε enc ∘ₗ SR)
    (claims ∘ₗ SD) ?_ (d := d) (d' := d') hd g
  · simpa only [LinearMap.comp_apply, map_add] using h
  · intro Δ hΔ
    obtain ⟨ρ, ⟨r, rfl⟩, hρ⟩ := level0_mem_map ε enc first rounds claims (LinearMap.range SR) H
      hfirst hrounds_first hcl hQ hS hH hR (SD Δ) hΔ
    exact ⟨r, hρ⟩

end Model

end QuotientSecurity.Hiding
