-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Layout

/-!
# An unopened row keeps `L - 3` uniform elements of `K`

The Merkle siblings of the first commitment hash rows that are not opened. In the random-oracle
model they are simulated unless the distinguisher queries the oracle at such a row, so what matters is
how well the view predicts an unopened row (`membership-zk.md`, "the siblings"; `HIDING.md`, step 3).

`prEvent_and_mul_card_le`: a group `C` of translations of the randomness that keeps the view and
moves the row injectively divides every joint probability `Pr[view = v ∧ row = z]` by `|C|`: given
the view, the row takes any value with probability at most `1/|C|`.

`HiddenLayout.unopened_row_le`: for an unopened position `x₀` (a first-piece vector `u` vanishing at
the opened positions and `1` at `x₀`, which exists when `|Q| < 2^s`), translating the first pieces by
`c_l·u` with `Σ_l ε_l c_l = 0` is such a group, of `|K|^(L - 3)` elements at least: the row at `x₀`
keeps `64·(L - 3)` bits given the view (`2368` for 40 lanes, `3840` for 63), whatever the table, the
challenges and the rounds (any map blind to the first pieces). The siblings are then simulated but
with probability `H·N·|K|^-(L-3)` for `H` oracle queries and `N` unopened rows (a union bound; the
oracle exchange itself is not formalized here).
-/

namespace QuotientSecurity.Hiding

open Finset OracleComp

set_option linter.unusedSectionVars false

section Entropy

variable {R V Z C : Type} [AddCommGroup R] [SampleableType R] [Fintype R] [AddCommGroup Z]
  [AddCommGroup C] [Fintype C]

/-- **Min-entropy by translation.** -/
theorem prEvent_and_mul_card_le (view : R → V) (row : R → Z) (τ : C →+ R) (ι : C → Z)
    (hι : Function.Injective ι) (hview : ∀ r c, view (r + τ c) = view r)
    (hrow : ∀ r c, row (r + τ c) = row r + ι c) (v : V) (z : Z) :
    Pr{let r ← $ᵗ R}[view r = v ∧ row r = z] * Fintype.card C ≤ Pr{let r ← $ᵗ R}[view r = v] := by
  classical
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample]
  set A := univ.filter fun r : R => view r = v ∧ row r = z
  set B := univ.filter fun r : R => view r = v
  have hAB : A.card * Fintype.card C ≤ B.card := by
    rw [← card_univ (α := C), ← card_product]
    refine Finset.card_le_card_of_injOn (fun p => p.1 + τ p.2) ?_ ?_
    · intro p hp
      obtain ⟨hp1, -⟩ := mem_product.mp hp
      obtain ⟨-, hv, -⟩ := mem_filter.mp hp1
      exact mem_filter.mpr ⟨mem_univ _, by rw [hview]; exact hv⟩
    · intro p hp q hq hpq
      obtain ⟨-, -, hpz⟩ := mem_filter.mp (mem_product.mp hp).1
      obtain ⟨-, -, hqz⟩ := mem_filter.mp (mem_product.mp hq).1
      simp only at hpq
      have hc : ι p.2 = ι q.2 := by
        have h1 := hrow p.1 p.2
        have h2 := hrow q.1 q.2
        rw [hpq, hpz] at h1
        rw [h1, hqz] at h2
        exact add_left_cancel h2
      have hc' : p.2 = q.2 := hι hc
      have h1 : p.1 = q.1 := by
        rw [hc'] at hpq
        exact add_right_cancel hpq
      exact Prod.ext h1 hc'
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast hAB

end Entropy

section Layout

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q]
  [DecidableEq Q]

/-- One entry's fold: `c ↦ Σ_l ε_l c_l`. -/
def foldVec (ε : ι → E) : (ι → K) →ₗ[K] E where
  toFun c := ∑ l, ε l * algebraMap K E (c l)
  map_add' c c' := by simp [mul_add, sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, mul_sum, Algebra.smul_def]
    refine sum_congr rfl fun l _ => ?_
    ring

/-- The fold's kernel on one entry has at least `|K|^(L - 3)` elements. -/
theorem card_ker_foldVec_ge [Fintype K] [FiniteDimensional K E] (h3 : Module.finrank K E = 3)
    (ε : ι → E) [Fintype (LinearMap.ker (foldVec (K := K) ε))] :
    Fintype.card K ^ (Fintype.card ι - 3) ≤ Fintype.card (LinearMap.ker (foldVec (K := K) ε)) := by
  rw [Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker (foldVec (K := K) ε))]
  have hrn := LinearMap.finrank_range_add_finrank_ker (foldVec (K := K) ε)
  have hr : Module.finrank K (LinearMap.range (foldVec (K := K) ε)) ≤ 3 :=
    h3 ▸ Submodule.finrank_le _
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  exact Nat.pow_le_pow_right Fintype.card_pos (by omega)

namespace HiddenLayout

variable (L : HiddenLayout ι Y)

theorem stackR_of_onFirst (T : ι → Y → K) (hT : OnFirst L.first T) : L.stackR T = T := by
  funext l y
  show (if L.randPos l y then T l y else 0) +
    (if l = L.ov ∧ y ∈ L.held then T L.share y else 0) = T l y
  by_cases hy : y ∈ L.first
  · have hheld : y ∉ L.held := Finset.disjoint_right.mp L.held_first hy
    simp [randPos, hy, hheld]
  · have h1 : T l y = 0 := hT l y hy
    have h2 : T L.share y = 0 := hT L.share y hy
    simp [h1, h2]

/-- **An unopened row keeps `L - 3` elements of `K` given the view.** For any rounds blind to the
first pieces, fold weights `ε`, opened positions `Q` (columns `enc`), and an unopened position whose
column is `x₀`, if a first-piece vector `u` vanishes at `Q` and is `1` at `x₀`: for every table, view
value and row value, `Pr[view = v ∧ row = z] · |K|^(L-3) ≤ Pr[view = v]`. -/
theorem unopened_row_le [Fintype K] [DecidableEq K] [FiniteDimensional K E]
    (h3 : Module.finrank K E = 3) [SampleableType (ι → Y → K)] {Rd : Type} [AddCommGroup Rd]
    [Module K Rd] (rounds : (ι → Y → K) →ₗ[K] Rd) (hrounds : ∀ T, OnFirst L.first T → rounds T = 0)
    (ε : ι → E) (enc : Q → Y → K) (x₀ : Y → K) (u : Y → K) (hu : ∀ y ∉ L.first, u y = 0)
    (huQ : ∀ x, ∑ y, enc x y * u y = 0) (hux : ∑ y, x₀ y * u y = 1) (d : ι → Y → K)
    (v : Rd × (Y → E) × (Q → ι → K)) (z : ι → K) :
    Pr{let r ← $ᵗ (ι → Y → K)}[viewMap rounds ε enc (L.stackD d + L.stackR r) = v ∧
        (fun l => ∑ y, x₀ y * (L.stackD d + L.stackR r) l y) = z]
        * (Fintype.card K ^ (Fintype.card ι - 3) : ℕ)
      ≤ Pr{let r ← $ᵗ (ι → Y → K)}[viewMap rounds ε enc (L.stackD d + L.stackR r) = v] := by
  classical
  set C := LinearMap.ker (foldVec (K := K) ε)
  let τ : C →+ (ι → Y → K) :=
    { toFun := fun c l y => (c : ι → K) l * u y
      map_zero' := by funext l y; simp
      map_add' := fun c c' => by funext l y; simp [add_mul] }
  have hτon : ∀ c : C, OnFirst L.first (τ c) := fun c l y hy => by
    show (c : ι → K) l * u y = 0
    rw [hu y hy, mul_zero]
  have hτview : ∀ c : C, viewMap rounds ε enc (τ c) = 0 := by
    intro c
    have hc : ∑ l, ε l * algebraMap K E ((c : ι → K) l) = 0 := c.2
    simp only [viewMap, LinearMap.prod_apply, Function.prod]
    refine Prod.ext (hrounds _ (hτon c)) (Prod.ext ?_ ?_)
    · funext y
      show ∑ l, ε l * algebraMap K E ((c : ι → K) l * u y) = 0
      simp only [map_mul, ← mul_assoc, ← sum_mul, hc, zero_mul]
    · funext x l
      show ∑ y, enc x y * ((c : ι → K) l * u y) = 0
      have : ∑ y, enc x y * ((c : ι → K) l * u y) = (c : ι → K) l * ∑ y, enc x y * u y := by
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
      rw [this, huQ, mul_zero]
  have h := prEvent_and_mul_card_le (R := ι → Y → K) (C := C)
    (fun r => viewMap rounds ε enc (L.stackD d + L.stackR r))
    (fun r => fun l => ∑ y, x₀ y * (L.stackD d + L.stackR r) l y) τ (fun c => (c : ι → K))
    Subtype.val_injective ?_ ?_ v z
  · refine le_trans ?_ h
    gcongr
    exact_mod_cast card_ker_foldVec_ge h3 ε
  · intro r c
    rw [(L.stackR (K := K)).map_add r (τ c), L.stackR_of_onFirst _ (hτon c), ← add_assoc,
      (viewMap rounds ε enc).map_add, hτview, add_zero]
  · intro r c
    funext l
    rw [(L.stackR (K := K)).map_add r (τ c), L.stackR_of_onFirst _ (hτon c), ← add_assoc]
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
    congr 1
    show ∑ y, x₀ y * ((c : ι → K) l * u y) = (c : ι → K) l
    have : ∑ y, x₀ y * ((c : ι → K) l * u y) = (c : ι → K) l * ∑ y, x₀ y * u y := by
      rw [mul_sum]
      refine sum_congr rfl fun y _ => ?_
      ring
    rw [this, hux, mul_one]

end HiddenLayout

end Layout

end QuotientSecurity.Hiding
