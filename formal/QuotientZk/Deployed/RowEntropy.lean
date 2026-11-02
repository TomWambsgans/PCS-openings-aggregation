-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The translation argument is F3's (`QuotientSecurity.Hiding.HiddenLayout.unopened_row_le`,
-- `formal/QuotientSecurity/Hiding/Merkle.lean`), restated for any linear randomness model with free
-- entries, as the redesigned layout (`crates/quotient/HIDING.md`, the gadget) needs.
import QuotientSecurity.Hiding
import QuotientZk.Rom.Main

/-!
# Unopened rows keep their entropy: the redesigned layout, and the joint view

**The layout.** The hidden layouts of `crates/quotient/HIDING.md` (the gadget's redesign: no share
lane; at the last nine entries of every lane's first piece, lanes `0, 31` and `1, 30` share one
random value and the overflow lane holds zero) leave every lane's entries `0 .. D` (`D = 2^s - 9 =
247`) uniform and independent: on stacks supported there the randomness is the identity
(`hR`), and no weight (claims, gadget) reaches them (`hrounds`). That is all the translation
argument of `HIDING.md` ("Why it hides", step 3) uses, so it is stated here for any linear
randomness model with free entries `F` (`row_entropy`): with `|Q| < |F|`, a vector `u` of degree
below `|F|` vanishing on `Q` and `1` at `x₀` (and `0` at `x₁`, for two rows) exists
(`QuotientSecurity.Hiding.exists_unopened_vector`), and translating the free entries by `c_l·u`,
`Σ_l ε_l c_l = 0`, keeps the view and moves the row `x₀` (or the difference of rows `x₀` and `x₁`)
by `c`: `L - 3` elements of `K`, `64 (L - 3)` bits (`2368` for `R1`'s 40 lanes, `3840` for `R2`'s 63).
The gadget's equalities are between **lanes** at entries past `F` (lanes `0, 31` and `1, 30` at
entries `D .. D + 6`); they make no two **rows** (positions) equal, and the pairwise statement
(`x₁ ≠ 0`) is what `zk_rom`'s `hent₂` asks.

**The joint view.** `prEvent_factor_le`: if the secret is `(a, b)` uniform, the view is a function
`Φ a (g a b)` of `a` and a table's view `g a b`, and given `g a b` and `a` the row `h a b` keeps its
entropy, then it keeps it given the view, even against a value `w a` that `a` determines (the
other table's rows, for `hent₂` across tables).
-/

open OracleComp
open scoped ENNReal

namespace QuotientZk.Deployed

open QuotientSecurity.Hiding Finset

set_option linter.unusedSectionVars false

section Rows

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q]
  [DecidableEq Q]

/-- The lanes' codewords at the position of coefficient vector `x`: a row. -/
def rowAt (x : Y → K) (T : ι → Y → K) : ι → K := fun l => ∑ y, x y * T l y

/-- **An unopened row, or the difference of two rows, keeps `L - 3` elements of `K` given the
view**, for a linear randomness model with free entries `F`. With `x₁ = 0` it is one row. -/
theorem row_entropy [Fintype K] [DecidableEq K] [FiniteDimensional K E]
    (h3 : Module.finrank K E = 3) [SampleableType (ι → Y → K)] {Rd : Type} [AddCommGroup Rd]
    [Module K Rd] (F : Finset Y) (stackR : (ι → Y → K) →ₗ[K] (ι → Y → K))
    (hR : ∀ T, OnFirst F T → stackR T = T) (rounds : (ι → Y → K) →ₗ[K] Rd)
    (hrounds : ∀ T, OnFirst F T → rounds T = 0) (ε : ι → E) (enc : Q → Y → K)
    (x₀ x₁ u : Y → K) (hu : ∀ y ∉ F, u y = 0) (huQ : ∀ x, ∑ y, enc x y * u y = 0)
    (hu₀ : ∑ y, x₀ y * u y = 1) (hu₁ : ∑ y, x₁ y * u y = 0) (base : ι → Y → K)
    (v : Rd × (Y → E) × (Q → ι → K)) (z : ι → K) :
    Pr{let r ← $ᵗ (ι → Y → K)}[viewMap rounds ε enc (base + stackR r) = v ∧
        rowAt x₀ (base + stackR r) - rowAt x₁ (base + stackR r) = z]
        * (Fintype.card K ^ (Fintype.card ι - 3) : ℕ)
      ≤ Pr{let r ← $ᵗ (ι → Y → K)}[viewMap rounds ε enc (base + stackR r) = v] := by
  classical
  set C := LinearMap.ker (foldVec (K := K) ε)
  let τ : C →+ (ι → Y → K) :=
    { toFun := fun c l y => (c : ι → K) l * u y
      map_zero' := by funext l y; simp
      map_add' := fun c c' => by funext l y; simp [add_mul] }
  have hτon : ∀ c : C, OnFirst F (τ c) := fun c l y hy => by
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
  have hrow : ∀ (x : Y → K) (c : C) (l : ι),
      ∑ y, x y * ((c : ι → K) l * u y) = (c : ι → K) l * ∑ y, x y * u y := by
    intro x c l
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    ring
  have h := prEvent_and_mul_card_le (R := ι → Y → K) (C := C)
    (fun r => viewMap rounds ε enc (base + stackR r))
    (fun r => rowAt x₀ (base + stackR r) - rowAt x₁ (base + stackR r)) τ (fun c => (c : ι → K))
    Subtype.val_injective ?_ ?_ v z
  · refine le_trans ?_ h
    gcongr
    exact_mod_cast card_ker_foldVec_ge h3 ε
  · intro r c
    rw [stackR.map_add r (τ c), hR _ (hτon c), ← add_assoc, (viewMap rounds ε enc).map_add,
      hτview, add_zero]
  · intro r c
    funext l
    rw [stackR.map_add r (τ c), hR _ (hτon c), ← add_assoc]
    simp only [rowAt, Pi.sub_apply, Pi.add_apply, mul_add, sum_add_distrib]
    show _ = _ + (c : ι → K) l
    have h0 : ∑ y, x₀ y * τ c l y = (c : ι → K) l := by
      show ∑ y, x₀ y * ((c : ι → K) l * u y) = _
      rw [hrow, hu₀, mul_one]
    have h1 : ∑ y, x₁ y * τ c l y = 0 := by
      show ∑ y, x₁ y * ((c : ι → K) l * u y) = _
      rw [hrow, hu₁, mul_zero]
    rw [h0, h1]
    abel

end Rows

/-! ## The joint view -/

section Factor

open Classical in
theorem prEvent_and_eq_tsum {B U : Type} (mb : ProbComp B) (g : B → U) (P : U → Prop)
    (R : B → Prop) :
    Pr{let b ← mb}[P (g b) ∧ R b] =
      ∑' u, (if P u then Pr{let b ← mb}[g b = u ∧ R b] else 0) := by
  classical
  rw [prEvent_eq_tsum_ite]
  simp_rw [prEvent_eq_tsum_ite mb (fun b => g b = _ ∧ R b)]
  calc ∑' b, (if P (g b) ∧ R b then Pr{let y ← mb}[y = b] else 0)
      = ∑' b, ∑' u, (if P u then (if g b = u ∧ R b then Pr{let y ← mb}[y = b] else 0) else 0) := by
        refine tsum_congr fun b => ?_
        rw [tsum_eq_single (g b) fun u hu => by simp [Ne.symm hu]]
        by_cases hP : P (g b) <;> by_cases hR : R b <;> simp [hP, hR]
    _ = _ := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun u => ?_
        split_ifs <;> simp

/-- **An event that keeps its entropy given a table's view keeps it given the joint view**: the
secret is `(a, b)`, the view a function of `a` and of `g a b`. -/
theorem prEvent_factor_le {A B V U : Type} [SampleableType A] [SampleableType B]
    (Φ : A → U → V) (g : A → B → U) (E : A → B → Prop) (δ : ℝ≥0∞)
    (hδ : ∀ a u, Pr{let b ← $ᵗ B}[g a b = u ∧ E a b] ≤ δ * Pr{let b ← $ᵗ B}[g a b = u])
    (v : V) :
    Pr{let s ← $ᵗ (A × B)}[Φ s.1 (g s.1 s.2) = v ∧ E s.1 s.2] ≤
      δ * Pr{let s ← $ᵗ (A × B)}[Φ s.1 (g s.1 s.2) = v] := by
  classical
  rw [SampleableType.uniformSample_prod_eq_bind A B, prEvent_bind_eq_tsum, prEvent_bind_eq_tsum,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [mul_left_comm]
  refine mul_le_mul_right ?_ _
  have hm : ∀ (ev : A × B → Prop),
      Pr{let x ← (($ᵗ B : ProbComp B) >>= fun b => (pure (a, b) : ProbComp (A × B)))}[ev x]
        = Pr{let b ← $ᵗ B}[ev (a, b)] := fun ev => by
    rw [show (($ᵗ B : ProbComp B) >>= fun b => (pure (a, b) : ProbComp (A × B))) =
        (fun b => (a, b)) <$> ($ᵗ B) by simp [map_eq_bind_pure_comp], prEvent_map]
  rw [hm, hm]
  rw [prEvent_and_eq_tsum ($ᵗ B) (g a) (fun u => Φ a u = v) (fun b => E a b)]
  have hv : Pr{let b ← $ᵗ B}[Φ a (g a b) = v] =
      ∑' u, (if Φ a u = v then Pr{let b ← $ᵗ B}[g a b = u] else 0) := by
    have := prEvent_and_eq_tsum ($ᵗ B) (g a) (fun u => Φ a u = v) (fun _ => True)
    simpa using this
  rw [hv, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun u => ?_
  split_ifs
  · exact hδ a u
  · simp

end Factor

end QuotientZk.Deployed
