-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Gadget

/-!
# The solvers' span: the hypothesis `hsolve` of `GadgetLayout.roundsReached`

`crates/quotient/HIDING.md`, "Condition (R) for every challenge: the gadget", step 1 (the solvers).
`GadgetLayout.roundsReached` takes, for each pattern `p` and each `e : E`, `K`-values on the lanes
of `p`'s other half that the stack has (`S = Set.range pos`), folding to `e` (`hsolve`). Here:

* `solve_of_span`, `hsolve_of_span`: `hsolve` holds when, on each half, the fold weights of some
  lanes of the stack span `E` over `K`.
* `span_one_x_y_xy` (*the cube lemma*): with `[E : K] = 3`, `1, x, y, xy` span `E` over `K` unless
  `x` or `y` lies in `K` (`mem_range_of_sq_eq`: `E` has no quadratic subfield over `K`, so
  `x² ∈ K + K x` puts `x` in `K`). `span_face`: so do the fold weights of the four lanes of a face
  of the lane cube in two coordinates whose challenges are not in `K`.
* `span_cube`, `hsolve_of_cube`: the cubes `32 .. 40` and `0 .. 8` span, so `hsolve` holds, for every
  `φ` with no coordinate in `{0, 1}` and at most one of `φ₀, φ₁, φ₂` in `K` (`¬ TwoInK φ`).
  `card_twoInK_le`, `prob_twoInK_le`: two of them lie in `K` for at most `3·|K|²·|E|⁴` challenges,
  probability `3·|K|²/|E|²` (`3·2^-256`); `prob_not_solvable_le`: with a coordinate in `{0, 1}`,
  `(12·|E| + 3·|K|²)/|E|²` (`12·2^-192 + 3·2^-256`).
* `hsolve_of_four`, `prob_not_span_four_le`: `hsolve` from four lanes of each half, `35, 34, 33, 39`
  and `3, 2, 1, 7`, whose spans fail (`card_not_span_four_le`) for at most
  `2·((13 + |K|)·|E| + |K|⁴)/|E|²` of the challenges (about `2^-126`).
* `span_cube_erase`: condition (S) for the random lanes `33 .. 40` (the upper cube but the overflow
  lane), outside the same set.
-/

namespace QuotientSecurity.Hiding

open Finset OracleComp

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]

/-! ### `hsolve` from a span -/

/-- Bit 5 of pattern `p`'s other half (its solvers'): set for the pairs, clear for the overflow lane. -/
def solverBit (p : Fin 3) : Bool := decide (p.val < 2)

theorem onOther_ofK (p : Fin 3) (s : (Fin 6 → Bool) → K)
    (h : ∀ b, b (Fin.last 5) ≠ solverBit p → s b = 0) : OnOther p (ofK (E := E) s) := by
  unfold OnOther
  split_ifs with hp
  · intro b hb
    have : s b = 0 := h b (by rw [hb]; simp [solverBit, hp])
    simp [ofK, this]
  · intro b hb
    have : s b = 0 := h b (by rw [hb]; simp [solverBit, hp])
    simp [ofK, this]

/-- **A solver from a span.** If the fold weights of lanes `T`, all of the stack (`S`) and on pattern
`p`'s other half, span `E` over `K`, every `e : E` is the fold of `K`-values on `T`. -/
theorem solve_of_span (φ : Fin 6 → E) (S : Set (Fin 6 → Bool)) (p : Fin 3) (T : Set (Fin 6 → Bool))
    (hTS : T ⊆ S) (hTp : ∀ b ∈ T, b (Fin.last 5) = solverBit p)
    (hspan : Submodule.span K (eqW φ '' T) = ⊤) (e : E) :
    ∃ s : (Fin 6 → Bool) → K, OnOther p (ofK (E := E) s) ∧ (∀ b, b ∉ S → s b = 0) ∧
      (∑ b, eqW φ b * algebraMap K E (s b)) = e := by
  have he : e ∈ Submodule.span K (eqW φ '' T) := hspan ▸ Submodule.mem_top
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := K)).mp he
  have hlT : ∀ b, b ∉ T → l b = 0 := fun b hb =>
    Finsupp.notMem_support_iff.mp fun hb' =>
      hb ((Finsupp.mem_supported (M := K) (R := K) l).mp hl hb')
  refine ⟨l, onOther_ofK p _ fun b hb => hlT b fun hbT => hb (hTp b hbT),
    fun b hb => hlT b fun hbT => hb (hTS hbT), ?_⟩
  rw [← hle, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  refine sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, mul_comm]

/-- **`hsolve` from the span on each half**: lanes `Tup` of the upper half and `Tlow` of the lower
half, all of the stack (`S`), whose fold weights span `E` over `K`. At `S = Set.range pos` this is
the hypothesis `hsolve` of `GadgetLayout.roundsReached`. -/
theorem hsolve_of_span (φ : Fin 6 → E) (S Tup Tlow : Set (Fin 6 → Bool)) (hup : Tup ⊆ S)
    (hlow : Tlow ⊆ S) (hupH : ∀ b ∈ Tup, b (Fin.last 5) = true)
    (hlowH : ∀ b ∈ Tlow, b (Fin.last 5) = false)
    (hspanU : Submodule.span K (eqW φ '' Tup) = ⊤) (hspanL : Submodule.span K (eqW φ '' Tlow) = ⊤) :
    ∀ (p : Fin 3) (e : E), ∃ s : (Fin 6 → Bool) → K, OnOther p (ofK (E := E) s) ∧
      (∀ b, b ∉ S → s b = 0) ∧ (∑ b, eqW φ b * algebraMap K E (s b)) = e := by
  intro p e
  by_cases hp : p.val < 2
  · exact solve_of_span φ S p Tup hup (fun b hb => by rw [hupH b hb]; simp [solverBit, hp])
      hspanU e
  · exact solve_of_span φ S p Tlow hlow (fun b hb => by rw [hlowH b hb]; simp [solverBit, hp])
      hspanL e

/-! ### The cube lemma -/

/-- Membership in the `K`-span of a pair, by coefficients. -/
theorem mem_span_range_pair' {x y v : E} :
    v ∈ Submodule.span K (Set.range ![x, y]) ↔ ∃ α β : K, α • x + β • y = v := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g 0, g 1, by simpa [Fin.sum_univ_two] using hg⟩
  · rintro ⟨α, β, h⟩
    exact ⟨![α, β], by simpa [Fin.sum_univ_two] using h⟩

section Cube

variable [FiniteDimensional K E]

/-- **No quadratic subfield.** With `[E : K] = 3`, an `x` with `x² ∈ K + K x` lies in `K`: its
minimal polynomial has degree at most 2 and dividing 3. -/
theorem mem_range_of_sq_eq (h3 : Module.finrank K E = 3) {x : E} (c d : K)
    (h : x ^ 2 = algebraMap K E c + algebraMap K E d * x) : x ∈ Set.range (algebraMap K E) := by
  have hint : IsIntegral K x := IsIntegral.of_finite K x
  set q : Polynomial K := Polynomial.X ^ 2 - (Polynomial.C d * Polynomial.X + Polynomial.C c)
    with hq
  have hmon : q.Monic := Polynomial.monic_X_pow_sub Polynomial.degree_linear_lt
  have hroot : Polynomial.aeval x q = 0 := by
    simp only [q, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, h]
    ring
  have hqdeg : q.natDegree = 2 := by
    rw [hq]
    compute_degree!
  have hnat : (minpoly K x).natDegree ≤ 2 :=
    hqdeg ▸ Polynomial.natDegree_le_natDegree (minpoly.min K x hmon hroot)
  have hdvd : (minpoly K x).natDegree ∣ 3 := h3 ▸ minpoly.degree_dvd hint
  have h1 : (minpoly K x).natDegree = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
    · exact h'
    · omega
  exact RingHom.mem_range.mp (minpoly.natDegree_eq_one_iff.mp h1)

/-- **The cube lemma** (`HIDING.md`, step 1): with `[E : K] = 3`, if neither `x` nor `y` lies in
`K`, then `1, x, y, x y` span `E` over `K`. Otherwise the span would be the plane of `1, x`, and
`y = a + b x` (`b ≠ 0`) with `x y` in that plane would put `x²` there. -/
theorem span_one_x_y_xy (h3 : Module.finrank K E = 3) {x y : E}
    (hx : x ∉ Set.range (algebraMap K E)) (hy : y ∉ Set.range (algebraMap K E)) :
    Submodule.span K ({1, x, y, x * y} : Set E) = ⊤ := by
  by_contra hne
  have hli : LinearIndependent K ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      exact ⟨by simpa using hst, rfl⟩
    · exfalso
      have htE : algebraMap K E t ≠ 0 := (map_ne_zero _).mpr ht
      refine hx ⟨-s / t, ?_⟩
      rw [map_div₀, map_neg, div_eq_iff htE]
      linear_combination -hst
  -- every generator lies in the plane of `1, x`, or three of them span `E`
  have hin : ∀ v ∈ ({1, x, y, x * y} : Set E),
      v ∈ Submodule.span K (Set.range ![(1 : E), x]) := by
    intro v hv
    by_contra hnot
    apply hne
    have hli3 : LinearIndependent K (Fin.cons v ![(1 : E), x] : Fin 3 → E) :=
      linearIndependent_finCons.mpr ⟨hli, hnot⟩
    have htop := hli3.span_eq_top_of_card_eq_finrank' (by simp [h3])
    rw [eq_top_iff, ← htop]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hv
    · simp
    · simp
  obtain ⟨a, b, hab⟩ := mem_span_range_pair'.mp (hin y (by simp))
  obtain ⟨c, d, hcd⟩ := mem_span_range_pair'.mp (hin (x * y) (by simp))
  simp only [Algebra.smul_def, mul_one] at hab hcd
  have hb : b ≠ 0 := by
    rintro rfl
    exact hy ⟨a, by simpa using hab⟩
  have hbE : algebraMap K E b ≠ 0 := (map_ne_zero _).mpr hb
  apply hx
  refine mem_range_of_sq_eq h3 (c / b) ((d - a) / b) ?_
  have key : algebraMap K E b * x ^ 2
      = algebraMap K E c + (algebraMap K E d - algebraMap K E a) * x := by
    rw [← hab] at hcd
    linear_combination -hcd
  rw [map_div₀, map_div₀, map_sub]
  field_simp
  linear_combination key

end Cube

/-! ### Faces of the lane cube -/

theorem eqFactor_true (t : E) : eqFactor true t = t := rfl

theorem eqFactor_false (t : E) : eqFactor false t = 1 - t := rfl

theorem eqFactor_ne_zero' (u : Bool) {t : E} (h0 : t ≠ 0) (h1 : t ≠ 1) : eqFactor u t ≠ 0 := by
  cases u
  · exact sub_ne_zero.mpr (Ne.symm h1)
  · exact h0

/-- Lane `r` with bits `a, b` set to `u, v`. -/
def setBits {n : ℕ} (r : Fin n → Bool) (a b : Fin n) (u v : Bool) : Fin n → Bool :=
  Function.update (Function.update r a u) b v

theorem setBits_of_ne {n : ℕ} (r : Fin n → Bool) {a b i : Fin n} (hia : i ≠ a) (hib : i ≠ b)
    (u v : Bool) : setBits r a b u v i = r i := by
  simp [setBits, Function.update_of_ne hia, Function.update_of_ne hib]

theorem eqW_setBits {n : ℕ} (φ : Fin n → E) (r : Fin n → Bool) {a b : Fin n} (hab : a ≠ b)
    (u v : Bool) :
    eqW φ (setBits r a b u v) = eqFactor u (φ a) * eqFactor v (φ b) *
      ∏ i ∈ (univ.erase a).erase b, eqFactor (r i) (φ i) := by
  have hb : b ∈ univ.erase a := mem_erase.mpr ⟨Ne.symm hab, mem_univ _⟩
  have ha' : setBits r a b u v a = u := by simp [setBits, Function.update_of_ne hab]
  have hb' : setBits r a b u v b = v := by simp [setBits]
  have e : eqW φ (setBits r a b u v) = ∏ i, eqFactor (setBits r a b u v i) (φ i) := rfl
  rw [e, ← mul_prod_erase univ _ (mem_univ a), ← mul_prod_erase _ _ hb, ← mul_assoc]
  simp only [ha', hb']
  congr 1
  refine prod_congr rfl fun i hi => ?_
  obtain ⟨hib, hi'⟩ := mem_erase.mp hi
  obtain ⟨hia, -⟩ := mem_erase.mp hi'
  rw [setBits_of_ne r hia hib]

section Face

variable [FiniteDimensional K E]

/-- **A face of the lane cube spans `E`**: the fold weights of the four lanes that agree with `r` off
two coordinates `a, b` whose challenges are not in `K` (the others avoiding `{0, 1}`) are a nonzero
multiple of `(1 - φ_a)(1 - φ_b), (1 - φ_a) φ_b, φ_a (1 - φ_b), φ_a φ_b`, whose span is that of
`1, φ_a, φ_b, φ_a φ_b`. -/
theorem span_face (h3 : Module.finrank K E = 3) {n : ℕ} (φ : Fin n → E) (r : Fin n → Bool)
    {a b : Fin n} (hab : a ≠ b) (hav : ∀ i, i ≠ a → i ≠ b → φ i ≠ 0 ∧ φ i ≠ 1)
    (ha : φ a ∉ Set.range (algebraMap K E)) (hb : φ b ∉ Set.range (algebraMap K E)) :
    Submodule.span K (Set.range fun uv : Bool × Bool => eqW φ (setBits r a b uv.1 uv.2)) = ⊤ := by
  set Q := ∏ i ∈ (univ.erase a).erase b, eqFactor (r i) (φ i)
  have hQ : Q ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun i hi => ?_
    obtain ⟨hib, hi'⟩ := mem_erase.mp hi
    obtain ⟨hia, -⟩ := mem_erase.mp hi'
    exact eqFactor_ne_zero' _ (hav i hia hib).1 (hav i hia hib).2
  set V := Submodule.span K (Set.range fun uv : Bool × Bool => eqW φ (setBits r a b uv.1 uv.2))
  have hmem : ∀ u v, eqFactor u (φ a) * eqFactor v (φ b) * Q ∈ V := by
    intro u v
    have : eqW φ (setBits r a b u v) ∈ V := Submodule.subset_span ⟨(u, v), rfl⟩
    rwa [eqW_setBits φ r hab u v] at this
  have hsub : Submodule.map (LinearMap.mulLeft K Q)
      (Submodule.span K ({1, φ a, φ b, φ a * φ b} : Set E)) ≤ V := by
    rw [← Submodule.span_image, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    simp only [LinearMap.mulLeft_apply, SetLike.mem_coe]
    rcases hz with rfl | rfl | rfl | rfl
    · have := V.add_mem (V.add_mem (V.add_mem (hmem false false) (hmem false true))
        (hmem true false)) (hmem true true)
      convert this using 1
      simp only [eqFactor_true, eqFactor_false]
      ring
    · have := V.add_mem (hmem true false) (hmem true true)
      convert this using 1
      simp only [eqFactor_true, eqFactor_false]
      ring
    · have := V.add_mem (hmem false true) (hmem true true)
      convert this using 1
      simp only [eqFactor_true, eqFactor_false]
      ring
    · convert hmem true true using 1
      simp only [eqFactor_true]
      ring
  rw [eq_top_iff]
  intro e _
  have h1 : Q⁻¹ * e ∈ Submodule.span K ({1, φ a, φ b, φ a * φ b} : Set E) := by
    rw [span_one_x_y_xy h3 ha hb]
    trivial
  have := hsub (Submodule.mem_map_of_mem h1)
  rwa [LinearMap.mulLeft_apply, ← mul_assoc, mul_inv_cancel₀ hQ, one_mul] at this

/-- A set of lanes containing a face spans. -/
theorem span_of_face (h3 : Module.finrank K E = 3) {n : ℕ} (φ : Fin n → E) (r : Fin n → Bool)
    {a b : Fin n} (hab : a ≠ b) (hav : ∀ i, i ≠ a → i ≠ b → φ i ≠ 0 ∧ φ i ≠ 1)
    (ha : φ a ∉ Set.range (algebraMap K E)) (hb : φ b ∉ Set.range (algebraMap K E))
    (T : Set (Fin n → Bool)) (hT : ∀ u v, setBits r a b u v ∈ T) :
    Submodule.span K (eqW φ '' T) = ⊤ := by
  rw [eq_top_iff, ← span_face h3 φ r hab hav ha hb]
  refine Submodule.span_mono ?_
  rintro _ ⟨uv, rfl⟩
  exact ⟨_, hT uv.1 uv.2, rfl⟩

end Face

/-! ### The cubes `32 .. 40` and `0 .. 8` -/

/-- Two of `φ₀, φ₁, φ₂` lie in `K`: the challenges at which the cube may not span. -/
def TwoInK (φ : Fin 6 → E) : Prop :=
  (φ 0 ∈ Set.range (algebraMap K E) ∧ φ 1 ∈ Set.range (algebraMap K E)) ∨
    (φ 0 ∈ Set.range (algebraMap K E) ∧ φ 2 ∈ Set.range (algebraMap K E)) ∨
    (φ 1 ∈ Set.range (algebraMap K E) ∧ φ 2 ∈ Set.range (algebraMap K E))

/-- The cube of lanes free in bits 0, 1, 2, with bits 3, 4 clear and bit 5 equal to `h`: lanes
`32 .. 40` (`h = true`: the overflow lane and the random lanes) or `0 .. 8`. -/
def cube (h : Bool) : Set (Fin 6 → Bool) := {b | b 3 = false ∧ b 4 = false ∧ b (Fin.last 5) = h}

theorem ne_of_three_le {i a : Fin 6} (hi : 3 ≤ i.val) (ha : a.val < 3) : i ≠ a := by
  rintro rfl
  omega

section Span

variable [FiniteDimensional K E]

/-- **Outside `TwoInK`, a set of lanes with a face in every two of the coordinates `0, 1, 2` spans**
(the face in `a, b` may depend on the third coordinate `c`). -/
theorem span_of_not_twoInK (h3 : Module.finrank K E = 3) (φ : Fin 6 → E)
    (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (hK : ¬ TwoInK (K := K) φ) (T : Set (Fin 6 → Bool))
    (hT : ∀ a b c : Fin 6, a.val < 3 → b.val < 3 → c.val < 3 → a ≠ b → a ≠ c → b ≠ c →
      ∃ r, ∀ u v, setBits r a b u v ∈ T) :
    Submodule.span K (eqW φ '' T) = ⊤ := by
  have hav : ∀ (a b : Fin 6) i, i ≠ a → i ≠ b → φ i ≠ 0 ∧ φ i ≠ 1 := fun _ _ i _ _ => hφ i
  unfold TwoInK at hK
  by_cases h0 : φ 0 ∈ Set.range (algebraMap K E)
  · have h1 : φ 1 ∉ Set.range (algebraMap K E) := fun h1 => hK (Or.inl ⟨h0, h1⟩)
    have h2 : φ 2 ∉ Set.range (algebraMap K E) := fun h2 => hK (Or.inr (Or.inl ⟨h0, h2⟩))
    obtain ⟨r, hr⟩ := hT 1 2 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    exact span_of_face h3 φ r (by decide) (hav 1 2) h1 h2 T hr
  · by_cases h1 : φ 1 ∈ Set.range (algebraMap K E)
    · have h2 : φ 2 ∉ Set.range (algebraMap K E) := fun h2 => hK (Or.inr (Or.inr ⟨h1, h2⟩))
      obtain ⟨r, hr⟩ := hT 0 2 1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
      exact span_of_face h3 φ r (by decide) (hav 0 2) h0 h2 T hr
    · obtain ⟨r, hr⟩ := hT 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
      exact span_of_face h3 φ r (by decide) (hav 0 1) h0 h1 T hr

/-- **The cubes span**: the fold weights of lanes `32 .. 40` (`h = true`), and of `0 .. 8`, span `E`
over `K` for every `φ` with no coordinate in `{0, 1}` and at most one of `φ₀, φ₁, φ₂` in `K`. -/
theorem span_cube (h3 : Module.finrank K E = 3) (φ : Fin 6 → E) (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1)
    (hK : ¬ TwoInK (K := K) φ) (h : Bool) : Submodule.span K (eqW φ '' cube h) = ⊤ := by
  refine span_of_not_twoInK h3 φ hφ hK _ fun a b c ha hb _ _ _ _ =>
    ⟨fun i => decide (i = Fin.last 5) && h, fun u v => ?_⟩
  have hfix : ∀ i : Fin 6, 3 ≤ i.val →
      setBits (fun i => decide (i = Fin.last 5) && h) a b u v i = (decide (i = Fin.last 5) && h) :=
    fun i hi => setBits_of_ne _ (ne_of_three_le hi ha) (ne_of_three_le hi hb) u v
  refine ⟨?_, ?_, ?_⟩
  · rw [hfix 3 (by decide)]
    rfl
  · rw [hfix 4 (by decide)]
    rfl
  · rw [hfix (Fin.last 5) (by decide)]
    simp

/-- **Condition (S) for the random lanes** `33 .. 40` (the upper cube but the overflow lane `32`),
outside the same set: the face in two of the coordinates `0, 1, 2` with the third set. -/
theorem span_cube_erase (h3 : Module.finrank K E = 3) (φ : Fin 6 → E)
    (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (hK : ¬ TwoInK (K := K) φ) :
    Submodule.span K (eqW φ '' {b | b ∈ cube true ∧ b ≠ lane 32}) = ⊤ := by
  have h32 : ∀ c : Fin 6, c.val < 3 → lane 32 c = false := by decide
  refine span_of_not_twoInK h3 φ hφ hK _ fun a b c ha hb hc hab hac hbc =>
    ⟨fun i => decide (i = Fin.last 5) || decide (i = c), fun u v => ?_⟩
  have hfix : ∀ i : Fin 6, 3 ≤ i.val →
      setBits (fun i => decide (i = Fin.last 5) || decide (i = c)) a b u v i
        = (decide (i = Fin.last 5) || decide (i = c)) :=
    fun i hi => setBits_of_ne _ (ne_of_three_le hi ha) (ne_of_three_le hi hb) u v
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hfix 3 (by decide), decide_eq_false (ne_of_three_le (i := 3) (by decide) hc)]
    rfl
  · rw [hfix 4 (by decide), decide_eq_false (ne_of_three_le (i := 4) (by decide) hc)]
    rfl
  · rw [hfix (Fin.last 5) (by decide)]
    simp
  · intro heq
    have hc' := congrFun heq c
    rw [setBits_of_ne _ (Ne.symm hac) (Ne.symm hbc), h32 c hc] at hc'
    simp at hc'

end Span

/-- **`hsolve` outside `TwoInK`**: for every `φ` with no coordinate in `{0, 1}` and at most one of
`φ₀, φ₁, φ₂` in `K`, given the upper cube (lanes `32 .. 40`, `cube_true_subset`) and the lower half
in the stack. This is `GadgetLayout.roundsReached`'s `hsolve` at `S = Set.range pos`, from its own
`hφ` and `hlow`. -/
theorem hsolve_of_cube [FiniteDimensional K E] (h3 : Module.finrank K E = 3) (φ : Fin 6 → E)
    (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (hK : ¬ TwoInK (K := K) φ) (S : Set (Fin 6 → Bool))
    (hup : cube true ⊆ S) (hlow : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ S) :
    ∀ (p : Fin 3) (e : E), ∃ s : (Fin 6 → Bool) → K, OnOther p (ofK (E := E) s) ∧
      (∀ b, b ∉ S → s b = 0) ∧ (∑ b, eqW φ b * algebraMap K E (s b)) = e :=
  hsolve_of_span φ S (cube true) (cube false) hup (fun b hb => hlow b hb.2.2) (fun _ hb => hb.2.2)
    (fun _ hb => hb.2.2) (span_cube h3 φ hφ hK true) (span_cube h3 φ hφ hK false)

/-- The upper cube is lanes `32 .. 40`. -/
theorem cube_true_subset {S : Set (Fin 6 → Bool)}
    (h : ∀ l : Fin 64, 32 ≤ (l : ℕ) → (l : ℕ) < 40 → lane l ∈ S) : cube true ⊆ S := by
  rintro b ⟨h3, h4, h5⟩
  have key : ∀ x0 x1 x2 : Bool, ∃ l : Fin 64, 32 ≤ (l : ℕ) ∧ (l : ℕ) < 40 ∧
      lane l = ![x0, x1, x2, false, false, true] := by decide
  obtain ⟨l, hl1, hl2, hl⟩ := key (b 0) (b 1) (b 2)
  have hb : b = ![b 0, b 1, b 2, false, false, true] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h3
    · exact h4
    · exact h5
  rw [hb, ← hl]
  exact h l hl1 hl2

/-! ### Four lanes of each half -/

/-- The upper half's four lanes `35, 34, 33, 39`: the pattern of `card_not_span_four_le` at
`a, b, c = 0, 1, 2`. -/
def upFour : Fin 4 → Fin 6 → Bool := ![lane 35, lane 34, lane 33, lane 39]

/-- The lower half's four lanes `3, 2, 1, 7`. -/
def lowFour : Fin 4 → Fin 6 → Bool := ![lane 3, lane 2, lane 1, lane 7]

theorem image_four (φ : Fin 6 → E) (r : Fin 4 → Fin 6 → Bool) :
    eqW φ '' Set.range r = Set.range ![eqW φ (r 0), eqW φ (r 1), eqW φ (r 2), eqW φ (r 3)] := by
  rw [← Set.range_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **`hsolve` from four lanes of each half** (`35, 34, 33, 39` and `3, 2, 1, 7`) whose fold weights
span `E`. -/
theorem hsolve_of_four (φ : Fin 6 → E) (S : Set (Fin 6 → Bool)) (hupS : ∀ i, upFour i ∈ S)
    (hlowS : ∀ i, lowFour i ∈ S)
    (hU : Submodule.span K (Set.range
      ![eqW φ (lane 35), eqW φ (lane 34), eqW φ (lane 33), eqW φ (lane 39)]) = ⊤)
    (hL : Submodule.span K (Set.range
      ![eqW φ (lane 3), eqW φ (lane 2), eqW φ (lane 1), eqW φ (lane 7)]) = ⊤) :
    ∀ (p : Fin 3) (e : E), ∃ s : (Fin 6 → Bool) → K, OnOther p (ofK (E := E) s) ∧
      (∀ b, b ∉ S → s b = 0) ∧ (∑ b, eqW φ b * algebraMap K E (s b)) = e := by
  refine hsolve_of_span φ S (Set.range upFour) (Set.range lowFour) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact hupS i
  · rintro _ ⟨i, rfl⟩
    exact hlowS i
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> decide
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> decide
  · rw [image_four]
    exact hU
  · rw [image_four]
    exact hL

/-! ### How often the span fails -/

section Prob

variable [Fintype K] [Fintype E] [DecidableEq E]

open Classical in
/-- Challenges with two given coordinates in `K`: at most `|K|²·|E|⁴`. -/
theorem card_pair_mem_le (a b : Fin 6) (hab : a ≠ b) :
    (univ.filter fun φ : Fin 6 → E =>
        φ a ∈ Set.range (algebraMap K E) ∧ φ b ∈ Set.range (algebraMap K E)).card
      ≤ Fintype.card K ^ 2 * Fintype.card E ^ 4 := by
  set R : Finset E := univ.image (algebraMap K E)
  set t : Fin 6 → Finset E := fun i => if i = a ∨ i = b then R else univ
  have hR : ∀ x ∈ Set.range (algebraMap K E), x ∈ R := by
    rintro _ ⟨k, rfl⟩
    exact mem_image_of_mem _ (mem_univ k)
  have hsub : (univ.filter fun φ : Fin 6 → E =>
      φ a ∈ Set.range (algebraMap K E) ∧ φ b ∈ Set.range (algebraMap K E))
      ⊆ Fintype.piFinset t := by
    intro φ hφ
    obtain ⟨ha, hb⟩ := (mem_filter.mp hφ).2
    refine Fintype.mem_piFinset.mpr fun i => ?_
    by_cases hi : i = a ∨ i = b
    · have hti : t i = R := ite_eq_left hi
      rw [hti]
      rcases hi with rfl | rfl
      · exact hR _ ha
      · exact hR _ hb
    · have hti : t i = univ := ite_eq_right hi
      rw [hti]
      exact mem_univ _
  have hc2 : (univ.filter fun i : Fin 6 => i = a ∨ i = b).card = 2 := by
    have hfa : (univ.filter fun i : Fin 6 => i = a ∨ i = b) = {a, b} := by
      ext i
      simp
    rw [hfa, card_pair hab]
  have hc4 : (univ.filter fun i : Fin 6 => ¬ (i = a ∨ i = b)).card = 4 := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin 6)))
      (fun i => i = a ∨ i = b)
    rw [card_univ, Fintype.card_fin, hc2] at this
    omega
  have hcard : ∏ i, (t i).card = R.card ^ 2 * Fintype.card E ^ 4 := by
    simp only [t, apply_ite card, card_univ]
    rw [prod_ite, prod_const, prod_const, hc2, hc4]
  calc _ ≤ (Fintype.piFinset t).card := card_le_card hsub
    _ = R.card ^ 2 * Fintype.card E ^ 4 := by rw [Fintype.card_piFinset, hcard]
    _ ≤ Fintype.card K ^ 2 * Fintype.card E ^ 4 := by
        gcongr
        exact card_image_le.trans_eq card_univ

open Classical in
/-- **Two of `φ₀, φ₁, φ₂` in `K`**: at most `3·|K|²·|E|⁴` challenges. -/
theorem card_twoInK_le :
    (univ.filter fun φ : Fin 6 → E => TwoInK (K := K) φ).card
      ≤ 3 * (Fintype.card K ^ 2 * Fintype.card E ^ 4) := by
  set A : Fin 6 → Fin 6 → Finset (Fin 6 → E) := fun a b => univ.filter fun φ =>
    φ a ∈ Set.range (algebraMap K E) ∧ φ b ∈ Set.range (algebraMap K E)
  have hsub : (univ.filter fun φ : Fin 6 → E => TwoInK (K := K) φ) ⊆ A 0 1 ∪ A 0 2 ∪ A 1 2 := by
    intro φ hφ
    rcases (mem_filter.mp hφ).2 with h | h | h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)
  calc _ ≤ (A 0 1 ∪ A 0 2 ∪ A 1 2).card := card_le_card hsub
    _ ≤ (A 0 1).card + (A 0 2).card + (A 1 2).card := by
        refine (card_union_le _ _).trans ?_
        have := card_union_le (A 0 1) (A 0 2)
        omega
    _ ≤ Fintype.card K ^ 2 * Fintype.card E ^ 4 + Fintype.card K ^ 2 * Fintype.card E ^ 4
          + Fintype.card K ^ 2 * Fintype.card E ^ 4 :=
        add_le_add (add_le_add (card_pair_mem_le 0 1 (by decide))
          (card_pair_mem_le 0 2 (by decide))) (card_pair_mem_le 1 2 (by decide))
    _ = _ := by ring

variable [SampleableType E] {Γ : Type} [SampleableType Γ] [Fintype Γ]

open Classical in
/-- **The sharper bound** (`HIDING.md`'s `3·2^-256`): for uniform challenges, two of `φ₀, φ₁, φ₂`
lie in `K` with probability at most `3·|K|²/|E|²`. -/
theorem prob_twoInK_le :
    Pr{let x ← $ᵗ (Γ × (Fin 6 → E))}[TwoInK (K := K) x.2]
      ≤ ((3 * Fintype.card K ^ 2 : ℕ) : ENNReal) / ((Fintype.card E ^ 2 : ℕ) : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample]
  set T := univ.filter fun φ : Fin 6 → E => TwoInK (K := K) φ
  have hsub : (univ.filter fun x : Γ × (Fin 6 → E) => TwoInK (K := K) x.2)
      ⊆ (univ : Finset Γ) ×ˢ T := by
    intro x hx
    exact mem_product.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩⟩
  have hle := card_le_card hsub
  rw [card_product, card_univ] at hle
  have hT := card_twoInK_le (K := K) (E := E)
  have hE : 0 < Fintype.card E := Fintype.card_pos
  have hΓ : 0 < Fintype.card Γ := Fintype.card_pos
  have hcardT : Fintype.card (Γ × (Fin 6 → E)) = Fintype.card Γ * Fintype.card E ^ 6 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [hcardT]
  refine HiddenLayout.natCast_div_le_natCast_div (Nat.mul_pos hΓ (Nat.pow_pos hE))
    (Nat.pow_pos hE) ?_
  calc (univ.filter fun x : Γ × (Fin 6 → E) => TwoInK (K := K) x.2).card * Fintype.card E ^ 2
      ≤ (Fintype.card Γ * T.card) * Fintype.card E ^ 2 := Nat.mul_le_mul_right _ hle
    _ ≤ (Fintype.card Γ * (3 * (Fintype.card K ^ 2 * Fintype.card E ^ 4))) * Fintype.card E ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hT)
    _ = _ := by ring

open Classical in
/-- **`hsolve_of_cube`'s hypotheses fail rarely**: for uniform challenges, some coordinate is in
`{0, 1}` or two of `φ₀, φ₁, φ₂` lie in `K` with probability at most `(12·|E| + 3·|K|²)/|E|²`
(`12·2^-192 + 3·2^-256` at `|K| = 2^64`, `|E| = 2^192`). -/
theorem prob_not_solvable_le :
    Pr{let x ← $ᵗ (Γ × (Fin 6 → E))}[¬ ((∀ i, x.2 i ≠ 0 ∧ x.2 i ≠ 1) ∧ ¬ TwoInK (K := K) x.2)]
      ≤ ((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
          ((Fintype.card E ^ 2 : ℕ) : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample]
  set Z := univ.filter fun φ : Fin 6 → E => ¬ ∀ i, φ i ≠ 0 ∧ φ i ≠ 1
  set T := univ.filter fun φ : Fin 6 → E => TwoInK (K := K) φ
  have hsub : (univ.filter fun x : Γ × (Fin 6 → E) =>
      ¬ ((∀ i, x.2 i ≠ 0 ∧ x.2 i ≠ 1) ∧ ¬ TwoInK (K := K) x.2)) ⊆ (univ : Finset Γ) ×ˢ (Z ∪ T) := by
    intro x hx
    refine mem_product.mpr ⟨mem_univ _, ?_⟩
    have h := (mem_filter.mp hx).2
    by_cases hz : ∀ i, x.2 i ≠ 0 ∧ x.2 i ≠ 1
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by
        by_contra ht
        exact h ⟨hz, ht⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hz⟩)
  have hle := card_le_card hsub
  rw [card_product, card_univ] at hle
  have hZ : Z.card * Fintype.card E ≤ (2 * 6) * Fintype.card E ^ 6 := card_not_avoid_mul_le
  have hT := card_twoInK_le (K := K) (E := E)
  have hU : (Z ∪ T).card ≤ Z.card + T.card := card_union_le _ _
  have hE : 0 < Fintype.card E := Fintype.card_pos
  have hΓ : 0 < Fintype.card Γ := Fintype.card_pos
  have hcardT : Fintype.card (Γ × (Fin 6 → E)) = Fintype.card Γ * Fintype.card E ^ 6 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [hcardT]
  refine HiddenLayout.natCast_div_le_natCast_div (Nat.mul_pos hΓ (Nat.pow_pos hE))
    (Nat.pow_pos hE) ?_
  calc (univ.filter fun x : Γ × (Fin 6 → E) =>
        ¬ ((∀ i, x.2 i ≠ 0 ∧ x.2 i ≠ 1) ∧ ¬ TwoInK (K := K) x.2)).card * Fintype.card E ^ 2
      ≤ (Fintype.card Γ * (Z.card + T.card)) * Fintype.card E ^ 2 :=
        Nat.mul_le_mul_right _ (hle.trans (Nat.mul_le_mul_left _ hU))
    _ = Fintype.card Γ * ((Z.card * Fintype.card E) * Fintype.card E
          + T.card * Fintype.card E ^ 2) := by ring
    _ ≤ Fintype.card Γ * (((2 * 6) * Fintype.card E ^ 6) * Fintype.card E
          + (3 * (Fintype.card K ^ 2 * Fintype.card E ^ 4)) * Fintype.card E ^ 2) := by
        gcongr
    _ = _ := by ring

open Classical in
/-- **The four-lane bound** (through `card_not_span_four_le`): for uniform challenges, the fold
weights of lanes `35, 34, 33, 39` or of `3, 2, 1, 7` fail to span `E` with probability at most
`2·((13 + |K|)·|E| + |K|⁴)/|E|²` (about `2^-126`). -/
theorem prob_not_span_four_le [FiniteDimensional K E] (h3 : Module.finrank K E = 3) :
    Pr{let x ← $ᵗ (Γ × (Fin 6 → E))}[¬ (Submodule.span K (Set.range
        ![eqW x.2 (lane 35), eqW x.2 (lane 34), eqW x.2 (lane 33), eqW x.2 (lane 39)]) = ⊤ ∧
      Submodule.span K (Set.range
        ![eqW x.2 (lane 3), eqW x.2 (lane 2), eqW x.2 (lane 1), eqW x.2 (lane 7)]) = ⊤)]
      ≤ ((2 * ((2 * 6 + Fintype.card K + 1) * Fintype.card E + Fintype.card K ^ 4) : ℕ) : ENNReal) /
          ((Fintype.card E ^ 2 : ℕ) : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample]
  set BU := univ.filter fun φ : Fin 6 → E => Submodule.span K (Set.range
    ![eqW φ (lane 35), eqW φ (lane 34), eqW φ (lane 33), eqW φ (lane 39)]) ≠ ⊤
  set BL := univ.filter fun φ : Fin 6 → E => Submodule.span K (Set.range
    ![eqW φ (lane 3), eqW φ (lane 2), eqW φ (lane 1), eqW φ (lane 7)]) ≠ ⊤
  have hsub : (univ.filter fun x : Γ × (Fin 6 → E) => ¬ (Submodule.span K (Set.range
        ![eqW x.2 (lane 35), eqW x.2 (lane 34), eqW x.2 (lane 33), eqW x.2 (lane 39)]) = ⊤ ∧
      Submodule.span K (Set.range
        ![eqW x.2 (lane 3), eqW x.2 (lane 2), eqW x.2 (lane 1), eqW x.2 (lane 7)]) = ⊤))
      ⊆ (univ : Finset Γ) ×ˢ (BU ∪ BL) := by
    intro x hx
    refine mem_product.mpr ⟨mem_univ _, ?_⟩
    have h := (mem_filter.mp hx).2
    by_cases hu : Submodule.span K (Set.range
        ![eqW x.2 (lane 35), eqW x.2 (lane 34), eqW x.2 (lane 33), eqW x.2 (lane 39)]) = ⊤
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, fun hl => h ⟨hu, hl⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hu⟩)
  have hle := card_le_card hsub
  rw [card_product, card_univ] at hle
  have hBU : BU.card * Fintype.card E ^ 2 ≤
      ((2 * 6 + Fintype.card K + 1) * Fintype.card E + Fintype.card K ^ 4) * Fintype.card E ^ 6 :=
    card_not_span_four_le h3 (lane 35) (lane 34) (lane 33) (lane 39) 0 1 2 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hBL : BL.card * Fintype.card E ^ 2 ≤
      ((2 * 6 + Fintype.card K + 1) * Fintype.card E + Fintype.card K ^ 4) * Fintype.card E ^ 6 :=
    card_not_span_four_le h3 (lane 3) (lane 2) (lane 1) (lane 7) 0 1 2 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hU : (BU ∪ BL).card ≤ BU.card + BL.card := card_union_le _ _
  have hE : 0 < Fintype.card E := Fintype.card_pos
  have hΓ : 0 < Fintype.card Γ := Fintype.card_pos
  have hcardT : Fintype.card (Γ × (Fin 6 → E)) = Fintype.card Γ * Fintype.card E ^ 6 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [hcardT]
  refine HiddenLayout.natCast_div_le_natCast_div (Nat.mul_pos hΓ (Nat.pow_pos hE))
    (Nat.pow_pos hE) ?_
  set M := ((2 * 6 + Fintype.card K + 1) * Fintype.card E + Fintype.card K ^ 4) * Fintype.card E ^ 6
  calc _ ≤ (Fintype.card Γ * (BU.card + BL.card)) * Fintype.card E ^ 2 :=
        Nat.mul_le_mul_right _ (hle.trans (Nat.mul_le_mul_left _ hU))
    _ = Fintype.card Γ * (BU.card * Fintype.card E ^ 2 + BL.card * Fintype.card E ^ 2) := by ring
    _ ≤ Fintype.card Γ * (M + M) := by gcongr
    _ = _ := by ring

end Prob

end QuotientSecurity.Hiding
