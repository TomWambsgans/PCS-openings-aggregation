-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds

/-!
# Hiding by translation

For fixed challenges, what an opening shows is a linear function of the committed table: the
table's part `A d` plus the randomness's part `B r`, the randomness `r` uniform. If every change
`Δ` of the table that keeps the claims moves the view by something the randomness can also
produce (`A Δ ∈ range B`), then a translation of the randomness, a bijection, carries the view of
one table to the view of the other: the two are identically distributed
(`hiding_of_mem_range`). Averaged over the challenges, the views differ by at most the probability
of the challenges where this fails (`prEvent_le_add_prEvent_bad`).
-/

open OracleComp

namespace QuotientSecurity.Hiding

section Translation

variable {R V : Type} [AddCommGroup R] [SampleableType R] [AddCommGroup V]

/-- A uniform sample shifted by a constant is uniform. -/
theorem add_uniform_evalDistEq (r₀ : R) : (· + r₀) <$> ($ᵗ R) =ᵈ ($ᵗ R) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective (AddGroup.addRight_bijective r₀)

/-- **Hiding by translation.** Two affine images of a uniform sample whose offsets differ by a
value of the linear part are identically distributed. -/
theorem translate_evalDistEq (B : R →+ V) {a a' : V} (h : a - a' ∈ Set.range B) :
    (fun r => a + B r) <$> ($ᵗ R) =ᵈ (fun r => a' + B r) <$> ($ᵗ R) := by
  obtain ⟨r₀, hr₀⟩ := h
  have hcomp : (fun r => a + B r) = (fun r => a' + B r) ∘ (· + r₀) := by
    funext r
    simp only [Function.comp_apply, map_add, hr₀]
    abel
  rw [hcomp]
  have h2 := (add_uniform_evalDistEq r₀).map (fun r => a' + B r)
  rwa [Functor.map_map] at h2

end Translation

section Linear

variable {K : Type} [Field K] {D R V C : Type} [AddCommGroup D] [Module K D] [AddCommGroup R]
  [Module K R] [SampleableType R] [AddCommGroup V] [Module K V] [AddCommGroup C] [Module K C]

/-- **The view hides the table given the claims.** If every change of the table that keeps the
claims changes the view by a change the randomness can make, then any two tables with the same
claims give views with the same distribution, under uniform randomness. -/
theorem hiding_of_mem_range (A : D →ₗ[K] V) (B : R →ₗ[K] V) (cl : D →ₗ[K] C)
    (h : ∀ Δ, cl Δ = 0 → A Δ ∈ LinearMap.range B) {d d' : D} (hd : cl d = cl d') :
    (fun r => A d + B r) <$> ($ᵗ R) =ᵈ (fun r => A d' + B r) <$> ($ᵗ R) := by
  refine translate_evalDistEq B.toAddMonoidHom ?_
  obtain ⟨r, hr⟩ := h (d - d') (by rw [map_sub, hd, sub_self])
  exact ⟨r, by simpa [map_sub] using hr⟩

/-- The same for anything computed from the view (the rest of the protocol, given the challenges). -/
theorem hiding_of_mem_range_map {O : Type} (A : D →ₗ[K] V) (B : R →ₗ[K] V) (cl : D →ₗ[K] C)
    (h : ∀ Δ, cl Δ = 0 → A Δ ∈ LinearMap.range B) {d d' : D} (hd : cl d = cl d') (g : V → O) :
    (fun r => g (A d + B r)) <$> ($ᵗ R) =ᵈ (fun r => g (A d' + B r)) <$> ($ᵗ R) := by
  have := (hiding_of_mem_range A B cl h hd).map g
  simpa only [Functor.map_map] using this

end Linear

section Average

variable {Ch O : Type} [SampleableType Ch] [Fintype Ch]

/-- The experiment that draws the challenges uniformly, then runs `run` on them, and outputs both. -/
noncomputable def withChallenges (run : Ch → ProbComp O) : ProbComp (Ch × O) :=
  ($ᵗ Ch) >>= fun c => (fun o => (c, o)) <$> run c

/-- **Statistical distance at most the bad challenges' probability.** Two experiments that agree
in distribution at every good challenge give every event on (challenges, output) probabilities that
differ by at most the probability of a bad challenge. -/
theorem prEvent_le_add_prEvent_bad (real sim : Ch → ProbComp O) (good : Ch → Prop)
    (h : ∀ c, good c → real c =ᵈ sim c) (S : Ch × O → Prop) :
    Pr{let x ← withChallenges real}[S x]
      ≤ Pr{let x ← withChallenges sim}[S x] + Pr{let c ← $ᵗ Ch}[¬ good c] := by
  classical
  unfold withChallenges
  rw [prEvent_bind_eq_sum_fintype, prEvent_bind_eq_sum_fintype]
  have hbad : Pr{let c ← $ᵗ Ch}[¬ good c]
      = ∑ c, Pr{let x ← $ᵗ Ch}[x = c] * (if ¬ good c then 1 else 0) := by
    have : ($ᵗ Ch : ProbComp Ch) = ($ᵗ Ch) >>= fun c => (pure c : ProbComp Ch) := by
      rw [bind_pure]
    conv_lhs => rw [this]
    rw [prEvent_bind_eq_sum_fintype]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [prEvent_pure]
  rw [hbad, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases hc : good c
  · have heq := ((h c hc).map (fun o => (c, o))).prEvent_eq S
    rw [heq]
    simp [hc]
  · simp only [hc, not_false_eq_true, ite_true, mul_one]
    calc Pr{let x ← $ᵗ Ch}[x = c] * Pr{let y ← (fun o => (c, o)) <$> real c}[S y]
        ≤ Pr{let x ← $ᵗ Ch}[x = c] * 1 := by gcongr; exact prEvent_le_one _
      _ ≤ _ := by rw [mul_one]; exact le_add_self

end Average

end QuotientSecurity.Hiding
