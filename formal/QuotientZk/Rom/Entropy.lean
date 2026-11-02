-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import VCVio.OracleComp.EvalDist.Sum
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Hitting a value that keeps its entropy given the view

A secret `s` is uniform; the world sees `Vf s` (the view) and runs `R (Vf s)`, which lists some
candidates `f z` (at most `N` of them). If, given the view, each candidate `w` is "hit" by the
secret with probability at most `δ` (`hent`: `Pr[Vf s = v ∧ hit s w] ≤ δ · Pr[Vf s = v]`, the
form of `QuotientSecurity.Hiding.HiddenLayout.unopened_row_le`), then a listed candidate is hit
with probability at most `N · δ` (`prEvent_hit_le`): what `R` does depends on the secret only
through the view.
-/

open OracleComp
open scoped ENNReal

namespace QuotientZk

section Sums

variable {Z W : Type}

/-- The indicator of a finite list sums to the number of its distinct elements. -/
theorem tsum_ite_mem_le [DecidableEq W] (l : List W) :
    ∑' w, (if w ∈ l then (1 : ℝ≥0∞) else 0) ≤ l.length := by
  rw [tsum_eq_sum (s := l.toFinset) fun w hw => by
    simp only [List.mem_toFinset] at hw; simp [hw]]
  calc ∑ w ∈ l.toFinset, (if w ∈ l then (1 : ℝ≥0∞) else 0)
      = ∑ w ∈ l.toFinset, (1 : ℝ≥0∞) :=
        Finset.sum_congr rfl fun w hw => by simp only [List.mem_toFinset] at hw; simp [hw]
    _ = l.toFinset.card := by simp
    _ ≤ l.length := by exact_mod_cast List.toFinset_card_le l

open Classical in
/-- A union bound: some listed element satisfies `P` with probability at most the sum, over the
elements satisfying `P`, of their probability of being listed. -/
theorem prEvent_exists_mem_le (mz : ProbComp Z) (f : Z → List W) (P : W → Prop) :
    Pr{let z ← mz}[∃ w ∈ f z, P w] ≤
      ∑' w, if P w then Pr{let z ← mz}[w ∈ f z] else 0 := by
  classical
  rw [prEvent_eq_tsum_ite]
  simp_rw [prEvent_eq_tsum_ite mz (fun z => _ ∈ f z)]
  calc ∑' z, (if ∃ w ∈ f z, P w then Pr{let y ← mz}[y = z] else 0)
      ≤ ∑' z, ∑' w, (if P w then (if w ∈ f z then Pr{let y ← mz}[y = z] else 0) else 0) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        split_ifs with h
        · obtain ⟨w, hw, hP⟩ := h
          refine le_trans (le_of_eq ?_) (ENNReal.le_tsum w)
          simp [hP, hw]
        · exact zero_le
    _ = ∑' w, ∑' z, (if P w then (if w ∈ f z then Pr{let y ← mz}[y = z] else 0) else 0) :=
        ENNReal.tsum_comm
    _ = _ := by
        refine tsum_congr fun w => ?_
        split_ifs <;> simp

/-- The expected number of listed elements is at most the bound on the list's length. -/
theorem tsum_prEvent_mem_le [DecidableEq W] (mz : ProbComp Z) (f : Z → List W) (N : ℕ)
    (hN : ∀ z ∈ support mz, (f z).length ≤ N) :
    ∑' w, Pr{let z ← mz}[w ∈ f z] ≤ N := by
  classical
  simp_rw [prEvent_eq_tsum_ite mz (fun z => _ ∈ f z)]
  rw [ENNReal.tsum_comm]
  calc ∑' z, ∑' w, (if w ∈ f z then Pr{let y ← mz}[y = z] else 0)
      = ∑' z, Pr{let y ← mz}[y = z] * ∑' w, (if w ∈ f z then (1 : ℝ≥0∞) else 0) := by
        refine tsum_congr fun z => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun w => ?_
        split_ifs <;> simp
    _ ≤ ∑' z, Pr{let y ← mz}[y = z] * N := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support mz
        · exact mul_le_mul_right ((tsum_ite_mem_le (f z)).trans (by exact_mod_cast hN z hz)) _
        · rw [prEvent_eq_zero_of_not_mem_support _ hz]; simp
    _ = N := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

end Sums

section Hit

variable {S V Z W : Type} [SampleableType S]

omit [SampleableType S] in
open Classical in
/-- Summing over the secret, grouped by the view. -/
theorem tsum_group (Vf : S → V) (F : V → S → ℝ≥0∞) :
    ∑' s, F (Vf s) s = ∑' v, ∑' s, (if Vf s = v then F v s else 0) := by
  classical
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun s => ?_
  rw [tsum_eq_single (Vf s) fun v hv => by rw [if_neg (Ne.symm hv)]]
  simp

/-- **Hitting a value that keeps its entropy given the view.** -/
theorem prEvent_hit_le [DecidableEq W] (Vf : S → V) (R : V → ProbComp Z) (f : Z → List W)
    (hit : S → W → Prop) (good : W → Prop) (N : ℕ) (δ : ℝ≥0∞)
    (hent : ∀ w, good w → ∀ v,
      Pr{let s ← $ᵗ S}[Vf s = v ∧ hit s w] ≤ δ * Pr{let s ← $ᵗ S}[Vf s = v])
    (hgood : ∀ s, ∀ z ∈ support (R (Vf s)), ∀ w ∈ f z, good w)
    (hN : ∀ s, ∀ z ∈ support (R (Vf s)), (f z).length ≤ N) :
    Pr{let x ← (do let s ← $ᵗ S; let z ← R (Vf s); return (s, z))}[∃ w ∈ f x.2, hit x.1 w] ≤
      N * δ := by
  classical
  set μ : S → ℝ≥0∞ := fun s => Pr{let y ← ($ᵗ S : ProbComp S)}[y = s]
  set G : V → W → ℝ≥0∞ := fun v w => Pr{let z ← R v}[w ∈ f z]
  -- the experiment as a sum over the secret
  have h1 : Pr{let x ← (do let s ← $ᵗ S; let z ← R (Vf s); return (s, z))}[∃ w ∈ f x.2, hit x.1 w]
      = ∑' s, μ s * Pr{let z ← R (Vf s)}[∃ w ∈ f z, hit s w] := by
    rw [prEvent_bind_eq_tsum]
    refine tsum_congr fun s => ?_
    congr 1
    have : (do let z ← R (Vf s); pure (s, z) : ProbComp (S × Z)) =
        (fun z => (s, z)) <$> R (Vf s) := by simp [map_eq_bind_pure_comp]
    rw [this, prEvent_map]
  -- a candidate that is not good is never listed
  have hG : ∀ s w, ¬ good w → G (Vf s) w = 0 := fun s w hw =>
    prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hwz => hw (hgood s z hz w hwz)
  -- the union bound, and the grouping by the view
  have h2 : ∀ s, μ s * Pr{let z ← R (Vf s)}[∃ w ∈ f z, hit s w] ≤
      ∑' w, if good w then μ s * (if hit s w then G (Vf s) w else 0) else 0 := by
    intro s
    refine (mul_le_mul_right (prEvent_exists_mem_le (R (Vf s)) f (hit s)) _).trans ?_
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun w => ?_
    by_cases hw : good w
    · simp [hw, G]
    · simp only [hw, if_false]
      split_ifs
      · exact le_of_eq (by rw [mul_eq_zero]; exact Or.inr (hG s w hw))
      · simp
  calc _ = ∑' s, μ s * Pr{let z ← R (Vf s)}[∃ w ∈ f z, hit s w] := h1
    _ ≤ ∑' s, ∑' w, (if good w then μ s * (if hit s w then G (Vf s) w else 0) else 0) :=
        ENNReal.tsum_le_tsum h2
    _ = ∑' w, ∑' s, (if good w then μ s * (if hit s w then G (Vf s) w else 0) else 0) :=
        ENNReal.tsum_comm
    _ ≤ ∑' w, ∑' v, G v w * (δ * Pr{let s ← $ᵗ S}[Vf s = v]) := by
        refine ENNReal.tsum_le_tsum fun w => ?_
        by_cases hw : good w
        · simp only [hw, if_true]
          rw [tsum_group Vf (fun v s => μ s * (if hit s w then G v w else 0))]
          refine ENNReal.tsum_le_tsum fun v => ?_
          calc ∑' s, (if Vf s = v then μ s * (if hit s w then G v w else 0) else 0)
              = G v w * ∑' s, (if Vf s = v ∧ hit s w then μ s else 0) := by
                rw [← ENNReal.tsum_mul_left]
                refine tsum_congr fun s => ?_
                by_cases h1 : Vf s = v <;> by_cases h2 : hit s w <;> simp [h1, h2, mul_comm]
            _ = G v w * Pr{let s ← $ᵗ S}[Vf s = v ∧ hit s w] := by
                rw [prEvent_eq_tsum_ite]
            _ ≤ G v w * (δ * Pr{let s ← $ᵗ S}[Vf s = v]) := mul_le_mul_right (hent w hw v) _
        · simp [hw]
    _ = δ * ∑' v, Pr{let s ← $ᵗ S}[Vf s = v] * ∑' w, G v w := by
        rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun v => ?_
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun w => ?_
        ring
    _ ≤ δ * ∑' v, Pr{let s ← $ᵗ S}[Vf s = v] * N := by
        refine mul_le_mul_right (ENNReal.tsum_le_tsum fun v => ?_) _
        by_cases hv : ∃ s, Vf s = v
        · obtain ⟨s, rfl⟩ := hv
          exact mul_le_mul_right (tsum_prEvent_mem_le (R (Vf s)) f N (hN s)) _
        · have : Pr{let s ← $ᵗ S}[Vf s = v] = 0 :=
            prEvent_eq_zero_of_forall_not _ _ fun s hs => hv ⟨s, hs⟩
          simp [this]
    _ ≤ δ * N := by
        rw [ENNReal.tsum_mul_right]
        refine mul_le_mul_right (mul_le_of_le_one_left (zero_le) ?_) _
        have := tsum_prEvent_le_one (Vf <$> ($ᵗ S : ProbComp S))
        simpa [prEvent_map] using this
    _ = N * δ := mul_comm _ _

end Hit

end QuotientZk
