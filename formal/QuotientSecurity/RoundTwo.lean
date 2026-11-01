-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/RoundTwo.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Protocol

/-!
# The second challenge

If the second message is not consistent with the first, the two identities hold at few points.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F] (P : Params F)

namespace Params

open Classical in
/-- **The second challenge.** If the second message is not consistent, the identities hold at no
more points than the larger of their degrees. -/
theorem card_consistentAt_le (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F)
    (α β γ : F) (h : ¬ P.Consistent stmt g R α β γ) :
    (univ.filter fun t : F => P.ConsistentAt stmt g R α β γ t).card
      ≤ max (copyDefect P g R α β γ).natDegree (gateDefect P g R α β).natDegree := by
  have key : ∀ p : F[X], p ≠ 0 → ∀ s : Finset F, (∀ t ∈ s, p.eval t = 0) →
      s.card ≤ p.natDegree := by
    intro p hp s hs
    calc s.card ≤ p.roots.toFinset.card := Finset.card_le_card fun t ht =>
          Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (hs t ht))
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := card_roots' p
  by_cases h1 : copyDefect P g R α β γ = 0
  · by_cases h2 : gateDefect P g R α β = 0
    · have h3 : R.top P ≠ P.target stmt γ := fun h3 => h ⟨h1, h2, h3⟩
      have : (univ.filter fun t : F => P.ConsistentAt stmt g R α β γ t) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun t _ ht => h3 ht.2.2
      rw [this]; simp
    · exact (key _ h2 _ fun t ht => (Finset.mem_filter.mp ht).2.2.1).trans (le_max_right _ _)
  · exact (key _ h1 _ fun t ht => (Finset.mem_filter.mp ht).2.1).trans (le_max_left _ _)

end Params

end QuotientSecurity
