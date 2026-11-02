-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the field `K`.
import E2ECompleteness.ProverConstants
import Bridge.Claims.Constants
import Bridge.Facts

/-!
# The Statement's constants and claims, discharged

* **`constants`**: the Statement's computed constants have their defining properties
  (`Constants`): `beta()` is a Cantor basis and `coordinates(11)` reads the region's coordinates, by
  kernel evaluation (`decide +kernel`, a few seconds); `row_vanishing(24)` vanishes exactly on the
  `X` cells, from Bridge-Defs' kernel-checked words of `τ` (`Bridge.rowVanishing_24_words`,
  `Bridge.tau_system`: `rowVanishing 24` itself is never evaluated whole) and three small evaluations;
* **`claimsMatch`**: the Statement's claims are Compose's `reduce`'s at its constants
  (Bridge-Defs' `Bridge.claimsMatch_statementConsts`; `stmtConsts` is `Bridge.statementConsts`).
-/

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain Finset
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness

/-- `stmtConsts` is Bridge-Defs' `statementConsts`. -/
theorem stmtConsts_eq : stmtConsts = Bridge.statementConsts := rfl

/-- **The Statement's claims are Compose's `reduce`'s** at its constants. -/
theorem claimsMatch : Bridge.ClaimsMatch stmtConsts := Bridge.claimsMatch_statementConsts

/-- **`beta()` is a Cantor basis** (its `28` vectors), by kernel evaluation. -/
theorem isCantorBasis : IsCantorBasis := by decide +kernel

/-- **`coordinates(11)` reads the region's coordinates**, by kernel evaluation. -/
theorem coordinatesRead : CoordinatesRead 11 := by decide +kernel

/-- The rows' polynomial at `x`, from `τ`'s words. -/
theorem rowPolyAt_words (x : K) :
    rowPolyAt (22 + 2) x = ((List.range (22 + 1)).map fun k ↦
      K.ofLane (Bridge.tauWords.getD k 0) * S^[k] x).sum := by
  rw [rowPolyAt_eq_sum, Bridge.sum_range_eq_list]
  congr 1
  refine List.map_congr_left fun k hk ↦ ?_
  rw [Bridge.getD_of_words Bridge.rowVanishing_24_words,
    Bridge.Ntt.chain_getD _ (by simp at hk; omega)]

/-- The three values the rows' polynomial must not vanish at, by kernel evaluation. -/
theorem rowPoly_words_ne :
    ((List.range (22 + 1)).map fun k ↦ K.ofLane (Bridge.tauWords.getD k 0) * S^[k] 1).sum ≠ 0 ∧
      ((List.range (22 + 1)).map fun k ↦
        K.ofLane (Bridge.tauWords.getD k 0) * S^[k] (betaF64 1)).sum ≠ 0 ∧
      ((List.range (22 + 1)).map fun k ↦
        K.ofLane (Bridge.tauWords.getD k 0) * S^[k] (1 + betaF64 1)).sum ≠ 0 := by
  decide +kernel

/-- **`row_vanishing(24)` vanishes exactly on the `X` cells** (`RowVanishingProperty 24`). -/
theorem rowVanishingProperty : RowVanishingProperty 24 := by
  have hB := Bridge.Ntt.cantorUpTo_of_isCantorBasis isCantorBasis (N := basisSize) le_rfl
  have hb1 : betaAt 1 = betaF64 1 := Bridge.betaAt_eq_deployedBasis 1 (by norm_num)
  obtain ⟨n1, n2, n3⟩ := rowPoly_words_ne
  refine ⟨?_, fun j hj2 ↦ ?_, ?_, ?_, ?_⟩
  · have hl : (rowVanishing 24).length = 22 + 1 := length_rowVanishing _
    rw [List.getLast?_eq_getElem?, hl]
    have h := Bridge.getD_of_words Bridge.rowVanishing_24_words 22
    rw [List.getD_eq_getElem?_getD] at h
    rcases he : (rowVanishing 24)[22]? with _ | x
    · rw [List.getElem?_eq_none_iff] at he
      omega
    · rw [he, Option.getD_some] at h
      rw [show 22 + 1 - 1 = 22 from rfl, he, h]
      rfl
  · show rowPolyAt (22 + 2) (betaAt j) = 0
    rw [rowPolyAt_eq_sum, Bridge.sum_range_eq_list]
    refine Eq.trans (congrArg List.sum (List.map_congr_left fun k hk ↦ ?_))
      (Bridge.tau_system j j.isLt hj2)
    have hk' : k < 22 + 1 := by simp at hk; omega
    rw [Bridge.getD_of_words Bridge.rowVanishing_24_words, Bridge.Ntt.chain_getD _ (by omega),
      Bridge.Ntt.iterate_betaAt hB (by have := j.isLt; unfold basisSize; omega), mul_comm]
    by_cases hkj : k ≤ (j : ℕ)
    · rw [if_pos hkj, if_pos hkj, Bridge.betaAt_eq_deployedBasis _ (by have := j.isLt; omega)]
      rfl
    · rw [if_neg hkj, if_neg hkj]
  · rw [show (24 : ℕ) = 22 + 2 from rfl, rowPolyAt_words]
    exact n1
  · rw [show (24 : ℕ) = 22 + 2 from rfl, rowPolyAt_words, hb1]
    exact n2
  · rw [show (24 : ℕ) = 22 + 2 from rfl, rowPolyAt_words, hb1]
    exact n3

/-- **The Statement's computed constants have their defining properties.** -/
theorem constants : Constants := ⟨isCantorBasis, coordinatesRead, rowVanishingProperty⟩

end E2ECompleteness

/-- info: 'E2ECompleteness.constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.constants

/-- info: 'E2ECompleteness.claimsMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.claimsMatch
