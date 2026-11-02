-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Claims.Reduce
import Bridge.Claims.Tau
import Compose.Claims
import QuotientSecurity.DeployedBasis

/-!
# The statement's constants meet `reduce`'s hypotheses

`Compose.Reduce.reduce`'s constants are parameters, constrained only where needed: `beta()` a
Cantor basis (`Compose.IsCantor`) and `tau` solving `row_vanishing`'s system
(`Compose.Reduce.RowVanishing`). The statement computes both (`PcsQuotient.Domain.beta`, the pivots
of `S` and a solve per vector; `rowVanishing 24`, a Gauss–Jordan elimination); here they are checked
by kernel evaluation (`decide +kernel`, no `native_decide`):

* `beta_lanes`: the statement's `28` basis words, the first `24` F0c's `betaWords` (about 4 s);
  so `betaAt_eq_deployedBasis`: `β_k` is `QuotientSecurity.deployedBasis`'s, `k < 24`, and
  **`isCantor_statementConsts`** follows from `deployedBasis`'s kernel-checked `S(β_{k+1}) = β_k`;
* `rowVanishing_24_words` (`Tau.lean`, `22` elimination steps): `τ`'s words (`tauWords`, the
  Rust's `row_vanishing(24)` that F5's graph carries); and **`rowVanishing_statementConsts`**: the
  `22` equations `Σ_{k ≤ 22} [k ≤ j] β_{j−k} τ_k = 0` and `τ_22 = 1`, evaluated in `K` (about
  `500` products).
-/

namespace Bridge

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

/-! ## Words -/

/-- An entry of a list of `K` given by its words. -/
theorem getD_of_words {l : List K} {ws : List UInt64} (h : l.map K.lane = ws) (i : ℕ) :
    l.getD i 0 = K.ofLane (ws.getD i 0) := by
  subst h
  by_cases hi : i < l.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
    rfl

/-! ## The Cantor basis -/

/-- **The statement's Cantor basis, as words**: F0c's `betaWords` (the first `24`, which the
instance reads), then four more (by kernel evaluation of the statement's pivots and solves). -/
theorem beta_lanes : PcsQuotient.Domain.beta.toList.map K.lane =
    betaWords ++ [0xf89578714bd28f96, 0x564dda59237a3352, 0xad33bc6cc75aed38, 0x57a3104fcd0e5f34] := by
  decide +kernel

theorem betaAt_eq_getD (k : ℕ) : betaAt k = PcsQuotient.Domain.beta.toList.getD k 0 := by
  simp [betaAt, List.getD_eq_getElem?_getD]

/-- **`β_k`, `k < 24`, is the deployed basis's** (`QuotientSecurity.deployedBasis`, `beta()`'s
words). -/
theorem betaAt_eq_deployedBasis (k : ℕ) (hk : k < 22 + 2) : betaAt k = deployedBasis.β k := by
  rw [betaAt_eq_getD, getD_of_words beta_lanes,
    List.getD_append _ _ _ _ (show k < betaWords.length by rw [show betaWords.length = 24 from rfl]; omega)]
  rfl

/-- **The statement's basis is a Cantor basis** (`Compose.IsCantor`, what `Compose`'s claims theorems
ask of `beta()`). -/
theorem isCantor_statementConsts : Compose.IsCantor statementConsts.beta := by
  refine ⟨?_, fun k hk ↦ ?_⟩
  · rw [statementConsts_beta, betaAt_eq_deployedBasis 0 (by norm_num)]
    exact deployedBasis.zero
  · rw [statementConsts_beta, betaAt_eq_deployedBasis (k + 1) hk,
      betaAt_eq_deployedBasis k (by omega)]
    exact deployedBasis.succ k hk

/-! ## The rows' polynomial -/

/-- `row_vanishing(24)`'s words (the Rust's, which F5's graph carries as `tau`). -/
def tauWords : List UInt64 :=
  [5246327309480240592, 462416703093199623, 5836061695391999385, 17933131952861334950,
    18372946041939442404, 12828942987611060278, 13588355210333287157, 1205146552516504875,
    981042065287506825, 5923339044450209179, 951408172292342183, 12676167449202766892,
    13719231351162120800, 12661900118541078806, 12449589984762772511, 11682037014426230835,
    1012368888076811759, 18272804218237563919, 5328687504910262779, 18383142605220007825,
    802269026382174146, 1506959928840120550, 1]

/-- **`rowVanishing 24`, as words** (`Tau.lean`: `22` kernel-checked elimination steps). -/
theorem rowVanishing_24_words : (rowVanishing 24).map K.lane = tauWords :=
  Claims.rowVanishing_24_lanes

/-- **`τ_k`** is the word `k` of `tauWords`. -/
theorem statementTau_eq (k : ℕ) : statementTau k = K.ofLane (tauWords.getD k 0) :=
  getD_of_words rowVanishing_24_words k

theorem sum_range_eq_list (f : ℕ → K) :
    ∀ n, ∑ k ∈ Finset.range n, f k = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_eq_list f n, List.range_succ, List.map_append,
      List.sum_append]
    simp

/-- `row_vanishing(24)`'s system, in `K`, by kernel evaluation (`22` equations of `23` products). -/
theorem tau_system : ∀ j < 22 + 2, 2 ≤ j →
    ((List.range (22 + 1)).map fun k ↦
      (if k ≤ j then betaF64 (j - k) else 0) * K.ofLane (tauWords.getD k 0)).sum = 0 := by
  decide +kernel

/-- **The statement's `τ` solves `row_vanishing`'s system** (`Compose.Reduce.RowVanishing`, what
`Compose`'s claims theorems ask of `tau`): `τ_22 = 1` and, for each `β_j`, `2 ≤ j < 24`,
`Σ_{k ≤ 22} [k ≤ j] β_{j−k} τ_k = 0`. -/
theorem rowVanishing_statementConsts : Compose.Reduce.RowVanishing statementConsts 22 := by
  refine ⟨?_, fun j hj2 hj ↦ ?_⟩
  · rw [statementConsts_tau, statementTau_eq]
    rfl
  · rw [sum_range_eq_list]
    refine Eq.trans (congrArg List.sum (List.map_congr_left fun k _ ↦ ?_)) (tau_system j hj hj2)
    rw [statementConsts_tau, statementTau_eq, statementConsts_beta]
    by_cases hkj : k ≤ j
    · rw [if_pos hkj, if_pos hkj, betaAt_eq_deployedBasis (j - k) (by omega)]
      rfl
    · rw [if_neg hkj, if_neg hkj]

end Bridge

/-- info: 'Bridge.isCantor_statementConsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.isCantor_statementConsts

/-- info: 'Bridge.rowVanishing_statementConsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.rowVanishing_statementConsts
