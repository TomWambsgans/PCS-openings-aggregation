-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Core
import QuotientSecurity.Hiding.Rounds
import QuotientSecurity.Hiding.Model
import QuotientSecurity.Hiding.Span
import QuotientSecurity.Hiding.SpanStrong
import QuotientSecurity.Hiding.Layout
import QuotientSecurity.Hiding.Merkle
import QuotientSecurity.Hiding.Interp
import QuotientSecurity.Hiding.Sumcheck
import QuotientSecurity.Hiding.Gadget
import QuotientSecurity.Hiding.GadgetLayout
import QuotientSecurity.Hiding.Solve

/-!
# Hiding WHIR openings of `K`-valued tables (`crates/quotient/HIDING.md`)

* `Hiding.Core`: a view `A d + B r` with uniform `r` hides `d` given its claims when every
  claim-preserving change of `d` is reached by `B`; averaging over challenges costs the bad set.
* `Hiding.Rounds`: WHIR's lane rounds, the sumcheck identity, and the subspace `ker lastMap`
  (33 `K`-dimensions at `k = 6`) where claim- and `f¹`-preserving changes move them.
* `Hiding.Model`: the level-0 view (rounds, folded table, opened rows) and `level0_hides`, the
  argument of `HIDING.md` for an arbitrary layout under (Q), (S), (H), (R).
* `Hiding.Span`, `Hiding.SpanStrong`: condition (S) fails for few challenges (three lanes: about
  `2^-64`; four lanes: about `2^-127`).
* `Hiding.Layout`: the hidden layouts of `opening::Layout::hidden` (first pieces, random lanes, the
  overflow lane and its share), the claims' weights there, and the theorem with its bound.
* `Hiding.Merkle`: an unopened row keeps `|K|^(L-3)` of min-entropy given the view.
* `Hiding.Interp`: condition (Q) for a code whose basis polynomial `y` has degree `y` (WHIR's novel
  basis), by Lagrange interpolation, and the vector an unopened row's entropy uses.
* `Hiding.Sumcheck`, `Hiding.Gadget`: condition (R) for the gadget of the hidden layouts (`HIDING.md`,
  "Condition (R) for every challenge"): one entry's rounds (solvers, the last round on each half,
  two weights reach every message), the deployed patterns (`deployed_reach_all`), and
  `column_reach`: through the gadget's entries, `ker lastMap` is in the `K`-span of its moves for
  every `Φ` with no coordinate in `{0, 1}` (and `2 Φ₀ ≠ 1`), given the solvers' span.
* `Hiding.Solve`: the solvers' span (`hsolve` of `GadgetLayout.roundsReached`) from the cube lemma
  (`[E : K] = 3`: no quadratic subfield), for every `φ` with no coordinate in `{0, 1}` and at most
  one of `φ₀, φ₁, φ₂` in `K`: fails with probability at most `(12·|E| + 3·|K|²)/|E|²`; or from four
  lanes of each half through `card_not_span_four_le` (about `2^-126`); and (S) for the random lanes
  `33 .. 40` outside the same set.
-/

/-- info: 'QuotientSecurity.Hiding.hiding_of_mem_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.hiding_of_mem_range

/-- info: 'QuotientSecurity.Hiding.prEvent_le_add_prEvent_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.prEvent_le_add_prEvent_bad

/-- info: 'QuotientSecurity.Hiding.lastClaim_laneRounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.lastClaim_laneRounds

/-- info: 'QuotientSecurity.Hiding.roundsMap_mem_ker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.roundsMap_mem_ker

/-- info: 'QuotientSecurity.Hiding.level0_hides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.level0_hides

/-- info: 'QuotientSecurity.Hiding.level0_view_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.level0_view_evalDistEq

/-- info: 'QuotientSecurity.Hiding.card_not_linearIndependent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.card_not_linearIndependent_le

/-- info: 'QuotientSecurity.Hiding.card_not_span_four_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.card_not_span_four_le

/-- info: 'QuotientSecurity.Hiding.HiddenLayout.claims_stackR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.HiddenLayout.claims_stackR

/-- info: 'QuotientSecurity.Hiding.HiddenLayout.hidden_view_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.HiddenLayout.hidden_view_evalDistEq

/-- info: 'QuotientSecurity.Hiding.HiddenLayout.prob_not_foldSpans_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.HiddenLayout.prob_not_foldSpans_le

/-- info: 'QuotientSecurity.Hiding.HiddenLayout.hidden_prEvent_le_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.HiddenLayout.hidden_prEvent_le_bound

/-- info: 'QuotientSecurity.Hiding.witness_lane_pattern' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.witness_lane_pattern

/-- info: 'QuotientSecurity.Hiding.quotient_lane_pattern' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.quotient_lane_pattern

/-- info: 'QuotientSecurity.Hiding.HiddenLayout.unopened_row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.HiddenLayout.unopened_row_le

/-- info: 'QuotientSecurity.Hiding.firstEval_surjective_of_degrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.firstEval_surjective_of_degrees

/-- info: 'QuotientSecurity.Hiding.exists_unopened_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.exists_unopened_vector

/-- info: 'QuotientSecurity.Hiding.reach_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.reach_all

/-- info: 'QuotientSecurity.Hiding.deployed_reach_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.deployed_reach_all

/-- info: 'QuotientSecurity.Hiding.column_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.column_reach

/-- info: 'QuotientSecurity.Hiding.rounds_lower_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.rounds_lower_upper

/-- info: 'QuotientSecurity.Hiding.GadgetLayout.roundsReached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.GadgetLayout.roundsReached

/-- info: 'QuotientSecurity.Hiding.hsolve_of_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.hsolve_of_span

/-- info: 'QuotientSecurity.Hiding.span_one_x_y_xy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.span_one_x_y_xy

/-- info: 'QuotientSecurity.Hiding.span_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.span_face

/-- info: 'QuotientSecurity.Hiding.span_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.span_cube

/-- info: 'QuotientSecurity.Hiding.span_cube_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.span_cube_erase

/-- info: 'QuotientSecurity.Hiding.hsolve_of_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.hsolve_of_cube

/-- info: 'QuotientSecurity.Hiding.cube_true_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.cube_true_subset

/-- info: 'QuotientSecurity.Hiding.hsolve_of_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.hsolve_of_four

/-- info: 'QuotientSecurity.Hiding.card_twoInK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.card_twoInK_le

/-- info: 'QuotientSecurity.Hiding.prob_twoInK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.prob_twoInK_le

/-- info: 'QuotientSecurity.Hiding.prob_not_solvable_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.prob_not_solvable_le

/-- info: 'QuotientSecurity.Hiding.prob_not_span_four_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Hiding.prob_not_span_four_le

namespace QuotientSecurity.Hiding

/-- **`hsolve_of_cube` discharges `GadgetLayout.roundsReached`'s `hsolve`** (the interface, checked):
condition (R) for every `φ` with no coordinate in `{0, 1}` and at most one of `φ₀, φ₁, φ₂` in `K`,
given lanes `32 .. 40` and the lower half in the stack. -/
example {K E ι Y : Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] [Fintype ι]
    [DecidableEq ι] [Fintype Y] [DecidableEq Y] (L : GadgetLayout ι Y)
    (h3 : Module.finrank K E = 3) {m : ℕ} (h2K : (2 : K) = 0) (pos : ι → (Fin 6 → Bool))
    (hpos : Function.Injective pos) (Wc : Fin m → ι → Y → E) (lam : Fin m → E) (φ : Fin 6 → E)
    (μ : E) (hμ : μ ≠ 0) (β : Module.Basis (Fin 3) K E)
    (hWg : ∀ p i b, HiddenLayout.combinedW pos Wc lam b (L.gent p i) = μ * β i * patE p b)
    (hA0 : pos (L.pairA 0) = lane 0) (hB0 : pos (L.pairB 0) = lane 31)
    (hA1 : pos (L.pairA 1) = lane 1) (hB1 : pos (L.pairB 1) = lane 30) (hov : pos L.ov = lane 32)
    (hlow : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range pos)
    (hcube : ∀ l : Fin 64, 32 ≤ (l : ℕ) → (l : ℕ) < 40 → lane l ∈ Set.range pos)
    (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (hK : ¬ TwoInK (K := K) φ) :
    L.RoundsReached (K := K) pos Wc lam φ := by
  have h2E : (2 : E) = 0 := by rw [← map_ofNat (algebraMap K E) 2, h2K, map_zero]
  exact L.roundsReached h2K pos hpos Wc lam φ μ hμ β hWg hA0 hB0 hA1 hB1 hov hlow
    (hcube 33 (by decide) (by decide)) hφ (by simp [h2E])
    (hsolve_of_cube h3 φ hφ hK _ (cube_true_subset hcube) hlow)

end QuotientSecurity.Hiding
