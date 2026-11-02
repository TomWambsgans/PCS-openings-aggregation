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
