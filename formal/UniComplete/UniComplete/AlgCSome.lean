-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgCRel
import UniComplete.Reference

/-!
# With Flock's output, and at the reference shape (milestone 4, the algebra, follow-up)

* **`atTOf_some`**: with Flock's output `out` ending in the ring switch (`out.end_ = .ring map target`, the main
  line), `atTOf … (some out)` is `atTOf … none` with the ring relation `⟨[⟨.qflock, out.point, ringTwist, 1⟩],
  target⟩` (`ringRel`) appended to its relations, the ring map `some map` and `pending = some (out.pending,
  out.point)`: the same values, the same `C2` columns (`atTOf_some_values`, `atTOf_some_c2Columns`,
  `atTOf_some_relations`, `atTOf_some_ringMap`, `atTOf_some_pending`).
* **`relations_hold_some`**: every relation off `C2` but that last one holds at `some out`, with the ring map
  `some map` (`relations_hold_rm`: no other relation has a ring-switch term, so the map does not matter). The ring
  relation is the Flock agent's (`FlockRingHolds`).
* **`relations_hold_reference`**, **`relations_hold_some_reference`**: the same at a trace of the reference shape
  (`UniStatement.reference`, heights `18 18 18 18 17 18`), `Small` and the coordinate functionals' property
  (`Domain.coordinateFunctionalsBasis_18`) discharged.
-/

namespace UniComplete.AlgC

open UniStatement LeanVM.Parameters

/-- **The ring switch's relation** on `q_flock` (`atTOf`'s last, with Flock's output). -/
def ringRel (out : FlockOut) (target : E) : Relation := ⟨[⟨.qflock, out.point, ringTwist, 1⟩], target⟩

set_option maxHeartbeats 1000000 in
/-- **`atTOf` with Flock's output (the ring switch)**: `atTOf … none` and the ring relation, its map, the
pending matrices. -/
theorem atTOf_some (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (out : FlockOut)
    {map : List E} {target : E} (hend : out.end_ = .ring map target) :
    atTOf tr c2 alphas beta gamma t (some out) =
      { atTOf tr c2 alphas beta gamma t none with
        relations := (atTOf tr c2 alphas beta gamma t none).relations ++ [ringRel out target]
        ringMap := some map
        pending := some (out.pending, out.point) } := by
  unfold atTOf
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind, hend, Array.toList_push]
  rfl


theorem atTOf_some_values (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (out : FlockOut)
    {map : List E} {target : E} (hend : out.end_ = .ring map target) :
    (atTOf tr c2 alphas beta gamma t (some out)).values = (atTOf tr c2 alphas beta gamma t none).values := by
  rw [atTOf_some tr c2 alphas beta gamma t out hend]

theorem atTOf_some_c2Columns (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (out : FlockOut)
    {map : List E} {target : E} (hend : out.end_ = .ring map target) :
    (atTOf tr c2 alphas beta gamma t (some out)).c2Columns = (atTOf tr c2 alphas beta gamma t none).c2Columns := by
  rw [atTOf_some tr c2 alphas beta gamma t out hend]

theorem atTOf_some_relations (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (out : FlockOut)
    {map : List E} {target : E} (hend : out.end_ = .ring map target) :
    (atTOf tr c2 alphas beta gamma t (some out)).relations =
      (atTOf tr c2 alphas beta gamma t none).relations ++ [ringRel out target] := by
  rw [atTOf_some tr c2 alphas beta gamma t out hend]

theorem atTOf_some_ringMap (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (out : FlockOut)
    {map : List E} {target : E} (hend : out.end_ = .ring map target) :
    (atTOf tr c2 alphas beta gamma t (some out)).ringMap = some map := by
  rw [atTOf_some tr c2 alphas beta gamma t out hend]

theorem atTOf_some_pending (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (out : FlockOut)
    {map : List E} {target : E} (hend : out.end_ = .ring map target) :
    (atTOf tr c2 alphas beta gamma t (some out)).pending = some (out.pending, out.point) := by
  rw [atTOf_some tr c2 alphas beta gamma t out hend]

/-- **With Flock's output, every relation off `C2` but the last (the ring switch's) holds**, at the layouts the
verifier states, the prover's stacks and the ring map `some map`. -/
theorem relations_hold_some {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) {alphas : List E} (hα : alphas.length = 4)
    (beta gamma t : E) (out : FlockOut) {map : List E} {target : E} (hend : out.end_ = .ring map target) :
    (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).relations.getLast? =
        some (ringRel out target) ∧
    ∀ rel ∈ (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).relations.dropLast,
      rel.commitment ≠ .c2 →
      UniComplete.Relation.Holds (layoutIn (layouts tr.shape
          (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).c2Columns))
        (stackOfTr tr (c2DataOf tr (eqKernel alphas) beta gamma))
        (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).ringMap rel := by
  rw [atTOf_some_relations _ _ _ _ _ _ out hend]
  refine ⟨List.getLast?_concat .., fun rel hrel ↦ ?_⟩
  rw [List.dropLast_concat] at hrel
  exact relations_hold_rm hH hS hC hα beta gamma t _ _ rel hrel

/-! ### At the reference shape -/

theorem small_of_reference {tr : Trace} (href : tr.shape = reference) : Small tr := by
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · have h : ∀ t < 6, [18, 18, 18, 18, 17, 18].getD t 0 ≤ 28 := by decide
    show tr.shape.heights.getD t 0 ≤ 28
    rw [href, reference_heights]
    exact h t ht
  · rw [href]
    decide +kernel

theorem coordinateFunctionalsBasis_reference {tr : Trace} (href : tr.shape = reference) :
    Domain.CoordinateFunctionalsBasis (tr.height opBlake2s) := by
  have h : tr.height opBlake2s = 18 := by
    show tr.shape.heights.getD opBlake2s 0 = 18
    rw [href, reference_heights]
    rfl
  rw [h]
  exact Domain.coordinateFunctionalsBasis_18

/-- **`relations_hold` at the reference shape**: an honest placed trace of the reference shape needs no other
hypothesis (`Small` and the coordinate functionals' property hold there). -/
theorem relations_hold_reference {tr : Trace} (hH : TraceHonest tr) (href : tr.shape = reference)
    {alphas : List E} (hα : alphas.length = 4) (beta gamma t : E) :
    ∀ rel ∈ (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).relations,
      rel.commitment ≠ .c2 →
      UniComplete.Relation.Holds (layoutIn (layouts tr.shape
          (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).c2Columns))
        (stackOfTr tr (c2DataOf tr (eqKernel alphas) beta gamma))
        (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).ringMap rel :=
  relations_hold hH (small_of_reference href) (coordinateFunctionalsBasis_reference href) hα beta gamma t

/-- **`relations_hold_some` at the reference shape.** -/
theorem relations_hold_some_reference {tr : Trace} (hH : TraceHonest tr) (href : tr.shape = reference)
    {alphas : List E} (hα : alphas.length = 4) (beta gamma t : E) (out : FlockOut) {map : List E} {target : E}
    (hend : out.end_ = .ring map target) :
    (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).relations.getLast? =
        some (ringRel out target) ∧
    ∀ rel ∈ (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).relations.dropLast,
      rel.commitment ≠ .c2 →
      UniComplete.Relation.Holds (layoutIn (layouts tr.shape
          (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).c2Columns))
        (stackOfTr tr (c2DataOf tr (eqKernel alphas) beta gamma))
        (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).ringMap rel :=
  relations_hold_some hH (small_of_reference href) (coordinateFunctionalsBasis_reference href) hα beta gamma t out
    hend

end UniComplete.AlgC

/-- info: 'UniComplete.AlgC.atTOf_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.atTOf_some

/-- info: 'UniComplete.AlgC.relations_hold_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.relations_hold_some

/-- info: 'UniComplete.AlgC.relations_hold_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.relations_hold_reference

/-- info: 'UniComplete.AlgC.relations_hold_some_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.relations_hold_some_reference
