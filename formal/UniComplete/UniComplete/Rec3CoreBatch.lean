-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's honest batch's hypotheses at the prover's
-- front state, as `CoreBatch.lean`'s `batchHolds_of`, `batchHolds_front`, `batchSyncsAt_front` for the main line.
import UniComplete.Rec3SyncVerifier
import UniComplete.CoreBatch

/-!
# π1-rec3's honest batch's hypotheses at the prover's front state

At the reference shape, for an honest trace, the prover's state when the paired batch starts (`frontOf3`) satisfies
`BatchHolds … none none` (`batchHolds3_of`, `batchHolds3_front`): every combined claim holds of its stack, is well
formed, on an aligned layout, its stack of `2^vars` words; there are no pending matrices (the walk took them). So the
paired batch synchronises with a zero terminal (`batchSyncsAt3_front`), unless `BadFp` (at `α, β`) or `BadT` (at `t`).

The relations at `t` are the main line's (`atTOf` is shared): `CoreBatch.relations_hold_front`, `atTOf_coversC2`,
`slotCondition_of_badT`, `atTOf_combined`, `stack_sizes`. They ask of Flock's output only that its end is a ring
switch whose target is `q_flock`'s ring sum (`FlockRing3`) and that its point has `h_B + 8` coordinates
(`FlockPointLen3`): named here, proved for π1-rec3's Flock prover in `Rec3Flock*.lean`.

Decision (recorded): Flock's prover is a parameter with those two facts as hypotheses, so this file does not depend
on Flock's prover's code.
-/

namespace UniComplete.Rec3

open UniStatement LeanVM.Parameters LeanVM.Protocol Finset
open UniComplete.Core (relations_hold_front atTOf_coversC2 slotCondition_of_badT stack_sizes)

/-- `squares c n` has `n` terms. -/
theorem squaresLen_coreBatch : ∀ (c : E) (n : ℕ), (squares c n).length = n
  | _, 0 => rfl
  | c, n + 1 => by rw [squares, List.length_cons, squaresLen_coreBatch (c * c) n]

/-- **Flock's ring switch**, at every writer: the end is a ring switch whose target is `q_flock`'s ring sum. -/
def FlockRing3 (flock : FlockProver Id) (logN : ℕ) (q : Array K) : Prop :=
  ∀ w : Wr, ∃ map target, ((flock logN flockMain q).run w).1.end_ = .ring map target ∧ map.length = 6 ∧
    ∑ u ∈ range (2 ^ ((flock logN flockMain q).run w).1.point.length),
      Flock.towerRingMap ((eqKernel ((flock logN flockMain q).run w).1.point).getD u 0) map * ofK (q.getD u 0) =
        target

/-- **Flock's point has `h_B + 8` coordinates**, at every writer. -/
def FlockPointLen3 (flock : FlockProver Id) (tr : Trace) : Prop :=
  ∀ w : Wr, ((flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock).run w).1.point.length =
    tr.shape.heights.getD opBlake2s 0 + 8

/-- **`BatchHolds` at `t`, `ρ`** (any challenges), no pending matrices, for an honest trace at the reference shape,
Flock's output a ring switch with its target true, `α, β` off `BadFp` and `t` off `BadT`. -/
theorem batchHolds3_of (tr : Trace) (hon : TraceHonest tr) (href : tr.shape = reference)
    {alphas : List E} (hα : alphas.length = 4) (beta gamma t rho : E) (out : FlockOut) {map : List E} {target : E}
    (hend : out.end_ = .ring map target) (hmap6 : map.length = 6)
    (hring : ∑ u ∈ range (2 ^ out.point.length),
      Flock.towerRingMap ((eqKernel out.point).getD u 0) map * ofK (tr.qflock.getD u 0) = target)
    (hlen : out.point.length = tr.shape.heights.getD opBlake2s 0 + 8)
    (hbad : ¬ BadFp tr alphas beta) (hbadT : ¬ Prob.BadT reference out.point t) :
    BatchHolds
      (commitments.filterMap fun c ↦
        (combine (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).relations c
          rho).map (c, ·))
      (layouts tr.shape (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).c2Columns)
      (stacksOf (c1Stack tr) (c2DataOf tr (eqKernel alphas) beta gamma).stack (setupStackOf tr))
      (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).ringMap none none := by
  have hslot := slotCondition_of_badT tr href t out (by omega) hbadT
  have hcov := atTOf_coversC2 tr hon href (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t out hend
  have hringMap :=
    AlgC.atTOf_some_ringMap tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t out hend
  obtain ⟨-, hcomb⟩ := atTOf_combined tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t rho
    (some out) (stacksOf (c1Stack tr) (c2DataOf tr (eqKernel alphas) beta gamma).stack (setupStackOf tr)) hα
    (fun o ho ↦ by obtain rfl := Option.some.inj ho; omega)
    (fun m hm ↦ by rw [hringMap] at hm; obtain rfl := Option.some.inj hm; omega) hcov hslot
  have hall := relations_hold_front tr hon href hα beta gamma t out hend hbad hring hlen
  have hcols : (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).c2Columns =
      Shape.c2Columns tr.shape := by
    rw [AlgC.atTOf_some_c2Columns _ _ _ _ _ _ out hend]
    exact AlgH.atTOf_c2Columns_eq hon _ alphas beta gamma t
  refine ⟨fun x hx ↦ ⟨(hcomb x hx).2 hall, (hcomb x hx).1, aligned_layoutIn _ (aligned_layouts _ _) _, ?_⟩,
    Or.inl ⟨rfl, rfl⟩⟩
  rw [hcols]
  exact stack_sizes tr href _ beta gamma x.1

/-- **The honest batch's hypotheses at π1-rec3's prover's front state**. -/
theorem batchHolds3_front (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (hon : TraceHonest tr) (href : tr.shape = reference) (seed : Digest)
    (hring : FlockRing3 flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) tr.qflock)
    (hlen : FlockPointLen3 flock tr)
    (hbad : ¬ BadFp tr (frontOf3 H commit flock tr (Wr.start seed)).1.alphas
      (frontOf3 H commit flock tr (Wr.start seed)).1.beta)
    (hbadT : ∀ out, (frontOf3 H commit flock tr (Wr.start seed)).1.flockOut = some out →
      ¬ Prob.BadT reference out.point (frontOf3 H commit flock tr (Wr.start seed)).1.t) :
    let F := (frontOf3 H commit flock tr (Wr.start seed)).1
    BatchHolds F.combined F.stackLayouts F.stackOf F.atT.ringMap none none := by
  simp only [frontOf3, FrontOut.stackOf] at hbad hbadT ⊢
  obtain ⟨map, target, hend, hmap6, hsum⟩ := hring _
  exact batchHolds3_of tr hon href (squaresLen_coreBatch _ 4) _ _ _ _ _ hend hmap6 hsum (hlen _) hbad (hbadT _ rfl)

/-- **The paired batch synchronises at π1-rec3's prover's front state, its terminal zero.** -/
theorem batchSyncsAt3_front (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (hon : TraceHonest tr) (href : tr.shape = reference) (seed : Digest)
    (hring : FlockRing3 flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) tr.qflock)
    (hlen : FlockPointLen3 flock tr)
    (hbad : ¬ BadFp tr (frontOf3 H commit flock tr (Wr.start seed)).1.alphas
      (frontOf3 H commit flock tr (Wr.start seed)).1.beta)
    (hbadT : ∀ out, (frontOf3 H commit flock tr (Wr.start seed)).1.flockOut = some out →
      ¬ Prob.BadT reference out.point (frontOf3 H commit flock tr (Wr.start seed)).1.t) :
    BatchSyncsAt3 H commit flock tr seed (fun _ ↦ 0) :=
  batchSyncs3_honest H _ _ _ _ (batchHolds3_front H commit flock tr hon href seed hring hlen hbad hbadT)

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.batchSyncsAt3_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.batchSyncsAt3_front
