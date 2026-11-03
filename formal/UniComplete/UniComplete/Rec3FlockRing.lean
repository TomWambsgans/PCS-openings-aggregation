-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `FlockProverRing.lean`'s honest-prover part
-- and of `CoreBatch.lean`'s Flock facts to π1-rec3's honest Flock prover (`Rec3Prover.lean`'s `flockProve3`).
import UniComplete.Rec3FlockShape
import UniComplete.FlockProverRing

/-!
# π1-rec3's honest Flock output: the facts the batch at `t` uses

`CoreBatch.lean`'s Flock facts (`Core.flock_point_length`, `Core.flock_ring`, `FlockP.flockRingSum`), for
`flockProve3` (`Rec3Prover.lean`), at a pure Keccak-256, every writer (any challenges):

* **`flock3_point_length`**: the point `q_flock`'s claim is at has `log_n − 6` coordinates (`log_n ≥ 14`, `flockMain`);
  `flock3_point_length'`: on a trace, `h_B + 8`;
* **`flock3_ring`**: the end is a ring switch of six stages (`flockMain`); `flockProve3_ring`: its map and target;
* **`flockRingSum3`**: Flock's ring identity, unfolded (`FlockP.flockRingHolds`'s content, in tower order): the end is
  a ring switch of six stages whose target is `Σ_u Φ(eq(point, u)) q_flock[u]`.

Only the front's draw differs from the main line's (`frontW3`), and none of these reads it: the point is
`chi_in' ++ chi_rest` (`FlockP.frontOf`) whatever the zerocheck's challenges, and the ring identity holds of the
lincheck's folds at any challenges (`FlockP.ringHolds_pure`). The proofs are the main line's through
`frontW3_eq`, `frontW3_slices`, `frontW3_shape`, `flockProve3_point`, `flockProve3_end`.

Decision (`CoreBatch.lean`'s, recorded): no term whose type is `FlockP.FlockRingHolds` of the prover's concrete output
is ever elaborated (the application elaborator normalises its result type, a `match` on the output's end, by `whnf`,
which evaluates the prover symbolically); `flockRingSum3` states the same fact unfolded (an `∃` of an equation).
-/

namespace UniComplete.Rec3

open UniStatement UniStatement.Flock LeanVM.Parameters Finset

set_option linter.deprecated false

section Ring

variable (H : List UInt8 → Id LeanVM.Protocol.Digest)

/-- **The end at π1-rec3** in tower order: the ring switch's map (`6` challenges drawn after the front) and the
target `towerTarget s map` of the slices sent. -/
theorem flockProve3_ring (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (ht : variant.slices = .tower) :
    ((flockProve3 H logN variant q).run w).1.end_ =
      .ring ((samplesW H ringMapShifts.length).run ((frontW3 H logN variant q).run w).2).1
        (towerTarget ((frontW3 H logN variant q).run w).1.2
          ((samplesW H ringMapShifts.length).run ((frontW3 H logN variant q).run w).2).1) := by
  have hc : variant.slices ≠ .claim := by rw [ht]; decide
  rw [flockProve3_end, frontW3_slices H logN variant q w hc, FlockP.endW_some, FlockP.ringEndW_eq, if_pos ht]

/-- **Flock's ring identity at π1-rec3, unfolded** (`FlockP.flockRingSum`'s statement for `flockProve3`, in tower
order): the prover ends with a ring switch of six stages whose target is `Σ_u Φ(eq(point, u)) q_flock[u]`. -/
theorem flockRingSum3 (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (ht : variant.slices = .tower) :
    ∃ map target, ((flockProve3 H logN variant q).run w).1.end_ = .ring map target ∧ map.length = 6 ∧
      ∑ u ∈ range (2 ^ ((flockProve3 H logN variant q).run w).1.point.length),
        towerRingMap ((eqKernel ((flockProve3 H logN variant q).run w).1.point).getD u 0) map * ofK (q.getD u 0) =
          target := by
  have hmap : ((samplesW H ringMapShifts.length).run ((frontW3 H logN variant q).run w).2).1.length = 6 := by
    rw [FlockP.samplesW_length]; rfl
  refine ⟨_, _, flockProve3_ring H logN variant q w ht, hmap, ?_⟩
  rw [flockProve3_point]
  generalize ((samplesW H ringMapShifts.length).run ((frontW3 H logN variant q).run w).2).1 = map at hmap ⊢
  show ∑ u ∈ range (2 ^ ((frontW3 H logN variant q).run w).1.1.point.length),
      towerRingMap ((eqKernel ((frontW3 H logN variant q).run w).1.1.point).getD u 0) map * ofK (q.getD u 0) =
    towerTarget ((frontW3 H logN variant q).run w).1.2 map
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW3_eq H logN variant q w
  have hlen : lc.challenges.length = 8 := by rw [hlc, FlockP.lcRounds_length]; rfl
  have hz : lc.z = lc.challenges.foldl FlockP.foldHigh (FlockP.lcWitnessOf variant.skip q zc) := by
    rw [hlc, FlockP.lcRounds_z]
  rw [hfr]
  show ∑ u ∈ range (2 ^ (lc.challenges.reverse ++ (zc.2.1.drop (packing - variant.skip)).drop lincheckRounds).length),
      towerRingMap ((eqKernel (lc.challenges.reverse ++
        (zc.2.1.drop (packing - variant.skip)).drop lincheckRounds)).getD u 0) map * ofK (q.getD u 0) =
    towerTarget lc.z.toList map
  rw [hz]
  exact FlockP.ringHolds_pure q _ lc.challenges map hlen hmap

end Ring

section Core

variable (H : List UInt8 → LeanVM.Protocol.Digest)

/-- **The point at π1-rec3** has `log_n − 6` coordinates (`Core.flock_point_length`'s). -/
theorem flock3_point_length (logN : ℕ) (q : Array K) (w : Wr) (hN : 14 ≤ logN) :
    ((flockProve3 (m := Id) (Pure.pure ∘ H) logN flockMain q).run w).1.point.length = logN - 6 := by
  rw [flockProve3_point]
  exact (frontW3_shape (Pure.pure ∘ H) logN flockMain q w (by decide) hN).2.2.2.2.2.2.2

/-- **The end at π1-rec3 is a ring switch of six stages** (`Core.flock_ring`'s). -/
theorem flock3_ring (logN : ℕ) (q : Array K) (w : Wr) :
    ∃ map target, ((flockProve3 (m := Id) (Pure.pure ∘ H) logN flockMain q).run w).1.end_ =
      .ring map target ∧ map.length = 6 :=
  ⟨_, _, flockProve3_ring (Pure.pure ∘ H) logN flockMain q w rfl, by rw [FlockP.samplesW_length]; rfl⟩

/-- **The point at π1-rec3 has `h_B + 8` coordinates** on a trace (`Core.flock_point_length'`'s). -/
theorem flock3_point_length' (tr : Trace) (w : Wr) :
    ((flockProve3 (m := Id) (Pure.pure ∘ H) (14 + tr.height 5) flockMain tr.qflock).run w).1.point.length =
      tr.shape.heights.getD opBlake2s 0 + 8 := by
  rw [flock3_point_length H _ _ _ (Nat.le_add_right _ _)]
  show 14 + tr.shape.heights.getD 5 0 - 6 = tr.shape.heights.getD 5 0 + 8
  omega

end Core

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.flockRingSum3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.flockRingSum3

/-- info: 'UniComplete.Rec3.flock3_point_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.flock3_point_length

/-- info: 'UniComplete.Rec3.flock3_ring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.flock3_ring
