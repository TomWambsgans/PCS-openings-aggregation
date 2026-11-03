-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls`, the block cost `hashBlocks`.
import UniComplete.Rec3Hyp
import UniComplete.FlockCost

/-!
# π1-rec3's honest Flock prover's cost, and the cost of its draws

The port of `FlockCost.lean`'s cost half to π1-rec3 (`Rec3Prover.lean`), in `ProverCost.lean`'s writer calculus
(`Cost.WC x k w P`: at most `k` blocks beyond one per byte written, at most `w` bytes):

* **The writer's draws**: the narrow draw costs one block beyond the bytes it hashes, as `sampleW`
  (`wc_sampleNarrowW`); a run of squares one block, and it has `count` terms (`wc_drawRunW`, `length_squares`).
* **Flock's honest prover at π1-rec3** (`flockCost_flockProve3H : Cost.FlockCost flockProve3H flockBlocks3 flockBytes
  flockCoords`): the zerocheck draws **one** challenge for its `log_n − k − 7` eq coordinates (the main line's
  `samplesW` drew one each), the skip's `z`, one per zerocheck round (`7 + (log_n − k − 7)`), `α`, the lincheck's
  `8`, the ring map's `6` (`flockBlocks3`); the bytes and the pending coordinates are the main line's
  (`flockBytes`, `flockCoords`: the coset values, two scalars a round, `v_a`, `v_b`, the `64` slices).

At the reference (`log_n = 32`, `flockMain`, skip `3`): `46` blocks (the main line's `67`), `3552` bytes, `19`
coordinates (`flockBlocks3_reference`, `flockCost3_reference`).

Decision (recorded): the pending claim's coordinates are carried as in the main line's `FlockCost` although
π1-rec3's stream does not use them (no matrices' reduction: the verifier walks the lincheck's terminal), so that the
main line's `Cost.FlockCost` is reused unchanged.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

set_option autoImplicit false

namespace UniComplete.Rec3

open UniComplete.Cost (WC WInv wpot wc_seq wc_mono wc_pure wc_sampleW)
open UniStatement.Flock

/-! ## The writer's draws -/

/-- `squares c n` has `n` terms. -/
theorem length_squares : ∀ (c : E) (n : ℕ), (squares c n).length = n
  | _, 0 => rfl
  | c, n + 1 => by rw [squares, List.length_cons, length_squares (c * c) n]

/-- **The narrow draw** costs at most one block beyond the bytes it hashes, which the potential holds (as
`Cost.wc_sampleW`). -/
theorem wc_sampleNarrowW : WC (sampleNarrowW callKeccak256) 1 0 fun _ _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u ↦ ⟨trivial, ?_, ?_, ?_, ?_⟩⟩
  · show (digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1 ≤
      1 + 0 + wpot c + e
    simp only [List.length_append, Cost.len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega
  · show c.stream.size ≤ c.stream.size
    exact le_rfl
  · exact le_rfl
  · show c.stream.size ≤ c.stream.size + 0
    omega
  · show c.stream.size - c.stream.size + e ≤ 1 + 0 + wpot c + e -
      ((digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1)
    simp only [List.length_append, Cost.len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega

/-- **A run of squares**: one challenge (none for an empty run), `count` terms. -/
theorem wc_drawRunW (count : ℕ) : WC (drawRunW callKeccak256 count) 1 0 fun l _ ↦ l.length = count := by
  unfold drawRunW
  split
  · next h => exact wc_mono (wc_pure _) (Nat.zero_le _) le_rfl fun b _ hb ↦ by rw [hb, List.length_nil, h]
  · refine wc_seq wc_sampleW (fun c _ _ ↦ ?_) le_rfl le_rfl
    exact wc_mono (wc_pure _) le_rfl le_rfl fun b _ hb ↦ by rw [hb, length_squares]

/-! ## Flock's prover at π1-rec3 -/

/-- **The zerocheck at π1-rec3**: the run of squares (one challenge), the skip, `7 + (log_n − k − 7)` rounds, `v_a`,
`v_b`. -/
theorem wc_zerocheckW3 (logN k : ℕ) (wit : FlockP.Wit) :
    WC (zerocheckW3 callKeccak256 logN k wit) (1 + 1 + (nFixed + (logN - k - nFixed)))
      (24 * 2 ^ k + 48 * (nFixed + (logN - k - nFixed)) + 48) fun _ _ ↦ True := by
  unfold zerocheckW3
  refine wc_seq (wc_drawRunW _) (fun sampled _ hs ↦ ?_) (by omega) (Nat.zero_le _)
  have hr : (fixedChallenges ++ sampled).length = nFixed + (logN - k - nFixed) := by
    rw [List.length_append, hs, FlockP.length_fixedChallenges]
  refine wc_seq (FlockP.wc_skipW _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (FlockP.wc_zcRounds _ _ _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (Cost.wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq (Cost.wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

/-- **Flock's front at π1-rec3**: the zerocheck, `α`, the lincheck, the `64` slices; `row_low`, `chi_in`, `chi_in'`
have at most `6 − k`, `8`, `8` coordinates. -/
theorem wc_frontW3 (logN : ℕ) (variant : Variant) (q : Array K) :
    WC (frontW3 callKeccak256 logN variant q)
      (1 + 1 + (nFixed + (logN - variant.skip - nFixed)) + 1 + lincheckRounds)
      (24 * 2 ^ variant.skip + 48 * (nFixed + (logN - variant.skip - nFixed)) + 48 + 48 * lincheckRounds +
        24 * kBits)
      fun frs _ ↦ frs.1.rowLow.length + frs.1.chiIn.length + frs.1.chiInPrime.length ≤
        packing - variant.skip + 2 * lincheckRounds := by
  unfold frontW3
  refine wc_seq (wc_zerocheckW3 _ _ _) (fun zc _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun alpha _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  refine wc_seq (FlockP.wc_lcRounds _ _ _ _) (fun lc _ hlc ↦ ?_) (by omega) (by omega)
  have hz : lc.z.toList.length = kBits := by
    rw [Array.length_toList, hlc.2, FlockP.size_lcWitnessOf, FlockP.slices_count]
  refine wc_seq (FlockP.wc_sendSlices _ _) (fun slices _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
  subst hb
  simp only [FlockP.frontOf, List.length_take, List.length_reverse, hlc.1]
  omega

end UniComplete.Rec3

namespace UniComplete

open UniStatement.Flock

/-- **π1-rec3's Flock blocks beyond its bytes**: the run of squares' one challenge, the skip's `z`, the zerocheck's
`7 + (log_n − k − 7)` round challenges, `α`, the lincheck's `8`, the ring map's `6`. -/
def flockBlocks3 (logN : ℕ) (variant : Flock.Variant) : ℕ :=
  1 + 1 + (nFixed + (logN - variant.skip - nFixed)) + 1 + lincheckRounds + ringMapShifts.length

/-- **π1-rec3's honest Flock prover's cost** (`ProverCost.lean`'s `FlockCost`): at most `flockBlocks3` blocks
beyond one per byte it writes, at most `flockBytes` bytes (the main line's), a pending claim of at most
`flockCoords` coordinates of its own. -/
theorem flockCost_flockProve3H : Cost.FlockCost Rec3.flockProve3H flockBlocks3 flockBytes flockCoords := by
  intro logN variant words
  show Cost.WC (Rec3.flockProve3 callKeccak256 logN variant words) _ _ _
  unfold Rec3.flockProve3 flockBlocks3 flockBytes flockCoords
  refine Cost.wc_seq (Rec3.wc_frontW3 _ _ _) (fun frs _ hfrs ↦ ?_) (by omega) (by omega)
  refine Cost.wc_seq (FlockP.wc_endW _ _) (fun e _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  refine Cost.wc_mono (Cost.wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
  subst hb
  obtain ⟨h1, h2, h3⟩ := FlockP.assemble_pending frs.1 frs.2 e
  rw [h1, h2, h3]
  exact hfrs

theorem flockBlocks3_reference : flockBlocks3 32 flockMain = 46 := by decide

/-- **At the reference (`log_n = 32`, skip `3`)**: `46` blocks, `3552` bytes, `19` coordinates, within
`ProverCost.lean`'s `2^32`, `2^32`, `2^16`. -/
theorem flockCost3_reference :
    flockBlocks3 32 flockMain ≤ 2 ^ 32 ∧ flockBytes 32 flockMain ≤ 2 ^ 32 ∧ flockCoords 32 flockMain ≤ 2 ^ 16 := by
  rw [flockBlocks3_reference, flockBytes_reference, flockCoords_reference]
  norm_num

end UniComplete

/-! ## Axioms -/

/-- info: 'UniComplete.flockCost_flockProve3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.flockCost_flockProve3H

/-- info: 'UniComplete.flockCost3_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.flockCost3_reference
