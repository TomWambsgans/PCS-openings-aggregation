-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The narrow challenges are π1-rec3's
-- (`crates/leanvm_flock_gas/src/transcript.rs`: `NARROW_BITS`, `narrow`, `Channel::sample_narrow`,
-- `sumcheck_drawn`), transcribed as `UniStatement.narrowE` (`formal/UniStatement/UniStatement/Rec.lean`).
import UniSound.Sumcheck
import UniStatement.Rec
import LeanVM.Parameters.Field

/-!
# Narrow challenges: a uniform hash output cut to 160 bits

From π1-rec2 on, every challenge of the batching sumcheck is `narrow(x) = E::new(x.c0, x.c1, x.c2 & 0xFFFF_FFFF)` of
the hash's uniform `x ∈ E` (`UniStatement.narrowE`): a uniform draw from a set of `2^160` elements. The rounds'
errors are then counts over `E` with each value of `narrowE` hit by at most `2^32` hash outputs:

* **`card_narrowE_fiber_le`**: each fiber of `narrowE` has at most `2^32` elements (it injects into `[0, 2^32)` by
  the top `32` bits of limb `2`; the other `160` bits are the value's).
* **Generic in the cut** (`nw : E → E` with fibers of at most `2^32` elements, `hnw`), so that the bounds below
  are proved once for any such map (and `narrowE` is one, `card_narrowE_fiber_le`):
  * **`prEvent_narrow_le`**: `Pr_x[nw x ∈ B] ≤ 2^32 |B| / |E|` (and `prEvent_narrow_pred_le`, for a predicate);
  * **`prEvent_narrow_root_le`**: Schwartz–Zippel at a narrow point, `2^32 · Σ deg / |E|`, i.e. `Σ deg / 2^160`
    (`prEvent_root_le` with the cut);
  * **`SumOracle.round_sound_narrow`**, **`SumOracle.step_sound_narrow`**: `SumOracle.round_sound` and
    `SumOracle.step_sound` (`Sumcheck.lean`) with the round's challenge `nw (c.headD 0)`, at `2 · 2^32 / |E|`;
    the narrow rounds' claims and point (`claimAfterN`, `pointAfterN`, `SumStateN`) are `claimAfter`,
    `pointAfter`, `SumState` with each challenge cut (`claimAfterN_id`, `pointAfterN_id`: at `nw = id` they are
    those).

Decisions (recorded): the file imports `UniSound.Sumcheck` (not only `UniSound.Prob`), since the narrow rounds are
`SumOracle`'s; the challenge stays the uniform draw `c` (the chain's `Compose.draws E 1`) and the cut is applied in
the event, as the verifier applies it (`sampleNarrow`); the bounds are stated with the natural-number numerator
`2 · 2^32`, `2^32 · Σ deg` over `|E|`, as `Prob.lean`'s.
-/

namespace UniSound

open LeanVM.Parameters OracleComp Finset UniStatement Polynomial
open scoped ENNReal

/-! ## The fibers of `narrowE` -/

theorem narrowE_limb0 (x : E) : (narrowE x).limb 0 = x.limb 0 := rfl

theorem narrowE_limb1 (x : E) : (narrowE x).limb 1 = x.limb 1 := rfl

theorem narrowE_limb2 (x : E) :
    (narrowE x).limb 2 = K.ofLane ((x.limb 2).lane &&& 0xFFFFFFFF) := rfl

theorem K_ofLane_lane (a : K) : K.ofLane a.lane = a := rfl

theorem K_lane_ofLane (w : UInt64) : (K.ofLane w).lane = w := rfl

/-- A 64-bit lane is its low `32` bits and its high `32`. -/
theorem uint64_eq_of_and_of_div {u v : UInt64} (h1 : u &&& 0xFFFFFFFF = v &&& 0xFFFFFFFF)
    (h2 : u.toNat / 2 ^ 32 = v.toNat / 2 ^ 32) : u = v := by
  have hm : ∀ w : UInt64, (w &&& 0xFFFFFFFF).toNat = w.toNat % 2 ^ 32 := fun w => by
    rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have h1' : u.toNat % 2 ^ 32 = v.toNat % 2 ^ 32 := by rw [← hm, ← hm, h1]
  apply UInt64.toNat_inj.mp
  rw [← Nat.div_add_mod u.toNat (2 ^ 32), ← Nat.div_add_mod v.toNat (2 ^ 32), h1', h2]

/-- The top `32` bits of limb `2`, the bits `narrowE` drops. -/
def narrowTop (x : E) : ℕ := (x.limb 2).lane.toNat / 2 ^ 32

theorem narrowTop_lt (x : E) : narrowTop x < 2 ^ 32 := by
  unfold narrowTop
  have h := UInt64.toNat_lt (x.limb 2).lane
  exact Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact h)

/-- Two hash outputs with the same narrow value and the same dropped bits are equal. -/
theorem eq_of_narrowE_eq {x y : E} (h : narrowE x = narrowE y) (ht : narrowTop x = narrowTop y) :
    x = y := by
  have h0 : x.limb 0 = y.limb 0 := by
    rw [← narrowE_limb0 x, ← narrowE_limb0 y, h]
  have h1 : x.limb 1 = y.limb 1 := by
    rw [← narrowE_limb1 x, ← narrowE_limb1 y, h]
  have h2 : x.limb 2 = y.limb 2 := by
    have hl : (x.limb 2).lane &&& 0xFFFFFFFF = (y.limb 2).lane &&& 0xFFFFFFFF := by
      rw [← K_lane_ofLane ((x.limb 2).lane &&& 0xFFFFFFFF),
        ← K_lane_ofLane ((y.limb 2).lane &&& 0xFFFFFFFF), ← narrowE_limb2, ← narrowE_limb2, h]
    rw [← K_ofLane_lane (x.limb 2), ← K_ofLane_lane (y.limb 2), uint64_eq_of_and_of_div hl ht]
  refine E.ext fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **Each fiber of `narrowE` has at most `2^32` elements**: it injects into `[0, 2^32)` by the dropped bits. -/
theorem card_narrowE_fiber_le (s : E) : (univ.filter fun x ↦ narrowE x = s).card ≤ 2 ^ 32 := by
  calc (univ.filter fun x ↦ narrowE x = s).card ≤ (range (2 ^ 32)).card :=
        card_le_card_of_injOn narrowTop (fun x _ => mem_range.mpr (narrowTop_lt x))
          (fun x hx y hy hxy =>
            eq_of_narrowE_eq (((mem_filter.mp (Finset.mem_coe.mp hx)).2).trans
              ((mem_filter.mp (Finset.mem_coe.mp hy)).2).symm) hxy)
    _ = 2 ^ 32 := card_range _

/-! ## A uniform challenge, cut -/

section Cut

variable (nw : E → E) (hnw : ∀ s, (univ.filter fun x ↦ nw x = s).card ≤ 2 ^ 32)

include hnw in
/-- The hash outputs whose cut lies in `B`: at most `2^32 |B|`. -/
theorem card_filter_cut_mem_le (B : Finset E) :
    (univ.filter fun x ↦ nw x ∈ B).card ≤ 2 ^ 32 * B.card := by
  classical
  have hmaps : ∀ x ∈ (univ.filter fun x ↦ nw x ∈ B), nw x ∈ B := fun x hx => (mem_filter.mp hx).2
  rw [Finset.card_eq_sum_card_fiberwise (f := nw) (t := B) hmaps]
  calc ∑ s ∈ B, ((univ.filter fun x ↦ nw x ∈ B).filter fun x ↦ nw x = s).card
      ≤ ∑ _s ∈ B, 2 ^ 32 := sum_le_sum fun s _ =>
        (card_le_card fun x hx => by
          simp only [mem_filter, mem_univ, true_and] at hx ⊢
          exact hx.2).trans (hnw s)
    _ = 2 ^ 32 * B.card := by rw [sum_const, smul_eq_mul, mul_comm]

include hnw in
/-- **A narrow challenge lies in `B`** with probability at most `2^32 |B| / |E|`. -/
theorem prEvent_narrow_le (B : Finset E) :
    Pr{let c ← Compose.draws E 1}[nw (c.headD 0) ∈ B] ≤
      ((2 ^ 32 * B.card : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  classical
  refine prEvent_draws_le_of_card 0 _ _ ?_
  rw [pow_zero, mul_one]
  refine le_trans (le_of_eq ?_) (card_filter_cut_mem_le nw hnw B)
  convert card_filter_fin_one (fun t => nw t ∈ B) using 2

include hnw in
/-- **A narrow challenge satisfies `Q`** with probability at most `2^32` times `Q`'s count over `|E|`. -/
theorem prEvent_narrow_pred_le (Q : E → Prop) [DecidablePred Q] :
    Pr{let c ← Compose.draws E 1}[Q (nw (c.headD 0))] ≤
      ((2 ^ 32 * (univ.filter Q).card : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  (prEvent_mono _ _ _ fun c h => by simpa using h).trans (prEvent_narrow_le nw hnw (univ.filter Q))

include hnw in
/-- **Schwartz–Zippel at a narrow point**: some nonzero polynomial of the list vanishes there with probability at
most `2^32` times the sum of their degrees over `|E|`, i.e. the sum of the degrees over `2^160`. -/
theorem prEvent_narrow_root_le (ps : List (Polynomial E)) :
    Pr{let c ← Compose.draws E 1}[∃ p ∈ ps, p ≠ 0 ∧ p.eval (nw (c.headD 0)) = 0] ≤
      ((2 ^ 32 * (ps.map Polynomial.natDegree).sum : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  classical
  refine (prEvent_narrow_pred_le nw hnw (fun t => ∃ p ∈ ps, p ≠ 0 ∧ p.eval t = 0)).trans ?_
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (card_exists_root_le ps))) _

/-! ## The sumcheck's rounds with narrow challenges -/

include hnw in
/-- **A round of the sumcheck with a narrow challenge is sound**: from a false claim, the round's narrow challenge
makes the next claim true with probability at most `2 · 2^32 / |E|`, whatever the message. -/
theorem SumOracle.round_sound_narrow (O : SumOracle) (r : List E) (hr : r.length < O.vars)
    (claim c0 c2 : E) :
    Pr{let c ← Compose.draws E 1}[claim ≠ O.T r ∧
        polyEval (roundCoeffs claim c0 c2) (nw (c.headD 0)) = O.T (r ++ [nw (c.headD 0)])] ≤
      ((2 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  set D : Polynomial E := roundPolyP claim c0 c2 - O.H r with hD
  have himp : ∀ c : List E, (claim ≠ O.T r ∧
      polyEval (roundCoeffs claim c0 c2) (nw (c.headD 0)) = O.T (r ++ [nw (c.headD 0)])) →
        ∃ p ∈ [D], p ≠ 0 ∧ p.eval (nw (c.headD 0)) = 0 := by
    intro c ⟨hne, heq⟩
    refine ⟨D, List.mem_singleton_self _, fun h0 => hne ?_, ?_⟩
    · have h1 : roundPolyP claim c0 c2 = O.H r := sub_eq_zero.mp h0
      rw [O.T_eq r hr, ← h1, roundPolyP_sum]
    · rw [hD, Polynomial.eval_sub, ← polyEval_roundCoeffs, O.eval_H, heq, sub_self]
  refine (prEvent_mono _ _ _ himp).trans ((prEvent_narrow_root_le nw hnw [D]).trans ?_)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  rw [mul_comm 2]
  exact Nat.mul_le_mul_left _
    ((natDegree_sub_le _ _).trans (max_le (natDegree_roundPolyP_le _ _ _) (O.deg_H r)))

end Cut

/-- **The claims along narrow rounds**: `claimAfter` with each round's challenge cut by `nw`. -/
def claimAfterN (nw : E → E) : E → List (List E × List E) → E
  | claim, [] => claim
  | claim, (m, c) :: rest =>
    claimAfterN nw (polyEval (roundCoeffs claim (m.getD 0 0) (m.getD 1 0)) (nw (c.headD 0))) rest

/-- The narrow rounds' point: each round's challenge cut. -/
def pointAfterN (nw : E → E) (rounds : List (List E × List E)) : List E :=
  rounds.map fun x => nw (x.2.headD 0)

theorem claimAfterN_id : ∀ (claim : E) (rs : List (List E × List E)),
    claimAfterN id claim rs = claimAfter claim rs
  | _, [] => rfl
  | _, (_, _) :: rest => claimAfterN_id _ rest

theorem pointAfterN_id (rs : List (List E × List E)) : pointAfterN id rs = pointAfter rs := rfl

theorem claimAfterN_append (nw : E → E) (claim : E) (rs : List (List E × List E)) (m c : List E) :
    claimAfterN nw claim (rs ++ [(m, c)]) =
      polyEval (roundCoeffs (claimAfterN nw claim rs) (m.getD 0 0) (m.getD 1 0)) (nw (c.headD 0)) := by
  induction rs generalizing claim with
  | nil => rfl
  | cons x rs ih => exact ih _

theorem pointAfterN_append (nw : E → E) (rs : List (List E × List E)) (m c : List E) :
    pointAfterN nw (rs ++ [(m, c)]) = pointAfterN nw rs ++ [nw (c.headD 0)] := by
  simp [pointAfterN]

theorem length_pointAfterN (nw : E → E) (rs : List (List E × List E)) :
    (pointAfterN nw rs).length = rs.length := by
  simp [pointAfterN]

/-- **The narrow sumcheck's state** after its rounds `rs` from `target`: the claim is the partial sum at the point
so far (`SumState` with the challenges cut). -/
def SumStateN (O : SumOracle) (nw : E → E) (target : E) (rs : List (List E × List E)) : Prop :=
  claimAfterN nw target rs = O.T (pointAfterN nw rs)

/-- **Each narrow round of the sumcheck**, as the chain's: its state from false to true with probability at most
`2 · 2^32 / |E|`. -/
theorem SumOracle.step_sound_narrow (O : SumOracle) (nw : E → E)
    (hnw : ∀ s, (univ.filter fun x ↦ nw x = s).card ≤ 2 ^ 32) (target : E)
    (rs : List (List E × List E)) (hr : rs.length < O.vars) (m : List E) :
    Pr{let c ← Compose.draws E 1}[¬ SumStateN O nw target rs ∧ SumStateN O nw target (rs ++ [(m, c)])] ≤
      ((2 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have himp : ∀ c : List E, (¬ SumStateN O nw target rs ∧ SumStateN O nw target (rs ++ [(m, c)])) →
      (claimAfterN nw target rs ≠ O.T (pointAfterN nw rs) ∧
        polyEval (roundCoeffs (claimAfterN nw target rs) (m.getD 0 0) (m.getD 1 0)) (nw (c.headD 0)) =
          O.T (pointAfterN nw rs ++ [nw (c.headD 0)])) := by
    intro c ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    unfold SumStateN at h2
    rwa [claimAfterN_append, pointAfterN_append] at h2
  exact (prEvent_mono _ _ _ himp).trans
    (O.round_sound_narrow nw hnw (pointAfterN nw rs) (by rw [length_pointAfterN]; exact hr) _ _ _)

/-- **π1-rec3's narrow rounds** (`narrowE`): `SumOracle.step_sound_narrow` at the verifier's cut. -/
theorem SumOracle.step_sound_narrowE (O : SumOracle) (target : E) (rs : List (List E × List E))
    (hr : rs.length < O.vars) (m : List E) :
    Pr{let c ← Compose.draws E 1}[¬ SumStateN O narrowE target rs ∧
        SumStateN O narrowE target (rs ++ [(m, c)])] ≤
      ((2 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  O.step_sound_narrow narrowE card_narrowE_fiber_le target rs hr m

end UniSound

/-- info: 'UniSound.card_narrowE_fiber_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.card_narrowE_fiber_le

/-- info: 'UniSound.prEvent_narrow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.prEvent_narrow_le

/-- info: 'UniSound.prEvent_narrow_pred_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.prEvent_narrow_pred_le

/-- info: 'UniSound.prEvent_narrow_root_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.prEvent_narrow_root_le

/-- info: 'UniSound.SumOracle.round_sound_narrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.SumOracle.round_sound_narrow

/-- info: 'UniSound.SumOracle.step_sound_narrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.SumOracle.step_sound_narrow

/-- info: 'UniSound.SumOracle.step_sound_narrowE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.SumOracle.step_sound_narrowE
