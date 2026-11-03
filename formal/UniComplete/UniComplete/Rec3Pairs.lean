-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's paired batch is
-- `crates/leanvm_flock_gas/src/transcript.rs`'s `sumcheck_pairs_drawn` (`pair_round_poly`, `pair_point`), its honest
-- prover `crates/leanvm_univariate/src/prover/batch.rs`'s `prove_pairs` (`leanvm-rec` 4247e37); the soundness side's
-- language is `formal/UniSound/UniSound/Rec3/Pairs.lean`'s (`ProdSum`, `pairCoeffs`, `BatchState3`).
import UniSound.Rec3.Pairs

/-!
# π1-rec3's paired rounds are complete

The batch of π1-rec3 (`UniStatement.sumcheckPairsDrawn`) runs its variables two at a time: pair `j`'s message is the
eight coefficients `c_0, c_1, c_2, c_4, …, c_8` of its round polynomial `G` (`c_3` left out), the verifier rebuilds
`c_3 = claim + c_6` (`pairRoundPoly`, `UniSound.pairCoeffs`), draws `z`, and the next claim is `G(z)` at the point's
two new coordinates `pairPoint z`. With the variables odd, a last plain round (`roundCoeffs`: `c_0, c_2` sent, `c_1`
from the claim).

**Completeness, generic in the sum** (any `UniSound.ProdSum P`, any root `b` of `X² + X + 1`):

* **`pairCoeffs_honest`**: if the nine coefficients `cs` of a polynomial evaluate to `X ↦ P.T (r ++ pairPoint b X)`
  (the honest pair polynomial, `ProdSum.pairH`), then the verifier rebuilds exactly `cs` from the honest message
  `msg8 cs` at the true claim `P.T r` (`c_3 = P.T r + c_6`: `Σ_(x ∈ V_2) G(x) = c_3 + c_6`, `sum_V2_nine`, and
  `Σ_(x ∈ V_2) G(x) = P.T r`, the four corners, `ProdSum.T_eq_pair`); so the next claim is `P.T (r ++ pairPoint b z)`
  at every challenge `z` (`pair_round_complete`);
* **`plain_round_complete`**: the last plain round likewise (`roundCoeffs (P.T r) a₀ a₂ = [a₀, a₁, a₂]` when
  `[a₀, a₁, a₂]` evaluates to `X ↦ P.T (r ++ [X])`);
* **`pairRoundPoly_reads`**: the verifier's `pairRoundPoly 2 claim` on the eight scalars `msg8 cs` returns
  `pairCoeffs claim (msg8 cs)` (`UniSound.pairCoeffs_eq_rust`);
* **the whole batch** in the soundness side's language (`UniSound.BatchState3`): from the true target, honest records
  keep the state true at every step (`batchState3_honest_step`), so after all `np + 1` records the verifier's last
  claim is `Σ_k c_k Â_k(r) B̂_k(r)` at the batch's point (`batchState3_honest_full`): the terminal holds at the honest
  point, at every challenge.

Decision (recorded): the honesty of a record is stated by evaluation (`∀ x, polyEval cs x = P.T (… ++ pairPoint b x)`),
not by equality with `ProdSum.pairH`'s coefficients, so the prover's concrete arithmetic (`Rec3Batch.lean`) needs
only an evaluation identity.
-/

namespace UniComplete.Rec3

open UniStatement UniSound LeanVM.Parameters Finset

/-! ## The honest pair message -/

/-- **The honest pair message**: a pair polynomial's nine coefficients but `c_3` (`prove_pairs`: every `d ≠ 3` sent). -/
def msg8 (cs : List E) : List E :=
  [cs.getD 0 0, cs.getD 1 0, cs.getD 2 0, cs.getD 4 0, cs.getD 5 0, cs.getD 6 0, cs.getD 7 0, cs.getD 8 0]

theorem length_msg8 (cs : List E) : (msg8 cs).length = 8 := rfl

theorem two_eq_zero_E3 : (2 : E) = 0 := CharTwo.two_eq_zero

/-- A list of nine. -/
theorem nine_eq (cs : List E) (h : cs.length = 9) :
    cs = [cs.getD 0 0, cs.getD 1 0, cs.getD 2 0, cs.getD 3 0, cs.getD 4 0, cs.getD 5 0, cs.getD 6 0, cs.getD 7 0,
      cs.getD 8 0] := by
  rcases cs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, t⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp only [List.length_cons, List.length_nil] at h
  all_goals first | omega | rfl

/-- **The verifier's rebuild at `c_3 + c_6`** is the polynomial itself. -/
theorem pairCoeffs_msg8 (cs : List E) (hcs : cs.length = 9) (claim : E)
    (h : claim = cs.getD 3 0 + cs.getD 6 0) : pairCoeffs claim (msg8 cs) = cs := by
  conv_rhs => rw [nine_eq cs hcs]
  simp only [pairCoeffs, msg8, List.getD_cons_zero, List.getD_cons_succ, h]
  congr 4
  linear_combination cs.getD 6 0 * two_eq_zero_E3

/-- **A pair polynomial's sum over `V_2`** is `c_3 + c_6` (`UniSound.psum_V2`, through `pairSum`). -/
theorem sum_V2_nine {b : E} (hb : b * b + b = 1) (cs : List E) (hcs : cs.length = 9) :
    ((V2 b).map fun x => polyEval cs x).sum = cs.getD 3 0 + cs.getD 6 0 := by
  have h := pairSum hb (cs.getD 3 0 + cs.getD 6 0) (msg8 cs)
  rwa [pairCoeffs_msg8 cs hcs _ rfl] at h

/-- **The honest pair message is rebuilt exactly**: if `cs` (nine coefficients) evaluates to the honest pair
polynomial `X ↦ P.T (r ++ pairPoint b X)`, the verifier's `pairCoeffs` at the true claim `P.T r` is `cs`. -/
theorem pairCoeffs_honest (P : ProdSum) {b : E} (hb : b * b + b = 1) (r : List E) (hr : r.length + 2 ≤ P.vars)
    (cs : List E) (hcs : cs.length = 9) (heval : ∀ x, polyEval cs x = P.T (r ++ pairPoint b x)) :
    pairCoeffs (P.T r) (msg8 cs) = cs := by
  refine pairCoeffs_msg8 cs hcs _ ?_
  rw [← sum_V2_nine hb cs hcs, P.T_eq_pair b hb r hr]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [heval, P.eval_pairH]

/-- **A pair round is complete**: on the honest message the verifier rebuilds the honest polynomial, and its next
claim is the true partial sum at the point's two new coordinates, at every challenge. -/
theorem pair_round_complete (P : ProdSum) {b : E} (hb : b * b + b = 1) (r : List E) (hr : r.length + 2 ≤ P.vars)
    (cs : List E) (hcs : cs.length = 9) (heval : ∀ x, polyEval cs x = P.T (r ++ pairPoint b x)) :
    pairCoeffs (P.T r) (msg8 cs) = cs ∧
      ∀ z, polyEval (pairCoeffs (P.T r) (msg8 cs)) z = P.T (r ++ pairPoint b z) := by
  have h := pairCoeffs_honest P hb r hr cs hcs heval
  exact ⟨h, fun z => by rw [h, heval]⟩

/-- **The last plain round is complete**: if `[a₀, a₁, a₂]` evaluates to `X ↦ P.T (r ++ [X])`, the verifier's
`roundCoeffs` at the true claim (`c_1 = claim + c_2`) is it. -/
theorem plain_round_complete (P : ProdSum) (r : List E) (hr : r.length < P.vars) (a0 a1 a2 : E)
    (heval : ∀ x, polyEval [a0, a1, a2] x = P.T (r ++ [x])) :
    roundCoeffs (P.T r) a0 a2 = [a0, a1, a2] := by
  have h0 := heval 0
  have h1 := heval 1
  simp only [polyEval, List.foldr_cons, List.foldr_nil, zero_add, mul_zero, mul_one] at h0 h1
  have hT : P.T r = P.T (r ++ [0]) + P.T (r ++ [1]) := by rw [P.T_eq r hr, P.eval_H, P.eval_H]
  simp only [roundCoeffs, List.cons.injEq, and_true, true_and]
  rw [hT, ← h0, ← h1]
  linear_combination (a0 + a2) * two_eq_zero_E3

/-! ## The verifier's reading of a pair message -/

/-- **`pairRoundPoly 2 claim` reads the eight scalars of `msg8 cs` and returns `pairCoeffs claim (msg8 cs)`**: its
`c_3` fold (`(k + 4) % 3 = 0` at `k = 2`, `c_6`) is `pairCoeffs`' (`UniSound.pairCoeffs_eq_rust`). -/
theorem pairRoundPoly_fold (claim : E) (cs : List E) :
    (msg8 cs).take 3 ++ [(((msg8 cs).drop 3).zip (List.range ((msg8 cs).drop 3).length)).foldl
        (fun acc (x : E × ℕ) ↦ if (x.2 + 4) % 3 = 0 then acc + x.1 else acc) claim] ++ (msg8 cs).drop 3 =
      pairCoeffs claim (msg8 cs) := by
  have h := pairCoeffs_eq_rust claim ((msg8 cs).take 3) ((msg8 cs).drop 3) rfl rfl
  rwa [List.take_append_drop] at h

/-! ## The whole batch, in the soundness side's language -/

/-- **An honest record** of π1-rec3's batch after the records `rs` (the first `np` pair rounds, then plain ones), at
the challenge cut `nw`: a pair round's message is `msg8 cs` for nine coefficients `cs` evaluating to the honest pair
polynomial at the point so far; a plain round's is `[a₀, a₂]` of a quadratic evaluating to the honest round
polynomial. -/
def HonestRecord (b : E) (nw : E → E) (P : ProdSum) (np : ℕ) (rs : List (List E × List E)) (m : List E) : Prop :=
  if rs.length < np then
    ∃ cs : List E, cs.length = 9 ∧ m = msg8 cs ∧
      ∀ x, polyEval cs x = P.T (pointAfter3 b nw np rs ++ pairPoint b x)
  else
    ∃ a0 a1 a2 : E, m = [a0, a2] ∧ ∀ x, polyEval [a0, a1, a2] x = P.T (pointAfter3 b nw np rs ++ [x])

/-- **An honest record keeps the batch's state true** (at `P.vars = 2 np + 1`, within the `np + 1` records), at every
challenge. -/
theorem batchState3_honest_step (P : ProdSum) (np : ℕ) {b : E} (hb : b * b + b = 1) (nw : E → E) (target : E)
    (rs : List (List E × List E)) (m c : List E) (hv : P.vars = 2 * np + 1) (hr : rs.length ≤ np)
    (hs : BatchState3 b nw P target rs) (hm : HonestRecord b nw P np rs m) :
    BatchState3 b nw P target (rs ++ [(m, c)]) := by
  have hnp : P.vars / 2 = np := by omega
  unfold BatchState3 at hs ⊢
  rw [hnp] at hs ⊢
  unfold HonestRecord at hm
  split_ifs at hm with hlt
  · -- A pair round.
    obtain ⟨cs, hcs, rfl, heval⟩ := hm
    have hx : (rs ++ [(msg8 cs, c)]).length ≤ np := by
      simp only [List.length_append, List.length_singleton]; omega
    have hc : claimAfter3 nw np target (rs ++ [(msg8 cs, c)]) =
        polyEval (pairCoeffs (claimAfter3 nw np target rs) (msg8 cs)) (nw (c.headD 0)) := by
      unfold claimAfter3
      rw [List.take_of_length_le hx, List.drop_of_length_le hx, List.take_of_length_le hr,
        List.drop_of_length_le hr, claimAfterPairs_append]
      rfl
    have hp : pointAfter3 b nw np (rs ++ [(msg8 cs, c)]) =
        pointAfter3 b nw np rs ++ pairPoint b (nw (c.headD 0)) := by
      unfold pointAfter3
      rw [List.take_of_length_le hx, List.drop_of_length_le hx, List.take_of_length_le hr,
        List.drop_of_length_le hr, pointAfterPairs_append]
      simp [pointAfterN]
    have hlen : (pointAfter3 b nw np rs).length + 2 ≤ P.vars := by
      rw [length_pointAfter3]; omega
    rw [hc, hp, hs, (pair_round_complete P hb _ hlen cs hcs heval).2]
  · -- The last plain round.
    obtain ⟨a0, a1, a2, rfl, heval⟩ := hm
    have hge : np ≤ rs.length := by omega
    have hc : claimAfter3 nw np target (rs ++ [([a0, a2], c)]) =
        polyEval (roundCoeffs (claimAfter3 nw np target rs) a0 a2) (nw (c.headD 0)) := by
      unfold claimAfter3
      rw [List.take_append_of_le_length hge, List.drop_append_of_le_length hge, claimAfterN_append]
      rfl
    have hp : pointAfter3 b nw np (rs ++ [([a0, a2], c)]) = pointAfter3 b nw np rs ++ [nw (c.headD 0)] := by
      unfold pointAfter3
      rw [List.take_append_of_le_length hge, List.drop_append_of_le_length hge, pointAfterN_append,
        List.append_assoc]
    have hlen : (pointAfter3 b nw np rs).length < P.vars := by
      rw [length_pointAfter3]; omega
    rw [hc, hp, hs, plain_round_complete P _ hlen a0 a1 a2 heval, heval]

/-- **Honest records, every one**: the `j`-th record honest after the first `j`. -/
def HonestRecords (b : E) (nw : E → E) (P : ProdSum) (np : ℕ) (rs : List (List E × List E)) : Prop :=
  ∀ j < rs.length, HonestRecord b nw P np (rs.take j) (rs.getD j ([], [])).1

theorem honestRecords_append (b : E) (nw : E → E) (P : ProdSum) (np : ℕ) (rs : List (List E × List E))
    (m c : List E) (h : HonestRecords b nw P np (rs ++ [(m, c)])) :
    HonestRecords b nw P np rs ∧ HonestRecord b nw P np rs m := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have h1 := h j (by simp; omega)
    rwa [List.take_append_of_le_length (by omega), List.getD_append _ _ _ _ hj] at h1
  · have h1 := h rs.length (by simp)
    rwa [List.take_left' rfl, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self] at h1

/-- **From the true target, honest records keep the state true** throughout (at most `np + 1` of them). -/
theorem batchState3_honest (P : ProdSum) (np : ℕ) {b : E} (hb : b * b + b = 1) (nw : E → E) (target : E)
    (hv : P.vars = 2 * np + 1) (ht : target = P.T []) :
    ∀ rs : List (List E × List E), rs.length ≤ np + 1 → HonestRecords b nw P np rs →
      BatchState3 b nw P target rs := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => intro _ _; exact (batchState3_nil b nw P target).mpr ht
  | append_singleton rs x ih =>
    intro hl hh
    obtain ⟨m, c⟩ := x
    obtain ⟨h1, h2⟩ := honestRecords_append b nw P np rs m c hh
    simp only [List.length_append, List.length_singleton] at hl
    exact batchState3_honest_step P np hb nw target rs m c hv (by omega) (ih (by omega) h1) h2

/-- **The terminal holds at the honest point**: after the `np` pair rounds and the last plain round, all honest, the
verifier's last claim is `Σ_k c_k Â_k(r) B̂_k(r)` at the batch's point `r` (`P.vars` coordinates). -/
theorem batchState3_honest_full (P : ProdSum) (np : ℕ) {b : E} (hb : b * b + b = 1) (nw : E → E) (target : E)
    (hv : P.vars = 2 * np + 1) (ht : target = P.T []) (rs : List (List E × List E)) (hr : rs.length = np + 1)
    (hh : HonestRecords b nw P np rs) :
    (pointAfter3 b nw np rs).length = P.vars ∧ claimAfter3 nw np target rs =
      ∑ k ∈ range P.n, P.coef k * (foldAll (P.A k) (pointAfter3 b nw np rs) 0 *
        foldAll (P.B k) (pointAfter3 b nw np rs) 0) := by
  obtain ⟨h1, h2⟩ := batchState3_full_np P np b nw target rs hv hr
  exact ⟨h1, h2.mp (batchState3_honest P np hb nw target hv ht rs (by omega) hh)⟩

/-- **At the verifier's constants** (`cantorBeta1`, the challenges as drawn): `batchState3_honest_full`. -/
theorem batchState3_honest_full_rec3 (P : ProdSum) (np : ℕ) (nw : E → E) (target : E) (hv : P.vars = 2 * np + 1)
    (ht : target = P.T []) (rs : List (List E × List E)) (hr : rs.length = np + 1)
    (hh : HonestRecords cantorBeta1 nw P np rs) :
    (pointAfter3 cantorBeta1 nw np rs).length = P.vars ∧ claimAfter3 nw np target rs =
      ∑ k ∈ range P.n, P.coef k * (foldAll (P.A k) (pointAfter3 cantorBeta1 nw np rs) 0 *
        foldAll (P.B k) (pointAfter3 cantorBeta1 nw np rs) 0) :=
  batchState3_honest_full P np cantorBeta1_spec nw target hv ht rs hr hh

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.pair_round_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.pair_round_complete

/-- info: 'UniComplete.Rec3.plain_round_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.plain_round_complete

/-- info: 'UniComplete.Rec3.batchState3_honest_full_rec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.batchState3_honest_full_rec3
