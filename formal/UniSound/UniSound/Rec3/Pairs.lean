-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The paired batch is π1-rec3's
-- (`crates/leanvm_flock_gas/src/transcript.rs`: `cantor_beta1`, `pair_point`, `pair_round_poly`,
-- `sumcheck_pairs_drawn`; `crates/leanvm_rec/SPEC-POINTS.md` §2.4, §3, §5), transcribed as `UniStatement.cantorBeta1`,
-- `UniStatement.pairPoint`, `UniStatement.pairRoundPoly`, `UniStatement.sumcheckPairsDrawn`
-- (`formal/UniStatement/UniStatement/Rec.lean`).
import UniSound.Rec3.Narrow
import LeanVM.Parameters.Generator

/-!
# The batching sumcheck two variables a round (π1-rec3)

π1-rec3's batch (`sumcheckPairsDrawn`) runs the `V = 2 np + 1` variables of `Σ_k c_k A_k B_k` (`ProdSum`, each
summand of degree `2` in each variable) two at a time, low first, then the last one as an ordinary round:

* **`GF(4)`** (`b * b + b = 1`, so `V_2 = [0, 1, b, b + 1]` is `GF(4)`, `V2`): `b^3 = 1` (`cube_of_hb`); the pair's
  coordinates `pairPoint b z = [z + b (z² + z), z² + z]` (`UniStatement.pairPoint z = pairPoint cantorBeta1 z`,
  `pairPoint_cantorBeta1`) map the four points to the corners `(0,0), (1,0), (0,1), (1,1)` (`pairPoint_zero`,
  `pairPoint_one`, `pairPoint_b`, `pairPoint_b1`); the power sums `Σ_(x ∈ V_2) x^e`, `e ≤ 8`, are `1` at `e = 3, 6`
  and `0` otherwise (`psum_V2`).
* **A pair's round polynomial** (`pairCoeffs claim m`, the Rust's `pair_round_poly` at `degree = 2`:
  `c_0, c_1, c_2` read, `c_3 = claim + c_6`, `c_4 … c_8` read; `pairCoeffs_eq_rust`): its sum over `V_2` is the
  claim by construction (`pairSum`); its polynomial `pairPolyP` (`polyEval_pairCoeffs`) has degree at most `8`.
* **`PairOracle b`**: `SumOracle` two variables a round: the honest polynomial `H r` of `X ↦ T(r ++ pairPoint b X)`,
  of degree at most `8`, `T r = Σ_(x ∈ V_2) H r (x)`. **`PairOracle.round_sound`**: with a narrow challenge (any
  cut `nw` of fibers at most `2^32`), a false claim turns true with probability at most `8 · 2^32 / |E|`
  (Schwartz–Zippel on `G − H r ≠ 0`); **`PairOracle.step_sound`** on the pair rounds' state (`PairState`,
  `claimAfterPairs`, `pointAfterPairs`).
* **`ProdSum.pairOracle`**: `P.T` itself (its tables folded low coordinate first) with `H r` the product of each
  table's quadruples folded at `(y_0(X), y_1(X))` (degree `4` each, `8` the products); `T_eq` from `ProdSum.T_eq`
  twice and the corners.
* **The whole batch** (`BatchState3 b nw P target rs`): the first `P.vars / 2` records are pair rounds, the rest
  plain narrow rounds (`claimAfterN`, `roundCoeffs`) continuing from the pairs' claim and point
  (`claimAfter3`, `pointAfter3`). **`batchState3_step`**: at `P.vars = 2 np + 1`, a record `rs.length ≤ np`
  turns the state true with probability at most `8 · 2^32 / |E|` for a pair (`rs.length < np`) and
  `2 · 2^32 / |E|` for the last plain round; `batchState3_nil` (the start: the target is the sum),
  `batchState3_full` (the end: the claim is `Σ_k c_k Â_k(r) B̂_k(r)` at the point, `ProdSum.T_full`).
* **The verifier's constants**: `cantorBeta1_spec` (`β_1² + β_1 = 1` for `UniStatement.cantorBeta1`, algebraically:
  `g = x^((2^64 − 1)/3)` has `g³ = 1`, `g ≠ 1` by leanerVM's `g_pow_card_sub_one`, `g_pow_div_three_ne_one`, and
  either root of `X² + X + 1` works, `order3_spec`), `betaWord_spec` (the word `0x19c9369f278adc02`,
  `UniStatement.beta`'s second, one product in `K` by the kernel); at them `batchState3_step_rec3`.

Decisions (recorded):
* `b` is a parameter with the hypothesis `hb : b * b + b = 1` where it is used (the power sums, the corners), so
  the pairs' soundness is proved for any root and instantiated at `cantorBeta1` (`cantorBeta1_spec`).
* The claims (`claimAfterPairs nw claim rs`) do not take `b`: a pair's round polynomial does not depend on it, only
  the point does (`pointAfterPairs b nw rs`).
* `V_2` is the list `V2 b = [0, 1, b, b + 1]` (the Cantor order `ω_0 … ω_3`), its sums `List.sum` of maps.
* `ProdSum.pairOracle`'s `T_eq` uses `ProdSum.T_eq` twice (each its `sum_range_two_mul`) rather than the sums
  directly; the honest polynomial is built from the quadruples (`ProdSum.quad`).
* The batch's records are split by `P.vars / 2`: with `P.vars` odd, the pair rounds and then one plain round (the
  Rust's `vars / 2` pairs and `vars % 2` plain rounds). `batchState3_step` takes `np` with `P.vars = 2 np + 1`, the
  form `UniSound.PairBatch`'s `step` asks for.
-/

namespace UniSound

open LeanVM.Parameters OracleComp Finset UniStatement Polynomial
open scoped ENNReal

/-! ## `GF(4)` -/

section Gf4

variable (b : E)

/-- **`V_2 = {0, 1, β_1, 1 + β_1}`**, in the Cantor order (`ω_i = i_0 + i_1 β_1`). -/
def V2 : List E := [0, 1, b, b + 1]

/-- **`pair_point(z)`** at `β_1 = b`: a pair's coordinates `(y_0(z), y_1(z)) = (z + b (z² + z), z² + z)`, low first. -/
def pairPoint (z : E) : List E := [z + b * (z * z + z), z * z + z]

/-- **The verifier's `pairPoint` is `pairPoint cantorBeta1`.** -/
theorem pairPoint_cantorBeta1 (z : E) : UniStatement.pairPoint z = pairPoint cantorBeta1 z := rfl

theorem length_pairPoint (z : E) : (pairPoint b z).length = 2 := rfl

variable {b}

theorem sq_of_hb (hb : b * b + b = 1) : b * b = b + 1 := by
  linear_combination hb - b * (CharTwo.two_eq_zero : (2 : E) = 0)

/-- **`b^3 = 1`.** -/
theorem cube_of_hb (hb : b * b + b = 1) : b ^ 3 = 1 := by
  linear_combination (b - 1) * hb + (b - 1) * (CharTwo.two_eq_zero : (2 : E) = 0)

/-- `b + 1` is the other root. -/
theorem hb_succ (hb : b * b + b = 1) : (b + 1) * (b + 1) + (b + 1) = 1 := by
  linear_combination hb + (b + 1) * (CharTwo.two_eq_zero : (2 : E) = 0)

/-! ### The corners -/

theorem pairPoint_zero : pairPoint b 0 = [0, 0] := by
  simp [pairPoint]

theorem pairPoint_one : pairPoint b 1 = [1, 0] := by
  rw [pairPoint, show (1 : E) * 1 + 1 = 0 by linear_combination (CharTwo.two_eq_zero : (2 : E) = 0),
    mul_zero, add_zero]

theorem pairPoint_b (hb : b * b + b = 1) : pairPoint b b = [0, 1] := by
  rw [pairPoint, hb, mul_one, CharTwo.add_self_eq_zero]

theorem pairPoint_b1 (hb : b * b + b = 1) : pairPoint b (b + 1) = [1, 1] := by
  rw [pairPoint, hb_succ hb, mul_one,
    show b + 1 + b = 1 by linear_combination b * (CharTwo.two_eq_zero : (2 : E) = 0)]

/-! ### The power sums over `V_2` -/

section Psum

variable (hb : b * b + b = 1)
include hb

omit hb in
theorem psum0 : (0 : E) ^ 0 + 1 ^ 0 + b ^ 0 + (b + 1) ^ 0 = 0 := by
  linear_combination 2 * (CharTwo.two_eq_zero : (2 : E) = 0)

omit hb in
theorem psum1 : (0 : E) ^ 1 + 1 ^ 1 + b ^ 1 + (b + 1) ^ 1 = 0 := by
  linear_combination (1 + b) * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem psum2 : (0 : E) ^ 2 + 1 ^ 2 + b ^ 2 + (b + 1) ^ 2 = 0 := by
  linear_combination 2 * hb + 2 * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem psum3 : (0 : E) ^ 3 + 1 ^ 3 + b ^ 3 + (b + 1) ^ 3 = 1 := by
  linear_combination (1 + 2 * b) * hb + (1 + 2 * b) * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem psum4 : (0 : E) ^ 4 + 1 ^ 4 + b ^ 4 + (b + 1) ^ 4 = 0 := by
  linear_combination (6 + 2 * b + 2 * b ^ 2) * hb + 4 * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem psum5 : (0 : E) ^ 5 + 1 ^ 5 + b ^ 5 + (b + 1) ^ 5 = 0 := by
  linear_combination (4 + 9 * b + 3 * b ^ 2 + 2 * b ^ 3) * hb +
    (3 + 5 * b) * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem psum6 : (0 : E) ^ 6 + 1 ^ 6 + b ^ 6 + (b + 1) ^ 6 = 1 := by
  linear_combination (17 + 11 * b + 13 * b ^ 2 + 4 * b ^ 3 + 2 * b ^ 4) * hb +
    9 * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem psum7 : (0 : E) ^ 7 + 1 ^ 7 + b ^ 7 + (b + 1) ^ 7 = 0 := by
  linear_combination (12 + 31 * b + 22 * b ^ 2 + 18 * b ^ 3 + 5 * b ^ 4 + 2 * b ^ 5) * hb +
    (7 + 13 * b) * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem psum8 : (0 : E) ^ 8 + 1 ^ 8 + b ^ 8 + (b + 1) ^ 8 = 0 := by
  linear_combination (46 + 38 * b + 56 * b ^ 2 + 38 * b ^ 3 + 24 * b ^ 4 + 6 * b ^ 5 + 2 * b ^ 6) * hb +
    24 * (CharTwo.two_eq_zero : (2 : E) = 0)

/-- **The power sums over `V_2 = GF(4)`**: `Σ_(x ∈ V_2) x^e` is `1` at `e = 3, 6` and `0` at the other `e ≤ 8`. -/
theorem psum_V2 (e : ℕ) (he : e ≤ 8) :
    ((V2 b).map fun x => x ^ e).sum = if e = 3 ∨ e = 6 then 1 else 0 := by
  have h : ((V2 b).map fun x => x ^ e).sum = (0 : E) ^ e + 1 ^ e + b ^ e + (b + 1) ^ e := by
    simp only [V2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  rw [h]
  interval_cases e
  · exact psum0.trans rfl
  · exact psum1.trans rfl
  · exact (psum2 hb).trans rfl
  · exact (psum3 hb).trans rfl
  · exact (psum4 hb).trans rfl
  · exact (psum5 hb).trans rfl
  · exact (psum6 hb).trans rfl
  · exact (psum7 hb).trans rfl
  · exact (psum8 hb).trans rfl

end Psum

end Gf4

/-! ## A pair's round polynomial -/

/-- **`pair_round_poly` at `degree = 2`**: the stream's `8` scalars `c_0, c_1, c_2, c_4, c_5, c_6, c_7, c_8` and
`c_3 = claim + c_6`. -/
def pairCoeffs (claim : E) (m : List E) : List E :=
  [m.getD 0 0, m.getD 1 0, m.getD 2 0, claim + m.getD 5 0, m.getD 3 0, m.getD 4 0, m.getD 5 0, m.getD 6 0,
    m.getD 7 0]

theorem length_pairCoeffs (claim : E) (m : List E) : (pairCoeffs claim m).length = 9 := rfl

/-- **The Rust's `c_3`** (`pairRoundPoly`'s fold at `degree = 2`: the high scalars `c_4 … c_8` at `k = 0 … 4`, the
one with `3 | k + 4` is `c_6`) and its layout `low ++ [c3] ++ high` are `pairCoeffs`. -/
theorem pairCoeffs_eq_rust (claim : E) (low high : List E) (hl : low.length = 3) (hh : high.length = 5) :
    low ++ [(high.zip (List.range high.length)).foldl
        (fun acc (x : E × ℕ) ↦ if (x.2 + 4) % 3 = 0 then acc + x.1 else acc) claim] ++ high =
      pairCoeffs claim (low ++ high) := by
  obtain ⟨a0, a1, a2, rfl⟩ := List.length_eq_three.mp hl
  rcases high with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, t⟩⟩⟩⟩⟩⟩
  all_goals simp only [List.length_cons, List.length_nil] at hh
  all_goals try omega
  first
    | rfl
    | simp [pairCoeffs, List.range_succ, List.zip, List.foldl]

/-- Its polynomial, `Σ_e c_e X^e`. -/
noncomputable def pairPolyP (claim : E) (m : List E) : Polynomial E :=
  C (m.getD 0 0) + C (m.getD 1 0) * X ^ 1 + C (m.getD 2 0) * X ^ 2 + C (claim + m.getD 5 0) * X ^ 3 +
    C (m.getD 3 0) * X ^ 4 + C (m.getD 4 0) * X ^ 5 + C (m.getD 5 0) * X ^ 6 + C (m.getD 6 0) * X ^ 7 +
    C (m.getD 7 0) * X ^ 8

theorem polyEval_pairCoeffs (claim : E) (m : List E) (x : E) :
    polyEval (pairCoeffs claim m) x = (pairPolyP claim m).eval x := by
  simp only [pairCoeffs, polyEval, List.foldr, pairPolyP, Polynomial.eval_add, eval_C, Polynomial.eval_mul,
    eval_X, eval_pow]
  ring

theorem natDegree_pairPolyP_le (claim : E) (m : List E) : (pairPolyP claim m).natDegree ≤ 8 := by
  have hC : ∀ a : E, (C a).natDegree ≤ 8 := fun a => (natDegree_C a).le.trans (Nat.zero_le _)
  have hX : ∀ (a : E) (k : ℕ), k ≤ 8 → (C a * X ^ k).natDegree ≤ 8 := fun a k hk =>
    (natDegree_C_mul_X_pow_le a k).trans hk
  unfold pairPolyP
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (hC _) (hX _ 1 (by norm_num)))
    (hX _ 2 (by norm_num))) (hX _ 3 (by norm_num))) (hX _ 4 (by norm_num))) (hX _ 5 (by norm_num)))
    (hX _ 6 (by norm_num))) (hX _ 7 (by norm_num))) (hX _ 8 le_rfl)

/-- **A pair's round polynomial sums to the claim over `V_2`**, by construction (`c_3 = claim + c_6`). -/
theorem pairSum {b : E} (hb : b * b + b = 1) (claim : E) (m : List E) :
    ((V2 b).map fun x => polyEval (pairCoeffs claim m) x).sum = claim := by
  have p0 := psum0 (b := b)
  have p1 := psum1 (b := b)
  have p2 := psum2 hb
  have p3 := psum3 hb
  have p4 := psum4 hb
  have p5 := psum5 hb
  have p6 := psum6 hb
  have p7 := psum7 hb
  have p8 := psum8 hb
  simp only [V2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pairCoeffs, polyEval, List.foldr]
  linear_combination m.getD 0 0 * p0 + m.getD 1 0 * p1 + m.getD 2 0 * p2 + (claim + m.getD 5 0) * p3 +
    m.getD 3 0 * p4 + m.getD 4 0 * p5 + m.getD 5 0 * p6 + m.getD 6 0 * p7 + m.getD 7 0 * p8 +
    m.getD 5 0 * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem pairSumP {b : E} (hb : b * b + b = 1) (claim : E) (m : List E) :
    ((V2 b).map fun x => (pairPolyP claim m).eval x).sum = claim := by
  simp only [← polyEval_pairCoeffs]
  exact pairSum hb claim m

/-! ## The pair rounds' oracle -/

/-- **A pair oracle** over `V` variables: the true partial sum at each prefix of coordinates, and the honest pair
polynomial there, `X ↦ T(r ++ pairPoint b X)`, of degree at most `8`, summing to `T r` over `V_2`. -/
structure PairOracle (b : E) where
  vars : ℕ
  T : List E → E
  H : List E → Polynomial E
  eval_H : ∀ r x, (H r).eval x = T (r ++ pairPoint b x)
  T_eq : ∀ r, r.length + 2 ≤ vars → T r = ((V2 b).map fun x => (H r).eval x).sum
  deg_H : ∀ r, (H r).natDegree ≤ 8

/-- **A pair round with a narrow challenge is sound**: from a false claim, the round's narrow challenge makes the
next claim true with probability at most `8 · 2^32 / |E|`, whatever the message. -/
theorem PairOracle.round_sound {b : E} (O : PairOracle b) (hb : b * b + b = 1) (nw : E → E)
    (hnw : ∀ s, (univ.filter fun x ↦ nw x = s).card ≤ 2 ^ 32) (r : List E) (hr : r.length + 2 ≤ O.vars)
    (claim : E) (m : List E) :
    Pr{let c ← Compose.draws E 1}[claim ≠ O.T r ∧
        polyEval (pairCoeffs claim m) (nw (c.headD 0)) = O.T (r ++ pairPoint b (nw (c.headD 0)))] ≤
      ((8 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  set D : Polynomial E := pairPolyP claim m - O.H r with hD
  have himp : ∀ c : List E, (claim ≠ O.T r ∧
      polyEval (pairCoeffs claim m) (nw (c.headD 0)) = O.T (r ++ pairPoint b (nw (c.headD 0)))) →
        ∃ p ∈ [D], p ≠ 0 ∧ p.eval (nw (c.headD 0)) = 0 := by
    intro c ⟨hne, heq⟩
    refine ⟨D, List.mem_singleton_self _, fun h0 => hne ?_, ?_⟩
    · have h1 : pairPolyP claim m = O.H r := sub_eq_zero.mp h0
      rw [O.T_eq r hr, ← h1]
      exact (pairSumP hb claim m).symm
    · rw [hD, Polynomial.eval_sub, ← polyEval_pairCoeffs, O.eval_H, heq, sub_self]
  refine (prEvent_mono _ _ _ himp).trans ((prEvent_narrow_root_le nw hnw [D]).trans ?_)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  rw [mul_comm 8]
  exact Nat.mul_le_mul_left _
    ((natDegree_sub_le _ _).trans (max_le (natDegree_pairPolyP_le _ _) (O.deg_H r)))

/-! ## Products of tables, two coordinates at a time -/

namespace ProdSum

variable (P : ProdSum)

/-- `y_0(X) = X + b (X² + X)`. -/
noncomputable def pairY0 (b : E) : Polynomial E := X + C b * (X * X + X)

/-- `y_1(X) = X² + X`. -/
noncomputable def pairY1 : Polynomial E := X * X + X

/-- A table's pair `j` folded at the polynomial `y`: `g(2j) + y (g(2j) + g(2j+1))`. -/
noncomputable def lin2 (g : ℕ → E) (j : ℕ) (y : Polynomial E) : Polynomial E :=
  C (g (2 * j)) + y * C (g (2 * j) + g (2 * j + 1))

/-- A table's quadruple `i` folded at `(y_0(X), y_1(X))`, low coordinate first. -/
noncomputable def quad (b : E) (g : ℕ → E) (i : ℕ) : Polynomial E :=
  lin2 g (2 * i) (pairY0 b) + pairY1 * (lin2 g (2 * i) (pairY0 b) + lin2 g (2 * i + 1) (pairY0 b))

theorem eval_quad (b : E) (g : ℕ → E) (i : ℕ) (x : E) :
    (quad b g i).eval x = foldT (foldT g (x + b * (x * x + x))) (x * x + x) i := by
  simp only [quad, lin2, pairY0, pairY1, foldT, Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_X]

theorem natDegree_pairY0_le (b : E) : (pairY0 b).natDegree ≤ 2 := by
  unfold pairY0
  refine natDegree_add_le_of_degree_le (natDegree_X_le.trans (by norm_num))
    ((natDegree_C_mul_le _ _).trans ?_)
  exact natDegree_add_le_of_degree_le ((natDegree_mul_le).trans (add_le_add natDegree_X_le natDegree_X_le))
    (natDegree_X_le.trans (by norm_num))

theorem natDegree_pairY1_le : (pairY1 : Polynomial E).natDegree ≤ 2 := by
  unfold pairY1
  exact natDegree_add_le_of_degree_le ((natDegree_mul_le).trans (add_le_add natDegree_X_le natDegree_X_le))
    (natDegree_X_le.trans (by norm_num))

theorem natDegree_lin2_le (g : ℕ → E) (j : ℕ) (y : Polynomial E) (hy : y.natDegree ≤ 2) :
    (lin2 g j y).natDegree ≤ 2 := by
  unfold lin2
  refine natDegree_add_le_of_degree_le ((natDegree_C _).le.trans (Nat.zero_le _)) ?_
  refine (natDegree_mul_le).trans ?_
  rw [natDegree_C, add_zero]
  exact hy

theorem natDegree_quad_le (b : E) (g : ℕ → E) (i : ℕ) : (quad b g i).natDegree ≤ 4 := by
  unfold quad
  have h0 := natDegree_lin2_le g (2 * i) (pairY0 b) (natDegree_pairY0_le b)
  have h1 := natDegree_lin2_le g (2 * i + 1) (pairY0 b) (natDegree_pairY0_le b)
  refine natDegree_add_le_of_degree_le (h0.trans (by norm_num)) ((natDegree_mul_le).trans ?_)
  exact (add_le_add natDegree_pairY1_le (natDegree_add_le_of_degree_le h0 h1)).trans (by norm_num)

/-- **The honest pair polynomial** after the prefix `r`: `X ↦ T(r ++ pairPoint b X)`, each table's quadruples
folded at `(y_0(X), y_1(X))`. -/
noncomputable def pairH (b : E) (r : List E) : Polynomial E :=
  ∑ k ∈ range P.n, C (P.coef k) * ∑ i ∈ range (2 ^ (P.vars - r.length - 2)),
    quad b (foldAll (P.A k) r) i * quad b (foldAll (P.B k) r) i

theorem length_append_pairPoint (b : E) (r : List E) (x : E) :
    (r ++ pairPoint b x).length = r.length + 2 := by
  simp [pairPoint]

theorem foldAll_append_pairPoint (f : ℕ → E) (b : E) (r : List E) (x : E) :
    foldAll f (r ++ pairPoint b x) = foldT (foldT (foldAll f r) (x + b * (x * x + x))) (x * x + x) := by
  simp [foldAll, pairPoint, List.foldl_append]

theorem eval_pairH (b : E) (r : List E) (x : E) : (P.pairH b r).eval x = P.T (r ++ pairPoint b x) := by
  unfold pairH T
  simp only [eval_finsetSum, Polynomial.eval_mul, eval_C, eval_quad, length_append_pairPoint,
    foldAll_append_pairPoint]
  rw [show P.vars - (r.length + 2) = P.vars - r.length - 2 by omega]

/-- The partial sum is the sum of its two halves on the next coordinate. -/
theorem T_split (r : List E) (hr : r.length < P.vars) : P.T r = P.T (r ++ [0]) + P.T (r ++ [1]) := by
  rw [P.T_eq r hr, P.eval_H, P.eval_H]

/-- **The partial sum is the pair polynomial's sum over `V_2`**: the four corners. -/
theorem T_eq_pair (b : E) (hb : b * b + b = 1) (r : List E) (hr : r.length + 2 ≤ P.vars) :
    P.T r = ((V2 b).map fun x => (P.pairH b r).eval x).sum := by
  simp only [V2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, eval_pairH, pairPoint_zero,
    pairPoint_one, pairPoint_b hb, pairPoint_b1 hb]
  rw [P.T_split r (by omega), P.T_split (r ++ [0]) (by simp; omega), P.T_split (r ++ [1]) (by simp; omega)]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  ring

theorem deg_pairH (b : E) (r : List E) : (P.pairH b r).natDegree ≤ 8 := by
  unfold pairH
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
  refine (natDegree_mul_le).trans ?_
  exact (add_le_add (natDegree_quad_le _ _ _) (natDegree_quad_le _ _ _)).trans (by norm_num)

/-- **The pair oracle of a sum of products of tables.** -/
noncomputable def pairOracle (b : E) (hb : b * b + b = 1) : PairOracle b where
  vars := P.vars
  T := P.T
  H := P.pairH b
  eval_H := P.eval_pairH b
  T_eq := P.T_eq_pair b hb
  deg_H := P.deg_pairH b

end ProdSum

/-! ## The pair rounds' claims and point -/

/-- **The claims along the pair rounds**: from `claim`, each round's `8` scalars `m` and its challenge `c` give the
next claim `G(nw c)` (`sumcheckPairsDrawn`'s loop). -/
def claimAfterPairs (nw : E → E) : E → List (List E × List E) → E
  | claim, [] => claim
  | claim, x :: rest => claimAfterPairs nw (polyEval (pairCoeffs claim x.1) (nw (x.2.headD 0))) rest

/-- **The pair rounds' point**: each challenge's two coordinates `pairPoint b (nw c)`, low first. -/
def pointAfterPairs (b : E) (nw : E → E) : List (List E × List E) → List E
  | [] => []
  | x :: rest => pairPoint b (nw (x.2.headD 0)) ++ pointAfterPairs b nw rest

theorem claimAfterPairs_append (nw : E → E) (claim : E) (rs : List (List E × List E)) (m c : List E) :
    claimAfterPairs nw claim (rs ++ [(m, c)]) =
      polyEval (pairCoeffs (claimAfterPairs nw claim rs) m) (nw (c.headD 0)) := by
  induction rs generalizing claim with
  | nil => rfl
  | cons x rs ih => exact ih _

theorem pointAfterPairs_append (b : E) (nw : E → E) (rs : List (List E × List E)) (m c : List E) :
    pointAfterPairs b nw (rs ++ [(m, c)]) = pointAfterPairs b nw rs ++ pairPoint b (nw (c.headD 0)) := by
  induction rs with
  | nil => simp [pointAfterPairs]
  | cons x rs ih => simp [pointAfterPairs, ih]

theorem length_pointAfterPairs (b : E) (nw : E → E) :
    ∀ rs : List (List E × List E), (pointAfterPairs b nw rs).length = 2 * rs.length
  | [] => rfl
  | _ :: rest => by
    simp only [pointAfterPairs, List.length_append, length_pairPoint, length_pointAfterPairs b nw rest,
      List.length_cons]
    ring

/-- The verifier's pair point: `pointAfterPairs` at `cantorBeta1` is the concatenation of
`UniStatement.pairPoint`s. -/
theorem pointAfterPairs_cantorBeta1 (nw : E → E) (rs : List (List E × List E)) :
    pointAfterPairs cantorBeta1 nw rs = rs.flatMap fun x => UniStatement.pairPoint (nw (x.2.headD 0)) := by
  induction rs with
  | nil => rfl
  | cons x rs ih => simp [pointAfterPairs, ih, pairPoint_cantorBeta1]

/-- **The pair rounds' state** after the records `rs` from `target`: the claim is the partial sum at the point so
far. -/
def PairState {b : E} (O : PairOracle b) (nw : E → E) (target : E) (rs : List (List E × List E)) : Prop :=
  claimAfterPairs nw target rs = O.T (pointAfterPairs b nw rs)

/-- **Each pair round**, as the chain's: its state from false to true with probability at most `8 · 2^32 / |E|`. -/
theorem PairOracle.step_sound {b : E} (O : PairOracle b) (hb : b * b + b = 1) (nw : E → E)
    (hnw : ∀ s, (univ.filter fun x ↦ nw x = s).card ≤ 2 ^ 32) (target : E) (rs : List (List E × List E))
    (hr : 2 * rs.length + 2 ≤ O.vars) (m : List E) :
    Pr{let c ← Compose.draws E 1}[¬ PairState O nw target rs ∧ PairState O nw target (rs ++ [(m, c)])] ≤
      ((8 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have himp : ∀ c : List E, (¬ PairState O nw target rs ∧ PairState O nw target (rs ++ [(m, c)])) →
      (claimAfterPairs nw target rs ≠ O.T (pointAfterPairs b nw rs) ∧
        polyEval (pairCoeffs (claimAfterPairs nw target rs) m) (nw (c.headD 0)) =
          O.T (pointAfterPairs b nw rs ++ pairPoint b (nw (c.headD 0)))) := by
    intro c ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    unfold PairState at h2
    rwa [claimAfterPairs_append, pointAfterPairs_append] at h2
  exact (prEvent_mono _ _ _ himp).trans
    (O.round_sound hb nw hnw _ (by rw [length_pointAfterPairs]; exact hr) _ _)

/-! ## The whole batch: the pair rounds, then the plain ones -/

/-- **The batch's claim** after the records `rs`: the first `np` pair rounds, then plain narrow rounds from the
pairs' claim. -/
def claimAfter3 (nw : E → E) (np : ℕ) (target : E) (rs : List (List E × List E)) : E :=
  claimAfterN nw (claimAfterPairs nw target (rs.take np)) (rs.drop np)

/-- **The batch's point** after the records `rs`: the pairs' coordinates, then the plain rounds' challenges. -/
def pointAfter3 (b : E) (nw : E → E) (np : ℕ) (rs : List (List E × List E)) : List E :=
  pointAfterPairs b nw (rs.take np) ++ pointAfterN nw (rs.drop np)

theorem length_pointAfter3 (b : E) (nw : E → E) (np : ℕ) (rs : List (List E × List E)) :
    (pointAfter3 b nw np rs).length = 2 * min np rs.length + (rs.length - np) := by
  simp only [pointAfter3, List.length_append, length_pointAfterPairs, length_pointAfterN, List.length_take,
    List.length_drop]

/-- **π1-rec3's batch state** after the records `rs` from `target`: the claim is the partial sum at the point so far,
the first `P.vars / 2` records pair rounds, the others plain rounds. -/
def BatchState3 (b : E) (nw : E → E) (P : ProdSum) (target : E) (rs : List (List E × List E)) : Prop :=
  claimAfter3 nw (P.vars / 2) target rs = P.T (pointAfter3 b nw (P.vars / 2) rs)

/-- **At the start** the state is: the target is the sum. -/
theorem batchState3_nil (b : E) (nw : E → E) (P : ProdSum) (target : E) :
    BatchState3 b nw P target [] ↔ target = P.T [] := by
  simp only [BatchState3, claimAfter3, pointAfter3, List.take_nil, List.drop_nil]
  exact Iff.rfl

/-- Within the pair rounds the batch state is the pair state. -/
theorem batchState3_iff_pairs (P : ProdSum) {b : E} (hb : b * b + b = 1) (nw : E → E) (target : E)
    (rs : List (List E × List E)) (hr : rs.length ≤ P.vars / 2) :
    BatchState3 b nw P target rs ↔ PairState (P.pairOracle b hb) nw target rs := by
  unfold BatchState3 claimAfter3 pointAfter3
  rw [List.take_of_length_le hr, List.drop_of_length_le hr]
  simp only [claimAfterN, pointAfterN, List.map_nil, List.append_nil]
  exact Iff.rfl

/-- **A pair round of the batch**: at most `8 · 2^32 / |E|`. -/
theorem batchState3_step_pair (P : ProdSum) {b : E} (hb : b * b + b = 1) (nw : E → E)
    (hnw : ∀ s, (univ.filter fun x ↦ nw x = s).card ≤ 2 ^ 32) (target : E) (rs : List (List E × List E))
    (m : List E) (hr : rs.length < P.vars / 2) :
    Pr{let c ← Compose.draws E 1}[¬ BatchState3 b nw P target rs ∧
        BatchState3 b nw P target (rs ++ [(m, c)])] ≤
      ((8 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have himp : ∀ c : List E, (¬ BatchState3 b nw P target rs ∧ BatchState3 b nw P target (rs ++ [(m, c)])) →
      (¬ PairState (P.pairOracle b hb) nw target rs ∧
        PairState (P.pairOracle b hb) nw target (rs ++ [(m, c)])) := by
    intro c ⟨h1, h2⟩
    exact ⟨fun h => h1 ((batchState3_iff_pairs P hb nw target rs hr.le).mpr h),
      (batchState3_iff_pairs P hb nw target _ (by simp only [List.length_append, List.length_singleton]; omega)).mp
        h2⟩
  exact (prEvent_mono _ _ _ himp).trans ((P.pairOracle b hb).step_sound hb nw hnw target rs
    (by show 2 * rs.length + 2 ≤ P.vars; omega) m)

/-- **A plain round of the batch**, after the pairs: at most `2 · 2^32 / |E|`. -/
theorem batchState3_step_last (P : ProdSum) (b : E) (nw : E → E)
    (hnw : ∀ s, (univ.filter fun x ↦ nw x = s).card ≤ 2 ^ 32) (target : E) (rs : List (List E × List E))
    (m : List E) (h1 : P.vars / 2 ≤ rs.length) (h2 : rs.length < P.vars - P.vars / 2) :
    Pr{let c ← Compose.draws E 1}[¬ BatchState3 b nw P target rs ∧
        BatchState3 b nw P target (rs ++ [(m, c)])] ≤
      ((2 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have happ : ∀ c : List E,
      claimAfter3 nw (P.vars / 2) target (rs ++ [(m, c)]) =
        polyEval (roundCoeffs (claimAfter3 nw (P.vars / 2) target rs) (m.getD 0 0) (m.getD 1 0))
          (nw (c.headD 0)) ∧
      pointAfter3 b nw (P.vars / 2) (rs ++ [(m, c)]) =
        pointAfter3 b nw (P.vars / 2) rs ++ [nw (c.headD 0)] := by
    intro c
    unfold claimAfter3 pointAfter3
    rw [List.take_append_of_le_length h1, List.drop_append_of_le_length h1, claimAfterN_append,
      pointAfterN_append, List.append_assoc]
    exact ⟨rfl, rfl⟩
  have himp : ∀ c : List E, (¬ BatchState3 b nw P target rs ∧ BatchState3 b nw P target (rs ++ [(m, c)])) →
      (claimAfter3 nw (P.vars / 2) target rs ≠ P.oracle.T (pointAfter3 b nw (P.vars / 2) rs) ∧
        polyEval (roundCoeffs (claimAfter3 nw (P.vars / 2) target rs) (m.getD 0 0) (m.getD 1 0))
            (nw (c.headD 0)) =
          P.oracle.T (pointAfter3 b nw (P.vars / 2) rs ++ [nw (c.headD 0)])) := by
    intro c ⟨h3, h4⟩
    refine ⟨h3, ?_⟩
    unfold BatchState3 at h4
    rw [(happ c).1, (happ c).2] at h4
    exact h4
  refine (prEvent_mono _ _ _ himp).trans (P.oracle.round_sound_narrow nw hnw _ ?_ _ _ _)
  show (pointAfter3 b nw (P.vars / 2) rs).length < P.vars
  rw [length_pointAfter3]
  omega

/-- **Each round of π1-rec3's batch** over `P.vars = 2 np + 1` variables, as the chain's: a pair round
(`rs.length < np`) at most `8 · 2^32 / |E|`, the last plain round `2 · 2^32 / |E|`. -/
theorem batchState3_step (P : ProdSum) (np : ℕ) {b : E} (hb : b * b + b = 1) (nw : E → E)
    (hnw : ∀ s, (univ.filter fun x ↦ nw x = s).card ≤ 2 ^ 32) (target : E) (rs : List (List E × List E))
    (m : List E) (hv : P.vars = 2 * np + 1) (hr : rs.length ≤ np) :
    Pr{let c ← Compose.draws E 1}[¬ BatchState3 b nw P target rs ∧
        BatchState3 b nw P target (rs ++ [(m, c)])] ≤
      if rs.length < np then ((8 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
      else ((2 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have hnp : P.vars / 2 = np := by omega
  split_ifs with h
  · exact batchState3_step_pair P hb nw hnw target rs m (by omega)
  · exact batchState3_step_last P b nw hnw target rs m (by omega) (by omega)

theorem length_pointAfter3_full (P : ProdSum) (b : E) (nw : E → E) (rs : List (List E × List E))
    (hr : rs.length = P.vars - P.vars / 2) : (pointAfter3 b nw (P.vars / 2) rs).length = P.vars := by
  rw [length_pointAfter3]
  omega

/-- **At the end** (all `P.vars - P.vars / 2` records), the state is: the claim is `Σ_k c_k Â_k(r) B̂_k(r)` at the
batch's point `r` (`ProdSum.T_full`). -/
theorem batchState3_full (P : ProdSum) (b : E) (nw : E → E) (target : E) (rs : List (List E × List E))
    (hr : rs.length = P.vars - P.vars / 2) :
    BatchState3 b nw P target rs ↔ claimAfter3 nw (P.vars / 2) target rs =
      ∑ k ∈ range P.n, P.coef k * (foldAll (P.A k) (pointAfter3 b nw (P.vars / 2) rs) 0 *
        foldAll (P.B k) (pointAfter3 b nw (P.vars / 2) rs) 0) := by
  unfold BatchState3
  rw [P.T_full _ (length_pointAfter3_full P b nw rs hr)]

/-! ## The verifier's constants -/

/-- **The order-3 form**: an element of order `3` is a root of `X² + X + 1`. -/
theorem order3_spec {x : E} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : x * x + x = 1 := by
  have h : (x - 1) * (x * x + x + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · linear_combination h - (CharTwo.two_eq_zero : (2 : E) = 0)

/-- With `x`, `x + 1`. -/
theorem order3_spec_succ {x : E} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : (x + 1) * (x + 1) + (x + 1) = 1 :=
  hb_succ (order3_spec h3 h1)

/-- `x^n` by square and multiply is the power. -/
theorem epowAux_eq_pow : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, hn => by
    have : n = 0 := by simpa using hn
    subst this
    simp [epowAux]
  | fuel + 1, base, out, n, hn => by
    have hn' : n / 2 < 2 ^ fuel := by rw [pow_succ] at hn; omega
    unfold epowAux
    split_ifs with h0 h1
    · subst h0
      simp
    · rw [epowAux_eq_pow fuel _ _ _ hn']
      conv_rhs => rw [← Nat.div_add_mod n 2, h1]
      ring
    · rw [epowAux_eq_pow fuel _ _ _ hn']
      have h1' : n % 2 = 0 := by omega
      conv_rhs => rw [← Nat.div_add_mod n 2, h1']
      ring

theorem epow_eq_pow (x : E) (n : ℕ) : epow x n = x ^ n := by
  rw [epow, epowAux_eq_pow _ _ _ _ Nat.lt_log2_self, one_mul]

/-- `GEN = E(2)` is `x` in `K`, leanerVM's `g`. -/
theorem gen_eq_ofK : UniStatement.gen = ofK LeanVM.Parameters.g := by
  rw [ofK_eq_ofLimbs]
  rfl

/-- `x^((2^64 − 1)/3)`, the element of order `3` `cantorBeta1` starts from. -/
def cantorG : E := epow UniStatement.gen ((2 ^ 64 - 1) / 3)

theorem cantorBeta1_eq :
    cantorBeta1 = if (cantorG.limb 0).lane &&& 1 = 0 then cantorG else cantorG + 1 := rfl

theorem ofK_pow_rec3 (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

theorem ofK_one_rec3 : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem cantorG_eq : cantorG = ofK (LeanVM.Parameters.g ^ ((2 ^ 64 - 1) / 3)) := by
  rw [cantorG, epow_eq_pow, gen_eq_ofK, ofK_pow_rec3]

theorem cantorG_pow_three : cantorG ^ 3 = 1 := by
  rw [cantorG_eq, ← ofK_pow_rec3, ← pow_mul,
    show (2 ^ 64 - 1) / 3 * 3 = 2 ^ 64 - 1 by norm_num, g_pow_card_sub_one, ofK_one_rec3]

theorem cantorG_ne_one : cantorG ≠ 1 := by
  rw [cantorG_eq, ← ofK_one_rec3]
  exact fun h => g_pow_div_three_ne_one (ofK_injective h)

/-- **`β_1² + β_1 = 1`** for the verifier's `cantorBeta1` (`cantor_beta1`), algebraically: `x^((2^64 − 1)/3)` has
order `3` (leanerVM's `g_pow_card_sub_one`, `g_pow_div_three_ne_one`), and both roots of `X² + X + 1` satisfy it. -/
theorem cantorBeta1_spec : cantorBeta1 * cantorBeta1 + cantorBeta1 = 1 := by
  rw [cantorBeta1_eq]
  split_ifs
  · exact order3_spec cantorG_pow_three cantorG_ne_one
  · exact order3_spec_succ cantorG_pow_three cantorG_ne_one

/-- **`β_1`'s word** `0x19c9369f278adc02` (`UniStatement.beta`'s second, `UniComplete.Domain.betaWords`): `β² + β = 1`,
one product in `K` by the kernel. -/
theorem betaWord_spec :
    ofK (K.ofLane 0x19c9369f278adc02) * ofK (K.ofLane 0x19c9369f278adc02) + ofK (K.ofLane 0x19c9369f278adc02) =
      1 := by
  have h : K.ofLane 0x19c9369f278adc02 * K.ofLane 0x19c9369f278adc02 + K.ofLane 0x19c9369f278adc02 = 1 := by
    decide +kernel
  rw [← ofK_mul, ← ofK_add, h, ofK_one_rec3]

/-- **π1-rec3's batch at the verifier's constants** (`cantorBeta1`, `narrowE`): `batchState3_step` with no
hypothesis left but the shape. -/
theorem batchState3_step_rec3 (P : ProdSum) (np : ℕ) (target : E) (rs : List (List E × List E)) (m : List E)
    (hv : P.vars = 2 * np + 1) (hr : rs.length ≤ np) :
    Pr{let c ← Compose.draws E 1}[¬ BatchState3 cantorBeta1 narrowE P target rs ∧
        BatchState3 cantorBeta1 narrowE P target (rs ++ [(m, c)])] ≤
      if rs.length < np then ((8 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
      else ((2 * 2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  batchState3_step P np cantorBeta1_spec narrowE card_narrowE_fiber_le target rs m hv hr

end UniSound

/-- info: 'UniSound.psum_V2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.psum_V2

/-- info: 'UniSound.pairSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.pairSum

/-- info: 'UniSound.pairCoeffs_eq_rust' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.pairCoeffs_eq_rust

/-- info: 'UniSound.PairOracle.round_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.PairOracle.round_sound

/-- info: 'UniSound.ProdSum.pairOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.ProdSum.pairOracle

/-- info: 'UniSound.PairOracle.step_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.PairOracle.step_sound

/-- info: 'UniSound.batchState3_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.batchState3_nil

/-- info: 'UniSound.batchState3_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.batchState3_step

/-- info: 'UniSound.batchState3_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.batchState3_full

/-- info: 'UniSound.cantorBeta1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.cantorBeta1_spec

/-- info: 'UniSound.betaWord_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.betaWord_spec

/-- info: 'UniSound.batchState3_step_rec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.batchState3_step_rec3
