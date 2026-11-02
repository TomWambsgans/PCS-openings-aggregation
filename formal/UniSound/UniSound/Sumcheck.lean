-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Prob

/-!
# The batching sumcheck, generic in its weights

`batch` (SPEC.md §8) proves `Σ_{u ∈ {0,1}^V} g(u) = target` for
`g = Σ_k λ^k W_k · C_k`, each `W_k` (the weight of commitment `k`'s combined claim, which the
verifier computes, `weightAt`) and `C_k` (the stack, zero-extended to `V` variables) a table of
`2^V` values read multilinearly. Here it is **generic in the weights**: any list of products of two
tables (`ProdSum`), so the gas iteration's changes to the weights (levers 1b, 1c) and the
matrices' reduction joining the batch as a `λ³` term (lever 4a: one more product, its tables
zero-extended) change only the instance.

* **A round** (`roundCoeffs`): the stream holds `c0, c2`; the round polynomial is
  `q = c0 + (claim + c2) X + c2 X²` (`roundPoly 3 claim none`), so `q(0) + q(1) = claim` by
  construction; the next claim is `q(x)` at the round's challenge (`polyEval`).
* **The state** before a round, after the prefix `r` of challenges: the claim is the true partial
  sum `T(r) = Σ_x g(r, x)` (`SumOracle`: the partial sums `T` and the honest round polynomials
  `H r`, of degree at most `2`, with `H r (x) = T(r ++ [x])` and `T r = H r (0) + H r (1)`).
* **`SumOracle.round_sound`**: a round turns a false claim into a true one with probability at most
  `2 / |E|` (Schwartz–Zippel on `q − H r ≠ 0`, of degree at most `2`).
* **`ProdSum.oracle`**: the sum oracle of `Σ_k c_k A_k B_k` for tables `A_k`, `B_k` folded low
  coordinate first (`foldT`, the multilinear extension's partial evaluation, as `multilinear_eval`
  and the stacks' points read their coordinates); at a full point `T r = Σ_k c_k Â_k(r) B̂_k(r)`
  (`ProdSum.T_full`).
-/

namespace UniSound

open LeanVM.Parameters Finset UniStatement Polynomial
open scoped ENNReal

/-! ## A round -/

/-- The round polynomial the stream gives (`roundPoly 3 claim none`): `[c0, claim + c2, c2]`. -/
def roundCoeffs (claim c0 c2 : E) : List E := [c0, claim + c2, c2]

/-- Its polynomial, `c0 + (claim + c2) X + c2 X²`. -/
noncomputable def roundPolyP (claim c0 c2 : E) : Polynomial E :=
  C c0 + C (claim + c2) * X + C c2 * X ^ 2

theorem polyEval_roundCoeffs (claim c0 c2 x : E) :
    polyEval (roundCoeffs claim c0 c2) x = (roundPolyP claim c0 c2).eval x := by
  simp only [roundCoeffs, polyEval, List.foldr, roundPolyP, Polynomial.eval_add, eval_C, Polynomial.eval_mul, eval_X,
    eval_pow]
  ring

theorem roundPolyP_sum (claim c0 c2 : E) :
    (roundPolyP claim c0 c2).eval 0 + (roundPolyP claim c0 c2).eval 1 = claim := by
  simp only [roundPolyP, Polynomial.eval_add, eval_C, Polynomial.eval_mul, eval_X, eval_pow]
  linear_combination (c0 + c2) * (CharTwo.two_eq_zero : (2 : E) = 0)

theorem natDegree_CX_le (a b : E) : (C a + X * C b).natDegree ≤ 1 :=
  (natDegree_add_le _ _).trans (max_le (by simp)
    ((natDegree_mul_le).trans (by rw [natDegree_C, add_zero]; exact natDegree_X_le)))

theorem natDegree_roundPolyP_le (claim c0 c2 : E) : (roundPolyP claim c0 c2).natDegree ≤ 2 := by
  unfold roundPolyP
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · simp
  · refine (natDegree_mul_le).trans ?_
    rw [natDegree_C, zero_add]
    exact natDegree_X_le.trans (by norm_num)
  · exact natDegree_C_mul_X_pow_le _ _

/-! ## The states -/

/-- **A sum oracle** over `V` variables: the true partial sum at each prefix of challenges, and the
honest round polynomial there. -/
structure SumOracle where
  vars : ℕ
  T : List E → E
  H : List E → Polynomial E
  eval_H : ∀ r x, (H r).eval x = T (r ++ [x])
  T_eq : ∀ r, r.length < vars → T r = (H r).eval 0 + (H r).eval 1
  deg_H : ∀ r, (H r).natDegree ≤ 2

/-- **A round of the sumcheck is sound**: from a false claim, the round's challenge makes the next
claim true with probability at most `2 / |E|`, whatever the message. -/
theorem SumOracle.round_sound (O : SumOracle) (r : List E) (hr : r.length < O.vars)
    (claim c0 c2 : E) :
    Pr{let c ← Compose.draws E 1}[claim ≠ O.T r ∧
        polyEval (roundCoeffs claim c0 c2) (c.headD 0) = O.T (r ++ [c.headD 0])] ≤
      ((2 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  set D : Polynomial E := roundPolyP claim c0 c2 - O.H r with hD
  have himp : ∀ c : List E, (claim ≠ O.T r ∧
      polyEval (roundCoeffs claim c0 c2) (c.headD 0) = O.T (r ++ [c.headD 0])) →
        ∃ p ∈ [D], p ≠ 0 ∧ p.eval (c.headD 0) = 0 := by
    intro c ⟨hne, heq⟩
    refine ⟨D, List.mem_singleton_self _, fun h0 => hne ?_, ?_⟩
    · have h1 : roundPolyP claim c0 c2 = O.H r := sub_eq_zero.mp h0
      rw [O.T_eq r hr, ← h1, roundPolyP_sum]
    · rw [hD, Polynomial.eval_sub, ← polyEval_roundCoeffs, O.eval_H, heq, sub_self]
  refine (prEvent_mono _ _ _ himp).trans ((prEvent_root_le [D]).trans ?_)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  exact (natDegree_sub_le _ _).trans (max_le (natDegree_roundPolyP_le _ _ _) (O.deg_H r))

/-! ## Products of tables -/

/-- One fold of a table on its low coordinate at `x` (`foldOnce`): `f(2i) + x (f(2i) + f(2i+1))`. -/
def foldT (f : ℕ → E) (x : E) : ℕ → E := fun i => f (2 * i) + x * (f (2 * i) + f (2 * i + 1))

/-- A table folded on the coordinates of a prefix, low first. -/
def foldAll (f : ℕ → E) (r : List E) : ℕ → E := r.foldl foldT f

theorem foldAll_append (f : ℕ → E) (r : List E) (x : E) :
    foldAll f (r ++ [x]) = foldT (foldAll f r) x := by
  simp [foldAll, List.foldl_append]

/-- **A sum of products of tables** over `V` variables: `Σ_{k < n} c_k A_k B_k`. -/
structure ProdSum where
  vars : ℕ
  n : ℕ
  coef : ℕ → E
  A : ℕ → ℕ → E
  B : ℕ → ℕ → E

namespace ProdSum

variable (P : ProdSum)

/-- The true partial sum after the prefix `r`. -/
def T (r : List E) : E :=
  ∑ k ∈ range P.n, P.coef k * ∑ i ∈ range (2 ^ (P.vars - r.length)),
    foldAll (P.A k) r i * foldAll (P.B k) r i

/-- The linear polynomial of a table's pair `i` after the prefix `r`. -/
noncomputable def lin (f : ℕ → E) (i : ℕ) : Polynomial E := C (f (2 * i)) + X * C (f (2 * i) + f (2 * i + 1))

/-- The honest round polynomial after the prefix `r`. -/
noncomputable def H (r : List E) : Polynomial E :=
  ∑ k ∈ range P.n, C (P.coef k) * ∑ i ∈ range (2 ^ (P.vars - r.length - 1)),
    lin (foldAll (P.A k) r) i * lin (foldAll (P.B k) r) i

theorem sum_range_two_mul (m : ℕ) (f : ℕ → E) :
    ∑ i ∈ range (2 * m), f i = ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

theorem eval_lin (f : ℕ → E) (i : ℕ) (x : E) : (lin f i).eval x = foldT f x i := by
  simp [lin, foldT, Polynomial.eval_add, Polynomial.eval_mul]

theorem eval_H (r : List E) (x : E) : (P.H r).eval x = P.T (r ++ [x]) := by
  unfold H T
  simp only [eval_finsetSum, Polynomial.eval_mul, eval_C, eval_lin, List.length_append,
    List.length_singleton, foldAll_append]
  refine sum_congr rfl fun k _ => ?_
  rw [show P.vars - (r.length + 1) = P.vars - r.length - 1 by omega]

theorem T_eq (r : List E) (hr : r.length < P.vars) : P.T r = (P.H r).eval 0 + (P.H r).eval 1 := by
  unfold H T
  simp only [eval_finsetSum, Polynomial.eval_mul, eval_C, eval_lin]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  rw [show P.vars - r.length = (P.vars - r.length - 1) + 1 by omega, pow_succ, mul_comm,
    sum_range_two_mul]
  refine sum_congr rfl fun i _ => ?_
  have h1 : ∀ a b : E, a + 1 * (a + b) = b := fun a b => by
    linear_combination a * (CharTwo.two_eq_zero : (2 : E) = 0)
  simp only [foldT, zero_mul, add_zero, h1]

theorem deg_H (r : List E) : (P.H r).natDegree ≤ 2 := by
  unfold H
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
  refine (natDegree_mul_le).trans ?_
  exact (add_le_add (natDegree_CX_le _ _) (natDegree_CX_le _ _)).trans (by norm_num)

/-- **The sum oracle of a sum of products of tables.** -/
noncomputable def oracle : SumOracle where
  vars := P.vars
  T := P.T
  H := P.H
  eval_H := P.eval_H
  T_eq := P.T_eq
  deg_H := P.deg_H

/-- At a full point the partial sum is the combination of the products of the tables' extensions
there. -/
theorem T_full (r : List E) (hr : r.length = P.vars) :
    P.T r = ∑ k ∈ range P.n, P.coef k * (foldAll (P.A k) r 0 * foldAll (P.B k) r 0) := by
  unfold T
  rw [hr, Nat.sub_self, pow_zero]
  simp

end ProdSum

/-! ## The rounds' claims -/

/-- **The claims along the rounds**: from `claim`, each round's message `[c0, c2]` and its challenge
`x` give the next claim `q(x)` (`sumcheck`'s loop). -/
def claimAfter : E → List (List E × List E) → E
  | claim, [] => claim
  | claim, (m, c) :: rest =>
    claimAfter (polyEval (roundCoeffs claim (m.getD 0 0) (m.getD 1 0)) (c.headD 0)) rest

/-- The rounds' challenges, the sumcheck's point. -/
def pointAfter (rounds : List (List E × List E)) : List E := rounds.map fun x => x.2.headD 0

theorem claimAfter_append (claim : E) (rs : List (List E × List E)) (m c : List E) :
    claimAfter claim (rs ++ [(m, c)]) =
      polyEval (roundCoeffs (claimAfter claim rs) (m.getD 0 0) (m.getD 1 0)) (c.headD 0) := by
  induction rs generalizing claim with
  | nil => rfl
  | cons x rs ih => exact ih _

theorem pointAfter_append (rs : List (List E × List E)) (m c : List E) :
    pointAfter (rs ++ [(m, c)]) = pointAfter rs ++ [c.headD 0] := by
  simp [pointAfter]

theorem length_pointAfter (rs : List (List E × List E)) : (pointAfter rs).length = rs.length := by
  simp [pointAfter]

/-- **The sumcheck's state** after its rounds `rs` from `target`: the claim is the partial sum at
the point so far. -/
def SumState (O : SumOracle) (target : E) (rs : List (List E × List E)) : Prop :=
  claimAfter target rs = O.T (pointAfter rs)

/-- **Each round of the sumcheck**, as the chain's: its state from false to true with probability at
most `2 / |E|`. -/
theorem SumOracle.step_sound (O : SumOracle) (target : E) (rs : List (List E × List E))
    (hr : rs.length < O.vars) (m : List E) :
    Pr{let c ← Compose.draws E 1}[¬ SumState O target rs ∧ SumState O target (rs ++ [(m, c)])] ≤
      ((2 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have himp : ∀ c : List E, (¬ SumState O target rs ∧ SumState O target (rs ++ [(m, c)])) →
      (claimAfter target rs ≠ O.T (pointAfter rs) ∧
        polyEval (roundCoeffs (claimAfter target rs) (m.getD 0 0) (m.getD 1 0)) (c.headD 0) =
          O.T (pointAfter rs ++ [c.headD 0])) := by
    intro c ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    unfold SumState at h2
    rwa [claimAfter_append, pointAfter_append] at h2
  exact (prEvent_mono _ _ _ himp).trans
    (O.round_sound (pointAfter rs) (by rw [length_pointAfter]; exact hr) _ _ _)

end UniSound
