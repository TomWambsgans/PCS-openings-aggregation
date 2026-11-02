-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Fs

/-!
# The sumcheck's folds are the claims' multilinear extensions

The batching sumcheck folds its tables on their coordinates, low first (`foldAll`, `foldOnce`'s
`f(2i) + x (f(2i) + f(2i+1))`); the claims `PCS_OPEN` checks are multilinear extensions written as
sums, `Σ_u eq(p, u) f(u)` (`cubeEq`, `mleStk`, `mleArr`). **`foldAll_eq_sum`**: they are the same,
`foldAll f r i = Σ_{u < 2^|r|} eq(r, u) f(i 2^|r| + u)`; so a stack's point claim at the batch's
point is its table's fold there (`mleStk_eq_foldAll`), the glue `UniFinal` needs between the
openings' claims and the sumcheck's last claim.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

theorem testBit_two_mul_add (u b k : ℕ) (hb : b < 2) :
    (2 * u + b).testBit (k + 1) = u.testBit k := by
  rw [Nat.testBit_succ]
  congr 1
  omega

theorem testBit_two_mul_add_zero (u b : ℕ) (hb : b < 2) :
    (2 * u + b).testBit 0 = decide (b = 1) := by
  rw [Nat.testBit_zero]
  interval_cases b <;> simp [Nat.add_mod]

/-- `eq((x, r), 2u + b) = (1 + x + b) eq(r, u)`. -/
theorem cubeEq_cons (x : E) (r : List E) (n u b : ℕ) (hb : b < 2) :
    cubeEq (x :: r) (n + 1) (2 * u + b) =
      (1 + x + if b = 1 then 1 else 0) * cubeEq r n u := by
  unfold cubeEq
  rw [Finset.prod_range_succ']
  rw [mul_comm]
  congr 1
  · simp only [List.getD_cons_zero, testBit_two_mul_add_zero u b hb, decide_eq_true_eq]
  · refine Finset.prod_congr rfl fun k _ => ?_
    simp only [List.getD_cons_succ, testBit_two_mul_add u b k hb]

/-- **A fold is a multilinear extension**: `foldAll f r i = Σ_{u < 2^|r|} eq(r, u) f(i 2^|r| + u)`. -/
theorem foldAll_eq_sum : ∀ (r : List E) (f : ℕ → E) (i : ℕ),
    foldAll f r i = ∑ u ∈ range (2 ^ r.length), cubeEq r r.length u * f (i * 2 ^ r.length + u)
  | [], f, i => by simp [foldAll, cubeEq]
  | x :: r, f, i => by
    have ih := foldAll_eq_sum r (foldT f x) i
    simp only [foldAll, List.foldl_cons] at ih ⊢
    rw [ih, List.length_cons, pow_succ, mul_comm (2 ^ r.length) 2, ProdSum.sum_range_two_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show 2 * u = 2 * u + 0 by rfl, cubeEq_cons x r r.length u 0 (by norm_num),
      cubeEq_cons x r r.length u 1 (by norm_num)]
    simp only [foldT, ite_eq_right (show (0 : ℕ) ≠ 1 by norm_num), add_zero]
    have e1 : i * (2 * 2 ^ r.length) + 2 * u = 2 * (i * 2 ^ r.length + u) := by ring
    have e2 : i * (2 * 2 ^ r.length) + (2 * u + 1) = 2 * (i * 2 ^ r.length + u) + 1 := by ring
    rw [e1, e2]
    simp only [ite_true]
    have h2 : (1 + x + 1 : E) = x := by
      linear_combination (CharTwo.two_eq_zero : (2 : E) = 0)
    rw [h2]
    ring

/-- **A stack's point claim is its table's fold at the point.** -/
theorem mleStk_eq_foldAll (c : Stk) (pt : List E) :
    mleStk c pt.length pt = foldAll (fun u => ofK (c u)) pt 0 := by
  rw [foldAll_eq_sum]
  unfold mleStk
  rw [Finset.sum_range (fun u => cubeEq pt pt.length u * ofK (c (0 * 2 ^ pt.length + u)))]
  simp

end UniSound
