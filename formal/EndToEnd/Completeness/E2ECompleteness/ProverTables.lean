-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The tables `E2ECompleteness.proveSpec` (`ProverDefs.lean`, `formal/Statement`'s `Prover.lean`)
-- computes, against `formal/Completeness`'s honest prover. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the fields `K`, `E` and their limbs.
import E2ECompleteness.ProverDefs
import Bridge.Ntt
import Completeness

/-!
# The prover's witness and wiring tables are the honest prover's

`proveSpec` (`ProverDefs.lean`) computes its tables with the additive transform
(`Domain.coefficients`); `formal/Completeness`'s honest prover takes them as `choose`s
(`tableOf`: a table whose polynomial takes given values at the cells). A table on `M` digits is
determined by its polynomial (`tablePoly_injective`: the novel basis has one degree per entry), so
the two agree as soon as their polynomials do, and those are fixed by their values at the cells
(`CantorBasis.tablePoly_ext`). Here, for any cells `f` given as an array, for any wiring:

* `betaAt_eq`: the Statement's basis (`beta()`, `IsCantorBasis`, its `solve` clearing the low bit)
  is `deployedBasis` on its first `24` vectors (`deployedBasis_unique`);
* **`witness_table`**: the witness table `witnessEntry` (the cells' coefficients, then the masks)
  is `natTable (witnessTable deployedBasis f masks)`;
* **`wiring_table`**: the circuit's wiring table `coefficients 24 0 (sigma.map point)` is
  `natTable (wiringTableK deployedBasis deployedSigma)`;

and the infrastructure the quotient table needs (`ProverQuotient*.lean`): tables padded with zeros
(`tablePoly_pad`), the transform over `E` (`values_getD_tablePoly_E`, `tablePoly_coefficients_E`),
points of `xor`s (`point_xor`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness

namespace ProverTables

/-! ## Tables of polynomials -/

section Generic

variable {F : Type*} [Field F] [CharP F 2]

/-- **A table whose polynomial is zero is zero**: the novel basis has one degree per entry. -/
theorem tablePoly_eq_zero : ∀ {M : ℕ} (d : (Fin M → Bool) → F), tablePoly d = 0 → d = 0
  | 0, d, h => by
    funext b
    have hb : b = default := Subsingleton.elim _ _
    unfold tablePoly at h
    rw [Fintype.sum_unique] at h
    simp only [Fin.prod_univ_zero, mul_one, C_eq_zero] at h
    rw [hb]
    exact h
  | M + 1, d, h => by
    rw [tablePoly_snoc] at h
    have h1 : tablePoly (fun b => d (Fin.snoc b true)) = 0 := by
      by_contra hne
      have hdeg0 := natDegree_tablePoly_lt (fun b => d (Fin.snoc b false))
      obtain ⟨hmon, hdeg⟩ := digitPoly_monic_natDegree (F := F) M
      have hmul : (digitPoly M * tablePoly (fun b => d (Fin.snoc b true)) : F[X]).natDegree =
          2 ^ M + (tablePoly (fun b => d (Fin.snoc b true))).natDegree := by
        rw [natDegree_mul hmon.ne_zero hne, hdeg]
      have e := congrArg natDegree (eq_neg_of_add_eq_zero_left h)
      rw [natDegree_neg, hmul] at e
      omega
    have h0 : tablePoly (fun b => d (Fin.snoc b false)) = 0 := by
      rw [h1, mul_zero, add_zero] at h
      exact h
    have e0 := tablePoly_eq_zero _ h0
    have e1 := tablePoly_eq_zero _ h1
    funext b
    rw [← Fin.snoc_init_self b]
    cases b (Fin.last M)
    · simpa using congrFun e0 (Fin.init b)
    · simpa using congrFun e1 (Fin.init b)

/-- **A table is determined by its polynomial.** -/
theorem tablePoly_injective {M : ℕ} {c c' : (Fin M → Bool) → F} (h : tablePoly c = tablePoly c') :
    c = c' :=
  sub_eq_zero.mp (tablePoly_eq_zero (c - c') (by rw [tablePoly_sub, h, sub_self]))

/-- **A table by numbers, zero from `2^M` on, holds the same polynomial on any `N ≥ M` digits.** -/
theorem tablePoly_pad {M : ℕ} (a : ℕ → F) (ha : ∀ n, 2 ^ M ≤ n → a n = 0) (N : ℕ) (hN : M ≤ N) :
    tablePoly (fun b : Fin N → Bool => a (Completeness.idx b)) =
      tablePoly (fun b : Fin M → Bool => a (Completeness.idx b)) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hMN ih =>
    rw [tablePoly_snoc, ← ih]
    have h1 : (fun b : Fin N → Bool =>
        a (Completeness.idx (Fin.snoc b true : Fin (N + 1) → Bool))) = fun _ => 0 := by
      funext b
      apply ha
      rw [Completeness.idx_snoc, if_pos rfl]
      calc 2 ^ M ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hMN
        _ ≤ _ := Nat.le_add_left _ _
    have h0 : (fun b : Fin N → Bool =>
        a (Completeness.idx (Fin.snoc b false : Fin (N + 1) → Bool))) =
          fun b => a (Completeness.idx b) := by
      funext b
      rw [Completeness.idx_snoc]
      simp
    rw [h1, h0, Completeness.tablePoly_zero, mul_zero, add_zero]

/-- A sum over the first `2^m` numbers is a sum over the cube. -/
theorem sum_range_cube {M' : Type*} [AddCommMonoid M'] {m : ℕ} (f : ℕ → M') :
    ∑ j ∈ range (2 ^ m), f j = ∑ b : Fin m → Bool, f (Completeness.idx b) := by
  refine Finset.sum_bij' (fun j _ ↦ Completeness.bitsOf m j) (fun b _ ↦ Completeness.idx b)
    (fun _ _ ↦ Finset.mem_univ _) (fun b _ ↦ Finset.mem_range.mpr (Completeness.idx_lt b))
    (fun j hj ↦ Completeness.idx_bitsOf m j (Finset.mem_range.mp hj))
    (fun b _ ↦ Completeness.bitsOf_idx b) (fun j hj ↦ ?_)
  rw [Completeness.idx_bitsOf m j (Finset.mem_range.mp hj)]

end Generic

/-! ## Arrays -/

theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) {p : ℕ} (hp : p < n) :
    (Array.ofFn f).getD p d = f ⟨p, hp⟩ := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hp]

theorem getD_of_size_le {α : Type*} (a : Array α) (d : α) {p : ℕ} (hp : a.size ≤ p) :
    a.getD p d = d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hp]

theorem getD_map {α β : Type*} (f : α → β) (a : Array α) (d : α) (p : ℕ) :
    (a.map f).getD p (f d) = f (a.getD p d) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[p]? <;> rfl

/-- An array of `K` read as a table by numbers. -/
theorem getD_eq_natTable {m : ℕ} (a : Array K) (ha : a.size = 2 ^ m) (c : (Fin m → Bool) → K)
    (h : ∀ b, a.getD (Completeness.idx b) 0 = c b) (i : ℕ) :
    a.getD i 0 = Completeness.natTable c i := by
  unfold Completeness.natTable
  split_ifs with hi
  · rw [← h, Completeness.idx_bitsOf m i hi]
  · exact getD_of_size_le a 0 (by omega)

/-! ## `K` in `E` -/

theorem ofK_eq (a : K) : ofK a = algebraMap K E a := rfl

theorem sq_ofK (x : K) : sq (ofK x) = ofK (S x) := by
  simp only [sq, S, ofK_eq, map_add, map_mul]

theorem sq_iterate_ofK (k : ℕ) (x : K) : sq^[k] (ofK x) = ofK (S^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sq_ofK, ih]

/-! ## Points -/

theorem point_xor (a b : ℕ) : point (a ^^^ b) = point a + point b := by
  rw [Bridge.Ntt.point_eq_sum, Bridge.Ntt.point_eq_sum, Bridge.Ntt.point_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit t <;> cases b.testBit t <;> simp [CharTwo.add_self_eq_zero]

theorem point_zero : point 0 = 0 := by
  rw [Bridge.Ntt.point_eq_sum]
  simp

/-- Disjoint bits add. -/
theorem add_eq_xor_of_lt (k q r : ℕ) (hr : r < 2 ^ k) : 2 ^ k * q + r = (2 ^ k * q) ^^^ r := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mul_pow_two_add q hr, Nat.testBit_two_pow_mul]
  by_cases hi : k ≤ i
  · have : r.testBit i = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hi))
    simp [hi, this]
  · simp [hi]

theorem point_add_of_lt (k q r : ℕ) (hr : r < 2 ^ k) :
    point (2 ^ k * q + r) = point (2 ^ k * q) + point r := by
  rw [add_eq_xor_of_lt k q r hr, point_xor]

/-! ## The Statement's basis is `deployedBasis` -/

/-- The fold that builds `beta`: entry `k + 1` is `g` of entry `k`. -/
theorem fold_push_spec (g : K → K) : ∀ n : ℕ,
    ((List.range n).foldl (fun b _ ↦ b.push (g (b.back?.getD 1))) #[(1 : K)]).size = n + 1 ∧
    ∀ k < n, ((List.range n).foldl (fun b _ ↦ b.push (g (b.back?.getD 1))) #[(1 : K)]).getD
        (k + 1) 0 =
      g (((List.range n).foldl (fun b _ ↦ b.push (g (b.back?.getD 1))) #[(1 : K)]).getD k 0)
  | 0 => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hs, hk⟩ := fold_push_spec g n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun b _ ↦ b.push (g (b.back?.getD 1))) #[(1 : K)] = A at hs hk
    have hback : A.back?.getD 1 = A.getD n 0 := by
      simp [Array.back?_eq_getElem?, Array.getD_eq_getD_getElem?, hs]
    have hget : ∀ j < n + 1, (A.push (g (A.back?.getD 1))).getD j 0 = A.getD j 0 := by
      intro j hj
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hs, show j ≠ n + 1 by omega]
    refine ⟨by rw [Array.size_push, hs], fun k hk' => ?_⟩
    rw [hget k (by omega)]
    by_cases hkn : k < n
    · rw [hget (k + 1) (by omega)]
      exact hk k hkn
    · have hkn' : k = n := by omega
      subst hkn'
      rw [← hback]
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]

theorem betaAt_succ {k : ℕ} (hk : k + 1 < basisSize) : betaAt (k + 1) = solve (betaAt k) := by
  have h := (fold_push_spec solve (basisSize - 1)).2 k (by omega)
  exact h

theorem lowBit_solve (x : K) : lowBit (solve x) = false := by
  show ((solveLoop 64 x.lane 0 &&& ~~~(1 : UInt64)).toNat.testBit 0) = false
  rw [UInt64.toNat_and, Nat.testBit_and]
  have : (~~~(1 : UInt64)).toNat.testBit 0 = false := by decide
  rw [this, Bool.and_false]

/-- **The Statement's basis is `deployedBasis`** on its first `24` vectors: both are Cantor bases
whose vectors after the first have the low bit clear. -/
theorem betaAt_eq (hB : IsCantorBasis) {k : ℕ} (hk : k < 22 + 2) :
    betaAt k = deployedBasis.β k := by
  have hC : Bridge.Ntt.CantorUpTo (22 + 2) :=
    Bridge.Ntt.cantorUpTo_of_isCantorBasis hB (by unfold basisSize; norm_num)
  refine deployedBasis_unique (Bridge.Ntt.cantorOf hC) (fun j hj hj' => ?_) k hk
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  show lowBit (betaAt (j + 1)) = false
  rw [betaAt_succ (by unfold basisSize; omega)]
  exact lowBit_solve _

/-- The cells' points: `B(idx x)` is `deployedBasis`'s point of `x`. -/
theorem point_idx (hB : IsCantorBasis) (x : Fin (22 + 2) → Bool) :
    point (Completeness.idx x) = deployedBasis.point x := by
  have hC : Bridge.Ntt.CantorUpTo (22 + 2) :=
    Bridge.Ntt.cantorUpTo_of_isCantorBasis hB (by unfold basisSize; norm_num)
  rw [Bridge.Ntt.point_eq_cantor hC (by unfold basisSize; norm_num) (Completeness.idx_lt x),
    Completeness.bitsOf_idx]
  unfold CantorBasis.point
  refine Finset.sum_congr rfl fun j _ => ?_
  show (if x j then betaAt j else 0) = _
  rw [betaAt_eq hB j.isLt]

end ProverTables

end E2ECompleteness
