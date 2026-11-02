-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The tables `E2ECompleteness.proveSpec` (`ProverDefs.lean`, `formal/Statement`'s `Prover.lean`)
-- computes, against `formal/Completeness`'s honest prover. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the fields `K`, `E` and their limbs.
import E2ECompleteness.ProverConstants

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
    unfold tablePoly at h
    rw [Fintype.sum_unique] at h
    simp only [Fin.prod_univ_zero, mul_one, C_eq_zero] at h
    exact (congrArg d (Subsingleton.elim b _)).trans h
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
      rw [Completeness.idx_snoc, ite_eq_left rfl]
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
  simp [Array.getD_eq_getD_getElem?, hp]

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

theorem sq_ofK (x : K) : QuotientSecurity.sq (ofK x) = ofK (S x) := by
  simp only [QuotientSecurity.sq, S, ofK_eq, map_add, map_mul]

theorem sq_iterate_ofK (k : ℕ) (x : K) : QuotientSecurity.sq^[k] (ofK x) = ofK (S^[k] x) := by
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
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add q hr, Nat.testBit_two_pow_mul]
  by_cases hi : k ≤ i
  · have : r.testBit i = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hi))
    simp [hi, this, show ¬ i < k by omega]
  · simp [hi, show i < k by omega]

theorem point_add_of_lt (k q r : ℕ) (hr : r < 2 ^ k) :
    point (2 ^ k * q + r) = point (2 ^ k * q) + point r := by
  rw [add_eq_xor_of_lt k q r hr, point_xor]

/-! ## The cells' points -/

/-- The cells' points: `B(idx x)` is `deployedBasis`'s point of `x`. -/
theorem point_idx (hK : Constants) (x : Fin (22 + 2) → Bool) :
    point (Completeness.idx x) = deployedBasis.point x := by
  have hC : Bridge.Ntt.CantorUpTo (22 + 2) :=
    Bridge.Ntt.cantorUpTo_of_isCantorBasis hK.cantor (by unfold basisSize; norm_num)
  rw [Bridge.Ntt.point_eq_cantor hC (by unfold basisSize; norm_num) (Completeness.idx_lt x),
    Completeness.bitsOf_idx]
  unfold CantorBasis.point
  refine Finset.sum_congr rfl fun j _ => ?_
  show (if x j then betaAt j else 0) = _
  rw [betaAt_eq_deployed hK j.isLt]

/-- The points of `cantorOf` (the Statement's basis) on `24` digits are `deployedBasis`'s. -/
theorem cantorOf_point (hK : Constants) {N : ℕ} (hC : Bridge.Ntt.CantorUpTo N)
    (x : Fin (22 + 2) → Bool) : (Bridge.Ntt.cantorOf hC).point x = deployedBasis.point x := by
  unfold CantorBasis.point
  refine Finset.sum_congr rfl fun j _ => ?_
  show (if x j then betaAt j else 0) = _
  rw [betaAt_eq_deployed hK j.isLt]

theorem cantorUpTo24 (hK : Constants) : Bridge.Ntt.CantorUpTo (22 + 2) :=
  Bridge.Ntt.cantorUpTo_of_isCantorBasis hK.cantor (by unfold basisSize; norm_num)

/-- `idx` of a number's bits is the number modulo `2^V`. -/
theorem idx_bitsOf_mod (V n : ℕ) : Completeness.idx (Completeness.bitsOf V n) = n % 2 ^ V := by
  have e : Completeness.bitsOf V n = Completeness.bitsOf V (n % 2 ^ V) := by
    funext k
    show n.testBit k = (n % 2 ^ V).testBit k
    rw [Nat.testBit_mod_two_pow]
    simp [k.isLt]
  rw [e, Completeness.idx_bitsOf V _ (Nat.mod_lt _ (by positivity))]

/-! ## Tables of the cells: `coefficients` is `tableOf` -/

/-- **`coefficients` of values at the cells is `tableOf` of them**: both tables hold the
polynomial taking those values at the cells (`tablePoly_coefficients_cantor`, `tableOf_eval`), so
they are equal (`tablePoly_injective`). -/
theorem coefficients_eq_tableOf (hK : Constants) (v : Array K) (hv : v.size = 2 ^ 24)
    (g : (Fin (22 + 2) → Bool) → K) (hg : ∀ x, v.getD (Completeness.idx x) 0 = g x)
    (b : Fin (22 + 2) → Bool) :
    (coefficients 24 0 v).getD (Completeness.idx b) 0 =
      Completeness.tableOf deployedBasis le_rfl g b := by
  have hC := cantorUpTo24 hK
  refine congrFun (tablePoly_injective (deployedBasis.tablePoly_ext le_rfl
    (fun b : Fin (22 + 2) → Bool => (coefficients (22 + 2) 0 v).getD (Completeness.idx b) 0) _
    fun x => ?_)) b
  rw [Completeness.tableOf_eval, ← cantorOf_point hK hC x,
    Bridge.Ntt.tablePoly_coefficients_cantor hC (by unfold basisSize; norm_num) v hv x, hg]

/-! ## The witness table -/

/-- **The witness table**: `proveSpec`'s witness table (`witnessEntry`: the cells' coefficients,
then the masks) is `formal/Completeness`'s `witnessTable` (`tableOf` of the cells, then
`maskTable`), entry by entry. -/
theorem witness_table (hK : Constants) (f : (Fin (22 + 2) → Bool) → K) (cells : Array K)
    (hcs : cells.size = 2 ^ 24) (hcells : ∀ b, cells.getD (Completeness.idx b) 0 = f b)
    (masks : PcsQuotient.Masks) (i : ℕ) :
    witnessEntry (2 ^ 24) (coefficients 24 0 cells) (PcsQuotient.maskEntries masks) i =
      Completeness.natTable (Completeness.witnessTable deployedBasis f masks) i := by
  have hinit : Fin.init (Completeness.bitsOf (22 + 2 + 1) i) = Completeness.bitsOf (22 + 2) i :=
    funext fun _ => rfl
  have hmsize : (PcsQuotient.maskEntries masks).size = 16 := Array.size_ofFn
  unfold witnessEntry Completeness.natTable Completeness.witnessTable Completeness.joinTable
  by_cases h24 : i < 2 ^ 24
  · have hl : Completeness.bitsOf (22 + 2 + 1) i (Fin.last _) = false :=
      Nat.testBit_eq_false_of_lt h24
    rw [if_pos h24, if_pos (by omega), hl, hinit]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← coefficients_eq_tableOf hK cells hcs f hcells, Completeness.idx_bitsOf _ _ h24]
  · rw [if_neg h24]
    by_cases h25 : i < 2 ^ (22 + 2 + 1)
    · have hl : Completeness.bitsOf (22 + 2 + 1) i (Fin.last _) = true := by
        show i.testBit (22 + 2) = true
        have e : i = 2 ^ (22 + 2) + (i - 2 ^ 24) := by omega
        rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt (by omega)]
        rfl
      rw [if_pos h25, hl, hinit]
      simp only [↓reduceIte]
      unfold Completeness.maskTable
      have hidx : Completeness.idx (Completeness.bitsOf (22 + 2) i) = i - 2 ^ 24 := by
        rw [idx_bitsOf_mod]
        omega
      by_cases h16 : i - 2 ^ 24 < 16
      · rw [PcsQuotient.maskEntries, getD_ofFn _ _ h16]
        simp only
        by_cases h12 : i - 2 ^ 24 < 12
        · rw [dif_pos (by rw [hidx]; exact h12), if_pos (by omega)]
          refine congrArg₂ masks (Fin.ext ?_) (Fin.ext ?_)
          · simp only [Fin.val_ofNat, hidx, Nat.mod_mod]
          · simp only [Fin.val_ofNat, hidx]
            exact Nat.mod_eq_of_lt (by omega)
        · rw [dif_neg (by rw [hidx]; exact h12), if_neg (by omega)]
      · rw [getD_of_size_le _ _ (by omega), dif_neg (by rw [hidx]; omega)]
    · rw [if_neg h25, getD_of_size_le _ _ (by rw [hmsize]; omega)]

/-! ## The wiring table -/

/-- **The wiring table**: `proveSpec`'s wiring table (`circuit.wiringTable`,
`coefficients 24 0 (sigma.map point)`) is `formal/Completeness`'s `wiringTableK` of the deployed
σ, entry by entry, for a `sigma` whose entry `b` is the point of the deployed σ of `b`. -/
theorem wiring_table (hK : Constants) (sigma : Array ℕ) (hss : sigma.size = 2 ^ 24)
    (hsigma : ∀ b, point (sigma.getD (Completeness.idx b) 0) =
      deployedBasis.point (deployedSigma b)) :
    (coefficients 24 0 (sigma.map point)).size = 2 ^ 24 ∧
      ∀ i, (coefficients 24 0 (sigma.map point)).getD i 0 =
        Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma) i := by
  have hs : (sigma.map point).size = 2 ^ 24 := by rw [Array.size_map, hss]
  refine ⟨by rw [Bridge.Ntt.coefficients_size, hs], fun i => ?_⟩
  refine getD_eq_natTable (m := 22 + 2) _ (by rw [Bridge.Ntt.coefficients_size, hs]) _ (fun b => ?_) i
  refine coefficients_eq_tableOf hK _ hs _ (fun x => ?_) b
  rw [← hsigma x, ← getD_map point sigma 0 (Completeness.idx x), point_zero]

end ProverTables

end E2ECompleteness

/-- info: 'E2ECompleteness.ProverTables.witness_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.ProverTables.witness_table

/-- info: 'E2ECompleteness.ProverTables.wiring_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.ProverTables.wiring_table

/-- info: 'E2ECompleteness.ProverTables.tablePoly_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.ProverTables.tablePoly_injective
