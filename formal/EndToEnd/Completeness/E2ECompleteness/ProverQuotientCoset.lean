-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The quotient table's computations on the coset (`ProverDefs.lean`'s `blocksOf`, `rowPolyOf`)
-- against `formal/QuotientSecurity`'s polynomials. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the fields `K`, `E`.
import E2ECompleteness.ProverTables

/-!
# The prover's coset: points, the public weights, the rows

The quotients are computed pointwise on the coset `β₂₆ + span(β₀ … β₂₅)` (`2^26` points, four
times the cells), in blocks of `2^11` points (`blocksOf`). Here, for the Statement's constants
(`Constants`):

* the transform over `E` (`values_getD_tablePoly_E`, `tablePoly_coefficients_E`), and two
  polynomials of degree below `2^26` agreeing on the coset are equal (`coset_ext_E`, `coset_ext_K`);
* on a block, the digits `w_k` of a point are the block's `wAt k` plus those of its offset in the
  block (`iterate_coset`);
* **`pub_coset`**: a block's weights (`blocksOf`'s first component) are F1's public weight `pub γ`
  at the block's points (through `Compose.Reduce.publicWeight`, `matches_deployed`; the Statement's
  `coordinates(11)` read the region's coordinates, `CoordinatesRead 11`);
* **`rowInv_coset`**, **`ofK_rowPolyOf`**: a block's row inverses are `1 / Z_rows` at its points;
  `Z_rows` and `Z_cells` do not vanish on the coset (`vRows_coset_ne_zero`, `vCells_coset_ne_zero`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness

namespace ProverQuotient

open ProverTables

/-! ## The transform over `E` -/

/-- **Entry `p < 2^m` of `values` over `E` is the table's polynomial at `offset + B(p)`.** -/
theorem values_getD_tablePoly_E {m : ℕ} (hB : Bridge.Ntt.CantorUpTo m) (hm : m ≤ basisSize)
    (offset : K) (c : Array E) (hc : c.size = 2 ^ m) {p : ℕ} (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 =
      (tablePoly (fun b : Fin m → Bool ↦ c.getD (Completeness.idx b) 0)).eval
        (ofK (offset + point p)) := by
  rw [Bridge.Ntt.values_getD_E hB hm offset c hc hp, tablePoly_eval, digitsEval, sum_range_cube]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Bridge.Ntt.X_idx, mul_comm, ofK_eq, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · rw [← ofK_eq, sq_iterate_ofK]
    rfl
  · exact map_one _

/-- **`coefficients` over `E` gives the table of the values.** -/
theorem tablePoly_coefficients_E {m : ℕ} (hB : Bridge.Ntt.CantorUpTo m) (hm : m ≤ basisSize)
    (offset : K) (v : Array E) (hv : v.size = 2 ^ m) {p : ℕ} (hp : p < 2 ^ m) :
    (tablePoly (fun b : Fin m → Bool ↦ (coefficients m offset v).getD (Completeness.idx b) 0)).eval
        (ofK (offset + point p)) = v.getD p 0 := by
  rw [← values_getD_tablePoly_E hB hm offset _ (by rw [Bridge.Ntt.coefficients_size, hv]) hp,
    Bridge.Ntt.values_coefficients_E m offset v hv]

theorem ofK_sum (s : Finset ℕ) (f : ℕ → K) : ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s

theorem ofK_prod (s : Finset ℕ) (f : ℕ → K) : ofK (∏ i ∈ s, f i) = ∏ i ∈ s, ofK (f i) :=
  map_prod (algebraMap K E) f s

/-! ## The coset -/

section Coset

variable (hK : Constants)

theorem cantorUpTo28 (hK : Constants) : Bridge.Ntt.CantorUpTo basisSize :=
  Bridge.Ntt.cantorUpTo_of_isCantorBasis hK.cantor le_rfl

theorem S_iterate_add (k : ℕ) (x y : K) : S^[k] (x + y) = S^[k] x + S^[k] y := by
  rw [Bridge.Ntt.S_eq_sq]
  exact sq_iterate_add k x y

theorem point_two_pow {n : ℕ} (hn : n < basisSize) : point (2 ^ n) = betaAt n := by
  rw [Bridge.Ntt.point_eq_sum, Finset.sum_eq_single n (fun t _ ht => by
      rw [Nat.testBit_two_pow]
      simp [Ne.symm ht]) (fun h => absurd (mem_range.mpr hn) h), Nat.testBit_two_pow_self]
  rfl

/-- A point of the coset is the point of `2^26 + p`. -/
theorem coset_point {p : ℕ} (hp : p < 2 ^ 26) : betaAt 26 + point p = point (2 ^ 26 + p) := by
  have h := point_add_of_lt 26 1 p hp
  rw [mul_one] at h
  rw [h, point_two_pow (by unfold basisSize; norm_num)]

include hK in
/-- **Distinct numbers below `2^28` are distinct points.** -/
theorem point_inj {a b : ℕ} (ha : a < 2 ^ basisSize) (hb : b < 2 ^ basisSize)
    (h : point a = point b) : a = b := by
  have hC := cantorUpTo28 hK
  rw [Bridge.Ntt.point_eq_cantor hC le_rfl ha, Bridge.Ntt.point_eq_cantor hC le_rfl hb] at h
  have e := congrArg Completeness.idx ((Bridge.Ntt.cantorOf hC).point_injective le_rfl h)
  rwa [Completeness.idx_bitsOf _ _ ha, Completeness.idx_bitsOf _ _ hb] at e

include hK in
/-- The coset's points are distinct, for any offset `c` that is the point `β₂₆` (abstracted, so that
no unification ever unfolds `betaAt`). -/
theorem coset_injective (c : K) (hc : ∀ p < 2 ^ 26, c + point p = point (2 ^ 26 + p)) :
    Function.Injective fun p : Fin (2 ^ 26) => c + point p := by
  intro a b h
  have h' : c + point a = c + point b := h
  rw [hc a a.isLt, hc b b.isLt] at h'
  have := point_inj hK (by unfold basisSize; omega) (by unfold basisSize; omega) h'
  exact Fin.ext (by omega)

include hK in
/-- **Two polynomials over `E` of degree below `2^26` agreeing on the coset are equal.** -/
theorem coset_ext_E' (c : K) (hc : ∀ p < 2 ^ 26, c + point p = point (2 ^ 26 + p))
    {P1 P2 : E[X]} (h1 : P1.natDegree < 2 ^ 26) (h2 : P2.natDegree < 2 ^ 26)
    (h : ∀ p < 2 ^ 26, P1.eval (ofK (c + point p)) = P2.eval (ofK (c + point p))) :
    P1 = P2 := by
  have hinj : Function.Injective fun p : Fin (2 ^ 26) => ofK (c + point p) := by
    intro a b hab
    have hab' : ofK (c + point a) = ofK (c + point b) := hab
    exact coset_injective hK c hc (ofK_injective hab')
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P1 - P2) hinj (fun p => ?_) ?_
  · show (P1 - P2).eval (ofK (c + point p)) = 0
    rw [Polynomial.eval_sub, h p p.isLt, sub_self]
  · rw [Fintype.card_fin]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt h1 h2)

include hK in
/-- **Two polynomials over `K` of degree below `2^26` agreeing on the coset are equal.** -/
theorem coset_ext_K' (c : K) (hc : ∀ p < 2 ^ 26, c + point p = point (2 ^ 26 + p))
    {P1 P2 : K[X]} (h1 : P1.natDegree < 2 ^ 26) (h2 : P2.natDegree < 2 ^ 26)
    (h : ∀ p < 2 ^ 26, P1.eval (c + point p) = P2.eval (c + point p)) :
    P1 = P2 := by
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P1 - P2) (coset_injective hK c hc)
    (fun p => ?_) ?_
  · show (P1 - P2).eval (c + point p) = 0
    rw [Polynomial.eval_sub, h p p.isLt, sub_self]
  · rw [Fintype.card_fin]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt h1 h2)

include hK in
theorem coset_ext_E {P1 P2 : E[X]} (h1 : P1.natDegree < 2 ^ 26) (h2 : P2.natDegree < 2 ^ 26)
    (h : ∀ p < 2 ^ 26, P1.eval (ofK (betaAt 26 + point p)) = P2.eval (ofK (betaAt 26 + point p))) :
    P1 = P2 :=
  coset_ext_E' hK (betaAt 26) (fun _ hp => coset_point hp) h1 h2 h

include hK in
theorem coset_ext_K {P1 P2 : K[X]} (h1 : P1.natDegree < 2 ^ 26) (h2 : P2.natDegree < 2 ^ 26)
    (h : ∀ p < 2 ^ 26, P1.eval (betaAt 26 + point p) = P2.eval (betaAt 26 + point p)) :
    P1 = P2 :=
  coset_ext_K' hK (betaAt 26) (fun _ hp => coset_point hp) h1 h2 h

include hK in
theorem iterate_point28 {n k : ℕ} (hn : n < 2 ^ basisSize) (hk : k ≤ basisSize) :
    S^[k] (point n) = point (n / 2 ^ k) :=
  Bridge.Ntt.iterate_point (cantorUpTo28 hK) le_rfl hn hk

end Coset

/-! ## The blocks of `blocksOf` -/

/-- `wAt k` of block `hi` (`blocksOf`): `w_k(β₂₆) + B(base >>> k)`, `base = hi · 2^11`. -/
def wAtB (hi k : ℕ) : K :=
  (chain (betaAt (PcsQuotient.cellVars 22 + 2)) (PcsQuotient.cellVars 22 + 1)).getD k 0 +
    point ((hi * 2 ^ PcsQuotient.region) >>> k)

/-- The region's selector of block `hi`: `∏_{11 ≤ k < 24} (1 + wAt k)`. -/
def indicatorB (hi : ℕ) : K :=
  (List.range' PcsQuotient.region (PcsQuotient.cellVars 22 - PcsQuotient.region)).foldl
    (fun acc k ↦ acc * (1 + wAtB hi k)) 1

/-- Coordinate `k` of block `hi`'s base point. -/
def shiftB (hi k : ℕ) : K :=
  (List.range' k (PcsQuotient.region - k)).foldl
    (fun acc j ↦ acc + (coordinates PcsQuotient.region).getD (j - k) 0 * wAtB hi j) 0

/-- `1 + μ_k` (`blocksOf`'s `slope`). -/
def slopeB (γ : E) (k : ℕ) : E :=
  1 + (PcsQuotient.coordinateWeight k).getD ([γ, γ * γ, (γ * γ) * (γ * γ)].getD (k - 8) 0)

/-- Block `hi`'s weights. -/
def weightsB (γ : E) (hi : ℕ) : Array E :=
  if indicatorB hi = 0 then #[ofK (indicatorB hi)]
  else (List.range PcsQuotient.region).foldl
    (fun ws k ↦ ws.map (· * (1 + slopeB γ k * ofK (shiftB hi k))) ++
      ws.map (· * ((1 + slopeB γ k * ofK (shiftB hi k)) + slopeB γ k)))
    #[ofK (indicatorB hi)]

/-- Block `hi`'s row inverses. -/
def rowInvB (hi : ℕ) : Array K :=
  Array.ofFn (n := 4) fun r ↦ (rowPolyOf 22 (betaAt (PcsQuotient.cellVars 22 + 2) +
    point (hi * 2 ^ PcsQuotient.region)) + rowPolyOf 22 (point r.val))⁻¹

/-- **Block `hi` of `blocksOf`.** -/
theorem blocksOf_getD (γ : E) {hi : ℕ} (h : hi < 2 ^ 15) :
    (blocksOf 22 γ).getD hi (#[], 0, #[]) =
      (weightsB γ hi, (wAtB hi (PcsQuotient.cellVars 22))⁻¹, rowInvB hi) := by
  rw [blocksOf, getD_ofFn _ _ (by unfold PcsQuotient.cellVars PcsQuotient.region; norm_num; omega)]
  rfl

section Blocks

variable (hK : Constants)

include hK in
/-- **On a block, `w_k` of a point is the block's `wAt k` plus `w_k` of its offset.** -/
theorem iterate_coset {p k : ℕ} (hp : p < 2 ^ 26) (hk : k < 25) :
    S^[k] (betaAt 26 + point p) = wAtB (p / 2 ^ 11) k + S^[k] (point (p % 2 ^ 11)) := by
  have hdec : p = 2 ^ 11 * (p / 2 ^ 11) + p % 2 ^ 11 := (Nat.div_add_mod p _).symm
  have hlt : 2 ^ 11 * (p / 2 ^ 11) < 2 ^ basisSize := by unfold basisSize; omega
  rw [S_iterate_add, hdec, point_add_of_lt 11 _ _ (Nat.mod_lt _ (by norm_num)), S_iterate_add,
    ← hdec, iterate_point28 hK hlt (by unfold basisSize; omega), ← add_assoc]
  refine congrArg (· + S^[k] (point (p % 2 ^ 11))) ?_
  unfold wAtB
  rw [show PcsQuotient.cellVars 22 + 2 = 26 from rfl, show PcsQuotient.region = 11 from rfl,
    Bridge.Ntt.chain_getD _ (by exact hk), Nat.shiftRight_eq_div_pow, mul_comm (p / 2 ^ 11)]

include hK in
theorem iterate_offset_high {r k : ℕ} (hr : r < 2 ^ 11) (hk : 11 ≤ k) (hk' : k ≤ basisSize) :
    S^[k] (point r) = 0 := by
  rw [iterate_point28 hK (by unfold basisSize; omega) hk',
    Nat.div_eq_of_lt (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hk)), point_zero]

theorem S_iterate_sum (s : Finset ℕ) (f : ℕ → K) (n : ℕ) :
    S^[n] (∑ i ∈ s, f i) = ∑ i ∈ s, S^[n] (f i) := by
  rw [Bridge.Ntt.S_eq_sq]
  exact sq_iterate_sum s f n

theorem S_iterate_zero (n : ℕ) : S^[n] (0 : K) = 0 := by
  rw [Bridge.Ntt.S_eq_sq]
  exact sq_iterate_zero n

end Blocks

/-! ## The region's coordinates -/

/-- One step of `coordinates`. -/
def coordStep (b : Array K) (d : ℕ) : Array K :=
  if d = 0 then b.push 1
  else b.push ((List.range d).foldl (fun acc e ↦ acc + betaAt (e + 1) * b.getD (d - 1 - e) 0) 0)

theorem getD_push_lt {α : Type*} (a : Array α) (x d : α) {i : ℕ} (hi : i < a.size) :
    (a.push x).getD i d = a.getD i d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hi.ne, hi]

theorem getD_push_eq {α : Type*} (a : Array α) (x d : α) {i : ℕ} (hi : i = a.size) :
    (a.push x).getD i d = x := by
  subst hi
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push]

theorem coordStep_fold : ∀ n : ℕ, ((List.range n).foldl coordStep #[]).size = n ∧
    ∀ d < n, ((List.range n).foldl coordStep #[]).getD d 0 = Compose.Reduce.coordinates betaAt d
  | 0 => ⟨rfl, fun d hd => absurd hd (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hs, hk⟩ := coordStep_fold n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl coordStep #[] = A at hs hk
    have hsz : (coordStep A n).size = n + 1 := by
      unfold coordStep
      split_ifs <;> simp [hs]
    refine ⟨hsz, fun d hd => ?_⟩
    by_cases hdn : d < n
    · unfold coordStep
      split_ifs <;> rw [getD_push_lt _ _ _ (by omega), hk d hdn]
    · have hd' : d = n := by omega
      subst hd'
      unfold coordStep
      split_ifs with h0
      · rw [getD_push_eq _ _ _ hs.symm, h0, Compose.Reduce.coordinates_zero]
      · obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
        rw [getD_push_eq _ _ _ hs.symm, List.range_eq_range', Compose.Reduce.foldl_range'_add,
          zero_add, Compose.Reduce.coordinates,
          Fin.sum_univ_eq_sum_range
            (fun e => betaAt (e + 1) * Compose.Reduce.coordinates betaAt (m - e)) (m + 1)]
        refine Finset.sum_congr rfl fun e he => ?_
        have he' := mem_range.mp he
        rw [zero_add, hk _ (by omega), show m + 1 - 1 - e = m - e by omega]

/-- **The Statement's `coordinates(n)` are `Compose`'s** (`domain::coordinates`, both). -/
theorem coordinates_getD {n d : ℕ} (hd : d < n) :
    (coordinates n).getD d 0 = Compose.Reduce.coordinates betaAt d := by
  have e : coordinates n = ((List.range n).foldl coordStep #[]).toList := rfl
  rw [e, List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]
  exact (coordStep_fold n).2 d hd

theorem coordinates_getD_zero : (coordinates 11).getD 0 0 = 1 := by
  rw [coordinates_getD (by norm_num), Compose.Reduce.coordinates_zero]

/-- `coordinateOf` as a sum. -/
theorem coordinateOf_eq {k : ℕ} (hk : k < 11) (x : K) :
    coordinateOf 11 k x = ∑ i ∈ range (11 - k), (coordinates 11).getD i 0 * S^[k + i] x := by
  unfold coordinateOf
  rw [Compose.Reduce.foldl_range'_add, zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.add_sub_cancel_left, Bridge.Ntt.chain_getD _ (by have := mem_range.mp hi; omega)]

theorem coordinateOf_sum {k : ℕ} (hk : k < 11) (s : Finset ℕ) (f : ℕ → K) :
    coordinateOf 11 k (∑ t ∈ s, f t) = ∑ t ∈ s, coordinateOf 11 k (f t) := by
  simp only [coordinateOf_eq hk, S_iterate_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem coordinateOf_zero {k : ℕ} (hk : k < 11) : coordinateOf 11 k 0 = 0 := by
  simp [coordinateOf_eq hk, S_iterate_zero]

/-- **Coordinate `k` of a point of the region is its bit `k`** (`CoordinatesRead 11`). -/
theorem coordinateOf_point (hK : Constants) {r k : ℕ} (hr : r < 2 ^ 11) (hk : k < 11) :
    coordinateOf 11 k (point r) = if r.testBit k then 1 else 0 := by
  rw [Bridge.Ntt.point_eq_sum_of_lt (N := 11) (by unfold basisSize; omega) hr, coordinateOf_sum hk,
    Finset.sum_eq_single k (fun t ht htk => ?_) (fun h => absurd (mem_range.mpr hk) h)]
  · split_ifs with hb
    · have := hK.coords ⟨k, hk⟩ ⟨k, hk⟩
      simpa using this
    · exact coordinateOf_zero hk
  · split_ifs with hb
    · have := hK.coords ⟨k, hk⟩ ⟨t, mem_range.mp ht⟩
      rw [this, ite_eq_right_iff]
      intro h
      exact absurd (congrArg Fin.val h) htk
    · exact coordinateOf_zero hk

/-- A block's coordinate `k` as a sum. -/
theorem shiftB_eq (hi : ℕ) {k : ℕ} (hk : k < 11) :
    shiftB hi k = ∑ i ∈ range (11 - k), (coordinates 11).getD i 0 * wAtB hi (k + i) := by
  unfold shiftB
  rw [show PcsQuotient.region = 11 from rfl, Compose.Reduce.foldl_range'_add, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_cancel_left]

/-- **`reduce`'s coordinate `k` at a point of `K`**, as the Statement's constants read it. -/
theorem coordinate_eq_sum {k : ℕ} (hk : k < 11) (y : K) :
    Compose.Reduce.coordinate stmtConsts (ofK y) k =
      ofK (∑ i ∈ range (11 - k), (coordinates 11).getD i 0 * S^[k + i] y) := by
  unfold Compose.Reduce.coordinate
  rw [Compose.Reduce.foldRange_add, show 11 - k = (10 - k) + 1 by omega, Finset.sum_range_succ',
    coordinates_getD_zero, one_mul, add_zero, Compose.Reduce.ofK_add, ofK_sum,
    Finset.sum_Ico_eq_sum_range, Compose.Reduce.wChain_eq, sq_iterate_ofK,
    show Compose.Reduce.region - (k + 1) = 10 - k by unfold Compose.Reduce.region; omega,
    add_comm (ofK (S^[k] y))]
  refine congrArg (fun z => z + ofK (S^[k] y)) (Finset.sum_congr rfl fun i hi => ?_)
  have hi' := mem_range.mp hi
  rw [Compose.Reduce.wChain_eq, sq_iterate_ofK, Compose.Reduce.ofK_mul,
    show k + 1 + i - k = i + 1 by omega, show k + (i + 1) = k + 1 + i by omega,
    coordinates_getD (n := 11) (by omega)]
  rfl

theorem bitWeight_eq' (j : ℕ) : PcsQuotient.bitWeight j = Compose.Reduce.bitWeight j := by
  unfold PcsQuotient.bitWeight Compose.Reduce.bitWeight
  simp only [Nat.shiftLeft_eq, one_mul]

theorem coordinateWeight_eq' (k : ℕ) :
    PcsQuotient.coordinateWeight k = Compose.Reduce.coordinateWeight k := by
  unfold PcsQuotient.coordinateWeight Compose.Reduce.coordinateWeight
  simp only [bitWeight_eq', Nat.shiftLeft_eq, one_mul]

/-- `blocksOf`'s slope is `reduce`'s. -/
theorem slope_eq' (γ : E) (k : ℕ) : Compose.Reduce.slope γ k = slopeB γ k := by
  unfold Compose.Reduce.slope slopeB
  rw [coordinateWeight_eq']
  cases Compose.Reduce.coordinateWeight k <;> rfl

/-! ## The weights -/

theorem getD_map_lt {α β : Type*} (A : Array α) (f : α → β) (d : α) (d' : β) {r : ℕ}
    (hr : r < A.size) : (A.map f).getD r d' = f (A.getD r d) := by
  simp [Array.getD_eq_getD_getElem?, hr]

theorem getD_append_left' {α : Type*} (A B : Array α) (d : α) {r : ℕ} (hr : r < A.size) :
    (A ++ B).getD r d = A.getD r d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hr]

theorem getD_append_right' {α : Type*} (A B : Array α) (d : α) {r : ℕ} (hr : A.size ≤ r) :
    (A ++ B).getD r d = B.getD (r - A.size) d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right hr]

/-- **The weights' fold**: entry `r` is `a` times, for each `k`, `hi' k` or `lo k` by bit `k`. -/
theorem fold_weights (lo hi' : ℕ → E) (a : E) : ∀ n : ℕ,
    ((List.range n).foldl (fun ws k ↦ ws.map (· * lo k) ++ ws.map (· * hi' k)) #[a]).size =
        2 ^ n ∧
    ∀ r < 2 ^ n, ((List.range n).foldl (fun ws k ↦ ws.map (· * lo k) ++ ws.map (· * hi' k))
        #[a]).getD r 0 = a * ∏ k ∈ range n, (if r.testBit k then hi' k else lo k)
  | 0 => ⟨rfl, fun r hr => by
      have : r = 0 := by simpa using hr
      subst this
      simp⟩
  | n + 1 => by
    obtain ⟨hs, hg⟩ := fold_weights lo hi' a n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun ws k ↦ ws.map (· * lo k) ++ ws.map (· * hi' k)) #[a] = A
      at hs hg
    refine ⟨by simp [hs, pow_succ, mul_two], fun r hr => ?_⟩
    rw [prod_range_succ]
    by_cases hrn : r < 2 ^ n
    · have hb : r.testBit n = false := Nat.testBit_eq_false_of_lt hrn
      rw [getD_append_left' _ _ _ (by simp [hs, hrn]), getD_map_lt A _ 0 0 (by rw [hs]; exact hrn),
        hg r hrn, hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring
    · have hr' : r - 2 ^ n < 2 ^ n := by rw [pow_succ] at hr; omega
      have hrr : r = 2 ^ n + (r - 2 ^ n) := by omega
      have hb : r.testBit n = true := by
        rw [hrr, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hr']
        rfl
      rw [getD_append_right' _ _ _ (by simp [hs]; omega), Array.size_map, hs,
        getD_map_lt A _ 0 0 (by rw [hs]; exact hr'), hg _ hr', hb]
      simp only [↓reduceIte]
      rw [mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' := mem_range.mp hk
      rw [hrr, Nat.testBit_two_pow_add_gt hk', Nat.add_sub_cancel_left]

section Pub

variable (hK : Constants)

include hK in
/-- **F1's public weight on a block's point**: the block's selector times one factor per coordinate
of the region, the block's coordinate plus the point's bit. -/
theorem pub_coset_eq (γ : E) {p : ℕ} (hp : p < 2 ^ 26) :
    (Completeness.deployedInstanceE.params.pub γ).eval (ofK (betaAt 26 + point p)) =
      ofK (indicatorB (p / 2 ^ 11)) * ∏ k ∈ range 11,
        (1 + (ofK (shiftB (p / 2 ^ 11) k) + if (p % 2 ^ 11).testBit k then 1 else 0) *
          slopeB γ k) := by
  have hr : p % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  rw [(matches_deployed hK).pub, Compose.Reduce.publicWeight, Compose.Reduce.foldRange_mul,
    Compose.Reduce.foldRange_mul, one_mul]
  refine congrArg₂ (· * ·) ?_ ?_
  · unfold indicatorB
    rw [Compose.Reduce.foldl_range'_mul, one_mul, ofK_prod, Finset.prod_Ico_eq_prod_range,
      show PcsQuotient.region = 11 from rfl, show PcsQuotient.cellVars 22 - 11 = 13 from rfl,
      show 22 + 2 - Compose.Reduce.region = 13 by unfold Compose.Reduce.region; omega]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    rw [Compose.Reduce.wChain_eq, sq_iterate_ofK, show Compose.Reduce.region = 11 from rfl,
      iterate_coset hK hp (by omega), iterate_offset_high hK hr (by omega)
        (by unfold basisSize; omega), add_zero, Compose.Reduce.ofK_add, Compose.Reduce.ofK_one]
  · rw [show Compose.Reduce.region = 11 from rfl, ← Finset.range_eq_Ico]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    rw [coordinate_eq_sum hk', slope_eq']
    refine congrArg (fun z => 1 + z * slopeB γ k) ?_
    have e : ∑ i ∈ range (11 - k), (coordinates 11).getD i 0 * S^[k + i] (betaAt 26 + point p) =
        shiftB (p / 2 ^ 11) k + coordinateOf 11 k (point (p % 2 ^ 11)) := by
      rw [shiftB_eq _ hk', coordinateOf_eq hk', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [iterate_coset hK hp (by have := mem_range.mp hi; omega), mul_add]
    rw [e, coordinateOf_point hK hr hk', Compose.Reduce.ofK_add]
    split_ifs
    · rw [Compose.Reduce.ofK_one]
    · rw [Compose.Reduce.ofK_zero]

include hK in
/-- **A block's weights are F1's public weight** at its points (`qValuesOf`'s `pub`). -/
theorem pub_coset (γ : E) {p : ℕ} (hp : p < 2 ^ 26) (w : E) :
    (if p % 2 ^ PcsQuotient.region < (weightsB γ (p / 2 ^ PcsQuotient.region)).size then
        (weightsB γ (p / 2 ^ PcsQuotient.region)).getD (p % 2 ^ PcsQuotient.region) 0 * w
      else 0) =
      (Completeness.deployedInstanceE.params.pub γ).eval (ofK (betaAt 26 + point p)) * w := by
  rw [show PcsQuotient.region = 11 from rfl, pub_coset_eq hK γ hp]
  have hr : p % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  unfold weightsB
  by_cases hind : indicatorB (p / 2 ^ 11) = 0
  · rw [if_pos hind, hind, Compose.Reduce.ofK_zero, zero_mul, zero_mul]
    have h0 : ∀ r : ℕ, (#[(0 : E)]).getD r 0 = 0 := fun r => by
      rcases r with _ | r <;> simp [Array.getD_eq_getD_getElem?]
    rw [h0, zero_mul, ite_self]
  · rw [if_neg hind]
    obtain ⟨hs, hg⟩ := fold_weights (fun k => 1 + slopeB γ k * ofK (shiftB (p / 2 ^ 11) k))
      (fun k => (1 + slopeB γ k * ofK (shiftB (p / 2 ^ 11) k)) + slopeB γ k)
      (ofK (indicatorB (p / 2 ^ 11))) 11
    beta_reduce at hs hg
    rw [show PcsQuotient.region = 11 from rfl]
    rw [if_pos (by rw [hs]; exact hr), hg _ hr]
    have hprod : ∏ k ∈ range 11, (if (p % 2 ^ 11).testBit k then
          (1 + slopeB γ k * ofK (shiftB (p / 2 ^ 11) k)) + slopeB γ k
        else 1 + slopeB γ k * ofK (shiftB (p / 2 ^ 11) k)) =
        ∏ k ∈ range 11, (1 + (ofK (shiftB (p / 2 ^ 11) k) +
          if (p % 2 ^ 11).testBit k then 1 else 0) * slopeB γ k) :=
      Finset.prod_congr rfl fun k _ => by split_ifs <;> ring
    rw [hprod]

end Pub

/-! ## The rows -/

theorem rowPolyOf_eq (x : K) :
    rowPolyOf 22 x = ∑ k ∈ range (22 + 1), (rowVanishing (22 + 2)).getD k 0 * S^[k] x := by
  show rowPolyAt (22 + 2) x = _
  rw [rowPolyAt_eq_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Bridge.Ntt.chain_getD _ (by have := mem_range.mp hk; omega)]

theorem rowPolyOf_add (a b : K) : rowPolyOf 22 (a + b) = rowPolyOf 22 a + rowPolyOf 22 b := by
  simp only [rowPolyOf_eq, S_iterate_add, mul_add, Finset.sum_add_distrib]

/-- **The rows' polynomial is `Z_rows`.** -/
theorem ofK_rowPolyOf (hK : Constants) (y : K) :
    ofK (rowPolyOf 22 y) = Completeness.deployedInstanceE.params.vRows.eval (ofK y) := by
  rw [(matches_deployed hK).rows, Compose.Reduce.rows, Compose.Reduce.foldRange_add, zero_add,
    rowPolyOf_eq, ofK_eq, map_sum, ← Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Compose.Reduce.wChain_eq, map_mul, ← ofK_eq, ← ofK_eq, sq_iterate_ofK]
  rfl

theorem idx_cellBits0 {n : ℕ} (y : Fin n → Bool) :
    Completeness.idx (cellBits (y, 0) : Fin (n + 1 + 1) → Bool) = 4 * Completeness.idx y := by
  show Completeness.idx (Fin.cons false (Fin.cons false y) : Fin (n + 1 + 1) → Bool) = _
  rw [Completeness.idx_cons, Completeness.idx_cons]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  ring

/-- The `X` cells' points in `E`. -/
theorem basis_point_cellBits0 (hK : Constants) (y : Fin 22 → Bool) :
    Completeness.deployedInstanceE.basis.point (cellBits (y, 0)) =
      ofK (point (4 * Completeness.idx y)) := by
  rw [Completeness.point_map (algebraMap K E) deployedBasis _ (fun _ => rfl), ← point_idx hK,
    idx_cellBits0]
  rfl

theorem rowPolyOf_four_mul (hK : Constants) {q : ℕ} (hq : q < 2 ^ 22) :
    rowPolyOf 22 (point (4 * q)) = 0 := by
  apply ofK_injective
  rw [ofK_rowPolyOf hK]
  have hmem : ofK (point (4 * q)) ∈ Completeness.deployedInstanceE.params.T := by
    show ofK (point (4 * q)) ∈ cantorT Completeness.deployedInstanceE.basis 22
    refine Finset.mem_image.mpr ⟨Completeness.bitsOf 22 q, Finset.mem_univ _, ?_⟩
    rw [basis_point_cellBits0 hK, Completeness.idx_bitsOf _ _ hq]
  rw [Completeness.deployedInstanceE.params.hRows _ hmem]
  exact Compose.Reduce.ofK_zero.symm

/-- **A block's row inverses** are `1 / rows` at its points. -/
theorem rowInv_coset (hK : Constants) {p : ℕ} (hp : p < 2 ^ 26) :
    (rowInvB (p / 2 ^ PcsQuotient.region)).getD (p % 4) 0 =
      (rowPolyOf 22 (betaAt 26 + point p))⁻¹ := by
  rw [rowInvB, getD_ofFn _ _ (Nat.mod_lt _ (by norm_num))]
  simp only
  rw [show PcsQuotient.cellVars 22 + 2 = 26 from rfl, show PcsQuotient.region = 11 from rfl]
  refine congrArg Inv.inv ?_
  have hr : p % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have e1 : point p =
      point (p / 2 ^ 11 * 2 ^ 11) + point (4 * (p % 2 ^ 11 / 4)) + point (p % 4) := by
    have h1 := point_add_of_lt 11 (p / 2 ^ 11) (p % 2 ^ 11) hr
    have h2 := point_add_of_lt 2 (p % 2 ^ 11 / 4) (p % 2 ^ 11 % 4) (Nat.mod_lt _ (by norm_num))
    have hm : p % 2 ^ 11 % 4 = p % 4 := Nat.mod_mod_of_dvd p (by norm_num)
    rw [hm, show (2 : ℕ) ^ 2 = 4 by norm_num] at h2
    rw [show 4 * (p % 2 ^ 11 / 4) + p % 4 = p % 2 ^ 11 by omega] at h2
    rw [Nat.div_add_mod] at h1
    rw [h1, h2, mul_comm (p / 2 ^ 11), add_assoc]
  have e2 : rowPolyOf 22 (betaAt 26 + point p) = rowPolyOf 22 (betaAt 26 +
      point (p / 2 ^ 11 * 2 ^ 11)) + rowPolyOf 22 (point (4 * (p % 2 ^ 11 / 4))) +
        rowPolyOf 22 (point (p % 4)) := by
    rw [e1, ← add_assoc, ← add_assoc, rowPolyOf_add (betaAt 26 + point (p / 2 ^ 11 * 2 ^ 11) +
      point (4 * (p % 2 ^ 11 / 4))) (point (p % 4)),
      rowPolyOf_add (betaAt 26 + point (p / 2 ^ 11 * 2 ^ 11)) (point (4 * (p % 2 ^ 11 / 4)))]
  rw [e2, rowPolyOf_four_mul hK (by omega), add_zero]

/-- **`Z_rows` does not vanish on the coset**: its roots are the `X` cells, in the span of the
first `24` vectors, and `β₂₆` is not. -/
theorem vRows_coset_ne_zero (hK : Constants) {p : ℕ} (hp : p < 2 ^ 26) :
    Completeness.deployedInstanceE.params.vRows.eval (ofK (betaAt 26 + point p)) ≠ 0 := by
  rw [Completeness.deployedInstanceE.exact.rows, eval_prod, Finset.prod_ne_zero_iff]
  intro x _
  rw [Polynomial.eval_sub, eval_X, eval_C, sub_ne_zero]
  intro hx
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp x.2
  rw [← hy, basis_point_cellBits0 hK] at hx
  have h' : betaAt 26 + point p = point (4 * Completeness.idx y) := ofK_injective hx
  rw [coset_point hp] at h'
  have hy' := Completeness.idx_lt y
  have := point_inj hK (by unfold basisSize; omega) (by unfold basisSize; omega) h'
  omega

/-- **`Z_cells` on the coset is the block's `wAt 24`.** -/
theorem vCells_coset (hK : Constants) {p : ℕ} (hp : p < 2 ^ 26) :
    Completeness.deployedInstanceE.params.vCells.eval (ofK (betaAt 26 + point p)) =
      ofK (wAtB (p / 2 ^ PcsQuotient.region) (PcsQuotient.cellVars 22)) := by
  rw [(matches_deployed hK).vCells, digitPoly_eval, sq_iterate_ofK,
    iterate_coset hK hp (by norm_num), iterate_offset_high hK (Nat.mod_lt _ (by norm_num))
      (by norm_num) (by unfold basisSize; norm_num), add_zero]
  rfl

/-- **`Z_cells` does not vanish on the coset.** -/
theorem vCells_coset_ne_zero (hK : Constants) {p : ℕ} (hp : p < 2 ^ 26) :
    Completeness.deployedInstanceE.params.vCells.eval (ofK (betaAt 26 + point p)) ≠ 0 := by
  rw [(matches_deployed hK).vCells, digitPoly_eval, sq_iterate_ofK, coset_point hp,
    iterate_point28 hK (by unfold basisSize; omega) (by unfold basisSize; norm_num)]
  intro h
  have h0 : point ((2 ^ 26 + p) / 2 ^ (22 + 2)) = point 0 := by
    rw [point_zero]
    exact ofK_injective (h.trans Compose.Reduce.ofK_zero.symm)
  have := point_inj hK (by unfold basisSize; omega) (by unfold basisSize; norm_num) h0
  omega

end ProverQuotient

end E2ECompleteness
