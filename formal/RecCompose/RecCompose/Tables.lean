-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The tables' polynomials are `crates/leanvm_rec/src/pi2/
-- prover.rs`'s (`W` committed in the basis `B`, `Q`'s `h`, `q` in the novel basis, the setup's `κ`, `κ + σ` in the basis
-- `B`), read through `formal/Statement`'s public layouts (`PcsQuotient.Layout.ofChunks`, `readEntry`); the novel basis
-- and its sums are `formal/UniComplete`'s (`AlgC.novP`) and `formal/QuotientSecurity`'s (`tablePoly`).
import RecCompose.Layers
import UniComplete.AlgCBasis
import UniSound.Ids.Cantor

/-!
# π2's tables' layer

`Pi2Tables D C` (`Layers.lean`) from the stacks: what each candidate stands for, and π2's four claims on the candidates
as the model's values.

* **`W`** (`m` variables, the basis `B`): its table `T` (the stack read under `W`'s layout) is the witness's column in the
  basis `B`; its polynomial is `w(x) = Σ_i T_i Π_l (s^l(x) if i_l else 1 + s^l(x))` (`wPoly`, degree below `2^m`), which
  takes the witness's values on `V_m` (`wPoly_eval_pointE`: `s^l(ω_x) = ω_{x >> l}`, so it is `basisValue`). Its
  **true fold values** at `t` are the table's partial evaluation at the high digits `w_r(t), …, w_{m−1}(t)` (`wFold`);
  the verifier's cells from them are the row's cells `w(t + ω_x)`, `x < 2^r` (`cells_wFold`: `s^l` is additive and
  `ω_{x >> l} = 0` for `l ≥ r`), and `W`'s claim at `(ρ, ρ², …, w_r(t), …)` is their fold at `ρ` (`claim_wFold`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## Products and sums over bits -/

/-- `eqBits` as a product over the point's coordinates. -/
theorem eqBits_foldl (i : ℕ) : ∀ (p : List E) (s : ℕ) (acc : E),
    (p.zipIdx s).foldl (fun w pk ↦ w * if i.testBit pk.2 then pk.1 else 1 + pk.1) acc =
      acc * ∏ k ∈ range p.length, (if i.testBit (s + k) then p.getD k 0 else 1 + p.getD k 0)
  | [], _, acc => by simp
  | q :: p, s, acc => by
    rw [List.zipIdx_cons, List.foldl_cons, eqBits_foldl i p (s + 1), List.length_cons,
      Finset.prod_range_succ' (fun k ↦ if i.testBit (s + k) then (q :: p).getD k 0 else 1 + (q :: p).getD k 0)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [mul_assoc, mul_comm (∏ k ∈ range p.length, _)]
    congr 2
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [show s + 1 + k = s + (k + 1) by ring]

/-- **`eqBits` is a product**: `Π_k (p_k if bit k of i else 1 + p_k)`. -/
theorem eqBits_eq_prod (p : List E) (i : ℕ) :
    PcsQuotient.eqBits p i = ∏ k ∈ range p.length, (if i.testBit k then p.getD k 0 else 1 + p.getD k 0) := by
  unfold PcsQuotient.eqBits
  rw [eqBits_foldl i p 0 1, one_mul]
  simp

/-- Bit `l` of `k + 2^a j`, `k < 2^a`. -/
theorem testBit_add_two_pow_mul {a k : ℕ} (hk : k < 2 ^ a) (j l : ℕ) :
    (k + 2 ^ a * j).testBit l = if l < a then k.testBit l else j.testBit (l - a) := by
  rw [add_comm, Nat.testBit_two_pow_mul_add j hk l]

/-- **A sum over `2^(a+b)` indices, split**: `i = k + 2^a j`. -/
theorem sum_range_two_pow_add {M : Type*} [AddCommMonoid M] (a : ℕ) (f : ℕ → M) : ∀ b : ℕ,
    ∑ i ∈ range (2 ^ (a + b)), f i = ∑ k ∈ range (2 ^ a), ∑ j ∈ range (2 ^ b), f (k + 2 ^ a * j)
  | 0 => by simp
  | b + 1 => by
    rw [show a + (b + 1) = (a + b) + 1 by ring, pow_succ, mul_two, Finset.sum_range_add,
      sum_range_two_pow_add a f b, sum_range_two_pow_add a (fun i ↦ f (2 ^ (a + b) + i)) b, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [pow_succ, mul_two, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    rw [pow_add]
    ring

/-- **`eqBits` of a concatenation**: `eq(p ++ q, k + 2^|p| j) = eq(p, k) eq(q, j)`, `k < 2^|p|`. -/
theorem eqBits_append (p q : List E) {k : ℕ} (hk : k < 2 ^ p.length) (j : ℕ) :
    PcsQuotient.eqBits (p ++ q) (k + 2 ^ p.length * j) = PcsQuotient.eqBits p k * PcsQuotient.eqBits q j := by
  rw [eqBits_eq_prod, eqBits_eq_prod, eqBits_eq_prod, List.length_append, Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.mp hl
    rw [testBit_add_two_pow_mul hk, if_pos hl', List.getD_append _ _ _ _ hl']
  · refine Finset.prod_congr rfl fun l _ ↦ ?_
    have hnl : ¬ p.length + l < p.length := by omega
    have hge : p.length ≤ p.length + l := by omega
    rw [testBit_add_two_pow_mul hk, if_neg hnl, Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ hge,
      Nat.add_sub_cancel_left]

/-! ## The points and the digits -/

/-- π2's points are the verifier's: `ω_i = pointE i`. -/
theorem pi2Omega_eq (i : ℕ) : pi2Omega i = UniStatement.pointE i := UniComplete.Domain.omega_basisE i

/-- `s^l(ω_x) = ω_{x >> l}` (`x < 2^32`). -/
theorem sq_iterate_pi2Omega (l : ℕ) {x : ℕ} (hx : x < 2 ^ 32) :
    QuotientSecurity.sq^[l] (pi2Omega x) = pi2Omega (x >>> l) := by
  rw [pi2Omega_eq, pi2Omega_eq]
  exact UniComplete.Domain.sq_iterate_pointE l hx

/-- `ω_0 = 0`. -/
theorem pi2Omega_zero : pi2Omega 0 = 0 := by rw [pi2Omega_eq]; exact UniComplete.Domain.pointE_zero

/-! ## `W`: the basis `B` -/

/-- The weight polynomial of index `i` on `m` digits: `Π_l (s^l if i_l else 1 + s^l)`. -/
noncomputable def eqPolyB (m i : ℕ) : E[X] :=
  ∏ l ∈ range m, if i.testBit l then QuotientSecurity.digitPoly l else 1 + QuotientSecurity.digitPoly l

/-- **A column's polynomial in the basis `B`**: `Σ_i T_i Π_l (s^l if i_l else 1 + s^l)`. -/
noncomputable def wPoly (m : ℕ) (T : ℕ → K) : E[X] := ∑ i ∈ range (2 ^ m), C (ofK (T i)) * eqPolyB m i

theorem eqPolyB_eval (m i : ℕ) (x : E) :
    (eqPolyB m i).eval x =
      ∏ l ∈ range m, if i.testBit l then QuotientSecurity.sq^[l] x else 1 + QuotientSecurity.sq^[l] x := by
  unfold eqPolyB
  rw [eval_prod]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  split_ifs
  · exact QuotientSecurity.digitPoly_eval l x
  · rw [Polynomial.eval_add, Polynomial.eval_one, QuotientSecurity.digitPoly_eval]

theorem wPoly_eval (m : ℕ) (T : ℕ → K) (x : E) :
    (wPoly m T).eval x = ∑ i ∈ range (2 ^ m), ofK (T i) *
      ∏ l ∈ range m, if i.testBit l then QuotientSecurity.sq^[l] x else 1 + QuotientSecurity.sq^[l] x := by
  unfold wPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, eqPolyB_eval]

theorem sum_two_pow_lt : ∀ m : ℕ, ∑ l ∈ range m, 2 ^ l < 2 ^ m
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := sum_two_pow_lt m
    omega

theorem natDegree_eqPolyB_le (m i : ℕ) : (eqPolyB m i).natDegree ≤ ∑ l ∈ range m, 2 ^ l := by
  unfold eqPolyB
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
  split_ifs
  · exact QuotientSecurity.natDegree_digitPoly_le l
  · exact (natDegree_add_le _ _).trans (by
      rw [natDegree_one, zero_max]; exact QuotientSecurity.natDegree_digitPoly_le l)

/-- **The column's polynomial has degree below `2^m`.** -/
theorem natDegree_wPoly_lt (m : ℕ) (T : ℕ → K) : (wPoly m T).natDegree < 2 ^ m := by
  unfold wPoly
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_) (sum_two_pow_lt m)
  exact (natDegree_C_mul_le _ _).trans (natDegree_eqPolyB_le m i)

/-- **The column's polynomial takes the basis-`B` values on `V_m`**: `w(ω_x) = basisValue T m x`. -/
theorem wPoly_eval_pointE {m : ℕ} (hm : m ≤ 32) (T : ℕ → K) {x : ℕ} (hx : x < 2 ^ m) :
    (wPoly m T).eval (pi2Omega x) =
      ofK (UniStatement.basisValue (Array.ofFn (n := 2 ^ m) fun i ↦ T i.val) m x) := by
  have hx32 : x < 2 ^ 32 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hm)
  unfold UniStatement.basisValue
  have hlen : ((List.range m).map fun l ↦ UniStatement.point (x >>> l)).length = m := by simp
  rw [UniSound.Ids.mleK_eq_sum _ _ (by rw [Array.size_ofFn, hlen]), hlen, wPoly_eval, UniSound.Ids.ofK_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [UniSound.Ids.ofK_mul, mul_comm (ofK (UniSound.Ids.cubeEqK _ _ _))]
  congr 1
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [Finset.mem_range.mp hi]
  · unfold UniSound.Ids.cubeEqK
    rw [UniSound.Ids.ofK_prod]
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hpl : ((List.range m).map fun l ↦ UniStatement.point (x >>> l)).getD l 0 = UniStatement.point (x >>> l) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp hl)]
      rfl
    rw [hpl, sq_iterate_pi2Omega l hx32, pi2Omega_eq]
    split_ifs
    · rfl
    · rw [UniSound.Ids.ofK_add, UniSound.Ids.ofK_one]
      rfl

/-- **`W`'s true fold values at `t`**: the table's partial evaluation at the high digits `w_r(t), …, w_{m−1}(t)`. -/
noncomputable def wFold (m r : ℕ) (T : ℕ → K) (t : E) (k : ℕ) : E :=
  ∑ j ∈ range (2 ^ (m - r)), ofK (T (k + 2 ^ r * j)) *
    ∏ l ∈ range (m - r), if j.testBit l then QuotientSecurity.sq^[r + l] t else 1 + QuotientSecurity.sq^[r + l] t

/-- **The sibling trick**: the verifier's cells from the true fold values are the row's cells, `w(t + ω_x)`,
`x < 2^r ≤ 2^m`. -/
theorem cells_wFold {m r : ℕ} (hrm : r ≤ m) (T : ℕ → K) (t : E) {x : ℕ} (hx : x < 2 ^ r) (hr32 : r ≤ 32) :
    RecPiop.cellsOf r pi2Omega (wFold m r T t) t x = (wPoly m T).eval (t + pi2Omega x) := by
  have hx32 : x < 2 ^ 32 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hr32)
  have hdig : ∀ l, QuotientSecurity.sq^[l] (t + pi2Omega x) = QuotientSecurity.sq^[l] t + pi2Omega (x >>> l) :=
    fun l ↦ by rw [QuotientSecurity.sq_iterate_add, sq_iterate_pi2Omega l hx32]
  have hhigh : ∀ l, r ≤ l → pi2Omega (x >>> l) = 0 := fun l hl ↦ by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hl)),
      pi2Omega_zero]
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrm
  rw [wPoly_eval, sum_range_two_pow_add r _ s]
  unfold RecPiop.cellsOf wFold
  simp only [Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hA : (∏ l ∈ range r, if (k + 2 ^ r * j).testBit l then QuotientSecurity.sq^[l] (t + pi2Omega x)
      else 1 + QuotientSecurity.sq^[l] (t + pi2Omega x)) =
      ∏ l ∈ range r, if k.testBit l then QuotientSecurity.sq^[l] t + pi2Omega (x >>> l)
        else 1 + (QuotientSecurity.sq^[l] t + pi2Omega (x >>> l)) := by
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.mp hl
    rw [testBit_add_two_pow_mul hk', if_pos hl', hdig]
  have hB : (∏ l ∈ range s, if (k + 2 ^ r * j).testBit (r + l) then QuotientSecurity.sq^[r + l] (t + pi2Omega x)
      else 1 + QuotientSecurity.sq^[r + l] (t + pi2Omega x)) =
      ∏ l ∈ range s, if j.testBit l then QuotientSecurity.sq^[r + l] t else 1 + QuotientSecurity.sq^[r + l] t := by
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    have hnl : ¬ r + l < r := by omega
    rw [testBit_add_two_pow_mul hk', if_neg hnl, Nat.add_sub_cancel_left, hdig, hhigh (r + l) (by omega), add_zero]
  rw [Finset.prod_range_add, hA, hB]
  ring

/-- `ρ` squared `l` times is `ρ^(2^l)`. -/
theorem sqIter_eq_pow (ρ : E) : ∀ l : ℕ, sqIter ρ l = ρ ^ (2 ^ l)
  | 0 => by simp [sqIter]
  | l + 1 => by
    have ih := sqIter_eq_pow ρ l
    unfold sqIter at ih ⊢
    rw [Function.iterate_succ_apply', ih, pow_succ, pow_mul, pow_two]

/-- **`W`'s claim is the true fold values' fold at `ρ`**: the table's multilinear extension at
`(ρ, ρ², …, ρ^(2^(r−1)), w_r(t), …, w_{m−1}(t))` is `foldAt r (wFold m r T t) ρ`. -/
theorem claim_wFold {m r : ℕ} (hrm : r ≤ m) (T : ℕ → K) (t ρ : E) :
    ∑ i ∈ range (2 ^ m), PcsQuotient.eqBits ((List.range r).map (sqIter ρ) ++
        ((digitsList t (m + 3)).drop r).take (m - r)) i * ofK (T i) =
      RecPiop.foldAt r (wFold m r T t) ρ := by
  have hlr : ((List.range r).map (sqIter ρ)).length = r := by simp
  have hhi : ∀ l < m - r, (((digitsList t (m + 3)).drop r).take (m - r)).getD l 0 =
      QuotientSecurity.sq^[r + l] t := fun l hl ↦ by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hl, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
    exact digitsList_getD t (by omega)
  have hlenhi : (((digitsList t (m + 3)).drop r).take (m - r)).length = m - r := by
    simp [digitsList]; omega
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrm
  simp only [Nat.add_sub_cancel_left] at hhi hlenhi ⊢
  rw [sum_range_two_pow_add r _ s]
  unfold RecPiop.foldAt wFold
  simp only [Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < 2 ^ ((List.range r).map (sqIter ρ)).length := by rw [hlr]; exact Finset.mem_range.mp hk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have e := eqBits_append ((List.range r).map (sqIter ρ)) (((digitsList t (r + s + 3)).drop r).take s) hk' j
  rw [hlr] at e
  rw [e]
  have h1 : PcsQuotient.eqBits ((List.range r).map (sqIter ρ)) k = RecPiop.eqPow r ρ k := by
    rw [eqBits_eq_prod, hlr]
    unfold RecPiop.eqPow
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp hl)]
    simp only [Option.map_some, Option.getD_some, sqIter_eq_pow]
  have h2 : PcsQuotient.eqBits (((digitsList t (r + s + 3)).drop r).take s) j =
      ∏ l ∈ range s, if j.testBit l then QuotientSecurity.sq^[r + l] t else 1 + QuotientSecurity.sq^[r + l] t := by
    rw [eqBits_eq_prod, hlenhi]
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    rw [hhi l (Finset.mem_range.mp hl)]
  rw [h1, h2]
  ring

end RecCompose
