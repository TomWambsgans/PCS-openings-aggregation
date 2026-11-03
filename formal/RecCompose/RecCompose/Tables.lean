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

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## Public layouts -/

/-- **A public layout holds nothing outside its chunks**: an entry whose chunk (`i / 2^lc`) is none of the listed ones
reads `0`. -/
theorem readEntry_ofChunks_zero {vars lc logN : ℕ} {chunks : List (ℕ × ℕ)}
    (hlane : logN - PcsQuotient.laneFold ≤ lc) (hlen : ∀ p ∈ chunks, p.2 ≤ 2 ^ lc) (stack : ℕ → K) {i : ℕ}
    (hi : ∀ p ∈ chunks, p.1 ≠ i / 2 ^ lc) :
    (PcsQuotient.Layout.ofChunks vars lc logN chunks).readEntry stack i = 0 := by
  obtain ⟨d, hd⟩ : ∃ d, lc = (logN - PcsQuotient.laneFold) + d := ⟨lc - (logN - PcsQuotient.laneFold), by omega⟩
  set a := logN - PcsQuotient.laneFold with ha
  have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
  have hnone : (PcsQuotient.Layout.ofChunks vars lc logN chunks).lanes.findIdx?
      (· = PcsQuotient.Lane.block (i / 2 ^ a)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    rw [decide_eq_false_iff_not]
    intro heq
    simp only [PcsQuotient.Layout.ofChunks, List.mem_flatMap] at hx
    obtain ⟨⟨c, len⟩, hc, hx⟩ := hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [PcsQuotient.Lane.block.injEq] at heq
    have hlenc : len ≤ 2 ^ lc := hlen (c, len) hc
    have hjd : j < 2 ^ d := by
      have h1 : (len + 2 ^ a - 1) / 2 ^ a ≤ 2 ^ d := by
        rw [Nat.div_le_iff_le_mul_add_pred hpos]
        rw [hd, pow_add] at hlenc
        generalize 2 ^ a * 2 ^ d = P at hlenc ⊢
        generalize 2 ^ a = A at hpos ⊢
        omega
      rw [← ha] at hj
      omega
    have hd' : lc - a = d := by omega
    rw [hd'] at heq
    refine hi (c, len) hc ?_
    show c = i / 2 ^ lc
    rw [hd, pow_add, ← Nat.div_div_eq_div_mul, ← heq, mul_comm c, Nat.add_comm, Nat.add_mul_div_left _ _
      (Nat.two_pow_pos d), Nat.div_eq_of_lt hjd, zero_add]
  have hlp : (PcsQuotient.Layout.ofChunks vars lc logN chunks).logPiece = none := rfl
  have hlg : (PcsQuotient.Layout.ofChunks vars lc logN chunks).logN = logN := rfl
  simp only [PcsQuotient.Layout.readEntry, hlp, PcsQuotient.Layout.logLane, hlg, ← ha, hnone]

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## The extension's coordinates -/

theorem one_add_yE_ne_zero : (1 + yE : E) ≠ 0 := by decide +kernel

theorem one_add_yE_sq_ne_zero : (1 + yE * yE : E) ≠ 0 := by
  have e : (1 + yE * yE : E) = (1 + yE) * (1 + yE) := by
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    linear_combination (-yE) * h2
  rw [e]
  exact mul_ne_zero one_add_yE_ne_zero one_add_yE_ne_zero

theorem ext_y0 : extension.1.1 = yE * (1 + yE)⁻¹ := rfl
theorem ext_y1 : extension.1.2 = yE * yE * (1 + yE * yE)⁻¹ := rfl
theorem ext_scale : extension.2 = ((1 + yE) * (1 + yE * yE))⁻¹ := by simp only [extension]

section Gen

variable {F : Type} [Field F] [CharP F 2]

theorem one_add_mul_inv {x : F} (hx : 1 + x ≠ 0) : 1 + x * (1 + x)⁻¹ = (1 + x)⁻¹ := by
  have h : (1 + x) * (1 + x)⁻¹ = 1 := mul_inv_cancel₀ hx
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (-1 : F) * h + x * (1 + x)⁻¹ * h2

/-- A digit's weight at `u = w/(1 + w)`: `(w if b else 1) (1 + w)⁻¹`. -/
theorem digit_weight {w : F} (hw : 1 + w ≠ 0) (b : Bool) :
    (if b then w / (1 + w) else 1 + w / (1 + w)) = (if b then w else 1) * (1 + w)⁻¹ := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, one_mul, div_eq_mul_inv]
    exact one_add_mul_inv hw
  · simp only [ite_true, div_eq_mul_inv]

theorem limbs_sum_gen (Y : F) (h0 : 1 + Y ≠ 0) (h1 : 1 + Y * Y ≠ 0) (f : ℕ → F) :
    (1 + Y * (1 + Y)⁻¹) * (1 + Y * Y * (1 + Y * Y)⁻¹) * f 0 + Y * (1 + Y)⁻¹ * (1 + Y * Y * (1 + Y * Y)⁻¹) * f 1 +
        (1 + Y * (1 + Y)⁻¹) * (Y * Y * (1 + Y * Y)⁻¹) * f 2 =
      ((1 + Y) * (1 + Y * Y))⁻¹ * (f 0 + Y * f 1 + Y ^ 2 * f 2) := by
  have e1 : 1 + Y * Y * (1 + Y * Y)⁻¹ = (1 + Y * Y)⁻¹ := one_add_mul_inv h1
  rw [one_add_mul_inv h0, e1, mul_inv]
  ring

end Gen

theorem eqBits_pair (p q : E) (l : ℕ) :
    PcsQuotient.eqBits [p, q] l = (if l.testBit 0 then p else 1 + p) * (if l.testBit 1 then q else 1 + q) := by
  rw [eqBits_eq_prod]
  simp [Finset.prod_range_succ]

/-- **The limbs' weights at the extension's point** are the scale times `1, Y, Y²` (limb `3` weighs `y₀ y₁`, read
nowhere): `Σ_{l<4} eq((y₀, y₁), l) f_l = s (f_0 + Y f_1 + Y² f_2)` when `f_3 = 0`. -/
theorem limbs_sum (f : ℕ → E) (h3 : f 3 = 0) :
    ∑ l ∈ range 4, PcsQuotient.eqBits [extension.1.1, extension.1.2] l * f l =
      extension.2 * ∑ l ∈ range 3, yE ^ l * f l := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h3, mul_zero, add_zero]
  rw [eqBits_pair _ _ 0, eqBits_pair _ _ 1, eqBits_pair _ _ 2]
  simp only [show (0 : ℕ).testBit 0 = false from rfl, show (0 : ℕ).testBit 1 = false from rfl,
    show (1 : ℕ).testBit 0 = true from rfl, show (1 : ℕ).testBit 1 = false from rfl,
    show (2 : ℕ).testBit 0 = false from rfl, show (2 : ℕ).testBit 1 = true from rfl, ite_true, ite_false,
    Bool.false_eq_true, pow_zero, pow_one, one_mul]
  rw [ext_y0, ext_y1, ext_scale]
  exact limbs_sum_gen yE one_add_yE_ne_zero one_add_yE_sq_ne_zero f

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## `Q`: the novel basis -/

/-- `Q`'s table: its stack read under `Q`'s layout (`m + 5` variables: the position's `m` bits, the novel index's two
digits' bits, the kind `h`/`q`, the limb's two bits). -/
def qTable (m : ℕ) (c : Stk) (i : ℕ) : K := (layoutsOf m).2.1.readEntry c i

/-- **`Q`'s coefficient** of kind `kind` (`0` for `h`, `1` for `q`) at the novel index `pd < 4N`: its limbs
`c_0 + Y c_1 + Y² c_2`, limb `l` at chunk `8 l + 4 kind + digit`. -/
def qCoef (T : ℕ → K) (m kind pd : ℕ) : E := ∑ l ∈ range 3, yE ^ l * ofK (T (pd + 2 ^ (m + 2) * (kind + 2 * l)))

/-- **`h`**: `Q`'s kind-`0` coefficients in the novel basis on `m` digits (degree below `N`). -/
noncomputable def hPoly (T : ℕ → K) (m : ℕ) : E[X] := UniComplete.AlgC.novP m (qCoef T m 0)

/-- **`q`**: `Q`'s kind-`1` coefficients in the novel basis on `m + 2` digits (degree below `4N`). -/
noncomputable def qPoly (T : ℕ → K) (m : ℕ) : E[X] := UniComplete.AlgC.novP (m + 2) (qCoef T m 1)

/-- **`Q`'s table is zero outside `quotient_chunks`**: `h`'s digits `1, 2, 3` and the limb `3`. -/
structure QZero (T : ℕ → K) (m : ℕ) : Prop where
  h_high : ∀ pd, 2 ^ m ≤ pd → pd < 2 ^ (m + 2) → ∀ l < 3, T (pd + 2 ^ (m + 2) * (0 + 2 * l)) = 0
  limb3 : ∀ pd < 2 ^ (m + 2), ∀ kind < 2, T (pd + 2 ^ (m + 2) * (kind + 2 * 3)) = 0

theorem chunk_of (m pd k : ℕ) :
    (pd + 2 ^ (m + 2) * k) / 2 ^ m = pd / 2 ^ m + 4 * k := by
  rw [show 2 ^ (m + 2) * k = 2 ^ m * (4 * k) by rw [pow_add]; ring, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m)]

theorem qChunks_mem {m : ℕ} {p : ℕ × ℕ} (hp : p ∈ quotientChunks m) :
    p.2 = 2 ^ m ∧ ∃ limb < 3, p.1 = 8 * limb ∨ ∃ d < 4, p.1 = 8 * limb + 4 + d := by
  unfold quotientChunks at hp
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map] at hp
  obtain ⟨limb, hl, h | ⟨d, hd, h⟩⟩ := hp
  · subst h; exact ⟨rfl, limb, hl, Or.inl rfl⟩
  · subst h; exact ⟨rfl, limb, hl, Or.inr ⟨d, hd, rfl⟩⟩

/-- **`Q`'s layout's zeros** (π2's `m ≥ 20`: its stack has `max(m + 4, 24)` variables, lanes of at most `2^m`). -/
theorem qZero {m : ℕ} (hm : 20 ≤ m) (c : Stk) : QZero (qTable m c) m := by
  have hQ : (layoutsOf m).2.1 = PcsQuotient.Layout.ofChunks (m + 5) m (max (m + 4) minCertifiedStack)
      (quotientChunks m) := by
    simp only [layoutsOf, certifiedFrom, hm, ite_true]
  have hlane : max (m + 4) minCertifiedStack - PcsQuotient.laneFold ≤ m := by
    simp only [minCertifiedStack, PcsQuotient.laneFold]; omega
  have hlen : ∀ p ∈ quotientChunks m, p.2 ≤ 2 ^ m := fun p hp ↦ (qChunks_mem hp).1.le
  have hq4 : ∀ pd < 2 ^ (m + 2), pd / 2 ^ m < 4 := fun pd h2 ↦ by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)]
    rw [pow_add] at h2; omega
  refine ⟨fun pd h1 h2 l _ ↦ ?_, fun pd hpd kind _ ↦ ?_⟩
  · unfold qTable
    rw [hQ]
    refine readEntry_ofChunks_zero hlane hlen c fun p hp heq ↦ ?_
    rw [chunk_of] at heq
    have hd1 : 1 ≤ pd / 2 ^ m := (Nat.le_div_iff_mul_le (Nat.two_pow_pos m)).mpr (by omega)
    have hd4 := hq4 pd h2
    generalize pd / 2 ^ m = q at heq hd1 hd4
    obtain ⟨-, limb, hlimb, h | ⟨d, hd, h⟩⟩ := qChunks_mem hp <;> omega
  · unfold qTable
    rw [hQ]
    refine readEntry_ofChunks_zero hlane hlen c fun p hp heq ↦ ?_
    rw [chunk_of] at heq
    have hd4 := hq4 pd hpd
    generalize pd / 2 ^ m = q at heq hd4
    obtain ⟨-, limb, hlimb, h | ⟨d, hd, h⟩⟩ := qChunks_mem hp <;> omega

/-! ### The weights of `Q`'s claims -/

/-- **The first coordinate of a claim's weight**: `Σ_i eq(x :: p, i) g_i = (1 + x) Σ_j eq(p, j) g_{2j} +
x Σ_j eq(p, j) g_{1 + 2j}`. -/
theorem sum_eqBits_cons (x : E) (p : List E) (g : ℕ → E) :
    ∑ i ∈ range (2 ^ (x :: p).length), PcsQuotient.eqBits (x :: p) i * g i =
      (1 + x) * ∑ j ∈ range (2 ^ p.length), PcsQuotient.eqBits p j * g (2 * j) +
        x * ∑ j ∈ range (2 ^ p.length), PcsQuotient.eqBits p j * g (1 + 2 * j) := by
  have hl : (x :: p).length = 1 + p.length := by simp [Nat.add_comm]
  rw [hl, sum_range_two_pow_add 1 _ p.length]
  have e : ∀ k < 2 ^ ([x] : List E).length, ∀ j,
      PcsQuotient.eqBits (x :: p) (k + 2 ^ 1 * j) = PcsQuotient.eqBits [x] k * PcsQuotient.eqBits p j :=
    fun k hk j ↦ eqBits_append [x] p hk j
  simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at e ⊢
  have e0 : ∀ j, PcsQuotient.eqBits (x :: p) (2 * j) = (1 + x) * PcsQuotient.eqBits p j := fun j ↦ by
    have := e 0 (by simp) j
    rw [zero_add] at this
    rw [this, eqBits_eq_prod]
    simp
  have e1 : ∀ j, PcsQuotient.eqBits (x :: p) (1 + 2 * j) = x * PcsQuotient.eqBits p j := fun j ↦ by
    rw [e 1 (by simp) j, eqBits_eq_prod]
    simp
  simp only [e0, e1, Finset.mul_sum, mul_assoc]

/-- `Σ_i eq(1^n, i) g_i = g_{2^n − 1}`. -/
theorem sum_eqBits_ones : ∀ (n : ℕ) (g : ℕ → E),
    ∑ i ∈ range (2 ^ n), PcsQuotient.eqBits (List.replicate n 1) i * g i = g (2 ^ n - 1)
  | 0, f => by simp [eqBits_eq_prod]
  | n + 1, f => by
    have h := sum_eqBits_cons 1 (List.replicate n 1) f
    rw [List.length_cons, List.length_replicate] at h
    rw [List.replicate_succ, h, CharTwo.add_self_eq_zero, zero_mul, zero_add, one_mul,
      sum_eqBits_ones n (fun j ↦ f (1 + 2 * j))]
    congr 1
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

/-- `Σ_i eq(0^n, i) g_i = g_0`. -/
theorem sum_eqBits_zeros : ∀ (n : ℕ) (g : ℕ → E),
    ∑ i ∈ range (2 ^ n), PcsQuotient.eqBits (List.replicate n 0) i * g i = g 0
  | 0, f => by simp [eqBits_eq_prod]
  | n + 1, f => by
    have h := sum_eqBits_cons 0 (List.replicate n 0) f
    rw [List.length_cons, List.length_replicate] at h
    rw [List.replicate_succ, h, add_zero, one_mul, zero_mul, add_zero, sum_eqBits_zeros n (fun j ↦ f (2 * j)),
      mul_zero]

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ### `Q`'s claims -/

theorem qCoef_zero_of {T : ℕ → K} {m kind pd : ℕ} (h : ∀ l < 3, T (pd + 2 ^ (m + 2) * (kind + 2 * l)) = 0) :
    qCoef T m kind pd = 0 := by
  unfold qCoef
  refine Finset.sum_eq_zero fun l hl ↦ ?_
  rw [h l (Finset.mem_range.mp hl), UniSound.Ids.ofK_zero, mul_zero]

/-- `h`'s coefficients at the novel indices below `4N`: only those below `N`. -/
theorem sum_qc0 {T : ℕ → K} {m : ℕ} (hz : QZero T m) (w : ℕ → E) :
    ∑ pd ∈ range (2 ^ (m + 2)), qCoef T m 0 pd * UniComplete.AlgC.novX (m + 2) pd w =
      ∑ k ∈ range (2 ^ m), qCoef T m 0 k * UniComplete.AlgC.novX m k w := by
  rw [sum_range_two_pow_add m _ 2]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  have hz' : ∀ j, 1 ≤ j → j < 4 → qCoef T m 0 (k + 2 ^ m * j) = 0 := fun j h1 h4 ↦
    qCoef_zero_of fun l hl ↦ hz.h_high _ (by nlinarith) (by rw [pow_add]; nlinarith) l hl
  simp only [show (2 : ℕ) ^ 2 = 4 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    hz' 1 (by norm_num) (by norm_num), hz' 2 (by norm_num) (by norm_num), hz' 3 (by norm_num) (by norm_num),
    zero_mul, add_zero, mul_zero]
  rw [UniComplete.AlgC.novX_low (by rw [pow_succ]; omega), UniComplete.AlgC.novX_low hk']

/-- A point's weight at `u_l = w_l/(1 + w_l)`: the novel monomial times `Π_l (1 + w_l)⁻¹`. -/
theorem eqBits_digits {u : List E} {n : ℕ} (hu : u.length = n) {w : ℕ → E} (hw : ∀ l < n, 1 + w l ≠ 0)
    (huw : ∀ l < n, u.getD l 0 = w l / (1 + w l)) (pd : ℕ) :
    PcsQuotient.eqBits u pd = UniComplete.AlgC.novX n pd w * ∏ l ∈ range n, (1 + w l)⁻¹ := by
  rw [eqBits_eq_prod, hu, UniComplete.AlgC.novX, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l hl ↦ ?_
  have hl' := Finset.mem_range.mp hl
  rw [huw l hl', digit_weight (hw l hl')]

/-- **`Q`'s first claim** at `(u, ρ', y₀, y₁)`, `u_l = w_l/(1 + w_l)`: the scale, `Π_l (1 + w_l)⁻¹`, and the combination
`(1 + ρ') h + ρ' q` at the digits `w`. -/
theorem claim_quotient {T : ℕ → K} {m : ℕ} (hz : QZero T m) {u : List E} (hu : u.length = m + 2) {w : ℕ → E}
    (hw : ∀ l < m + 2, 1 + w l ≠ 0) (huw : ∀ l < m + 2, u.getD l 0 = w l / (1 + w l)) (ρ' : E) :
    ∑ i ∈ range (2 ^ (m + 5)), PcsQuotient.eqBits (u ++ [ρ', extension.1.1, extension.1.2]) i * ofK (T i) =
      extension.2 * (∏ l ∈ range (m + 2), (1 + w l)⁻¹) *
        ((1 + ρ') * ∑ k ∈ range (2 ^ m), qCoef T m 0 k * UniComplete.AlgC.novX m k w +
          ρ' * ∑ k ∈ range (2 ^ (m + 2)), qCoef T m 1 k * UniComplete.AlgC.novX (m + 2) k w) := by
  rw [show m + 5 = (m + 2) + 3 by ring, sum_range_two_pow_add (m + 2) _ 3, ← sum_qc0 hz w]
  have hinner : ∀ pd < 2 ^ (m + 2), ∑ kd ∈ range (2 ^ 3), PcsQuotient.eqBits (u ++ [ρ', extension.1.1, extension.1.2])
      (pd + 2 ^ (m + 2) * kd) * ofK (T (pd + 2 ^ (m + 2) * kd)) =
      UniComplete.AlgC.novX (m + 2) pd w * (∏ l ∈ range (m + 2), (1 + w l)⁻¹) *
        (extension.2 * ((1 + ρ') * qCoef T m 0 pd + ρ' * qCoef T m 1 pd)) := by
    intro pd hpd
    have hpd' : pd < 2 ^ u.length := by rw [hu]; exact hpd
    have happ : ∀ kd, PcsQuotient.eqBits (u ++ [ρ', extension.1.1, extension.1.2]) (pd + 2 ^ (m + 2) * kd) =
        PcsQuotient.eqBits u pd * PcsQuotient.eqBits [ρ', extension.1.1, extension.1.2] kd := fun kd ↦ by
      have := eqBits_append u [ρ', extension.1.1, extension.1.2] hpd' kd
      rw [hu] at this
      exact this
    simp only [happ, mul_assoc]
    rw [← Finset.mul_sum, eqBits_digits hu hw huw pd]
    have hc := sum_eqBits_cons ρ' [extension.1.1, extension.1.2] (fun kd ↦ ofK (T (pd + 2 ^ (m + 2) * kd)))
    simp only [List.length_cons, List.length_nil] at hc
    rw [show (2 : ℕ) ^ 3 = 2 ^ (0 + 1 + 1 + 1) from rfl, hc]
    have h0 := limbs_sum (fun l ↦ ofK (T (pd + 2 ^ (m + 2) * (2 * l))))
      (by show ofK (T (pd + 2 ^ (m + 2) * (2 * 3))) = 0
          rw [show 2 * 3 = 0 + 2 * 3 by rfl, hz.limb3 pd hpd 0 (by norm_num), UniSound.Ids.ofK_zero])
    have h1 := limbs_sum (fun l ↦ ofK (T (pd + 2 ^ (m + 2) * (1 + 2 * l))))
      (by show ofK (T (pd + 2 ^ (m + 2) * (1 + 2 * 3))) = 0
          rw [hz.limb3 pd hpd 1 (by norm_num), UniSound.Ids.ofK_zero])
    rw [show (2 : ℕ) ^ (0 + 1 + 1) = 4 from rfl, h0, h1]
    unfold qCoef
    simp only [zero_add]
    ring
  rw [Finset.sum_congr rfl fun pd hpd ↦ hinner pd (Finset.mem_range.mp hpd), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

/-- **`Q`'s second claim** at `(1^m, 0, 0, 0, y₀, y₁)`: the scale times `h`'s top coefficient. -/
theorem claim_sum {T : ℕ → K} {m : ℕ} (hz : QZero T m) :
    ∑ i ∈ range (2 ^ (m + 5)), PcsQuotient.eqBits (List.replicate m 1 ++ [0, 0, 0] ++ [extension.1.1, extension.1.2])
      i * ofK (T i) = extension.2 * qCoef T m 0 (2 ^ m - 1) := by
  have hrep : (List.replicate m (1 : E)).length = m := List.length_replicate
  rw [List.append_assoc, sum_range_two_pow_add m _ 5]
  have happ : ∀ pos < 2 ^ m, ∀ c, PcsQuotient.eqBits (List.replicate m 1 ++ ([0, 0, 0] ++ [extension.1.1,
      extension.1.2])) (pos + 2 ^ m * c) = PcsQuotient.eqBits (List.replicate m 1) pos *
        PcsQuotient.eqBits ([0, 0, 0] ++ [extension.1.1, extension.1.2]) c := fun pos hpos c ↦ by
    have := eqBits_append (List.replicate m (1 : E)) ([0, 0, 0] ++ [extension.1.1, extension.1.2])
      (by rw [hrep]; exact hpos) c
    rw [hrep] at this
    exact this
  rw [Finset.sum_congr rfl fun pos hpos ↦ Finset.sum_congr rfl fun c _ ↦ by
    rw [happ pos (Finset.mem_range.mp hpos) c, mul_assoc]]
  simp only [← Finset.mul_sum]
  rw [sum_eqBits_ones m (fun pos ↦ ∑ c ∈ range (2 ^ 5), PcsQuotient.eqBits ([0, 0, 0] ++ [extension.1.1,
    extension.1.2]) c * ofK (T (pos + 2 ^ m * c)))]
  have hz3 : ([0, 0, 0] : List E) = List.replicate 3 0 := rfl
  rw [show (5 : ℕ) = 3 + 2 by rfl, sum_range_two_pow_add 3 _ 2]
  have happ2 : ∀ d < 2 ^ 3, ∀ l, PcsQuotient.eqBits ([0, 0, 0] ++ [extension.1.1, extension.1.2]) (d + 2 ^ 3 * l) =
      PcsQuotient.eqBits [0, 0, 0] d * PcsQuotient.eqBits [extension.1.1, extension.1.2] l := fun d hd l ↦
    eqBits_append [0, 0, 0] [extension.1.1, extension.1.2] (by simpa using hd) l
  rw [Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun l _ ↦ by
    rw [happ2 d (Finset.mem_range.mp hd) l, mul_assoc]]
  simp only [← Finset.mul_sum]
  rw [hz3, sum_eqBits_zeros 3 (fun d ↦ ∑ l ∈ range (2 ^ 2), PcsQuotient.eqBits [extension.1.1, extension.1.2] l *
    ofK (T (2 ^ m - 1 + 2 ^ m * (d + 2 ^ 3 * l))))]
  have hidx : ∀ l, 2 ^ m - 1 + 2 ^ m * (0 + 2 ^ 3 * l) = 2 ^ m - 1 + 2 ^ (m + 2) * (0 + 2 * l) := fun l ↦ by
    rw [pow_add]; ring
  simp only [hidx]
  have hpd : 2 ^ m - 1 < 2 ^ (m + 2) := by
    have : 2 ^ m ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  rw [show (2 : ℕ) ^ 2 = 4 from rfl, limbs_sum _ (by
    show ofK (T (2 ^ m - 1 + 2 ^ (m + 2) * (0 + 2 * 3))) = 0
    rw [hz.limb3 _ hpd 0 (by norm_num), UniSound.Ids.ofK_zero])]
  rfl

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ### `h` and `q` at a point, `Σ_V h` -/

/-- The digits `w_l(x) = s^l(x)`. -/
theorem wP_eval_sq (l : ℕ) (x : E) : (UniComplete.Domain.wP l).eval x = QuotientSecurity.sq^[l] x :=
  UniComplete.Domain.wP_eval x l

/-- **A novel-basis polynomial at a point**: `Σ_k d_k Π_{l : k_l} s^l(x)`. -/
theorem novP_eval_sq (m : ℕ) (d : ℕ → E) (x : E) :
    (UniComplete.AlgC.novP m d).eval x =
      ∑ k ∈ range (2 ^ m), d k * UniComplete.AlgC.novX m k (fun l ↦ QuotientSecurity.sq^[l] x) := by
  rw [UniComplete.AlgC.novP_eval]
  simp only [wP_eval_sq]

/-- The novel polynomial as `QuotientSecurity.tablePoly` of the table its bits index. -/
theorem novP_eval_tablePoly (m : ℕ) (d : ℕ → E) (x : E) :
    (UniComplete.AlgC.novP m d).eval x = (QuotientSecurity.tablePoly (fun b : Fin m → Bool ↦
      ∑ i ∈ range (2 ^ m), if (fun k : Fin m ↦ i.testBit k) = b then d i else 0)).eval x := by
  rw [novP_eval_sq, QuotientSecurity.tablePoly_eval]
  unfold QuotientSecurity.digitsEval
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  congr 1
  unfold UniComplete.AlgC.novX
  rw [← Fin.prod_univ_eq_prod_range (fun l ↦ if i.testBit l then QuotientSecurity.sq^[l] x else 1) m]

/-- **`Σ_V h` is `h`'s top coefficient**: `Σ_{i<2^m} h(ω_i) = d_{2^m − 1}` (`RecPiop.sum_tablePoly_omega`). -/
theorem sum_novP_omega {m : ℕ} (hm : m ≤ 32) (d : ℕ → E) :
    ∑ i ∈ range (2 ^ m), (UniComplete.AlgC.novP m d).eval (pi2Omega i) = d (2 ^ m - 1) := by
  simp only [novP_eval_tablePoly]
  rw [RecPiop.sum_tablePoly_omega UniComplete.Domain.basisE hm]
  have hbits : (fun k : Fin m ↦ (2 ^ m - 1).testBit k) = fun _ ↦ true := by
    funext k
    rw [Nat.testBit_two_pow_sub_one]
    simp
  have hlt : 2 ^ m - 1 < 2 ^ m := Nat.sub_lt (Nat.two_pow_pos m) Nat.one_pos
  rw [Finset.sum_eq_single (2 ^ m - 1) (fun i hi hne ↦ by
      rw [if_neg]
      intro h
      apply hne
      exact (RecPiop.image_bits m).2 (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr (Finset.mem_range.mpr hlt))
        (h.trans hbits.symm))
    (fun h ↦ absurd (Finset.mem_range.mpr hlt) h), if_pos hbits]

end RecCompose
