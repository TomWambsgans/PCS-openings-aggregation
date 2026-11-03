-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Bridges
import Heap.Cantor

/-!
# The verifier's points, digits and columns on the Cantor subspaces

From `BetaCantor` (the verifier's `beta` is a Cantor basis on its first `24` vectors):

* `cantorE`: that basis in `E`, so `Heap.Cantor`'s facts apply; `pointE_eq_omega`: the verifier's
  `pointE i` is `Heap.omega` of it for `i < 2^24`; `iterate_pointE`: `w_l(ω_i) = ω_{i >> l}`;
* `mleK_eq_sum`, `basisValue_eq`: `basisValue` (the value at `ω_x` of a basis-`B` column, what
  `lv42Column` reads) is the column's claim at the digits of `ω_x`;
* **`c1P_eval_pointE`**: a `C1` column's polynomial (`c1P`) at `ω_x` is `ofK` of its value `c1Val`
  (given the column's one limb aligned inside the stack, `C1Limbs`, `LayoutAligned`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

/-! ## `K` inside `E` -/

theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b
theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b
theorem ofK_one : ofK (1 : K) = 1 := map_one (algebraMap K E)
theorem ofK_zero : ofK (0 : K) = 0 := map_zero (algebraMap K E)
theorem ofK_sum {ι : Type} (s : Finset ι) (f : ι → K) : ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s
theorem ofK_prod {ι : Type} (s : Finset ι) (f : ι → K) : ofK (∏ i ∈ s, f i) = ∏ i ∈ s, ofK (f i) :=
  map_prod (algebraMap K E) f s

theorem ofK_sq (a : K) : QuotientSecurity.sq (ofK a) = ofK (sK a) := by
  simp only [QuotientSecurity.sq, sK, ofK_add, ofK_mul]

/-! ## The basis -/

/-- **The verifier's Cantor basis, in `E`**, on its first `24` vectors. -/
def cantorE (h : BetaCantor) : QuotientSecurity.CantorBasis E 24 where
  β k := ofK (beta.getD k 0)
  zero := by rw [h.1, ofK_one]
  succ k hk := by rw [ofK_sq, h.2 k hk]

theorem foldl_ite_add {M : Type} [AddCommMonoid M] (f : ℕ → M) (p : ℕ → Bool) : ∀ n : ℕ,
    (List.range n).foldl (fun acc k ↦ if p k then acc + f k else acc) 0 =
      ∑ k ∈ range n, if p k then f k else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_ite_add f p n, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs <;> simp

/-- **The verifier's points are the Cantor basis's**: `pointE i = ω_i` for `i < 2^24`. -/
theorem pointE_eq_omega (h : BetaCantor) {i : ℕ} (hi : i < 2 ^ 24) :
    pointE i = Heap.omega (cantorE h) i := by
  unfold pointE point Heap.omega
  rw [foldl_ite_add (fun k ↦ beta.getD k 0) (fun k ↦ i.testBit k), ofK_sum]
  have h32 : basisSize = 24 + 8 := rfl
  rw [h32, Finset.sum_range_add]
  have hz : ∑ k ∈ range 8, ofK (if i.testBit (24 + k) then beta.getD (24 + k) 0 else 0) = 0 :=
    Finset.sum_eq_zero fun k _ ↦ by
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs <;> simp [cantorE]

/-- **The digits at the points**: `w_l(ω_i) = ω_{i >> l}`, `i < 2^24`. -/
theorem iterate_pointE (h : BetaCantor) (l : ℕ) {i : ℕ} (hi : i < 2 ^ 24) :
    QuotientSecurity.sq^[l] (pointE i) = pointE (i >>> l) := by
  have hl : i >>> l < 2 ^ 24 :=
    lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hi
  rw [pointE_eq_omega h hi, pointE_eq_omega h hl]
  exact Heap.sq_iterate_omega (cantorE h) l hi

theorem eval_digitP_pointE (h : BetaCantor) (l : ℕ) {i : ℕ} (hi : i < 2 ^ 24) :
    (digitP l).eval (pointE i) = pointE (i >>> l) := by
  rw [eval_digitP, iterate_pointE h l hi]

theorem pointE_zero : pointE 0 = 0 := by
  unfold pointE point
  rw [foldl_ite_add (fun k ↦ beta.getD k 0) (fun k ↦ (0 : ℕ).testBit k)]
  simp

/-! ## Basis-`B` values -/

/-- `eq(pt, i)` in `K`: `Π_l (pt_l if i_l else 1 + pt_l)`. -/
def cubeEqK (pt : List K) (n i : ℕ) : K :=
  ∏ l ∈ range n, if i.testBit l then pt.getD l 0 else 1 + pt.getD l 0

theorem sum_range_two_mul_K (m : ℕ) (f : ℕ → K) :
    ∑ i ∈ range (2 * m), f i = ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

theorem cubeEqK_cons (r : K) (pt : List K) (n i b : ℕ) (hb : b < 2) :
    cubeEqK (r :: pt) (n + 1) (2 * i + b) = (if b = 1 then r else 1 + r) * cubeEqK pt n i := by
  unfold cubeEqK
  rw [Finset.prod_range_succ']
  have h1 : ∀ k ∈ range n, (if (2 * i + b).testBit (k + 1) then (r :: pt).getD (k + 1) 0
      else 1 + (r :: pt).getD (k + 1) 0) = if i.testBit k then pt.getD k 0 else 1 + pt.getD k 0 :=
    fun k _ ↦ by simp only [List.getD_cons_succ, testBit_two_mul_add i b k hb]
  have h0 : (if (2 * i + b).testBit 0 then (r :: pt).getD 0 0 else 1 + (r :: pt).getD 0 0) =
      if b = 1 then r else 1 + r := by
    simp only [List.getD_cons_zero, testBit_two_mul_add_zero i b hb, decide_eq_true_eq]
  rw [Finset.prod_congr rfl h1, h0]
  ring

/-- **`mleK` is the claim's sum**: on a table of `2^|pt|` entries, `Σ_i eq(pt, i) table_i`. -/
theorem mleK_eq_sum : ∀ (pt : List K) (table : Array K), table.size = 2 ^ pt.length →
    mleK table pt = ∑ i ∈ range (2 ^ pt.length), cubeEqK pt pt.length i * table.getD i 0
  | [], table, hs => by
    simp [mleK, cubeEqK]
  | r :: pt, table, hs => by
    have hm : mleK table (r :: pt) = mleK (Array.ofFn (n := table.size / 2) fun i ↦
        table.getD (2 * i.val) 0 + r * (table.getD (2 * i.val) 0 + table.getD (2 * i.val + 1) 0)) pt := rfl
    have hs' : (Array.ofFn (n := table.size / 2) fun i ↦
        table.getD (2 * i.val) 0 + r * (table.getD (2 * i.val) 0 + table.getD (2 * i.val + 1) 0)).size =
          2 ^ pt.length := by
      rw [Array.size_ofFn, hs, List.length_cons, pow_succ]; omega
    rw [hm, mleK_eq_sum pt _ hs', List.length_cons, pow_succ, mul_comm (2 ^ pt.length) 2,
      sum_range_two_mul_K]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have hlt : i < table.size / 2 := by rw [hs, List.length_cons, pow_succ]; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hlt, dite_true, Option.getD_some]
    rw [show 2 * i = 2 * i + 0 by rfl, cubeEqK_cons r pt pt.length i 0 (by norm_num),
      cubeEqK_cons r pt pt.length i 1 (by norm_num)]
    simp only [ite_true, show (0 : ℕ) ≠ 1 by norm_num, ite_false, add_zero]
    ring

/-! ## Columns at the points -/

theorem c1Layout_eq (S : Shape) : c1Layout S = layoutOf S .c1 := rfl

theorem setupLayout_eq (S : Shape) : setupLayout S = layoutOf S .setup := rfl

theorem one_add_ite (a : E) (b : Bool) :
    1 + a + (if b then 1 else 0) = if b then a else 1 + a := by
  cases b
  · simp
  · simp only [ite_true]
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]

theorem ofK_cubeEqK (pt : List K) (n i : ℕ) :
    ofK (cubeEqK pt n i) = cubeEq (pt.map ofK) n i := by
  unfold cubeEqK cubeEq
  rw [ofK_prod]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [one_add_ite]
  have : (pt.map ofK).getD l 0 = ofK (pt.getD l 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases pt[l]? <;> simp
  rw [this]
  split_ifs <;> simp [ofK_add]

theorem blockBase_of_aligned {off v V : ℕ} (hal : 2 ^ v ∣ off) (hV : off < 2 ^ V) :
    blockBase off v V = off := by
  unfold blockBase
  rw [Nat.mod_eq_of_lt hV]
  exact Nat.div_mul_cancel hal

/-- **A one-limb column's polynomial at `ω_x`** is `ofK` of its basis-`B` value there. -/
theorem colPoly_eval_pointE (h : BetaCantor) (L : StackLayout) (V : ℕ) (C : Stk) (col : Column)
    (v off x : ℕ) (hl : L.limbs col = [(0, v, off)]) (hal : 2 ^ v ∣ off)
    (hin : off + 2 ^ v ≤ 2 ^ L.vars) (hLV : L.vars ≤ V) (hv : v ≤ 24) (hx : x < 2 ^ v) :
    (colPoly L V C col digitP).eval (pointE x) =
      ofK (basisValue (Array.ofFn (n := 2 ^ v) fun i ↦ C (off + i.val)) v x) := by
  have hx24 : x < 2 ^ 24 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hv)
  have hoff : off < 2 ^ V := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hLV
    have := Nat.two_pow_pos v
    omega
  unfold colPoly
  rw [hl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, blockBase_of_aligned hal hoff]
  simp only [limbScale, ite_true, map_one, one_mul]
  rw [eval_mlP _ v digitP (pointE x) (((List.range v).map fun l ↦ point (x >>> l)).map ofK) (fun l hl ↦ by
    rw [eval_digitP_pointE h l hx24, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hl]
    rfl)]
  unfold basisValue
  rw [mleK_eq_sum _ _ (by simp), ofK_sum]
  simp only [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [ofK_mul, ofK_cubeEqK]
  congr 1
  unfold stE
  rw [ite_eq_left (by omega)]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [hi]

end UniSound.Ids
