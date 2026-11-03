-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgHLayout
import UniComplete.Honest

/-!
# The leaves' polynomials at the domain's points, and their degrees (milestone 4)

* **Evaluation is a ring map** (`ev x p = (tp p).eval x`): the forms, the fingerprints, the memory's and the
  bytecode's tuples' fingerprints at the columns' polynomials evaluate to the same expressions at the columns'
  values (`ev_formP`, `ev_fpP`, `ev_memoryFpP`, `ev_bytecodeFpP`, `ev_foldl_mul`);
* **the fingerprints the heap divides by are `BadFp`'s**: `fpE` of a tuple of at most `16` forms is `fpOf` of its
  coordinates (`fpE_eq_fpOf`), the memory's and the bytecode's fingerprints are `fpOf` of their tuples
  (`memoryFp_eq_fpOf`, `bytecodeFp_eq_fpOf`);
* **degrees**: a form's polynomial at columns of degree `≤ n − 1` has degree `≤ |monomial| (n − 1)`, a tuple's
  fingerprint `≤ tupleDegree · (n − 1)` (`natDegree_fpP_le`);
* **`Z_act`, `Z_pad`** (`tp_zActP`, `tp_zPadP`): the prover's (CompPoly's) are the domain's (`Domain.zActP`,
  `Domain.zPadP = w_r /ₘ Z_act`), `r ≤ 31`, `rows ≤ 2^r`: the product of all the cosets' factors and the last
  row's is `w_r` (`prod_cosets_mul_last`).
-/

namespace UniComplete.AlgH

open Polynomial UniStatement LeanVM.Parameters Finset
open UniComplete.Domain (wP wP_monic wP_natDegree wP_zero wP_succ ite_pos_of ite_neg_of)

/-! ### Evaluation as a ring map -/

/-- Evaluation at `x` of a prover polynomial, as a ring map. -/
noncomputable def ev (x : E) : Poly →+* E :=
  (Polynomial.evalRingHom x).comp CompPoly.CPolynomial.toPolyRingHom

theorem ev_apply (x : E) (p : Poly) : ev x p = (tp p).eval x := by
  simp [ev, CompPoly.CPolynomial.toPolyRingHom_apply]

theorem ev_C (x c : E) : ev x (pC c) = c := by rw [ev_apply, tp_C, eval_C]

theorem ev_X (x : E) : ev x pX = x := by rw [ev_apply, tp_X, eval_X]

theorem ev_foldl_mul {α : Type*} (x : E) (g : α → Poly) :
    ∀ (l : List α) (a : Poly), ev x (l.foldl (fun p j ↦ p * g j) a) = l.foldl (fun p j ↦ p * ev x (g j)) (ev x a)
  | [], _ => rfl
  | j :: l, a => by rw [List.foldl_cons, List.foldl_cons, ev_foldl_mul x g l, map_mul]

theorem foldl_mul_eq {M : Type*} [CommMonoid M] {α : Type*} (g : α → M) :
    ∀ (l : List α) (a : M), l.foldl (fun acc x ↦ acc * g x) a = a * (l.map g).prod
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_mul_eq g l, List.map_cons, List.prod_cons, mul_assoc]

theorem foldl_add_eq {M : Type*} [AddCommMonoid M] {α : Type*} (g : α → M) :
    ∀ (l : List α) (a : M), l.foldl (fun acc x ↦ acc + g x) a = a + (l.map g).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_eq g l, List.map_cons, List.sum_cons, add_assoc]

theorem ev_formP_aux (x : E) (col : ℕ → Poly) :
    ∀ (f : Form) (a : Poly),
      ev x (f.foldl (fun acc (mc : List ℕ × E) ↦ acc + pC mc.2 * mc.1.foldl (fun p j ↦ p * col j) 1) a) =
        f.foldl (fun acc (mc : List ℕ × E) ↦ acc + mc.2 * mc.1.foldl (fun p j ↦ p * ev x (col j)) 1) (ev x a)
  | [], _ => rfl
  | (mono, c) :: f, a => by
    rw [List.foldl_cons, List.foldl_cons, ev_formP_aux x col f, map_add, map_mul, ev_C, ev_foldl_mul, map_one]

/-- **A form at the columns' polynomials evaluates to the form at their values.** -/
theorem ev_formP (x : E) (f : Form) (col : ℕ → Poly) : ev x (formP f col) = formE f fun j ↦ ev x (col j) := by
  unfold formP formE
  exact (ev_formP_aux x col f 0).trans (by rw [map_zero])

theorem ev_fpP_aux (x : E) (weights : Array E) (col : ℕ → Poly) :
    ∀ (l : List (Form × ℕ)) (a : Poly),
      ev x (l.foldl (fun acc (fs : Form × ℕ) ↦ acc + pC (weights.getD fs.2 0) * formP fs.1 col) a) =
        l.foldl (fun acc (fs : Form × ℕ) ↦ acc + weights.getD fs.2 0 * formE fs.1 fun j ↦ ev x (col j)) (ev x a)
  | [], _ => rfl
  | (f, s) :: l, a => by
    rw [List.foldl_cons, List.foldl_cons, ev_fpP_aux x weights col l, map_add, map_mul, ev_C, ev_formP]

/-- **A tuple's fingerprint at the columns' polynomials evaluates to the fingerprint at their values.** -/
theorem ev_fpP (x : E) (tuple : List Form) (weights : Array E) (beta : E) (col : ℕ → Poly) :
    ev x (fpP tuple weights beta col) = fpE tuple weights beta fun j ↦ ev x (col j) := by
  unfold fpP fpE
  exact (ev_fpP_aux x weights col _ _).trans (by rw [ev_C])

theorem ev_list_getD (x : E) (l : List Poly) (k : ℕ) : ev x (l.getD k 0) = (l.map (ev x)).getD k 0 := by
  rw [← map_zero (ev x), List.getD_map]

/-- The memory cell's fingerprint at polynomials. -/
theorem ev_memoryFpP (x : E) (weights : Array E) (beta : E) (address count : Poly) (limbs : List Poly) :
    ev x (memoryFpP weights beta address count limbs) =
      memoryFp weights beta (ev x address) (ev x count) (limbs.map (ev x)) := by
  unfold memoryFpP memoryFp
  rw [foldl_add_eq, foldl_add_eq, map_add, map_list_sum, List.map_map]
  simp only [map_add, map_mul, ev_C, Function.comp_def, ev_list_getD]

/-- The instruction's fingerprint at polynomials. -/
theorem ev_bytecodeFpP (x : E) (weights : Array E) (beta : E) (slot : ℕ → Poly) :
    ev x (bytecodeFpP weights beta slot) = bytecodeFp weights beta fun s ↦ ev x (slot s) := by
  unfold bytecodeFpP bytecodeFp
  rw [foldl_add_eq, foldl_add_eq, map_add, map_list_sum, List.map_map]
  simp only [map_mul, ev_C, Function.comp_def]

/-! ### The fingerprints the heap divides by are `BadFp`'s -/

theorem foldl_zip_range' {M : Type*} [AddCommMonoid M] {α : Type*} (g : α → ℕ → M) (d : α) :
    ∀ (l : List α) (k : ℕ) (a : M), (l.zip (List.range' k l.length)).foldl (fun acc (fs : α × ℕ) ↦ acc + g fs.1 fs.2) a =
      a + ∑ s ∈ range l.length, g (l.getD s d) (k + s)
  | [], _, a => by simp
  | f :: l, k, a => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons, foldl_zip_range' g d l (k + 1),
      Finset.sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [List.getD_cons_succ, show k + 1 + s = k + (s + 1) by ring]

theorem fpE_eq_sum (tuple : List Form) (weights : Array E) (beta : E) (col : ℕ → E) :
    fpE tuple weights beta col = beta + ∑ s ∈ range tuple.length, weights.getD s 0 * formE (tuple.getD s []) col := by
  unfold fpE
  rw [List.range_eq_range']
  exact (foldl_zip_range' (fun f s ↦ weights.getD s 0 * formE f col) [] tuple 0 beta).trans (by simp)

theorem sum_map_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).sum = ∑ k ∈ range n, g k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem fpOf_eq_sum (weights : Array E) (beta : E) (tau : List E) :
    fpOf weights beta tau = beta + ∑ s ∈ range 16, weights.getD s 0 * tau.getD s 0 := by
  unfold fpOf
  rw [foldl_add_eq, sum_map_range]


theorem formE_nil (col : ℕ → E) : formE [] col = 0 := rfl

theorem getD_tupleAt (tuple : List Form) (col : ℕ → E) {s : ℕ} (hs : s < 16) :
    (tupleAt tuple col).getD s 0 = formE (tuple.getD s []) col := by
  simp only [tupleAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs, Option.map_some,
    Option.getD_some]

/-- **A tuple of at most `16` forms**: its fingerprint is `fpOf` of its coordinates (`tupleAt`). -/
theorem fpE_eq_fpOf {tuple : List Form} (hl : tuple.length ≤ 16) (weights : Array E) (beta : E) (col : ℕ → E) :
    fpE tuple weights beta col = fpOf weights beta (tupleAt tuple col) := by
  rw [fpE_eq_sum, fpOf_eq_sum]
  refine congrArg (beta + ·) ?_
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hl) fun s _ hs ↦ ?_]
  · refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hs16 : s < 16 := lt_of_lt_of_le (Finset.mem_range.mp hs) hl
    rw [getD_tupleAt tuple col hs16]
  · have hs16 : s < 16 := Finset.mem_range.mp ‹_›
    have hge : tuple.length ≤ s := by simpa using hs
    rw [getD_tupleAt tuple col hs16, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none,
      formE_nil, mul_zero]

theorem range16 : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl

theorem range3 : List.range 3 = [0, 1, 2] := rfl

/-- **A memory cell's fingerprint is `fpOf` of its tuple.** -/
theorem memoryFp_eq_fpOf (tr : Trace) (weights : Array E) (beta : E) (i : ℕ) (count : E) :
    memoryFp weights beta (ofK (LeanVM.Parameters.gpow i)) count
        ((List.range 3).map fun k ↦ ofK ((tr.memory.getD k #[]).getD i 0)) =
      fpOf weights beta (memoryTuple tr i count) := by
  unfold memoryFp fpOf memoryTuple
  simp only [range16, range3, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.replicate_succ, List.replicate_zero, List.getD_cons_zero, List.getD_cons_succ]
  ring

/-- **An instruction's fingerprint is `fpOf` of its tuple.** -/
theorem bytecodeFp_eq_fpOf (tr : Trace) (weights : Array E) (beta : E) (i : ℕ) (count : E) :
    bytecodeFp weights beta (fun s ↦ bytecodeSlot tr i s count) = fpOf weights beta (bytecodeTuple tr i count) := by
  unfold bytecodeFp fpOf bytecodeTuple
  simp only [range16, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ]

/-! ### Degrees -/

theorem natDegree_foldl_mul_le (g : ℕ → Poly) (n : ℕ) (hg : ∀ j, (tp (g j)).natDegree ≤ n) :
    ∀ (mono : List ℕ) (a : Poly), (tp (mono.foldl (fun p j ↦ p * g j) a)).natDegree ≤
      (tp a).natDegree + mono.length * n
  | [], a => by simp
  | j :: mono, a => by
    rw [List.foldl_cons]
    refine (natDegree_foldl_mul_le g n hg mono _).trans ?_
    rw [tp_mul, List.length_cons]
    have := (natDegree_mul_le (p := tp a) (q := tp (g j))).trans (Nat.add_le_add_left (hg j) _)
    nlinarith

theorem natDegree_foldl_add_le {α : Type*} (g : α → Poly) (B : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, (tp (g x)).natDegree ≤ B) → ∀ (a : Poly), (tp a).natDegree ≤ B →
      (tp (l.foldl (fun acc x ↦ acc + g x) a)).natDegree ≤ B
  | [], _, _, ha => ha
  | x :: l, hg, a, ha => by
    rw [List.foldl_cons]
    refine natDegree_foldl_add_le g B l (fun y hy ↦ hg y (List.mem_cons_of_mem _ hy)) _ ?_
    rw [tp_add]
    exact (natDegree_add_le _ _).trans (max_le ha (hg x (List.mem_cons_self ..)))

/-- One form's contribution to `tupleDegree`: the longest monomial with a nonzero coefficient. -/
def formDeg (d : ℕ) (f : Form) : ℕ := f.foldl (fun d (mc : List ℕ × E) ↦ if mc.2 = 0 then d else max d mc.1.length) d

theorem tupleDegree_eq (tuple : List Form) : tupleDegree tuple = max 1 (tuple.foldl formDeg 0) := rfl

theorem le_formDeg (f : Form) : ∀ d, d ≤ formDeg d f := by
  induction f with
  | nil => intro d; exact le_rfl
  | cons mc f ih =>
    intro d
    unfold formDeg
    rw [List.foldl_cons]
    refine le_trans ?_ (ih _)
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _

theorem mem_le_formDeg (f : Form) : ∀ d, ∀ mc ∈ f, mc.2 ≠ 0 → mc.1.length ≤ formDeg d f := by
  induction f with
  | nil => intro d mc hmc; exact absurd hmc List.not_mem_nil
  | cons mc' f ih =>
    intro d mc hmc hc
    unfold formDeg
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmc with rfl | hmc
    · refine le_trans ?_ (le_formDeg f _)
      rw [ite_neg_of hc]
      exact le_max_right _ _
    · exact ih _ mc hmc hc

theorem le_foldl_formDeg : ∀ (tuple : List Form) (d : ℕ), d ≤ tuple.foldl formDeg d
  | [], _ => le_rfl
  | f :: tuple, d => (le_formDeg f d).trans (le_foldl_formDeg tuple _)

theorem mem_le_foldl_formDeg : ∀ (tuple : List Form) (d : ℕ), ∀ f ∈ tuple, ∀ mc ∈ f, mc.2 ≠ 0 →
    mc.1.length ≤ tuple.foldl formDeg d
  | [], _, _, hf, _, _, _ => absurd hf List.not_mem_nil
  | f' :: tuple, d, f, hf, mc, hmc, hc => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (mem_le_formDeg f d mc hmc hc).trans (le_foldl_formDeg tuple _)
    · exact mem_le_foldl_formDeg tuple _ f hf mc hmc hc

theorem natDegree_formP_le (f : Form) (col : ℕ → Poly) (n D : ℕ) (hcol : ∀ j, (tp (col j)).natDegree ≤ n)
    (hf : ∀ mc ∈ f, mc.2 ≠ 0 → mc.1.length ≤ D) : (tp (formP f col)).natDegree ≤ D * n := by
  unfold formP
  refine natDegree_foldl_add_le (fun (mc : List ℕ × E) ↦ pC mc.2 * mc.1.foldl (fun p j ↦ p * col j) 1) _ f
    (fun mc hmc ↦ ?_) 0 (by rw [tp_zero, natDegree_zero]; exact Nat.zero_le _)
  by_cases hc : mc.2 = 0
  · show (tp (pC mc.2 * _)).natDegree ≤ _
    rw [hc, tp_mul, tp_C, C_0, zero_mul, natDegree_zero]; exact Nat.zero_le _
  · show (tp (pC mc.2 * _)).natDegree ≤ _
    rw [tp_mul, tp_C]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_foldl_mul_le col n hcol mc.1 1).trans ?_
    rw [tp_one, natDegree_one, zero_add]
    exact Nat.mul_le_mul_right n (hf mc hmc hc)

/-- **A tuple's fingerprint at columns of degree `≤ n` has degree `≤ tupleDegree · n`.** -/
theorem natDegree_fpP_le (tuple : List Form) (weights : Array E) (beta : E) (col : ℕ → Poly) (n : ℕ)
    (hcol : ∀ j, (tp (col j)).natDegree ≤ n) : (tp (fpP tuple weights beta col)).natDegree ≤ tupleDegree tuple * n := by
  unfold fpP
  refine natDegree_foldl_add_le (fun (fs : Form × ℕ) ↦ pC (weights.getD fs.2 0) * formP fs.1 col) _ _
    (fun fs hfs ↦ ?_) _ (by rw [tp_C, natDegree_C]; exact Nat.zero_le _)
  show (tp (pC _ * formP fs.1 col)).natDegree ≤ _
  rw [tp_mul, tp_C]
  refine (natDegree_C_mul_le _ _).trans (natDegree_formP_le _ col n _ hcol fun mc hmc hc ↦ ?_)
  rw [tupleDegree_eq]
  exact (mem_le_foldl_formDeg tuple 0 fs.1 (List.of_mem_zip hfs).1 mc hmc hc).trans (le_max_right _ _)

theorem one_le_tupleDegree (tuple : List Form) : 1 ≤ tupleDegree tuple := le_max_left _ _


/-! ### `Z_act`, `Z_pad` -/

theorem tp_foldl_ite_mul (c : ℕ → Prop) [DecidablePred c] (f : ℕ → Poly) :
    ∀ (n : ℕ) (a : Poly), tp ((List.range n).foldl (fun acc b ↦ if c b then acc * f b else acc) a) =
      tp a * ∏ b ∈ (range n).filter c, tp (f b)
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.range_add_one,
      Finset.filter_insert]
    by_cases hn : c n
    · rw [ite_pos_of hn, ite_pos_of hn, tp_mul, tp_foldl_ite_mul c f n a,
        Finset.prod_insert (by simp), mul_comm (tp (f n)), mul_assoc]
    · rw [ite_neg_of hn, ite_neg_of hn, tp_foldl_ite_mul c f n a]

theorem tp_foldl_ite_mul' (c : ℕ → Prop) [DecidablePred c] (f : ℕ → Poly) (n : ℕ) (a : Poly) :
    tp ((List.range n).foldl (fun acc b ↦ if c b then acc else acc * f b) a) =
      tp a * ∏ b ∈ (range n).filter (fun b ↦ ¬ c b), tp (f b) := by
  have : (fun acc b ↦ if c b then acc else acc * f b) = (fun acc b ↦ if ¬ c b then acc * f b else acc) := by
    funext acc b
    by_cases h : c b
    · rw [ite_pos_of h, ite_neg_of (not_not.mpr h)]
    · rw [ite_neg_of h, ite_pos_of h]
  rw [this, tp_foldl_ite_mul]

theorem tp_cosetP (b a : ℕ) : tp (cosetP b a) = wP b + C (pointE a) := by rw [cosetP, tp_add, tp_wPoly, tp_C]

/-- **The prover's `Z_act` is the domain's.** -/
theorem tp_zActP (rows r : ℕ) : tp (zActP rows r) = Domain.zActP rows r := by
  unfold zActP Domain.zActP
  by_cases hf : rows = 2 ^ r
  · rw [ite_pos_of hf, ite_pos_of hf, tp_wPoly]
  · rw [ite_neg_of hf, ite_neg_of hf, tp_foldl_ite_mul, tp_one, one_mul]
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    rw [tp_cosetP]
    rfl

theorem activePositions_all (r : ℕ) :
    (activePositions (2 ^ r - 1) r).toFinset = range (2 ^ r - 1) := by
  ext i
  rw [List.mem_toFinset, Finset.mem_range]
  constructor
  · intro hi
    have hlt := Domain.lt_of_mem_activePositions hi
    have ha := (Domain.mem_activePositions_iff hlt).mp hi
    unfold isActive at ha
    rw [ite_neg_of (by have := Nat.one_le_two_pow (n := r); omega)] at ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    omega
  · intro hi
    have hlt : i < 2 ^ r := by omega
    refine (Domain.mem_activePositions_iff hlt).mpr ?_
    unfold isActive
    rw [ite_neg_of (by have := Nat.one_le_two_pow (n := r); omega)]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (Domain.log2_gap_lt hlt (by omega))

theorem CharTwo_X_add_C (a : E) : (X + C a : E[X]) = X - C a := by
  rw [sub_eq_add_neg, CharTwo.neg_eq]

/-- **All the cosets' factors and the last row's make `w_r`.** -/
theorem prod_cosets_mul_last {r : ℕ} (hr : r ≤ 31) :
    (∏ b ∈ range r, (wP b + C (cosetOffset r b))) * (X + C (pointE (2 ^ r - 1))) = wP r := by
  have h1 : ∏ b ∈ range r, (wP b + C (cosetOffset r b)) = Domain.zActP (2 ^ r - 1) r := by
    unfold Domain.zActP
    rw [ite_neg_of (by have := Nat.one_le_two_pow (n := r); omega),
      Finset.filter_true_of_mem fun b hb ↦ by
        rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (Finset.mem_range.mp hb)]
  have h2 : 2 ^ r = 2 ^ r - 1 + 1 := by have := Nat.one_le_two_pow (n := r); omega
  rw [h1, Domain.zActP_eq_linProd hr (by omega), activePositions_all r, Domain.wP_eq_linProd (by omega),
    CharTwo_X_add_C, Domain.linProd, Domain.linProd, h2]
  simp only [Nat.add_sub_cancel]
  rw [Finset.prod_range_succ]

/-- **The prover's `Z_pad` is the domain's** (`w_r /ₘ Z_act`), `r ≤ 31`, `rows ≤ 2^r`. -/
theorem tp_zPadP {rows r : ℕ} (hr : r ≤ 31) : tp (zPadP rows r) = Domain.zPadP rows r := by
  unfold zPadP Domain.zPadP
  by_cases hf : rows = 2 ^ r
  · rw [ite_pos_of hf, tp_one]
    unfold Domain.zActP
    rw [ite_pos_of hf]
    have := mul_divByMonic_cancel_left (1 : E[X]) (wP_monic r)
    rw [mul_one] at this
    exact this.symm
  · rw [ite_neg_of hf, tp_foldl_ite_mul', tp_cosetP]
    have hprod : Domain.zActP rows r * ((wP 0 + C (pointE (2 ^ r - 1))) *
        ∏ b ∈ (range r).filter (fun b ↦ ¬ rows.testBit b = true), tp (cosetP b (2 ^ (r - b) - 2))) = wP r := by
      unfold Domain.zActP
      rw [ite_neg_of hf, wP_zero]
      have e : ∀ b, tp (cosetP b (2 ^ (r - b) - 2)) = wP b + C (cosetOffset r b) := fun b ↦ tp_cosetP _ _
      simp only [e]
      rw [show ∀ (A P Q : E[X]), A * (P * Q) = (A * Q) * P from fun A P Q ↦ by ring]
      rw [Finset.prod_filter_mul_prod_filter_not, prod_cosets_mul_last hr]
    rw [← hprod, mul_divByMonic_cancel_left _ (Domain.zActP_monic rows r)]

end UniComplete.AlgH
