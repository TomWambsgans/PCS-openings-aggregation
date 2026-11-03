-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Eval

/-!
# The identities' degrees (`DegBoundP`)

Every polynomial of `polysOf` is bounded from its construction, symbolically in the shape's numbers;
no polynomial is evaluated.

* **Columns** (`ndeg_colPoly`): a column's polynomial at a polynomial point has degree at most the sum
  of its point's coordinates' degrees over its limb's variables, which `StackLayout.new` sets to the
  column's (`c1_limbs`, `c2_limbs`, `setup_limbs`): at the digits `w_l` (degree `2^l`) a column of `v`
  variables has degree below `2^v`; a heap block's restriction `R_b` below `2^r`; `q_flock`'s slot at
  `y(X)` at most `h_B 2^(h_B − 1)` (`y_l = Σ_{m<h_B} a_{l,m} X^(2^m)`).
* **Products** (`ndeg_listProd`): a table's pull product at most `Σ_j deg(τ_j) 2^r`, `deg(τ_j)` its tuple's
  largest monomial (`fdeg`, the kernel reads the six tables' monomials, not their coefficients:
  `tables_pullDeg`, `tables_pushDeg`); `Z_act` below `2^(r+1)`; the lift `w_m / w_r` at most `2^m`.
* **Quotients** (`ndeg_quotP`, `chunks_sum_le`): `Q_0 + w_{e_0}(Q_1 + w_{e_1} Q_2)` has degree at most
  `Σ_c 2^(e_c)`, and `chunks` covers `n` coefficients with `Σ_c 2^(e_c) ≤ 5n/4` (the greedy chunks,
  the third rounded up).
* **`degBound_of`**: the degrees' sum is at most `treeB + wB + Σ_b blockB b` at every shape whose
  heap is `HeapGood`; **`degBound_reference`**: at most `50,708,397 < 2^25.6` at the reference shape
  (the tree `2^24 + 2`, `Z_bad P_W` `5,636,097`, the six tables' leaves `22,265,774`, the memory's
  `4,718,590`, the bytecode's `1,179,646`, the unused block's `2^17`), by `norm_num`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial UniSound.Ids.Eval

/-! ## Degrees of sums and products -/

theorem ndeg_listSum (l : List (Polynomial E)) (B : ℕ) (h : ∀ p ∈ l, p.natDegree ≤ B) :
    l.sum.natDegree ≤ B := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.sum_cons]
    exact (natDegree_add_le _ _).trans (max_le (h p (List.mem_cons_self ..))
      (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq)))

theorem ndeg_listProd : ∀ l : List (Polynomial E), l.prod.natDegree ≤ (l.map natDegree).sum
  | [] => by simp
  | p :: l => by
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact natDegree_mul_le.trans (Nat.add_le_add_left (ndeg_listProd l) _)

theorem ndeg_add {p q : Polynomial E} {B : ℕ} (hp : p.natDegree ≤ B) (hq : q.natDegree ≤ B) :
    (p + q).natDegree ≤ B :=
  (natDegree_add_le _ _).trans (max_le hp hq)

theorem ndeg_mul {p q : Polynomial E} {a b B : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b)
    (h : a + b ≤ B) : (p * q).natDegree ≤ B :=
  natDegree_mul_le.trans ((Nat.add_le_add hp hq).trans h)

theorem ndeg_C (a : E) (B : ℕ) : (C a).natDegree ≤ B := by simp

theorem ndeg_Cmul {a : E} {p : Polynomial E} {B : ℕ} (hp : p.natDegree ≤ B) : (C a * p).natDegree ≤ B :=
  (natDegree_C_mul_le _ _).trans hp

theorem list_sum_map_le {α : Type} (l : List α) (f g : α → ℕ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..)) (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-! ## Columns at polynomial points -/

/-- **A column's polynomial**: at most the point's coordinates' degrees summed over each limb's
variables. -/
theorem ndeg_colPoly (L : StackLayout) (V : ℕ) (St : Stk) (col : Column) (pt : ℕ → Polynomial E) (B : ℕ)
    (h : ∀ b ∈ L.limbs col, ∑ l ∈ range b.2.1, (pt l).natDegree ≤ B) :
    (colPoly L V St col pt).natDegree ≤ B := by
  unfold colPoly
  refine ndeg_listSum _ _ fun p hp ↦ ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
  exact ndeg_Cmul ((natDegree_mlP_le _ _ _).trans (h b hb))

theorem sum_pow_add_le (v s : ℕ) : ∑ l ∈ range v, 2 ^ (l + s) ≤ 2 ^ (v + s) := by
  have h := sum_two_pow_lt v
  have e : ∑ l ∈ range v, 2 ^ (l + s) = (∑ l ∈ range v, 2 ^ l) * 2 ^ s := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ ↦ pow_add 2 l s
  rw [e, pow_add]
  exact Nat.mul_le_mul_right _ h.le

/-- Coordinates of degree at most `2^(l+s)`: the sum over `v` variables at most `2^(v+s)`. -/
theorem sum_deg_pow (pt : ℕ → Polynomial E) (v s : ℕ) (h : ∀ l < v, (pt l).natDegree ≤ 2 ^ (l + s)) :
    ∑ l ∈ range v, (pt l).natDegree ≤ 2 ^ (v + s) :=
  (Finset.sum_le_sum fun l hl ↦ h l (mem_range.mp hl)).trans (sum_pow_add_le v s)

/-- Coordinates of degree `2^l` below `r` and constant above: the sum at most `2^r`. -/
theorem sum_deg_below (pt : ℕ → Polynomial E) (v r : ℕ)
    (h : ∀ l < v, (pt l).natDegree ≤ if l < r then 2 ^ l else 0) :
    ∑ l ∈ range v, (pt l).natDegree ≤ 2 ^ r := by
  refine (Finset.sum_le_sum fun l hl ↦ h l (mem_range.mp hl)).trans ?_
  rw [← Finset.sum_filter]
  refine (Finset.sum_le_sum_of_subset fun l hl ↦ ?_).trans (sum_two_pow_lt r).le
  simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
  exact hl.2

theorem digit_le (l : ℕ) : (digitP l).natDegree ≤ 2 ^ (l + 0) := by
  rw [add_zero]; exact natDegree_digitP l

/-- **A `C1` column** at the digits: below `2^v`, `v` its variables. -/
theorem ndeg_c1P (S : Shape) (c : Stk) (col : Column) : (c1P S c col).natDegree ≤ 2 ^ c1Vars S col := by
  unfold c1P
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [(c1_limbs S col b hb).1, ← add_zero (c1Vars S col)]
  exact sum_deg_pow digitP _ 0 fun l _ ↦ digit_le l

/-- **A `C2` column** at a point of coordinates of degree at most `2^(l+s)`. -/
theorem ndeg_c2P (S : Shape) (c2 : Stk) (col : Column) (pt : ℕ → Polynomial E) (s : ℕ)
    (h : ∀ l, (pt l).natDegree ≤ 2 ^ (l + s)) :
    (c2P S c2 col pt).natDegree ≤ 2 ^ (c2Vars S col + s) := by
  unfold c2P
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [(c2_limbs S col b hb).1]
  exact sum_deg_pow pt _ s fun l _ ↦ h l

theorem ndeg_c2P_digits (S : Shape) (c2 : Stk) (col : Column) :
    (c2P S c2 col digitP).natDegree ≤ 2 ^ c2Vars S col := by
  simpa using ndeg_c2P S c2 col digitP 0 digit_le

/-- **The restriction `R_b`**: `T` at the block's mixed point, below `2^r`. -/
theorem ndeg_restr (S : Shape) (c2 : Stk) (b : Block) : (c2P S c2 .heap (mixP b)).natDegree ≤ 2 ^ b.r := by
  unfold c2P
  refine ndeg_colPoly _ _ _ _ _ _ fun bl _ ↦ sum_deg_below _ _ _ fun l _ ↦ ?_
  unfold mixP
  split_ifs
  · exact ndeg_add (natDegree_digitP l) (ndeg_C _ _)
  · simp

/-- The setup's addresses at the digits. -/
theorem ndeg_suP_address (S : Shape) (st : Stk) : (suP S st .address digitP).natDegree ≤ 2 ^ S.logMemory := by
  unfold suP
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [(setup_limbs S .address b hb).2.1 rfl, ← add_zero S.logMemory]
  exact sum_deg_pow digitP _ 0 fun l _ ↦ digit_le l

/-- The setup's bytecode tuples at `(α, w)`: below `2^lb`. -/
theorem ndeg_suP_tuple (S : Shape) (st : Stk) (alphas : List E) :
    (suP S st .bytecodeTuple (fun l ↦ if l < 4 then C (alphas.getD l 0) else digitP (l - 4))).natDegree ≤
      2 ^ S.logBytecode := by
  unfold suP
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [(setup_limbs S .bytecodeTuple b hb).1 rfl,
    show S.logBytecode + 4 = 4 + S.logBytecode from add_comm _ _, Finset.sum_range_add]
  have h1 : ∑ x ∈ range 4, (if x < 4 then C (alphas.getD x 0) else digitP (x - 4)).natDegree = 0 :=
    Finset.sum_eq_zero fun x hx ↦ by rw [ite_eq_left (mem_range.mp hx), natDegree_C]
  rw [h1, zero_add]
  refine (Finset.sum_le_sum fun l _ ↦ ?_).trans (sum_two_pow_lt _).le
  rw [ite_eq_right (show ¬ 4 + l < 4 by omega), show 4 + l - 4 = l by omega]
  exact natDegree_digitP l

/-- A coordinate functional `y_l = Σ_m a_{l,m} X^(2^m)`. -/
theorem ndeg_yP (a : Array (Array K)) (l : ℕ) : (yP a l).natDegree ≤ 2 ^ (a.size - 1) := by
  unfold yP
  refine ndeg_listSum _ _ fun p hp ↦ ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hm
  exact ndeg_Cmul ((natDegree_X_pow_le _).trans (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- **`q_flock`'s slot at `y(X)`**: at most `h_B 2^(h_B − 1)`. -/
theorem ndeg_slotP (S : Shape) (c : Stk) (slot : ℕ) :
    (slotP S c slot).natDegree ≤ S.heights.getD opBlake2s 0 * 2 ^ (S.heights.getD opBlake2s 0 - 1) := by
  unfold slotP
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [(c1_limbs S .qflock b hb).1]
  show ∑ l ∈ range (S.heights.getD opBlake2s 0 + 8), _ ≤ _
  rw [show S.heights.getD opBlake2s 0 + 8 = 8 + S.heights.getD opBlake2s 0 from add_comm _ _,
    Finset.sum_range_add]
  have h1 : ∑ x ∈ range 8, (if x < 8 then C (bitE slot x)
      else yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) (x - 8)).natDegree = 0 :=
    Finset.sum_eq_zero fun x hx ↦ by rw [ite_eq_left (mem_range.mp hx), natDegree_C]
  rw [h1, zero_add]
  refine (Finset.sum_le_sum (g := fun _ ↦ 2 ^ (S.heights.getD opBlake2s 0 - 1)) fun l _ ↦ ?_).trans
    (by simp)
  rw [ite_eq_right (show ¬ 8 + l < 8 by omega)]
  have := ndeg_yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) (8 + l - 8)
  rwa [coordinateFunctionals_size] at this

/-! ## Lifts, `Z_act`, `Z_bad` -/

theorem range'_pow_sum (r : ℕ) : ∀ k, ((List.range' r k).map (2 ^ ·)).sum + 2 ^ r = 2 ^ (r + k)
  | 0 => by simp
  | k + 1 => by
    rw [List.range'_succ, List.map_cons, List.sum_cons]
    have := range'_pow_sum (r + 1) k
    rw [show r + (k + 1) = r + 1 + k by ring, ← this, pow_succ]
    ring

theorem digit_one_le (j : ℕ) : (digitP j + 1).natDegree ≤ 2 ^ j :=
  ndeg_add (natDegree_digitP j) (by simp)

/-- **The lift `w_m / w_r`**: at most `2^m`. -/
theorem ndeg_liftP (r m : ℕ) : (liftP r m).natDegree ≤ 2 ^ m := by
  unfold liftP
  refine (ndeg_listProd _).trans ?_
  rw [List.map_map]
  refine (list_sum_map_le _ _ (2 ^ ·) fun j _ ↦ digit_one_le j).trans ?_
  by_cases hrm : r ≤ m
  · have h := range'_pow_sum r (m - r)
    have e : r + (m - r) = m := by omega
    rw [e] at h
    have := Nat.two_pow_pos r
    omega
  · rw [show m - r = 0 by omega]
    simp

theorem ndeg_zFold (F : ℕ → Polynomial E) (hF : ∀ b, (F b).natDegree ≤ 2 ^ b) :
    ∀ (l : List ℕ) (P : Polynomial E) (A : ℕ), P.natDegree ≤ A →
      (l.foldl (fun prod b ↦ prod * F b) P).natDegree ≤ A + (l.map (2 ^ ·)).sum
  | [], P, A, h => by simpa using h
  | b :: l, P, A, h => by
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ← add_assoc]
    exact ndeg_zFold F hF l _ _ (ndeg_mul h (hF b) le_rfl)

/-- **`Z_act`**: below `2^(r+1)`. -/
theorem ndeg_zActP (bits : List E) (r : ℕ) : (zActP bits r).natDegree ≤ 2 ^ (r + 1) := by
  unfold zActP
  have hF : ∀ b, (1 + C (bits.getD b 0) * (digitP b + C (cosetOffset r b + 1))).natDegree ≤ 2 ^ b :=
    fun b ↦ ndeg_add (by simp) (ndeg_Cmul (ndeg_add (natDegree_digitP b) (ndeg_C _ _)))
  have h0 : (1 + C (bits.getD r 0) * (digitP r + 1)).natDegree ≤ 2 ^ r :=
    ndeg_add (by simp) (ndeg_Cmul (digit_one_le r))
  refine (ndeg_zFold _ hF (List.range r) _ _ h0).trans ?_
  have h := range'_pow_sum 0 r
  rw [zero_add, pow_zero] at h
  rw [List.range_eq_range', pow_succ]
  omega

/-- **`Z_bad = (y_0 + X)(y_0 + p_0)`**: at most `2 · 2^(h_B − 1)`. -/
theorem ndeg_zBad (S : Shape) (p0 : E) :
    (zBad S p0).natDegree ≤ 2 * 2 ^ (S.heights.getD opBlake2s 0 - 1) := by
  unfold zBad
  have hy := ndeg_yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) 0
  rw [coordinateFunctionals_size] at hy
  have h1 : (1 : ℕ) ≤ 2 ^ (S.heights.getD opBlake2s 0 - 1) := Nat.one_le_two_pow
  exact ndeg_mul (ndeg_add hy (natDegree_X_le.trans h1)) (ndeg_add hy (ndeg_C _ _)) (by omega)

/-! ## Forms, tuples, fingerprint products -/

/-- A form's largest monomial. -/
def formMax (f : Form) : ℕ := (f.map fun mc ↦ mc.1.length).foldr max 0

/-- **A tuple's degree bound**: its largest monomial, at least `1` (the verifier's `tupleDegree` without
the zero-coefficient check). -/
def fdeg (tup : List Form) : ℕ := max 1 ((tup.map formMax).foldr max 0)

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem le_fdeg (tup : List Form) : ∀ f ∈ tup, ∀ mc ∈ f, mc.1.length ≤ fdeg tup := fun f hf mc hmc ↦
  (le_foldr_max (l := f.map fun mc ↦ mc.1.length) (List.mem_map.mpr ⟨mc, hmc, rfl⟩)).trans
    ((le_foldr_max (l := tup.map formMax) (List.mem_map.mpr ⟨f, hf, rfl⟩)).trans (le_max_right _ _))

theorem ndeg_formP (f : Form) (cols : ℕ → Polynomial E) (B k : ℕ) (hc : ∀ i, (cols i).natDegree ≤ B)
    (hk : ∀ mc ∈ f, mc.1.length ≤ k) : (formP f cols).natDegree ≤ k * B := by
  unfold formP
  refine ndeg_listSum _ _ fun p hp ↦ ?_
  obtain ⟨⟨m, cf⟩, hm, rfl⟩ := List.mem_map.mp hp
  have hl := hk _ hm
  rcases m with _ | ⟨i, _ | ⟨j, _ | ⟨_, _⟩⟩⟩
  · simp
  · simp only [List.length_cons, List.length_nil] at hl
    exact ndeg_Cmul ((hc i).trans (Nat.le_mul_of_pos_left B (by omega)))
  · simp only [List.length_cons, List.length_nil] at hl
    exact ndeg_mul (ndeg_Cmul (hc i)) (hc j) (by
      have := Nat.mul_le_mul_right B hl
      omega)
  · simp

theorem ndeg_tupleP (tuple : List Form) (weights : Array E) (cols : ℕ → Polynomial E) (B k : ℕ)
    (hc : ∀ i, (cols i).natDegree ≤ B) (hk : ∀ f ∈ tuple, ∀ mc ∈ f, mc.1.length ≤ k) :
    (tupleP tuple weights cols).natDegree ≤ k * B := by
  unfold tupleP
  refine ndeg_listSum _ _ fun p hp ↦ ?_
  obtain ⟨⟨f, s⟩, hq, rfl⟩ := List.mem_map.mp hp
  exact ndeg_Cmul (ndeg_formP _ cols B k hc (hk _ (List.of_mem_zip hq).1))

/-- A table's pull tuples' degrees, summed. -/
def pullDeg (tab : Table) : ℕ := ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ fdeg fl.1).sum

/-- A table's push tuples' degrees, summed. -/
def pushDeg (tab : Table) : ℕ := ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ fdeg fl.2).sum

/-- **A table's pull product**: at most `pullDeg · B`, its columns of degree at most `B`. -/
theorem ndeg_pullP (tab : Table) (weights : Array E) (beta : E) (cols : ℕ → Polynomial E) (B : ℕ)
    (hc : ∀ i, (cols i).natDegree ≤ B) : (pullP tab weights beta cols).natDegree ≤ pullDeg tab * B := by
  unfold pullP pullDeg
  refine (ndeg_listProd _).trans ?_
  rw [List.map_map, ← List.sum_map_mul_right]
  exact list_sum_map_le _ _ _ fun fl _ ↦ ndeg_add (ndeg_C _ _) (ndeg_tupleP _ _ _ B _ hc (le_fdeg fl.1))

/-- **A table's push product.** -/
theorem ndeg_pushP (tab : Table) (weights : Array E) (beta : E) (cols : ℕ → Polynomial E) (B : ℕ)
    (hc : ∀ i, (cols i).natDegree ≤ B) : (pushP tab weights beta cols).natDegree ≤ pushDeg tab * B := by
  unfold pushP pushDeg
  refine (ndeg_listProd _).trans ?_
  rw [List.map_map, ← List.sum_map_mul_right]
  exact list_sum_map_le _ _ _ fun fl _ ↦ ndeg_add (ndeg_C _ _) (ndeg_tupleP _ _ _ B _ hc (le_fdeg fl.2))

/-- The verifier's leaf degrees are at most the tuples' monomials'. -/
theorem tableDegrees_le' (tab : Table) :
    (tableDegrees tab).1 ≤ 1 + pullDeg tab ∧ (tableDegrees tab).2 ≤ pushDeg tab := by
  rw [tableDegrees_eq]
  refine ⟨Nat.add_le_add_left (list_sum_map_le _ _ _ fun fl _ ↦
    tupleDegree_le _ _ (le_max_left _ _) (le_fdeg fl.1)) 1, ?_⟩
  rw [zero_add]
  exact list_sum_map_le _ _ _ fun fl _ ↦ tupleDegree_le _ _ (le_max_left _ _) (le_fdeg fl.2)

/-! ## The six tables, as the degrees read them (the kernel reads monomials, not coefficients) -/

/-- The tables' pull degrees. -/
def pullL : List ℕ := [8, 8, 4, 8, 8, 20]

/-- The tables' push degrees. -/
def pushL : List ℕ := [8, 8, 4, 8, 9, 20]

/-- The tables' opcodes and counters' numbers. -/
def ocL : List (ℕ × ℕ) := [(0, 4), (1, 4), (2, 2), (3, 4), (4, 4), (5, 10)]

set_option maxRecDepth 100000 in
theorem tables_pullDeg : tables.map pullDeg = pullL := by decide +kernel

set_option maxRecDepth 100000 in
theorem tables_pushDeg : tables.map pushDeg = pushL := by decide +kernel

set_option maxRecDepth 100000 in
theorem tables_oc : tables.map (fun tab ↦ (tab.opcode, tab.countColumns.length)) = ocL := by
  decide +kernel

theorem pullDeg_getD (t : ℕ) : pullDeg (tables.getD t default) = pullL.getD t 0 := by
  rw [← tables_pullDeg, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases tables[t]? <;> rfl

theorem pushDeg_getD (t : ℕ) : pushDeg (tables.getD t default) = pushL.getD t 0 := by
  rw [← tables_pushDeg, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases tables[t]? <;> rfl

theorem mem_ocL {tab : Table} (h : tab ∈ tables) : (tab.opcode, tab.countColumns.length) ∈ ocL := by
  rw [← tables_oc]
  exact List.mem_map.mpr ⟨tab, h, rfl⟩

/-! ## Quotients and their chunks -/

/-- **A quotient from its chunks**: at most `Σ_c 2^(e_c)`. -/
theorem ndeg_quotP (S : Shape) (c2 : Stk) : ∀ (column : ℕ → Column) (sizes : List ℕ),
    (∀ c < sizes.length, (c2P S c2 (column c) digitP).natDegree ≤ 2 ^ sizes.getD c 0) →
    (quotP S c2 column sizes).natDegree ≤ (sizes.map (2 ^ ·)).sum
  | _, [], _ => by simp [quotP]
  | column, e :: rest, h => by
    rw [quotP_cons]
    have h0 := h 0 (by simp)
    have ih := ndeg_quotP S c2 (fun c ↦ column (c + 1)) rest
      (fun c hc ↦ by simpa using h (c + 1) (by simp; omega))
    simp only [List.getD_cons_zero] at h0
    rw [List.map_cons, List.sum_cons]
    exact ndeg_add (h0.trans (Nat.le_add_right _ _)) (ndeg_mul (natDegree_digitP e) ih le_rfl)

/-- `chunks`' potential: `4 Σ 2^e + β(k) · left`, `β = 5, 6, 8, 8, …` after `k` chunks. -/
def cβ : ℕ → ℕ
  | 0 => 5
  | 1 => 6
  | _ + 2 => 8

/-- The potential is at most `5 n`. -/
def ChunkPot (n : ℕ) (s : Array ℕ × ℕ) : Prop :=
  4 * (s.1.toList.map (2 ^ ·)).sum + cβ s.1.size * s.2 ≤ 5 * n

theorem chunkStep_pot (n : ℕ) (s : Array ℕ × ℕ) (x : ℕ) (h : ChunkPot n s) :
    ChunkPot n (chunkStep s x) := by
  unfold ChunkPot at *
  unfold chunkStep
  by_cases h0 : s.2 > 0
  · rw [ite_eq_left h0]
    have hne : s.2 ≠ 0 := by omega
    have hle := Nat.log2_self_le hne
    have hlt := Nat.lt_log2_self (n := s.2)
    rw [pow_succ] at hlt
    split_ifs with hs
    · simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, mul_zero, pow_succ]
      rw [hs.1, show cβ 2 = 8 from rfl] at h
      omega
    · simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Array.size_push]
      rcases Nat.lt_or_ge s.1.size 2 with hlt2 | hge
      · rcases Nat.lt_or_ge s.1.size 1 with hlt1 | hge1
        · have e0 : s.1.size = 0 := by omega
          rw [e0, show cβ 0 = 5 from rfl] at h
          rw [e0, show cβ (0 + 1) = 6 from rfl]
          omega
        · have e1 : s.1.size = 1 := by omega
          rw [e1, show cβ 1 = 6 from rfl] at h
          rw [e1, show cβ (1 + 1) = 8 from rfl]
          omega
      · obtain ⟨k, hk⟩ : ∃ k, s.1.size = k + 2 := ⟨s.1.size - 2, by omega⟩
        rw [hk, show cβ (k + 2) = 8 from rfl] at h
        rw [hk, show cβ (k + 2 + 1) = 8 from rfl]
        omega
  · rw [ite_eq_right h0]
    exact h

/-- **The chunks cover `n` coefficients with `Σ 2^e ≤ 5n/4`.** -/
theorem chunks_sum_le (n : ℕ) : 4 * ((chunks n).map (2 ^ ·)).sum ≤ 5 * n := by
  rw [chunks_eq]
  have key : ∀ (l : List ℕ) (s : Array ℕ × ℕ), ChunkPot n s → ChunkPot n (l.foldl chunkStep s) := by
    intro l
    induction l with
    | nil => intro s h; exact h
    | cons x l ih => intro s h; exact ih _ (chunkStep_pot n s x h)
  have := key (List.range' 0 4) (#[], n) (by simp [ChunkPot, cβ])
  unfold ChunkPot at this
  omega

/-- `5n/4`. -/
def chB (n : ℕ) : ℕ := 5 * n / 4

theorem chB_mono {m n : ℕ} (h : m ≤ n) : chB m ≤ chB n := Nat.div_le_div_right (by omega)

theorem chunks_le_chB (n : ℕ) : ((chunks n).map (2 ^ ·)).sum ≤ chB n := by
  have := chunks_sum_le n
  unfold chB
  omega

/-! ## The constraint quotient's degree -/

/-- A table's bound on the constraint quotient's degree: `max(2^r max(1, counts), r 2^r / 2)`. -/
def cdOf (S : Shape) (p : ℕ × ℕ) : ℕ :=
  max (2 ^ S.heights.getD p.1 0 * max 1 p.2) (S.heights.getD p.1 0 * (2 ^ S.heights.getD p.1 0 / 2))

/-- **The constraint quotient's degree bound.** -/
def cdB (S : Shape) : ℕ := max ((ocL.map (cdOf S)).foldr max 0) (2 ^ S.logMemory)

theorem cdStep_le (S : Shape) (B d : ℕ) (tab : Table) (hd : d ≤ B)
    (hB : cdOf S (tab.opcode, tab.countColumns.length) ≤ B) : cdStep S d tab ≤ B := by
  unfold cdStep cdOf at *
  dsimp only at *
  generalize S.heights.getD tab.opcode 0 = r at hB ⊢
  generalize tab.countColumns.length = cnt at hB ⊢
  generalize 2 ^ r = n at hB ⊢
  generalize hM : max 1 cnt = M at hB
  have hm : 1 ≤ M := hM ▸ le_max_left _ _
  have hm1 : n ≤ n * M := Nat.le_mul_of_pos_right _ hm
  have h2a : (n - 1) * (1 + cnt) ≤ n * (1 + cnt) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h2b : n * (1 + cnt) = n + n * cnt := by ring
  have h2c : n * cnt ≤ n * M := Nat.mul_le_mul_left _ (hM ▸ le_max_right _ _)
  have hB1 := (le_max_left _ _).trans hB
  have hB2 := (le_max_right _ _).trans hB
  have hJ : n - 2 ≤ B := by omega
  have hC : (n - 1) * (1 + cnt) - n ≤ B := by omega
  have hBl : r * (n / 2) - n ≤ B := (Nat.sub_le _ _).trans hB2
  unfold UniStatement.degree
  split_ifs <;> simp only [max_le_iff] <;> omega

theorem constraintDegree_le (S : Shape) : S.constraintDegree ≤ cdB S := by
  have key : ∀ (L : List Table), (∀ tab ∈ L, tab ∈ tables) → ∀ d ≤ (ocL.map (cdOf S)).foldr max 0,
      L.foldl (cdStep S) d ≤ (ocL.map (cdOf S)).foldr max 0 := by
    intro L
    induction L with
    | nil => intro _ d hd; exact hd
    | cons tab L ih =>
      intro hL d hd
      rw [List.foldl_cons]
      have htab : tab ∈ tables := hL tab (List.mem_cons_self ..)
      have hc : cdOf S (tab.opcode, tab.countColumns.length) ≤ (ocL.map (cdOf S)).foldr max 0 :=
        le_foldr_max (List.mem_map.mpr ⟨_, mem_ocL htab, rfl⟩)
      exact ih (fun t ht ↦ hL t (List.mem_cons_of_mem _ ht)) _ (cdStep_le S _ d tab hd hc)
  unfold Shape.constraintDegree cdB
  dsimp only
  exact max_le_max (key tables (fun _ h ↦ h) 0 (Nat.zero_le _)) (Nat.sub_le _ _)

/-! ## The constraints' degrees -/

/-- A table's bound on its constraints' `W_i`: `2^r (1 + max(1, counts))`. -/
def wOf (S : Shape) (p : ℕ × ℕ) : ℕ := 2 ^ S.heights.getD p.1 0 * (1 + max 1 p.2)

/-- **The constraints' `W_i` bound**: the tables', `q_flock`'s slots', the public lines'. -/
def wMax (S : Shape) : ℕ :=
  max (2 ^ S.logMemory) (max (S.heights.getD opBlake2s 0 * 2 ^ (S.heights.getD opBlake2s 0 - 1))
    ((ocL.map (wOf S)).foldr max 0))

theorem wOf_le (S : Shape) {tab : Table} (h : tab ∈ tables) :
    wOf S (tab.opcode, tab.countColumns.length) ≤ wMax S :=
  (le_foldr_max (List.mem_map.mpr ⟨_, mem_ocL h, rfl⟩)).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- **Each constraint `(M_i, W_i)`**: `deg M_i + deg W_i ≤ 2^(r_W) + wMax`. -/
theorem ndeg_constraints (S : Shape) (c1 : Stk) (pw : List E) :
    ∀ mw ∈ constraintsP S c1 pw, mw.1.natDegree + mw.2.natDegree ≤ 2 ^ S.constraintVars + wMax S := by
  intro mw hmw
  unfold constraintsP at hmw
  rcases List.mem_append.mp hmw with hmw | hmw
  · obtain ⟨tab, htab, hmw⟩ := List.mem_flatMap.mp hmw
    have hw := wOf_le S htab
    unfold wOf at hw
    dsimp only at hw
    have hcol : ∀ i, (c1P S c1 (.table tab.opcode i)).natDegree ≤ 2 ^ S.heights.getD tab.opcode 0 :=
      fun i ↦ ndeg_c1P S c1 _
    have hinv : (c1P S c1 (.inverse tab.opcode)).natDegree ≤ 2 ^ S.heights.getD tab.opcode 0 :=
      ndeg_c1P S c1 _
    have hlift := ndeg_liftP (S.heights.getD tab.opcode 0) S.constraintVars
    generalize hH : 2 ^ S.heights.getD tab.opcode 0 = H at hcol hinv hw
    have hm1 : H ≤ H * max 1 tab.countColumns.length :=
      Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.one_pos (le_max_left _ _))
    have hm2 : H * (1 + max 1 tab.countColumns.length) = H + H * max 1 tab.countColumns.length := by ring
    have hm3 : tab.countColumns.length * H ≤ H * max 1 tab.countColumns.length := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (le_max_right _ _)
    unfold tableConstraintsP at hmw
    dsimp only at hmw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmw
    rcases hmw with ((hmw | rfl) | hmw)
    · split_ifs at hmw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmw
        rcases hmw with rfl | rfl
        · refine Nat.add_le_add hlift ?_
          exact ndeg_add ((hcol _).trans (by omega)) (ndeg_mul (hcol _) (hcol _) (by omega))
        · refine Nat.add_le_add hlift ?_
          exact ndeg_mul (hcol _) (ndeg_add (hcol _) ((natDegree_one).le.trans (Nat.zero_le _)))
            (by omega)
      · simp at hmw
    · refine Nat.add_le_add hlift ?_
      have hprod : ((tab.countColumns.map fun c ↦ c1P S c1 (.table tab.opcode c)).prod).natDegree ≤
          tab.countColumns.length * H := by
        refine (ndeg_listProd _).trans ?_
        rw [List.map_map]
        refine (sum_le_of (k := H) fun x hx ↦ ?_).trans (le_of_eq (by rw [List.length_map]))
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        exact hcol c
      exact ndeg_add (ndeg_mul hinv hprod (by omega)) (by simp)
    · split_ifs at hmw
      · obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hmw
        obtain ⟨slot, _, rfl⟩ := Option.map_eq_some_iff.mp hc
        refine Nat.add_le_add hlift (ndeg_add ((hcol c).trans ?_) ((ndeg_slotP S c1 slot).trans ?_))
        · omega
        · unfold wMax
          exact (le_max_left _ _).trans (le_max_right _ _)
      · simp at hmw
  · unfold linesP at hmw
    obtain ⟨lk, _, rfl⟩ := List.mem_map.mp hmw
    refine Nat.add_le_add (ndeg_liftP 1 _) ?_
    have hm : (c1P S c1 (.memory lk.2)).natDegree ≤ 2 ^ S.logMemory := ndeg_c1P S c1 _
    have h1 : (1 : ℕ) ≤ 2 ^ S.logMemory := Nat.one_le_two_pow
    refine (ndeg_add (ndeg_add hm (ndeg_C _ _)) (ndeg_mul natDegree_X_le (natDegree_C _).le
      (by omega))).trans (le_max_left _ _)

/-- **The constraint quotient's identity `Z_bad (Σ γ^i M_i W_i + Q_W w_{r_W})`.** -/
def wB (S : Shape) : ℕ :=
  2 * 2 ^ (S.heights.getD opBlake2s 0 - 1) +
    max (2 ^ S.constraintVars + wMax S) (chB (cdB S + 1) + 2 ^ S.constraintVars)

theorem ndeg_wP (S : Shape) (c1 c2 : Stk) (pw : List E) (gamma p0 : E) :
    (wP S c1 c2 pw gamma p0).natDegree ≤ wB S := by
  unfold wP wB
  refine ndeg_mul (ndeg_zBad S p0) (ndeg_add ?_ ?_) le_rfl
  · refine ndeg_listSum _ _ fun p hp ↦ ?_
    obtain ⟨⟨mw, i⟩, hmw, rfl⟩ := List.mem_map.mp hp
    have := ndeg_constraints S c1 pw mw (List.of_mem_zip hmw).1
    exact (ndeg_mul (ndeg_Cmul le_rfl) le_rfl this).trans (le_max_left _ _)
  · refine (ndeg_mul ((ndeg_quotP S c2 _ _ fun c _ ↦ ndeg_c2P_digits S c2 _).trans
      ((chunks_le_chB _).trans (chB_mono (Nat.add_le_add_right (constraintDegree_le S) 1))))
      (natDegree_digitP _) le_rfl).trans (le_max_right _ _)

/-! ## The tree and the root -/

/-- **The tree's identity**: at most `2^(h+1) + 2`. -/
def treeB (S : Shape) : ℕ := 2 ^ (S.heap.h + 1) + 2

theorem ndeg_treeP (S : Shape) (c2 : Stk) : (treeP S c2).natDegree ≤ treeB S := by
  unfold treeP treeB
  have hA : (c2P S c2 .heap (fun l ↦ digitP (l + 1))).natDegree ≤ 2 ^ (S.heap.h + 1) :=
    ndeg_c2P S c2 .heap _ 1 fun l ↦ natDegree_digitP (l + 1)
  have hB : (c2P S c2 .heap digitP).natDegree ≤ 2 ^ S.heap.h := ndeg_c2P_digits S c2 .heap
  have hB2 : (c2P S c2 .heap (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l)).natDegree ≤
      2 ^ S.heap.h := by
    exact ndeg_c2P S c2 .heap (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l) 0 fun l ↦ by
      split_ifs with h
      · subst h; exact digit_one_le 0
      · exact digit_le l
  have hQ0 : (c2P S c2 (.treeQuotient 0) digitP).natDegree ≤ 2 ^ S.heap.h :=
    ndeg_c2P_digits S c2 (.treeQuotient 0)
  have hQ1 : (c2P S c2 (.treeQuotient 1) digitP).natDegree ≤ 2 ^ 0 :=
    ndeg_c2P_digits S c2 (.treeQuotient 1)
  rw [pow_zero] at hQ1
  have h1 : (digitP 1).natDegree ≤ 2 := natDegree_digitP 1
  have hh := natDegree_digitP S.heap.h
  rw [pow_succ] at hA ⊢
  exact ndeg_add (ndeg_mul h1 (ndeg_add hA (ndeg_mul hB hB2 (by omega))) (by omega))
    (ndeg_mul hh (ndeg_add (hQ0.trans (Nat.le_succ _)) (ndeg_mul hh hQ1 le_rfl)) (by omega))

theorem ndeg_rootP (S : Shape) (c2 : Stk) (weights : Array E) (beta : E) :
    (rootP S c2 weights beta).natDegree ≤ 0 := by
  unfold rootP
  refine ndeg_add (ndeg_Cmul ?_) (ndeg_C _ _)
  unfold c2P
  refine ndeg_colPoly _ _ _ _ _ _ fun _ _ ↦ (Finset.sum_eq_zero fun l _ ↦ ?_).le
  split_ifs <;> simp

/-! ## The heap blocks' leaves -/

/-- **A table's leaf** `R (P w_r + Z²) + Q w_r Z + P' w_r + Z²`, at height `r`, pull and push degrees
`P`, `Q`. -/
def tabB (r P Q : ℕ) : ℕ :=
  max (2 ^ r + max (P * 2 ^ r + 2 ^ r) (2 ^ (r + 2)))
    (max (chB (UniStatement.degree (max (1 + P) Q * (2 ^ r - 1) + (2 ^ r - Shape.leastRows r)) (2 ^ r) + 1) +
        (2 ^ r + 2 ^ (r + 1)))
      (max (Q * 2 ^ r + 2 ^ r) (2 ^ (r + 2))))

/-- **The memory's or the bytecode's leaf** `R P + Q w_r + P'`, its tuples' column of `v` variables. -/
def memB (r v : ℕ) : ℕ := max (2 ^ r + 2 ^ v) (chB (UniStatement.degree (2 * (2 ^ r - 1)) (2 ^ r) + 1) + 2 ^ r)

/-- **A heap block's leaf identity's degree bound.** -/
def blockB (S : Shape) (b : Block) : ℕ :=
  match b.leaves with
  | .unused => 2 ^ b.r
  | .memory => memB b.r S.logMemory
  | .bytecode => memB b.r S.logBytecode
  | .table t => tabB b.r (pullL.getD t 0) (pushL.getD t 0)

theorem ndeg_memPullP (S : Shape) (c1 setup : Stk) (weights : Array E) (beta : E) :
    (memPullP S c1 setup weights beta).natDegree ≤ 2 ^ S.logMemory := by
  unfold memPullP
  have hm : ∀ k, (c1P S c1 (.memory k)).natDegree ≤ 2 ^ S.logMemory := fun k ↦ ndeg_c1P S c1 (.memory k)
  refine ndeg_add (ndeg_add (ndeg_add (ndeg_add (ndeg_C _ _) (ndeg_C _ _))
    (ndeg_Cmul (ndeg_suP_address S setup))) (ndeg_Cmul (hm 3))) (ndeg_listSum _ _ fun p hp ↦ ?_)
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
  exact ndeg_Cmul (hm k)

theorem ndeg_bcPullP (S : Shape) (c1 setup : Stk) (alphas : List E) (weights : Array E) (beta : E) :
    (bcPullP S c1 setup alphas weights beta).natDegree ≤ 2 ^ S.logBytecode := by
  unfold bcPullP
  exact ndeg_add (ndeg_add (ndeg_C _ _) (ndeg_suP_tuple S setup alphas))
    (ndeg_Cmul (ndeg_c1P S c1 .bytecodeFinal))

/-- A leaf quotient's chunks, at the block's leaf degree. -/
theorem ndeg_leafQ (S : Shape) (c2 : Stk) (b : Block) (i d : ℕ) (hbi : S.heap.blocks.getD i default = b)
    (hd : Shape.leafDegree b = some d) :
    (quotP S c2 (Column.leafQuotient i) (chunks (d + 1))).natDegree ≤ chB (d + 1) := by
  refine (ndeg_quotP S c2 _ _ fun c _ ↦ ?_).trans (chunks_le_chB _)
  have hv : c2Vars S (.leafQuotient i c) = (chunks (d + 1)).getD c 0 := by
    simp only [c2Vars, hbi, hd]
  rw [← hv]
  exact ndeg_c2P_digits S c2 _

/-- **A heap block's leaf identity**: at most `blockB`. -/
theorem ndeg_blockP (S : Shape) (hH : HeapGood S) (c1 c2 setup : Stk) (rows : List ℕ) (alphas : List E)
    (beta : E) (b : Block) (i : ℕ) (hb : b ∈ S.heap.blocks) (hbi : S.heap.blocks.getD i default = b) :
    (blockP S c1 c2 setup rows alphas beta b i).natDegree ≤ blockB S b := by
  have hblk := hH.2.2.2.2.2 b hb
  have hR := ndeg_restr S c2 b
  have hw := natDegree_digitP b.r
  unfold blockP blockB
  rcases hlv : b.leaves with _ | _ | t | _ <;> rw [hlv] at hblk <;> dsimp only
  · -- The memory's block.
    have hd : Shape.leafDegree b = some (UniStatement.degree (2 * (2 ^ b.r - 1)) (2 ^ b.r)) := by
      unfold Shape.leafDegree; rw [hlv]
    have hq := ndeg_leafQ S c2 b i _ hbi hd
    have hp := ndeg_memPullP S c1 setup (eqKernel alphas) beta
    unfold memB
    refine ndeg_add (ndeg_add (ndeg_mul hR hp (le_max_left _ _)) (ndeg_mul hq hw (le_max_right _ _)))
      (ndeg_add (hp.trans ?_) (ndeg_Cmul (ndeg_add (by simp) ((ndeg_c1P S c1 (.memory 3)).trans ?_))))
    · exact (Nat.le_add_left _ _).trans (le_max_left _ _)
    · exact (Nat.le_add_left _ _).trans (le_max_left _ _)
  · -- The bytecode's block.
    have hd : Shape.leafDegree b = some (UniStatement.degree (2 * (2 ^ b.r - 1)) (2 ^ b.r)) := by
      unfold Shape.leafDegree; rw [hlv]
    have hq := ndeg_leafQ S c2 b i _ hbi hd
    have hp := ndeg_bcPullP S c1 setup alphas (eqKernel alphas) beta
    unfold memB
    refine ndeg_add (ndeg_add (ndeg_mul hR hp (le_max_left _ _)) (ndeg_mul hq hw (le_max_right _ _)))
      (ndeg_add (hp.trans ?_) (ndeg_Cmul (ndeg_add (by simp) ((ndeg_c1P S c1 .bytecodeFinal).trans ?_))))
    · exact (Nat.le_add_left _ _).trans (le_max_left _ _)
    · exact (Nat.le_add_left _ _).trans (le_max_left _ _)
  · -- A table's block.
    obtain ⟨ht, hr⟩ := hblk
    have hop := tables_opcode t ht
    have hd : Shape.leafDegree b = some (UniStatement.degree (max (tableDegrees (tables.getD t default)).1
        (tableDegrees (tables.getD t default)).2 * (2 ^ b.r - 1) + (2 ^ b.r - Shape.leastRows b.r))
        (2 ^ b.r)) := by
      unfold Shape.leafDegree; rw [hlv]
    have hq := ndeg_leafQ S c2 b i _ hbi hd
    obtain ⟨hpd, hppd⟩ := tableDegrees_le' (tables.getD t default)
    rw [pullDeg_getD] at hpd
    rw [pushDeg_getD] at hppd
    have hq' : (quotP S c2 (Column.leafQuotient i) (chunks (UniStatement.degree (max
        (tableDegrees (tables.getD t default)).1 (tableDegrees (tables.getD t default)).2 * (2 ^ b.r - 1) +
          (2 ^ b.r - Shape.leastRows b.r)) (2 ^ b.r) + 1))).natDegree ≤
        chB (UniStatement.degree (max (1 + pullL.getD t 0) (pushL.getD t 0) * (2 ^ b.r - 1) +
          (2 ^ b.r - Shape.leastRows b.r)) (2 ^ b.r) + 1) := by
      refine hq.trans (chB_mono (Nat.add_le_add_right (Nat.sub_le_sub_right (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (max_le_max hpd hppd)) _) _) _))
    have hcol : ∀ c, (c1P S c1 (.table (tables.getD t default).opcode c)).natDegree ≤ 2 ^ b.r := fun c ↦ by
      rw [hop, hr]
      exact ndeg_c1P S c1 _
    have hpull := ndeg_pullP (tables.getD t default) (eqKernel alphas) beta _ _ hcol
    have hpush := ndeg_pushP (tables.getD t default) (eqKernel alphas) beta _ _ hcol
    rw [pullDeg_getD] at hpull
    rw [pushDeg_getD] at hpush
    have hZ := ndeg_zActP ((List.range (b.r + 1)).map fun j ↦ intBits (rows.getD t 0) j 1) b.r
    have hZ2 : (zActP ((List.range (b.r + 1)).map fun j ↦ intBits (rows.getD t 0) j 1) b.r ^ 2).natDegree ≤
        2 ^ (b.r + 2) := by
      refine natDegree_pow_le.trans ?_
      have e : 2 ^ (b.r + 2) = 2 ^ (b.r + 1) * 2 := by ring
      rw [e]
      omega
    unfold tabB
    refine ndeg_add (ndeg_add (ndeg_add ?_ ?_) ?_) ?_
    · exact ndeg_mul hR (ndeg_add (ndeg_mul hpull hw le_rfl |>.trans (le_max_left _ _))
        (hZ2.trans (le_max_right _ _))) (le_max_left _ _)
    · exact ndeg_mul hq' (ndeg_mul hw hZ le_rfl) ((le_max_left _ _).trans (le_max_right _ _))
    · exact (ndeg_mul hpush hw le_rfl).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · exact hZ2.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · -- An unused block.
    exact ndeg_add hR ((natDegree_one).le.trans (Nat.zero_le _))

/-! ## The identities' degrees -/

/-- **The identities' degrees, summed**, at a shape whose heap is `HeapGood`. -/
theorem degBound_of (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (hH : HeapGood D.shape) :
    DegBoundP D Fl (treeB D.shape + wB D.shape + (D.shape.heap.blocks.map (blockB D.shape)).sum) := by
  intro s c1 ch fd c2
  unfold polysOf
  split_ifs
  · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, List.map_map]
    have h1 := ndeg_treeP D.shape c2
    have h2 := ndeg_rootP D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch)
    have h3 := ndeg_wP D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0)
    have h4 : ((D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)).map
        (Polynomial.natDegree ∘ fun bi ↦ blockP D.shape c1 c2 (stackFor D c1 c2 .setup) s.2 (alphasOf ch)
          (betaOf ch) bi.1 bi.2)).sum ≤ (D.shape.heap.blocks.map (blockB D.shape)).sum := by
      rw [← map_zip_fst D.shape.heap.blocks (List.range D.shape.heap.blocks.length) (by simp)
        (blockB D.shape)]
      refine list_sum_map_le _ _ _ fun bi hbi ↦ ?_
      obtain ⟨b, i⟩ := bi
      exact ndeg_blockP D.shape hH c1 c2 _ s.2 (alphasOf ch) (betaOf ch) b i (List.of_mem_zip hbi).1
        (mem_zip_range_iff _ default _ hbi).2
    omega
  · simp

theorem treeB_reference : treeB reference = 2 ^ 24 + 2 := by
  rw [treeB, heap_reference.1]

/-- **The bound at the reference shape**, by `norm_num` on the closed sum (`reference` is rewritten
to its numbers first, so nothing reduces its heap). -/
theorem refBound :
    treeB reference + wB reference + ((heapBlocksRef.map Block.ofTuple).map (blockB reference)).sum ≤
      50708397 := by
  rw [treeB_reference, reference_eq]
  simp only [heapBlocksRef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Block.ofTuple,
    blockB, wB, wMax, cdB, cdOf, wOf, ocL, tabB, memB, chB, pullL, pushL, List.foldr_cons,
    List.foldr_nil, List.getD_cons_succ, List.getD_cons_zero, Shape.leastRows, UniStatement.degree,
    Shape.constraintVars, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, opBlake2s]
  norm_num [max_def]

/-- **The identities' degrees at the reference shape**: at most `50,708,397`. -/
theorem degBound_reference (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (hS : D.shape = reference) :
    DegBoundP D Fl 50708397 := by
  intro s c1 ch fd c2
  refine (degBound_of D Fl (hS ▸ heapGood_reference) s c1 ch fd c2).trans ?_
  rw [hS, heap_blocks_reference]
  exact refBound

end UniSound.Ids

/-- info: 'UniSound.Ids.degBound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.degBound_of

/-- info: 'UniSound.Ids.degBound_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.degBound_reference
