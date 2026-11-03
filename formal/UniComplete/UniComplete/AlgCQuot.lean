-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgCChunks
import UniComplete.AlgCTerm

/-!
# The constraint quotient divides exactly and fits its chunks (milestone 4, the algebra, item 3)

`constraintNumerator tr γ words` is `Σ_i γ^i M_i · (w_{r_W} / w_{r_i})` over the constraints in the verifier's order
(`numItems`: per table JUMP's two, the counters' `z Π c + 1`, BLAKE2S's copies `copy − ℓ`, then the three public
lines); **`constraintNumerator_eq`** states it as that fold (`addItem`), unfolding the prover's loops once.

* **Divisibility** (`numerator_dvd`): every `M_i` vanishes on its table's `V_{r_i}` for an honest trace
  (`TraceHonest`: JUMP's two constraints, the counters' inverse, the copies `copy_j = ℓ_j` where `ℓ_j(ω_i)` is the
  slot's value since `y_l(ω_i) = i_l` (`CoordinateFunctionalsBasis`, the domain agent's item 7), the public lines
  through cells `0` and `1`), so `w_{r_i} ∣ M_i` (`wP_dvd_of_vanish`) and `w_{r_W} = w_{r_i} · lift_i` divides every
  term.
* **The degree** (`numerator_natDegree_le`): every term has degree at most `D + 2^{r_W}`, `D = Shape.constraintDegree`,
  so the quotient `Q_W = N / w_{r_W}` has degree at most `D` and **fits** its chunks `chunks (D + 1)`
  (`constraintQuotient_fits`).

Hypotheses beyond `TraceHonest`: every table's height and the memory's log-size at most `28` (`Small`, the
interpolation's range; see `AlgCBasis` for why `29 ≤ r ≤ 31` fails), and `CoordinateFunctionalsBasis` at
BLAKE2S's height (not kernel-checked at `18`, see `DomainCoord`).
-/

namespace UniComplete.AlgC

open UniStatement LeanVM.Parameters Polynomial Finset

/-! ### The numerator as a fold -/

/-- A constraint of the batch: its polynomial `M_i` and its lift `w_{r_W} / w_{r_i}`. -/
abbrev Item := Poly × Poly

/-- Add `γ^i M_i lift_i`, the power the second component. -/
def addItem (gamma : E) (s : Poly × E) (it : Item) : Poly × E := (s.1 + pC s.2 * it.1 * it.2, s.2 * gamma)

/-- BLAKE2S's copy of slot `slot` in column `c`: `copy_c + ℓ_slot`, `ℓ` read through `y(X)`. -/
def copyPoly (tr : Trace) (table : Table) (c slot : ℕ) : Poly :=
  (tablePolys tr table.opcode).getD c 0 +
    mleP (Array.ofFn (n := 2 ^ tr.height table.opcode) fun u ↦ pC (ofK (tr.qflock.getD (slot + 256 * u.val) 0)))
      ((List.range (tr.height table.opcode)).map (coordinateP (coordinateFunctionals (tr.height table.opcode))))

/-- The counters' constraint `z Π c + 1`. -/
def counterPoly (tr : Trace) (table : Table) : Poly :=
  table.countColumns.foldl (fun p c ↦ p * (tablePolys tr table.opcode).getD c 0)
    (colPolyK (tr.height table.opcode) (inverseColumn tr table.opcode)) + 1

/-- A table's column polynomial by name. -/
def colP (tr : Trace) (table : Table) (n : String) : Poly :=
  (tablePolys tr table.opcode).getD (colIdx table.columns n) 0

/-- **A table's constraints**, in the verifier's order. -/
def tableItems (tr : Trace) (table : Table) : List Item :=
  let lift := liftP (tr.height table.opcode) tr.shape.constraintVars
  (if table.opcode = opJump then
    [(colP tr table "b" + colP tr table "v_cond" * colP tr table "w", lift),
      (colP tr table "v_cond" * (colP tr table "b" + 1), lift)] else []) ++
  [(counterPoly tr table, lift)] ++
  (if table.opcode = opBlake2s then
    (List.range table.width).filterMap fun c ↦
      (qflockSlot (table.columns.getD c "")).map fun slot ↦ (copyPoly tr table c slot, lift)
   else [])

/-- The public lines' constraints `mem_k + low + X (low + high)`, lifted from `V_1`. -/
def publicItems (tr : Trace) (words : List E) : List Item :=
  ([(words.getD 0 0, words.getD 2 0), (words.getD 1 0, words.getD 3 0), ((0 : E), (0 : E))].zip (List.range 3)).map
    fun x ↦ (colPolyK tr.shape.logMemory (tr.memory.getD x.2 #[]) + pC x.1.1 + pX * pC (x.1.1 + x.1.2),
      liftP 1 tr.shape.constraintVars)

/-- **The constraints of the batch**, in the verifier's order. -/
def numItems (tr : Trace) (words : List E) : List Item := tables.flatMap (tableItems tr) ++ publicItems tr words

/-- An `Id` loop that always continues is a fold. -/
theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (g : α → β → β)
    (h : ∀ a ∈ l, ∀ b, f a b = pure (ForInStep.yield (g a b))) :
    forIn l init f = pure (l.foldl (fun b a ↦ g a b) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, h x (by simp)]
    exact ih (g x init) fun a ha b ↦ h a (List.mem_cons_of_mem _ ha) b

theorem foldl_filterMap {α β γ : Type} (l : List α) (f : α → Option β) (g : γ → β → γ) (s : γ) :
    (l.filterMap f).foldl g s = l.foldl (fun s a ↦ match f a with | some b => g s b | none => s) s := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, List.foldl_cons]
    cases hx : f x with
    | none => exact ih s
    | some b => exact ih _

theorem foldl_ext' {α β : Type} (f g : β → α → β) (l : List α) (s : β) (h : ∀ b a, f b a = g b a) :
    l.foldl f s = l.foldl g s := by
  rw [show f = g from funext fun b ↦ funext fun a ↦ h b a]

theorem foldl_map_eq {α β γ : Type} (l : List α) (f : α → β) (g : γ → β → γ) (s : γ) :
    (l.map f).foldl g s = l.foldl (fun s a ↦ g s (f a)) s := List.foldl_map

/-- **The prover's constraint numerator is the fold of its constraints.** -/
theorem constraintNumerator_eq (tr : Trace) (gamma : E) (words : List E) :
    constraintNumerator tr gamma words = ((numItems tr words).foldl (addItem gamma) (0, 1)).1 := by
  unfold constraintNumerator
  simp only [Id.run, List.forIn_pure_yield_eq_foldl]
  rw [forIn_id_yield tables (0, 1) _ (fun table s ↦ (tableItems tr table).foldl (addItem gamma) s)]
  · simp only [pure_bind, numItems, List.foldl_append, List.foldl_flatMap, publicItems, foldl_map_eq]
    rfl
  · intro table _ s
    by_cases hJ : table.opcode = opJump
    · have hB : ¬ table.opcode = opBlake2s := by rw [hJ]; decide
      simp only [Domain.ite_pos_of hJ, Domain.ite_neg_of hB, tableItems, List.append_nil, List.cons_append,
        List.nil_append, List.foldl_cons, List.foldl_nil, addItem, colP, counterPoly]
    · by_cases hB : table.opcode = opBlake2s
      · simp only [Domain.ite_neg_of hJ, Domain.ite_pos_of hB, tableItems, List.nil_append, List.cons_append,
          List.foldl_cons, foldl_filterMap]
        rw [forIn_id_yield _ _ _ (fun c s ↦ match qflockSlot (table.columns.getD c "") with
          | some slot => addItem gamma s (copyPoly tr table c slot,
              liftP (tr.height table.opcode) tr.shape.constraintVars)
          | none => s)]
        · simp only [pure_bind]
          refine congrArg (fun x ↦ pure (ForInStep.yield x)) (foldl_ext' _ _ _ _ fun b a ↦ ?_)
          cases qflockSlot (table.columns.getD a "") <;> rfl
        · intro c _ s'
          cases qflockSlot (table.columns.getD c "") <;> rfl
      · simp only [Domain.ite_neg_of hJ, Domain.ite_neg_of hB, tableItems, List.nil_append, List.append_nil,
          List.foldl_cons, List.foldl_nil, addItem, counterPoly]

/-! ### The lifts and the subspace polynomials -/

theorem tp_foldl_mul {α : Type} (l : List α) (f : α → Poly) (a : Poly) :
    (l.foldl (fun acc j ↦ acc * f j) a).toPoly = a.toPoly * (l.map fun j ↦ (f j).toPoly).prod := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, tp_mul, List.map_cons, List.prod_cons, mul_assoc]

/-- **`liftP r m` is `Π_{j ∈ [r, m)} (w_j + 1)`.** -/
theorem liftP_toPoly (r m : ℕ) : (liftP r m).toPoly = ∏ j ∈ Ico r (r + (m - r)), (Domain.wP j + 1) := by
  unfold liftP
  rw [tp_foldl_mul, tp_one, one_mul, Domain.prod_map_range']
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [tp_add, wPoly_toPoly, tp_one]

/-- **`w_r · lift = w_m`** (`r ≤ m`). -/
theorem wP_mul_liftP {r m : ℕ} (h : r ≤ m) : Domain.wP r * (liftP r m).toPoly = Domain.wP m := by
  rw [liftP_toPoly, ← Domain.wP_eq_mul, Nat.add_sub_cancel' h]

/-- **The lift at `t` is the verifier's `vanishingRatio`** (`m ≤ n` digits). -/
theorem pEval_liftP (t : E) (r : ℕ) {m n : ℕ} (hm : m ≤ n) :
    pEval t (liftP r m) = vanishingRatio (digits t n) r m := by
  rw [Domain.vanishingRatio_digits t hm, pEval_eq, liftP_toPoly, Polynomial.eval_prod]
  rcases Nat.lt_or_ge m r with hmr | hmr
  · rw [Nat.sub_eq_zero_of_le hmr.le, Nat.add_zero, Finset.Ico_self, Finset.Ico_eq_empty_of_le hmr.le, Finset.prod_empty, Finset.prod_empty]
  · rw [Nat.add_sub_cancel' hmr]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Polynomial.eval_add, Polynomial.eval_one, Domain.wP_eval]

theorem liftP_natDegree {r m : ℕ} (h : r ≤ m) : (liftP r m).toPoly.natDegree = 2 ^ m - 2 ^ r := by
  have hm := wP_mul_liftP h
  have hne : (liftP r m).toPoly ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero] at hm
    exact (Domain.wP_monic m).ne_zero hm.symm
  have := congrArg Polynomial.natDegree hm
  rw [(Domain.wP_monic r).natDegree_mul' hne, Domain.wP_natDegree, Domain.wP_natDegree] at this
  omega

/-- **A polynomial vanishing on `V_r` is a multiple of `w_r`** (`r ≤ 32`). -/
theorem wP_dvd_of_vanish {r : ℕ} (hr : r ≤ 32) (p : E[X]) (h : ∀ i < 2 ^ r, p.eval (pointE i) = 0) :
    Domain.wP r ∣ p := by
  by_cases hp : p = 0
  · rw [hp]
    exact dvd_zero _
  have hb : ∀ j ∈ range (2 ^ r), j < 2 ^ 32 := fun j hj ↦
    lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.pow_le_pow_right (by norm_num) hr)
  rw [Domain.wP_eq_linProd hr, Domain.linProd]
  have hmap : ∏ j ∈ range (2 ^ r), (X - C (pointE j)) =
      (((range (2 ^ r)).val.map pointE).map fun a ↦ X - C a).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hnd : ((range (2 ^ r)).val.map pointE).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy hxy ↦ Domain.pointE_injOn (hb x hx) (hb y hy) hxy) (range _).nodup
  have hle : (range (2 ^ r)).val.map pointE ≤ p.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp ha
    exact (mem_roots hp).mpr (h j (Finset.mem_range.mp hj))
  rw [hmap]
  exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hp _).mpr hle

/-! ### Divisibility of the batch -/

/-- **A constraint the batch can divide**: it vanishes on its domain `V_r` (`w_r ∣ M`), and its lift is
`w_{r_W} / w_r`. -/
def ItemOK (rW : ℕ) (it : Item) : Prop := ∃ r, r ≤ rW ∧ it.2 = liftP r rW ∧ Domain.wP r ∣ it.1.toPoly

theorem itemOK_dvd {rW : ℕ} {it : Item} (h : ItemOK rW it) : Domain.wP rW ∣ (it.1 * it.2).toPoly := by
  obtain ⟨r, hr, h2, ⟨q, hq⟩⟩ := h
  rw [tp_mul, h2, hq, mul_comm (Domain.wP r) q, mul_assoc, wP_mul_liftP hr]
  exact dvd_mul_left _ _

theorem foldl_addItem_dvd (gamma : E) (rW : ℕ) : ∀ (items : List Item) (s : Poly × E),
    Domain.wP rW ∣ s.1.toPoly → (∀ it ∈ items, ItemOK rW it) →
      Domain.wP rW ∣ (items.foldl (addItem gamma) s).1.toPoly
  | [], _, h, _ => h
  | it :: rest, s, h, hits => by
    rw [List.foldl_cons]
    refine foldl_addItem_dvd gamma rW rest _ ?_ (fun x hx ↦ hits x (List.mem_cons_of_mem _ hx))
    show Domain.wP rW ∣ (s.1 + pC s.2 * it.1 * it.2).toPoly
    rw [tp_add, mul_assoc, tp_mul]
    exact dvd_add h (dvd_mul_of_dvd_right (itemOK_dvd (hits it (by simp))) _)


/-! ### The trace's columns on `V_r` -/

/-- **The sizes the algebra needs**: every table's height and the memory's log-size at most `28` (the additive
transform's basis, `AlgCBasis`). -/
structure Small (tr : Trace) : Prop where
  heights : ∀ t < 6, tr.height t ≤ 28
  memory : tr.shape.logMemory ≤ 28

theorem mem_tables {table : Table} (h : table ∈ tables) :
    table.opcode < 6 ∧ tables.getD table.opcode default = table := by
  simp only [tables, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, rfl⟩

theorem le_foldl_max (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih (max a y)
    refine ⟨le_trans (le_max_left _ _) h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right _ _) h1
    · exact h2 x hx

theorem height_le_constraintVars (tr : Trace) (t : ℕ) : tr.height t ≤ tr.shape.constraintVars := by
  unfold Trace.height Shape.constraintVars
  by_cases ht : t < tr.shape.heights.length
  · rw [List.getD_eq_getElem _ _ ht]
    exact (le_foldl_max _ 0).2 _ (List.mem_append_left _ (List.getElem_mem ht))
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem logMemory_le_constraintVars (tr : Trace) : tr.shape.logMemory ≤ tr.shape.constraintVars :=
  (le_foldl_max _ 0).2 _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem tablePolys_getD (tr : Trace) (t : ℕ) {c : ℕ} (hc : c < (tables.getD t default).width) :
    (tablePolys tr t).getD c 0 = colPolyK (tr.height t) (tr.column t c) :=
  E2ECompleteness.getD_ofFn' _ hc _

theorem eval_tableCol {tr : Trace} (hH : TraceHonest tr) (hS : Small tr) {t c i : ℕ} (ht : t < 6)
    (hc : c < (tables.getD t default).width) (hi : i < 2 ^ tr.height t) :
    ((tablePolys tr t).getD c 0).toPoly.eval (pointE i) = ofK ((tr.column t c).getD i 0) := by
  rw [tablePolys_getD tr t hc, ← pEval_eq]
  exact pEval_colPolyK_pointE (hS.heights t ht) _ ((hH.tablesSize.2 t ht).2 c hc) hi

theorem inverseColumn_getD (tr : Trace) (t : ℕ) {i : ℕ} (hi : i < 2 ^ tr.height t) :
    (inverseColumn tr t).getD i 0 =
      ((tables.getD t default).countColumns.foldl (fun acc c ↦ acc * (tr.column t c).getD i 0) 1)⁻¹ :=
  E2ECompleteness.getD_ofFn' _ hi _

theorem embed_listProd (l : List K) : ofK l.prod = (l.map ofK).prod := map_list_prod (algebraMap K E) l

theorem countColumns_lt (table : Table) : ∀ c ∈ table.countColumns, c < table.width := by
  intro c hc
  unfold Table.countColumns at hc
  exact List.mem_range.mp (List.mem_filter.mp hc).1

/-- **The counters' constraint vanishes on `V_r`**: `z Π c + 1 = (Π c)⁻¹ Π c + 1 = 0`, the counters nonzero. -/
theorem counter_vanish {tr : Trace} (hH : TraceHonest tr) (hS : Small tr) {table : Table} (htab : table ∈ tables)
    {i : ℕ} (hi : i < 2 ^ tr.height table.opcode) : (counterPoly tr table).toPoly.eval (pointE i) = 0 := by
  obtain ⟨ht, hget⟩ := mem_tables htab
  have hcnt := hH.counters _ ht i hi
  rw [hget] at hcnt
  unfold counterPoly
  rw [tp_add, tp_one, Polynomial.eval_add, Polynomial.eval_one, tp_foldl_mul, Polynomial.eval_mul,
    Polynomial.eval_list_prod, List.map_map, ← pEval_eq,
    pEval_colPolyK_pointE (hS.heights _ ht) _ (inverseColumn_size tr _) hi, inverseColumn_getD tr _ hi, hget]
  have hcols : (table.countColumns.map ((fun p ↦ Polynomial.eval (pointE i) p) ∘ fun j ↦
      ((tablePolys tr table.opcode).getD j 0).toPoly)) =
      (table.countColumns.map fun c ↦ (tr.column table.opcode c).getD i 0).map ofK := by
    rw [List.map_map]
    refine List.map_congr_left fun c hc ↦ ?_
    simp only [Function.comp_apply]
    exact eval_tableCol hH hS ht (by rw [hget]; exact countColumns_lt table c hc) hi
  rw [hcols, ← embed_listProd, ← Domain.embed_mul, Domain.foldl_mul_eq_prod, one_mul,
    inv_mul_cancel₀ (by rwa [Domain.foldl_mul_eq_prod, one_mul] at hcnt), Domain.embed_one]
  exact CharTwo.add_self_eq_zero 1


/-- JUMP's table. -/
theorem jumpTable_eq : tables.getD opJump default = ⟨opJump, jumpColumns, flushesJump⟩ := rfl

/-- BLAKE2S's table. -/
theorem blakeTable_eq : tables.getD opBlake2s default = ⟨opBlake2s, blake2sColumns, flushesBlake2s⟩ := rfl

/-- **JUMP's two constraints vanish on `V_r`.** -/
theorem jump_vanish {tr : Trace} (hH : TraceHonest tr) (hS : Small tr) {table : Table} (htab : table ∈ tables)
    (hJ : table.opcode = opJump) {i : ℕ} (hi : i < 2 ^ tr.height table.opcode) :
    (colP tr table "b" + colP tr table "v_cond" * colP tr table "w").toPoly.eval (pointE i) = 0 ∧
      (colP tr table "v_cond" * (colP tr table "b" + 1)).toPoly.eval (pointE i) = 0 := by
  obtain ⟨-, hget⟩ := mem_tables htab
  rw [hJ] at hget hi
  subst hget
  have hb : colIdx jumpColumns "b" < (tables.getD opJump default).width := by decide
  have hv : colIdx jumpColumns "v_cond" < (tables.getD opJump default).width := by decide
  have hw : colIdx jumpColumns "w" < (tables.getD opJump default).width := by decide
  obtain ⟨h1, h2⟩ := hH.jump i hi
  simp only [colP, jumpTable_eq] at h1 h2 ⊢
  rw [tp_add, tp_mul, tp_mul, tp_add, tp_one, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_one, eval_tableCol hH hS (by decide) hb hi,
    eval_tableCol hH hS (by decide) hv hi, eval_tableCol hH hS (by decide) hw hi]
  refine ⟨?_, ?_⟩
  · rw [← Domain.embed_mul, ← Domain.embed_add, h1, Domain.embed_zero]
  · rw [← Domain.embed_one, ← Domain.embed_add, ← Domain.embed_mul, h2, Domain.embed_zero]

theorem sqn_eq_pow (x : E) : ∀ m : ℕ, sqn x m = x ^ (2 ^ m)
  | 0 => by simp [sqn]
  | m + 1 => by
    rw [sqn, sqn_eq_pow (x * x) m, ← pow_two, ← pow_mul, pow_succ, mul_comm]

/-- The coordinate polynomial's fold, evaluated, is `coordinatesAt`'s fold at the Frobenius powers. -/
theorem coord_fold (t : E) : ∀ (as : List K) (ms : List ℕ) (acc : Poly) (e : E), pEval t acc = e →
    pEval t ((as.zip ms).foldl (fun acc (a, mm) ↦ acc + pC (ofK a) * pX ^ (2 ^ mm)) acc) =
      (as.zip (ms.map (sqn t))).foldl (fun acc (a, x) ↦ if a ≠ 0 then acc + ofK a * x else acc) e
  | [], _, _, _, h => by simpa using h
  | _ :: _, [], _, _, h => by simpa using h
  | a :: as, m :: ms, acc, e, h => by
    rw [List.zip_cons_cons, List.map_cons, List.zip_cons_cons, List.foldl_cons, List.foldl_cons]
    refine coord_fold t as ms _ _ ?_
    rw [pEval_eq, tp_add, tp_mul, tp_C, tp_pow, tp_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← sqn_eq_pow, ← pEval_eq, h]
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha]

theorem coordinateFunctionals_shape (r : ℕ) :
    ∃ g : Fin r → Fin r → K, coordinateFunctionals r = Array.ofFn fun l ↦ Array.ofFn (g l) := ⟨_, rfl⟩

theorem coordinateFunctionals_row_size (r : ℕ) {l : ℕ} (hl : l < r) :
    ((coordinateFunctionals r).getD l #[]).size = r := by
  obtain ⟨g, hg⟩ := coordinateFunctionals_shape r
  rw [hg, E2ECompleteness.getD_ofFn' _ hl, Array.size_ofFn]

/-- **The coordinates at `t` are the coordinate polynomials at `t`.** -/
theorem coordinatesAt_eq_map (t : E) (r : ℕ) :
    coordinatesAt t (coordinateFunctionals r) =
      (List.range r).map fun l ↦ pEval t (coordinateP (coordinateFunctionals r) l) := by
  have hsize : (coordinateFunctionals r).size = r := Domain.coordinateFunctionals_size r
  unfold coordinatesAt coordinateP
  apply List.ext_getElem
  · simp [hsize]
  · intro l h1 _
    have hl : l < r := by simpa [hsize] using h1
    have hrow : (coordinateFunctionals r).getD l #[] =
        (coordinateFunctionals r).toList[l]'(by simp [hsize, hl]) := by
      simp [Array.getD_eq_getD_getElem?, hl, hsize]
    have hrs := coordinateFunctionals_row_size r hl
    simp only [List.getElem_map, List.getElem_range]
    rw [hrow] at hrs ⊢
    symm
    refine (coord_fold t _ _ 0 0 (by rw [pEval_eq, tp_zero, Polynomial.eval_zero])).trans ?_
    rw [hrs]
    conv in List.range (coordinateFunctionals r).size => rw [hsize]

theorem getD_map_pEval (a : Array Poly) (t : E) (k : ℕ) : (a.map (pEval t)).getD k 0 = pEval t (a.getD k 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[k]? with
  | none => show (0 : E) = pEval t 0; rw [pEval_eq, tp_zero, Polynomial.eval_zero]
  | some x => rfl

theorem mleP_nil (vals : Array Poly) : mleP vals [] = vals.getD 0 0 := rfl

theorem mleP_cons (vals : Array Poly) (r : Poly) (rs : List Poly) :
    mleP vals (r :: rs) = mleP (Array.ofFn (n := vals.size / 2) fun i ↦
      vals.getD (2 * i.val) 0 + r * (vals.getD (2 * i.val) 0 + vals.getD (2 * i.val + 1) 0)) rs := rfl

theorem map_mleStep (t : E) (vals : Array Poly) (r : Poly) :
    (Array.ofFn (n := vals.size / 2) fun i ↦
      vals.getD (2 * i.val) 0 + r * (vals.getD (2 * i.val) 0 + vals.getD (2 * i.val + 1) 0)).map (pEval t) =
      UniStatement.foldOnce (vals.map (pEval t)) (pEval t r) := by
  refine Bridge.Ntt.array_ext_getD_E (by simp [UniComplete.foldOnce_size]) fun i hi ↦ ?_
  have hi' : i < vals.size / 2 := by simpa using hi
  rw [getD_map_pEval, E2ECompleteness.getD_ofFn' _ hi', UniComplete.foldOnce_getD _ _ (by simpa using hi'),
    getD_map_pEval, getD_map_pEval]
  simp only [pEval_eq, tp_add, tp_mul, Polynomial.eval_add, Polynomial.eval_mul]

/-- **`mleP` at `t`** is the multilinear extension of the values at the coordinates' values. -/
theorem pEval_mleP (t : E) : ∀ (pt : List Poly) (vals : Array Poly),
    pEval t (mleP vals pt) = ((pt.map (pEval t)).foldl UniStatement.foldOnce (vals.map (pEval t))).getD 0 0
  | [], vals => by rw [mleP_nil, List.map_nil, List.foldl_nil, getD_map_pEval]
  | r :: rs, vals => by
    rw [mleP_cons, pEval_mleP t rs, List.map_cons, List.foldl_cons, map_mleStep]

/-- **The slot's polynomial `ℓ` at `ω_i` is the slot's value at row `i`** (`y(ω_i)` the bits of `i`). -/
theorem mleP_slot_pointE (q : Array K) {r i slot : ℕ} (hC : Domain.CoordinateFunctionalsBasis r) (hi : i < 2 ^ r) :
    pEval (pointE i) (mleP (Array.ofFn (n := 2 ^ r) fun u ↦ pC (ofK (q.getD (slot + 256 * u.val) 0)))
      ((List.range r).map (coordinateP (coordinateFunctionals r)))) = ofK (q.getD (slot + 256 * i) 0) := by
  rw [pEval_mleP, List.map_map]
  have hpt : (List.range r).map (pEval (pointE i) ∘ coordinateP (coordinateFunctionals r)) =
      LeanVM.Protocol.EndToEnd.boolPoint r i := by
    have := coordinatesAt_eq_map (pointE i) r
    rw [Domain.coordinatesAt_pointE_of_basis hC hi] at this
    rw [show (pEval (pointE i) ∘ coordinateP (coordinateFunctionals r)) =
      fun l ↦ pEval (pointE i) (coordinateP (coordinateFunctionals r) l) from rfl, ← this]
    rfl
  have hlen : (LeanVM.Protocol.EndToEnd.boolPoint r i).length = r := by simp [LeanVM.Protocol.EndToEnd.boolPoint]
  rw [hpt, UniComplete.foldl_foldOnce _ _ (by simp [hlen])]
  rw [hlen, Finset.sum_eq_single i]
  · rw [LeanVM.Protocol.EndToEnd.Complete.eqEval_boolPoint_boolPoint r i i hi hi, Domain.ite_pos_of rfl, mul_one,
      getD_map_pEval, E2ECompleteness.getD_ofFn' _ hi, pEval_eq, tp_C, Polynomial.eval_C]
  · intro x hx hxi
    rw [LeanVM.Protocol.EndToEnd.Complete.eqEval_boolPoint_boolPoint r x i (Finset.mem_range.mp hx) hi,
      Domain.ite_neg_of hxi, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hi) h

/-- **BLAKE2S's copies vanish on `V_r`**: `copy_c(ω_i) = ℓ(ω_i)`, the slot's value. -/
theorem copy_vanish {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) {table : Table} (htab : table ∈ tables)
    (hB : table.opcode = opBlake2s) {c slot : ℕ} (hc : c < table.width)
    (hslot : qflockSlot (table.columns.getD c "") = some slot) {i : ℕ} (hi : i < 2 ^ tr.height table.opcode) :
    (copyPoly tr table c slot).toPoly.eval (pointE i) = 0 := by
  obtain ⟨-, hget⟩ := mem_tables htab
  rw [hB] at hget hi
  subst hget
  simp only [blakeTable_eq] at hc hslot
  have hcopy := hH.copies i hi c hc slot hslot
  unfold copyPoly
  simp only [blakeTable_eq]
  rw [tp_add, Polynomial.eval_add, eval_tableCol hH hS (by decide) (by rw [blakeTable_eq]; exact hc) hi,
    ← pEval_eq, mleP_slot_pointE _ hC hi, hcopy]
  exact CharTwo.add_self_eq_zero _

theorem mem_tableItems {tr : Trace} {table : Table} {it : Item} (h : it ∈ tableItems tr table) :
    (table.opcode = opJump ∧ (it = (colP tr table "b" + colP tr table "v_cond" * colP tr table "w",
        liftP (tr.height table.opcode) tr.shape.constraintVars) ∨
      it = (colP tr table "v_cond" * (colP tr table "b" + 1),
        liftP (tr.height table.opcode) tr.shape.constraintVars))) ∨
    it = (counterPoly tr table, liftP (tr.height table.opcode) tr.shape.constraintVars) ∨
    (table.opcode = opBlake2s ∧ ∃ c < table.width, ∃ slot, qflockSlot (table.columns.getD c "") = some slot ∧
      it = (copyPoly tr table c slot, liftP (tr.height table.opcode) tr.shape.constraintVars)) := by
  simp only [tableItems, List.mem_append, List.mem_singleton] at h
  rcases h with (hJ | hc) | hB
  · by_cases hJ' : table.opcode = opJump
    · rw [Domain.ite_pos_of hJ'] at hJ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
      exact Or.inl ⟨hJ', hJ⟩
    · rw [Domain.ite_neg_of hJ'] at hJ
      simp at hJ
  · exact Or.inr (Or.inl hc)
  · by_cases hB' : table.opcode = opBlake2s
    · rw [Domain.ite_pos_of hB'] at hB
      obtain ⟨c, hc, hmap⟩ := List.mem_filterMap.mp hB
      obtain ⟨slot, hslot, rfl⟩ := Option.map_eq_some_iff.mp hmap
      exact Or.inr (Or.inr ⟨hB', c, List.mem_range.mp hc, slot, hslot, rfl⟩)
    · rw [Domain.ite_neg_of hB'] at hB
      simp at hB

/-- **Every table constraint vanishes on its table's `V_r`.** -/
theorem tableItems_ok {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) {table : Table} (htab : table ∈ tables) :
    ∀ it ∈ tableItems tr table, ItemOK tr.shape.constraintVars it := by
  obtain ⟨ht, -⟩ := mem_tables htab
  have hr := height_le_constraintVars tr table.opcode
  have hr28 := hS.heights _ ht
  intro it hit
  rcases mem_tableItems hit with ⟨hJ, rfl | rfl⟩ | rfl | ⟨hB, c, hc, slot, hslot, rfl⟩
  · exact ⟨_, hr, rfl, wP_dvd_of_vanish (by omega) _ fun i hi ↦ (jump_vanish hH hS htab hJ hi).1⟩
  · exact ⟨_, hr, rfl, wP_dvd_of_vanish (by omega) _ fun i hi ↦ (jump_vanish hH hS htab hJ hi).2⟩
  · exact ⟨_, hr, rfl, wP_dvd_of_vanish (by omega) _ fun i hi ↦ counter_vanish hH hS htab hi⟩
  · exact ⟨_, hr, rfl, wP_dvd_of_vanish (by omega) _ fun i hi ↦ copy_vanish hH hS hC htab hB hc hslot hi⟩


/-! ### The public lines -/

theorem pointE_one : pointE 1 = 1 := by
  rw [← Domain.omega_basisE]
  exact Heap.omega_one Domain.basisE (by norm_num)

theorem ofLane_zero : K.ofLane 0 = 0 := by decide

/-- `eK w` is the word in `K`, embedded. -/
theorem eK_eq_ofK (w : UInt64) : eK w = ofK (K.ofLane w) := by
  show E.ofLimbs (K.ofLane w) (K.ofLane 0) (K.ofLane 0) = _
  rw [ofLane_zero]
  exact (Primitives.F192.ofF64_eq _).symm

theorem publicWords_getD (tr : Trace) {k : ℕ} (hk : k < 4) :
    (publicWordsOf tr.publicInput).getD k 0 = ofK (publicK tr k) := by
  unfold publicWordsOf
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range, eK_eq_ofK]
  rfl

theorem logMemory_pos {tr : Trace} (hH : TraceHonest tr) : 1 ≤ tr.shape.logMemory := by
  have h := hH.valid.2
  simp only [Shape.validate, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  omega

/-- **A public line vanishes on `V_1`** when the memory's cells `0`, `1` hold its two values. -/
theorem public_dvd {tr : Trace} (hH : TraceHonest tr) (hS : Small tr) {k : ℕ} (hk : k < 4) (low high : E)
    (h0 : ofK ((tr.memory.getD k #[]).getD 0 0) = low) (h1 : ofK ((tr.memory.getD k #[]).getD 1 0) = high) :
    Domain.wP 1 ∣ (colPolyK tr.shape.logMemory (tr.memory.getD k #[]) + pC low + pX * pC (low + high)).toPoly := by
  have hlm := logMemory_pos hH
  have h2 : 2 ≤ 2 ^ tr.shape.logMemory := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ tr.shape.logMemory := Nat.pow_le_pow_right (by norm_num) hlm
  have hsize := hH.memorySize.2 k hk
  refine wP_dvd_of_vanish (by norm_num) _ fun i hi ↦ ?_
  rw [tp_add, tp_add, tp_mul, tp_C, tp_C, tp_X, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_X, ← pEval_eq,
    pEval_colPolyK_pointE hS.memory _ hsize (by omega)]
  have hc2 : ∀ x : E, x + x = 0 := fun x ↦ CharTwo.add_self_eq_zero x
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [h0, Domain.pointE_zero, zero_mul, add_zero, hc2]
  · rw [h1, pointE_one, one_mul]
    linear_combination (hc2 low) + (hc2 high)

/-- **The public lines vanish on `V_1`**, the memory's cells `0`, `1` being the public input's words. -/
theorem publicItems_ok {tr : Trace} (hH : TraceHonest tr) (hS : Small tr) :
    ∀ it ∈ publicItems tr (publicWordsOf tr.publicInput), ItemOK tr.shape.constraintVars it := by
  have h1 : 1 ≤ tr.shape.constraintVars := le_trans (logMemory_pos hH) (logMemory_le_constraintVars tr)
  obtain ⟨p00, p01, p10, p11, p20, p21⟩ := hH.publicLines
  intro it hit
  simp only [publicItems, show List.range 3 = [0, 1, 2] from rfl, List.zip_cons_cons, List.zip_nil_right,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl
  · refine ⟨1, h1, rfl, public_dvd hH hS (by norm_num) _ _ ?_ ?_⟩
    · rw [p00, publicWords_getD tr (by norm_num)]
    · rw [p01, publicWords_getD tr (by norm_num)]
  · refine ⟨1, h1, rfl, public_dvd hH hS (by norm_num) _ _ ?_ ?_⟩
    · rw [p10, publicWords_getD tr (by norm_num)]
    · rw [p11, publicWords_getD tr (by norm_num)]
  · refine ⟨1, h1, rfl, public_dvd hH hS (by norm_num) _ _ ?_ ?_⟩
    · rw [p20, Domain.embed_zero]
    · rw [p21, Domain.embed_zero]

/-! ### The quotient divides exactly -/

/-- **Every constraint of the batch vanishes on its domain.** -/
theorem numItems_ok {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) :
    ∀ it ∈ numItems tr (publicWordsOf tr.publicInput), ItemOK tr.shape.constraintVars it := by
  intro it hit
  rcases List.mem_append.mp hit with h | h
  · obtain ⟨table, htab, hit'⟩ := List.mem_flatMap.mp h
    exact tableItems_ok hH hS hC htab it hit'
  · exact publicItems_ok hH hS it h

/-- **`w_{r_W}` divides the constraints' numerator** of an honest trace. -/
theorem numerator_dvd {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) (gamma : E) :
    Domain.wP tr.shape.constraintVars ∣ (constraintNumerator tr gamma (publicWordsOf tr.publicInput)).toPoly := by
  rw [constraintNumerator_eq]
  exact foldl_addItem_dvd gamma _ _ (0, 1) (by rw [tp_zero]; exact dvd_zero _) (numItems_ok hH hS hC)

/-- **The constraint quotient divides exactly**: `Q_W · w_{r_W} = N`. -/
theorem constraintQuotient_mul {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) (gamma : E) :
    (constraintQuotient tr gamma (publicWordsOf tr.publicInput)).toPoly * Domain.wP tr.shape.constraintVars =
      (constraintNumerator tr gamma (publicWordsOf tr.publicInput)).toPoly := by
  unfold constraintQuotient
  rw [toPoly_divM _ _ (wPoly_monic _), wPoly_toPoly]
  have h := modByMonic_add_div (constraintNumerator tr gamma (publicWordsOf tr.publicInput)).toPoly
    (Domain.wP tr.shape.constraintVars)
  rw [(modByMonic_eq_zero_iff_dvd (Domain.wP_monic _)).mpr (numerator_dvd hH hS hC gamma), zero_add] at h
  rw [mul_comm]
  exact h


/-! ### The degree -/

/-- `Shape.constraintDegree`'s step over the tables. -/
def degStep (shape : Shape) (d : ℕ) (table : Table) : ℕ :=
  let r := shape.heights.getD table.opcode 0
  let n := 2 ^ r
  let d := if table.opcode = opJump then max d (degree n 2) else d
  let d := max d (degree ((n - 1) * (1 + table.countColumns.length)) n)
  if table.opcode = opBlake2s then max d (degree (r * (n / 2)) n) else d

theorem constraintDegree_eq (shape : Shape) :
    shape.constraintDegree = max (tables.foldl (degStep shape) 0) (degree (2 ^ shape.logMemory) 3) := rfl

theorem foldl_ge {α : Type} (f : ℕ → α → ℕ) (hmono : ∀ d x, d ≤ f d x) :
    ∀ (l : List α) (d : ℕ), d ≤ l.foldl f d
  | [], _ => le_rfl
  | x :: xs, d => le_trans (hmono d x) (foldl_ge f hmono xs (f d x))

theorem foldl_comp_le {α : Type} (f : ℕ → α → ℕ) (hmono : ∀ d x, d ≤ f d x) (c : α → ℕ)
    (hc : ∀ d x, c x ≤ f d x) : ∀ (l : List α) (d : ℕ), ∀ x ∈ l, c x ≤ l.foldl f d
  | [], _, _, h => absurd h (List.not_mem_nil)
  | y :: ys, d, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (hc d x) (foldl_ge f hmono ys _)
    · exact foldl_comp_le f hmono c hc ys _ x h

theorem degStep_mono (shape : Shape) (d : ℕ) (table : Table) : d ≤ degStep shape d table := by
  unfold degStep
  dsimp only
  split_ifs <;> omega

/-- **The constraint degree bounds each table's quotient degrees** (JUMP's, the counters', BLAKE2S's copies'). -/
theorem le_constraintDegree (shape : Shape) {table : Table} (htab : table ∈ tables) :
    (table.opcode = opJump → degree (2 ^ shape.heights.getD table.opcode 0) 2 ≤ shape.constraintDegree) ∧
    degree ((2 ^ shape.heights.getD table.opcode 0 - 1) * (1 + table.countColumns.length))
      (2 ^ shape.heights.getD table.opcode 0) ≤ shape.constraintDegree ∧
    (table.opcode = opBlake2s → degree (shape.heights.getD table.opcode 0 * (2 ^ shape.heights.getD table.opcode 0 / 2))
      (2 ^ shape.heights.getD table.opcode 0) ≤ shape.constraintDegree) := by
  rw [constraintDegree_eq]
  have key : ∀ c : Table → ℕ, (∀ d x, c x ≤ degStep shape d x) →
      c table ≤ max (tables.foldl (degStep shape) 0) (degree (2 ^ shape.logMemory) 3) := fun c hc ↦
    le_trans (foldl_comp_le (degStep shape) (degStep_mono shape) c hc tables 0 table htab) (le_max_left _ _)
  refine ⟨fun hJ ↦ ?_, ?_, fun hB ↦ ?_⟩
  · have := key (fun x ↦ if x.opcode = opJump then degree (2 ^ shape.heights.getD x.opcode 0) 2 else 0)
      (fun d x ↦ by unfold degStep; dsimp only; split_ifs <;> omega)
    simpa [hJ] using this
  · exact key (fun x ↦ degree ((2 ^ shape.heights.getD x.opcode 0 - 1) * (1 + x.countColumns.length))
      (2 ^ shape.heights.getD x.opcode 0)) (fun d x ↦ by unfold degStep; dsimp only; split_ifs <;> omega)
  · have := key (fun x ↦ if x.opcode = opBlake2s then
      degree (shape.heights.getD x.opcode 0 * (2 ^ shape.heights.getD x.opcode 0 / 2))
        (2 ^ shape.heights.getD x.opcode 0) else 0)
      (fun d x ↦ by unfold degStep; dsimp only; split_ifs <;> omega)
    simpa [hB] using this

theorem public_le_constraintDegree (shape : Shape) : degree (2 ^ shape.logMemory) 3 ≤ shape.constraintDegree := by
  rw [constraintDegree_eq]
  exact le_max_right _ _

theorem tablePolys_natDegree (tr : Trace) (t c : ℕ) :
    ((tablePolys tr t).getD c 0).toPoly.natDegree < 2 ^ tr.height t := by
  by_cases hc : c < (tables.getD t default).width
  · rw [tablePolys_getD tr t hc]
    exact colPolyK_natDegree_lt _ _
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [tablePolys, Array.size_ofFn]; omega),
      Option.getD_none, tp_zero, natDegree_zero]
    exact Nat.two_pow_pos _

theorem natDegree_foldl_mul {α : Type} (l : List α) (f : α → Poly) (B : ℕ)
    (hf : ∀ x, (f x).toPoly.natDegree ≤ B) : ∀ z : Poly,
      (l.foldl (fun p c ↦ p * f c) z).toPoly.natDegree ≤ z.toPoly.natDegree + l.length * B := by
  induction l with
  | nil => intro z; simp
  | cons x xs ih =>
    intro z
    rw [List.foldl_cons]
    refine le_trans (ih _) ?_
    rw [tp_mul, List.length_cons]
    have := natDegree_mul_le (p := z.toPoly) (q := (f x).toPoly)
    have := hf x
    nlinarith

theorem natDegree_coordFold (F : Poly → K × ℕ → Poly)
    (hF : ∀ acc a mm, (F acc (a, mm)).toPoly.natDegree ≤ max acc.toPoly.natDegree (2 ^ mm)) (B : ℕ) :
    ∀ (as : List K) (ms : List ℕ) (acc : Poly), (∀ m ∈ ms, 2 ^ m ≤ B) →
      ((as.zip ms).foldl F acc).toPoly.natDegree ≤ max acc.toPoly.natDegree B
  | [], _, acc, _ => by simp
  | _ :: _, [], acc, _ => by simp
  | a :: as, m :: ms, acc, hB => by
    rw [List.zip_cons_cons, List.foldl_cons]
    refine le_trans (natDegree_coordFold F hF B as ms _ fun x hx ↦ hB x (List.mem_cons_of_mem _ hx)) ?_
    have h1 := hF acc a m
    have h2 := hB m (by simp)
    omega

/-- `y_l = Σ_m a_{l,m} X^(2^m)` has degree at most `2^(r−1)`. -/
theorem coordinateP_natDegree (r : ℕ) {l : ℕ} (hl : l < r) :
    (coordinateP (coordinateFunctionals r) l).toPoly.natDegree ≤ 2 ^ (r - 1) := by
  unfold coordinateP
  refine le_trans (natDegree_coordFold _ ?_ (2 ^ (r - 1)) _ _ 0 ?_) ?_
  · intro acc a mm
    show (acc + pC (ofK a) * pX ^ (2 ^ mm)).toPoly.natDegree ≤ _
    rw [tp_add, tp_mul, tp_C, tp_pow, tp_X]
    refine le_trans (natDegree_add_le _ _) (max_le_max le_rfl ?_)
    refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X_pow]
  · intro m hm
    rw [List.mem_range, coordinateFunctionals_row_size r hl] at hm
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [tp_zero, natDegree_zero]
    simp

theorem natDegree_mleP : ∀ (pt : List Poly) (vals : Array Poly) (D : ℕ),
    (∀ k, (vals.getD k 0).toPoly.natDegree ≤ D) →
      (mleP vals pt).toPoly.natDegree ≤ D + (pt.map fun p ↦ p.toPoly.natDegree).sum
  | [], vals, D, h => by rw [mleP_nil]; simpa using h 0
  | r :: rs, vals, D, h => by
    rw [mleP_cons, List.map_cons, List.sum_cons, ← Nat.add_assoc]
    refine natDegree_mleP rs _ _ fun k ↦ ?_
    by_cases hk : k < vals.size / 2
    · rw [E2ECompleteness.getD_ofFn' _ hk]
      show (vals.getD (2 * k) 0 + r * (vals.getD (2 * k) 0 + vals.getD (2 * k + 1) 0)).toPoly.natDegree ≤ _
      rw [tp_add, tp_mul, tp_add]
      have h1 := h (2 * k)
      have h2 := h (2 * k + 1)
      have h3 := natDegree_add_le (vals.getD (2 * k) 0).toPoly (vals.getD (2 * k + 1) 0).toPoly
      have h4 := natDegree_mul_le (p := r.toPoly)
        (q := (vals.getD (2 * k) 0).toPoly + (vals.getD (2 * k + 1) 0).toPoly)
      have h5 := natDegree_add_le (vals.getD (2 * k) 0).toPoly
        (r.toPoly * ((vals.getD (2 * k) 0).toPoly + (vals.getD (2 * k + 1) 0).toPoly))
      omega
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega), Option.getD_none, tp_zero,
        natDegree_zero]
      exact Nat.zero_le _

/-- **The copy's degree**: `deg(copy + ℓ) ≤ max(2^r − 1, r 2^(r−1))`. -/
theorem copyPoly_natDegree (tr : Trace) (table : Table) (c slot : ℕ) :
    (copyPoly tr table c slot).toPoly.natDegree ≤
      max (2 ^ tr.height table.opcode - 1) (tr.height table.opcode * 2 ^ (tr.height table.opcode - 1)) := by
  unfold copyPoly
  rw [tp_add]
  refine le_trans (natDegree_add_le _ _) (max_le_max (by
    have := tablePolys_natDegree tr table.opcode c; omega) ?_)
  refine le_trans (natDegree_mleP _ _ 0 fun k ↦ ?_) ?_
  · by_cases hk : k < 2 ^ tr.height table.opcode
    · rw [E2ECompleteness.getD_ofFn' _ hk, tp_C, natDegree_C]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega), Option.getD_none, tp_zero,
        natDegree_zero]
  · rw [Nat.zero_add, List.map_map]
    refine le_trans (List.sum_le_length_nsmul _ (2 ^ (tr.height table.opcode - 1)) fun x hx ↦ ?_) ?_
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      exact coordinateP_natDegree _ (List.mem_range.mp hl)
    · simp

/-- A constraint of degree at most `D + 2^r` on `V_r`, lifted, has degree at most `D + 2^{r_W}`. -/
theorem item_natDegree {M : Poly} {r rW D : ℕ} (hr : r ≤ rW) (hM : M.toPoly.natDegree ≤ D + 2 ^ r) :
    (M * liftP r rW).toPoly.natDegree ≤ D + 2 ^ rW := by
  rw [tp_mul]
  have := natDegree_mul_le (p := M.toPoly) (q := (liftP r rW).toPoly)
  rw [liftP_natDegree hr] at this
  have : 2 ^ r ≤ 2 ^ rW := Nat.pow_le_pow_right (by norm_num) hr
  omega

/-- **Every table constraint, lifted, has degree at most `D + 2^{r_W}`.** -/
theorem tableItems_deg (tr : Trace) {table : Table} (htab : table ∈ tables) :
    ∀ it ∈ tableItems tr table, (it.1 * it.2).toPoly.natDegree ≤ tr.shape.constraintDegree + 2 ^ tr.shape.constraintVars := by
  have hr := height_le_constraintVars tr table.opcode
  obtain ⟨hJD, hCD, hBD⟩ := le_constraintDegree tr.shape htab
  have hn := Nat.one_le_two_pow (n := tr.height table.opcode)
  have hcol : ∀ c, ((tablePolys tr table.opcode).getD c 0).toPoly.natDegree ≤ 2 ^ tr.height table.opcode - 1 :=
    fun c ↦ by have := tablePolys_natDegree tr table.opcode c; omega
  intro it hit
  rcases mem_tableItems hit with ⟨hJ, rfl | rfl⟩ | rfl | ⟨hB, c, hc, slot, hslot, rfl⟩
  · refine item_natDegree hr ?_
    have h1 := hJD hJ
    unfold UniStatement.degree at h1
    unfold colP
    rw [tp_add, tp_mul]
    have := natDegree_add_le ((tablePolys tr table.opcode).getD (colIdx table.columns "b") 0).toPoly
      (((tablePolys tr table.opcode).getD (colIdx table.columns "v_cond") 0).toPoly *
        ((tablePolys tr table.opcode).getD (colIdx table.columns "w") 0).toPoly)
    have := natDegree_mul_le (p := ((tablePolys tr table.opcode).getD (colIdx table.columns "v_cond") 0).toPoly)
      (q := ((tablePolys tr table.opcode).getD (colIdx table.columns "w") 0).toPoly)
    have := hcol (colIdx table.columns "b")
    have := hcol (colIdx table.columns "v_cond")
    have := hcol (colIdx table.columns "w")
    unfold Trace.height at *
    omega
  · refine item_natDegree hr ?_
    have h1 := hJD hJ
    unfold UniStatement.degree at h1
    unfold colP
    rw [tp_mul, tp_add, tp_one]
    have := natDegree_add_le ((tablePolys tr table.opcode).getD (colIdx table.columns "b") 0).toPoly 1
    have := natDegree_mul_le (p := ((tablePolys tr table.opcode).getD (colIdx table.columns "v_cond") 0).toPoly)
      (q := ((tablePolys tr table.opcode).getD (colIdx table.columns "b") 0).toPoly + 1)
    have := hcol (colIdx table.columns "b")
    have := hcol (colIdx table.columns "v_cond")
    rw [natDegree_one] at *
    unfold Trace.height at *
    omega
  · refine item_natDegree hr ?_
    unfold UniStatement.degree at hCD
    unfold counterPoly
    rw [tp_add, tp_one]
    have h1 := natDegree_foldl_mul table.countColumns (fun c ↦ (tablePolys tr table.opcode).getD c 0)
      (2 ^ tr.height table.opcode - 1) hcol (colPolyK (tr.height table.opcode) (inverseColumn tr table.opcode))
    have h2 := colPolyK_natDegree_lt (tr.height table.opcode) (inverseColumn tr table.opcode)
    have h3 := natDegree_add_le (table.countColumns.foldl (fun p c ↦ p * (tablePolys tr table.opcode).getD c 0)
      (colPolyK (tr.height table.opcode) (inverseColumn tr table.opcode))).toPoly 1
    rw [natDegree_one] at h3
    have h4 : (2 ^ tr.height table.opcode - 1) * (1 + table.countColumns.length) =
        (2 ^ tr.height table.opcode - 1) + table.countColumns.length * (2 ^ tr.height table.opcode - 1) := by ring
    unfold Trace.height at *
    omega
  · refine item_natDegree hr ?_
    show (copyPoly tr table c slot).toPoly.natDegree ≤ _
    have h1 := hBD hB
    unfold UniStatement.degree at h1
    have h2 := copyPoly_natDegree tr table c slot
    have h3 : tr.height table.opcode * 2 ^ (tr.height table.opcode - 1) =
        tr.height table.opcode * (2 ^ tr.height table.opcode / 2) := by
      rcases Nat.eq_zero_or_pos (tr.height table.opcode) with h0 | hpos
      · rw [h0]; simp
      · congr 1
        rw [show tr.height table.opcode = tr.height table.opcode - 1 + 1 by omega, pow_succ,
          Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]
    unfold Trace.height at *
    omega

/-- **Every public line, lifted, has degree at most `D + 2^{r_W}`.** -/
theorem publicItems_deg (tr : Trace) (words : List E) :
    ∀ it ∈ publicItems tr words, (it.1 * it.2).toPoly.natDegree ≤
      tr.shape.constraintDegree + 2 ^ tr.shape.constraintVars := by
  have hD := public_le_constraintDegree tr.shape
  unfold UniStatement.degree at hD
  have hr : 1 ≤ tr.shape.constraintVars ∨ tr.shape.constraintVars = 0 := by omega
  intro it hit
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hit
  dsimp only
  rw [tp_mul]
  refine le_trans natDegree_mul_le ?_
  rw [tp_add, tp_add, tp_mul, tp_C, tp_C, tp_X]
  have h1 := colPolyK_natDegree_lt tr.shape.logMemory (tr.memory.getD x.2 #[])
  have h2 := natDegree_add_le (colPolyK tr.shape.logMemory (tr.memory.getD x.2 #[])).toPoly (C x.1.1)
  have h3 := natDegree_add_le ((colPolyK tr.shape.logMemory (tr.memory.getD x.2 #[])).toPoly + C x.1.1)
    (X * C (x.1.1 + x.1.2))
  have h4 := natDegree_mul_le (p := (X : E[X])) (q := C (x.1.1 + x.1.2))
  rw [natDegree_C] at h2 h4
  rw [natDegree_X] at h4
  rcases hr with hr | hr
  · rw [liftP_natDegree hr]
    have : 2 ≤ 2 ^ tr.shape.constraintVars := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ tr.shape.constraintVars := Nat.pow_le_pow_right (by norm_num) hr
    omega
  · have hlm := logMemory_le_constraintVars tr
    rw [hr] at hlm ⊢
    have h0 : 2 ^ tr.shape.logMemory = 1 := by rw [show tr.shape.logMemory = 0 by omega]; rfl
    have hl : (liftP 1 0).toPoly = 1 := by
      rw [liftP_toPoly]
      simp
    rw [hl, natDegree_one]
    omega

theorem foldl_addItem_deg (gamma : E) (B : ℕ) : ∀ (items : List Item) (s : Poly × E),
    s.1.toPoly.natDegree ≤ B → (∀ it ∈ items, (it.1 * it.2).toPoly.natDegree ≤ B) →
      (items.foldl (addItem gamma) s).1.toPoly.natDegree ≤ B
  | [], _, h, _ => h
  | it :: rest, s, h, hits => by
    rw [List.foldl_cons]
    refine foldl_addItem_deg gamma B rest _ ?_ (fun x hx ↦ hits x (List.mem_cons_of_mem _ hx))
    show (s.1 + pC s.2 * it.1 * it.2).toPoly.natDegree ≤ B
    rw [tp_add, mul_assoc, tp_mul, tp_C]
    refine le_trans (natDegree_add_le _ _) (max_le h (le_trans (natDegree_C_mul_le _ _) (hits it (by simp))))

/-- **The numerator's degree is at most `D + 2^{r_W}`.** -/
theorem numerator_natDegree_le (tr : Trace) (gamma : E) (words : List E) :
    (constraintNumerator tr gamma words).toPoly.natDegree ≤ tr.shape.constraintDegree + 2 ^ tr.shape.constraintVars := by
  rw [constraintNumerator_eq]
  refine foldl_addItem_deg gamma _ _ (0, 1) (by rw [tp_zero, natDegree_zero]; exact Nat.zero_le _) fun it hit ↦ ?_
  rcases List.mem_append.mp hit with h | h
  · obtain ⟨table, htab, hit'⟩ := List.mem_flatMap.mp h
    exact tableItems_deg tr htab it hit'
  · exact publicItems_deg tr words it h

/-- **The constraint quotient's degree is at most `Shape.constraintDegree`.** -/
theorem constraintQuotient_natDegree_le {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) (gamma : E) :
    (constraintQuotient tr gamma (publicWordsOf tr.publicInput)).toPoly.natDegree ≤ tr.shape.constraintDegree := by
  have hmul := constraintQuotient_mul hH hS hC gamma
  have hN := numerator_natDegree_le tr gamma (publicWordsOf tr.publicInput)
  by_cases hQ : (constraintQuotient tr gamma (publicWordsOf tr.publicInput)).toPoly = 0
  · rw [hQ, natDegree_zero]
    exact Nat.zero_le _
  · rw [← hmul, mul_comm, (Domain.wP_monic _).natDegree_mul' hQ, Domain.wP_natDegree] at hN
    omega

/-- **The constraint quotient fits its chunks** `chunks (D + 1)`: its degree is below `Σ 2^e`. -/
theorem constraintQuotient_fits {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) (gamma : E) :
    (constraintQuotient tr gamma (publicWordsOf tr.publicInput)).toPoly.natDegree <
      ((chunks (tr.shape.constraintDegree + 1)).map (2 ^ ·)).sum := by
  have h1 := constraintQuotient_natDegree_le hH hS hC gamma
  have h2 := (chunks_spec (n := tr.shape.constraintDegree + 1) (by omega)).2.1
  omega


end UniComplete.AlgC

/-- info: 'UniComplete.AlgC.constraintNumerator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.constraintNumerator_eq

/-- info: 'UniComplete.AlgC.numerator_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.numerator_dvd

/-- info: 'UniComplete.AlgC.constraintQuotient_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.constraintQuotient_mul

/-- info: 'UniComplete.AlgC.constraintQuotient_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.constraintQuotient_natDegree_le

/-- info: 'UniComplete.AlgC.constraintQuotient_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.constraintQuotient_fits
