-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Cvec

/-!
# `CvecOkP`: the constraint vectors' vanishing gives the rows' constraints

`cvecOk`: where every entry of every row's constraint vector vanishes on `V_{r_W}`, the counts are in
range (out of range the vectors hold a `1`) and `RowConstraints` holds: each constraint `(M_i, W_i)` has
`M_i = 1` on its table's domain, so `W_i(ω_x) = 0` there, and `W_i(ω_x)` is the constraint on `C1`'s row
`x` read in `K`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

/-- **How `C1` is read** (the bridges the reading of `C1`'s columns at the points rests on). -/
structure C1Reading (D : Deployment) : Prop where
  beta : BetaCantor
  functionals : FunctionalsCorrect (D.shape.heights.getD opBlake2s 0)
  limbs : C1Limbs D.shape
  aligned : LayoutAligned (layoutOf D.shape .c1)
  vars : (layoutOf D.shape .c1).vars ≤ batchVars D.shape
  rW : D.shape.constraintVars ≤ 24

theorem le_foldl_max : ∀ (l : List ℕ) (b a : ℕ), a ∈ l ∨ a ≤ b → a ≤ l.foldl max b
  | [], _, _, h => by simpa using h
  | x :: l, b, a, h => by
    rw [List.foldl_cons]
    refine le_foldl_max l (max b x) a ?_
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl h
    · exact Or.inr (le_trans h (le_max_left _ _))

theorem height_le_rW (S : Shape) (o : ℕ) : S.heights.getD o 0 ≤ S.constraintVars := by
  unfold Shape.constraintVars
  by_cases ho : o < S.heights.length
  · refine le_foldl_max _ 0 _ (Or.inl (List.mem_append_left _ ?_))
    rw [List.getD_eq_getElem _ _ ho]
    exact List.getElem_mem ho
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem logMemory_le_rW (S : Shape) : S.logMemory ≤ S.constraintVars :=
  le_foldl_max _ 0 _ (Or.inl (List.mem_append_right _ (List.mem_singleton_self _)))

theorem tables_opcode (o : ℕ) (ho : o < 6) : (tables.getD o default).opcode = o := by
  interval_cases o <;> rfl

theorem tables_mem (o : ℕ) (ho : o < 6) : tables.getD o default ∈ tables := by
  rw [List.getD_eq_getElem _ _ (by simp [tables]; omega)]
  exact List.getElem_mem _

theorem qflockSlot_lt {n : String} {slot : ℕ} (h : qflockSlot n = some slot) : slot < 20 := by
  unfold qflockSlot at h
  have := List.findIdx?_eq_some_iff_getElem.mp h
  obtain ⟨hlt, _⟩ := this
  simpa [blake2sSlots] using hlt

theorem qflockSlot_empty : qflockSlot "" = none := by decide

theorem ofK_list_prod (l : List K) : ofK l.prod = (l.map ofK).prod := map_list_prod (algebraMap K E) l

theorem lift_mul_eval (h : BetaCantor) (r m x : ℕ) (hx : x < 2 ^ r) (hx24 : x < 2 ^ 24) (W : Polynomial E) :
    (liftP r m * W).eval (pointE x) = W.eval (pointE x) := by
  rw [Polynomial.eval_mul, liftP_eval_pointE h r m x hx hx24, one_mul]

/-- **The constraint vectors give the rows' constraints.** -/
theorem cvecOk (D : Deployment) (hr : C1Reading D) : CvecOkP D := by
  intro s c hall
  have hfit : CountsFit D.shape s.2 := by
    by_contra hn
    have := hall 0 (Nat.two_pow_pos _) 1 (by simp [cvecOf, hn])
    exact one_ne_zero this
  set S := D.shape
  set rW := S.constraintVars
  set pw := publicWordsOf s.1.toList
  have hzero : ∀ mw ∈ constraintsP S c pw, ∀ x < 2 ^ rW, (mw.1 * mw.2).eval (pointE x) = 0 :=
    fun mw hmw x hx ↦ hall x hx _ (by
      unfold cvecOf
      rw [ite_eq_left (show CountsFit D.shape s.2 from hfit)]
      exact List.mem_map_of_mem (f := fun mw ↦ (mw.1 * mw.2).eval (pointE x)) hmw)
  -- A table's constraint vanishes on its rows.
  have htab : ∀ o < 6, ∀ W, (liftP (S.heights.getD o 0) rW, W) ∈ tableConstraintsP S c (tables.getD o default) →
      ∀ x < 2 ^ S.heights.getD o 0, W.eval (pointE x) = 0 := by
    intro o ho W hW x hx
    have hx' : x < 2 ^ rW := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (height_le_rW S o))
    have hx24 : x < 2 ^ 24 := lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by norm_num) hr.rW)
    have := hzero _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, tables_mem o ho, hW⟩)) x hx'
    rwa [lift_mul_eval hr.beta _ _ x hx hx24] at this
  -- The columns at the points.
  have hcol : ∀ o < 6, ∀ i < (tables.getD o default).width, ∀ x < 2 ^ S.heights.getD o 0,
      (c1P S c (.table o i)).eval (pointE x) = ofK (c1Val D c (.table o i) (S.heights.getD o 0) x) := by
    intro o ho i hi x hx
    obtain ⟨off, hl⟩ := hr.limbs.1 o ho i hi
    exact c1P_eval_pointE D hr.beta hr.aligned hr.vars c _ _ off x hl
      ((height_le_rW S o).trans hr.rW) hx
  have hinv : ∀ o < 6, ∀ x < 2 ^ S.heights.getD o 0,
      (c1P S c (.inverse o)).eval (pointE x) = ofK (c1Val D c (.inverse o) (S.heights.getD o 0) x) := by
    intro o ho x hx
    obtain ⟨off, hl⟩ := hr.limbs.2.1 o ho
    exact c1P_eval_pointE D hr.beta hr.aligned hr.vars c _ _ off x hl
      ((height_le_rW S o).trans hr.rW) hx
  refine ⟨hfit, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- JUMP
    intro x hx
    have hmem1 : (liftP (S.heights.getD 4 0) rW,
        c1P S c (.table 4 (colIdx jumpColumns "b")) + c1P S c (.table 4 (colIdx jumpColumns "v_cond")) *
          c1P S c (.table 4 (colIdx jumpColumns "w"))) ∈ tableConstraintsP S c (tables.getD 4 default) := by
      unfold tableConstraintsP
      rw [show tables.getD 4 default = ⟨opJump, jumpColumns, flushesJump⟩ from rfl]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
    have hmem2 : (liftP (S.heights.getD 4 0) rW,
        c1P S c (.table 4 (colIdx jumpColumns "v_cond")) *
          (c1P S c (.table 4 (colIdx jumpColumns "b")) + 1)) ∈ tableConstraintsP S c (tables.getD 4 default) := by
      unfold tableConstraintsP
      rw [show tables.getD 4 default = ⟨opJump, jumpColumns, flushesJump⟩ from rfl]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have e1 := htab 4 (by norm_num) _ hmem1 x hx
    have e2 := htab 4 (by norm_num) _ hmem2 x hx
    have hw : ∀ n, colIdx jumpColumns n < 14 → (c1P S c (.table 4 (colIdx jumpColumns n))).eval (pointE x) =
        ofK (c1Val D c (.table 4 (colIdx jumpColumns n)) (S.heights.getD 4 0) x) :=
      fun n hn ↦ hcol 4 (by norm_num) _ (by simpa [tables, Table.width, jumpColumns] using hn) x hx
    simp only [Polynomial.eval_add, Polynomial.eval_mul, eval_one] at e1 e2
    rw [hw "b" (by decide), hw "v_cond" (by decide), hw "w" (by decide)] at e1
    rw [hw "b" (by decide), hw "v_cond" (by decide)] at e2
    refine ⟨ofK_injective ?_, ofK_injective ?_⟩
    · rw [ofK_add, ofK_mul, ofK_zero]; exact e1
    · rw [ofK_mul, ofK_add, ofK_one, ofK_zero]; exact e2
  · -- the counters
    intro o ho x hx
    have hmem : (liftP (S.heights.getD o 0) rW, c1P S c (.inverse o) *
        ((tables.getD o default).countColumns.map fun j ↦ c1P S c (.table o j)).prod + 1) ∈
          tableConstraintsP S c (tables.getD o default) := by
      unfold tableConstraintsP
      rw [tables_opcode o ho]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    have e := htab o ho _ hmem x hx
    rw [Polynomial.eval_add, Polynomial.eval_mul, eval_one, eval_list_prod_of, List.map_map,
      hinv o ho x hx] at e
    have hc : ∀ j ∈ (tables.getD o default).countColumns,
        (Polynomial.eval (pointE x) ∘ fun j ↦ c1P S c (.table o j)) j =
          ofK (c1Val D c (.table o j) (S.heights.getD o 0) x) := by
      intro j hj
      have : j < (tables.getD o default).width := by
        unfold Table.countColumns at hj
        exact List.mem_range.mp (List.mem_filter.mp hj).1
      exact hcol o ho j this x hx
    rw [List.map_congr_left hc] at e
    refine ofK_injective ?_
    rw [ofK_mul, ofK_one, ofK_list_prod, List.map_map]
    exact (CharTwo.add_eq_zero.mp e)
  · -- the copies
    intro x hx col slot hs
    obtain ⟨off, hl⟩ := hr.limbs.2.2.2.2
    have hcol37 : col < 37 := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by simp [blake2sColumns]; omega), qflockSlot_empty] at hs
      cases hs
    have hmem : (liftP (S.heights.getD 5 0) rW, c1P S c (.table 5 col) + slotP S c slot) ∈
        tableConstraintsP S c (tables.getD 5 default) := by
      unfold tableConstraintsP
      rw [show tables.getD 5 default = ⟨opBlake2s, blake2sColumns, flushesBlake2s⟩ from rfl]
      simp only [opJump, opBlake2s, show ¬ (5 : ℕ) = 4 by norm_num, ite_false, ite_true,
        List.nil_append]
      refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨col, ?_, ?_⟩)
      · exact List.mem_range.mpr (by simpa [Table.width, blake2sColumns] using hcol37)
      · rw [hs]; rfl
    have e := htab 5 (by norm_num) _ hmem x hx
    rw [Polynomial.eval_add, hcol 5 (by norm_num) col (by simpa [tables, Table.width, blake2sColumns]
      using hcol37) x hx, slotP_eval_pointE D hr.beta hr.functionals
      ((height_le_rW S 5).trans hr.rW) hr.aligned hr.vars c off hl slot x
      (by have := qflockSlot_lt hs; omega) hx] at e
    have hq : qfOff D = off := by
      unfold qfOff
      rw [c1Layout_eq, hl]
      rfl
    rw [hq]
    exact (ofK_injective (CharTwo.add_eq_zero.mp e)).trans (by rw [add_assoc])
  · -- the public lines
    intro k hk
    obtain ⟨off, hl⟩ := hr.limbs.2.2.1 k (by omega)
    have hmem : (liftP 1 rW, c1P S c (.memory k) + C ((linesOf pw).getD k (0, 0)).1 +
        X * C (((linesOf pw).getD k (0, 0)).1 + ((linesOf pw).getD k (0, 0)).2)) ∈ constraintsP S c pw := by
      refine List.mem_append_right _ (List.mem_map.mpr ⟨((linesOf pw).getD k (0, 0), k), ?_, rfl⟩)
      have hk3 : k < ((linesOf pw).zip (List.range 3)).length := by simp [linesOf]; omega
      have := List.getElem_mem hk3
      rw [List.getElem_zip, List.getElem_range] at this
      rw [List.getD_eq_getElem _ _ (by simp [linesOf]; omega)]
      exact this
    have hlm : S.logMemory ≤ 24 := (logMemory_le_rW S).trans hr.rW
    have h1 : 1 < 2 ^ S.logMemory := Nat.one_lt_two_pow D.logMemory_pos.ne'
    have hpt : ∀ x < 2, (c1P S c (.memory k)).eval (pointE x) =
        ofK (c1Val D c (.memory k) S.logMemory x) := fun x hx ↦
      c1P_eval_pointE D hr.beta hr.aligned hr.vars c _ _ off x hl hlm (by omega)
    have hrW1 : 1 ≤ rW := (Nat.one_le_iff_ne_zero.mpr D.logMemory_pos.ne').trans (logMemory_le_rW S)
    have e0 := hzero _ hmem 0 (Nat.two_pow_pos _)
    have e1 := hzero _ hmem 1 (Nat.one_lt_two_pow (by omega))
    rw [lift_mul_eval hr.beta 1 rW 0 (by norm_num) (by norm_num)] at e0
    rw [lift_mul_eval hr.beta 1 rW 1 (by norm_num) (by norm_num)] at e1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_X] at e0 e1
    rw [hpt 0 (by norm_num), pointE_zero, zero_mul, add_zero] at e0
    rw [hpt 1 (by norm_num)] at e1
    have hp1 : pointE 1 = 1 := by
      rw [pointE_eq_omega hr.beta (by norm_num), Heap.omega_one (cantorE hr.beta) (by norm_num)]
    rw [hp1, one_mul] at e1
    constructor
    · rw [← CharTwo.add_eq_zero.mp e0]
      unfold toK
      simp
      rfl
    · have h2 : ofK (c1Val D c (.memory k) S.logMemory 1) = ((linesOf pw).getD k (0, 0)).2 := by
        have := e1
        rw [add_assoc, ← add_assoc ((linesOf pw).getD k (0, 0)).1, CharTwo.add_self_eq_zero,
          zero_add] at this
        exact CharTwo.add_eq_zero.mp this
      rw [← h2]
      unfold toK
      simp
      rfl
