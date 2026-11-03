-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Main

/-!
# Every heap block's leaves from its identity

The rows' fingerprints (`pullP_eval`, `pushP_eval`: a table's pull and push products at `ω_k` are the
fingerprints of `tupleK` of its forms at `C1`'s row `k`), and each block's leaf identity at `ω_k`, `k < 2^r`
(`tableHolds`, `memHolds`, `unusedHolds`; the bytecode's from `BcTupleEval`, the setup's tuple claim at
`(α, ω_k)`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

/-! ## Forms and tuples at a row -/

theorem formP_eval (f : Form) (cols : ℕ → Polynomial E) (row : ℕ → K) (θ : E)
    (hcol : ∀ i, (cols i).eval θ = ofK (row i)) (hK : ∀ mc ∈ f, ofK (toK mc.2) = mc.2) :
    (formP f cols).eval θ = ofK (formK f row) := by
  induction f with
  | nil => simp [formP, formK]
  | cons mc f ih =>
    have ih' := ih fun m hm ↦ hK m (List.mem_cons_of_mem _ hm)
    have hmc := hK mc (List.mem_cons_self ..)
    unfold formP formK at *
    rw [List.map_cons, List.sum_cons, Polynomial.eval_add, ih', List.map_cons, List.sum_cons, ofK_add]
    congr 1
    rcases mc with ⟨m, cf⟩
    rcases m with _ | ⟨i, _ | ⟨j, _ | ⟨_, _⟩⟩⟩
    · simp [hmc]
    · simp [Polynomial.eval_mul, hcol, ofK_mul, hmc]
    · simp [Polynomial.eval_mul, hcol, ofK_mul, hmc, mul_assoc]
    · simp

theorem tupleP_eval (tup : List Form) (weights : Array E) (cols : ℕ → Polynomial E) (row : ℕ → K) (θ : E)
    (hcol : ∀ i, (cols i).eval θ = ofK (row i)) (hK : ∀ f ∈ tup, ∀ mc ∈ f, ofK (toK mc.2) = mc.2)
    (hlen : tup.length ≤ 16) :
    (tupleP tup weights cols).eval θ = ∑ s : Fin 16, weights.getD s.val 0 * ofK ((tupleK tup row).get s) := by
  unfold tupleP tupleK
  rw [eval_listSum, List.map_map, List.range_eq_range', sum_zip_range _ tup 0 []]
  simp only [Vector.get_ofFn]
  rw [sum_fin16 (fun s ↦ weights.getD s 0 * ofK (formK (tup.getD s []) row))]
  rw [← Finset.sum_range_add_sum_Ico _ hlen]
  have hz : ∑ s ∈ Ico tup.length 16, weights.getD s 0 * ofK (formK (tup.getD s []) row) = 0 :=
    Finset.sum_eq_zero fun s hs ↦ by
      rw [Finset.mem_Ico] at hs
      rw [List.getD_eq_default _ _ hs.1]
      simp [formK]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hs
  simp only [Function.comp_apply, zero_add, Polynomial.eval_mul, eval_C]
  rw [formP_eval _ cols row θ hcol (hK _ (by rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem hs))]

/-! ## The rows' products -/

theorem map_zip_fst {α β γ : Type} (l₁ : List α) (l₂ : List β) (h : l₁.length ≤ l₂.length) (g : α → γ) :
    (l₁.zip l₂).map (fun p ↦ g p.1) = l₁.map g := by
  rw [show (fun p : α × β ↦ g p.1) = g ∘ Prod.fst from rfl, ← List.map_map, List.map_fst_zip h]

theorem map_zip_snd {α β γ : Type} (l₁ : List α) (l₂ : List β) (h : l₂.length ≤ l₁.length) (g : β → γ) :
    (l₁.zip l₂).map (fun p ↦ g p.2) = l₂.map g := by
  rw [show (fun p : α × β ↦ g p.2) = g ∘ Prod.snd from rfl, ← List.map_map, List.map_snd_zip h]

/-- **A table's pull product at a row** is the fingerprints' product of its forms at the row. -/
theorem pullP_eval (hE : EqKernelLagrange) (tab : Table) (hlen : tab.flushes.pull.length = tab.flushes.push.length)
    (htup : ∀ tup ∈ tab.flushes.pull ++ tab.flushes.push, tup.length ≤ 16 ∧ ∀ f ∈ tup, ∀ mc ∈ f, ofK (toK mc.2) = mc.2)
    (cols : ℕ → Polynomial E) (row : ℕ → K) (θ : E) (hcol : ∀ i, (cols i).eval θ = ofK (row i)) (ch : List E) :
    (pullP tab (eqKernel (alphasOf ch)) (betaOf ch) cols).eval θ =
      Heap.fpProd (Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0))
        (tab.flushes.pull.map fun tup ↦ tupleK tup row) := by
  unfold pullP Heap.fpProd
  rw [eval_list_prod_of, List.map_map, List.map_map]
  refine (congrArg List.prod (map_zip_fst _ _ (le_of_eq hlen)
    (fun tup ↦ (C (betaOf ch) + tupleP tup (eqKernel (alphasOf ch)) cols).eval θ))).trans
    (congrArg List.prod (List.map_congr_left fun tup htp ↦ ?_))
  have ht := htup tup (List.mem_append_left _ htp)
  simp only [Function.comp_apply]
  rw [Polynomial.eval_add, eval_C, tupleP_eval tup _ cols row θ hcol ht.2 ht.1, fp_eq hE]
  rfl

/-- **A table's push product at a row.** -/
theorem pushP_eval (hE : EqKernelLagrange) (tab : Table) (hlen : tab.flushes.pull.length = tab.flushes.push.length)
    (htup : ∀ tup ∈ tab.flushes.pull ++ tab.flushes.push, tup.length ≤ 16 ∧ ∀ f ∈ tup, ∀ mc ∈ f, ofK (toK mc.2) = mc.2)
    (cols : ℕ → Polynomial E) (row : ℕ → K) (θ : E) (hcol : ∀ i, (cols i).eval θ = ofK (row i)) (ch : List E) :
    (pushP tab (eqKernel (alphasOf ch)) (betaOf ch) cols).eval θ =
      Heap.fpProd (Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0))
        (tab.flushes.push.map fun tup ↦ tupleK tup row) := by
  unfold pushP Heap.fpProd
  rw [eval_list_prod_of, List.map_map, List.map_map]
  refine (congrArg List.prod (map_zip_snd _ _ (le_of_eq hlen.symm)
    (fun tup ↦ (C (betaOf ch) + tupleP tup (eqKernel (alphasOf ch)) cols).eval θ))).trans
    (congrArg List.prod (List.map_congr_left fun tup htp ↦ ?_))
  have ht := htup tup (List.mem_append_right _ htp)
  simp only [Function.comp_apply]
  rw [Polynomial.eval_add, eval_C, tupleP_eval tup _ cols row θ hcol ht.2 ht.1, fp_eq hE]
  rfl

/-! ## Columns of `C1` absent from the layout -/

theorem mleK_empty : ∀ pt : List K, mleK #[] pt = 0
  | [] => rfl
  | r :: pt => by
    have : mleK #[] (r :: pt) = mleK (Array.ofFn (n := (#[] : Array K).size / 2) fun i ↦
        (#[] : Array K).getD (2 * i.val) 0 + r * ((#[] : Array K).getD (2 * i.val) 0 +
          (#[] : Array K).getD (2 * i.val + 1) 0)) pt := rfl
    rw [this, show (Array.ofFn (n := (#[] : Array K).size / 2) fun i ↦
        (#[] : Array K).getD (2 * i.val) 0 + r * ((#[] : Array K).getD (2 * i.val) 0 +
          (#[] : Array K).getD (2 * i.val + 1) 0)) = #[] from by simp]
    exact mleK_empty pt

/-- An absent column's polynomial is `0`, and its value. -/
theorem c1P_eval_absent (D : Deployment) (c : Stk) (col : Column) (v x : ℕ)
    (hl : (layoutOf D.shape .c1).limbs col = []) :
    (c1P D.shape c col).eval (pointE x) = ofK (c1Val D c col v x) := by
  unfold c1P colPoly c1Val c1Block basisValue
  rw [hl, c1Layout_eq, hl]
  simp [mleK_empty]

/-! ## How the heap is read -/

/-- **The setup's bytecode tuple at `(α, ω_x)`**: `Σ_s eq(α, s)` times slot `s`'s value at instruction `x`. -/
def BcTupleEval (D : Deployment) : Prop :=
  ∀ (ch : List E) (x : ℕ), x < 2 ^ D.shape.logBytecode →
    (suP D.shape (setupStk D) .bytecodeTuple
        (fun l ↦ if l < 4 then C ((alphasOf ch).getD l 0) else digitP (l - 4))).eval (pointE x) =
      ∑ s : Fin 16, (eqKernel (alphasOf ch)).getD s.val 0 * ofK (slotVal D s.val x)

/-- **The bridges the heap's reading rests on.** -/
structure HeapReading (D : Deployment) : Prop where
  c1 : C1Reading D
  absent : ∀ o < 6, ∀ i, (tables.getD o default).width ≤ i → (layoutOf D.shape .c1).limbs (.table o i) = []
  heap : HeapGood D.shape
  zAct : ZActZero
  eqk : EqKernelLagrange
  gpowK : GpowInK
  tablesF : TablesFacts
  setupLimbs : SetupLimbs D.shape
  setupAligned : LayoutAligned (layoutOf D.shape .setup)
  setupVars : (layoutOf D.shape .setup).vars ≤ batchVars D.shape
  hB2 : 2 ≤ D.shape.heights.getD opBlake2s 0
  heightsLt : ∀ o < 6, D.shape.heights.getD o 0 < 24
  bcTuple : BcTupleEval D

theorem eK_eq (w : UInt64) : eK w = ofK (K.ofLane w) := by
  unfold eK eNew
  rw [ofLimbs_eq, show K.ofLane 0 = 0 from rfl, ofK_zero]
  ring

theorem toK_ofK (a : K) : toK (ofK a) = a := by unfold toK; simp

/-- A table column of `C1` at `ω_x`, present or absent. -/
theorem c1Col_eval (D : Deployment) (hr : HeapReading D) (c : Stk) (o : ℕ) (ho : o < 6) (i x : ℕ)
    (hx : x < 2 ^ D.shape.heights.getD o 0) :
    (c1P D.shape c (.table o i)).eval (pointE x) = ofK (c1Row D c o x i) := by
  unfold c1Row
  by_cases hi : i < (tables.getD o default).width
  · obtain ⟨off, hl⟩ := hr.c1.limbs.1 o ho i hi
    exact c1P_eval_pointE D hr.c1.beta hr.c1.aligned hr.c1.vars c _ _ off x hl
      ((height_le_rW D.shape o).trans hr.c1.rW) hx
  · exact c1P_eval_absent D c _ _ x (hr.absent o ho i (by omega))

/-! ## The blocks -/

/-- The weights `eq(α, s)`. -/
noncomputable abbrev wt (ch : List E) (s : ℕ) : E := (eqKernel (alphasOf ch)).getD s 0

theorem fp_memTupleK (hE : EqKernelLagrange) (D : Deployment) (c : Stk) (ch : List E) (cnt : K) (x : ℕ) :
    Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) (memTupleK D c cnt x) =
      ch.getD 4 0 + wt ch 0 * ofK (toK sepMem) + wt ch 1 * ofK (suVal D .address D.shape.logMemory x) +
        wt ch 2 * ofK cnt + wt ch 3 * ofK (c1Val D c (.memory 0) D.shape.logMemory x) +
        wt ch 4 * ofK (c1Val D c (.memory 1) D.shape.logMemory x) +
        wt ch 5 * ofK (c1Val D c (.memory 2) D.shape.logMemory x) := by
  rw [fp_eq hE]
  unfold memTupleK
  simp only [Vector.get_ofFn]
  rw [sum_fin16 (fun s ↦ wt ch s * ofK (if s = 0 then toK sepMem
    else if s = 1 then suVal D .address D.shape.logMemory x
    else if s = 2 then cnt
    else if s < 6 then c1Val D c (.memory (s - 3)) D.shape.logMemory x else 0))]
  simp (config := {decide := true}) only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ite_true, ite_false, ofK_zero, mul_zero, add_zero, Nat.reduceSub]
  ring

theorem fp_bcTupleK (hE : EqKernelLagrange) (D : Deployment) (ch : List E) (cnt : K) (x : ℕ) :
    Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) (bcTupleK D cnt x) =
      ch.getD 4 0 + ∑ s : Fin 16, wt ch s.val * ofK (slotVal D s.val x) + wt ch 2 * ofK cnt := by
  rw [fp_eq hE]
  unfold bcTupleK
  simp only [Vector.get_ofFn, ofK_add, mul_add, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 2
  rw [sum_fin16 (fun s ↦ wt ch s * ofK (if s = 2 then cnt else 0))]
  simp (config := {decide := true}) only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ite_true, ite_false, ofK_zero, mul_zero, add_zero]

theorem pointE_shift_zero {k r : ℕ} (hk : k < 2 ^ r) : pointE (k >>> r) = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hk, pointE_zero]

theorem fpProd_single {τ : Type} (f : τ → E) (a : τ) : Heap.fpProd f [a] = f a := by
  simp [Heap.fpProd]

section Blocks

variable (D : Deployment) (hr : HeapReading D) (c1 c2 : Stk) (s : USt) (ch : List E) (b : Block) (i : ℕ)

include hr in
/-- The restriction at `ω_k`. -/
theorem restr_eval (hal : 2 ^ b.r ∣ b.position) {k : ℕ} (hk : k < 2 ^ b.r)
    (hpk : b.position + k < 2 ^ 24) :
    (c2P D.shape c2 .heap (mixP b)).eval (pointE k) = heapT D.shape c2 (b.position + k) :=
  c2P_eval_congr _ _ _ _ _ _ _ fun l ↦ mixP_eval_pointE hr.c1.beta b hal hk hpk l

include hr in
/-- **A table's block from its leaf identity.** -/
theorem tableHolds (hfit : CountsFit D.shape s.2) (t : ℕ) (hb : b.leaves = .table t) (ht : t < 6)
    (hrb : b.r = D.shape.heights.getD t 0) (hal : 2 ^ b.r ∣ b.position) (hpos : b.position + 2 ^ b.r ≤ 2 ^ 24)
    (hP : blockP D.shape c1 c2 (stackFor D c1 c2 .setup) s.2 (alphasOf ch) (betaOf ch) b i = 0) :
    (blockK D c1 s.2 b).Holds (Heap.fp (fun j ↦ ch.getD j.val 0) (ch.getD 4 0)) (heapT D.shape c2)
      b.position := by
  intro k hk
  have hbk : blockK D c1 s.2 b = tableBlockK D c1 s.2 b t := by unfold blockK; rw [hb]
  rw [hbk]
  unfold blockP at hP
  rw [hb] at hP
  simp only at hP
  rw [leaf_form] at hP
  have hk' : k < 2 ^ b.r := by
    have := blockK_r D c1 s.2 b
    simp only [Heap.LeafBlock.size, this] at hk
    exact hk
  have hk24 : k < 2 ^ 24 := by omega
  have hw : (digitP b.r).eval (pointE k) = 0 := by
    rw [eval_digitP_pointE hr.c1.beta _ hk24, pointE_shift_zero hk']
  have hw' : (derivative (digitP b.r)).eval (pointE k) = 1 := by rw [derivative_digitP, eval_one]
  have hR := restr_eval D hr c2 b hal hk' (by omega)
  have hcols : ∀ j, (c1P D.shape c1 (.table (tables.getD t default).opcode j)).eval (pointE k) =
      ofK (c1Row D c1 t k j) := by
    intro j
    rw [tables_opcode t ht]
    exact c1Col_eval D hr c1 t ht j k (hrb ▸ hk')
  have hfacts := hr.tablesF _ (tables_mem t ht)
  have hcount : s.2.getD t 0 ≤ 2 ^ b.r := hrb ▸ hfit.2 t ht
  have hZ := hr.zAct hr.c1.beta (s.2.getD t 0) b.r k (hrb ▸ hr.heightsLt t ht) hcount hk'
  unfold tableBlockK
  simp only
  by_cases ha : isActive k (s.2.getD t 0) b.r = true
  · simp only [ha, ite_true]
    have hA := active_of_leaf _ _ _ _ (pointE k) hP hw hw' (hZ.mpr ha)
    rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hZ.mpr ha,
      mul_zero, add_zero, hR, pullP_eval hr.eqk _ hfacts.1 hfacts.2 _ _ _ hcols ch,
      pushP_eval hr.eqk _ hfacts.1 hfacts.2 _ _ _ hcols ch] at hA
    exact CharTwo.add_eq_zero.mp hA
  · simp only [ha, Bool.false_eq_true, ite_false]
    have h1 := padding_of_leaf _ _ _ _ (pointE k) hP hw (fun h0 ↦ ha (hZ.mp h0))
    rw [hR] at h1
    simp [Heap.fpProd, h1]

theorem hk_of (k : ℕ) (hk : k < (blockK D c1 s.2 b).size) : k < 2 ^ b.r := by
  have := blockK_r D c1 s.2 b
  simp only [Heap.LeafBlock.size, this] at hk
  exact hk

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

include hr in
/-- **The memory's block from its leaf identity.** -/
theorem memHolds (hb : b.leaves = .memory) (hrb : b.r = D.shape.logMemory) (hal : 2 ^ b.r ∣ b.position)
    (hpos : b.position + 2 ^ b.r ≤ 2 ^ 24)
    (hP : blockP D.shape c1 c2 (stackFor D c1 c2 .setup) s.2 (alphasOf ch) (betaOf ch) b i = 0) :
    (blockK D c1 s.2 b).Holds (Heap.fp (fun j ↦ ch.getD j.val 0) (ch.getD 4 0)) (heapT D.shape c2)
      b.position := by
  intro k hk
  have hk' := hk_of D c1 s b k hk
  have hk24 : k < 2 ^ 24 := by omega
  have hbk : blockK D c1 s.2 b = Heap.LeafBlock.pair b.r (memTupleK D c1 1)
      (fun x ↦ memTupleK D c1 (c1Val D c1 (.memory 3) D.shape.logMemory x) x) := by
    unfold blockK; rw [hb]
  rw [hbk]
  show heapT D.shape c2 (b.position + k) * Heap.fpProd _ [_] = Heap.fpProd _ [_]
  rw [fpProd_single, fpProd_single, fp_memTupleK hr.eqk, fp_memTupleK hr.eqk]
  unfold blockP at hP
  rw [hb] at hP
  simp only at hP
  have he := congrArg (Polynomial.eval (pointE k)) hP
  have hlm : D.shape.logMemory ≤ 24 := (logMemory_le_rW D.shape).trans hr.c1.rW
  have hkm : k < 2 ^ D.shape.logMemory := hrb ▸ hk'
  have hmem : ∀ j < 4, (c1P D.shape c1 (.memory j)).eval (pointE k) =
      ofK (c1Val D c1 (.memory j) D.shape.logMemory k) := fun j hj ↦ by
    obtain ⟨off, hl⟩ := hr.c1.limbs.2.2.1 j hj
    exact c1P_eval_pointE D hr.c1.beta hr.c1.aligned hr.c1.vars c1 _ _ off k hl hlm hkm
  have haddr : (suP D.shape (stackFor D c1 c2 .setup) .address digitP).eval (pointE k) =
      ofK (suVal D .address D.shape.logMemory k) := by
    obtain ⟨off, hl⟩ := hr.setupLimbs.1
    have hbl := hr.setupAligned _ (limbs_mem_blocks (b := (0, D.shape.logMemory, off))
      (by rw [hl]; exact List.mem_singleton_self _))
    unfold suP
    rw [colPoly_eval_pointE hr.c1.beta _ _ _ _ _ off k hl hbl.1 hbl.2 hr.setupVars hlm hkm]
    unfold suVal c1Block
    rw [setupLayout_eq, hl]
    rfl
  simp only [memPullP, Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_one, eval_zero,
    List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd] at he
  rw [eval_digitP_pointE hr.c1.beta _ hk24, pointE_shift_zero hk', mul_zero, add_zero,
    restr_eval D hr c2 b hal hk' (by omega), hmem 0 (by norm_num), hmem 1 (by norm_num),
    hmem 2 (by norm_num), hmem 3 (by norm_num), haddr] at he
  have hsep : ofK (toK sepMem) = sepMem := by
    unfold sepMem gen
    rw [eK_eq, toK_ofK]
  rw [hsep, ofK_one]
  have h2 := two_eq_zero_E
  unfold betaOf at he
  refine CharTwo.add_eq_zero.mp ?_
  linear_combination he + (-(wt ch 2 * ofK (c1Val D c1 (.memory 3) D.shape.logMemory k))) * h2

include hr in
/-- **The bytecode's block from its leaf identity.** -/
theorem bcHolds (hb : b.leaves = .bytecode) (hrb : b.r = D.shape.logBytecode) (hal : 2 ^ b.r ∣ b.position)
    (hpos : b.position + 2 ^ b.r ≤ 2 ^ 24) (hlb : D.shape.logBytecode ≤ 24)
    (hP : blockP D.shape c1 c2 (stackFor D c1 c2 .setup) s.2 (alphasOf ch) (betaOf ch) b i = 0) :
    (blockK D c1 s.2 b).Holds (Heap.fp (fun j ↦ ch.getD j.val 0) (ch.getD 4 0)) (heapT D.shape c2)
      b.position := by
  intro k hk
  have hk' := hk_of D c1 s b k hk
  have hk24 : k < 2 ^ 24 := by omega
  have hbk : blockK D c1 s.2 b = Heap.LeafBlock.pair b.r (bcTupleK D 1)
      (fun x ↦ bcTupleK D (c1Val D c1 .bytecodeFinal D.shape.logBytecode x) x) := by
    unfold blockK; rw [hb]
  rw [hbk]
  show heapT D.shape c2 (b.position + k) * Heap.fpProd _ [_] = Heap.fpProd _ [_]
  rw [fpProd_single, fpProd_single, fp_bcTupleK hr.eqk, fp_bcTupleK hr.eqk]
  unfold blockP at hP
  rw [hb] at hP
  simp only at hP
  have he := congrArg (Polynomial.eval (pointE k)) hP
  have hkb : k < 2 ^ D.shape.logBytecode := hrb ▸ hk'
  have hbf : (c1P D.shape c1 .bytecodeFinal).eval (pointE k) =
      ofK (c1Val D c1 .bytecodeFinal D.shape.logBytecode k) := by
    obtain ⟨off, hl⟩ := hr.c1.limbs.2.2.2.1
    exact c1P_eval_pointE D hr.c1.beta hr.c1.aligned hr.c1.vars c1 _ _ off k hl hlb hkb
  simp only [bcPullP, Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_one, eval_zero] at he
  rw [eval_digitP_pointE hr.c1.beta _ hk24, pointE_shift_zero hk', mul_zero, add_zero,
    restr_eval D hr c2 b hal hk' (by omega), hbf, show stackFor D c1 c2 .setup = setupStk D from rfl,
    hr.bcTuple ch k hkb] at he
  rw [ofK_one]
  have h2 := two_eq_zero_E
  unfold betaOf at he
  refine CharTwo.add_eq_zero.mp ?_
  linear_combination he + (-(wt ch 2 * ofK (c1Val D c1 .bytecodeFinal D.shape.logBytecode k))) * h2

include hr in
/-- **An unused block from its identity.** -/
theorem unusedHolds (hb : b.leaves = .unused) (hal : 2 ^ b.r ∣ b.position)
    (hpos : b.position + 2 ^ b.r ≤ 2 ^ 24)
    (hP : blockP D.shape c1 c2 (stackFor D c1 c2 .setup) s.2 (alphasOf ch) (betaOf ch) b i = 0) :
    (blockK D c1 s.2 b).Holds (Heap.fp (fun j ↦ ch.getD j.val 0) (ch.getD 4 0)) (heapT D.shape c2)
      b.position := by
  intro k hk
  have hk' := hk_of D c1 s b k hk
  have hbk : blockK D c1 s.2 b = Heap.LeafBlock.unused b.r := by unfold blockK; rw [hb]
  rw [hbk]
  unfold blockP at hP
  rw [hb] at hP
  simp only at hP
  have he := congrArg (Polynomial.eval (pointE k)) hP
  rw [Polynomial.eval_add, eval_one, eval_zero, restr_eval D hr c2 b hal hk' (by omega)] at he
  simp [Heap.LeafBlock.unused, Heap.fpProd, CharTwo.add_eq_zero.mp he]

end Blocks

end UniSound.Ids
