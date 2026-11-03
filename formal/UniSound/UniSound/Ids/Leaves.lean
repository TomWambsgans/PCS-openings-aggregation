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

end UniSound.Ids
