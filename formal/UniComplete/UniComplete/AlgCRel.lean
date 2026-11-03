-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgCConstraint
import UniComplete.AlgCRun

/-!
# The honest prover's relations on `C1` and the setup hold (milestone 4, the algebra, item 2)

For an honest placed trace (`TraceHonest`, its heights and memory at most `28`: `Small`), four challenges `α`,
any `β`, `γ`, `t`, and `a := atTOf tr (c2DataOf tr (eqKernel α) β γ) α β γ t none` (the values sent at `t` and the
relations the verifier states, computed with its own `tablePart` and `constraintRelation`): **every relation of
`a.relations` not on `C2` holds** on the prover's stacks (`relations_hold`), at the layouts the verifier states
(`layoutIn (layouts tr.shape a.c2Columns)`) and the prover's stacks (`c1Stack tr`, `(c2DataOf …).stack`,
`setupStackOf tr`):

* each table's relations (its sent values, its fingerprints: `AlgCRun.tablePartOf_holds`, the term values
  `AlgCTerm.termEval_c1_table`);
* the memory's three (its final counts, its addresses on the setup, its limbs' fingerprint) and the bytecode's two
  (its final counts, its tuple on the setup at `(α, w(t))`: slot `2` is zero, `TraceHonest.slotsFixed`);
* **the constraint quotient's identity** `Σ_i γ^i lift_i M_i(t) = Q_W(t) w_{r_W}(t)` (`constraintRelation_eval`,
  `Q_W w_{r_W} = N` by `constraintQuotient_mul`, `Q_W(t)` read from its chunks by `chunksValue_chunksB`, which needs
  the quotient to fit: `constraintQuotient_fits`).

The heap's relations are on `C2` (`AlgCRun.heapRelations_c2`); without Flock's output there is no ring term.
The hypothesis `CoordinateFunctionalsBasis` at BLAKE2S's height is the domain agent's item 7 (not kernel-checked at
`18`).
-/

namespace UniComplete.AlgC

open UniStatement LeanVM.Parameters Polynomial Finset

/-- **The prover's three stacks**, by commitment (`proveStreamWith`'s `stackOf`). -/
def stackOfTr (tr : Trace) (c2 : C2Data) : Commitment → Array K
  | .c1 => c1Stack tr
  | .c2 => c2.stack
  | .setup => setupStackOf tr

/-! ### The point's digits -/

theorem atW_length (tr : Trace) (t : E) :
    (atW tr t).length = max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2 :=
  Domain.length_digits _ _

theorem take_atW_length (tr : Trace) (t : E) {r : ℕ} (hr : r ≤ tr.shape.constraintVars) :
    ((atW tr t).take r).length = r := by
  rw [List.length_take, atW_length]
  omega

/-- **A committed `K`-column read at `t`** (the multilinear extension of its basis-`B` coefficients at the point's
digits) is its polynomial at `t`. -/
theorem mle_atW (tr : Trace) (t : E) {r : ℕ} (hr : r ≤ tr.shape.constraintVars) (v : Array K) (hv : v.size = 2 ^ r) :
    multilinearEval ((bCoefficients r v).toList.map ofK) ((atW tr t).take r) = pEval t (colPolyK r v) := by
  have h := evalB_bCoefficients r _ v hv (by omega : r ≤ (max tr.shape.heap.h
    (tr.shape.constraintVars + 4) + 2)) t
  unfold evalB at h
  rw [Array.toList_map] at h
  exact h

theorem atColumn_eq {tr : Trace} (hH : TraceHonest tr) (t : E) {table : Table} (htab : table ∈ tables)
    {c : ℕ} (hc : c < table.width) :
    atColumn tr (atW tr t) table c = pEval t ((tablePolys tr table.opcode).getD c 0) := by
  obtain ⟨ht, hget⟩ := mem_tables htab
  have hc' : c < (tables.getD table.opcode default).width := by rw [hget]; exact hc
  unfold atColumn evalB
  rw [Array.toList_map, tablePolys_getD tr _ hc']
  exact mle_atW tr t (height_le_constraintVars tr _) _ ((hH.tablesSize.2 _ ht).2 c hc')

/-! ### The zero slot -/

theorem stageF_zero (lam : ℕ → K) (k : ℕ) : Bridge.Ntt.stageF false lam k (fun _ ↦ (0 : K)) = fun _ ↦ 0 := by
  funext p
  simp [Bridge.Ntt.stageF]

theorem coefficientsF_zero (lamOf : ℕ → ℕ → K) : ∀ m, Bridge.Ntt.coefficientsF lamOf m (fun _ ↦ (0 : K)) = fun _ ↦ 0
  | 0 => rfl
  | m + 1 => by rw [Bridge.Ntt.coefficientsF_succ, coefficientsF_zero lamOf m, stageF_zero]

/-- **A column of zeros has zero coefficients.** -/
theorem bCoefficients_zero (r : ℕ) (v : Array K) (hv : v.size = 2 ^ r) (hz : ∀ i < 2 ^ r, v.getD i 0 = 0) :
    ∀ k < 2 ^ r, (bCoefficients r v).getD k 0 = 0 := by
  have hfun : (fun i ↦ v.getD i 0) = fun _ ↦ (0 : K) := by
    funext i
    by_cases hi : i < 2 ^ r
    · exact hz i hi
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
  have hc : ∀ j < 2 ^ r, (PcsQuotient.Domain.coefficients r 0 v).getD j 0 = 0 := fun j hj ↦ by
    rw [Bridge.Ntt.coefficients_getD_K' r 0 v hv j hj, hfun, coefficientsF_zero]
  intro k hk
  unfold bCoefficients
  rw [subsetSums_eq, ss_getD _ r (by rw [Bridge.Ntt.coefficients_size, hv]) hk]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [hc j (Finset.mem_range.mp hj)]
  simp

theorem mle_zero (a : Array E) (pt : List E) (ha : a.size = 2 ^ pt.length) (hz : ∀ x < 2 ^ pt.length, a.getD x 0 = 0) :
    multilinearEval a.toList pt = 0 := by
  rw [mle_eq_sum a pt ha]
  exact Finset.sum_eq_zero fun x hx ↦ by rw [hz x (Finset.mem_range.mp hx), zero_mul]

/-- **Slot `2` of the bytecode (the count's) reads zero at `t`.** -/
theorem atSlot_two {tr : Trace} (hH : TraceHonest tr) (t : E) (hlb : tr.shape.logBytecode ≤ tr.shape.constraintVars) :
    atSlot tr (atW tr t) 2 = 0 := by
  have hsize := hH.slotsSize.2 2 (by norm_num)
  have hz : ∀ i < 2 ^ tr.shape.logBytecode, (tr.slots.getD 2 #[]).getD i 0 = 0 := fun i hi ↦
    (hH.slotsFixed i hi).2.2
  unfold atSlot evalB
  have hlen := take_atW_length tr t hlb
  refine mle_zero _ _ (by rw [Array.size_map, bCoefficients_size, hsize, hlen]) fun x hx ↦ ?_
  rw [hlen] at hx
  rw [getD_map_ofK, bCoefficients_zero _ _ hsize hz x hx, Domain.embed_zero]

/-! ### Sums -/

theorem foldl_add_range (f : ℕ → E) (b : E) : ∀ n : ℕ,
    (List.range n).foldl (fun acc s ↦ acc + f s) b = b + ∑ s ∈ range n, f s
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_add_range f b n, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    ring

/-! ### Terms on the prover's stacks -/

/-- **A term's value on its commitment's stack**, at the layouts the verifier states (no ring map: Flock's
relation is not among these). -/
def evOf (tr : Trace) (c2 : C2Data) (cols : List (Column × ℕ × Bool)) (rm : Option (List E)) (x : Term) : E :=
  termEval (layoutIn (layouts tr.shape cols) x.column.commitment) (stackOfTr tr c2 x.column.commitment) rm x

theorem evOf_c1 (tr : Trace) (c2 : C2Data) (cols : List (Column × ℕ × Bool)) (rm : Option (List E)) (x : Term)
    (hx : x.column.commitment = .c1) : evOf tr c2 cols rm x = termEval (c1Layout tr.shape) (c1Stack tr) rm x := by
  unfold evOf
  rw [hx]
  rfl

theorem evOf_setup (tr : Trace) (c2 : C2Data) (cols : List (Column × ℕ × Bool)) (rm : Option (List E)) (x : Term)
    (hx : x.column.commitment = .setup) :
    evOf tr c2 cols rm x = termEval (setupLayout tr.shape) (setupStackOf tr) rm x := by
  unfold evOf
  rw [hx]
  rfl

theorem mem_zip_map {α β : Type} (f : α → β) : ∀ (l : List α), ∀ x ∈ l.zip (l.map f), x.2 = f x.1 ∧ x.1 ∈ l
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, x, h => by
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, List.mem_cons_self ..⟩
    · obtain ⟨h1, h2⟩ := mem_zip_map f l x h
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

/-- Only BLAKE2S's columns are `q_flock`'s slots, all below `20`. -/
theorem qflockSlot_tables : ∀ t < 6, ∀ c < (tables.getD t default).width,
    ((qflockSlot ((tables.getD t default).columns.getD c "")).all fun s ↦ decide (t = opBlake2s ∧ s < 20)) =
      true := by
  decide +kernel

theorem qflockSlot_spec {table : Table} (htab : table ∈ tables) {c slot : ℕ} (hc : c < table.width)
    (h : qflockSlot (table.columns.getD c "") = some slot) : table.opcode = opBlake2s ∧ slot < 20 := by
  obtain ⟨ht, hget⟩ := mem_tables htab
  have := qflockSlot_tables _ ht c (by rw [hget]; exact hc)
  rw [hget, h, Option.all_some] at this
  exact of_decide_eq_true this

theorem map_pEval_slotVals (t : E) (q : Array K) (h slot : ℕ) :
    (Array.ofFn (n := 2 ^ h) fun u ↦ pC (ofK (q.getD (slot + 256 * u.val) 0))).map (pEval t) =
      ((List.range (2 ^ h)).map fun u ↦ ofK (q.getD (slot + 256 * u) 0)).toArray := by
  refine Bridge.Ntt.array_ext_getD_E (by simp) fun i hi ↦ ?_
  have hi' : i < 2 ^ h := by simpa using hi
  rw [getD_map_pEval, E2ECompleteness.getD_ofFn' _ hi', pE_C,
    E2ECompleteness.toArray_getD' ((List.range (2 ^ h)).map fun u ↦ ofK (q.getD (slot + 256 * u) 0)) i 0,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi']
  rfl

theorem coordinatesAt_eq_map_comp (t : E) (r : ℕ) :
    coordinatesAt t (coordinateFunctionals r) =
      (List.range r).map (pEval t ∘ coordinateP (coordinateFunctionals r)) := coordinatesAt_eq_map t r

/-- **Every table, its part and its terms read at `t` on the prover's stacks** (`TableAt`). -/
theorem tableAt_of {tr : Trace} (hH : TraceHonest tr) (c2 : C2Data) (cols : List (Column × ℕ × Bool))
    (rm : Option (List E)) (weights : Array E) (beta t : E) {table : Table} (htab : table ∈ tables) :
    TableAt tr t (atW tr t) (evOf tr c2 cols rm) (table, (atPart tr weights beta (atW tr t) table).1) := by
  obtain ⟨ht, hget⟩ := mem_tables htab
  have hr := height_le_constraintVars tr table.opcode
  have hlen := take_atW_length tr t hr
  refine ⟨htab, fun i hi ↦ ?_, fun c k hc ↦ ?_, fun k ↦ ?_, fun c slot k hc hslot ↦ ?_, ?_⟩
  · show (tablePartOf table (tr.shape.heights.getD table.opcode 0) weights beta (atW tr t)
      (atColumn tr (atW tr t) table)).1.sent.getD i none = _
    rw [tablePartOf_sent htab (tr.shape.heights.getD table.opcode 0) weights beta (atW tr t)
      (atColumn tr (atW tr t) table) i hi, atColumn_eq hH t htab (sentColumns_lt htab hi)]
  · have hc' : c < (tables.getD table.opcode default).width := by rw [hget]; exact hc
    have h1 := termEval_c1_table tr rm ht hc' ((hH.tablesSize.2 _ ht).2 c hc') hlen k
    have h2 := mle_atW tr t hr _ ((hH.tablesSize.2 _ ht).2 c hc')
    rw [evOf_c1 _ _ _ _ _ rfl, tablePolys_getD tr _ hc']
    exact h1.trans (congrArg (k * ·) h2)
  · have h1 := termEval_c1_inverse tr rm ht hlen k
    have h2 := mle_atW tr t hr _ (inverseColumn_size tr table.opcode)
    rw [evOf_c1 _ _ _ _ _ rfl]
    exact h1.trans (congrArg (k * ·) h2)
  · obtain ⟨hB, hs⟩ := qflockSlot_spec htab hc hslot
    have hF : (coordinatesAt t (coordinateFunctionals (tr.shape.heights.getD table.opcode 0))).length =
        tr.height 5 := by
      rw [coordinatesAt_eq_map, List.length_map, List.length_range, hB]
      rfl
    have h1 := termEval_c1_qflockSlot tr rm (by omega : slot < 256) hF k
    rw [evOf_c1 _ _ _ _ _ rfl, h1, pEval_mleP, List.map_map, map_pEval_slotVals, ← coordinatesAt_eq_map_comp, hB]
    rfl
  · exact (pEval_liftP t _ (by omega)).symm


/-- The bytecode's block is in the heap: `lb < h`. -/
theorem logBytecode_lt_heap (s : Shape) : s.logBytecode < s.heap.h := by
  unfold Shape.heap HeapLayout.new
  simp only []
  generalize hS : List.mergeSort ([(Leaves.memory, s.logMemory), (Leaves.bytecode, s.logBytecode)] ++
    (List.range s.heights.length).map fun t ↦ (Leaves.table t, s.heights.getD t 0))
    (fun a b ↦ b.2 < a.2 || (a.2 == b.2 && a.1.order ≤ b.1.order)) = S
  have hperm : S.Perm ([(Leaves.memory, s.logMemory), (Leaves.bytecode, s.logBytecode)] ++
      (List.range s.heights.length).map fun t ↦ (Leaves.table t, s.heights.getD t 0)) := by
    rw [← hS]
    exact List.mergeSort_perm _ _
  have hsum : 2 ^ s.logBytecode ≤ (S.map fun x ↦ 2 ^ x.2).sum := by
    rw [(hperm.map _).sum_eq]
    exact List.le_sum_of_mem (by simp)
  show s.logBytecode < log2Ceil (S.map fun x ↦ 2 ^ x.2).sum + 1
  generalize (S.map fun x ↦ 2 ^ x.2).sum = T at hsum
  unfold log2Ceil
  split_ifs with hT
  · have : 2 ^ s.logBytecode ≤ 1 := le_trans hsum hT
    have h0 : s.logBytecode = 0 := by
      by_contra hne
      have : 2 ≤ 2 ^ s.logBytecode := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ s.logBytecode := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  · have h1 := Nat.lt_log2_self (n := T - 1)
    have h2 : 2 ^ s.logBytecode ≤ 2 ^ ((T - 1).log2 + 1) := by omega
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega



/-! ### The memory's and the bytecode's relations -/

theorem evOf_memory {tr : Trace} (hH : TraceHonest tr) (c2 : C2Data) (cols : List (Column × ℕ × Bool))
    (rm : Option (List E)) (t : E)
    {k : ℕ} (hk : k < 4) (c : E) :
    evOf tr c2 cols rm (term (.memory k) ((atW tr t).take tr.shape.logMemory) c) = c * atMem tr (atW tr t) k := by
  rw [evOf_c1 _ _ _ _ _ rfl, termEval_c1_memory tr rm hk (hH.memorySize.2 k hk)
    (take_atW_length tr t (logMemory_le_constraintVars tr))]
  unfold atMem evalB
  rw [Array.toList_map]

/-- **The memory's three relations hold**: its final counts and its addresses at `w(t)` (the latter on the
setup), its limbs' fingerprint. -/
theorem memoryRels_hold {tr : Trace} (hH : TraceHonest tr) (c2 : C2Data) (cols : List (Column × ℕ × Bool))
    (rm : Option (List E)) (weights : Array E) (beta t : E) :
    ∀ rel ∈ atMemoryRels tr weights beta (atW tr t), (rel.terms.map (evOf tr c2 cols rm)).sum = rel.value := by
  have hlen := take_atW_length tr t (logMemory_le_constraintVars tr)
  intro rel hrel
  simp only [atMemoryRels, List.mem_cons, List.not_mem_nil, or_false] at hrel
  rcases hrel with rfl | rfl | rfl
  · simp only [Relation.equal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [evOf_memory hH c2 cols rm t (by norm_num), one_mul]
  · simp only [Relation.equal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [evOf_setup _ _ _ _ _ rfl, termEval_setup_address tr rm hlen, one_mul]
    unfold atAddress evalB
    rw [Array.toList_map]
  · simp only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [evOf_memory hH c2 cols rm t (by norm_num), evOf_memory hH c2 cols rm t (by norm_num),
      evOf_memory hH c2 cols rm t (by norm_num)]
    unfold atMemoryPull memoryFp
    simp only [show List.range 3 = [0, 1, 2] from rfl, List.foldl_cons, List.foldl_nil, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    linear_combination (-(beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * atAddress tr (atW tr t) +
      weights.getD 2 0 * atMem tr (atW tr t) 3)) * Domain.two_eq_zero_E

/-- **The bytecode's two relations hold**: its final counts at `w(t)`, its tuple on the setup at `(α, w(t))` (slot
`2` zero, so the sent pull's slot `2` is the final count's). -/
theorem bytecodeRels_hold {tr : Trace} (hH : TraceHonest tr) (c2 : C2Data) (cols : List (Column × ℕ × Bool))
    (rm : Option (List E)) {alphas : List E} (hα : alphas.length = 4) (beta t : E) :
    ∀ rel ∈ atBytecodeRels tr alphas beta (atW tr t), (rel.terms.map (evOf tr c2 cols rm)).sum = rel.value := by
  have hlb := logBytecode_lt_heap tr.shape
  have hlen : ((atW tr t).take tr.shape.logBytecode).length = tr.shape.logBytecode := by
    rw [List.length_take, atW_length]
    omega
  intro rel hrel
  simp only [atBytecodeRels, List.mem_cons, List.not_mem_nil, or_false] at hrel
  rcases hrel with rfl | rfl
  · simp only [Relation.equal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [evOf_c1 _ _ _ _ _ rfl, termEval_c1_bytecodeFinal tr rm hH.bytecodeSize hlen, one_mul]
    unfold atBytecodeFinal evalB
    rw [Array.toList_map]
  · simp only [Relation.equal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [evOf_setup _ _ _ _ _ rfl, termEval_setup_bytecodeTuple tr rm hα hlen hH.slotsSize.2, one_mul]
    have hslot : ∀ s, multilinearEval ((bCoefficients tr.shape.logBytecode (tr.slots.getD s #[])).toList.map ofK)
        ((atW tr t).take tr.shape.logBytecode) = atSlot tr (atW tr t) s := fun s ↦ by
      unfold atSlot evalB
      rw [Array.toList_map]
    simp only [hslot]
    have h2 : atSlot tr (atW tr t) 2 = 0 := by
      unfold atSlot evalB
      have hsize := hH.slotsSize.2 2 (by norm_num)
      refine mle_zero _ _ (by rw [Array.size_map, bCoefficients_size, hsize, hlen]) fun x hx ↦ ?_
      rw [hlen] at hx
      rw [getD_map_ofK, bCoefficients_zero _ _ hsize (fun i hi ↦ (hH.slotsFixed i hi).2.2) x hx, Domain.embed_zero]
    unfold atBytecodePull bytecodeFp
    rw [foldl_add_range]
    have hsplit : ∑ s ∈ range 16, (eqKernel alphas).getD s 0 *
        (if s = 2 then atBytecodeFinal tr (atW tr t) else atSlot tr (atW tr t) s) =
        ∑ s ∈ range 16, (eqKernel alphas).getD s 0 * atSlot tr (atW tr t) s +
          (eqKernel alphas).getD 2 0 * atBytecodeFinal tr (atW tr t) := by
      have hterm : ∀ s ∈ range 16, (eqKernel alphas).getD s 0 *
          (if s = 2 then atBytecodeFinal tr (atW tr t) else atSlot tr (atW tr t) s) =
          (eqKernel alphas).getD s 0 * atSlot tr (atW tr t) s +
            (if s = 2 then (eqKernel alphas).getD s 0 * atBytecodeFinal tr (atW tr t) else 0) := by
        intro s _
        by_cases hs : s = 2
        · rw [Domain.ite_pos_of hs, Domain.ite_pos_of hs, hs, h2, mul_zero, zero_add]
        · rw [Domain.ite_neg_of hs, Domain.ite_neg_of hs, add_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        Finset.sum_ite_eq' (range 16) 2 (fun s ↦ (eqKernel alphas).getD s 0 * atBytecodeFinal tr (atW tr t)),
        Domain.ite_pos_of (Finset.mem_range.mpr (by norm_num))]
    rw [hsplit]
    linear_combination (-(beta + (eqKernel alphas).getD 2 0 * atBytecodeFinal tr (atW tr t))) *
      Domain.two_eq_zero_E

/-! ### The constraint quotient's identity -/

theorem countColumns_le : tables.all (fun t ↦ decide (t.countColumns.length ≤ 10)) = true := by
  decide +kernel

theorem degStep_lt {tr : Trace} (hS : Small tr) {table : Table} (htab : table ∈ tables) {d : ℕ}
    (hd : d < 2 ^ (tr.shape.constraintVars + 4)) : degStep tr.shape d table < 2 ^ (tr.shape.constraintVars + 4) := by
  obtain ⟨ht, -⟩ := mem_tables htab
  have hr : tr.shape.heights.getD table.opcode 0 ≤ tr.shape.constraintVars := height_le_constraintVars tr _
  have h28 : tr.shape.heights.getD table.opcode 0 ≤ 28 := hS.heights _ ht
  have hc : table.countColumns.length ≤ 10 := by
    have := List.all_eq_true.mp countColumns_le table htab
    simpa using this
  have hn : 2 ^ tr.shape.heights.getD table.opcode 0 ≤ 2 ^ tr.shape.constraintVars :=
    Nat.pow_le_pow_right (by norm_num) hr
  have hB : 2 ^ (tr.shape.constraintVars + 4) = 16 * 2 ^ tr.shape.constraintVars := by rw [pow_add]; ring
  have h1 : (2 ^ tr.shape.heights.getD table.opcode 0 - 1) * (1 + table.countColumns.length) ≤
      (2 ^ tr.shape.heights.getD table.opcode 0) * 11 := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  have h2 : tr.shape.heights.getD table.opcode 0 * (2 ^ tr.shape.heights.getD table.opcode 0 / 2) ≤
      28 * (2 ^ tr.shape.heights.getD table.opcode 0 / 2) := Nat.mul_le_mul h28 le_rfl
  have h3 : 2 * (2 ^ tr.shape.heights.getD table.opcode 0 / 2) ≤ 2 ^ tr.shape.heights.getD table.opcode 0 :=
    Nat.mul_div_le _ _
  have h4 := Nat.one_le_two_pow (n := tr.shape.heights.getD table.opcode 0)
  have h5 := Nat.one_le_two_pow (n := tr.shape.constraintVars)
  unfold degStep UniStatement.degree
  dsimp only
  split_ifs <;> omega

theorem foldl_degStep_lt {tr : Trace} (hS : Small tr) : ∀ (l : List Table), (∀ x ∈ l, x ∈ tables) →
    ∀ d, d < 2 ^ (tr.shape.constraintVars + 4) → l.foldl (degStep tr.shape) d < 2 ^ (tr.shape.constraintVars + 4)
  | [], _, _, hd => hd
  | x :: l, hl, d, hd => foldl_degStep_lt hS l (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)) _
      (degStep_lt hS (hl x (by simp)) hd)

/-- **The constraint quotient's degree is below `2^{r_W + 4}`** (its chunks are read at digits below `r_W + 5`). -/
theorem constraintDegree_lt {tr : Trace} (hS : Small tr) :
    tr.shape.constraintDegree < 2 ^ (tr.shape.constraintVars + 4) := by
  rw [constraintDegree_eq]
  refine max_lt (foldl_degStep_lt hS tables (fun _ h ↦ h) 0 (Nat.two_pow_pos _)) ?_
  have hlm : 2 ^ tr.shape.logMemory ≤ 2 ^ tr.shape.constraintVars :=
    Nat.pow_le_pow_right (by norm_num) (logMemory_le_constraintVars tr)
  have hB : 2 ^ (tr.shape.constraintVars + 4) = 16 * 2 ^ tr.shape.constraintVars := by rw [pow_add]; ring
  have h5 := Nat.one_le_two_pow (n := tr.shape.constraintVars)
  unfold UniStatement.degree
  omega

/-- **`Q_W(t)` read from its chunks is the quotient at `t`.** -/
theorem atConstraintValue_eq {tr : Trace} (hS : Small tr) (weights : Array E) (beta gamma t : E) :
    atConstraintValue (c2DataOf tr weights beta gamma) (atW tr t) =
      pEval t (constraintQuotient tr gamma (publicWordsOf tr.publicInput)) := by
  have hD := constraintDegree_lt hS
  obtain ⟨hshape, -, hle⟩ := chunks_spec (n := tr.shape.constraintDegree + 1) (by omega)
  have hlog : (tr.shape.constraintDegree + 1).log2 < tr.shape.constraintVars + 5 := by
    rw [Nat.log2_lt (by omega)]
    rw [pow_succ]
    omega
  refine chunksValue_chunksB _ _ hshape (constraintQuotient_fits tr gamma _) t _ fun e he ↦ ?_
  have := hle e he
  omega

/-- **The constraint quotient's identity holds**: `Σ_i γ^i lift_i M_i(t) = Q_W(t) w_{r_W}(t)` on `C1`. -/
theorem constraintRel_hold {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) (cols : List (Column × ℕ × Bool))
    (rm : Option (List E)) (alphas : List E) (beta gamma t : E) (c2 : C2Data) (hc2 : c2 = c2DataOf tr (eqKernel alphas) beta gamma) :
    ((atConstraint tr c2 alphas beta gamma t).1.terms.map (evOf tr c2 cols rm)).sum =
      (atConstraint tr c2 alphas beta gamma t).1.value := by
  have hrW : tr.shape.constraintVars < max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2 := by omega
  have hmem : ∀ k c, k < 3 → evOf tr c2 cols rm (term (.memory k) ((atW tr t).take tr.shape.logMemory) c) =
      c * pEval t (colPolyK tr.shape.logMemory (tr.memory.getD k #[])) := fun k c hk ↦ by
    rw [evOf_memory hH c2 cols rm t (by omega)]
    unfold atMem evalB
    rw [Array.toList_map, mle_atW tr t (logMemory_le_constraintVars tr) _ (hH.memorySize.2 k (by omega))]
  have hparts : ∀ x ∈ tables.zip (atParts tr (eqKernel alphas) beta (atW tr t)),
      TableAt tr t (atW tr t) (evOf tr c2 cols rm) x := fun x hx ↦ by
    obtain ⟨h2, h1⟩ := mem_zip_map _ tables x hx
    have := tableAt_of hH c2 cols rm (eqKernel alphas) beta t h1
    rw [← h2] at this
    exact this
  have h := constraintRelation_eval tr gamma t (atConstraintValue c2 (atW tr t)) (atW tr t) (evOf tr c2 cols rm)
    (atParts tr (eqKernel alphas) beta (atW tr t)) (publicWordsOf tr.publicInput)
    (by unfold atParts; rw [List.length_map]) hparts hmem (pEval_liftP t 1 hrW.le).symm
  have hQ : atConstraintValue c2 (atW tr t) * (atW tr t).getD tr.shape.constraintVars 0 =
      pEval t (constraintNumerator tr gamma (publicWordsOf tr.publicInput)) := by
    rw [hc2, atConstraintValue_eq hS,
      show (atW tr t).getD tr.shape.constraintVars 0 = (Domain.wP tr.shape.constraintVars).eval t from
        digit_eq t hrW, pEval_eq, pEval_eq, ← Polynomial.eval_mul,
      constraintQuotient_mul hH hS hC gamma]
  rw [hQ] at h
  rw [show atConstraint tr c2 alphas beta gamma t = constraintRelation tr.shape
    (atParts tr (eqKernel alphas) beta (atW tr t)) (publicWordsOf tr.publicInput) gamma t
    (atConstraintValue c2 (atW tr t)) (atW tr t) from rfl]
  generalize constraintRelation tr.shape (atParts tr (eqKernel alphas) beta (atW tr t))
    (publicWordsOf tr.publicInput) gamma t (atConstraintValue c2 (atW tr t)) (atW tr t) = R at h ⊢
  generalize pEval t (constraintNumerator tr gamma (publicWordsOf tr.publicInput)) = N at h
  generalize (R.1.terms.map (evOf tr c2 cols rm)).sum = S at h ⊢
  linear_combination h.1 - (R.1.value - N) * Domain.two_eq_zero_E

/-! ### The headline -/

/-- **Every relation the verifier states at `t` off `C2` holds on the honest prover's stacks, whatever the ring
map and `C2`'s column list** (none of these relations has a ring-switch term, and `C1`'s and the setup's layouts do
not depend on `C2`'s columns). -/
theorem relations_hold_rm {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) {alphas : List E} (hα : alphas.length = 4)
    (beta gamma t : E) (cols : List (Column × ℕ × Bool)) (rm : Option (List E)) :
    ∀ rel ∈ (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).relations,
      rel.commitment ≠ .c2 →
      UniComplete.Relation.Holds (layoutIn (layouts tr.shape cols))
        (stackOfTr tr (c2DataOf tr (eqKernel alphas) beta gamma)) rm rel := by
  intro rel hrel hc2
  show (rel.terms.map (evOf tr (c2DataOf tr (eqKernel alphas) beta gamma) cols rm)).sum = rel.value
  rw [atTOf_relations] at hrel
  simp only [List.mem_append, List.mem_singleton] at hrel
  rcases hrel with (((h | h) | h) | h) | h
  · obtain ⟨table, htab, h'⟩ := List.mem_flatMap.mp h
    refine tablePartOf_holds htab _ _ _ _ _ _ (fun c k hc ↦ ?_) rel h'
    rw [(tableAt_of hH (c2DataOf tr (eqKernel alphas) beta gamma) _ rm (eqKernel alphas) beta t htab).col c k hc,
      atColumn_eq hH t htab hc]
  · exact memoryRels_hold hH _ _ rm _ beta t rel h
  · exact bytecodeRels_hold hH _ _ rm hα beta t rel h
  · subst h
    exact constraintRel_hold hH hS hC _ rm alphas beta gamma t _ rfl
  · exact absurd (heapRelations_c2 _ _ _ _ _ _ _ _ _ _ _ _ _ (chunks_succ_ne_nil _) rel h) hc2

/-- **Every relation the verifier states at `t` off `C2` holds on the honest prover's stacks** (item 2): for an
honest placed trace (heights and memory at most `28`, the coordinate functionals' basis property at BLAKE2S's
height), four `α`, any `β`, `γ`, `t`, and the prover's `C2` (`c2DataOf`), every relation of `atTOf … none` whose
commitment is `C1` or the setup holds at the layouts the verifier states and the prover's three stacks. -/
theorem relations_hold {tr : Trace} (hH : TraceHonest tr) (hS : Small tr)
    (hC : Domain.CoordinateFunctionalsBasis (tr.height opBlake2s)) {alphas : List E} (hα : alphas.length = 4)
    (beta gamma t : E) :
    ∀ rel ∈ (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).relations,
      rel.commitment ≠ .c2 →
      UniComplete.Relation.Holds (layoutIn (layouts tr.shape
          (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).c2Columns))
        (stackOfTr tr (c2DataOf tr (eqKernel alphas) beta gamma))
        (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none).ringMap rel :=
  relations_hold_rm hH hS hC hα beta gamma t _ _

end UniComplete.AlgC

/-- info: 'UniComplete.AlgC.relations_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.relations_hold

/-- info: 'UniComplete.AlgC.constraintRel_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.constraintRel_hold

/-- info: 'UniComplete.AlgC.memoryRels_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.memoryRels_hold

/-- info: 'UniComplete.AlgC.bytecodeRels_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.bytecodeRels_hold
