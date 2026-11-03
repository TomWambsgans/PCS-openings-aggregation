-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The layouts' limbs, `c1Vars`, the heap's relations and
-- the constraint relation as folds, `chunk_lt` and the hazard's argument are `formal/UniSound`'s (`Ids/Eval.lean`:
-- `limbs_new_mem`, `heapRelations_fst`, `qTerms_mem`, `crOf`, `crStep_Q`, `y_self`; `Ids/Deployed.lean`: `c1Cols_eq`,
-- `heap_reference`).
import RecGraph.Sim.TablePart
import RecGraph.Sim.Batch

/-!
# The simulation: reduce's relations satisfy the tail's conditions off the hazard

`shapeSpec : ShapeSpec tableShape constraintShape heapShape TailOK`. For each commitment:

* its layout is `LayoutOK` (`layoutOK_newC`): a column's limbs are its entries in the layout's column list
  (`limbs_new_memC`), and each list gives a column one variable count (`c1Vars`, `c2VarsC`, `setupVarsC`);
* every term of its relations has its `TermKind` (`TermFact`): a plain term's column has at most its point's variables
  (the heap's leaf quotients' chunks, from the parts' degrees, at most `25 < 27 = |w|`), a slot is at `y(t)`, the ring
  term at Flock's point;
* no `C1` point extends `y(t)` (`PointFact`): `C1`'s points are prefixes of `w` (first coordinate `t`), `y(t)` or
  Flock's point (first coordinate `p_0`), and off the hazard `y_0 ≠ t, p_0`.
-/

set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph.Pi1

/-! ## Layouts -/

/-- **A column's limbs are its entries** in the layout's column list, each limb one of three. -/
theorem limbs_new_memC (cols : List (Column × ℕ × Bool)) (col : Column) (b : ℕ × ℕ × ℕ)
    (hb : b ∈ (StackLayout.new cols).limbs col) : b.1 < 3 ∧ ∃ e, (col, b.2.1, e) ∈ cols := by
  unfold StackLayout.new at hb
  dsimp only at hb
  rw [(UniSound.Ids.foldl_place _ (fun _ _ _ _ ↦ rfl) _ #[] 0).1] at hb
  rw [UniSound.Ids.limbs_eq] at hb
  simp only [List.nil_append] at hb
  have hm := UniSound.Ids.limbs_place col ((cols.flatMap fun x ↦ (List.range (if x.2.2 then 3 else 1)).map fun limb ↦
    (x.1, limb, x.2.1)).mergeSort fun a b ↦ decide (b.2.2 ≤ a.2.2)) 0
  have h1 : (col, b.1, b.2.1) ∈ ((cols.flatMap fun x ↦ (List.range (if x.2.2 then 3 else 1)).map fun limb ↦
      (x.1, limb, x.2.1)).mergeSort fun a b ↦ decide (b.2.2 ≤ a.2.2)).filter (fun x ↦ x.1 == col) := by
    rw [← hm]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  obtain ⟨h2, -⟩ := List.mem_filter.mp h1
  rw [List.mem_mergeSort] at h2
  obtain ⟨⟨c', v, e⟩, hc, hx⟩ := List.mem_flatMap.mp h2
  obtain ⟨limb, hl, he⟩ := List.mem_map.mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  refine ⟨?_, e, hc⟩
  rw [List.mem_range] at hl
  split at hl <;> omega

/-- **A layout of columns each listed at one variable count is `LayoutOK`.** -/
theorem layoutOK_newC {cols : List (Column × ℕ × Bool)} (V : Column → ℕ)
    (hV : ∀ col v e, (col, v, e) ∈ cols → v = V col) : LayoutOK (StackLayout.new cols) := by
  intro col b hb
  obtain ⟨h1, e, he⟩ := limbs_new_memC cols col b hb
  refine ⟨h1, ?_⟩
  unfold headVars
  cases hl : (StackLayout.new cols).limbs col with
  | nil => rw [hl] at hb; simp at hb
  | cons b0 rest =>
    obtain ⟨-, e0, he0⟩ := limbs_new_memC cols col b0 (by rw [hl]; exact List.mem_cons_self ..)
    rw [List.headD_cons, hV _ _ _ he, hV _ _ _ he0]

/-- A heap block's leaf quotient's degree, its table's part's degrees from `parts`. -/
def leafDegC (parts : List TablePart) (block : Block) : ℕ :=
  match block.leaves with
  | .unused => 0
  | .memory => degree (2 * (2 ^ block.r - 1)) (2 ^ block.r)
  | .bytecode => degree (2 * (2 ^ block.r - 1)) (2 ^ block.r)
  | .table t => degree (max (parts.getD t default).pullDegree (parts.getD t default).pushDegree *
      (2 ^ block.r - 1) + (2 ^ block.r - Shape.leastRows block.r)) (2 ^ block.r)

/-- **`C2`'s columns' variables** at π1-rec3's shape, the leaf quotients' from `parts`. -/
def c2VarsC (parts : List TablePart) : Column → ℕ
  | .heap => reference.heap.h
  | .treeQuotient 0 => reference.heap.h
  | .treeQuotient _ => 0
  | .constraintQuotient c => (chunks (reference.constraintDegree + 1)).getD c 0
  | .leafQuotient i c => (chunks (leafDegC parts (reference.heap.blocks.getD i default) + 1)).getD c 0
  | _ => 0

/-- **The setup's columns' variables.** -/
def setupVarsC : Column → ℕ
  | .bytecodeTuple => reference.logBytecode + 4
  | .address => reference.logMemory
  | _ => 0

/-- A column's variables in any of π1-rec3's layouts. -/
def colVarsC (parts : List TablePart) (col : Column) : ℕ :=
  max (UniSound.Ids.c1Vars reference col) (max (c2VarsC parts col) (setupVarsC col))

/-- **`C2`'s entries** (`c2Uni` of the heap's leaf columns): on `C2`, at `c2VarsC`. -/
theorem c2Uni_entryC (activeE : List E) (partsE : List TablePart) (weightsE : Array E)
    (betaE hvE cvE mplE mpsE bplE bpsE : E) (wE : List E) (col : Column) (v : ℕ) (e : Bool)
    (h : (col, v, e) ∈ c2Uni (UniStatement.heapRelations reference activeE partsE weightsE betaE hvE cvE mplE mpsE
      bplE bpsE wE (chunks (reference.constraintDegree + 1))).2) :
    col.commitment = .c2 ∧ v = c2VarsC partsE col := by
  rw [heapRelations_sndC] at h
  unfold c2Uni at h
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_flatMap,
    Prod.mk.injEq] at h
  rcases h with ((⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩) | ⟨x, hx, rfl, rfl, -⟩) | ⟨⟨blk, idx⟩, hx, hm⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, (UniSound.Ids.Eval.mem_zip_range_iff _ 0 x hx).2.symm⟩
  · have hget := (UniSound.Ids.Eval.mem_zip_range_iff _ default _ hx).2
    dsimp only at hget hm
    unfold leafColsC chunkColsC at hm
    cases hl : blk.leaves
    case unused => simp [hl] at hm
    all_goals
      simp only [hl] at hm
      rw [Array.toList_map, List.toList_toArray] at hm
      obtain ⟨⟨ee, ch⟩, hy, hq⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, -⟩ := hq
      refine ⟨rfl, ?_⟩
      show _ = (chunks (leafDegC partsE (reference.heap.blocks.getD idx default) + 1)).getD ch 0
      rw [hget, leafDegC, hl]
      exact (UniSound.Ids.Eval.mem_zip_range_iff _ 0 _ hy).2.symm

/-- **A limb's variables**: at most its column's, and `q_flock`'s `26`. -/
theorem limb_varsC {c2 : List (Column × ℕ × Bool)} {parts : List TablePart}
    (hc2 : ∀ col v e, (col, v, e) ∈ c2 → col.commitment = .c2 ∧ v = c2VarsC parts col) (c : Commitment)
    (col : Column) (b : ℕ × ℕ × ℕ) (hb : b ∈ (layoutAt (layouts reference c2) c).limbs col) :
    b.2.1 ≤ colVarsC parts col ∧ (col = .qflock → b.2.1 = 26) := by
  cases c
  · change b ∈ (StackLayout.new (UniSound.Ids.c1Cols reference)).limbs col at hb
    obtain ⟨-, e, he⟩ := limbs_new_memC _ col b hb
    rw [UniSound.Ids.c1Cols_eq] at he
    obtain ⟨c, _, hc⟩ := List.mem_map.mp he
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, h2, -⟩ := hc
    refine ⟨by rw [← h2]; exact le_max_left _ _, fun h ↦ ?_⟩
    subst h
    rw [← h2]
    show reference.heights.getD opBlake2s 0 + 8 = 26
    rw [reference_blake2s_height]
  · change b ∈ (StackLayout.new c2).limbs col at hb
    obtain ⟨-, e, he⟩ := limbs_new_memC _ col b hb
    obtain ⟨hcm, hv⟩ := hc2 _ _ _ he
    refine ⟨by rw [hv]; exact (le_max_left _ _).trans (le_max_right _ _), fun h ↦ ?_⟩
    subst h
    cases hcm
  · change b ∈ (StackLayout.new (UniSound.Ids.setupCols reference)).limbs col at hb
    obtain ⟨-, e, he⟩ := limbs_new_memC _ col b hb
    simp only [UniSound.Ids.setupCols, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at he
    rcases he with ⟨rfl, h, -⟩ | ⟨rfl, h, -⟩
    · exact ⟨by rw [h]; exact (le_max_right _ _).trans (le_max_right _ _), fun h' ↦ by cases h'⟩
    · exact ⟨by rw [h]; exact (le_max_right _ _).trans (le_max_right _ _), fun h' ↦ by cases h'⟩

/-- **Every layout is `LayoutOK`.** -/
theorem layoutsOKC {c2 : List (Column × ℕ × Bool)} {parts : List TablePart}
    (hc2 : ∀ col v e, (col, v, e) ∈ c2 → col.commitment = .c2 ∧ v = c2VarsC parts col) (c : Commitment) :
    LayoutOK (layoutAt (layouts reference c2) c) := by
  cases c
  · show LayoutOK (StackLayout.new (UniSound.Ids.c1Cols reference))
    refine layoutOK_newC (UniSound.Ids.c1Vars reference) fun col v e h ↦ ?_
    rw [UniSound.Ids.c1Cols_eq] at h
    obtain ⟨c, _, hc⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    rfl
  · exact layoutOK_newC (c2VarsC parts) fun col v e h ↦ (hc2 col v e h).2
  · show LayoutOK (StackLayout.new (UniSound.Ids.setupCols reference))
    refine layoutOK_newC setupVarsC fun col v e h ↦ ?_
    simp only [UniSound.Ids.setupCols, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl

/-! ## The terms' facts -/

/-- **A term's kind at π1-rec3's layouts**: plain, its column's variables at most its point's; a slot at `y`; or the
ring-switch term on `q_flock` at Flock's point. -/
def TermFact (parts : List TablePart) (y fp : List E) (tm : Term) : Prop :=
  (tm.twist = 0 ∧ (∀ j, tm.column ≠ .qflockSlot j) ∧ colVarsC parts tm.column ≤ tm.point.length) ∨
  (tm.twist = 0 ∧ (∃ j, tm.column = .qflockSlot j) ∧ tm.point = y) ∨
  (tm.twist = ringTwist ∧ tm.column = .qflock ∧ tm.point = fp)

/-- **A `C1` term's point**: a prefix of the digits, `y` or Flock's point. -/
def PointFact (wE y fp : List E) (tm : Term) : Prop :=
  tm.column.commitment = .c1 → (∃ k, tm.point = wE.take k) ∨ tm.point = y ∨ tm.point = fp

/-- **A relation's facts**: its terms on one commitment, each with its kind and its point. -/
def RelFact (parts : List TablePart) (wE y fp : List E) (r : Relation) : Prop :=
  (∃ c, ∀ tm ∈ r.terms, tm.column.commitment = c) ∧ ∀ tm ∈ r.terms, TermFact parts y fp tm ∧ PointFact wE y fp tm

theorem termKind_ofC {c2 : List (Column × ℕ × Bool)} {parts : List TablePart}
    (hc2 : ∀ col v e, (col, v, e) ∈ c2 → col.commitment = .c2 ∧ v = c2VarsC parts col) (c : Commitment)
    {y fp : List E} (hy : y.length = 18) (hfp : fp.length = 26) {tm : Term} (h : TermFact parts y fp tm) :
    TermKind (layoutAt (layouts reference c2) c) tm.column tm.point tm.twist := by
  rcases h with ⟨htw, hns, hle⟩ | ⟨htw, hs, hpt⟩ | ⟨htw, hq, hpt⟩
  · exact Or.inl ⟨htw, hns, fun b hb ↦ (limb_varsC hc2 c _ b hb).1.trans hle⟩
  · refine Or.inr (Or.inl ⟨htw, hs, fun b hb ↦ ?_⟩)
    have := (limb_varsC hc2 c _ b hb).2 rfl
    rw [hpt, hy]
    omega
  · refine Or.inr (Or.inr ⟨htw, fun j h ↦ (by rw [hq] at h; cases h), fun b hb ↦ ?_⟩)
    rw [hq] at hb
    have := (limb_varsC hc2 c _ b hb).2 rfl
    rw [hpt, hfp]
    omega

theorem relCommitC {r : Relation} {c : Commitment} (h : ∀ tm ∈ r.terms, tm.column.commitment = c) {tm : Term}
    (htm : tm ∈ r.terms) : r.commitment = c := by
  unfold Relation.commitment
  cases hr : r.terms with
  | nil => rw [hr] at htm; simp at htm
  | cons t0 _ => exact h t0 (by rw [hr]; exact List.mem_cons_self ..)

/-- **The tail's conditions from the relations' facts**, and no prefix of the digits or Flock's point extending `y`. -/
theorem tailOK_ofC {rels : List Relation} {c2 : List (Column × ℕ × Bool)} {parts : List TablePart} {wE y fp : List E}
    (hc2 : ∀ col v e, (col, v, e) ∈ c2 → col.commitment = .c2 ∧ v = c2VarsC parts col) (hy : y.length = 18)
    (hfp : fp.length = 26) (hR : ∀ r ∈ rels, RelFact parts wE y fp r)
    (hw : ∀ k, y.length < (wE.take k).length → (wE.take k).take y.length ≠ y)
    (hf : fp.take y.length ≠ y) : TailOK rels c2 := by
  intro c _
  refine ⟨layoutsOKC hc2 c, fun r hr tm htm ↦ ?_, fun r hr tm htm hs r' hr' tm' htm' hlt heq ↦ ?_⟩
  · exact termKind_ofC hc2 c hy hfp ((hR r (List.mem_filter.mp hr).1).2 tm htm).1
  · obtain ⟨hr1, hrc⟩ := List.mem_filter.mp hr
    obtain ⟨hr1', hrc'⟩ := List.mem_filter.mp hr'
    rw [beq_iff_eq] at hrc hrc'
    obtain ⟨⟨c0, hc0⟩, hfacts⟩ := hR r hr1
    obtain ⟨⟨c0', hc0'⟩, hfacts'⟩ := hR r' hr1'
    obtain ⟨j, hj⟩ := hs
    have hpt : tm.point = y := by
      rcases (hfacts tm htm).1 with ⟨-, hns, -⟩ | ⟨-, -, hpt⟩ | ⟨-, hq, -⟩
      · exact absurd hj (hns j)
      · exact hpt
      · rw [hq] at hj; cases hj
    have hc1 : c0 = .c1 := by rw [← hc0 tm htm, hj]; rfl
    have hc' : c0' = .c1 := by rw [← relCommitC hc0' htm', hrc', ← hrc, relCommitC hc0 htm, hc1]
    rw [hpt] at hlt heq
    rcases (hfacts' tm' htm').2 (by rw [hc0' tm' htm', hc']) with ⟨k, hk⟩ | hk | hk
    · rw [hk] at hlt heq
      exact hw k hlt heq
    · rw [hk] at hlt
      exact lt_irrefl _ hlt
    · rw [hk] at heq
      exact hf heq

/-! ## π1-rec3's numbers -/

theorem heights_leC (o : ℕ) : reference.heights.getD o 0 ≤ 18 := by
  rw [UniSound.Ids.reference_eq]
  rcases o with _ | _ | _ | _ | _ | _ | o <;> simp

theorem logMemory_eqC : reference.logMemory = 21 := by rw [UniSound.Ids.reference_eq]

theorem logBytecode_eqC : reference.logBytecode = 19 := by rw [UniSound.Ids.reference_eq]

theorem wLen_eqC : wLen = 27 := by
  unfold wLen
  have h1 := UniSound.Ids.heap_reference.1
  have h2 : reference.constraintVars = 21 := by rw [UniSound.Ids.reference_eq]; decide
  omega

theorem tdegC : ∀ t ∈ tables, (tableDegrees t).1 ≤ 21 ∧ (tableDegrees t).2 ≤ 21 := by decide +kernel

theorem blocks_rC : ∀ b ∈ reference.heap.blocks, b.r ≤ 21 := by
  rw [UniSound.Ids.heap_blocks_reference]
  decide

theorem constraintDegree_ltC : reference.constraintDegree + 1 < 2 ^ 28 := by
  rw [UniSound.Ids.reference_eq]
  decide +kernel

theorem partDeg_leC {partsE : List TablePart} (hparts : ∀ p ∈ partsE, PartDeg p) (t : ℕ) :
    max (partsE.getD t default).pullDegree (partsE.getD t default).pushDegree ≤ 21 := by
  rcases Nat.lt_or_ge t partsE.length with h | h
  · obtain ⟨t', ht', h1, h2⟩ := hparts (partsE.getD t default)
      (by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    rw [h1, h2]
    have := tdegC t' ht'
    omega
  · rw [List.getD_eq_default _ _ h]
    show max 0 0 ≤ 21
    omega

/-- **A leaf quotient's chunks** are fewer than `2^28` coefficients' (so each at most `27` variables). -/
theorem leafDeg_ltC {partsE : List TablePart} (hparts : ∀ p ∈ partsE, PartDeg p) {blk : Block}
    (hb : blk ∈ reference.heap.blocks) : leafDegC partsE blk + 1 < 2 ^ 28 := by
  have hX : 2 ^ blk.r ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) (blocks_rC blk hb)
  have e21 : (2 : ℕ) ^ 21 = 2097152 := by norm_num
  have e28 : (2 : ℕ) ^ 28 = 268435456 := by norm_num
  rw [e21] at hX
  rw [e28]
  unfold leafDegC degree
  split
  · omega
  · generalize 2 ^ blk.r = X at hX ⊢
    omega
  · generalize 2 ^ blk.r = X at hX ⊢
    omega
  · rename_i t _
    have hm := Nat.mul_le_mul_right (2 ^ blk.r - 1) (partDeg_leC hparts t)
    generalize max (partsE.getD t default).pullDegree (partsE.getD t default).pushDegree * (2 ^ blk.r - 1) = P
      at hm ⊢
    generalize Shape.leastRows blk.r = L
    generalize 2 ^ blk.r = X at hX hm ⊢
    omega

/-! ## Columns' variables -/

theorem colVars_tableC (parts : List TablePart) (o i : ℕ) :
    colVarsC parts (.table o i) = reference.heights.getD o 0 := by
  show max (reference.heights.getD o 0) (max 0 0) = _
  omega

theorem colVars_inverseC (parts : List TablePart) (o : ℕ) :
    colVarsC parts (.inverse o) = reference.heights.getD o 0 := by
  show max (reference.heights.getD o 0) (max 0 0) = _
  omega

theorem colVars_memoryC (parts : List TablePart) (k : ℕ) : colVarsC parts (.memory k) = reference.logMemory := by
  show max reference.logMemory (max 0 0) = _
  omega

theorem colVars_bytecodeFinalC (parts : List TablePart) :
    colVarsC parts .bytecodeFinal = reference.logBytecode := by
  show max reference.logBytecode (max 0 0) = _
  omega

theorem colVars_addressC (parts : List TablePart) : colVarsC parts .address = reference.logMemory := by
  show max 0 (max 0 reference.logMemory) = _
  omega

theorem colVars_bytecodeTupleC (parts : List TablePart) :
    colVarsC parts .bytecodeTuple = reference.logBytecode + 4 := by
  show max 0 (max 0 (reference.logBytecode + 4)) = _
  omega

theorem colVars_heapC (parts : List TablePart) : colVarsC parts .heap = reference.heap.h := by
  show max 0 (max reference.heap.h 0) = _
  omega

theorem colVars_tq0C (parts : List TablePart) : colVarsC parts (.treeQuotient 0) = reference.heap.h := by
  show max 0 (max reference.heap.h 0) = _
  omega

theorem colVars_tq1C (parts : List TablePart) : colVarsC parts (.treeQuotient 1) = 0 := rfl

theorem colVars_cqC (parts : List TablePart) (c : ℕ) :
    colVarsC parts (.constraintQuotient c) = (chunks (reference.constraintDegree + 1)).getD c 0 := by
  show max 0 (max ((chunks (reference.constraintDegree + 1)).getD c 0) 0) = _
  omega

theorem colVars_leafC (parts : List TablePart) (i c : ℕ) :
    colVarsC parts (.leafQuotient i c) =
      (chunks (leafDegC parts (reference.heap.blocks.getD i default) + 1)).getD c 0 := by
  show max 0 (max ((chunks (leafDegC parts (reference.heap.blocks.getD i default) + 1)).getD c 0) 0) = _
  omega

/-! ## The constraint relation's terms -/

/-- `y(t)`, BLAKE2S's coordinates of `t`. -/
abbrev yC (tE : E) : List E := coordinatesAt tE (coordinateFunctionals (reference.heights.getD opBlake2s 0))

/-- **A constraint term**: untwisted; a table's column or its inverse at its height's prefix of `w`, the memory's at
`w[..lm]`, or a slot at `y`. -/
def CrTmC (w y : List E) (tm : Term) : Prop :=
  tm.twist = 0 ∧ ((∃ o c, tm.column = .table o c ∧ tm.point = w.take (reference.heights.getD o 0)) ∨
    (∃ o, tm.column = .inverse o ∧ tm.point = w.take (reference.heights.getD o 0)) ∨
    (∃ k, tm.column = .memory k ∧ tm.point = w.take reference.logMemory) ∨
    (∃ j, tm.column = .qflockSlot j ∧ tm.point = y))

theorem copyFold_CrC (o : ℕ) (columns : List String) (w y : List E) (lift gamma : E) :
    ∀ (l : List ℕ) (s : Array Term × E),
      ∀ tm ∈ (l.foldl (UniSound.Ids.Eval.copyStep o (reference.heights.getD o 0) columns w y lift gamma) s).1.toList,
        tm ∈ s.1.toList ∨ CrTmC w y tm
  | [], _, _, h => Or.inl h
  | c :: l, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases copyFold_CrC o columns w y lift gamma l _ tm h with h1 | h1
    · unfold UniSound.Ids.Eval.copyStep at h1
      split at h1
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h1
        rcases h1 with (h1 | rfl) | rfl
        · exact Or.inl h1
        · exact Or.inr ⟨rfl, Or.inl ⟨o, c, rfl, rfl⟩⟩
        · exact Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr ⟨_, rfl, rfl⟩))⟩
      · exact Or.inl h1
    · exact Or.inr h1

theorem crStep_CrC (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ) (x : Table × TablePart) :
    ∀ tm ∈ (UniSound.Ids.Eval.crStep reference gamma t w s x).2.1.toList, tm ∈ s.2.1.toList ∨ CrTmC w (yC t) tm := by
  intro tm htm
  unfold UniSound.Ids.Eval.crStep at htm
  dsimp only at htm
  by_cases hj : x.1.opcode = opJump
  · have hb : ¬ x.1.opcode = opBlake2s := by rw [hj]; decide
    simp only [ite_eq_left hj, ite_eq_right hb, Array.toList_push, List.mem_append, List.mem_singleton] at htm
    rcases htm with (h | rfl) | rfl
    · exact Or.inl h
    · exact Or.inr ⟨rfl, Or.inl ⟨_, _, rfl, rfl⟩⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩
  · by_cases hb : x.1.opcode = opBlake2s
    · simp only [ite_eq_right hj, ite_eq_left hb] at htm
      rcases copyFold_CrC _ _ _ _ _ _ _ _ tm htm with h | h
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact Or.inl h
        · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩
      · rw [hb] at h
        exact Or.inr h
    · simp only [ite_eq_right hj, ite_eq_right hb, Array.toList_push, List.mem_append, List.mem_singleton] at htm
      rcases htm with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩

theorem crFold_CrC (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart)) (s : E × Array Term × E × ℕ),
    ∀ tm ∈ (L.foldl (UniSound.Ids.Eval.crStep reference gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨ CrTmC w (yC t) tm
  | [], _, _, h => Or.inl h
  | x :: L, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases crFold_CrC gamma t w L _ tm h with h1 | h1
    · exact crStep_CrC gamma t w s x tm h1
    · exact Or.inr h1

theorem lineFold_CrC (gamma t : E) (w y : List E) : ∀ (l : List ((E × E) × ℕ)) (s : E × Array Term × E),
    ∀ tm ∈ (l.foldl (UniSound.Ids.Eval.lineStep reference gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨ CrTmC w y tm
  | [], _, _, h => Or.inl h
  | x :: l, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases lineFold_CrC gamma t w y l _ tm h with h1 | h1
    · simp only [UniSound.Ids.Eval.lineStep, Array.toList_push, List.mem_append, List.mem_singleton] at h1
      rcases h1 with h1 | rfl
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))⟩
    · exact Or.inr h1

theorem crOf_CrC (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E) :
    ∀ tm ∈ (UniSound.Ids.Eval.crOf reference parts pw gamma t cv w).1.terms, CrTmC w (yC t) tm := by
  intro tm htm
  unfold UniSound.Ids.Eval.crOf at htm
  dsimp only at htm
  rcases lineFold_CrC gamma t w (yC t) _ _ tm htm with h | h
  · rcases crFold_CrC gamma t w _ _ tm h with h' | h'
    · simp at h'
    · exact h'
  · exact h

/-! ## The relations' facts -/

theorem forall₂_leftOfC {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ {b : β}, b ∈ m → ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => absurd hb List.not_mem_nil
  | _, _, .cons hr hl, _, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨a, ha, h⟩ := forall₂_leftOfC hl hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem relFact_singleC {parts : List TablePart} {wE y fp : List E} {tm : Term} {v : E}
    (h1 : TermFact parts y fp tm) (h2 : PointFact wE y fp tm) : RelFact parts wE y fp ⟨[tm], v⟩ :=
  ⟨⟨tm.column.commitment, fun t ht ↦ by rw [List.mem_singleton.mp ht]⟩,
    fun t ht ↦ by rw [List.mem_singleton.mp ht]; exact ⟨h1, h2⟩⟩

theorem tf_takeC {parts : List TablePart} {y fp wE : List E} (hwl : wE.length = 27) {col : Column} {k : ℕ} {c : E}
    (hns : ∀ j, col ≠ .qflockSlot j) (hle : colVarsC parts col ≤ k) (hk : k ≤ 27) :
    TermFact parts y fp (term col (wE.take k) c) :=
  Or.inl ⟨rfl, hns, by show colVarsC parts col ≤ (wE.take k).length; rw [List.length_take, hwl]; omega⟩

theorem tabRels_factC {outs : List (TablePart × List Relation)} {wE : List E} (hwl : wE.length = 27)
    (hTS : List.Forall₂ (fun t o ↦ tableShape t wE o) tables outs) (parts : List TablePart) (y fp : List E) :
    ∀ r ∈ (tabRels outs).toList, RelFact parts wE y fp r := by
  intro r hr
  unfold tabRels at hr
  rw [foldl_append_toListC (fun o : TablePart × List Relation ↦ o.2.toArray)] at hr
  simp only [List.nil_append, List.mem_flatMap] at hr
  obtain ⟨o, ho, hro⟩ := hr
  obtain ⟨t, -, hsh⟩ := forall₂_leftOfC hTS ho
  refine ⟨⟨.c1, fun tm htm ↦ ?_⟩, fun tm htm ↦ ?_⟩
  · obtain ⟨⟨i, hi⟩, -, -⟩ := hsh r hro tm htm
    rw [hi]
    rfl
  · obtain ⟨⟨i, hi⟩, hpt, htw⟩ := hsh r hro tm htm
    refine ⟨Or.inl ⟨htw, fun j h ↦ (by rw [hi] at h; cases h), ?_⟩, fun _ ↦ Or.inl ⟨_, hpt⟩⟩
    rw [hi, hpt, colVars_tableC, List.length_take, hwl]
    have := heights_leC t.opcode
    omega

theorem constraint_factC {wE : List E} (hwl : wE.length = 27) {tE : E} {constraint : Relation}
    (hCS : constraintShape wE tE constraint) (parts : List TablePart) (fp : List E) :
    RelFact parts wE (yC tE) fp constraint := by
  obtain ⟨partsE, pwE, gammaE, cvE, rfl⟩ := hCS
  rw [UniSound.Ids.Eval.constraintRelation_eq]
  have hC := crOf_CrC partsE pwE gammaE tE cvE wE
  refine ⟨⟨.c1, fun tm htm ↦ ?_⟩, fun tm htm ↦ ?_⟩
  · obtain ⟨-, ⟨o, c, hc, -⟩ | ⟨o, hc, -⟩ | ⟨k, hc, -⟩ | ⟨j, hc, -⟩⟩ := hC tm htm <;> rw [hc] <;> rfl
  · obtain ⟨htw, ⟨o, c, hc, hp⟩ | ⟨o, hc, hp⟩ | ⟨k, hc, hp⟩ | ⟨j, hc, hp⟩⟩ := hC tm htm
    · refine ⟨Or.inl ⟨htw, fun j h ↦ (by rw [hc] at h; cases h), ?_⟩, fun _ ↦ Or.inl ⟨_, hp⟩⟩
      rw [hc, hp, colVars_tableC, List.length_take, hwl]
      have := heights_leC o
      omega
    · refine ⟨Or.inl ⟨htw, fun j h ↦ (by rw [hc] at h; cases h), ?_⟩, fun _ ↦ Or.inl ⟨_, hp⟩⟩
      rw [hc, hp, colVars_inverseC, List.length_take, hwl]
      have := heights_leC o
      omega
    · refine ⟨Or.inl ⟨htw, fun j h ↦ (by rw [hc] at h; cases h), ?_⟩, fun _ ↦ Or.inl ⟨_, hp⟩⟩
      rw [hc, hp, colVars_memoryC, List.length_take, hwl, logMemory_eqC]
      omega
    · exact ⟨Or.inr (Or.inl ⟨htw, ⟨j, hc⟩, hp⟩), fun _ ↦ Or.inr (Or.inl hp)⟩

/-- A leaf quotient's term: at its chunk's prefix of `w`, of its chunk's variables. -/
theorem leafTerm_factC {wE : List E} (hwl : wE.length = 27) {partsE : List TablePart}
    (hparts : ∀ p ∈ partsE, PartDeg p) {blk : Block} {idx : ℕ}
    (hx : (blk, idx) ∈ reference.heap.blocks.zip (List.range reference.heap.blocks.length)) {sizes : List ℕ}
    (hsz : sizes = chunks (leafDegC partsE blk + 1)) {sc : E} {tm : Term}
    (htm : tm ∈ quotientTerms (Column.leafQuotient idx) sizes wE sc) (y fp : List E) : TermFact partsE y fp tm := by
  subst hsz
  rw [UniSound.Ids.Eval.quotientTerms_eq] at htm
  obtain ⟨c, hc, h1, h2, h3⟩ := UniSound.Ids.Eval.qTerms_mem _ wE _ 0 _ tm htm
  rw [Nat.zero_add] at h1
  have hmemc : (chunks (leafDegC partsE blk + 1)).getD c 0 ∈ chunks (leafDegC partsE blk + 1) := by
    rw [List.getD_eq_getElem _ _ hc]
    exact List.getElem_mem hc
  have hlt := UniSound.Ids.Eval.chunk_lt _ 28 (leafDeg_ltC hparts (List.of_mem_zip hx).1) _ hmemc
  have hget : reference.heap.blocks.getD idx default = blk := (UniSound.Ids.Eval.mem_zip_range_iff _ default _ hx).2
  refine Or.inl ⟨h3, fun j h ↦ (by rw [h1] at h; cases h), ?_⟩
  rw [h1, h2, colVars_leafC, hget, List.length_take, hwl]
  omega

theorem heap_factC {wE : List E} (hwl : wE.length = 27) (activeE : List E) (partsE : List TablePart)
    (weightsE : Array E) (betaE hvE cvE mplE mpsE bplE bpsE : E) (hparts : ∀ p ∈ partsE, PartDeg p) (y fp : List E) :
    ∀ r ∈ (UniStatement.heapRelations reference activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE
      (chunks (reference.constraintDegree + 1))).1, RelFact partsE wE y fp r := by
  intro r hr
  have hc2 := UniSound.Ids.Eval.heap_terms reference activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE _
    r hr
  refine ⟨⟨.c2, fun tm htm ↦ (hc2 tm htm).1⟩, fun tm htm ↦ ⟨?_, fun h ↦ by rw [(hc2 tm htm).1] at h; cases h⟩⟩
  have hh := UniSound.Ids.heap_reference.1
  rw [UniSound.Ids.Eval.heapRelations_fst] at hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | hr) | rfl
  · simp only [Relation.equal, List.mem_singleton] at htm
    subst htm
    exact tf_takeC hwl (fun j h ↦ by cases h) (by rw [colVars_heapC]) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at htm
    rcases htm with rfl | rfl | rfl | rfl
    · refine Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩
      show colVarsC partsE .heap ≤ ((wE.drop 1).take reference.heap.h).length
      rw [colVars_heapC, List.length_take, List.length_drop, hwl]
      omega
    · refine Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩
      show colVarsC partsE .heap ≤ ((wE.take reference.heap.h).modify 0 (· + 1)).length
      rw [colVars_heapC, List.length_modify, List.length_take, hwl]
      omega
    · exact tf_takeC hwl (fun j h ↦ by cases h) (by rw [colVars_tq0C]) (by omega)
    · refine Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩
      show colVarsC partsE (.treeQuotient 1) ≤ ([] : List E).length
      rw [colVars_tq1C]
      exact Nat.zero_le _
  · simp only [List.mem_singleton] at htm
    subst htm
    refine Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩
    show colVarsC partsE .heap ≤ ((List.range reference.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0).length
    rw [colVars_heapC, List.length_map, List.length_range]
  · obtain ⟨⟨blk, idx⟩, hx, rfl⟩ := List.mem_map.mp hr
    have hmixed : ∀ c : E, TermFact partsE y fp (term .heap ((List.range reference.heap.h).map fun l ↦
        if l < blk.r then wE.getD l 0 + pointE (blk.position >>> l) else pointE (blk.position >>> l)) c) :=
      fun c ↦ Or.inl ⟨rfl, fun j h ↦ (by cases h), by
        show colVarsC partsE .heap ≤ ((List.range reference.heap.h).map _).length
        rw [colVars_heapC, List.length_map, List.length_range]⟩
    unfold UniSound.Ids.Eval.blockRel at htm
    dsimp only at htm
    cases hl : blk.leaves <;> simp only [hl, List.mem_append, List.mem_singleton] at htm
    all_goals first
      | (subst htm; exact hmixed _)
      | (rcases htm with rfl | htm
         · exact hmixed _
         · exact leafTerm_factC hwl hparts hx (by simp only [leafDegC, hl]) htm y fp)
  · rw [UniSound.Ids.Eval.quotientTerms_eq] at htm
    obtain ⟨c, hc, h1, h2, h3⟩ := UniSound.Ids.Eval.qTerms_mem _ wE _ 0 _ tm htm
    rw [Nat.zero_add] at h1
    have hmemc : (chunks (reference.constraintDegree + 1)).getD c 0 ∈ chunks (reference.constraintDegree + 1) := by
      rw [List.getD_eq_getElem _ _ hc]
      exact List.getElem_mem hc
    have hlt := UniSound.Ids.Eval.chunk_lt _ 28 constraintDegree_ltC _ hmemc
    refine Or.inl ⟨h3, fun j h ↦ (by rw [h1] at h; cases h), ?_⟩
    rw [h1, h2, colVars_cqC, List.length_take, hwl]
    omega

/-! ## Off the hazard, no `C1` point extends `y(t)` -/

theorem take_getD0C (l : List E) (m : ℕ) (hm : 0 < m) : (l.take m).getD 0 0 = l.getD 0 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  cases l <;> rfl

theorem digits_getD0C (tE : E) : (digits tE wLen).getD 0 0 = tE := by
  rw [digits_eq, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range, wLen_eqC]; omega),
    List.getElem_map, List.getElem_range]
  rfl

/-- **Off `Z_bad`'s roots, `y(t)`'s first coordinate is neither `t` nor `p_0`** (`UniSound.Ids.Eval.y_self`'s
argument), at any shape (at `reference` the kernel would evaluate the functionals). -/
theorem y0_neGenC (S : UniStatement.Shape) {tE p0 : E} (hsz : 0 < S.heights.getD opBlake2s 0)
    (hz : (UniSound.Ids.zBad S p0).eval tE ≠ 0) :
    (coordinatesAt tE (coordinateFunctionals (S.heights.getD opBlake2s 0))).getD 0 0 ≠ tE ∧
      (coordinatesAt tE (coordinateFunctionals (S.heights.getD opBlake2s 0))).getD 0 0 ≠ p0 := by
  have hy0 : (coordinatesAt tE (coordinateFunctionals (S.heights.getD opBlake2s 0))).getD 0 0 =
      (UniSound.Ids.yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) 0).eval tE :=
    UniSound.Ids.Eval.coordinatesAt_getD _ _ _ (by rw [UniSound.Ids.Eval.coordinateFunctionals_size]; exact hsz)
  unfold UniSound.Ids.zBad at hz
  rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    ← hy0] at hz
  exact ⟨fun h ↦ hz (by rw [h, CharTwo.add_self_eq_zero, zero_mul]),
    fun h ↦ hz (by rw [h, CharTwo.add_self_eq_zero, mul_zero])⟩

/-- **Off the hazard, `y(t)`'s first coordinate is neither `t` nor `p_0`.** -/
theorem y0_neC {tE p0 : E} (hhaz : ¬ Hazard p0 tE) : (yC tE).getD 0 0 ≠ tE ∧ (yC tE).getD 0 0 ≠ p0 :=
  y0_neGenC reference (by rw [reference_blake2s_height]; omega) hhaz

/-! ## `Compose`'s interface: the shapes -/

/-- **`ShapeSpec`**: off the hazard, reduce's relations satisfy the tail's conditions (`TailOK`), from the parts'
shapes. -/
theorem shapeSpec : ShapeSpec tableShape constraintShape heapShape TailOK := by
  intro tE alphasE betaE flockPt target outs mfc addr mpl bfc bpl constraint heapOut hα hfp hTS hCS hHS hhaz
  obtain ⟨activeE, partsE, weightsE, betaH, hvE, cvE, mplE, mpsE, bplE, bpsE, -, -, hparts, -, rfl⟩ := hHS
  have hwl : (digits tE wLen).length = 27 := by rw [digits_lengthC, wLen_eqC]
  have hy : (yC tE).length = 18 := by
    rw [UniSound.Ids.Eval.coordinatesAt_length, UniSound.Ids.Eval.coordinateFunctionals_size,
      reference_blake2s_height]
  obtain ⟨hne1, hne2⟩ := y0_neC hhaz
  have hlm := logMemory_eqC
  have hlb := logBytecode_eqC
  refine tailOK_ofC (parts := partsE) (wE := digits tE wLen) (y := yC tE) (fp := flockPt)
    (c2Uni_entryC activeE partsE weightsE betaH hvE cvE mplE mpsE bplE bpsE (digits tE wLen)) hy hfp ?_ ?_ ?_
  · intro r hr
    unfold relsUni at hr
    simp only [Array.toList_push, Array.toList_append, List.mem_append, List.mem_singleton] at hr
    rcases hr with ((((((((hr | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | hr) | rfl)
    · exact tabRels_factC hwl hTS partsE _ _ r hr
    · exact relFact_singleC (tf_takeC hwl (fun j h ↦ by cases h) (by rw [colVars_memoryC]) (by omega))
        (fun _ ↦ Or.inl ⟨_, rfl⟩)
    · exact relFact_singleC (tf_takeC hwl (fun j h ↦ by cases h) (by rw [colVars_addressC]) (by omega))
        (fun h ↦ by cases h)
    · refine ⟨⟨.c1, fun tm htm ↦ ?_⟩, fun tm htm ↦ ?_⟩
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp htm
        rfl
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp htm
        exact ⟨tf_takeC hwl (fun j h ↦ by cases h) (by rw [colVars_memoryC]) (by omega), fun _ ↦ Or.inl ⟨_, rfl⟩⟩
    · exact relFact_singleC (tf_takeC hwl (fun j h ↦ by cases h) (by rw [colVars_bytecodeFinalC]) (by omega))
        (fun _ ↦ Or.inl ⟨_, rfl⟩)
    · refine relFact_singleC (Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩) (fun h ↦ by cases h)
      show colVarsC partsE .bytecodeTuple ≤ (alphasE ++ (digits tE wLen).take reference.logBytecode).length
      rw [colVars_bytecodeTupleC, List.length_append, List.length_take, hwl, hα]
      omega
    · exact constraint_factC hwl hCS partsE flockPt
    · exact heap_factC hwl activeE partsE weightsE betaH hvE cvE mplE mpsE bplE bpsE hparts _ _ r hr
    · exact relFact_singleC (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (fun _ ↦ Or.inr (Or.inr rfl))
  · intro k hlt heq
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hlt
      · exact hk
    have h0 := congrArg (fun l ↦ l.getD 0 0) heq
    rw [take_getD0C _ (yC tE).length (by omega), take_getD0C (digits tE wLen) k hk, digits_getD0C] at h0
    exact hne1 h0.symm
  · intro heq
    have h0 := congrArg (fun l ↦ l.getD 0 0) heq
    rw [take_getD0C flockPt (yC tE).length (by omega)] at h0
    apply hne2
    rw [← h0]
    cases flockPt <;> rfl

/-- info: 'RecGraph.Sim.shapeSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shapeSpec

end RecGraph.Sim
