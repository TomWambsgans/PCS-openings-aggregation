-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Eval

/-!
# The relations' number, the columns absent from `C1`, the constraints' number

* **`relCount_reference`** (`RelCountP D Fl 135`): `relsOf` is each table's part (its sent values,
  then at most two relations a flush: `tablePartOf_rels_len`), the memory's three, the bytecode's two,
  the constraint quotient's, the heap's `3 + |blocks| + 1` (`heapRelations_fst`) and at most one ring
  end. The tables' part is `115` (the kernel counts the six tables' sent columns and flushes, no
  coefficient), the reference heap has `9` blocks.
* **`c1Absent`**: a column not in a stack's column list has no limbs (`limbs_new_absent`, for any
  `StackLayout.new`), so a table's column past its width has none in `C1`, at every shape.
* **`ncvOf_eq`**: `30` constraints at every shape (`JUMP`'s two, six counters, `BLAKE2S`'s eighteen
  copies, three public lines) plus one.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset UniSound.Ids.Eval

/-! ## The relations' number -/

theorem flushStep_rels_len (at_ : ℕ → Column) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) (st : TPState) (fl : List Form × List Form) :
    (flushStep at_ pt weights beta sent st fl).rels.length ≤ st.rels.length + 2 := by
  unfold flushStep
  dsimp only
  split_ifs <;> simp

theorem flushFold_rels_len (at_ : ℕ → Column) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) : ∀ (l : List (List Form × List Form)) (st : TPState),
      (l.foldl (flushStep at_ pt weights beta sent) st).rels.length ≤ st.rels.length + 2 * l.length
  | [], st => by simp
  | fl :: l, st => by
    rw [List.foldl_cons]
    have h1 := flushFold_rels_len at_ pt weights beta sent l (flushStep at_ pt weights beta sent st fl)
    have h2 := flushStep_rels_len at_ pt weights beta sent st fl
    rw [List.length_cons]
    omega

/-- A table's relations: its sent values', at most two a flush. -/
def tabRels (tab : Table) : ℕ := (sentColumns tab).length + 2 * (tab.flushes.pull.zip tab.flushes.push).length

theorem tablePartOf_rels_len (tab : Table) (lh : ℕ) (weights : Array E) (beta : E) (w vals : List E) :
    (tablePartOf tab lh weights beta w vals).2.1.length ≤ tabRels tab := by
  unfold tablePartOf tabRels
  dsimp only
  refine (flushFold_rels_len _ _ _ _ _ _ _).trans ?_
  simp

theorem tablesPart_rels_len (S : Shape) (weights : Array E) (beta : E) (w : List E) :
    ∀ (ts : List Table) (vals : List E),
      (tablesPart S weights beta w ts vals).2.1.length ≤ (ts.map tabRels).sum
  | [], _ => by simp [tablesPart]
  | t :: ts, vals => by
    simp only [tablesPart, List.length_append, List.map_cons, List.sum_cons]
    have h1 := tablePartOf_rels_len t (S.heights.getD t.opcode 0) weights beta w vals
    have h2 := tablesPart_rels_len S weights beta w ts
      (tablePartOf t (S.heights.getD t.opcode 0) weights beta w vals).2.2
    omega

set_option maxRecDepth 100000 in
/-- **The six tables' relations**: `115` (the kernel counts their sent columns and flushes). -/
theorem tables_rels : (tables.map tabRels).sum = 115 := by
  decide +kernel

theorem ringRels_len (inp : RelInput) : inp.ringRels.length ≤ 1 := by
  unfold RelInput.ringRels
  split <;> simp

/-- **The verifier's relations at `t`**: at most `115 + 6 + |blocks| + 5`. -/
theorem relsOf_len (inp : RelInput) : (relsOf inp).length ≤ 126 + inp.shape.heap.blocks.length := by
  unfold relsOf RelInput.heap
  rw [heapRelations_fst]
  have h1 : inp.tp.2.1.length ≤ 115 :=
    (tablesPart_rels_len inp.shape inp.weights inp.beta inp.w tables inp.vals).trans_eq tables_rels
  have h2 := ringRels_len inp
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_zip,
    List.length_range, min_self, RelInput.memRels, RelInput.bcRels]
  omega

/-- **At most `135` relations** at the reference shape (`9` heap blocks). -/
theorem relCount_reference (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (hS : D.shape = reference) :
    RelCountP D Fl 135 := by
  intro s ch fd t vals
  have h := relsOf_len (relInput D s ch (Fl.prog.out fd []) t vals)
  have hb : (relInput D s ch (Fl.prog.out fd []) t vals).shape.heap.blocks.length = 9 := by
    show D.shape.heap.blocks.length = 9
    rw [hS, heap_blocks_reference]
    rfl
  unfold relsAt
  omega

/-! ## Columns absent from a layout -/

/-- **A column not listed has no limbs**, in any `StackLayout.new`. -/
theorem limbs_new_absent (cols : List (Column × ℕ × Bool)) (col : Column) (h : ∀ x ∈ cols, x.1 ≠ col) :
    (StackLayout.new cols).limbs col = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun b hb ↦ by
    obtain ⟨e, he⟩ := limbs_new_mem cols col b hb
    exact h _ he rfl

/-- Every table is the one at its opcode. -/
theorem tables_getD_opcode : ∀ tab ∈ tables, tables.getD tab.opcode default = tab := by
  simp only [tables, List.mem_cons, List.not_mem_nil, or_false]
  rintro tab (rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

/-- **A table's column past its width has no limbs in `C1`**, at every shape. -/
theorem c1Absent (S : Shape) : ∀ o < 6, ∀ i, (tables.getD o default).width ≤ i →
    (layoutOf S .c1).limbs (.table o i) = [] := by
  intro o _ i hi
  rw [layoutOf_c1]
  refine limbs_new_absent _ _ fun x hx he ↦ ?_
  rw [c1Cols_eq] at hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  dsimp only at he
  subst he
  unfold c1Names at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_map, List.mem_range] at hc
  rcases hc with ((h | ⟨tab, htab, ⟨c, hc, he⟩ | h⟩) | ⟨k, _, h⟩) | h
  · exact Column.noConfusion h
  · simp only [Column.table.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [tables_getD_opcode tab htab] at hi
    omega
  · exact Column.noConfusion h
  · exact Column.noConfusion h
  · exact Column.noConfusion h

/-! ## The constraints' number -/

theorem tableConstraintsP_len (S : Shape) (c : Stk) (tab : Table) :
    (tableConstraintsP S c tab).length = (if tab.opcode = opJump then 2 else 0) + 1 +
      if tab.opcode = opBlake2s then
        ((List.range tab.width).filterMap fun i ↦ qflockSlot (tab.columns.getD i "")).length
      else 0 := by
  unfold tableConstraintsP
  dsimp only
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> simp [length_filterMap_map]

/-- A table's constraints' number. -/
def tabCons (tab : Table) : ℕ := (if tab.opcode = opJump then 2 else 0) + 1 +
  if tab.opcode = opBlake2s then
    ((List.range tab.width).filterMap fun i ↦ qflockSlot (tab.columns.getD i "")).length
  else 0

set_option maxRecDepth 100000 in
theorem tables_cons : (tables.map tabCons).sum = 26 := by
  decide +kernel

/-- **`30` constraint vectors' entries**, at every shape. -/
theorem ncvOf_eq (S : Shape) : ncvOf S = 30 := by
  unfold ncvOf constraintsP linesP
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_zip, linesOf,
    List.length_cons, List.length_nil, List.length_range]
  rw [show (tables.map fun tab ↦ (tableConstraintsP S (fun _ ↦ 0) tab).length) = tables.map tabCons from
    List.map_congr_left fun tab _ ↦ tableConstraintsP_len S _ tab, tables_cons]
  norm_num

end UniSound.Ids

/-- info: 'UniSound.Ids.relCount_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.relCount_reference

/-- info: 'UniSound.Ids.c1Absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.c1Absent

/-- info: 'UniSound.Ids.ncvOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.ncvOf_eq
