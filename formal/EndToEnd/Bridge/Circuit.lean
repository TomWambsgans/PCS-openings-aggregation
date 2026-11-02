-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit.Build
import Bridge.Circuit.Wiring

/-!
# The statement's circuit is F0b's

`PcsQuotient.membership 22` (`formal/Statement/PcsQuotient/Circuit.lean`) and F0b's
`PcsCircuit.membership` (`formal/Circuit/Circuit/Defs.lean`) are two transcriptions of
`quotient::circuit::membership`, with two types of sources. **`membership_eq`**: read by `srcTr`
(`circuitTr`), the statement's circuit is F0b's, field by field (`membership_logRows`,
`membership_usedRows`, `membership_rows`, `membership_inputs`, `membership_sigma`). The proof
simulates the statement's builder by F0b's step by step for general arguments
(`Bridge/Circuit/Sim.lean`, `Loops.lean`, `Keccak.lean`, `Build.lean`), and the two wirings on any
rows that read rows of the circuit (`Wiring.lean`), F0b's `membership_order` and
`membership_input_row` saying that `membership`'s do. Nothing evaluates the circuit.
-/

namespace Bridge.Circuit

/-- An F0b row as the statement's. -/
def rowOf (r : PcsCircuit.Row) : PcsQuotient.Row := ⟨srcOf r.x, srcOf r.y, srcOf r.c⟩

@[simp] theorem rowOf_rowTr (r : PcsQuotient.Row) : rowOf (rowTr r) = r := by
  obtain ⟨x, y, c⟩ := r
  simp [rowOf, rowTr]

/-- **The statement's circuit read as F0b's**: its rows read by `srcTr`, the rest kept. -/
def circuitTr (c : PcsQuotient.Circuit) : PcsCircuit.Circuit :=
  ⟨c.logRows, c.usedRows, c.rows.map rowTr, c.inputs, c.sigma⟩

/-! ## The run of the membership rows -/

/-- The statement's `membership` is `finish` of its builder's run, read by projections (by
definition: `formal/Statement/PcsQuotient/Circuit.lean` reads the run by projections, so that no
proof about the circuit's fields evaluates the `2^22`-row run). -/
theorem membership_eq_finish (logRows : ℕ) : PcsQuotient.membership logRows =
    PcsQuotient.finish logRows
      (PcsQuotient.publicWords (PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.1.1
        (PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.1.2)
      (PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.2 := rfl

theorem qrun_def {α : Type} (p : PcsQuotient.BuildM α) (b : PcsQuotient.Builder) :
    qrun p b = (p.run b).run := rfl

/-- F0b's run of the membership rows simulates the statement's. -/
theorem membershipRun_sim :
    (PcsCircuit.runBuild PcsCircuit.membershipBuild PcsCircuit.Builder.new).1.1 =
        ((PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.1.1.map srcTr).toArray ∧
      (PcsCircuit.runBuild PcsCircuit.membershipBuild PcsCircuit.Builder.new).1.2 =
        ((PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.1.2.map srcTr).toArray ∧
      (PcsCircuit.runBuild PcsCircuit.membershipBuild PcsCircuit.Builder.new).2 =
        bTr (PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.2 := by
  have h := sim_membershipBuilder PcsQuotient.Builder.new
  rw [bTr_new, qrun_def] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem pcMembership_eq : PcsCircuit.membership =
    (bTr (PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.2).finish
      PcsCircuit.logRows (PcsCircuit.publicWords
        ((PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.1.1.map srcTr).toArray
        ((PcsQuotient.membershipBuilder.run PcsQuotient.Builder.new).run.1.2.map srcTr).toArray) := by
  obtain ⟨h1, h2, h3⟩ := membershipRun_sim
  rw [PcsCircuit.membership_eq, h1, h2, h3]

/-- The statement's `22` is F0b's `logRows`. -/
theorem membership_22 : PcsQuotient.membership 22 = PcsQuotient.membership PcsCircuit.logRows :=
  congrArg PcsQuotient.membership (rfl : (22 : ℕ) = PcsCircuit.logRows)

/-! ## Closing, field by field, for every builder and wires -/

section Finish

variable (logRows : ℕ) (y root : List PcsQuotient.Src) (b : PcsQuotient.Builder)

theorem finish_logRows' :
    (PcsQuotient.finish logRows (PcsQuotient.publicWords y root) b).logRows =
      ((bTr b).finish logRows
        (PcsCircuit.publicWords (y.map srcTr).toArray (root.map srcTr).toArray)).logRows := rfl

theorem finish_usedRows' :
    (PcsQuotient.finish logRows (PcsQuotient.publicWords y root) b).usedRows =
      ((bTr b).finish logRows
        (PcsCircuit.publicWords (y.map srcTr).toArray (root.map srcTr).toArray)).usedRows := by
  rw [finish_eq]
  simp [PcsCircuit.Builder.finish]

theorem finish_inputs' :
    (PcsQuotient.finish logRows (PcsQuotient.publicWords y root) b).inputs =
      ((bTr b).finish logRows
        (PcsCircuit.publicWords (y.map srcTr).toArray (root.map srcTr).toArray)).inputs := rfl

theorem finish_rows' :
    (PcsQuotient.finish logRows (PcsQuotient.publicWords y root) b).rows.map rowTr =
      ((bTr b).finish logRows
        (PcsCircuit.publicWords (y.map srcTr).toArray (root.map srcTr).toArray)).rows := by
  rw [finish_eq]
  exact finish_rows logRows y root b

theorem finish_sigma'
    (hs : ∀ r < 2 ^ logRows,
      PcsCircuit.slot (((bTr b).finish logRows (PcsCircuit.publicWords (y.map srcTr).toArray
        (root.map srcTr).toArray)).rows.getD r .idle).x < 2 ^ logRows + 2 ∧
      PcsCircuit.slot (((bTr b).finish logRows (PcsCircuit.publicWords (y.map srcTr).toArray
        (root.map srcTr).toArray)).rows.getD r .idle).y < 2 ^ logRows + 2 ∧
      PcsCircuit.slot (((bTr b).finish logRows (PcsCircuit.publicWords (y.map srcTr).toArray
        (root.map srcTr).toArray)).rows.getD r .idle).c < 2 ^ logRows + 2) :
    (PcsQuotient.finish logRows (PcsQuotient.publicWords y root) b).sigma =
      ((bTr b).finish logRows
        (PcsCircuit.publicWords (y.map srcTr).toArray (root.map srcTr).toArray)).sigma := by
  have hrows := finish_rows' logRows y root b
  rw [finish_eq] at hrows ⊢
  simp only at hrows ⊢
  have hσ : ((bTr b).finish logRows (PcsCircuit.publicWords (y.map srcTr).toArray
      (root.map srcTr).toArray)).sigma = PcsCircuit.wiring ((bTr b).finish logRows
        (PcsCircuit.publicWords (y.map srcTr).toArray (root.map srcTr).toArray)).rows := rfl
  rw [hσ, ← hrows]
  have hsz : (finishRowsQ logRows (PcsQuotient.publicWords y root) b).size = 2 ^ logRows := by
    simp [finishRowsQ]
  refine wiring_eq logRows _ hsz fun r hr => ?_
  rw [hsz] at hr ⊢
  obtain ⟨hx, hy, hc⟩ := hs r hr
  have hget : ((bTr b).finish logRows (PcsCircuit.publicWords (y.map srcTr).toArray
      (root.map srcTr).toArray)).rows.getD r .idle =
      rowTr ((finishRowsQ logRows (PcsQuotient.publicWords y root) b).getD r PcsQuotient.idle) := by
    rw [← hrows]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases (finishRowsQ logRows (PcsQuotient.publicWords y root) b)[r]? <;> rfl
  rw [hget] at hx hy hc
  simp only [rowTr, ← qSlot_eq] at hx hy hc
  exact ⟨hx, hy, hc⟩

end Finish

/-! ## The membership circuit, field by field -/

-- The circuits are closed terms of `2^22` rows: nothing below may unfold them.
attribute [local irreducible] PcsQuotient.membership PcsCircuit.membership
  PcsQuotient.membershipBuilder PcsCircuit.membershipBuild

/-- The circuit's size, as given. -/
theorem membership_logRows (logRows : ℕ) : (PcsQuotient.membership logRows).logRows = logRows := by
  rw [membership_eq_finish]
  exact finish_logRows' logRows _ _ _

theorem membership_logRows' :
    (PcsQuotient.membership 22).logRows = PcsCircuit.membership.logRows := by
  rw [membership_22, membership_eq_finish, pcMembership_eq]
  exact finish_logRows' PcsCircuit.logRows _ _ _

theorem membership_usedRows :
    (PcsQuotient.membership 22).usedRows = PcsCircuit.membership.usedRows := by
  rw [membership_22, membership_eq_finish, pcMembership_eq]
  exact finish_usedRows' PcsCircuit.logRows _ _ _

/-- **The inputs** (the rows of the free bits, in order). -/
theorem membership_inputs : (PcsQuotient.membership 22).inputs = PcsCircuit.membership.inputs := by
  rw [membership_22, membership_eq_finish, pcMembership_eq]
  exact finish_inputs' PcsCircuit.logRows _ _ _

/-- The input rows are rows of the circuit. -/
theorem membership_inputs_lt : ∀ r ∈ (PcsQuotient.membership 22).inputs, r < 2 ^ 22 := by
  intro r hr
  rw [membership_inputs] at hr
  exact (PcsCircuit.membership_input_row r hr).1

/-- **The rows**, read by `rowTr`. -/
theorem membership_rows :
    (PcsQuotient.membership 22).rows.map rowTr = PcsCircuit.membership.rows := by
  rw [membership_22, membership_eq_finish, pcMembership_eq]
  exact finish_rows' PcsCircuit.logRows _ _ _

theorem map_rowTr_rowOf (a : Array PcsQuotient.Row) : (a.map rowTr).map rowOf = a := by
  rw [Array.map_map]
  conv_rhs => rw [← Array.map_id a]
  congr 1
  funext r
  exact rowOf_rowTr r

/-- **The rows**, F0b's read by `rowOf`. -/
theorem membership_rows' :
    (PcsQuotient.membership 22).rows = PcsCircuit.membership.rows.map rowOf := by
  rw [← membership_rows, map_rowTr_rowOf]

theorem slot_lt_of_ranked {rk : ℕ} {s : PcsCircuit.Src} (h : PcsCircuit.Ranked rk s) :
    PcsCircuit.slot s < 2 ^ PcsCircuit.logRows + 2 := by
  cases s with
  | zero => simp [PcsCircuit.slot]
  | one => simp [PcsCircuit.slot]
  | row r => simp only [PcsCircuit.Ranked] at h; simp only [PcsCircuit.slot]; omega

/-- Every source of `membership` reads a slot below `2^22 + 2`: a constant or a row of the
circuit (F0b's `membership_input_row`, `membership_order`). -/
theorem membership_slots (r : ℕ) (hr : r < 2 ^ PcsCircuit.logRows) :
    PcsCircuit.slot (PcsCircuit.membership.rows.getD r .idle).x < 2 ^ PcsCircuit.logRows + 2 ∧
      PcsCircuit.slot (PcsCircuit.membership.rows.getD r .idle).y < 2 ^ PcsCircuit.logRows + 2 ∧
      PcsCircuit.slot (PcsCircuit.membership.rows.getD r .idle).c < 2 ^ PcsCircuit.logRows + 2 := by
  rcases Classical.em (r ∈ PcsCircuit.membership.inputs) with hin | hin
  · obtain ⟨hlt, -, hrow⟩ := PcsCircuit.membership_input_row r hin
    rw [hrow]
    show 2 + r < 2 ^ PcsCircuit.logRows + 2 ∧ 2 + r < 2 ^ PcsCircuit.logRows + 2 ∧
      2 + r < 2 ^ PcsCircuit.logRows + 2
    omega
  · obtain ⟨hx, hy, hc⟩ := PcsCircuit.membership_order r hr hin
    exact ⟨slot_lt_of_ranked hx, slot_lt_of_ranked hy, slot_lt_of_ranked hc⟩

/-- **σ**: the statement's wiring of `membership 22` is F0b's. -/
theorem membership_sigma : (PcsQuotient.membership 22).sigma = PcsCircuit.membership.sigma := by
  have hs := membership_slots
  rw [pcMembership_eq] at hs
  rw [membership_22, membership_eq_finish, pcMembership_eq]
  exact finish_sigma' PcsCircuit.logRows _ _ _ hs

/-- **The statement's circuit is F0b's**, read by `srcTr`. -/
theorem membership_eq : circuitTr (PcsQuotient.membership 22) = PcsCircuit.membership := by
  have e : ∀ c : PcsCircuit.Circuit, c = ⟨c.logRows, c.usedRows, c.rows, c.inputs, c.sigma⟩ :=
    fun _ => rfl
  rw [e PcsCircuit.membership, ← membership_logRows', ← membership_usedRows, ← membership_rows,
    ← membership_inputs, ← membership_sigma]
  rfl

end Bridge.Circuit
