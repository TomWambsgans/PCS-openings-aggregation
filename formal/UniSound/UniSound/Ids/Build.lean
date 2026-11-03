-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Batch

/-!
# `BusModel` and `UniIdsRest`, constructed

**`busModelOf D N h`** and **`idsRestOf D N h Fl g`**: the bus model and the identity model of
`UniSound.Bus`, for a deployment `D` and Flock's phase `Fl`, from the data of `Model.lean`, the proved
reductions (the batch's start, `batch_start_of`; the pending matrices', `pending_of_diffs`; the bounds),
and two structures of named hypotheses:

* `IdsHyps D N` — the bridges of `Bridges.lean` (the batch's algebra, the deployment's constants, Lv42),
  each a statement about the verifier's, Lv42's or the deployment's definitions;
* `IdsGaps D Fl` — the reductions between the verifier's checks and the identities not yet proved
  here: the relations at `t` give the identities at `t` (`DiffsEvalP`), the identities as polynomials give
  the heap and the constraint vectors (`MainOfPolysP`), the constraint vectors give the rows' constraints
  (`CvecOkP`), the ring-switch relation gives Flock's claim (`DiffsFlockP`), the degrees (`DegBoundP`), the
  relations' number (`RelCountP`).

`uniKnowledgeSoundness_ids`: the end theorem with these in place of `B` and `J`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

/-! ## The reductions, stated -/

/-- **The relations at `t` give the identities at `t`.** -/
def DiffsEvalP (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) : Prop :=
  ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffsOf D Fl s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    ∀ P ∈ polysOf D Fl s c1 ch fd c2, P.eval t = 0

/-- **The identities as polynomials give the heap and the constraint vectors** (`BusModel.MainOK`). -/
def MainOfPolysP (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) : Prop :=
  ∀ s c1 ch fd c2, (∀ P ∈ polysOf D Fl s c1 ch fd c2, P = 0) →
    (hdOf D c1 s).Sat (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) ∧
      ∀ x < 2 ^ D.shape.constraintVars, powComb (cvecOf D c1 s x) (ch.getD 5 0) = 0

/-- **The constraint vectors' vanishing gives the counts in range and the rows' constraints.** -/
def CvecOkP (D : Deployment) : Prop :=
  ∀ s c, (∀ x < 2 ^ D.shape.constraintVars, ∀ v ∈ cvecOf D c s x, v = 0) →
    CountsFit D.shape s.2 ∧ RowConstraints D c s

/-- **The ring-switch relation gives Flock's claim on `q_flock`.** -/
def DiffsFlockP (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) : Prop :=
  ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffsOf D Fl s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    FlockEndHolds (qfOf D c1 κ) (Fl.prog.out fd [])

/-- **The identities' degrees** sum to at most `d`. -/
def DegBoundP (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (d : ℕ) : Prop :=
  ∀ s c1 ch fd c2, ((polysOf D Fl s c1 ch fd c2).map Polynomial.natDegree).sum ≤ d

/-- **At most `n` relations.** -/
def RelCountP (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (n : ℕ) : Prop :=
  ∀ s ch fd t vals, (relsAt D Fl s ch fd t vals).length ≤ n

/-- **The bridges** (`Bridges.lean`), at the bus bound `N`. -/
structure IdsHyps (D : Deployment) (N : ℕ) : Prop where
  weightAtLinear : WeightAtLinear
  combineEq : CombineEq
  lvRealizes : LvRealizes D
  lvConstraints : LvConstraints D
  lvAux : LvAux D
  lvBusCount : LvBusCount D N
  heapGood : HeapGood D.shape

/-- **The reductions not yet proved here**, at the degrees' bound `d` and the relations' `n`. -/
structure IdsGaps (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (d n : ℕ) : Prop where
  diffsEval : DiffsEvalP D Fl
  mainOfPolys : MainOfPolysP D Fl
  cvecOk : CvecOkP D
  diffsFlock : DiffsFlockP D Fl
  degBound : DegBoundP D Fl d
  relCount : RelCountP D Fl n

/-! ## Proved fields -/

/-- The number of constraints, any `C1` (the list's shape does not depend on the stack). -/
noncomputable def ncvOf (S : Shape) : ℕ := (constraintsP S (fun _ ↦ 0) []).length + 1

theorem length_filterMap_map {α β γ : Type} (l : List α) (o : α → Option β) (g : α → β → γ) :
    (l.filterMap fun x ↦ (o x).map (g x)).length = (l.filterMap o).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    cases o a <;> simp [ih]

theorem length_constraintsP (S : Shape) (c : Stk) (pw : List E) :
    (constraintsP S c pw).length = (constraintsP S (fun _ ↦ 0) []).length := by
  unfold constraintsP linesP tableConstraintsP
  generalize tables = ts
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_zip, linesOf,
    List.length_cons, List.length_nil, List.length_range]
  refine congrArg (· + _) (congrArg List.sum (List.map_congr_left fun tab _ ↦ ?_))
  split_ifs <;> simp [length_filterMap_map]

theorem cvecOf_len (D : Deployment) (s : USt) (c : Stk) (x : ℕ) :
    (cvecOf D c s x).length ≤ ncvOf D.shape := by
  unfold cvecOf ncvOf
  split_ifs
  · rw [List.length_map, length_constraintsP]; omega
  · simp

/-- Each heap block's leaves read off `C1` has the block's size. -/
theorem blockK_r (D : Deployment) (c : Stk) (rows : List ℕ) (b : Block) :
    (blockK D c rows b).r = b.r := by
  unfold blockK
  cases b.leaves <;> rfl

/-- **The heap read off `C1` is well formed** (`HeapGood`: the blocks fill the leaves). -/
theorem hdOf_wf (D : Deployment) (hH : HeapGood D.shape) (c : Stk) (s : USt) :
    (hdOf D c s).WellFormed := by
  refine ⟨hH.1, ?_⟩
  show Heap.total (D.shape.heap.blocks.map (blockK D c s.2)) = 2 ^ (D.shape.heap.h - 1)
  unfold Heap.total
  rw [List.map_map]
  rw [← hH.2.2.1]
  congr 1
  refine List.map_congr_left fun b _ ↦ ?_
  simp [blockK_r]

theorem diffsOf_count (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (s : USt) (c1 : Stk) (ch : List E)
    (fd : Done) (c2 : Stk) (t : E) (vals : List E) : (diffsOf D Fl s c1 ch fd c2 t vals).length ≤ 4 := by
  unfold diffsOf
  split_ifs <;> simp [commitments]

theorem diffsOf_len (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (n : ℕ) (hn : RelCountP D Fl n)
    (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E) (vals : List E) :
    ∀ d ∈ diffsOf D Fl s c1 ch fd c2 t vals, d.length ≤ max n 1 := by
  intro d hd
  unfold diffsOf at hd
  split_ifs at hd
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hd
    rcases hd with ⟨c, _, rfl⟩ | rfl
    · rw [List.length_map]
      exact (List.length_filter_le _ _).trans ((hn s ch fd t vals).trans (le_max_left _ _))
    · simp
  · simp only [List.mem_singleton] at hd
    subst hd
    simp

/-- **The pending matrices' difference gives their claim** (`diffs_pending`). -/
theorem pending_of_diffs (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (s : USt) (c1 : Stk)
    (ch : List E) (fd : Done) (c2 : Stk) (t : E) (vals : List E)
    (h : ∀ d ∈ diffsOf D Fl s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) :
    PendingHolds (Fl.prog.out fd []).2.2 := by
  unfold diffsOf at h
  split_ifs at h with hg
  · have h0 := h _ (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
      (pendDiff (Fl.prog.out fd []).2.2 (batchVars D.shape)) (List.mem_singleton_self _)
    set p := (Fl.prog.out fd []).2.2
    have hr : p.rounds ≤ batchVars D.shape := hg.2.2.2
    unfold PendingHolds
    unfold pendDiff at h0
    have hsum : ∑ u ∈ range (2 ^ batchVars D.shape), Pending.Gext p u * Pending.Llift p u =
        ∑ u ∈ range (2 ^ p.rounds), Pending.G p u * Pending.L p u := by
      have hle : 2 ^ p.rounds ≤ 2 ^ batchVars D.shape := Nat.pow_le_pow_right (by norm_num) hr
      rw [← Finset.sum_range_add_sum_Ico _ hle]
      have hz : ∑ u ∈ Ico (2 ^ p.rounds) (2 ^ batchVars D.shape),
          Pending.Gext p u * Pending.Llift p u = 0 :=
        Finset.sum_eq_zero fun u hu ↦ by
          rw [Finset.mem_Ico] at hu
          simp [Pending.Gext, show ¬ u < 2 ^ p.rounds by omega]
      rw [hz, add_zero]
      refine Finset.sum_congr rfl fun u hu ↦ ?_
      rw [Finset.mem_range] at hu
      simp [Pending.Gext, Pending.Llift, hu, Nat.mod_eq_of_lt hu]
    rw [hsum] at h0
    exact (CharTwo.add_eq_zero.mp h0).symm
  · exact absurd (h [1] (by simp) 1 (by simp)) one_ne_zero

theorem prodOf_vars (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (s : USt) (c1 : Stk) (ch : List E)
    (fd : Done) (c2 : Stk) (t : E) (vals : List E) (ρ l : E) :
    (prodOf D Fl s c1 ch fd c2 t vals ρ l).vars = batchVars D.shape := by
  unfold prodOf
  split_ifs <;> rfl

/-! ## The models -/

/-- The values the stream sends at `t`: each table's sent columns and sent fingerprints, then the
memory's three, the bytecode's two, `T(t)`, `Q_W(t)` (as `tablePartOf` reads them). -/
def nVOf (S : Shape) : ℕ :=
  (tablesPart S #[] 0 [] tables (List.replicate 4096 0)).2.2.length |> fun left ↦ 4096 - left + 7

/-- **The bus model** of the deployment `D` (`κ` its `BLAKE2S` height). -/
noncomputable def busModelOf (D : Deployment) (N : ℕ) (h : IdsHyps D N) (hc : CvecOkP D) :
    BusModel D (D.shape.heights.getD opBlake2s 0) where
  hd s c := hdOf D c s
  wf s c := hdOf_wf D h.heapGood c s
  Copies s c := CopiesOf D c s
  realizes s c hcp := h.lvRealizes s c hcp
  N := N
  hpush s c hcp := (h.lvBusCount s.2 hcp.1).1
  hpull s c hcp := (h.lvBusCount s.2 hcp.1).2
  nrows := 2 ^ D.shape.constraintVars
  cvec s c x := cvecOf D c s x
  ncv := ncvOf D.shape
  cvec_len s c x := cvecOf_len D s c x
  cvec_ok s c hall := by
    obtain ⟨hfit, hrow⟩ := hc s c hall
    obtain ⟨hcv, hcn, hpl⟩ := h.lvConstraints s c hfit hrow
    exact ⟨hcv, hcn, hpl, hfit, hrow.copies⟩
  qf c := qfOf D c (D.shape.heights.getD opBlake2s 0)
  aux_of_flock s c hf := h.lvAux s c hf

/-- **The identity model** of the deployment `D` and Flock's phase `Fl`. -/
noncomputable def idsRestOf (D : Deployment) (N : ℕ) (h : IdsHyps D N)
    (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (d n : ℕ) (g : IdsGaps D Fl d n) :
    UniIdsRest D Fl (busModelOf D N h g.cvecOk) where
  nV := nVOf D.shape
  V := batchVars D.shape
  polys := polysOf D Fl
  degSum := d
  deg_le := g.degBound
  main_of_polys s c1 ch fd c2 hP := g.mainOfPolys s c1 ch fd c2 hP
  diffs := diffsOf D Fl
  nRel := max n 1
  diffs_len := diffsOf_len D Fl n g.relCount
  diffs_count := diffsOf_count D Fl
  diffs_eval := g.diffsEval
  diffs_flock := g.diffsFlock
  diffs_pending := pending_of_diffs D Fl
  prod := prodOf D Fl
  prod_vars := prodOf_vars D Fl
  target := targetOf D Fl
  batch_start := batch_start_of D Fl h.weightAtLinear h.combineEq

/-- **Knowledge soundness with the bus and identity models constructed** (`uniKnowledgeSoundness_bus`
at `busModelOf`, `idsRestOf`): under the Flock hypothesis `hFlock`, the bridges `h`, the reductions `g`,
the code-level links `C`, `hFin`, the Fiat–Shamir layer `hFs`, and the numbers. -/
theorem uniKnowledgeSoundness_ids (D : Deployment) (N : ℕ) (h : IdsHyps D N)
    (hFlock : FlockSound (D.shape.heights.getD opBlake2s 0)) (d n : ℕ) (g : IdsGaps D hFlock d n)
    (C : UniCode D hFlock (nVOf D.shape) (batchVars D.shape))
    (hFin : UniFinal D hFlock
      (UniIds.ofBus hFlock (busModelOf D N h g.cvecOk) (idsRestOf D N h hFlock d n g)) C)
    (hFs : FsLayer D hFlock (nVOf D.shape) (batchVars D.shape) C)
    (hB : 4 * N + ncvOf D.shape ≤ 2 ^ 32)
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : d ≤ 2 ^ 32) (hrel : max n 1 + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_bus hFlock (busModelOf D N h g.cvecOk) (idsRestOf D N h hFlock d n g) C hFin hFs
    hB hFl hdeg hrel

end UniSound.Ids
