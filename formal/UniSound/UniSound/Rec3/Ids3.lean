-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The identity model is `Ids/`'s (the main line's),
-- read at π1-rec3's transcripts; the batch's start follows `Ids/Batch.lean`'s `batch_start_of`.
import UniSound.Ids.Build
import UniSound.Rec3.BusSq
import UniSound.Rec3.Piop3
import FlockSoundUni.Rec3Instance

/-!
# π1-rec3's identity model, from the main line's

**`ids3Of`**: `UniIds3 D F3 np` for π1-rec3's Flock phase `F3 = flockSound3_of tx hw`, from the main line's
identity model `idsRestOf D N h Fl d n g` at Flock's main-line instance `Fl` (`flockSoundInstance κ`), read at
π1-rec3's transcripts:

* round `0`'s three challenges `[c, β, γ]` as the main line's six (`expandCh`: `α = (c, c², c⁴, c⁸)`), the bus's
  error over three draws `BusModel.mainSoundSq` (`16 N / |E|` and the constraints');
* Flock's transcript as the main line's (`expandFd`: the squares' one challenge written out), so that
  `F3.outM fd = Fl.prog.out (expandFd fd) []` (definitionally): the polynomials, the merge polynomial, the relations'
  differences (the pending matrices' among them) are the main line's at the expanded transcript;
* **the batch without the pending term** (`prod3Of`: the three commitments' products; `target3Of`: their values'
  combination), whose start holds when the pending claim is its sum (`batch_start3_of`): the pending difference
  then vanishes (`pendDiff_eq_zero`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset FlockSound.Uni
open scoped ENNReal

section Batch3

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ)

open Classical in
/-- **π1-rec3's batch**: `Σ_{k<3} λ^k W_k C_k` over the batch's variables (the main line's `prodOf` without the
pending matrices' product). -/
noncomputable def prod3Of (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) : ProdSum :=
  if CountsFit D.shape s.2 ∧ FlockGood κ (batchVars D.shape) (Fl.prog.out fd []) then
    { vars := batchVars D.shape
      n := 3
      coef := fun k ↦ l ^ k
      A := fun k u ↦ weightAt (combAt D Fl s ch fd t vals ρ (cm k)) (layoutOf D.shape (cm k))
        (bitsE u (batchVars D.shape)) (ringMapAt Fl fd)
      B := fun k u ↦ stE (stackFor D c1 c2 (cm k)) (layoutOf D.shape (cm k)).vars u }
  else { vars := batchVars D.shape, n := 0, coef := fun _ ↦ 0, A := fun _ _ ↦ 0, B := fun _ _ ↦ 0 }

open Classical in
/-- **π1-rec3's batch's target**: `Σ_{k<3} λ^k v_k`. -/
noncomputable def target3Of (s : USt) (_c1 : Stk) (ch : List E) (fd : Done) (_c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) : E :=
  if CountsFit D.shape s.2 ∧ FlockGood κ (batchVars D.shape) (Fl.prog.out fd []) then
    ∑ k ∈ range 3, l ^ k * (combAt D Fl s ch fd t vals ρ (cm k)).value
  else 1

theorem prod3Of_vars (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E) (vals : List E)
    (ρ l : E) : (prod3Of D Fl s c1 ch fd c2 t vals ρ l).vars = batchVars D.shape := by
  unfold prod3Of
  split_ifs <;> rfl

/-- **The pending difference vanishes when the pending claim is its sum** (the converse of `pending_of_diffs`). -/
theorem pendDiff_eq_zero (p : Flock.Pending) (V : ℕ) (hr : p.rounds ≤ V) (h : PendingHolds p) :
    pendDiff p V = 0 := by
  unfold pendDiff
  have hsum : ∑ u ∈ range (2 ^ V), Pending.Gext p u * Pending.Llift p u =
      ∑ u ∈ range (2 ^ p.rounds), Pending.G p u * Pending.L p u := by
    have hle : 2 ^ p.rounds ≤ 2 ^ V := Nat.pow_le_pow_right (by norm_num) hr
    rw [← Finset.sum_range_add_sum_Ico _ hle]
    have hz : ∑ u ∈ Ico (2 ^ p.rounds) (2 ^ V), Pending.Gext p u * Pending.Llift p u = 0 :=
      Finset.sum_eq_zero fun u hu ↦ by
        rw [Finset.mem_Ico] at hu
        simp [Pending.Gext, show ¬ u < 2 ^ p.rounds by omega]
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    rw [Finset.mem_range] at hu
    simp [Pending.Gext, Pending.Llift, hu, Nat.mod_eq_of_lt hu]
  rw [hsum, ← h]
  exact CharTwo.add_self_eq_zero _

/-- **π1-rec3's batch's start**: with the pending claim its sum, the batch's sum plus its target is the combination
by `λ` of the commitments' combinations by `ρ` of their relations' differences (and of the pending difference, then
zero). -/
theorem batch_start3_of (hW : WeightAtLinear) (hC : CombineEq) (s : USt) (c1 : Stk) (ch : List E) (fd : Done)
    (c2 : Stk) (t : E) (vals : List E) (ρ l : E) (hp : PendingHolds (Fl.prog.out fd []).2.2) :
    (prod3Of D Fl s c1 ch fd c2 t vals ρ l).T [] + target3Of D Fl s c1 ch fd c2 t vals ρ l =
      powComb ((diffsOf D Fl s c1 ch fd c2 t vals).map fun d ↦ powComb d ρ) l := by
  unfold prod3Of target3Of diffsOf
  split_ifs with hg
  · have hz := pendDiff_eq_zero (Fl.prog.out fd []).2.2 (batchVars D.shape) hg.2.2.2 hp
    have h0 := comm_start hW hC (relsAt D Fl s ch fd t vals) .c1 ρ (layoutOf D.shape .c1)
      (ringMapAt Fl fd) (batchVars D.shape) (stackFor D c1 c2 .c1)
    have h1 := comm_start hW hC (relsAt D Fl s ch fd t vals) .c2 ρ (layoutOf D.shape .c2)
      (ringMapAt Fl fd) (batchVars D.shape) (stackFor D c1 c2 .c2)
    have h2 := comm_start hW hC (relsAt D Fl s ch fd t vals) .setup ρ (layoutOf D.shape .setup)
      (ringMapAt Fl fd) (batchVars D.shape) (stackFor D c1 c2 .setup)
    simp only [ProdSum.T, List.length_nil, Nat.sub_zero, foldAll, List.foldl_nil,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, commitments, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, powComb_cons, powComb_nil, mul_zero, add_zero]
    simp only [cm, combAt, commitments, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 ⊢
    rw [hz, ← h0, ← h1, ← h2]
    ring
  · simp [ProdSum.T, powComb_cons, powComb_nil]

end Batch3

section Model

variable (D : Deployment) (N : ℕ) (h : IdsHyps D N) (d n : ℕ)
  (g : IdsGaps D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) d n)
  (tx : Tx (D.shape.heights.getD opBlake2s 0)) (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) (np : ℕ)

/-- **π1-rec3's identity model**, from the main line's at the expanded transcripts. -/
noncomputable def ids3Of (hV : batchVars D.shape = 2 * np + 1) : UniIds3 D (flockSound3_of tx hw) np where
  nV := nVOf D.shape
  qf := (busModelOf D N h g.cvecOk).qf
  MainHolds := MainHoldsOf D
  rel_of := (busModelOf D N h g.cvecOk).rel_of
  MainOK s c ch := (busModelOf D N h g.cvecOk).MainOK s c (expandCh ch)
  errMain := (busModelOf D N h g.cvecOk).errMainSq
  mainSound := (busModelOf D N h g.cvecOk).mainSoundSq
  polys s c1 ch fd c2 := (idsRestOf D N h _ d n g).polys s c1 (expandCh ch)
    (expandFd (D.shape.heights.getD opBlake2s 0) fd) c2
  degSum := d
  deg_le s c1 ch fd c2 := (idsRestOf D N h _ d n g).deg_le s c1 (expandCh ch) _ c2
  main_of_polys s c1 ch fd c2 hP := (idsRestOf D N h _ d n g).main_of_polys s c1 (expandCh ch) _ c2 hP
  zb fd := (idsRestOf D N h _ d n g).zb (expandFd (D.shape.heights.getD opBlake2s 0) fd)
  zb_ne _ := (idsRestOf D N h _ d n g).zb_ne _
  degBad := zBadDeg D.shape
  zb_deg _ := (idsRestOf D N h _ d n g).zb_deg _
  diffs s c1 ch fd c2 t vals := (idsRestOf D N h _ d n g).diffs s c1 (expandCh ch)
    (expandFd (D.shape.heights.getD opBlake2s 0) fd) c2 t vals
  nRel := max n 1
  diffs_len s c1 ch fd c2 t vals := (idsRestOf D N h _ d n g).diffs_len s c1 (expandCh ch) _ c2 t vals
  diffs_count s c1 ch fd c2 t vals := (idsRestOf D N h _ d n g).diffs_count s c1 (expandCh ch) _ c2 t vals
  diffs_eval s c1 ch fd c2 t vals hz := (idsRestOf D N h _ d n g).diffs_eval s c1 (expandCh ch) _ c2 t vals hz
  diffs_flock s c1 ch fd c2 t vals hz := (idsRestOf D N h _ d n g).diffs_flock s c1 (expandCh ch) _ c2 t vals hz
  diffs_pending s c1 ch fd c2 t vals hz :=
    (idsRestOf D N h _ d n g).diffs_pending s c1 (expandCh ch) _ c2 t vals hz
  prod s c1 ch fd c2 t vals ρ l := prod3Of D (flockSoundInstance _) s c1 (expandCh ch)
    (expandFd (D.shape.heights.getD opBlake2s 0) fd) c2 t vals ρ l
  prod_vars s c1 ch fd c2 t vals ρ l := by rw [prod3Of_vars, hV]
  target s c1 ch fd c2 t vals ρ l := target3Of D (flockSoundInstance _) s c1 (expandCh ch)
    (expandFd (D.shape.heights.getD opBlake2s 0) fd) c2 t vals ρ l
  batch_start s c1 ch fd c2 t vals ρ l hp :=
    batch_start3_of D _ h.weightAtLinear h.combineEq s c1 (expandCh ch) _ c2 t vals ρ l hp

end Model

end UniSound.Ids

/-- info: 'UniSound.Ids.ids3Of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.ids3Of

/-- info: 'UniSound.Ids.batch_start3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.batch_start3_of
