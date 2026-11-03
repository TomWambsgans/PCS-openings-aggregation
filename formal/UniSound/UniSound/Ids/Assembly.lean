-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.MainOk
import UniSound.Ids.FlockEnd
import UniSound.Ids.Deployed
import UniSound.Ids.LvLink
import UniSound.Ids.LvRealize

/-!
# `B` and `J` for the reference deployment

For a deployment `D` at the reference shape (`UniStatement.reference`: 1,000 signatures, heights
`18 18 18 18 17 18`, memory `2^21`, bytecode `2^19`), **`busModelRef`** and **`idsRestRef`** are
`BusModel D 18`-style and `UniIdsRest` models with every bridge of `Bridges.lean` proved but those in
**`IdsRemaining`**: the relations at `t` give the identities at `t` (`DiffsEvalP`), the identities'
degrees and the relations' number (`DegBoundP`, `RelCountP`), and a few facts of the verifier's
definitions (`TowerWeight`, `ZActZero`, `EqKernelLagrange`, `GpowInK`, `TablesFacts`, the absent columns,
the setup's bytecode tuple at the points `BcTupleEval`). **`uniKnowledgeSoundness_ref`** is the end
theorem with them.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

/-- A stack's variables are at most the batch's. -/
theorem layoutVars_le (S : Shape) (c : Commitment) : (layoutOf S c).vars ≤ batchVars S := by
  unfold layoutOf batchVars
  cases h : (layoutsOf S).find? (·.1 == c) with
  | none => simp
  | some p =>
    simp only [Option.map_some, Option.getD_some]
    exact le_foldl_max _ 0 _ (Or.inl (List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some h, rfl⟩))

/-- **What remains** (named hypotheses not proved in this library). -/
structure IdsRemaining (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (d n : ℕ) : Prop where
  diffsEval : DiffsEvalP D Fl
  degBound : DegBoundP D Fl d
  relCount : RelCountP D Fl n
  towerWeight : TowerWeight
  zAct : ZActZero
  eqk : EqKernelLagrange
  gpowK : GpowInK
  tablesF : TablesFacts
  absent : ∀ o < 6, ∀ i, (tables.getD o default).width ≤ i →
    (layoutOf D.shape .c1).limbs (.table o i) = []
  bcTuple : BcTupleEval D

section Ref

variable (D : Deployment) (hS : D.shape = reference)

include hS in
theorem c1Reading_ref : C1Reading D where
  beta := betaCantor
  functionals := by rw [hS, reference_eq]; exact functionalsCorrect18
  limbs := c1Limbs _
  aligned := layoutAligned_new _
  vars := layoutVars_le _ _
  rW := by rw [hS, reference_eq]; decide

include hS in
theorem heapReading_ref {κ : ℕ} (Fl : FlockSound κ) (d n : ℕ) (g : IdsRemaining D Fl d n) :
    HeapReading D where
  c1 := c1Reading_ref D hS
  absent := g.absent
  heap := by rw [hS]; exact heapGood_reference
  zAct := g.zAct
  eqk := g.eqk
  gpowK := g.gpowK
  tablesF := g.tablesF
  setupLimbs := setupLimbs _
  setupAligned := layoutAligned_new _
  setupVars := layoutVars_le _ _
  hB2 := by rw [hS, reference_eq]; decide
  heightsLt := by rw [hS, reference_eq]; decide
  bcTuple := g.bcTuple

include hS in
/-- **The bridges, proved at the reference shape.** -/
theorem idsHyps_ref : IdsHyps D (busBound D.shape) where
  weightAtLinear := weightAtLinear
  combineEq := combineEq
  lvRealizes := lvRealizes D (lvReadBack D) basisValueInv (c1Limbs _) (by rw [hS]; exact heapGood_reference)
  lvConstraints := lvConstraints D
  lvAux := lvAux D (c1Limbs _)
  lvBusCount := lvBusCount D
  heapGood := by rw [hS]; exact heapGood_reference

include hS in
/-- **The reductions, proved from what remains.** -/
theorem idsGaps_ref (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (d n : ℕ)
    (g : IdsRemaining D Fl d n) : IdsGaps D Fl d n where
  diffsEval := g.diffsEval
  mainOfPolys := mainOfPolys D Fl (heapReading_ref D hS Fl d n g)
  cvecOk := cvecOk D (c1Reading_ref D hS)
  diffsFlock := diffsFlock D Fl (c1Reading_ref D hS) g.towerWeight
  degBound := g.degBound
  relCount := g.relCount

/-- **The bus model of the reference deployment.** -/
noncomputable def busModelRef : BusModel D (D.shape.heights.getD opBlake2s 0) :=
  busModelOf D (busBound D.shape) (idsHyps_ref D hS) (cvecOk D (c1Reading_ref D hS))

/-- **The identity model of the reference deployment**, from what remains. -/
noncomputable def idsRestRef (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (d n : ℕ)
    (g : IdsRemaining D Fl d n) : UniIdsRest D Fl (busModelRef D hS) :=
  idsRestOf D (busBound D.shape) (idsHyps_ref D hS) Fl d n (idsGaps_ref D hS Fl d n g)

end Ref

/-- **Knowledge soundness at the reference shape**, with `B` and `J` constructed: under the Flock
hypothesis, what remains (`IdsRemaining`), the code-level links, the Fiat–Shamir layer, and the numbers. -/
theorem uniKnowledgeSoundness_ref (D : Deployment) (hS : D.shape = reference)
    (hFlock : FlockSound (D.shape.heights.getD opBlake2s 0)) (d n : ℕ) (g : IdsRemaining D hFlock d n)
    (C : UniCode D hFlock (nVOf D.shape) (batchVars D.shape))
    (hFin : UniFinal D hFlock (UniIds.ofBus hFlock (busModelRef D hS) (idsRestRef D hS hFlock d n g)) C)
    (hFs : FsLayer D hFlock (nVOf D.shape) (batchVars D.shape) C)
    (hncv : ncvOf D.shape ≤ 100)
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : d ≤ 2 ^ 32) (hrel : max n 1 + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_bus hFlock (busModelRef D hS) (idsRestRef D hS hFlock d n g) C hFin hFs
    (by
      have := busBound_reference
      show 4 * busBound D.shape + ncvOf D.shape ≤ 2 ^ 32
      rw [hS] at hncv ⊢
      omega)
    hFl hdeg hrel

end UniSound.Ids

/-- info: 'UniSound.Ids.uniKnowledgeSoundness_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.uniKnowledgeSoundness_ref

/-- info: 'UniSound.Ids.mainOfPolys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.mainOfPolys

/-- info: 'UniSound.Ids.cvecOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.cvecOk

/-- info: 'UniSound.Ids.diffsFlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.diffsFlock

/-- info: 'UniSound.Ids.batch_start_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.batch_start_of
