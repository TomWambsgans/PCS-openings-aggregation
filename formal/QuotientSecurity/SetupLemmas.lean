-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/SetupLemmas.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Setup
import QuotientSecurity.ConcreteZK
import QuotientSecurity.Notation

/-!
# Between the statements and the theorems they rest on

Plumbing for `Statement.lean`: the relation on cells indexed by bits is the model's, the bounds
are the fractions written there, and the honest prover's messages fit their tables.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp Polynomial Module NNReal

namespace QuotientSecurity

namespace Instance

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] (I : Instance F)

/-- The cells, by their bits. -/
noncomputable def cellEquiv : (Fin (20 + 2) → Bool) ≃ I.params.T × Fin 4 :=
  cantorCells (n := 20) I.basis le22

theorem cellsOf_eq (g : Fin 4 → F[X]) (x : Fin (20 + 2) → Bool) :
    I.cellsOf g x = I.params.cells g (I.cellEquiv x) := by
  have h := Params.cellPoly_zero_eval_pt I.params g (I.cellEquiv x)
  have hp : I.params.pt (I.cellEquiv x) = I.basis.point x :=
    cantorCells_point (n := 20) I.basis le22 x
  rw [← h, hp]
  unfold cellsOf witnessPoly Params.cellPoly
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [shift]

theorem cells_eq (g : Fin 4 → F[X]) :
    (fun x => I.params.cells g (I.cellEquiv x)) = I.cellsOf g :=
  funext fun x => (I.cellsOf_eq g x).symm

/-- **The model's relation is `Relation`**, on cells indexed by bits. -/
theorem sat_iff (stmt : Fin 8 → F) (w : I.params.T × Fin 4 → F) :
    I.params.Sat stmt w ↔ I.Relation stmt fun x => w (I.cellEquiv x) := by
  set e := I.cellEquiv with he
  have hrow : ∀ (y : Fin 20 → Bool) (c : Fin 4),
      e (cellBits (y, c)) = (cantorRows (n := 20) I.basis le22 y, c) := by
    intro y c
    rw [he]
    show (Equiv.prodCongr _ _) (cellBits.symm (cellBits (y, c))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hσ : ∀ x, I.params.σ (e x) = e (I.wiring x) := fun x => by
    show (e.permCongr I.wiring) (e x) = _
    simp [Equiv.permCongr_apply]
  have hword : ∀ J : Fin 8, I.params.wordSum J w = ∑ x, regionWeight I.c J x * w (e x) :=
    fun J => membershipParams_wordSum I.basis le22 I.wiring _ I.c _ _ J w
  unfold Params.Sat Relation
  refine and_congr ⟨fun h y => ?_, fun h x => ?_⟩ (and_congr ⟨fun h x => ?_, fun h i => ?_⟩
    (forall_congr' fun J => by rw [hword J]))
  · have := h (cantorRows (n := 20) I.basis le22 y)
    simp only [hrow]
    exact this
  · obtain ⟨y, rfl⟩ := (cantorRows (n := 20) I.basis le22).surjective x
    have := h y
    simp only [hrow] at this
    exact this
  · have := h (e x)
    rwa [hσ x] at this
  · obtain ⟨x, rfl⟩ := e.surjective i
    rw [hσ x]
    exact h x

theorem sat_of_relation (stmt : Fin 8 → F) (g : Fin 4 → F[X])
    (h : I.Relation stmt (I.cellsOf g)) : I.params.Sat stmt (I.params.cells g) :=
  (I.sat_iff stmt _).mpr ((I.cells_eq g).symm ▸ h)

theorem relation_of_sat (stmt : Fin 8 → F) (g : Fin 4 → F[X])
    (h : I.params.Sat stmt (I.params.cells g)) : I.Relation stmt (I.cellsOf g) :=
  (I.cells_eq g) ▸ (I.sat_iff stmt _).mp h

theorem pub_hPub : ∀ (γ : F) (w : (Fin (20 + 2) → Bool) → F),
    ∑ x, (pubProd (invSeq I.basis.β) (regionMu I.c) 11 (20 + 2) γ).eval (I.basis.point x) * w x
      = ∑ J : Fin 8, γ ^ (J : ℕ) * weightedSum (regionWeight I.c J) w :=
  membershipPub_hPub I.basis (invSeq I.basis.β) I.c le22 (invSeq_zero _)
    fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd

theorem exact : I.params.Exact := Params.ofCantor_exact I.basis le22 I.wiring 8 _ _ I.pub_hPub

theorem nCells : I.params.nCells = 2 ^ 22 :=
  Params.ofCantor_nCells I.basis le22 I.wiring 8 _ _ I.pub_hPub

end Instance

namespace Params

variable {F : Type} [Field F] [DecidableEq F] (P : Params F)

/-- The degree of the honest copy quotient, for parameters and a first message of given
degrees. Stated for any parameters, so nothing of an instance is unfolded. -/
theorem natDegree_honest_le (g : Witness F) (α β γ : F) (c p N : ℕ)
    (hcell : ∀ r, (cellPoly P g r).natDegree ≤ c) (hσ : P.sigmaPoly.natDegree ≤ N)
    (hpub : (P.pub γ).natDegree ≤ p) (hmon : P.vCells.Monic) (hdeg : P.vCells.natDegree = N)
    (hNc : N ≤ c) (hc1 : 1 ≤ c)
    (hh : (Lagrange.interpolate Finset.univ P.pt (sumValue P g α β γ)).natDegree ≤ N) :
    (honest P g α β γ).q.natDegree ≤ p + 3 * c - N ∧ True := by
  have hD : (dPoly P g α β).natDegree ≤ c := by
    unfold dPoly
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ (hcell 0)) ?_
    · rw [natDegree_C]; exact Nat.zero_le _
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans hc1)
  have hD' : (dNextPoly P g α β).natDegree ≤ c := by
    unfold dNextPoly
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ (hcell 0)) ?_
    · rw [natDegree_C]; exact Nat.zero_le _
    · exact (natDegree_C_mul_le _ _).trans (hσ.trans hNc)
  have hDD : (dPoly P g α β * dNextPoly P g α β).natDegree ≤ 2 * c :=
    natDegree_mul_le.trans (by omega)
  have hcopy : (copyPoly P g α β γ).natDegree ≤ p + 3 * c := by
    unfold copyPoly
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by omega) (by omega)) ?_
    refine natDegree_mul_le.trans ?_
    have := natDegree_mul_le (p := P.pub γ) (q := cellPoly P g 0)
    have h0 := hcell 0
    omega
  have hnum : (dPoly P g α β * dNextPoly P g α β
      * Lagrange.interpolate Finset.univ P.pt (sumValue P g α β γ)
      + copyPoly P g α β γ).natDegree ≤ p + 3 * c :=
    natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by omega)) hcopy
  refine ⟨?_, trivial⟩
  show (_ / P.vCells).natDegree ≤ _
  rw [← divByMonic_eq_div _ hmon, natDegree_divByMonic _ hmon, hdeg]
  omega

theorem natDegree_honest_qGate_le (g : Witness F) (α β γ : F) (hmon : P.vRows.Monic) :
    (honest P g α β γ).qGate.natDegree ≤ (gatePoly P g).natDegree - P.vRows.natDegree := by
  show (_ / P.vRows).natDegree ≤ _
  rw [← divByMonic_eq_div _ hmon, natDegree_divByMonic _ hmon]

end Params

namespace Instance

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] (I : Instance F)

/-- **The honest second message fits its table.** For a first message of degree at most
`2^20 + 2`, which a masked witness has, the honest prover's five polynomials have degree at most
`2^24`. -/
theorem honest_legal (g : Fin 4 → F[X]) (hg : ∀ j, (g j).natDegree ≤ 2 ^ 20 + 2) (α β γ : F) :
    (Params.honest I.params g α β γ).h₀.natDegree ≤ 2 ^ 24 ∧
      (Params.honest I.params g α β γ).hHigh.natDegree ≤ 2 ^ 24 ∧
      (Params.honest I.params g α β γ).q.natDegree ≤ 2 ^ 24 ∧
      (Params.honest I.params g α β γ).qGate.natDegree ≤ 2 ^ 24 ∧
      (Params.honest I.params g α β γ).junk.natDegree ≤ 2 ^ 24 := by
  classical
  -- The same bounds, with the first message's own degree.
  let B' : I.params.Bounds := { I.bounds with witness := 2 ^ 20 + 2 }
  let gm : B'.Msg₁ := ⟨g, hg⟩
  have hcell : ∀ c, (Params.cellPoly I.params g c).natDegree ≤ 4194315 := fun c =>
    (Params.natDegree_cellPoly_le B' gm c).trans (by
      show 3 + (2 ^ 20 + 2) * 4 ≤ 4194315
      norm_num)
  have hgate : (Params.gatePoly I.params g).natDegree ≤ 16777260 :=
    (Params.natDegree_gatePoly_le B' gm).trans (by
      show 4 * (3 + (2 ^ 20 + 2) * 4) ≤ 16777260
      norm_num)
  have hσ : I.params.sigmaPoly.natDegree ≤ 4194304 := I.bounds.hSigma.trans (by
    show 2 ^ (20 + 2) ≤ 4194304
    norm_num)
  have hpub : (I.params.pub γ).natDegree ≤ 4203520 := (I.bounds.hPub γ).trans (by
    show 2 ^ 22 + 9 * 2 ^ 10 ≤ 4203520
    norm_num)
  have hE := I.exact
  have hcmon : I.params.vCells.Monic := (digitPoly_monic_natDegree (20 + 2)).1
  have hcdeg : I.params.vCells.natDegree = 4194304 :=
    (digitPoly_monic_natDegree (F := F) (20 + 2)).2.trans (by norm_num)
  have hrmon : I.params.vRows.Monic := by
    rw [hE.rows]; exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hrdeg : I.params.vRows.natDegree = 1048576 := by
    rw [hE.rows, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    exact (card_cantorT (n := 20) I.basis le22).trans (by norm_num)
  have hh : (Lagrange.interpolate Finset.univ I.params.pt
      (Params.sumValue I.params g α β γ)).natDegree ≤ 4194304 := by
    refine natDegree_le_of_degree_le (le_of_lt (lt_of_lt_of_eq
      (Lagrange.degree_interpolate_lt _ I.params.pt_injective.injOn) ?_))
    rw [Finset.card_univ]
    exact_mod_cast I.nCells.trans (by norm_num)
  have hall := Params.natDegree_honest_le I.params g α β γ 4194315 4203520 4194304 hcell hσ hpub
    hcmon hcdeg (by norm_num) (by norm_num) hh
  refine ⟨hh.trans (by norm_num), by simp [Params.honest], hall.1.trans (by norm_num), ?_,
    by simp [Params.honest]⟩
  refine (Params.natDegree_honest_qGate_le I.params g α β γ hrmon).trans ?_
  rw [hrdeg]
  exact (Nat.sub_le_sub_right hgate _).trans (by norm_num)

end Instance

theorem bound_eq (Q : ℕ) :
    ((Q + 3 : ℕ) : ENNReal) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0) : ENNReal)
      = (Q + 3 : ENNReal) / 2 ^ 128 := by
  rw [ENNReal.coe_div (by positivity)]
  simp [div_eq_mul_inv]

theorem coe_bit : (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0) : ENNReal) = 1 / 2 ^ 128 := by
  rw [ENNReal.coe_div (by positivity)]
  simp

namespace Instance

section Experiments

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
variable [CharP K 2] [Fintype K] [DecidableEq K] [FiniteDimensional K E]
variable [SampleableType K] [SampleableType E]
variable {H : Type} [SampleableType H] [Fintype H] [DecidableEq H]
variable (I : Instance E)

/-- The mask's polynomial vanishes on the rows. -/
theorem mask_vanishes (x : I.params.T) :
    aeval (rowPoly.eval (x : E)) (digitPoly 20 : K[X]) = 0 := by
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp x.2
  rw [← eval_map_algebraMap, digitPoly_map, digitPoly_eval, rowPoly_eval,
    ← Function.iterate_add_apply, ← hy]
  exact I.basis.iterate_point le22 _

theorem zkBound_le (hq : Fintype.card E = 2 ^ 192) (U : Finset H) :
    zkBound I.params (digitPoly 20 : K[X]) U ≤ 1 / 2 ^ 128 + U.card / Fintype.card H := by
  have he : zkError I.params (digitPoly 20 : K[X]) ≤ 1 / 2 ^ 128 :=
    zkError_le hq I.nCells _ (digitPoly_monic_natDegree 20).2.le
  unfold zkBound
  rw [← coe_bit]
  exact add_le_add_left (ENNReal.coe_le_coe.mpr he) _

theorem real_event (c₀ : I.Table H) (stmt : Fin 8 → E) (gK : Fin 4 → K[X])
    (S : I.View H → Prop) :
    Pr{let o ← I.real c₀ stmt gK}[S o] = Pr{let x ← realNI c₀ stmt gK (digitPoly 20)}[S x] :=
  rfl

theorem sim_event (c₀ : I.Table H) (stmt : Fin 8 → E) (S : I.View H → Prop) :
    Pr{let o ← I.sim K c₀ stmt}[S o] = Pr{let x ← simNI (K := K) c₀ stmt}[S x] :=
  rfl

/-- A witness's cells are those of its commitment with no mask. -/
theorem witnessCells_eq (gK : Fin 4 → K[X]) :
    I.witnessCells gK = I.cellsOf (committed gK (digitPoly 20) 0) := by
  unfold witnessCells
  congr 1
  funext j
  simp [committed, maskPoly]

end Experiments

end Instance

end QuotientSecurity
