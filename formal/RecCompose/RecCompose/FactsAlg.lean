-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.View
import RecCompose.Layers

/-!
# The view's formulas and public terms as `RecPiop`'s values

* the coefficients `adapt` writes are `1`, `Y`, `Y²`, `γ`, `γ Y` and the elements of `K` (`oneC_eval`, …);
* an expression slot's formula is its polynomial (`exprFormula_eval`: `toPoly2`'s `Poly2.eval`), a port's its
  fingerprint (`portFormula_eval`: `fpEval` of `portWeights`), at the powers `1, γ` of `γ`;
* **the public limbs** `pubOfC`: a port's limbs from π2's public scalars, by its source, in the form the verifier's
  term needs at every scalar list (`term_value`) and that the fingerprint determines among limbs in `K`
  (`pub_canon`): the statement's words and a root's halves as `canon2` pairs (`x + Y·x₁, x₁`, which are `x₀, x₁` when
  `x` has no `Y²` limb), an element as its three limbs, a zero check or a padding port as zeros.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Primitives

/-! ## The coefficients -/

theorem eNew_lane (k : K) : UniStatement.eNew (K.lane k) 0 0 = F192.ofF64 k := by
  show F192.ofLimbs k 0 0 = _
  exact (F192.ofF64_eq k).symm

theorem oneC_field : oneC.field = 1 := by
  show F192.ofLimbs 1 0 0 = 1
  exact F192.one_eq.symm

theorem yC_field : yC.field = F192.Y := rfl

theorem y2C_field : y2C.field = F192.Y ^ 2 := by
  show F192.ofLimbs 0 0 1 = _
  rw [F192.ofLimbs_eq]
  simp

theorem gC_field : gC.field = 1 := oneC_field

theorem gyC_field : gyC.field = F192.Y := rfl

theorem kCoeff_eval (k : K) (gs : List E) (hg : gs.getD 0 0 = 1) :
    (kCoeff k).toF.eval gs = F192.ofF64 k := by
  show (kCoeff k).field * gs.getD 0 0 = _
  rw [hg, mul_one]
  exact eNew_lane k

theorem cellLin_eval (c : ℕ) (gs : List E) (hg : gs.getD 0 0 = 1) (cell : ℕ → E) :
    (cellLin c).toF.eval gs cell = cell c := by
  show (0 : E) + oneC.field * gs.getD 0 0 * cell c = cell c
  rw [oneC_field, hg]
  ring

/-! ## The formulas -/

/-- **An expression slot's formula is its polynomial.** -/
theorem exprFormula_eval (p : RecCircuit.Poly) (gs : List E) (hg : gs.getD 0 0 = 1) (cell : ℕ → E) :
    (exprFormula p).toF.eval gs cell = (RecCircuit.toPoly2 p).eval cell := by
  have hlin : (exprFormula p).toF.lin.eval gs cell = (p.linear.map fun t ↦ F192.ofF64 t.2 * cell t.1).sum := by
    show ((p.linear.map fun t ↦ (kCoeff t.2, t.1)).map fun t ↦ (t.1.toF, t.2)).foldl
      (fun acc t ↦ acc + t.1.eval gs * cell t.2) 0 = _
    rw [foldl_add_sum, zero_add, List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t _ ↦ ?_)
    show (kCoeff t.2).toF.eval gs * cell t.1 = _
    rw [kCoeff_eval _ _ hg]
  have hprod : ∀ a : E, ((p.quadratic.map fun t ↦ (kCoeff t.2.2, cellLin t.1, cellLin t.2.1)).map
      fun q ↦ (q.1.toF, q.2.1.toF, q.2.2.toF)).foldl
        (fun acc q ↦ acc + q.1.eval gs * (q.2.1.eval gs cell * q.2.2.eval gs cell)) a =
      a + (p.quadratic.map fun t ↦ F192.ofF64 t.2.2 * (cell t.1 * cell t.2.1)).sum := by
    intro a
    rw [foldl_add_sum, List.map_map, List.map_map]
    refine congrArg (a + ·) (congrArg List.sum (List.map_congr_left fun t _ ↦ ?_))
    show (kCoeff t.2.2).toF.eval gs * ((cellLin t.1).toF.eval gs cell * (cellLin t.2.1).toF.eval gs cell) = _
    rw [kCoeff_eval _ _ hg, cellLin_eval _ _ hg, cellLin_eval _ _ hg]
  show ((p.quadratic.map fun t ↦ (kCoeff t.2.2, cellLin t.1, cellLin t.2.1)).map
      fun q ↦ (q.1.toF, q.2.1.toF, q.2.2.toF)).foldl
        (fun acc q ↦ acc + q.1.eval gs * (q.2.1.eval gs cell * q.2.2.eval gs cell))
        ((exprFormula p).toF.lin.eval gs cell) = _
  rw [hprod, hlin]
  unfold RecPiop.Poly2.eval RecCircuit.toPoly2
  simp only [List.map_map, Function.comp_def, Algebra.algebraMap_self, RingHom.id_apply]

theorem oneC_eval (gs : List E) (hg0 : gs.getD 0 0 = 1) : oneC.toF.eval gs = 1 := by
  show oneC.field * gs.getD 0 0 = 1
  rw [oneC_field, hg0, one_mul]

theorem yC_eval (gs : List E) (hg0 : gs.getD 0 0 = 1) : yC.toF.eval gs = F192.Y := by
  show yC.field * gs.getD 0 0 = _
  rw [yC_field, hg0, mul_one]

theorem y2C_eval (gs : List E) (hg0 : gs.getD 0 0 = 1) : y2C.toF.eval gs = F192.Y ^ 2 := by
  show y2C.field * gs.getD 0 0 = _
  rw [y2C_field, hg0, mul_one]

theorem gC_eval (gs : List E) (γ : E) (hg1 : gs.getD 1 0 = γ) : gC.toF.eval gs = γ := by
  show gC.field * gs.getD 1 0 = _
  rw [gC_field, hg1, one_mul]

theorem gyC_eval (gs : List E) (γ : E) (hg1 : gs.getD 1 0 = γ) : gyC.toF.eval gs = F192.Y * γ := by
  show gyC.field * gs.getD 1 0 = _
  rw [gyC_field, hg1]

/-- A linear formula's value: its terms' sum. -/
theorem linear_eval (ts : List (Coeff × ℕ)) (gs : List E) (cell : ℕ → E) :
    (⟨⟨ts, none⟩, []⟩ : Formula).toF.eval gs cell = (ts.map fun t ↦ t.1.toF.eval gs * cell t.2).sum := by
  show (ts.map fun t ↦ (t.1.toF, t.2)).foldl (fun acc t ↦ acc + t.1.eval gs * cell t.2) 0 = _
  rw [foldl_add_sum, zero_add, List.map_map]
  rfl

/-- **A port's formula is its fingerprint**, at `γ` read from the powers. -/
theorem portFormula_eval (ls : List ℕ) (gs : List E) (γ : E) (hg0 : gs.getD 0 0 = 1) (hg1 : gs.getD 1 0 = γ)
    (cell : ℕ → E) : (portFormula ls).toF.eval gs cell = RecPiop.fpEval (RecCircuit.portWeights ls) γ cell := by
  have hfall : ∀ l : List ℕ, (⟨⟨l.map fun c ↦ (oneC, c), none⟩, []⟩ : Formula).toF.eval gs cell =
      RecPiop.fpEval (l.map fun c ↦ ⟨c, [1]⟩) γ cell := by
    intro l
    rw [linear_eval]
    unfold RecPiop.fpEval
    simp only [List.map_map, Function.comp_def, oneC_eval gs hg0, RecPiop.horner, Algebra.algebraMap_self,
      RingHom.id_apply, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  match ls with
  | [] => exact hfall []
  | [a] => exact hfall [a]
  | [a, b] => exact hfall [a, b]
  | [a, b, d] =>
    show (⟨⟨[(oneC, a), (yC, b), (y2C, d)], none⟩, []⟩ : Formula).toF.eval gs cell = _
    rw [linear_eval]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, oneC_eval gs hg0, yC_eval gs hg0,
      y2C_eval gs hg0]
    simp only [RecPiop.fpEval, RecCircuit.portWeights, RecPiop.horner, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.foldr_cons, List.foldr_nil, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | [a, b, d, e] =>
    show (⟨⟨[(oneC, a), (yC, b), (gC, d), (gyC, e)], none⟩, []⟩ : Formula).toF.eval gs cell = _
    rw [linear_eval]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, oneC_eval gs hg0, yC_eval gs hg0,
      gC_eval gs γ hg1, gyC_eval gs γ hg1]
    simp only [RecPiop.fpEval, RecCircuit.portWeights, RecPiop.horner, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.foldr_cons, List.foldr_nil, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | a :: b :: d :: e :: f :: rest => exact hfall (a :: b :: d :: e :: f :: rest)

/-! ## The public limbs -/

/-- `x` as two limbs of the form `L₀ + Y L₁`: `(x + Y x₁, x₁)`, `x₁` its `Y` limb. -/
def canon2 (x : E) : List E := [x + F192.Y * F192.ofF64 (F192.limb x 1), F192.ofF64 (F192.limb x 1)]

/-- `x`'s three limbs. -/
def limbs3 (x : E) : List E := [F192.ofF64 (F192.limb x 0), F192.ofF64 (F192.limb x 1), F192.ofF64 (F192.limb x 2)]

/-- **Port `j`'s public limbs** of π2's public scalars `pubs`, by its source (`roots` π2's roots count). -/
def pubOfSource (roots : ℕ) (pubs : List E) : RecCircuit.Source → List E
  | .statement => canon2 (pubs.getD 0 0 + F192.Y * pubs.getD 1 0) ++ canon2 (pubs.getD 2 0 + F192.Y * pubs.getD 3 0)
  | .root i => canon2 (pubs.getD (4 + 2 * i + 1) 0) ++ canon2 (pubs.getD (4 + 2 * i) 0)
  | .element i => limbs3 (pubs.getD (4 + 2 * roots + i) 0)
  | .zero | .pad => [0, 0, 0]

/-- **The compiled circuit's public limbs.** -/
def pubOfC (c : RecCircuit.Circuit) (pubs : List E) (j : ℕ) : List E :=
  pubOfSource (publicCounts c).1 pubs (c.ports.getD j default).source

theorem pubOfSource_length (roots : ℕ) (pubs : List E) (s : RecCircuit.Source) :
    (pubOfSource roots pubs s).length = s.limbs := by
  cases s <;> rfl

theorem canon2_fp (x : E) : (canon2 x).getD 0 0 + F192.Y * (canon2 x).getD 1 0 = x := by
  simp only [canon2, List.getD_cons_zero, List.getD_cons_succ]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem limb1_ofF64_add (a b : K) : (F192.ofF64 a + F192.Y * F192.ofF64 b).limb 1 = b := by
  rw [F192.Y_mul_ofF64, F192.ofF64_eq, F192.ofLimbs_add_ofLimbs]
  simp

theorem limb_ofF64_add (a b : K) : (F192.ofF64 a + F192.Y * F192.ofF64 b).limb 0 = a := by
  rw [F192.Y_mul_ofF64, F192.ofF64_eq, F192.ofLimbs_add_ofLimbs]
  simp

/-- **`canon2` of `L₀ + Y L₁`** with `L₀, L₁ ∈ K` is `L₀, L₁`. -/
theorem canon2_ofF64 (a b : K) : canon2 (F192.ofF64 a + F192.Y * F192.ofF64 b) = [F192.ofF64 a, F192.ofF64 b] := by
  unfold canon2
  rw [limb1_ofF64_add]
  congr 1
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem limbs3_fp (x : E) :
    (limbs3 x).getD 0 0 + F192.Y * (limbs3 x).getD 1 0 + F192.Y ^ 2 * (limbs3 x).getD 2 0 = x := by
  simp only [limbs3, List.getD_cons_zero, List.getD_cons_succ]
  conv_rhs => rw [← F192.ofLimbs_limb x, F192.ofLimbs_eq]
  ring

end RecCompose
