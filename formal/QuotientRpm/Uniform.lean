-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientRpm.Chain
import QuotientRpm.FreshBad

/-!
# Uniform cells and uniform challenges

* `prEvent_cell`, `prEvent_three_cells`: in a uniform table, the answer at a cell is uniform, and
  so are the answers along a path of three distinct cells, each cell chosen from the answer at the
  one before (the first challenge's three hashes: the state after the root gives `α`, its hash `β`,
  that one's hash `γ`).
* `prEvent_uniform_balanced`: a map whose fibres all have one size sends the uniform distribution
  to the uniform one; so **the low 192 bits of a uniform 256-bit state are uniform**
  (`prEvent_chal`, `prEvent_chal₃`), every limb triple having `256^8` states (`stateLimbs_fiber`).
* `prob_first_chain`, `prob_second_chain`, `prob_third_chain`: the round errors of
  `RoundByRound.lean`, for challenges read off uniform states.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace QuotientRpm

/-! ## Draws one after the other -/

/-- An event after a draw, bounded draw by draw. -/
theorem prEvent_bind_mono' {α : Type} (mx : ProbComp α) (X Y : α → ProbComp Prop)
    (h : ∀ a, prEvent (X a) ≤ prEvent (Y a)) : prEvent (mx >>= X) ≤ prEvent (mx >>= Y) := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  exact MeasureTheory.lintegral_mono h

/-! ## Cells of a uniform table -/

section Table

variable {D Rg : Type} [DecidableEq D] [Fintype D] [SampleableType Rg] [SampleableType (D → Rg)]

/-- **The answer at a cell of a uniform table is uniform.** -/
theorem prEvent_cell (t : D) (p : Rg → Prop) :
    Pr{let g ← $ᵗ (D → Rg)}[p (g t)] ≤ Pr{let u ← $ᵗ Rg}[p u] := by
  rw [prEvent_uniformTable_update (R := fun _ => Rg) t (fun g => p (g t))]
  have h : ∀ u : Rg, prEvent ((fun g : D → Rg => p (Function.update g t u t)) <$> ($ᵗ (D → Rg))) ≤
      prEvent (pure (p u) : ProbComp Prop) := by
    intro u
    simp only [Function.update_self]
    classical
    by_cases hp : p u
    · rw [prEvent_pure_prop]
      simp only [hp, ite_true]
      exact prEvent_le_one _
    · rw [prEvent_const_of_not _ hp]
      simp
  refine (prEvent_bind_mono' _ _ _ h).trans (le_of_eq ?_)
  simp only [bind_pure_comp]

/-- **Three cells along a path.** The answers at `t`, at the cell `f` names from it, and at the
cell `f` names from that, all distinct, are three uniform draws. -/
theorem prEvent_three_cells (t : D) (f : Rg → D) (Q : Rg → Rg → Rg → Prop) :
    Pr{let g ← $ᵗ (D → Rg)}[f (g t) ≠ t ∧ f (g (f (g t))) ≠ t ∧ f (g (f (g t))) ≠ f (g t) ∧
      Q (g t) (g (f (g t))) (g (f (g (f (g t)))))] ≤
    Pr{let a ← $ᵗ Rg; let b ← $ᵗ Rg; let d ← $ᵗ Rg}[Q a b d] := by
  rw [prEvent_uniformTable_update (R := fun _ => Rg) t]
  refine prEvent_bind_mono' _ _ _ fun a => ?_
  -- The answer at `t` is `a`; the next two cells are not `t`.
  refine (prEvent_mono _ _ (fun g => f a ≠ t ∧ f (g (f a)) ≠ t ∧ f (g (f a)) ≠ f a ∧
      Q a (g (f a)) (g (f (g (f a))))) fun g h => ?_).trans ?_
  · simp only [Function.update_self] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [Function.update_of_ne h1] at h2 h3 h4
    rw [Function.update_of_ne h2] at h4
    exact ⟨h1, h2, h3, h4⟩
  classical
  by_cases ha : f a = t
  · rw [prEvent_eq_zero_of_forall_not _ _ fun g h => h.1 ha]
    simp
  rw [prEvent_uniformTable_update (R := fun _ => Rg) (f a)]
  refine prEvent_bind_mono' _ _ _ fun b => ?_
  refine (prEvent_mono _ _ (fun g => Q a b (g (f b))) fun g h => ?_).trans ?_
  · simp only [Function.update_self] at h
    obtain ⟨-, -, h3, h4⟩ := h
    rwa [Function.update_of_ne h3] at h4
  exact prEvent_cell (f b) (Q a b)

end Table

/-! ## Uniform maps -/

/-- **A map whose fibres all have one size sends the uniform distribution to the uniform one.** -/
theorem prEvent_uniform_balanced {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [DecidableEq Y]
    [SampleableType X] [SampleableType Y] (φ : X → Y) (k : ℕ)
    (hk : ∀ y, (Finset.univ.filter fun x => φ x = y).card = k) (p : Y → Prop) [DecidablePred p] :
    Pr{let x ← $ᵗ X}[p (φ x)] = Pr{let y ← $ᵗ Y}[p y] := by
  rw [SampleableType.prEvent_uniformSample (fun x => p (φ x)),
    SampleableType.prEvent_uniformSample p]
  have hX : Fintype.card X = k * Fintype.card Y := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp [hk, Finset.sum_const, Finset.card_univ, mul_comm]
  have hP : (Finset.univ.filter fun x => p (φ x)).card = k * (Finset.univ.filter p).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ.filter p)
      (fun x hx => by simpa using hx)]
    rw [Finset.sum_congr rfl (g := fun _ => k), Finset.sum_const, smul_eq_mul, mul_comm]
    intro y hy
    rw [← hk y, Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr fun x _ => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hy, h⟩
  have hk0 : k ≠ 0 := by
    intro h0
    have := Fintype.card_pos (α := X)
    rw [hX, h0, zero_mul] at this
    exact lt_irrefl 0 this
  rw [hX, hP, Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_left _ _ (by exact_mod_cast hk0) (ENNReal.natCast_ne_top k)

/-- The fibres of a product of maps are the products of their fibres. -/
theorem card_fiber_prod {X Y X' Y' : Type} [Fintype X] [Fintype X'] [DecidableEq Y] [DecidableEq Y']
    (φ : X → Y) (ψ : X' → Y') (k k' : ℕ) (hφ : ∀ y, (Finset.univ.filter fun x => φ x = y).card = k)
    (hψ : ∀ y, (Finset.univ.filter fun x => ψ x = y).card = k') (y : Y × Y') :
    (Finset.univ.filter fun x : X × X' => (φ x.1, ψ x.2) = y).card = k * k' := by
  have h : (Finset.univ.filter fun x : X × X' => (φ x.1, ψ x.2) = y) =
      (Finset.univ.filter fun x => φ x = y.1) ×ˢ (Finset.univ.filter fun x => ψ x = y.2) := by
    ext x
    simp [Prod.ext_iff]
  rw [h, Finset.card_product, hφ, hψ]

/-! ## The challenges of uniform states -/

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : QuotientSecurity.Params F} {B : P.Bounds} (W : Wire P B)

theorem chal_fiber (x : F) :
    (Finset.univ.filter fun st : Bytes32 => W.chal st = x).card =
      (Finset.univ : Finset (Vector UInt8 8)).card := by
  have h : (Finset.univ.filter fun st : Bytes32 => W.chal st = x) =
      Finset.univ.filter fun st : Bytes32 => stateLimbs st = W.limbs x :=
    Finset.filter_congr fun st _ => by simp only [Wire.chal, Equiv.symm_apply_eq]
  rw [h]
  exact stateLimbs_fiber (W.limbs x)

/-- **The low 192 bits of a uniform state are uniform.** -/
theorem prEvent_chal (p : F → Prop) :
    Pr{let st ← $ᵗ Bytes32}[p (W.chal st)] = Pr{let x ← $ᵗ F}[p x] := by
  classical
  exact prEvent_uniform_balanced W.chal _ (chal_fiber W) p

/-- The three challenges of three uniform states are uniform. -/
theorem prEvent_chal₃ (p : F × F × F → Prop) :
    Pr{let s ← $ᵗ (Bytes32 × Bytes32 × Bytes32)}[p (W.chal s.1, W.chal s.2.1, W.chal s.2.2)] =
      Pr{let c ← $ᵗ (F × F × F)}[p c] := by
  classical
  have h2 := card_fiber_prod W.chal W.chal _ _ (chal_fiber W) (chal_fiber W)
  have h3 := card_fiber_prod W.chal (fun s : Bytes32 × Bytes32 => (W.chal s.1, W.chal s.2)) _ _
    (chal_fiber W) h2
  exact prEvent_uniform_balanced (fun s : Bytes32 × Bytes32 × Bytes32 =>
    (W.chal s.1, W.chal s.2.1, W.chal s.2.2)) _ h3 p

open QuotientSecurity QuotientSecurity.Params

/-- Three draws, as one draw of a triple. -/
theorem prEvent_three_draws {Rg : Type} [SampleableType Rg] (Q : Rg → Rg → Rg → Prop) :
    Pr{let a ← $ᵗ Rg; let b ← $ᵗ Rg; let d ← $ᵗ Rg}[Q a b d] =
      Pr{let s ← $ᵗ (Rg × Rg × Rg)}[Q s.1 s.2.1 s.2.2] := by
  simp only [SampleableType.uniformSample_prod_eq_bind, bind_assoc, pure_bind,
    map_eq_bind_pure_comp, Function.comp_def]

open Classical in
/-- The first round's error, for the three challenges read off three uniform states. -/
theorem prob_first_chain (stmt : Fin P.words → F) (g : B.Msg₁) :
    Pr{let s ← $ᵗ (Bytes32 × Bytes32 × Bytes32)}[¬ State₁ stmt g ∧
      State₂ stmt g (W.chal s.1, W.chal s.2.1, W.chal s.2.2)] ≤ (roundError P B : ℝ≥0∞) := by
  rw [prEvent_chal₃ W (fun c => ¬ State₁ stmt g ∧ State₂ stmt g c)]
  refine (prob_first P B stmt g).trans ?_
  exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)

open Classical in
/-- The second round's error, for the challenge read off a uniform state. -/
theorem prob_second_chain (stmt : Fin P.words → F) (g : B.Msg₁) (c : F × F × F) (R : B.Msg₂) :
    Pr{let s ← $ᵗ Bytes32}[¬ State₃ stmt g c R ∧ State₄ stmt g c R (W.chal s)] ≤
      (roundError P B : ℝ≥0∞) := by
  rw [prEvent_chal W (fun t => ¬ State₃ stmt g c R ∧ State₄ stmt g c R t)]
  refine (prob_second P B stmt g c R).trans ?_
  exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)

open Classical in
/-- The third round's error, for the challenge read off a uniform state. -/
theorem prob_third_chain (stmt : Fin P.words → F) (g : B.Msg₁) (c : F × F × F) (R : B.Msg₂) (t : F)
    (v : (Fin 4 → F) × F) :
    Pr{let s ← $ᵗ Bytes32}[¬ State₄ stmt g c R t ∧ State₆ stmt g c R t v (W.chal s)] ≤
      (roundError P B : ℝ≥0∞) := by
  rw [prEvent_chal W (fun ρ => ¬ State₄ stmt g c R t ∧ State₆ stmt g c R t v ρ)]
  refine (prob_third P B stmt g c R t v).trans ?_
  exact_mod_cast le_max_right _ _

end QuotientRpm
