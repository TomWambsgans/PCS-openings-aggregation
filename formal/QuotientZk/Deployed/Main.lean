-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.RowEntropy
import QuotientZk.Deployed.Bound

/-!
# Zero knowledge of the deployed proof, in the random-oracle model

`zk_rom` for the deployed prover: the skeleton `skel sh` of `Skeleton.lean` (the reduction's
Keccak-256 chain, leanVM's Merkle trees, the three openings' duplex with grinding), the oracle
`G = (Keccak-256, Keccak-f[1600])` of `Skeleton.lean`, and a prover `P` (its messages and its
secret tables' rows). Three hypotheses remain here, each named (for the deployed prover, the
end theorem `zeroKnowledge_closed` discharges them: `JointHVZK` in its approximate form by
`Instance/Nondeg.lean`'s `jointHVZKε_of_linkV`, `FSFresh` below, `Factors` by `Instance/JointV.lean`'s
`factors_singleV`, `factors_pairV`):

* **`JointHVZK P simV good εhv`**: the honest-verifier zero knowledge of the whole interactive
  protocol (the reduction's masks, F1; each secret table's hidden layout, F3 with the gadget's
  condition (R)): at good challenges the view `P.view s σ` of uniform randomness is `simV σ`, and
  bad challenges have probability at most `εhv`;
* **`FSFresh P (skel sh) c₀ εFS`**: the honest prover's Fiat–Shamir queries find their inputs
  unanswered but with probability `εFS` (every Fiat–Shamir input holds the previous answer or a
  fresh root: a collision bound, a hypothesis of this file, proved for the deployed skeleton in
  `Deployed/Fresh.lean`: `fsFresh_deployed`, `fsFresh_deployed_bits`; with the setup and an empty
  cache before the proof, `Deployed/Fresh/Setup.lean`'s `fsFresh_setup_deployed_bits`, `2^-113`);
* **`Factors`**, for every challenge vector and unopened leaf (and pair of leaves): the joint view
  is a function of the rest of the randomness and of the leaf's table's F3 view, the table's
  padding being independent (the deployed prover's structure). With it the entropy hypotheses of
  `zk_rom` are **proved**: `Factors.bound` turns each table's entropy into the joint view's, and
  `hidden_hδ` gives each table's entropy from the layout (`row_entropy`): `δ = |K|^-(L - 3)`,
  `2^-2368` for the witness table's 40 lanes, `2^-3840` for the quotient table's 63.

**`zk_deployed`**: for every distinguisher of at most `QD` oracle queries, the real and the
simulated games are within `εFS + εhv + 2^24 (|c₀| + QP + QD) δ + 2^48 δ₂` (`2^24` the leaf positions
of the two secret tables), and **`zk_deployed_bits`**: with `δ = δ₂ = 2^-2368` and
`|c₀| + QP + QD ≤ 2^128`, within `εFS + εhv + 2^-2200`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace QuotientZk.Deployed

set_option linter.unusedSectionVars false

/-! ## The named hypotheses -/

section Named

variable {S I O M K X Pf : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
  [DecidableEq K] [DecidableEq X] [Inhabited I] [SampleableType S]

/-- **The interactive protocol's honest-verifier zero knowledge**: at good challenges, the view of
uniform randomness is the simulator's; bad challenges have probability at most `ε`. -/
def JointHVZK (P : Proto S I O M K X) (simV : List O → ProbComp (View M I K X))
    (good : List O → Prop) (ε : ℝ≥0∞) : Prop :=
  (∀ σ, good σ → (fun s => P.view s σ) <$> ($ᵗ S) =ᵈ simV σ) ∧
    Pr{let σ ← uniformList O P.n}[¬ good σ] ≤ ε

/-- **The honest prover's Fiat–Shamir inputs are fresh** but with probability `ε`, run from an
oracle that holds `c₀`. -/
def FSFresh (P : Proto S I O M K X) (skel : OracleComp (OpSpec I O M K X) Pf)
    (c₀ : List (I × O)) (ε : ℝ≥0∞) : Prop :=
  Pr{let x ← (do
      let s ← $ᵗ S
      let z ← (simulateQ (implReal P s) skel).run (St.init c₀)
      return z.2.fs)}[x = true] ≤ ε

/-- **How the joint view factors through a secret table**, for an event `Ev` of the randomness
(a leaf's row equal to a value, or two leaves' rows equal): the randomness is a pair `(a, b)`, `b`
the table's padding; the view is a function of `a` and of the table's view `g a b`; and given `a`
and `g a b` the event has probability at most `δ`. -/
structure Factors (P : Proto S I O M K X) (σ : List O) (Ev : S → Prop) (δ : ℝ≥0∞) : Type 1 where
  A : Type
  B : Type
  U : Type
  [sA : SampleableType A]
  [sB : SampleableType B]
  e : S ≃ A × B
  Φ : A → U → View M I K X
  g : A → B → U
  E : A → B → Prop
  hview : ∀ s, P.view s σ = Φ (e s).1 (g (e s).1 (e s).2)
  hev : ∀ s, Ev s ↔ E (e s).1 (e s).2
  hδ : ∀ a u, Pr{let b ← $ᵗ B}[g a b = u ∧ E a b] ≤ δ * Pr{let b ← $ᵗ B}[g a b = u]

attribute [instance] Factors.sA Factors.sB

/-- **The event keeps its entropy given the joint view.** -/
theorem Factors.bound {P : Proto S I O M K X} {σ : List O} {Ev : S → Prop} {δ : ℝ≥0∞}
    (F : Factors P σ Ev δ) (v : View M I K X) :
    Pr{let s ← $ᵗ S}[P.view s σ = v ∧ Ev s] ≤ δ * Pr{let s ← $ᵗ S}[P.view s σ = v] := by
  have hS : ∀ p : S → Prop, Pr{let s ← $ᵗ S}[p s] = Pr{let x ← $ᵗ (F.A × F.B)}[p (F.e.symm x)] :=
    fun p => by
      rw [← ((SampleableType.map_uniformSample_evalDistEq_of_bijective
        F.e.symm.bijective).prEvent_eq p), prEvent_map]
  rw [hS, hS]
  have h1 : ∀ x : F.A × F.B, (P.view (F.e.symm x) σ = v ∧ Ev (F.e.symm x)) ↔
      (F.Φ x.1 (F.g x.1 x.2) = v ∧ F.E x.1 x.2) := fun x => by
    rw [F.hview, F.hev, Equiv.apply_symm_apply]
  have h2 : ∀ x : F.A × F.B, P.view (F.e.symm x) σ = v ↔ F.Φ x.1 (F.g x.1 x.2) = v :=
    fun x => by rw [F.hview, Equiv.apply_symm_apply]
  simp_rw [h1, h2]
  exact prEvent_factor_le F.Φ F.g F.E δ F.hδ v

end Named

/-! ## Each hidden table's entropy -/

section Hidden

open QuotientSecurity.Hiding

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q]
  [DecidableEq Q]

/-- **A hidden table's rows keep `L - 3` elements of `K` given its view**, in `Factors`'s form
(`δ = |K|^-(L-3)`): for its padding `b` uniform and any part `base a` the rest determines, the event
"row `x₀` minus row `x₁` is `z a`" (one row against a value: `x₁ = 0`; two rows: `z = 0`). -/
theorem hidden_hδ [Fintype K] [DecidableEq K] [FiniteDimensional K E]
    (h3 : Module.finrank K E = 3) [SampleableType (ι → Y → K)] {A Rd : Type} [AddCommGroup Rd]
    [Module K Rd] (F : Finset Y) (stackR : (ι → Y → K) →ₗ[K] (ι → Y → K))
    (hR : ∀ T, OnFirst F T → stackR T = T) (rounds : (ι → Y → K) →ₗ[K] Rd)
    (hrounds : ∀ T, OnFirst F T → rounds T = 0) (ε : ι → E) (enc : Q → Y → K)
    (x₀ x₁ u : Y → K) (hu : ∀ y ∉ F, u y = 0) (huQ : ∀ x, ∑ y, enc x y * u y = 0)
    (hu₀ : ∑ y, x₀ y * u y = 1) (hu₁ : ∑ y, x₁ y * u y = 0) (base : A → ι → Y → K)
    (z : A → ι → K) (a : A) (v : Rd × (Y → E) × (Q → ι → K)) :
    Pr{let r ← $ᵗ (ι → Y → K)}[viewMap rounds ε enc (base a + stackR r) = v ∧
        rowAt x₀ (base a + stackR r) - rowAt x₁ (base a + stackR r) = z a] ≤
      ((Fintype.card K ^ (Fintype.card ι - 3) : ℕ) : ℝ≥0∞)⁻¹ *
        Pr{let r ← $ᵗ (ι → Y → K)}[viewMap rounds ε enc (base a + stackR r) = v] := by
  have h := row_entropy h3 F stackR hR rounds hrounds ε enc x₀ x₁ u hu huQ hu₀ hu₁ (base a) v (z a)
  have hc : ((Fintype.card K ^ (Fintype.card ι - 3) : ℕ) : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card K := Fintype.card_pos
    exact_mod_cast (pow_pos this _).ne'
  calc _ = (Pr{let r ← $ᵗ (ι → Y → K)}[viewMap rounds ε enc (base a + stackR r) = v ∧
          rowAt x₀ (base a + stackR r) - rowAt x₁ (base a + stackR r) = z a] *
          ((Fintype.card K ^ (Fintype.card ι - 3) : ℕ) : ℝ≥0∞)) *
          ((Fintype.card K ^ (Fintype.card ι - 3) : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), mul_one]
    _ ≤ Pr{let r ← $ᵗ (ι → Y → K)}[viewMap rounds ε enc (base a + stackR r) = v] *
          ((Fintype.card K ^ (Fintype.card ι - 3) : ℕ) : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := mul_comm _ _

set_option exponentiation.threshold 4000 in
/-- At our sizes: `|K| = 2^64`, 40 lanes (the witness table) give `2^-2368`; 63 (the quotient
table) give `2^-3840 ≤ 2^-2368`. -/
theorem card_pow_lanes (L : ℕ) (hL : 40 ≤ L) :
    (((2 ^ 64) ^ (L - 3) : ℕ) : ℝ≥0∞)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 2368)⁻¹ := by
  rw [ENNReal.inv_le_inv]
  have : (2 : ℝ≥0∞) ^ 2368 = ((2 ^ 2368 : ℕ) : ℝ≥0∞) := by push_cast; ring
  rw [this]
  refine Nat.cast_le.mpr ?_
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Hidden

/-! ## The deployed theorem -/

section Deployed

variable {S : Type} [SampleableType S]

instance : Fintype (Tbl × Pos) := inferInstance

theorem card_positions : Fintype.card (Tbl × Pos) = 2 ^ 24 := by
  simp [Fintype.card_prod, Fintype.card_fin]

/-- **Zero knowledge of the deployed proof, in the random-oracle model.** For the skeleton of the
deployed prover (at most `skelBound sh` operations, `skel_queryBound`) and a prover `P` whose view
factors through each secret table (`hfac`, `hfac₂`), every distinguisher `D` of at most `QD` queries
tells the real game from the simulated one with advantage at most
`εFS + εhv + 2^24 (|c₀| + skelBound sh + QD) δ + 2^48 δ₂`. -/
theorem zk_deployed (sh : Shape) (P : Proto S Inp Out Msg Tbl Pos) (c₀ : List (Inp × Out))
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εFS εhv δ δ₂ : ℝ≥0∞) (QD : ℕ)
    (hFS : FSFresh P (skel sh) c₀ εFS) (hHV : JointHVZK P simV good εhv)
    (hfac : ∀ σ k x, P.opened σ k x = false → ∀ y,
      Nonempty (Factors P σ (fun s => P.rows s σ k x = y) δ))
    (hfac₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') →
      Nonempty (Factors P σ (fun s => P.rows s σ k x = P.rows s σ k' x') δ₂))
    (D : Proof → OracleComp (Inp →ₒ Out) Bool) (hD : ∀ π, IsTotalQueryBound (D π) QD) :
    Close (realGame P (skel sh) c₀ D) (simGame P simV (skel sh) c₀ D)
      (εFS + εhv + ((2 ^ 24 * (c₀.length + (skelBound sh + QD)) : ℕ) * δ +
        (2 ^ 48 : ℕ) * δ₂)) := by
  have h := zk_rom P (skel sh) c₀ simV good εFS εhv δ δ₂ (skelBound sh) QD (skel_queryBound sh)
    hFS hHV.1 hHV.2
    (fun σ k x hx v y => (hfac σ k x hx y).some.bound v)
    (fun σ k x k' x' hx hx' hne v => (hfac₂ σ k x k' x' hx hx' hne).some.bound v) D hD
  rw [card_positions] at h
  simpa [show (2 ^ 24) ^ 2 = 2 ^ 48 by norm_num] using h

/-- **At our sizes**: with the hidden layouts' `δ = δ₂ = 2^-2368` and at most `2^128` oracle entries
and queries in all, the Merkle term is below `2^-2200`. -/
theorem merkleTerm_le (n : ℕ) (hn : n ≤ 2 ^ 128) :
    ((2 ^ 24 * n : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 2368)⁻¹ + ((2 ^ 48 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 2368)⁻¹
      ≤ ((2 : ℝ≥0∞) ^ 2200)⁻¹ := by
  rw [← add_mul, ← Nat.cast_add]
  have h1 : 2 ^ 24 * n + 2 ^ 48 ≤ 2 ^ 168 := by
    calc 2 ^ 24 * n + 2 ^ 48 ≤ 2 ^ 24 * 2 ^ 128 + 2 ^ 48 := by gcongr
      _ ≤ 2 ^ 168 := by norm_num
  calc ((2 ^ 24 * n + 2 ^ 48 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 2368)⁻¹
      ≤ ((2 : ℝ≥0∞) ^ 168) * ((2 : ℝ≥0∞) ^ 2368)⁻¹ := by
        gcongr
        exact_mod_cast h1
    _ = ((2 : ℝ≥0∞) ^ 2200)⁻¹ := by
        rw [show (2 : ℝ≥0∞) ^ 2368 = 2 ^ 168 * 2 ^ 2200 by rw [← pow_add],
          ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), ← mul_assoc,
          ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]

/-- **Zero knowledge of the deployed proof at our sizes**: the deployed shape (`2^22` rows; the
wiring codeword's `2^19` rows), the layouts' `δ = δ₂ = 2^-2368` (`hidden_hδ`, `card_pow_lanes`), and
at most `2^127` initial oracle entries and distinguisher queries: advantage at most
`εFS + εhv + 2^-2200`. -/
theorem zk_deployed_bits (stmt : Statement) (idW idσ idQ : QuotientRpm.Bytes32) (rows : List (List UInt8))
    (hrows : rows.length = 2 ^ 19) (P : Proto S Inp Out Msg Tbl Pos) (c₀ : List (Inp × Out))
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εFS εhv : ℝ≥0∞) (QD : ℕ) (hQ : c₀.length + QD ≤ 2 ^ 127)
    (hFS : FSFresh P (skel (deployedShape stmt idW idσ idQ rows)) c₀ εFS)
    (hHV : JointHVZK P simV good εhv)
    (hfac : ∀ σ k x, P.opened σ k x = false → ∀ y,
      Nonempty (Factors P σ (fun s => P.rows s σ k x = y) ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (hfac₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') →
      Nonempty (Factors P σ (fun s => P.rows s σ k x = P.rows s σ k' x') ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (D : Proof → OracleComp (Inp →ₒ Out) Bool) (hD : ∀ π, IsTotalQueryBound (D π) QD) :
    Close (realGame P (skel (deployedShape stmt idW idσ idQ rows)) c₀ D)
      (simGame P simV (skel (deployedShape stmt idW idσ idQ rows)) c₀ D)
      (εFS + εhv + ((2 : ℝ≥0∞) ^ 2200)⁻¹) := by
  have hb := skelBound_deployed stmt idW idσ idQ rows hrows
  refine (zk_deployed _ P c₀ simV good εFS εhv _ _ QD hFS hHV hfac hfac₂ D hD).mono
    (add_le_add le_rfl (merkleTerm_le _ ?_))
  have : (2 : ℕ) ^ 70 + 2 ^ 127 ≤ 2 ^ 128 := by norm_num
  omega

end Deployed

end QuotientZk.Deployed
