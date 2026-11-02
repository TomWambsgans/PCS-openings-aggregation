-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Joint
import QuotientZk.Deployed.Main

/-!
# The joint model discharges `zk_deployed`'s `JointHVZK` and `Factors`

`zk_deployed` (`Deployed/Main.lean`) is stated for any prover `P : Proto S Inp Out Msg Tbl Pos`
and leaves three named hypotheses: `FSFresh` (the Fiat–Shamir inputs' freshness), `JointHVZK` and,
per unopened leaf (and pair of leaves), `Factors`. This file proves the last two for every prover
that **is the joint model** (`Link`):

* its randomness is the masks and the two tables' paddings, `S = Mk × (ι₁ → Y₁ → K) × (ι₂ → Y₂ → K)`;
* its interactive view is a public function `out σ` of the joint view (`Model.view`, `Joint.lean`)
  at the challenges `chOf σ` the oracle's answers give (`hview`), and those are uniform (`hch`);
* a secret table's unopened leaf is an injective encoding (`enc₁`, `enc₂`: the leaf's bytes) of a
  row of its stack, the row at the position's coefficient vector (`code₁ σ x`: the basis
  polynomials' values at the leaf's point) (`rows₁`, `rows₂`);
* for an unopened position (two unopened positions), a vector of degree below the gadget vanishes
  at the opened positions and is `1` at it (`1` and `0` at the two) (`free₁`, `free₁₂`, `free₂`,
  `free₂₂`): (Q) for the unopened rows, which `exists_unopened_vector` gives for a degree-graded basis
  when the opened positions are fewer than the free entries.

**`jointHVZK_of_link`**: `JointHVZK P simV good (1/2^165)` at our sizes, with `simV σ =
out σ <$> jointSim … (chOf σ)` (`joint_hzk`, `joint_hgood_bits`).

**`factors_single`**, **`factors_pair`**: `Factors` for every unopened leaf and pair of leaves, with
`δ = 2^-2368`, through each table's F3 view (`Deployed.hidden_hδ` on the gadget layout,
`Deployed.gadget_stackR_of_onFirst`): the view is a function of the other table's padding, the
masks, and this table's level-0 view, and the row keeps `L - 3` elements of `K` given that.

**`zk_deployed_joint`**: `zk_deployed_bits` with both discharged: the real and simulated games are
within `εFS + 2^-165 + 2^-2200`, given `FSFresh` and the joint model's named hypotheses.

**Superseded**: `jointHVZK_of_link` and `zk_deployed_joint` ask the honest tables' claims (`hT₁`,
`hT₂`) at every mask, which the honest tables do not meet at degenerate challenges and masks; the
deployed result is `zeroKnowledge_closed` through `jointHVZKε_of_linkV` (`Instance/Nondeg.lean`).
`factors_single`, `factors_pair` have their counterparts `factors_singleV`, `factors_pairV`
(`Instance/JointV.lean`), which that chain uses.
-/

open OracleComp OracleSpec Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open scoped ENNReal NNReal

namespace QuotientZk.Joint

set_option linter.unusedSectionVars false

/-! ## Monotonicity of `Factors` -/

/-- `Factors` with a larger `δ`. -/
def factorsMono {S I Ob Mm Kt Xt : Type} [Inhabited I] [SampleableType S]
    {P : Proto S I Ob Mm Kt Xt} {σ : List Ob} {Ev : S → Prop} {δ δ' : ℝ≥0∞}
    (F : Deployed.Factors P σ Ev δ) (h : δ ≤ δ') : Deployed.Factors P σ Ev δ' where
  A := F.A
  B := F.B
  U := F.U
  e := F.e
  Φ := F.Φ
  g := F.g
  E := F.E
  hview := F.hview
  hev := F.hev
  hδ := fun a u => (F.hδ a u).trans (mul_le_mul_left h _)

/-! ## One table's factorization -/

section Table

variable {K E ι Y Q : Type} [Field K] [Field E] [Algebra K E]
  [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q] [DecidableEq Q]

/-- **The joint view factors through one gadget-layout table's view**: the randomness is `(a, b)`,
`b` the table's padding; the view is `Φ a` of the table's level-0 view of `base a + stackR b`; an
event that forces a row (or a difference of two rows) of the stack to a value `a` determines keeps
`L - 3` elements of `K` given the view (`Deployed.hidden_hδ`). -/
theorem factors_table [Fintype K] [DecidableEq K] [FiniteDimensional K E]
    [SampleableType (ι → Y → K)] (h3 : finrank K E = 3) {Sx A I Ob Mm Kt Xt : Type} [Inhabited I]
    [SampleableType Sx] [SampleableType A] (P : Proto Sx I Ob Mm Kt Xt) (σ : List Ob)
    (Ev : Sx → Prop) (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) {m : ℕ}
    (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (β : Fin 3 → E) (lam : Fin (m + 1) → E)
    (φ : Fin 6 → E) (enc : Q → Y → K) (e : Sx ≃ A × (ι → Y → K)) (base : A → ι → Y → K)
    (Φ : A → (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → View Mm I Kt Xt)
    (hview : ∀ s, P.view s σ =
      Φ (e s).1 (Gadget.levelMap L pos Wc β lam φ enc (base (e s).1 + L.stackR (e s).2)))
    (x₀ x₁ u : Y → K) (hu : ∀ y ∉ L.first, u y = 0) (huQ : ∀ q, ∑ y, enc q y * u y = 0)
    (hu₀ : ∑ y, x₀ y * u y = 1) (hu₁ : ∑ y, x₁ y * u y = 0) (z : A → ι → K)
    (hev : ∀ s, Ev s → Deployed.rowAt x₀ (base (e s).1 + L.stackR (e s).2) -
      Deployed.rowAt x₁ (base (e s).1 + L.stackR (e s).2) = z (e s).1) :
    Nonempty (Deployed.Factors P σ Ev
      ((Fintype.card K ^ (Fintype.card ι - 3) : ℕ) : ℝ≥0∞)⁻¹) := by
  classical
  have hWb := Gadget.combinedW_first L pos Wc hW β lam
  refine ⟨Deployed.Factors.mk (A := A) (B := ι → Y → K)
    (U := (Fin 6 → E × E) × (Y → E) × (Q → ι → K)) e Φ
    (fun a b => Gadget.levelMap L pos Wc β lam φ enc (base a + L.stackR b))
    (fun a b => Ev (e.symm (a, b))) hview (fun s => by simp) ?_⟩
  intro a v
  have hmono : Pr{let b ← $ᵗ (ι → Y → K)}[Gadget.levelMap L pos Wc β lam φ enc
        (base a + L.stackR b) = v ∧ Ev (e.symm (a, b))] ≤
      Pr{let b ← $ᵗ (ι → Y → K)}[Gadget.levelMap L pos Wc β lam φ enc (base a + L.stackR b) = v ∧
        Deployed.rowAt x₀ (base a + L.stackR b) - Deployed.rowAt x₁ (base a + L.stackR b) =
          z a] := by
    refine prEvent_mono _ _ _ fun b h => ⟨h.1, ?_⟩
    have := hev (e.symm (a, b)) h.2
    simpa using this
  refine hmono.trans ?_
  exact Deployed.hidden_hδ h3 L.first L.stackR (Deployed.gadget_stackR_of_onFirst L)
    (roundsMap pos φ (HiddenLayout.combinedW pos (Gadget.claimsW L pos Wc β) lam))
    (fun T hT => roundsMap_eq_zero pos φ _ L.first hWb T hT) (HiddenLayout.foldW pos φ) enc
    x₀ x₁ u hu huQ hu₀ hu₁ base z a v

theorem rowAt_zero (T : ι → Y → K) : Deployed.rowAt (0 : Y → K) T = 0 := by
  funext l
  simp [Deployed.rowAt]

end Table

/-! ## The link between a prover and the joint model -/

section Link

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]

/-- The prover's randomness: the masks and the two tables' paddings. -/
abbrev Rand (K ι₁ Y₁ ι₂ Y₂ : Type) := (Fin 4 → Fin 3 → K) × (ι₁ → Y₁ → K) × (ι₂ → Y₂ → K)

/-- The witness table's stack, at challenges `c`, for the randomness `s`. -/
def stack₁ (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁) (c : Chal E Γ₁ Γ₂ Γw)
    (s : Rand K ι₁ Y₁ ι₂ Y₂) : ι₁ → Y₁ → K :=
  S₁.L.stackD (T₁ c s.1) + S₁.L.stackR s.2.1

/-- The quotient table's stack. -/
def stack₂ (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂) (c : Chal E Γ₁ Γ₂ Γw)
    (s : Rand K ι₁ Y₁ ι₂ Y₂) : ι₂ → Y₂ → K :=
  S₂.L.stackD (T₂ c s.1) + S₂.L.stackR s.2.2

/-- A vector of degree below the gadget, vanishing at the opened positions, with given values at
one or two positions' coefficient vectors. -/
def FreeVec {Y Q : Type} [Fintype Y] (first : Finset Y) (enc : Q → Y → K) (u : Y → K) : Prop :=
  (∀ y ∉ first, u y = 0) ∧ ∀ q, ∑ y, enc q y * u y = 0

/-- **A prover that is the joint model**: its view is a public function of the joint view at the
challenges its oracle answers give (uniform), and its unopened leaves are injective encodings of
its stacks' rows, each with a free vector ((Q) for the unopened rows). -/
structure Link {I Ob Mm Xt : Type} [Inhabited I] (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) I Ob Mm (Fin 2) Xt)
    (P₀ : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (wir : Chal E Γ₁ Γ₂ Γw → W)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂) where
  /-- The challenges the oracle's answers give. -/
  chOf : List Ob → Chal E Γ₁ Γ₂ Γw
  /-- The interactive view from the joint view (public). -/
  out : List Ob → ((Fin 4 → E) × E) × W × O₁ × O₂ → View Mm I (Fin 2) Xt
  hview : ∀ s σ, P.view s σ = out σ ((model P₀ gK van wir T₁ T₂ S₁ S₂).view (chOf σ) s)
  /-- A leaf's bytes from its row, per table; injective. -/
  enc₁ : (ι₁ → K) → I
  enc₂ : (ι₂ → K) → I
  inj₁ : Function.Injective enc₁
  inj₂ : Function.Injective enc₂
  /-- A position's coefficient vector: the basis polynomials' values at its point. -/
  code₁ : List Ob → Xt → Y₁ → K
  code₂ : List Ob → Xt → Y₂ → K
  /-- An unopened leaf is its row's encoding. -/
  rows₁ : ∀ s σ x, P.opened σ 0 x = false →
    P.rows s σ 0 x = enc₁ (Deployed.rowAt (code₁ σ x) (stack₁ T₁ S₁ (chOf σ) s))
  rows₂ : ∀ s σ x, P.opened σ 1 x = false →
    P.rows s σ 1 x = enc₂ (Deployed.rowAt (code₂ σ x) (stack₂ T₂ S₂ (chOf σ) s))
  /-- **(Q) for the unopened rows**: free vectors. -/
  free₁ : ∀ σ x, P.opened σ 0 x = false →
    ∃ u, FreeVec S₁.L.first (S₁.enc (chOf σ)) u ∧ ∑ y, code₁ σ x y * u y = 1
  free₁₂ : ∀ σ x x', P.opened σ 0 x = false → P.opened σ 0 x' = false → x ≠ x' →
    ∃ u, FreeVec S₁.L.first (S₁.enc (chOf σ)) u ∧ ∑ y, code₁ σ x y * u y = 1 ∧
      ∑ y, code₁ σ x' y * u y = 0
  free₂ : ∀ σ x, P.opened σ 1 x = false →
    ∃ u, FreeVec S₂.L.first (S₂.enc (chOf σ)) u ∧ ∑ y, code₂ σ x y * u y = 1
  free₂₂ : ∀ σ x x', P.opened σ 1 x = false → P.opened σ 1 x' = false → x ≠ x' →
    ∃ u, FreeVec S₂.L.first (S₂.enc (chOf σ)) u ∧ ∑ y, code₂ σ x y * u y = 1 ∧
      ∑ y, code₂ σ x' y * u y = 0

variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  {I Ob Mm Xt : Type} [Inhabited I]
  {P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) I Ob Mm (Fin 2) Xt} {P₀ : Params E} {gK : Fin 4 → K[X]}
  {van : K[X]} {wir : Chal E Γ₁ Γ₂ Γw → W}
  {T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K}
  {T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K}
  {S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁}
  {S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂}

/-- The randomness split as (masks and the quotient table's padding, the witness table's). -/
def split₁ : Rand K ι₁ Y₁ ι₂ Y₂ ≃ ((Fin 4 → Fin 3 → K) × (ι₂ → Y₂ → K)) × (ι₁ → Y₁ → K) where
  toFun s := ((s.1, s.2.2), s.2.1)
  invFun p := (p.1.1, p.2, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The randomness split as (masks and the witness table's padding, the quotient table's). -/
def split₂ : Rand K ι₁ Y₁ ι₂ Y₂ ≃ ((Fin 4 → Fin 3 → K) × (ι₁ → Y₁ → K)) × (ι₂ → Y₂ → K) where
  toFun s := ((s.1, s.2.1), s.2.2)
  invFun p := (p.1.1, p.1.2, p.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Through the witness table: an event forcing a row difference of its stack to a value the rest
determines. -/
theorem factors₁ (hS₁ : S₁.Conditions) (h3 : finrank K E = 3)
    (lk : Link P P₀ gK van wir T₁ T₂ S₁ S₂) (σ : List Ob) (Ev : Rand K ι₁ Y₁ ι₂ Y₂ → Prop)
    (x₀ x₁ u : Y₁ → K) (hu : FreeVec S₁.L.first (S₁.enc (lk.chOf σ)) u)
    (hu₀ : ∑ y, x₀ y * u y = 1) (hu₁ : ∑ y, x₁ y * u y = 0)
    (z : (Fin 4 → Fin 3 → K) × (ι₂ → Y₂ → K) → ι₁ → K)
    (hev : ∀ s, Ev s → Deployed.rowAt x₀ (stack₁ T₁ S₁ (lk.chOf σ) s) -
      Deployed.rowAt x₁ (stack₁ T₁ S₁ (lk.chOf σ) s) = z (s.1, s.2.2)) :
    Nonempty (Deployed.Factors P σ Ev
      ((Fintype.card K ^ (Fintype.card ι₁ - 3) : ℕ) : ℝ≥0∞)⁻¹) := by
  set c := lk.chOf σ
  exact factors_table h3 P σ Ev S₁.L S₁.pos (S₁.Wc c) (hS₁.weightsFit c) S₁.β
    (Gadget.powers S₁.m (lam₁ c)) (phi₁ c) (S₁.enc c) split₁ (fun a => S₁.L.stackD (T₁ c a.1))
    (fun a v => lk.out σ (redMsgs P₀ gK van c.1.1.2 a.1, wir c, S₁.rest c v,
      S₂.view lam₂ phi₂ c (T₂ c a.1) a.2))
    (fun s => lk.hview s σ) x₀ x₁ u hu.1 hu.2 hu₀ hu₁ z (fun s h => hev s h)

/-- Through the quotient table. -/
theorem factors₂ (hS₂ : S₂.Conditions) (h3 : finrank K E = 3)
    (lk : Link P P₀ gK van wir T₁ T₂ S₁ S₂) (σ : List Ob) (Ev : Rand K ι₁ Y₁ ι₂ Y₂ → Prop)
    (x₀ x₁ u : Y₂ → K) (hu : FreeVec S₂.L.first (S₂.enc (lk.chOf σ)) u)
    (hu₀ : ∑ y, x₀ y * u y = 1) (hu₁ : ∑ y, x₁ y * u y = 0)
    (z : (Fin 4 → Fin 3 → K) × (ι₁ → Y₁ → K) → ι₂ → K)
    (hev : ∀ s, Ev s → Deployed.rowAt x₀ (stack₂ T₂ S₂ (lk.chOf σ) s) -
      Deployed.rowAt x₁ (stack₂ T₂ S₂ (lk.chOf σ) s) = z (s.1, s.2.1)) :
    Nonempty (Deployed.Factors P σ Ev
      ((Fintype.card K ^ (Fintype.card ι₂ - 3) : ℕ) : ℝ≥0∞)⁻¹) := by
  set c := lk.chOf σ
  exact factors_table h3 P σ Ev S₂.L S₂.pos (S₂.Wc c) (hS₂.weightsFit c) S₂.β
    (Gadget.powers S₂.m (lam₂ c)) (phi₂ c) (S₂.enc c) split₂ (fun a => S₂.L.stackD (T₂ c a.1))
    (fun a v => lk.out σ (redMsgs P₀ gK van c.1.1.2 a.1, wir c,
      S₁.view lam₁ phi₁ c (T₁ c a.1) a.2, S₂.rest c v))
    (fun s => lk.hview s σ) x₀ x₁ u hu.1 hu.2 hu₀ hu₁ z (fun s h => hev s h)

/-- The preimage of a leaf's bytes under an injective encoding, or zero. -/
noncomputable def preimage {R I : Type} [Zero R] (f : R → I) (y : I) : R :=
  open Classical in if h : ∃ w, f w = y then h.choose else 0

theorem preimage_eq {R I : Type} [Zero R] {f : R → I} (hf : Function.Injective f) {w : R}
    {y : I} (h : f w = y) : preimage f y = w := by
  classical
  have hex : ∃ w, f w = y := ⟨w, h⟩
  unfold preimage
  rw [dif_pos hex]
  exact hf (hex.choose_spec.trans h.symm)

/-- `δ` at our sizes: `|K| = 2^64` and at least 40 lanes. -/
theorem delta_le (hK : Fintype.card K = 2 ^ 64) (ι : Type) [Fintype ι] (h40 : 40 ≤ Fintype.card ι) :
    ((Fintype.card K ^ (Fintype.card ι - 3) : ℕ) : ℝ≥0∞)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 2368)⁻¹ := by
  rw [hK]
  exact Deployed.card_pow_lanes _ h40

/-- **`Factors` for every unopened leaf** (`zk_deployed`'s `hfac`), `δ = 2^-2368`. -/
theorem factors_single (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions) (h3 : finrank K E = 3)
    (hK : Fintype.card K = 2 ^ 64) (h40₁ : 40 ≤ Fintype.card ι₁) (h40₂ : 40 ≤ Fintype.card ι₂)
    (lk : Link P P₀ gK van wir T₁ T₂ S₁ S₂) :
    ∀ σ k x, P.opened σ k x = false → ∀ y,
      Nonempty (Deployed.Factors P σ (fun s => P.rows s σ k x = y) ((2 : ℝ≥0∞) ^ 2368)⁻¹) := by
  intro σ k x hx y
  fin_cases k
  · obtain ⟨u, hu, hu₀⟩ := lk.free₁ σ x hx
    obtain ⟨F⟩ := factors₁ hS₁ h3 lk σ (fun s => P.rows s σ 0 x = y) (lk.code₁ σ x) 0 u hu hu₀
      (by simp) (fun _ => preimage lk.enc₁ y) (fun s h => by
        rw [rowAt_zero, sub_zero]
        exact (preimage_eq lk.inj₁ ((lk.rows₁ s σ x hx).symm.trans h)).symm)
    exact ⟨factorsMono F (delta_le hK ι₁ h40₁)⟩
  · obtain ⟨u, hu, hu₀⟩ := lk.free₂ σ x hx
    obtain ⟨F⟩ := factors₂ hS₂ h3 lk σ (fun s => P.rows s σ 1 x = y) (lk.code₂ σ x) 0 u hu hu₀
      (by simp) (fun _ => preimage lk.enc₂ y) (fun s h => by
        rw [rowAt_zero, sub_zero]
        exact (preimage_eq lk.inj₂ ((lk.rows₂ s σ x hx).symm.trans h)).symm)
    exact ⟨factorsMono F (delta_le hK ι₂ h40₂)⟩

/-- **`Factors` for every pair of unopened leaves** (`zk_deployed`'s `hfac₂`), `δ₂ = 2^-2368`. -/
theorem factors_pair (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions) (h3 : finrank K E = 3)
    (hK : Fintype.card K = 2 ^ 64) (h40₁ : 40 ≤ Fintype.card ι₁) (h40₂ : 40 ≤ Fintype.card ι₂)
    (lk : Link P P₀ gK van wir T₁ T₂ S₁ S₂) :
    ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false → (k, x) ≠ (k', x') →
      Nonempty (Deployed.Factors P σ (fun s => P.rows s σ k x = P.rows s σ k' x')
        ((2 : ℝ≥0∞) ^ 2368)⁻¹) := by
  intro σ k x k' x' hx hx' hne
  fin_cases k <;> fin_cases k'
  · -- two leaves of the witness table
    have hxx : x ≠ x' := fun h => hne (by simp [h])
    obtain ⟨u, hu, hu₀, hu₁⟩ := lk.free₁₂ σ x x' hx hx' hxx
    obtain ⟨F⟩ := factors₁ hS₁ h3 lk σ (fun s => P.rows s σ 0 x = P.rows s σ 0 x')
      (lk.code₁ σ x) (lk.code₁ σ x') u hu hu₀ hu₁ (fun _ => 0) (fun s h => by
        rw [lk.rows₁ s σ x hx, lk.rows₁ s σ x' hx'] at h
        rw [lk.inj₁ h, sub_self])
    exact ⟨factorsMono F (delta_le hK ι₁ h40₁)⟩
  · -- a witness leaf and a quotient leaf: through the witness table
    obtain ⟨u, hu, hu₀⟩ := lk.free₁ σ x hx
    obtain ⟨F⟩ := factors₁ hS₁ h3 lk σ (fun s => P.rows s σ 0 x = P.rows s σ 1 x')
      (lk.code₁ σ x) 0 u hu hu₀ (by simp)
      (fun a => preimage lk.enc₁ (lk.enc₂ (Deployed.rowAt (lk.code₂ σ x')
        (S₂.L.stackD (T₂ (lk.chOf σ) a.1) + S₂.L.stackR a.2))))
      (fun s h => by
        rw [rowAt_zero, sub_zero]
        rw [lk.rows₁ s σ x hx, lk.rows₂ s σ x' hx'] at h
        exact (preimage_eq lk.inj₁ h).symm)
    exact ⟨factorsMono F (delta_le hK ι₁ h40₁)⟩
  · -- a quotient leaf and a witness leaf: through the quotient table
    obtain ⟨u, hu, hu₀⟩ := lk.free₂ σ x hx
    obtain ⟨F⟩ := factors₂ hS₂ h3 lk σ (fun s => P.rows s σ 1 x = P.rows s σ 0 x')
      (lk.code₂ σ x) 0 u hu hu₀ (by simp)
      (fun a => preimage lk.enc₂ (lk.enc₁ (Deployed.rowAt (lk.code₁ σ x')
        (S₁.L.stackD (T₁ (lk.chOf σ) a.1) + S₁.L.stackR a.2))))
      (fun s h => by
        rw [rowAt_zero, sub_zero]
        rw [lk.rows₂ s σ x hx, lk.rows₁ s σ x' hx'] at h
        exact (preimage_eq lk.inj₂ h).symm)
    exact ⟨factorsMono F (delta_le hK ι₂ h40₂)⟩
  · -- two leaves of the quotient table
    have hxx : x ≠ x' := fun h => hne (by simp [h])
    obtain ⟨u, hu, hu₀, hu₁⟩ := lk.free₂₂ σ x x' hx hx' hxx
    obtain ⟨F⟩ := factors₂ hS₂ h3 lk σ (fun s => P.rows s σ 1 x = P.rows s σ 1 x')
      (lk.code₂ σ x) (lk.code₂ σ x') u hu hu₀ hu₁ (fun _ => 0) (fun s h => by
        rw [lk.rows₂ s σ x hx, lk.rows₂ s σ x' hx'] at h
        rw [lk.inj₂ h, sub_self])
    exact ⟨factorsMono F (delta_le hK ι₂ h40₂)⟩

end Link

/-! ## `JointHVZK` and the deployed theorem -/

section Final

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **Superseded**: its hypotheses `hT₁`/`hT₂` are not met by the honest tables at degenerate
challenges/masks; the deployed result is `zeroKnowledge_closed` through `jointHVZKε_of_linkV`
(`Instance/Nondeg.lean`). (`hT₁`, `hT₂` ask the honest tables' claims at every mask, with no
`ClaimsND`.)

**`zk_deployed`'s `JointHVZK`** for a prover that is the joint model, at our sizes:
`εhv = 2^-165`, the simulator `out σ <$> jointSim … (chOf σ)`. -/
theorem jointHVZK_of_link {I Ob Mm Xt : Type} [DecidableEq I] [Inhabited I] [SampleableType Ob]
    [Inhabited Ob] [DecidableEq Xt] (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) I Ob Mm (Fin 2) Xt)
    (h3 : finrank K E = 3) (P₀ : Params E) (hE : P₀.Exact) (stmt : Fin P₀.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P₀.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22)
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P₀ gK van c → ∀ m, S₁.claims c (T₁ c m) = cl₁ c (redMsgs P₀ gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P₀ gK van c → ∀ m, S₂.claims c (T₂ c m) = cl₂ c (redMsgs P₀ gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P₀ gK van c → ∀ v, S₁.claims c (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P₀ gK van c → ∀ v, S₂.claims c (simT₂ c v) = cl₂ c v)
    (lk : Link P P₀ gK van wir T₁ T₂ S₁ S₂)
    (hch : lk.chOf <$> uniformList Ob P.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw))) :
    Deployed.JointHVZK P
      (fun σ => lk.out σ <$> jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
      (fun σ => good P₀ gK van (lk.chOf σ)) (1 / 2 ^ 165) :=
  ⟨hzk_of_factor P lk.chOf (model P₀ gK van wir T₁ T₂ S₁ S₂).view lk.out lk.hview
      (jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂) (good P₀ gK van)
      (joint_hzk h3 P₀ hE stmt gK van hvan hsat inK hinK sigmaAt hsig wir S₁ S₂ hS₁ hS₂ T₁ T₂
        cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂),
    hgood_of_uniform P.n lk.chOf hch (good P₀ gK van) _
      (joint_hgood_bits P₀ gK van hvan0 hq hK hN hdeg)⟩

/-- **Superseded**: its hypotheses `hT₁`/`hT₂` are not met by the honest tables at degenerate
challenges/masks; the deployed result is `zeroKnowledge_closed` through `jointHVZKε_of_linkV`
(`Instance/Nondeg.lean`). (`hT₁`, `hT₂` ask the honest tables' claims at every mask, with no
`ClaimsND`.)

**Zero knowledge of the deployed proof, with the joint model**: `zk_deployed_bits` with
`JointHVZK` (`jointHVZK_of_link`) and `Factors` (`factors_single`, `factors_pair`) discharged. For
the deployed skeleton and a prover that is the joint model, every distinguisher of at most `QD`
queries (with `|c₀| + QD ≤ 2^127`) tells the real game from the simulated one with advantage at most
`εFS + 2^-165 + 2^-2200`. Remaining: `hFS` (`FSFresh`), and the joint model's named hypotheses
(F1's, (Q) and `WeightsFit` and the layouts' lanes in `S₁.Conditions`, `S₂.Conditions`, the
claims `hT`/`hsimT`, the link `lk` and `hch`, the sizes). -/
theorem zk_deployed_joint (stmtD : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) Deployed.Inp Deployed.Out Deployed.Msg Deployed.Tbl
      Deployed.Pos)
    (c₀ : List (Deployed.Inp × Deployed.Out)) (εFS : ℝ≥0∞) (QD : ℕ) (hQ : c₀.length + QD ≤ 2 ^ 127)
    (hFS : Deployed.FSFresh P (Deployed.skel (Deployed.deployedShape stmtD idW idσ idQ rowsW)) c₀ εFS)
    (h3 : finrank K E = 3) (P₀ : Params E) (hE : P₀.Exact) (stmt : Fin P₀.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P₀.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22) (h40₁ : 40 ≤ Fintype.card ι₁) (h40₂ : 40 ≤ Fintype.card ι₂)
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P₀ gK van c → ∀ m, S₁.claims c (T₁ c m) = cl₁ c (redMsgs P₀ gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P₀ gK van c → ∀ m, S₂.claims c (T₂ c m) = cl₂ c (redMsgs P₀ gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P₀ gK van c → ∀ v, S₁.claims c (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P₀ gK van c → ∀ v, S₂.claims c (simT₂ c v) = cl₂ c v)
    (lk : Link P P₀ gK van wir T₁ T₂ S₁ S₂)
    (hch : lk.chOf <$> uniformList Deployed.Out P.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw)))
    (D : Deployed.Proof → OracleComp (Deployed.Inp →ₒ Deployed.Out) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD) :
    Close (realGame P (Deployed.skel (Deployed.deployedShape stmtD idW idσ idQ rowsW)) c₀ D)
      (simGame P (fun σ => lk.out σ <$> jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
        (Deployed.skel (Deployed.deployedShape stmtD idW idσ idQ rowsW)) c₀ D)
      (εFS + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹) :=
  Deployed.zk_deployed_bits stmtD idW idσ idQ rowsW hrows P c₀ _ _ εFS (1 / 2 ^ 165) QD hQ hFS
    (jointHVZK_of_link P h3 P₀ hE stmt gK van hvan hsat hvan0 hq hK hN hdeg inK hinK sigmaAt hsig
      wir S₁ S₂ hS₁ hS₂ T₁ T₂ cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂ lk hch)
    (factors_single hS₁ hS₂ h3 hK h40₁ h40₂ lk) (factors_pair hS₁ hS₂ h3 hK h40₁ h40₂ lk) D hD

end Final

end QuotientZk.Joint
