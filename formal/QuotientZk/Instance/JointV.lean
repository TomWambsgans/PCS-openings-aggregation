-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.FreshJoint

/-!
# The joint model with claims that read the five values

`Joint.lean`'s `SecretOpening` takes its claims' weights `Wc : Ch → …` from the challenges alone,
and `model` opens each secret table at `c`. The deployed quotient opening does not fit: its first
claim's point has the coordinate `vCells(t) / claimDen(α, β, t, a, s)`
(`Implementation.modelQuotient`, `Formula.quotient`), which reads the five values `(a, s)`, so its
weight (and with it the lane rounds WHIR sends) is a function of the challenges **and** of the
reduction's messages. This file is `Joint.lean`, `JointDeployed.lean` and `RpmJoint.lean` again for
openings over `ChV = Chal × Vals` (the challenges and the five values):

* `modelV`: `JointCore`'s generic `Model` with each secret table carried with the five values
  (`tab₁ c m = (redMsgs m, T₁ c m)`), opened at `(c, v)`; its claims are the five values with the
  table's claims at `(c, v)`, so two tables with the same claims have the same five values;
* **`joint_hzkV`**: `JointCore.view_evalDistEq` at every good challenge, the per-opening hiding
  being `SecretOpening.hides` at `(c, v)` (the good challenges do not read `v`);
* `LinkV`, `factors_tableV` (`factors_table` with weights and encodings that read the rest of the
  randomness), `factors_singleV`, `factors_pairV`, **`jointHVZK_of_linkV`**;
* **`zk_rpm_deployed_jointV_fs'`**: `zk_rpm_deployed_joint_fs'` (`FreshJoint.lean`: `FSFresh`,
  `hrow`, `hduplex` discharged for a prover `ofBytes Pb`) for this model.

The witness opening's weights do not read `v`; nothing here needs them to.

**Superseded where the honest tables' claims are hypotheses.** `joint_hzkV`, `jointHVZK_of_linkV`
and `zk_rpm_deployed_jointV_fs'` ask them (`hT₁`, `hT₂`) at every mask of every good challenge,
with no `ClaimsND`, which the honest tables do not meet (where the claims' scales or `claimDen`
vanish, `Nondeg.lean`'s header). The deployed result is `zeroKnowledge_closed` through
`Nondeg.lean`'s `joint_hzkV_nd`, `jointHVZKε_of_linkV` (with `QuotientZk.DRpm.zk_rpm_skel_approx`);
`modelV`, `jointSimV`, `LinkV`, `factors_singleV` and `factors_pairV` are used there as they are.
-/

open OracleComp OracleSpec Polynomial Module QuotientSecurity QuotientSecurity.Hiding Common
open QuotientZk.Joint
open scoped ENNReal NNReal

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

/-- The five values: the four cells' values and the wiring's. -/
abbrev Vals (E : Type) := (Fin 4 → E) × E

/-- What an opening reads: the challenges and the five values. -/
abbrev ChV (E Γ₁ Γ₂ Γw : Type) := Chal E Γ₁ Γ₂ Γw × Vals E

/-- The witness opening's `λ` and `φ`, and the quotient opening's: the challenges'. -/
abbrev lamV₁ {E Γ₁ Γ₂ Γw : Type} (c : ChV E Γ₁ Γ₂ Γw) : E := lam₁ c.1
abbrev phiV₁ {E Γ₁ Γ₂ Γw : Type} (c : ChV E Γ₁ Γ₂ Γw) : Fin 6 → E := phi₁ c.1
abbrev lamV₂ {E Γ₁ Γ₂ Γw : Type} (c : ChV E Γ₁ Γ₂ Γw) : E := lam₂ c.1
abbrev phiV₂ {E Γ₁ Γ₂ Γw : Type} (c : ChV E Γ₁ Γ₂ Γw) : Fin 6 → E := phi₂ c.1

/-! ## The model -/

section Model

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]

/-- **The honest protocol's joint model, the openings reading the five values**: each secret
table is carried with the five values and opened at `(c, v)`. -/
noncomputable def modelV (P : Params E) (gK : Fin 4 → K[X]) (van : K[X])
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂) :
    Model (Chal E Γ₁ Γ₂ Γw) (Fin 4 → Fin 3 → K) (ι₁ → Y₁ → K) (ι₂ → Y₂ → K) (Vals E) W
      (Vals E × (ι₁ → Y₁ → K)) (Vals E × (ι₂ → Y₂ → K)) O₁ O₂ (Vals E × (Fin S₁.m → E))
      (Vals E × (Fin S₂.m → E)) where
  red c := redMsgs P gK van c.1.1.2
  wir := wir
  tab₁ c m := (redMsgs P gK van c.1.1.2 m, T₁ c m)
  tab₂ c m := (redMsgs P gK van c.1.1.2 m, T₂ c m)
  open₁ c d r := S₁.view lamV₁ phiV₁ (c, d.1) d.2 r
  open₂ c d r := S₂.view lamV₂ phiV₂ (c, d.1) d.2 r
  cl₁ c d := (d.1, S₁.claims (c, d.1) d.2)
  cl₂ c d := (d.1, S₂.claims (c, d.1) d.2)

/-- **The simulator**, from the challenges and public data only: the reduction's simulated values
`v`, then each secret opening of the public table `simTᵢ c v` at `(c, v)` with a fresh padding. -/
def jointSimV [SampleableType K] [SampleableType E] [SampleableType (ι₁ → Y₁ → K)]
    [SampleableType (ι₂ → Y₂ → K)] (inK : E → Bool) (sigmaAt : E → E)
    (wir : Chal E Γ₁ Γ₂ Γw → W) (S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (simT₁ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₂ → Y₂ → K) (c : Chal E Γ₁ Γ₂ Γw) :
    ProbComp (Vals E × W × O₁ × O₂) :=
  simulate wir (fun c (d : Vals E × (ι₁ → Y₁ → K)) r => S₁.view lamV₁ phiV₁ (c, d.1) d.2 r)
    (fun c (d : Vals E × (ι₂ → Y₂ → K)) r => S₂.view lamV₂ phiV₂ (c, d.1) d.2 r)
    (fun c => simRed (K := K) inK sigmaAt c.1.1.2) (fun c v => (v, simT₁ c v))
    (fun c v => (v, simT₂ c v)) c

variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]

/-- An opening at `(c, v)` hides its table given its claims, as `Model`'s opening of the pair
`(v, d)`: equal claims force equal five values. -/
theorem hides_pair {ι Y Q O : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]
    [Fintype Q] [DecidableEq Q] [SampleableType (ι → Y → K)] (h3 : finrank K E = 3)
    (S : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι Y Q O) (hS : S.Conditions)
    (lamOf : ChV E Γ₁ Γ₂ Γw → E) (φOf : ChV E Γ₁ Γ₂ Γw → Fin 6 → E) (c : Chal E Γ₁ Γ₂ Γw)
    (hc : ∀ v, Gadget.GoodCh (K := K) (φOf (c, v)) (lamOf (c, v))) :
    Hides (fun c (d : Vals E × (ι → Y → K)) r => S.view lamOf φOf (c, d.1) d.2 r)
      (fun c (d : Vals E × (ι → Y → K)) => (d.1, S.claims (c, d.1) d.2)) c := by
  rintro ⟨v, d⟩ ⟨v', d'⟩ hd
  obtain ⟨rfl, h2⟩ := Prod.mk.inj hd
  exact S.hides h3 hS lamOf φOf (c, v) (hc v) d d' h2

/-- **Superseded**: its hypotheses `hT₁`/`hT₂` are not met by the honest tables at degenerate
challenges/masks; the deployed result is `zeroKnowledge_closed` through `jointHVZKε_of_linkV`
(`Instance/Nondeg.lean`; this theorem's form there: `joint_hzkV_nd`). (`hT₁`, `hT₂` ask the
honest tables' claims at every mask, with no `ClaimsND`; where `claimScale 2 23 t = 0` the
verifier's witness value is `0`, `EndToEnd/Review/E2EZkNondeg.lean`.)

**Joint honest-verifier zero knowledge, the openings reading the five values**: at every good
challenge the honest view under uniform masks and paddings has the distribution of `jointSimV`. -/
theorem joint_hzkV (h3 : finrank K E = 3) (P : Params E) (hE : P.Exact) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0)))
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P gK van c → ∀ m,
      S₁.claims (c, redMsgs P gK van c.1.1.2 m) (T₁ c m) = cl₁ c (redMsgs P gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P gK van c → ∀ m,
      S₂.claims (c, redMsgs P gK van c.1.1.2 m) (T₂ c m) = cl₂ c (redMsgs P gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P gK van c → ∀ v, S₁.claims (c, v) (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P gK van c → ∀ v, S₂.claims (c, v) (simT₂ c v) = cl₂ c v) :
    ∀ c, good P gK van c →
      (modelV P gK van wir T₁ T₂ S₁ S₂).view c <$>
          ($ᵗ ((Fin 4 → Fin 3 → K) × (ι₁ → Y₁ → K) × (ι₂ → Y₂ → K)))
        =ᵈ jointSimV inK sigmaAt wir S₁ S₂ simT₁ simT₂ c := by
  intro c hc
  exact view_evalDistEq (modelV P gK van wir T₁ T₂ S₁ S₂)
    (fun c => simRed (K := K) inK sigmaAt c.1.1.2) (fun c v => (v, simT₁ c v))
    (fun c v => (v, simT₂ c v)) c
    (redMsgs_evalDistEq P h3 hE stmt gK van hvan hsat inK hinK sigmaAt hsig c.1.1.1 c.1.1.2 hc.1)
    (hides_pair h3 S₁ hS₁ lamV₁ phiV₁ c fun _ => hc.2.1)
    (hides_pair h3 S₂ hS₂ lamV₂ phiV₂ c fun _ => hc.2.2)
    (fun m => by
      show (redMsgs P gK van c.1.1.2 m, S₁.claims (c, redMsgs P gK van c.1.1.2 m)
          (simT₁ c (redMsgs P gK van c.1.1.2 m))) =
        (redMsgs P gK van c.1.1.2 m, S₁.claims (c, redMsgs P gK van c.1.1.2 m) (T₁ c m))
      rw [hsimT₁ c hc, hT₁ c hc m])
    (fun m => by
      show (redMsgs P gK van c.1.1.2 m, S₂.claims (c, redMsgs P gK van c.1.1.2 m)
          (simT₂ c (redMsgs P gK van c.1.1.2 m))) =
        (redMsgs P gK van c.1.1.2 m, S₂.claims (c, redMsgs P gK van c.1.1.2 m) (T₂ c m))
      rw [hsimT₂ c hc, hT₂ c hc m])

end Model

/-! ## One table's factorization, the weights and the encoding reading the rest -/

section Table

variable {K E ι Y Q : Type} [Field K] [Field E] [Algebra K E]
  [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q] [DecidableEq Q]

/-- `factors_table` with weights `Wc a` and an encoding `enc a` that read the rest `a` of the
randomness (the five values, and through them the masks). -/
theorem factors_tableV [Fintype K] [DecidableEq K] [FiniteDimensional K E]
    [SampleableType (ι → Y → K)] (h3 : finrank K E = 3) {Sx A I Ob Mm Kt Xt : Type} [Inhabited I]
    [SampleableType Sx] [SampleableType A] (P : Proto Sx I Ob Mm Kt Xt) (σ : List Ob)
    (Ev : Sx → Prop) (L : GadgetLayout ι Y) (pos : ι → (Fin 6 → Bool)) {m : ℕ}
    (Wc : A → Fin m → ι → Y → E) (hW : ∀ a, L.WeightsFit (Wc a)) (β : Fin 3 → E)
    (lam : Fin (m + 1) → E) (φ : Fin 6 → E) (enc : A → Q → Y → K) (e : Sx ≃ A × (ι → Y → K))
    (base : A → ι → Y → K)
    (Φ : A → (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → View Mm I Kt Xt)
    (hview : ∀ s, P.view s σ = Φ (e s).1 (Gadget.levelMap L pos (Wc (e s).1) β lam φ
      (enc (e s).1) (base (e s).1 + L.stackR (e s).2)))
    (x₀ x₁ u : Y → K) (hu : ∀ y ∉ L.first, u y = 0) (huQ : ∀ a q, ∑ y, enc a q y * u y = 0)
    (hu₀ : ∑ y, x₀ y * u y = 1) (hu₁ : ∑ y, x₁ y * u y = 0) (z : A → ι → K)
    (hev : ∀ s, Ev s → Deployed.rowAt x₀ (base (e s).1 + L.stackR (e s).2) -
      Deployed.rowAt x₁ (base (e s).1 + L.stackR (e s).2) = z (e s).1) :
    Nonempty (Deployed.Factors P σ Ev
      ((Fintype.card K ^ (Fintype.card ι - 3) : ℕ) : ℝ≥0∞)⁻¹) := by
  classical
  refine ⟨Deployed.Factors.mk (A := A) (B := ι → Y → K)
    (U := (Fin 6 → E × E) × (Y → E) × (Q → ι → K)) e Φ
    (fun a b => Gadget.levelMap L pos (Wc a) β lam φ (enc a) (base a + L.stackR b))
    (fun a b => Ev (e.symm (a, b))) hview (fun s => by simp) ?_⟩
  intro a v
  have hWb := Gadget.combinedW_first L pos (Wc a) (hW a) β lam
  have hmono : Pr{let b ← $ᵗ (ι → Y → K)}[Gadget.levelMap L pos (Wc a) β lam φ (enc a)
        (base a + L.stackR b) = v ∧ Ev (e.symm (a, b))] ≤
      Pr{let b ← $ᵗ (ι → Y → K)}[Gadget.levelMap L pos (Wc a) β lam φ (enc a)
        (base a + L.stackR b) = v ∧
        Deployed.rowAt x₀ (base a + L.stackR b) - Deployed.rowAt x₁ (base a + L.stackR b) =
          z a] := by
    refine prEvent_mono _ _ _ fun b h => ⟨h.1, ?_⟩
    have := hev (e.symm (a, b)) h.2
    simpa using this
  refine hmono.trans ?_
  exact Deployed.hidden_hδ h3 L.first L.stackR (Deployed.gadget_stackR_of_onFirst L)
    (roundsMap pos φ (HiddenLayout.combinedW pos (Gadget.claimsW L pos (Wc a) β) lam))
    (fun T hT => roundsMap_eq_zero pos φ _ L.first hWb T hT) (HiddenLayout.foldW pos φ) (enc a)
    x₀ x₁ u hu (huQ a) hu₀ hu₁ base z a v

end Table

/-! ## The link between a prover and the model -/

section Link

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]

/-- The witness table's stack, at challenges `c`, for the randomness `s`. -/
def stackV₁ (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K) (L : GadgetLayout ι₁ Y₁)
    (c : Chal E Γ₁ Γ₂ Γw) (s : Rand K ι₁ Y₁ ι₂ Y₂) : ι₁ → Y₁ → K :=
  L.stackD (T₁ c s.1) + L.stackR s.2.1

/-- The quotient table's stack. -/
def stackV₂ (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K) (L : GadgetLayout ι₂ Y₂)
    (c : Chal E Γ₁ Γ₂ Γw) (s : Rand K ι₁ Y₁ ι₂ Y₂) : ι₂ → Y₂ → K :=
  L.stackD (T₂ c s.1) + L.stackR s.2.2

/-- **A prover that is the model `modelV`** (`Link` for it): its view is a public function of the
joint view at the challenges its oracle answers give; its unopened leaves are injective encodings
of its stacks' rows, each with a free vector at every value of the five values ((Q) for the
unopened rows). -/
structure LinkV {I Ob Mm Xt : Type} [Inhabited I]
    (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) I Ob Mm (Fin 2) Xt)
    (P₀ : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (wir : Chal E Γ₁ Γ₂ Γw → W)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂) where
  chOf : List Ob → Chal E Γ₁ Γ₂ Γw
  out : List Ob → Vals E × W × O₁ × O₂ → View Mm I (Fin 2) Xt
  hview : ∀ s σ, P.view s σ = out σ ((modelV P₀ gK van wir T₁ T₂ S₁ S₂).view (chOf σ) s)
  enc₁ : (ι₁ → K) → I
  enc₂ : (ι₂ → K) → I
  inj₁ : Function.Injective enc₁
  inj₂ : Function.Injective enc₂
  code₁ : List Ob → Xt → Y₁ → K
  code₂ : List Ob → Xt → Y₂ → K
  rows₁ : ∀ s σ x, P.opened σ 0 x = false →
    P.rows s σ 0 x = enc₁ (Deployed.rowAt (code₁ σ x) (stackV₁ T₁ S₁.L (chOf σ) s))
  rows₂ : ∀ s σ x, P.opened σ 1 x = false →
    P.rows s σ 1 x = enc₂ (Deployed.rowAt (code₂ σ x) (stackV₂ T₂ S₂.L (chOf σ) s))
  free₁ : ∀ σ x, P.opened σ 0 x = false →
    ∃ u, (∀ v, FreeVec S₁.L.first (S₁.enc (chOf σ, v)) u) ∧ ∑ y, code₁ σ x y * u y = 1
  free₁₂ : ∀ σ x x', P.opened σ 0 x = false → P.opened σ 0 x' = false → x ≠ x' →
    ∃ u, (∀ v, FreeVec S₁.L.first (S₁.enc (chOf σ, v)) u) ∧ ∑ y, code₁ σ x y * u y = 1 ∧
      ∑ y, code₁ σ x' y * u y = 0
  free₂ : ∀ σ x, P.opened σ 1 x = false →
    ∃ u, (∀ v, FreeVec S₂.L.first (S₂.enc (chOf σ, v)) u) ∧ ∑ y, code₂ σ x y * u y = 1
  free₂₂ : ∀ σ x x', P.opened σ 1 x = false → P.opened σ 1 x' = false → x ≠ x' →
    ∃ u, (∀ v, FreeVec S₂.L.first (S₂.enc (chOf σ, v)) u) ∧ ∑ y, code₂ σ x y * u y = 1 ∧
      ∑ y, code₂ σ x' y * u y = 0

variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  {I Ob Mm Xt : Type} [Inhabited I]
  {P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) I Ob Mm (Fin 2) Xt} {P₀ : Params E} {gK : Fin 4 → K[X]}
  {van : K[X]} {wir : Chal E Γ₁ Γ₂ Γw → W}
  {T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K}
  {T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K}
  {S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁}
  {S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂}

/-- Through the witness table. -/
theorem factorsV₁ (hS₁ : S₁.Conditions) (h3 : finrank K E = 3)
    (lk : LinkV P P₀ gK van wir T₁ T₂ S₁ S₂) (σ : List Ob) (Ev : Rand K ι₁ Y₁ ι₂ Y₂ → Prop)
    (x₀ x₁ u : Y₁ → K) (hu : ∀ v, FreeVec S₁.L.first (S₁.enc (lk.chOf σ, v)) u)
    (hu₀ : ∑ y, x₀ y * u y = 1) (hu₁ : ∑ y, x₁ y * u y = 0)
    (z : (Fin 4 → Fin 3 → K) × (ι₂ → Y₂ → K) → ι₁ → K)
    (hev : ∀ s, Ev s → Deployed.rowAt x₀ (stackV₁ T₁ S₁.L (lk.chOf σ) s) -
      Deployed.rowAt x₁ (stackV₁ T₁ S₁.L (lk.chOf σ) s) = z (s.1, s.2.2)) :
    Nonempty (Deployed.Factors P σ Ev
      ((Fintype.card K ^ (Fintype.card ι₁ - 3) : ℕ) : ℝ≥0∞)⁻¹) := by
  set c := lk.chOf σ
  exact factors_tableV h3 P σ Ev S₁.L S₁.pos (fun a => S₁.Wc (c, redMsgs P₀ gK van c.1.1.2 a.1))
    (fun a => hS₁.weightsFit _) S₁.β (Gadget.powers S₁.m (lam₁ c)) (phi₁ c)
    (fun a => S₁.enc (c, redMsgs P₀ gK van c.1.1.2 a.1)) split₁
    (fun a => S₁.L.stackD (T₁ c a.1))
    (fun a lv => lk.out σ (redMsgs P₀ gK van c.1.1.2 a.1, wir c,
      S₁.rest (c, redMsgs P₀ gK van c.1.1.2 a.1) lv,
      S₂.view lamV₂ phiV₂ (c, redMsgs P₀ gK van c.1.1.2 a.1) (T₂ c a.1) a.2))
    (fun s => lk.hview s σ) x₀ x₁ u (hu (redMsgs P₀ gK van c.1.1.2 0)).1
    (fun a => (hu _).2) hu₀ hu₁ z (fun s h => hev s h)

/-- Through the quotient table. -/
theorem factorsV₂ (hS₂ : S₂.Conditions) (h3 : finrank K E = 3)
    (lk : LinkV P P₀ gK van wir T₁ T₂ S₁ S₂) (σ : List Ob) (Ev : Rand K ι₁ Y₁ ι₂ Y₂ → Prop)
    (x₀ x₁ u : Y₂ → K) (hu : ∀ v, FreeVec S₂.L.first (S₂.enc (lk.chOf σ, v)) u)
    (hu₀ : ∑ y, x₀ y * u y = 1) (hu₁ : ∑ y, x₁ y * u y = 0)
    (z : (Fin 4 → Fin 3 → K) × (ι₁ → Y₁ → K) → ι₂ → K)
    (hev : ∀ s, Ev s → Deployed.rowAt x₀ (stackV₂ T₂ S₂.L (lk.chOf σ) s) -
      Deployed.rowAt x₁ (stackV₂ T₂ S₂.L (lk.chOf σ) s) = z (s.1, s.2.1)) :
    Nonempty (Deployed.Factors P σ Ev
      ((Fintype.card K ^ (Fintype.card ι₂ - 3) : ℕ) : ℝ≥0∞)⁻¹) := by
  set c := lk.chOf σ
  exact factors_tableV h3 P σ Ev S₂.L S₂.pos (fun a => S₂.Wc (c, redMsgs P₀ gK van c.1.1.2 a.1))
    (fun a => hS₂.weightsFit _) S₂.β (Gadget.powers S₂.m (lam₂ c)) (phi₂ c)
    (fun a => S₂.enc (c, redMsgs P₀ gK van c.1.1.2 a.1)) split₂
    (fun a => S₂.L.stackD (T₂ c a.1))
    (fun a lv => lk.out σ (redMsgs P₀ gK van c.1.1.2 a.1, wir c,
      S₁.view lamV₁ phiV₁ (c, redMsgs P₀ gK van c.1.1.2 a.1) (T₁ c a.1) a.2,
      S₂.rest (c, redMsgs P₀ gK van c.1.1.2 a.1) lv))
    (fun s => lk.hview s σ) x₀ x₁ u (hu (redMsgs P₀ gK van c.1.1.2 0)).1
    (fun a => (hu _).2) hu₀ hu₁ z (fun s h => hev s h)

/-- **`Factors` for every unopened leaf**, `δ = 2^-2368`. -/
theorem factors_singleV (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions) (h3 : finrank K E = 3)
    (hK : Fintype.card K = 2 ^ 64) (h40₁ : 40 ≤ Fintype.card ι₁) (h40₂ : 40 ≤ Fintype.card ι₂)
    (lk : LinkV P P₀ gK van wir T₁ T₂ S₁ S₂) :
    ∀ σ k x, P.opened σ k x = false → ∀ y,
      Nonempty (Deployed.Factors P σ (fun s => P.rows s σ k x = y) ((2 : ℝ≥0∞) ^ 2368)⁻¹) := by
  intro σ k x hx y
  fin_cases k
  · obtain ⟨u, hu, hu₀⟩ := lk.free₁ σ x hx
    obtain ⟨F⟩ := factorsV₁ hS₁ h3 lk σ (fun s => P.rows s σ 0 x = y) (lk.code₁ σ x) 0 u hu hu₀
      (by simp) (fun _ => preimage lk.enc₁ y) (fun s h => by
        rw [rowAt_zero, sub_zero]
        exact (preimage_eq lk.inj₁ ((lk.rows₁ s σ x hx).symm.trans h)).symm)
    exact ⟨factorsMono F (delta_le hK ι₁ h40₁)⟩
  · obtain ⟨u, hu, hu₀⟩ := lk.free₂ σ x hx
    obtain ⟨F⟩ := factorsV₂ hS₂ h3 lk σ (fun s => P.rows s σ 1 x = y) (lk.code₂ σ x) 0 u hu hu₀
      (by simp) (fun _ => preimage lk.enc₂ y) (fun s h => by
        rw [rowAt_zero, sub_zero]
        exact (preimage_eq lk.inj₂ ((lk.rows₂ s σ x hx).symm.trans h)).symm)
    exact ⟨factorsMono F (delta_le hK ι₂ h40₂)⟩

/-- **`Factors` for every pair of unopened leaves**, `δ₂ = 2^-2368`. -/
theorem factors_pairV (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions) (h3 : finrank K E = 3)
    (hK : Fintype.card K = 2 ^ 64) (h40₁ : 40 ≤ Fintype.card ι₁) (h40₂ : 40 ≤ Fintype.card ι₂)
    (lk : LinkV P P₀ gK van wir T₁ T₂ S₁ S₂) :
    ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false → (k, x) ≠ (k', x') →
      Nonempty (Deployed.Factors P σ (fun s => P.rows s σ k x = P.rows s σ k' x')
        ((2 : ℝ≥0∞) ^ 2368)⁻¹) := by
  intro σ k x k' x' hx hx' hne
  fin_cases k <;> fin_cases k'
  · have hxx : x ≠ x' := fun h => hne (by simp [h])
    obtain ⟨u, hu, hu₀, hu₁⟩ := lk.free₁₂ σ x x' hx hx' hxx
    obtain ⟨F⟩ := factorsV₁ hS₁ h3 lk σ (fun s => P.rows s σ 0 x = P.rows s σ 0 x')
      (lk.code₁ σ x) (lk.code₁ σ x') u hu hu₀ hu₁ (fun _ => 0) (fun s h => by
        rw [lk.rows₁ s σ x hx, lk.rows₁ s σ x' hx'] at h
        rw [lk.inj₁ h, sub_self])
    exact ⟨factorsMono F (delta_le hK ι₁ h40₁)⟩
  · obtain ⟨u, hu, hu₀⟩ := lk.free₁ σ x hx
    obtain ⟨F⟩ := factorsV₁ hS₁ h3 lk σ (fun s => P.rows s σ 0 x = P.rows s σ 1 x')
      (lk.code₁ σ x) 0 u hu hu₀ (by simp)
      (fun a => preimage lk.enc₁ (lk.enc₂ (Deployed.rowAt (lk.code₂ σ x')
        (S₂.L.stackD (T₂ (lk.chOf σ) a.1) + S₂.L.stackR a.2))))
      (fun s h => by
        rw [rowAt_zero, sub_zero]
        rw [lk.rows₁ s σ x hx, lk.rows₂ s σ x' hx'] at h
        exact (preimage_eq lk.inj₁ h).symm)
    exact ⟨factorsMono F (delta_le hK ι₁ h40₁)⟩
  · obtain ⟨u, hu, hu₀⟩ := lk.free₂ σ x hx
    obtain ⟨F⟩ := factorsV₂ hS₂ h3 lk σ (fun s => P.rows s σ 1 x = P.rows s σ 0 x')
      (lk.code₂ σ x) 0 u hu hu₀ (by simp)
      (fun a => preimage lk.enc₂ (lk.enc₁ (Deployed.rowAt (lk.code₁ σ x')
        (S₁.L.stackD (T₁ (lk.chOf σ) a.1) + S₁.L.stackR a.2))))
      (fun s h => by
        rw [rowAt_zero, sub_zero]
        rw [lk.rows₂ s σ x hx, lk.rows₁ s σ x' hx'] at h
        exact (preimage_eq lk.inj₂ h).symm)
    exact ⟨factorsMono F (delta_le hK ι₂ h40₂)⟩
  · have hxx : x ≠ x' := fun h => hne (by simp [h])
    obtain ⟨u, hu, hu₀, hu₁⟩ := lk.free₂₂ σ x x' hx hx' hxx
    obtain ⟨F⟩ := factorsV₂ hS₂ h3 lk σ (fun s => P.rows s σ 1 x = P.rows s σ 1 x')
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
(`Instance/Nondeg.lean`: `hT₁`, `hT₂` under `ClaimsND` only, `εhv = 2^-165 + 2^-125`,
`εz = 2/2^192`). (`hT₁`, `hT₂` here ask the honest tables' claims at every mask, with no
`ClaimsND`.)

**`JointHVZK`** for a prover that is the model `modelV`, at our sizes: `εhv = 2^-165`. -/
theorem jointHVZK_of_linkV {I Ob Mm Xt : Type} [DecidableEq I] [Inhabited I] [SampleableType Ob]
    [Inhabited Ob] [DecidableEq Xt] (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) I Ob Mm (Fin 2) Xt)
    (h3 : finrank K E = 3) (P₀ : Params E) (hE : P₀.Exact) (stmt : Fin P₀.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P₀.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22)
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P₀ gK van c → ∀ m,
      S₁.claims (c, redMsgs P₀ gK van c.1.1.2 m) (T₁ c m) = cl₁ c (redMsgs P₀ gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P₀ gK van c → ∀ m,
      S₂.claims (c, redMsgs P₀ gK van c.1.1.2 m) (T₂ c m) = cl₂ c (redMsgs P₀ gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P₀ gK van c → ∀ v, S₁.claims (c, v) (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P₀ gK van c → ∀ v, S₂.claims (c, v) (simT₂ c v) = cl₂ c v)
    (lk : LinkV P P₀ gK van wir T₁ T₂ S₁ S₂)
    (hch : lk.chOf <$> uniformList Ob P.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw))) :
    Deployed.JointHVZK P
      (fun σ => lk.out σ <$> jointSimV inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
      (fun σ => good P₀ gK van (lk.chOf σ)) (1 / 2 ^ 165) :=
  ⟨hzk_of_factor P lk.chOf (modelV P₀ gK van wir T₁ T₂ S₁ S₂).view lk.out lk.hview
      (jointSimV inK sigmaAt wir S₁ S₂ simT₁ simT₂) (good P₀ gK van)
      (joint_hzkV h3 P₀ hE stmt gK van hvan hsat inK hinK sigmaAt hsig wir S₁ S₂ hS₁ hS₂ T₁ T₂
        cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂),
    hgood_of_uniform P.n lk.chOf hch (good P₀ gK van) _
      (joint_hgood_bits P₀ gK van hvan0 hq hK hN hdeg)⟩

open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec Proof) in
open QuotientZk.Deployed.Fresh in
/-- **Superseded**: its hypotheses `hT₁`/`hT₂` are not met by the honest tables at degenerate
challenges/masks; the deployed result is `zeroKnowledge_closed` through `jointHVZKε_of_linkV`
(`Instance/Nondeg.lean`). (`hT₁`, `hT₂` ask the honest tables' claims at every mask, with no
`ClaimsND`.)

**Zero knowledge of the deployed proof in the random-permutation model, for the model
`modelV`, `FSFresh` discharged**: `zk_rpm_deployed_joint_fs'` (`FreshJoint.lean`) with the openings
reading the five values. For a prover whose leaf rows are byte strings longer than 192 bytes
(`ofBytes Pb`), that meets `fsFresh_deployed_bits`'s conditions and is the model `modelV`
(`LinkV`), every distinguisher of at most `QD ≤ 2^127` queries of `π` and `π⁻¹`, the real game
making at most `Q` permutation calls, has advantage at most
`2^-54 + 2^-165 + 2^-2200 + Q² / 2^508`. -/
theorem zk_rpm_deployed_jointV_fs' (stmtD : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19) (sh : Deployed.Shape)
    (hsh : sh = Deployed.deployedShape stmtD idW idσ idQ rowsW)
    (Pb : Proto (Rand K ι₁ Y₁ ι₂ Y₂) (List UInt8) Out Msg Tbl Pos)
    (QD Q : ℕ) (hQD : QD ≤ 2 ^ 127)
    (cw : Fin 3 → QuotientRpm.Bytes32 → List UInt8)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ (Rand K ι₁ Y₁ ι₂ Y₂)}[(DRpm.ofBytes Pb).rowFn s [] 0 0 = y] ≤
      ((2 : ℝ≥0∞) ^ 2368)⁻¹)
    (hlong : ∀ s h k x, 192 < (Pb.rowFn s h k x).length) (hcK : Pb.cK 0 = 0)
    (hclW : ClaimsAt (DRpm.ofBytes Pb) 5 4 (cw 0)) (hclσ : ClaimsAt (DRpm.ofBytes Pb) 128 3 (cw 1))
    (hclQ : ClaimsAt (DRpm.ofBytes Pb) 242 3 (cw 2)) (hn : 242 ≤ Pb.n)
    (h3 : finrank K E = 3) (P₀ : Params E) (hE : P₀.Exact) (stmt : Fin P₀.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P₀.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22) (h40₁ : 40 ≤ Fintype.card ι₁) (h40₂ : 40 ≤ Fintype.card ι₂)
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P₀ gK van c → ∀ m,
      S₁.claims (c, redMsgs P₀ gK van c.1.1.2 m) (T₁ c m) = cl₁ c (redMsgs P₀ gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P₀ gK van c → ∀ m,
      S₂.claims (c, redMsgs P₀ gK van c.1.1.2 m) (T₂ c m) = cl₂ c (redMsgs P₀ gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P₀ gK van c → ∀ v, S₁.claims (c, v) (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P₀ gK van c → ∀ v, S₂.claims (c, v) (simT₂ c v) = cl₂ c v)
    (lk : LinkV (DRpm.ofBytes Pb) P₀ gK van wir T₁ T₂ S₁ S₂)
    (hch : lk.chOf <$> uniformList Out Pb.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw)))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost (DRpm.zkGameRpmD (DRpm.ofBytes Pb) (Deployed.skel sh) D s)
      Common.permutationCallCost Q) :
    Close (DRpm.realGameRpmD (DRpm.ofBytes Pb) (Deployed.skel sh) D)
      (DRpm.simGameRpmD (DRpm.ofBytes Pb)
        (fun σ => lk.out σ <$> jointSimV inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
        (Deployed.skel sh) D)
      (((2 : ℝ≥0∞) ^ 54)⁻¹ + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹ + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) :=
  DRpm.zk_rpm_deployed_bits' stmtD idW idσ idQ rowsW hrows sh hsh Pb _ _ _ (1 / 2 ^ 165) QD Q hQD
    (by rw [hsh]; exact (fsFresh_deployed_bits stmtD idW idσ idQ rowsW hrows (DRpm.ofBytes Pb) []
      (Nat.zero_le _) cw hcw hrow₀ (fun s h k x => ⟨_, rfl, hlong s h k x⟩) hcK hclW hclσ hclQ hn))
    (jointHVZK_of_linkV (DRpm.ofBytes Pb) h3 P₀ hE stmt gK van hvan hsat hvan0 hq hK hN hdeg inK
      hinK sigmaAt hsig wir S₁ S₂ hS₁ hS₂ T₁ T₂ cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂ lk hch)
    (factors_singleV hS₁ hS₂ h3 hK h40₁ h40₂ lk) (factors_pairV hS₁ hS₂ h3 hK h40₁ h40₂ lk)
    D hD hQ

end Final

end QuotientZk.Instance
