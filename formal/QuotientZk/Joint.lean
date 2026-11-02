-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.JointReduction
import QuotientZk.JointGadget
import QuotientZk.Rom.Main

/-!
# Joint honest-verifier zero knowledge of the whole interactive protocol

The interactive protocol of `crates/quotient` at challenges `c` shows the honest verifier the
reduction's five field elements (`redMsgs`, the claims being the verifier's functions of them), the
public wiring table's opening, and the two secret tables' WHIR openings (`SecretOpening.view`: F3's
level-0 view on a `GadgetLayout` stack, and everything WHIR shows after the first fold, `rest`, a
function of it and the challenges). The prover's randomness is `s = (masks, padding₁, padding₂)`,
uniform: `Mk × (ι₁ → Y₁ → K) × (ι₂ → Y₂ → K)`.

The challenges (`Chal`): `(((α, β, γ), t), ρ)` of the reduction, then for each secret opening
`((λ, ·), φ)` (the claims' batching challenge, the rest of its challenges, the six lane-fold
challenges), and the wiring opening's.

* **`joint_hzk`** (`zk_rom`'s `hzk`): at every good challenge (`good`: F1's `Good` and each
  opening's `GoodCh`), the honest view under uniform `s` has exactly the distribution of `jointSim`.
* **`joint_hgood`** (`zk_rom`'s `hgood`): uniform challenges are not good with probability at most
  `zkError + 2·((12|E| + 3|K|²)/|E|² + 1/|E|)`; **`joint_hgood_bits`**: `≤ 2^-165` at our sizes
  (`zkError ≤ 3·2^24/2^192 < 2^-166`, each opening `13·2^-192 + 3·2^-256 < 2^-188`).
* **`zk_rom_of_joint`**: `zk_rom` with these, for a `Proto` whose view is a public function of the
  joint view at the challenges the oracle's answers give (`hview`, `hch`): the instantiation's
  remaining obligations are `zk_rom`'s own (`hFS`, `hent`, `hent₂`).

**The simulator** `jointSim` is a plain (compiled, not `noncomputable`) definition from the
statement's public data and the challenges: `simRed` (four values uniform in `E`, or `K` when the
row `t^4 + t` lies in `K`, tested by the public `inK`; the wiring value `sigmaAt t`), the public
tables `simT₁ c v`, `simT₂ c v` it builds from the simulated values with the verifier's claims,
opened by the honest WHIR algorithm (`SecretOpening.view`) with fresh paddings, and the wiring
opening `wir c`. Its cost is the honest prover's openings' (two table builds, two level-0 views
and the rest of WHIR) plus four samples and two evaluations. `#print axioms` cannot certify this:
every definition that samples (VCVio's `SampleableType` class carries a measure-theoretic proof)
lists `Classical.choice`; the compiler's acceptance of the `def` is the check, and
`JointAxioms.lean` runs `simulate` and `simRed` (`OracleComp.runIO`).

**Hypotheses, named.** F1's: `h3` (`[E : K] = 3`), `hE` (`P.Exact`), `hvan`, `hsat` (the witness
satisfies the relation), `hvan0`. The simulator's public functions: `hinK`, `hsig`. Each secret
opening's `SecretOpening.Conditions`: **(Q)** `condQ`, **`WeightsFit`** `weightsFit`, and the
layout's lanes (`placed`, `lowHalf`, `cubeRand`: the gadget's pairs and overflow lane, the lower half
of the lane indices and the cube `32 .. 40` on the stack, its lanes but `32` random). The claims:
`hT₁`, `hT₂` (the honest tables meet the verifier's claims `cl₁`, `cl₂`, computed from the five
values: completeness of the layouts) and `hsimT₁`, `hsimT₂` (the simulator's tables meet them).
Condition (S) and condition (R) are **not** hypotheses: they hold at every good challenge
(`Gadget.view_evalDistEq_of_good`, from `GadgetLayout.roundsReached` and the cube lemma).
-/

open OracleComp Polynomial Module QuotientSecurity QuotientSecurity.Hiding
open scoped NNReal

namespace QuotientZk.Joint

set_option linter.unusedSectionVars false

/-! ## A secret table's opening -/

/-- **A secret table's opening, as deployed**: its hidden layout with the gadget (`L`, lane indices
`pos`), its `m` claims' weights (functions of the challenges), the gadget's coefficients `β` (`1, t, t²`, a basis of `E` over
`K`), the opened positions' encoding (`enc`), and what WHIR shows after the first fold (`rest`), a
function of the level-0 view and the challenges. -/
structure SecretOpening (K E Ch ι Y Q O : Type) [Field K] [Field E] [Algebra K E] where
  L : GadgetLayout ι Y
  pos : ι → (Fin 6 → Bool)
  m : ℕ
  Wc : Ch → Fin m → ι → Y → E
  β : Fin 3 → E
  enc : Ch → Q → Y → K
  rest : Ch → (Fin 6 → E × E) × (Y → E) × (Q → ι → K) → O

variable {K E Ch ι Y Q O : Type} [Field K] [Field E] [Algebra K E]
  [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q] [DecidableEq Q]

namespace SecretOpening

variable (S : SecretOpening K E Ch ι Y Q O)

/-- The opening's view of table `d` with padding `r`, at the batching challenge `lamOf c` and the
lane-fold challenges `φOf c`. -/
def view (lamOf : Ch → E) (φOf : Ch → Fin 6 → E) (c : Ch) (d r : ι → Y → K) : O :=
  S.rest c (Gadget.levelMap S.L S.pos (S.Wc c) S.β (Gadget.powers S.m (lamOf c)) (φOf c) (S.enc c)
    (S.L.stackD d + S.L.stackR r))

/-- The claims the opening proves of table `d`. -/
def claims (c : Ch) (d : ι → Y → K) : Fin S.m → E :=
  HiddenLayout.claimsMap (S.Wc c) (S.L.stackD d)

/-- **The opening's hypotheses**: (Q), `WeightsFit`, and the layout's lanes. -/
structure Conditions : Prop where
  /-- The gadget's pairs `(0, 31)`, `(1, 30)` and overflow lane `32`, `pos` injective. -/
  placed : Gadget.Placed S.L S.pos
  /-- The pairs' first lanes are not random lanes. -/
  pairANotRand : ∀ p, ¬ S.L.isRand (S.L.pairA p)
  /-- The lower half of the lane indices is on the stack. -/
  lowHalf : ∀ b : Fin 6 → Bool, b (Fin.last 5) = false → b ∈ Set.range S.pos
  /-- Lanes `32 .. 40` are on the stack. -/
  cubeOn : ∀ l : Fin 64, 32 ≤ (l : ℕ) → (l : ℕ) < 40 → lane l ∈ Set.range S.pos
  /-- Lanes `33 .. 40` (the cube `32 .. 40` but `32`) are random lanes. -/
  cubeRand : ∀ b ∈ cube true, b ≠ lane 32 → ∃ r, S.pos r = b ∧ S.L.isRand r
  /-- **`WeightsFit`**: the claims weigh nothing of the randomness or of the gadget's entries. -/
  weightsFit : ∀ c, S.L.WeightsFit (S.Wc c)
  /-- **(Q)**: the entries below the gadget take every value at the opened positions. -/
  condQ : ∀ c, Function.Surjective (firstEval (S.enc c) S.L.first)
  /-- The gadget's coefficients are a basis of `E` over `K` (`1, t, t²`). -/
  basis : ∃ b : Module.Basis (Fin 3) K E, ⇑b = S.β

/-- The opening hides its table given its claims at every good challenge
(`GadgetLayout.view_evalDistEq`). -/
theorem hides [CharP E 2] [FiniteDimensional K E] [SampleableType (ι → Y → K)]
    (h3 : finrank K E = 3) (hS : S.Conditions) (lamOf : Ch → E) (φOf : Ch → Fin 6 → E) (c : Ch)
    (hc : Gadget.GoodCh (K := K) (φOf c) (lamOf c)) :
    Hides (S.view lamOf φOf) S.claims c := by
  intro d d' hd
  obtain ⟨b, hb⟩ := hS.basis
  have h := Gadget.view_evalDistEq_of_good S.L h3 S.pos hS.placed hS.pairANotRand hS.lowHalf
    hS.cubeOn hS.cubeRand (S.Wc c) (hS.weightsFit c) b (S.enc c) (hS.condQ c) (lamOf c) (φOf c) hc
    (S.rest c) hd
  rw [hb] at h
  exact h

end SecretOpening

/-! ## The joint protocol -/

/-- The challenges: the reduction's `(((α, β, γ), t), ρ)`, each secret opening's `((λ, ·), φ)`,
the wiring opening's. -/
abbrev Chal (E Γ₁ Γ₂ Γw : Type) :=
  (((E × E × E) × E) × E) × ((E × Γ₁) × (Fin 6 → E)) × ((E × Γ₂) × (Fin 6 → E)) × Γw

section Joint

variable {Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]

/-- The witness opening's batching challenge `λ` and lane-fold challenges `φ`. -/
abbrev lam₁ (c : Chal E Γ₁ Γ₂ Γw) : E := c.2.1.1.1
abbrev phi₁ (c : Chal E Γ₁ Γ₂ Γw) : Fin 6 → E := c.2.1.2
/-- The quotient opening's. -/
abbrev lam₂ (c : Chal E Γ₁ Γ₂ Γw) : E := c.2.2.1.1.1
abbrev phi₂ (c : Chal E Γ₁ Γ₂ Γw) : Fin 6 → E := c.2.2.1.2

variable [DecidableEq E] [CharP E 2] [Fintype E]

/-- **The honest protocol's joint model**: the reduction's messages from the masks, the wiring
opening, the two secret tables (`T₁`, `T₂`: the honest prover's stacks' tables, from the masks and
the witness) and their openings. -/
noncomputable def model (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (wir : Chal E Γ₁ Γ₂ Γw → W)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂) :
    Model (Chal E Γ₁ Γ₂ Γw) (Fin 4 → Fin 3 → K) (ι₁ → Y₁ → K) (ι₂ → Y₂ → K) ((Fin 4 → E) × E) W
      (ι₁ → Y₁ → K) (ι₂ → Y₂ → K) O₁ O₂ (Fin S₁.m → E) (Fin S₂.m → E) where
  red c := redMsgs P gK van c.1.1.2
  wir := wir
  tab₁ := T₁
  tab₂ := T₂
  open₁ := S₁.view lam₁ phi₁
  open₂ := S₂.view lam₂ phi₂
  cl₁ := S₁.claims
  cl₂ := S₂.claims

/-- **The simulator**, from the challenges and public data only. -/
def jointSim [SampleableType K] [SampleableType E] [SampleableType (ι₁ → Y₁ → K)]
    [SampleableType (ι₂ → Y₂ → K)] (inK : E → Bool) (sigmaAt : E → E)
    (wir : Chal E Γ₁ Γ₂ Γw → W) (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (simT₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₂ → Y₂ → K) (c : Chal E Γ₁ Γ₂ Γw) :
    ProbComp (((Fin 4 → E) × E) × W × O₁ × O₂) :=
  simulate wir (S₁.view lam₁ phi₁) (S₂.view lam₂ phi₂)
    (fun c => simRed (K := K) inK sigmaAt c.1.1.2) simT₁ simT₂ c

/-- **The good challenges**: F1's for the witness, and each secret opening's `GoodCh`. -/
def good (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (c : Chal E Γ₁ Γ₂ Γw) : Prop :=
  Good (P := P) gK van c.1.1.1 c.1.1.2 ∧ Gadget.GoodCh (K := K) (phi₁ c) (lam₁ c) ∧
    Gadget.GoodCh (K := K) (phi₂ c) (lam₂ c)

variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]

/-- **Joint honest-verifier zero knowledge** (`zk_rom`'s `hzk`): at every good challenge, the whole
honest view — the five field elements, the wiring opening, the two secret openings — under uniform
masks and paddings has the distribution of `jointSim`. -/
theorem joint_hzk (h3 : finrank K E = 3) (P : Params E) (hE : P.Exact) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0)))
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P gK van c → ∀ m, S₁.claims c (T₁ c m) = cl₁ c (redMsgs P gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P gK van c → ∀ m, S₂.claims c (T₂ c m) = cl₂ c (redMsgs P gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P gK van c → ∀ v, S₁.claims c (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P gK van c → ∀ v, S₂.claims c (simT₂ c v) = cl₂ c v) :
    ∀ c, good P gK van c →
      (model P gK van wir T₁ T₂ S₁ S₂).view c <$>
          ($ᵗ ((Fin 4 → Fin 3 → K) × (ι₁ → Y₁ → K) × (ι₂ → Y₂ → K)))
        =ᵈ jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂ c := by
  intro c hc
  exact view_evalDistEq (model P gK van wir T₁ T₂ S₁ S₂)
    (fun c => simRed (K := K) inK sigmaAt c.1.1.2) simT₁ simT₂ c
    (redMsgs_evalDistEq P h3 hE stmt gK van hvan hsat inK hinK sigmaAt hsig c.1.1.1 c.1.1.2 hc.1)
    (S₁.hides h3 hS₁ lam₁ phi₁ c hc.2.1) (S₂.hides h3 hS₂ lam₂ phi₂ c hc.2.2)
    (fun m => (hsimT₁ c hc _).trans (hT₁ c hc m).symm)
    (fun m => (hsimT₂ c hc _).trans (hT₂ c hc m).symm)

variable [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **The bad challenges** (`zk_rom`'s `hgood`): F1's, and each secret opening's. -/
theorem joint_hgood (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (hvan0 : van ≠ 0) :
    Pr{let c ← $ᵗ (Chal E Γ₁ Γ₂ Γw)}[¬ good P gK van c] ≤
      (zkError P van : ENNReal) +
        (((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
            ((Fintype.card E ^ 2 : ℕ) : ENNReal) + 1 / (Fintype.card E : ENNReal) +
          (((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
            ((Fintype.card E ^ 2 : ℕ) : ENNReal) + 1 / (Fintype.card E : ENNReal))) := by
  classical
  refine (prEvent_not_and_le _ _ _).trans (add_le_add ?_
    ((prEvent_not_and_le _ _ _).trans (add_le_add ?_ ?_)))
  · -- F1's challenges
    refine le_trans (le_of_eq (prEvent_uniform_fst (A := ((E × E × E) × E) × E)
      (fun x => ¬ Good (P := P) gK van x.1.1 x.1.2))) ?_
    refine le_trans (le_of_eq (prEvent_uniform_fst (A := (E × E × E) × E)
      (fun x => ¬ Good (P := P) gK van x.1 x.2))) ?_
    exact prob_not_good_le P gK van hvan0
  · -- the witness opening's
    refine le_trans (le_of_eq (prEvent_uniform_snd
      (fun y : ((E × Γ₁) × (Fin 6 → E)) × ((E × Γ₂) × (Fin 6 → E)) × Γw =>
        ¬ Gadget.GoodCh (K := K) y.1.2 y.1.1.1))) ?_
    refine le_trans (le_of_eq (prEvent_uniform_fst
      (fun x : (E × Γ₁) × (Fin 6 → E) => ¬ Gadget.GoodCh (K := K) x.2 x.1.1))) ?_
    exact Gadget.prob_not_goodCh_le
  · -- the quotient opening's
    refine le_trans (le_of_eq (prEvent_uniform_snd
      (fun y : ((E × Γ₁) × (Fin 6 → E)) × ((E × Γ₂) × (Fin 6 → E)) × Γw =>
        ¬ Gadget.GoodCh (K := K) y.2.1.2 y.2.1.1.1))) ?_
    refine le_trans (le_of_eq (prEvent_uniform_snd
      (fun y : ((E × Γ₂) × (Fin 6 → E)) × Γw => ¬ Gadget.GoodCh (K := K) y.1.2 y.1.1.1))) ?_
    refine le_trans (le_of_eq (prEvent_uniform_fst
      (fun x : (E × Γ₂) × (Fin 6 → E) => ¬ Gadget.GoodCh (K := K) x.2 x.1.1))) ?_
    exact Gadget.prob_not_goodCh_le

/-- **`εhv` at our sizes**: `|E| = 2^192`, `|K| = 2^64`, `2^24` cells, `deg van ≤ 2^22`: the
challenges are not good with probability at most `2^-165` (F1's `3·2^24/2^192 < 2^-166`, each
opening's `13·2^-192 + 3·2^-256 < 2^-188`). -/
theorem joint_hgood_bits (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22) :
    Pr{let c ← $ᵗ (Chal E Γ₁ Γ₂ Γw)}[¬ good P gK van c] ≤ 1 / 2 ^ 165 := by
  refine (joint_hgood P gK van hvan0).trans ?_
  have ho : ((2 * 6 * Fintype.card E + 3 * Fintype.card K ^ 2 : ℕ) : ENNReal) /
        ((Fintype.card E ^ 2 : ℕ) : ENNReal) + 1 / (Fintype.card E : ENNReal) ≤ 1 / 2 ^ 188 := by
    rw [hq, hK]
    exact Gadget.goodCh_bound_le
  have hz := zkError_le_166 P hq hN van hdeg
  have h2 : (1 : ENNReal) / 2 ^ 188 + 1 / 2 ^ 188 ≤ 1 / 2 ^ 166 := by
    rw [ENNReal.div_add_div_same]
    have h := HiddenLayout.natCast_div_le_natCast_div (a := 2) (b := 2 ^ 188) (c := 1)
      (d := 2 ^ 166) (by positivity) (by positivity) (by norm_num)
    convert h using 1 <;> norm_num
  have h1 : (1 : ENNReal) / 2 ^ 166 + 1 / 2 ^ 166 ≤ 1 / 2 ^ 165 := by
    rw [ENNReal.div_add_div_same]
    have h := HiddenLayout.natCast_div_le_natCast_div (a := 2) (b := 2 ^ 166) (c := 1)
      (d := 2 ^ 165) (by positivity) (by positivity) (by norm_num)
    convert h using 1 <;> norm_num
  calc _ ≤ (1 : ENNReal) / 2 ^ 166 + (1 / 2 ^ 188 + 1 / 2 ^ 188) := by gcongr
    _ ≤ 1 / 2 ^ 166 + 1 / 2 ^ 166 := by gcongr
    _ ≤ 1 / 2 ^ 165 := h1

end Joint

/-! ## The bridge to `zk_rom` -/

section Bridge

variable {S I Ob Mm Kt Xt Pf JV Ch : Type}

/-- If the protocol's interactive view is a public function of the joint view at the challenges
`chOf σ`, the joint simulator gives `zk_rom`'s `hzk`. -/
theorem hzk_of_factor [Inhabited I] [SampleableType S] (P : Proto S I Ob Mm Kt Xt)
    (chOf : List Ob → Ch) (jv : Ch → S → JV) (out : List Ob → JV → View Mm I Kt Xt)
    (hview : ∀ s σ, P.view s σ = out σ (jv (chOf σ) s)) (simJ : Ch → ProbComp JV)
    (good : Ch → Prop) (hj : ∀ c, good c → jv c <$> ($ᵗ S) =ᵈ simJ c) :
    ∀ σ, good (chOf σ) → (fun s => P.view s σ) <$> ($ᵗ S) =ᵈ (out σ <$> simJ (chOf σ)) := by
  intro σ hσ
  have h : (fun s => P.view s σ) = out σ ∘ jv (chOf σ) := funext fun s => hview s σ
  have h' := (hj _ hσ).map (out σ)
  rw [Functor.map_map] at h'
  rw [h]
  exact h'

/-- If the challenges the oracle's answers give are uniform, the joint bad-challenge bound gives
`zk_rom`'s `hgood`. -/
theorem hgood_of_uniform [SampleableType Ob] [SampleableType Ch] (n : ℕ) (chOf : List Ob → Ch)
    (hch : chOf <$> uniformList Ob n =ᵈ ($ᵗ Ch)) (good : Ch → Prop) (ε : ENNReal)
    (h : Pr{let c ← $ᵗ Ch}[¬ good c] ≤ ε) :
    Pr{let σ ← uniformList Ob n}[¬ good (chOf σ)] ≤ ε := by
  have e := hch.prEvent_eq (fun c => ¬ good c)
  rw [prEvent_map] at e
  rw [e]
  exact h

/-- **`zk_rom` from the joint view**: for a non-interactive prover (`Proto`, `skel`) whose
interactive view is a public function of the joint view (`hview`) at challenges the oracle's
answers give uniformly (`hch`), with the joint honest-verifier zero knowledge (`hj`, e.g.
`joint_hzk`) and bad-challenge bound (`hεhv`, e.g. `joint_hgood_bits`), the real and simulated
games are close. -/
theorem zk_rom_of_joint [DecidableEq I] [SampleableType Ob] [Inhabited Ob] [DecidableEq Kt]
    [DecidableEq Xt] [Inhabited I] [SampleableType S] [SampleableType Ch] [Fintype (Kt × Xt)]
    (P : Proto S I Ob Mm Kt Xt) (skel : OracleComp (OpSpec I Ob Mm Kt Xt) Pf) (c₀ : List (I × Ob))
    (chOf : List Ob → Ch) (jv : Ch → S → JV) (out : List Ob → JV → View Mm I Kt Xt)
    (hview : ∀ s σ, P.view s σ = out σ (jv (chOf σ) s)) (simJ : Ch → ProbComp JV)
    (good : Ch → Prop) (hj : ∀ c, good c → jv c <$> ($ᵗ S) =ᵈ simJ c)
    (hch : chOf <$> uniformList Ob P.n =ᵈ ($ᵗ Ch))
    (εFS εhv δ δ₂ : ENNReal) (QP QD : ℕ) (hεhv : Pr{let c ← $ᵗ Ch}[¬ good c] ≤ εhv)
    (hQP : IsTotalQueryBound skel QP)
    (hFS : Pr{let x ← (do
        let s ← $ᵗ S
        let z ← (simulateQ (implReal P s) skel).run (St.init c₀)
        return z.2.fs)}[x = true] ≤ εFS)
    (hent : ∀ σ k x, P.opened σ k x = false → ∀ v y,
      Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = y] ≤
        δ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hent₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') → ∀ v,
        Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = P.rows s σ k' x'] ≤
          δ₂ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (D : Pf → OracleComp (I →ₒ Ob) Bool) (hD : ∀ π, IsTotalQueryBound (D π) QD) :
    Close (realGame P skel c₀ D) (simGame P (fun σ => out σ <$> simJ (chOf σ)) skel c₀ D)
      (εFS + εhv + ((Fintype.card (Kt × Xt) * (c₀.length + (QP + QD)) : ℕ) * δ +
        (Fintype.card (Kt × Xt) ^ 2 : ℕ) * δ₂)) :=
  zk_rom P skel c₀ (fun σ => out σ <$> simJ (chOf σ)) (fun σ => good (chOf σ)) εFS εhv δ δ₂ QP QD
    hQP hFS (hzk_of_factor P chOf jv out hview simJ good hj)
    (hgood_of_uniform P.n chOf hch good εhv hεhv) hent hent₂ D hD

end Bridge

end QuotientZk.Joint
