-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statements read are `formal/RecStatement`'s
-- (`Pi1HazardKeccakHonest`, `Pi1HazardKeccak`, `RecGraph.MergeHazard`); the Keccak-f[1600] readings follow
-- `Pi1KFRpm.lean`'s (`pi1CompletenessKeccak_iff`).
import RecCompose.Pi1KFRpm

/-!
# The merge-hazard premises with their Fiat–Shamir over `Φ`

`RecStatement.Pi1HazardKeccakHonest D P1 δh` (completeness) and `RecStatement.Pi1HazardKeccak D εh` (soundness) are
premises of the end-to-end theorems at the **real Keccak-f[1600]**: π1-rec3's run on the honest proof's stream (on the
adversary's accepted stream) avoids the merge hazard (`RecGraph.MergeHazard`: the run draws `t`, challenge 49, and `t`
is a root of `Z_bad(p_0)`, `p_0` challenge 42). This file states them with Keccak-f[1600] replaced by a permutation
`Φ`, as `Pi1KFRpm.lean` does for `Pi1CompletenessKeccak`:

* **`HazardAt o`**: the hazard on a run's outcome (its final channel's challenges 42 and 49, at least 50 drawn);
  `RecGraph.MergeHazard π iv input s` is `HazardAt` of the run over `π` at the reference shape (`mergeHazard_iff`).
* **`pi1HazardFsWith Φ D roots input s`**: π1-rec3's IV over `Φ` at the setup's roots (`pi1IvWith Φ`), the run over
  `Φ` on the stream `s` (`runWithFs Φ`, at the reference shape, as `MergeHazard`), its hazard; at
  `Φ = pure ∘ keccakF1600` it is `MergeHazard keccakF1600` at π1's contract IV (**`pi1HazardFsWith_kf`**).
* **Completeness**: `pi1FsHonestHazardExperiment D Φ`, **`Pi1HazardFsHonest D Φ δ`**: the recursion's π1 prover with
  its Fiat–Shamir over `Φ` (`pi1ProverFs (keccak256With Φ)`, its trees and openings over `π`), the hazard of the run
  over `Φ` on its stream. **The Keccak reading** (**`pi1HazardKeccakHonest_iff`**):
  `Pi1HazardKeccakHonest D (pi1Rec3ProverKF D) δ ↔ Pi1HazardFsHonest D (pure ∘ keccakF1600) δ`.
* **Soundness**: `pi1FsHazardExperiment D Φ B`, **`Pi1HazardFs D Φ εh`**: the adversary's stream, the hazard of the
  run over `Φ` on it (the graph's checks not asked). **The Keccak reading** (**`pi1HazardKeccak_of_fs`**):
  `Pi1HazardFs D (pure ∘ keccakF1600) εh → Pi1HazardKeccak D εh` (the premise asks the hazard on accepted streams
  only, so this direction).

**Not proved here**: the random-permutation readings (`Pi1HazardFsHonest D queryPermutation δh`,
`Pi1HazardFs D queryPermutation εh`). `RecGraph.hazard_prob` is a count for a uniform `t`, not a game; the completeness
route left is in `Review/STATEMENT_REVIEW_2.md`, finding 3.
-/

set_option autoImplicit false

namespace RecCompose.Pi1Hazard

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open UniComplete UniComplete.Rec3
open RecCompose.Pi1KF
open RecStatement (RecDeployment Pi1Prover Pi1StreamAdversary)
open scoped ENNReal

/-! ## The hazard on an outcome -/

/-- **The merge hazard at a run's outcome**: the run drew `t` (challenge 49: at least 50 challenges) and `t` is
hazardous for challenge 42 (`RecGraph.Hazard`, a root of `Z_bad(p_0)`). -/
def HazardAt (o : UniStatement.Outcome) : Prop :=
  50 ≤ o.chan.challenges.size ∧ RecGraph.Hazard (o.chan.challenges.getD 42 0) (o.chan.challenges.getD 49 0)

noncomputable instance (o : UniStatement.Outcome) : Decidable (HazardAt o) := by unfold HazardAt; infer_instance

/-- The hazard, as a verdict. -/
noncomputable def hazardOf (o : UniStatement.Outcome) : Bool := decide (HazardAt o)

theorem hazardOf_eq_true (o : UniStatement.Outcome) : hazardOf o = true ↔ HazardAt o := decide_eq_true_iff

/-- **`MergeHazard` is the hazard at π1-rec3's run over `π`** at the reference shape. -/
theorem mergeHazard_iff (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) :
    RecGraph.MergeHazard π iv publicInput stream ↔
      HazardAt (Id.run (runWithFs (m := Id) (fun s ↦ pure (π s)) reference iv publicInput stream
        (.flock flockMain) .point .rec3 true)) := Iff.rfl

/-! ## The hazard check with its Fiat–Shamir over `Φ` -/

section With

variable {m : Type → Type} [Monad m] (Φ : KeccakState → m KeccakState)

/-- **The hazard of π1-rec3's run over `Φ`** on the stream `s`: π1-rec3's IV over `Φ` at the setup's roots, the run
over `Φ` at the reference shape (as `RecGraph.MergeHazard`), the hazard at its outcome. -/
noncomputable def pi1HazardFsWith (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (s : Array UInt8) : m Bool := do
  let iv ← RecStatement.pi1IvWith Φ D.shape D.programIv roots
  let o ← runWithFs Φ reference iv input.toList s (.flock flockMain) .point .rec3 true
  return hazardOf o

end With

/-- **At `Φ = pure ∘ keccakF1600`**, in any lawful monad: the hazard of the deployed run at π1's contract IV. -/
theorem pi1HazardFsWith_kf {m : Type → Type} [Monad m] [LawfulMonad m] (D : Deployment) (roots : SetupRoots)
    (input : Vector UInt8 32) (s : Array UInt8) :
    pi1HazardFsWith (m := m) (fun x ↦ pure (keccakF1600 x)) D roots input s =
      pure (hazardOf (runFs reference (RecStatement.pi1Iv D.shape D.programIv roots) input.toList s
        (.flock flockMain) .point .rec3 true)) := by
  unfold pi1HazardFsWith
  rw [pi1IvWith_kf, pure_bind, runWithFs_kf, pure_bind]

/-- The hazard of the deployed run is `MergeHazard` over Keccak-f[1600]. -/
theorem hazardOf_runFs (iv publicInput : List UInt8) (s : Array UInt8) :
    hazardOf (runFs reference iv publicInput s (.flock flockMain) .point .rec3 true) = true ↔
      RecGraph.MergeHazard keccakF1600 iv publicInput s := by
  rw [hazardOf_eq_true, mergeHazard_iff]
  rfl

/-- **Events of a map**, under `runWithRandomPermutation`. -/
theorem prEvent_rwrp_map {α β : Type} (f : α → β) (Y : OracleComp RandomPermutationOracles α) (p : β → Prop) :
    Pr{let b ← runWithRandomPermutation (f <$> Y)}[p b] = Pr{let a ← runWithRandomPermutation Y}[p (f a)] := by
  rw [PcsQuotient.EndToEnd.Eager.prEvent_runWithRandomPermutation,
    PcsQuotient.EndToEnd.Eager.prEvent_runWithRandomPermutation]
  simp only [simulateQ_map, prEvent_map]

/-! ## Completeness: the honest proofs' hazard -/

/-- **The honest proofs' hazard with Keccak-f[1600] replaced by `Φ`**: the recursive setup, the recursion's π1 prover
with its Fiat–Shamir `keccak256With Φ` (its trees and openings over `π`), the hazard of π1-rec3's run over `Φ` on its
stream, at π1's IV over `Φ`. -/
noncomputable def pi1FsHonestHazardExperiment (D : RecDeployment)
    (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← pi1ProverFs (keccak256With Φ) D input rows q with
    | none => return false
    | some p1 => pi1HazardFsWith Φ D.pi1 trees.roots.pi1 input p1.stream

/-- **π1-rec3's honest proofs avoid the merge hazard with Keccak-f[1600] replaced by `Φ`**, but with probability
`δ`. -/
def Pi1HazardFsHonest (D : RecDeployment) (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState)
    (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← pi1FsHonestHazardExperiment D Φ input rows q}[v = true] ≤ δ

/-- The honest hazard experiment's outcome, read: the hazard of the deployed run at the IV on the stream. -/
noncomputable def honestHazardOf (input : Vector UInt8 32) : Option (List UInt8 × Array UInt8) → Bool
  | none => false
  | some (iv, s) => hazardOf (runFs reference iv input.toList s (.flock flockMain) .point .rec3 true)

/-- **At `Φ = pure ∘ keccakF1600`, the experiment is `Pi1HazardKeccakHonest`'s**, read. -/
theorem pi1FsHonestHazardExperiment_kf (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) :
    pi1FsHonestHazardExperiment D (fun s ↦ pure (keccakF1600 s)) input rows q =
      runWithRandomPermutation (honestHazardOf input <$> (do
        let trees ← D.setupTreesWith queryPermutation
        match ← pi1Rec3ProverKF D input rows q with
        | none => return none
        | some p1 => return some (D.pi1IvAt trees.roots.pi1, p1.stream))) := by
  unfold pi1FsHonestHazardExperiment pi1Rec3ProverKF
  rw [keccak256With_kf_fun]
  simp only [map_bind]
  refine congrArg _ (bind_congr fun trees ↦ bind_congr fun o ↦ ?_)
  cases o with
  | none => simp [honestHazardOf]
  | some p1 =>
    simp only [map_pure, honestHazardOf, pi1HazardFsWith_kf]
    rfl

/-- **The Keccak reading**: `Pi1HazardKeccakHonest` at the recursion's π1 prover is the honest hazard with π1-rec3's
Fiat–Shamir over the real Keccak-f[1600] on both sides (prover and run), its openings over `π`. -/
theorem pi1HazardKeccakHonest_iff (D : RecDeployment) (δ : ℝ≥0∞) :
    RecStatement.Pi1HazardKeccakHonest D (pi1Rec3ProverKF D) δ ↔
      Pi1HazardFsHonest D (fun s ↦ pure (keccakF1600 s)) δ := by
  unfold RecStatement.Pi1HazardKeccakHonest Pi1HazardFsHonest
  refine forall_congr' fun input ↦ forall_congr' fun rows ↦ forall_congr' fun q ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ ?_
  rw [pi1FsHonestHazardExperiment_kf, prEvent_rwrp_map]
  unfold RecStatement.pi1HonestHazardExperiment
  have hev : ∀ z : Option (List UInt8 × Array UInt8), honestHazardOf input z = true ↔
      ∃ iv s, z = some (iv, s) ∧ RecGraph.MergeHazard keccakF1600 iv input.toList s := by
    intro z
    rcases z with _ | ⟨iv, s⟩
    · simp [honestHazardOf]
    · simp only [honestHazardOf, hazardOf_runFs, Option.some.injEq, Prod.mk.injEq]
      exact ⟨fun h ↦ ⟨iv, s, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨h1, h2⟩, h⟩ ↦ h1 ▸ h2 ▸ h⟩
  simp only [hev]
  exact Iff.rfl

/-! ## Soundness: the adversary's stream's hazard -/

/-- **The merge hazard's experiment with Keccak-f[1600] replaced by `Φ`**: the recursive setup, the adversary's
public input and stream, the hazard of π1-rec3's run over `Φ` on it at π1's IV over `Φ` (the graph's checks not
asked). -/
noncomputable def pi1FsHazardExperiment (D : RecDeployment)
    (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState) (B : Pi1StreamAdversary) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, _) ← (simulateQ loggedOracles (B trees.roots trees.evaluations)).run []
    pi1HazardFsWith Φ D.pi1 trees.roots.pi1 z.1 z.2

/-- **π1-rec3's run with Keccak-f[1600] replaced by `Φ` avoids the merge hazard** on every adversary's stream, but
with probability `εh Q`, `Q` counting calls of `π` and `π⁻¹`. -/
def Pi1HazardFs (D : RecDeployment) (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState)
    (εh : ℕ → ℝ≥0∞) : Prop :=
  ∀ (B : Pi1StreamAdversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (B roots evals) permutationCallCost Q) →
    Pr{let v ← pi1FsHazardExperiment D Φ B}[v = true] ≤ εh Q

/-- The hazard experiment's outcome, read: the hazard of the deployed run at the IV on the stream. -/
noncomputable def streamHazardOf (z : List UInt8 × Vector UInt8 32 × Array UInt8) : Bool :=
  hazardOf (runFs reference z.1 z.2.1.toList z.2.2 (.flock flockMain) .point .rec3 true)

/-- **At `Φ = pure ∘ keccakF1600`**, the experiment is `pi1HazardExperiment`'s, read. -/
theorem pi1FsHazardExperiment_kf (D : RecDeployment) (B : Pi1StreamAdversary) :
    pi1FsHazardExperiment D (fun s ↦ pure (keccakF1600 s)) B =
      runWithRandomPermutation (streamHazardOf <$> (do
        let trees ← D.setupTreesWith queryPermutation
        let (z, _) ← (simulateQ loggedOracles (B trees.roots trees.evaluations)).run []
        return (D.pi1IvAt trees.roots.pi1, z))) := by
  unfold pi1FsHazardExperiment
  simp only [map_bind, map_pure, pi1HazardFsWith_kf]
  rfl

/-- **The Keccak reading**: the stream hazard over the real Keccak-f[1600] bounds `Pi1HazardKeccak` (which asks the
hazard on streams π1-rec3's graph accepts only). -/
theorem pi1HazardKeccak_of_fs (D : RecDeployment) (εh : ℕ → ℝ≥0∞)
    (h : Pi1HazardFs D (fun s ↦ pure (keccakF1600 s)) εh) : RecStatement.Pi1HazardKeccak D εh := by
  intro B Q hQ
  refine le_trans ?_ (h B Q hQ)
  rw [pi1FsHazardExperiment_kf, prEvent_rwrp_map]
  unfold RecStatement.pi1HazardExperiment
  refine prEvent_mono _ _ _ fun z hz ↦ ?_
  exact (hazardOf_runFs _ _ _).mpr hz.2

end RecCompose.Pi1Hazard

/-- info: 'RecCompose.Pi1Hazard.pi1HazardKeccakHonest_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1Hazard.pi1HazardKeccakHonest_iff

/-- info: 'RecCompose.Pi1Hazard.pi1HazardKeccak_of_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1Hazard.pi1HazardKeccak_of_fs
