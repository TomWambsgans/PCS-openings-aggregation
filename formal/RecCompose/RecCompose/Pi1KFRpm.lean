-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement read is `formal/RecStatement`'s
-- (`Pi1CompletenessKeccak`, `pi1KeccakVerifierWith`); its random-permutation reading is `formal/UniStatement`'s
-- `UniCompletenessRec3` (`RecSecurity.lean`), proved by `formal/UniComplete`'s `uniCompletenessRec3_end_closed`. The
-- eager form of the random-permutation model is `formal/EndToEnd/ZK/ProverBridgeEager.lean`'s; Keccak-256 through a
-- monad morphism `ProverBridgeParam.lean`'s (`keccak256With_hom`).
import RecCompose.Pi1KF
import RecCompose.RunShape
import RecCompose.RpmC
import UniComplete.Rec3EndClosed
import ZK.ProverBridgeParam

/-!
# `Pi1CompletenessKeccak` at the recursion's π1 prover: what it says, and its random-permutation reading

`RecStatement.Pi1CompletenessKeccak D P1 δ1` is a **premise** of the end-to-end completeness theorems: π1-rec3's honest
proof, its Fiat–Shamir over the real Keccak-f[1600], its openings over the random permutation `π`, is rejected by
π1-rec3's verifier at Keccak-f[1600] (`pi1KeccakVerifierWith`, openings over `π`) with probability at most `δ1`. At the
old prover (`Pi2G.pi1Rec3Prover`, Fiat–Shamir over `π`) prover and verifier disagreed on every challenge, so it held
only for `δ1 ≈ 1` (statement review, finding 4). At the recursion's prover `pi1Rec3ProverKF` both hash the
Fiat–Shamir with Keccak-f[1600]. This file makes the premise's content explicit:

* **`pi1VerifierFsWith Φ F`**: `pi1KeccakVerifierWith` with its Fiat–Shamir over a permutation `Φ` (π1-rec3's IV
  `pi1IvWith Φ`, the run `runWithFs Φ`), its openings over `F`; at `Φ = pure ∘ keccakF1600` it is `pi1KeccakVerifierWith`
  (**`pi1VerifierFsWith_kf`**, any lawful monad).
* **`pi1FsCompletenessExperiment D Φ`**, **`Pi1CompletenessFs D Φ δ`**: the completeness experiment with Keccak-f[1600]
  replaced by `Φ` on both sides (the prover's Fiat–Shamir `keccak256With Φ`, the verifier's `Φ`), the trees and
  openings over `π`.
* **The Keccak reading** (**`pi1CompletenessKeccak_iff`**): `Pi1CompletenessKeccak D (pi1Rec3ProverKF D) δ ↔
  Pi1CompletenessFs D (pure ∘ keccakF1600) δ`.
* **The random-permutation reading, proved** (**`pi1CompletenessFs_rpm`**): at `Φ = π` (Keccak-f[1600] read as the
  random permutation, one permutation for the Fiat–Shamir and the openings) the experiment is π1-rec3's own
  (`uniCompletenessExperimentRec3` of `uniProverRec3RP`, `pi1ProverFs_rpm`), but for π2's setup tree, built and unused;
  so `Pi1CompletenessFs D π deltaRec3`, from `uniCompletenessRec3_end_closed`, `deltaRec3 < 2^-167`.
* **No matrices gap** (**`verifierFs_eq`**, **`pi1KeccakVerifierWith_kf_eq`**): `pi1KeccakVerifierWith` omits
  `verifyWithFs`'s check that the walk leaves no matrices' claim, but π1-rec3's run never returns one
  (`runWithFs_shape`), so at the reference shape the verifier is π1-rec3's deployed `verifierRec3With`, equal as
  programs, over every permutation and at Keccak-f[1600].

**The gap, stated plainly.** Nothing here proves the Keccak reading. `Pi1CompletenessKeccak D (pi1Rec3ProverKF D) δ1`
is the heuristic "Keccak-f[1600] behaves as the random permutation for this fixed honest prover": the experiment at
`Φ = pure ∘ keccakF1600` has the error of the experiment at `Φ = π`, which is proved below `2^-167`. It is a heuristic
about one fixed, efficient, honest prover (no adversary), the weakest form of the Fiat–Shamir heuristic; it is not
implied by anything proved.
-/

set_option autoImplicit false

namespace RecCompose.Pi1KF

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open UniComplete UniComplete.Rec3
open RecStatement (RecDeployment Pi1Prover)
open PcsQuotient.EndToEnd.Eager
open scoped ENNReal

/-! ## The verifier with its Fiat–Shamir over `Φ` -/

section With

variable {m : Type → Type} [Monad m] (Φ F : KeccakState → m KeccakState)

/-- **π1-rec3's verifier with its Fiat–Shamir over `Φ`** and its three openings over `F`: `pi1KeccakVerifierWith` with
`pi1IvWith Φ` and `runWithFs Φ` for `pi1Iv` and `runFs`. -/
def pi1VerifierFsWith (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof) : m Bool := do
  let iv ← RecStatement.pi1IvWith Φ D.shape D.programIv roots
  let o ← runWithFs Φ D.shape iv input.toList proof.stream (.flock flockMain) .point .rec3 true
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := layoutWords D.shape
    let callOf : Commitment → Digest × List UInt8 × LeanVM.Protocol.Compile.Proof
      | .c1 => (rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← pcsOpenWith F (layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    return ok

end With

section Lawful

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- `pure ∘ Id.run`, a morphism from `Id`. -/
def idMorph : Morph Id m := ⟨fun x ↦ pure (Id.run x), fun _ ↦ rfl, fun x f ↦ by simp⟩

/-- `pure ∘ Id.run`, a morphism from `Id` (`ZK`'s kind). -/
def idMHom : PcsQuotient.EndToEnd.MHom Id m := ⟨fun x ↦ pure (Id.run x), fun _ ↦ rfl, fun x f ↦ by simp⟩

/-- **Keccak-256 over the real Keccak-f[1600], in any lawful monad, is the pure `keccak256`.** -/
theorem keccak256With_kf (x : List UInt8) :
    keccak256With (m := m) (fun s ↦ pure (keccakF1600 s)) x = pure (KeccakHash.keccak256 x) := by
  have h := PcsQuotient.EndToEnd.Param.keccak256With_hom (idMHom (m := m)) (fun s ↦ (pure (keccakF1600 s) : Id _)) x
  simp only [idMHom] at h
  exact h.symm

theorem keccak256With_kf_fun :
    keccak256With (m := m) (fun s ↦ pure (keccakF1600 s)) = hKF := funext keccak256With_kf

/-- π1-rec3's IV over the real Keccak-f[1600], in any lawful monad: the pure `pi1Iv`. -/
theorem pi1IvWith_kf (s : UniStatement.Shape) (programIv : List UInt8) (roots : SetupRoots) :
    RecStatement.pi1IvWith (m := m) (fun x ↦ pure (keccakF1600 x)) s programIv roots =
      pure (RecStatement.pi1Iv s programIv roots) := by
  have h := UniComplete.Rec3.Morph.app_contractIvForWithH (idMorph (m := m))
    (fun x ↦ (pure (KeccakHash.keccak256 x) : Id Digest)) s (.flock flockMain) .rec3 true programIv roots
  simp only [idMorph] at h
  unfold RecStatement.pi1IvWith RecStatement.pi1Iv
  rw [contractIvForWith_eqH, keccak256With_kf_fun]
  exact h.symm

/-- π1-rec3's run over the real Keccak-f[1600], in any lawful monad: the pure `runFs`. -/
theorem runWithFs_kf (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) (fs : FsShape) (walk : Bool) :
    runWithFs (m := m) (fun x ↦ pure (keccakF1600 x)) shape iv publicInput stream blake2s mode fs walk =
      pure (runFs shape iv publicInput stream blake2s mode fs walk) := by
  have h := UniComplete.Rec3.Morph.app_runWithFsH (idMorph (m := m))
    (fun x ↦ (pure (KeccakHash.keccak256 x) : Id Digest)) shape iv publicInput stream blake2s mode fs walk
  simp only [idMorph] at h
  have hid : keccak256With (m := Id) (fun x ↦ pure (keccakF1600 x)) =
      fun x ↦ (pure (KeccakHash.keccak256 x) : Id Digest) := rfl
  unfold runFs
  rw [runWithFs_eqH, runWithFs_eqH (m := Id), keccak256With_kf_fun, hid, h]
  rfl

/-- **At `Φ = pure ∘ keccakF1600`, the verifier is `pi1KeccakVerifierWith`.** -/
theorem pi1VerifierFsWith_kf (F : KeccakState → m KeccakState) :
    pi1VerifierFsWith (fun s ↦ pure (keccakF1600 s)) F = RecStatement.pi1KeccakVerifierWith F := by
  funext D roots input proof
  unfold pi1VerifierFsWith RecStatement.pi1KeccakVerifierWith
  rw [pi1IvWith_kf, pure_bind, runWithFs_kf, pure_bind]
  rfl

end Lawful

/-! ## The experiment with its Fiat–Shamir over `Φ` -/

/-- **π1-rec3's completeness experiment with Keccak-f[1600] replaced by `Φ`**: the recursive setup, the prover with its
Fiat–Shamir `keccak256With Φ` (its trees and openings over `π`), the verifier with its Fiat–Shamir over `Φ` (its
openings over `π`). -/
noncomputable def pi1FsCompletenessExperiment (D : RecDeployment)
    (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← pi1ProverFs (keccak256With Φ) D input rows q with
    | none => return false
    | some p1 => pi1VerifierFsWith Φ queryPermutation D.pi1 trees.roots.pi1 input p1

/-- **π1-rec3's completeness with Keccak-f[1600] replaced by `Φ`**, error `δ`. -/
def Pi1CompletenessFs (D : RecDeployment) (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState)
    (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← pi1FsCompletenessExperiment D Φ input rows q}[v = false] ≤ δ

/-- **The Keccak reading**: the experiment at `Φ = pure ∘ keccakF1600` is `Pi1CompletenessKeccak`'s at the recursion's
π1 prover. -/
theorem pi1FsCompletenessExperiment_kf (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) :
    pi1FsCompletenessExperiment D (fun s ↦ pure (keccakF1600 s)) input rows q =
      RecStatement.pi1KeccakCompletenessExperiment D (pi1Rec3ProverKF D) input rows q := by
  unfold pi1FsCompletenessExperiment RecStatement.pi1KeccakCompletenessExperiment pi1Rec3ProverKF
  rw [keccak256With_kf_fun, pi1VerifierFsWith_kf]
  rfl

/-- **`Pi1CompletenessKeccak` at the recursion's π1 prover is the completeness of π1-rec3 with its Fiat–Shamir over
the real Keccak-f[1600]** on both sides, its openings over `π`. -/
theorem pi1CompletenessKeccak_iff (D : RecDeployment) (δ : ℝ≥0∞) :
    RecStatement.Pi1CompletenessKeccak D (pi1Rec3ProverKF D) δ ↔
      Pi1CompletenessFs D (fun s ↦ pure (keccakF1600 s)) δ := by
  unfold RecStatement.Pi1CompletenessKeccak Pi1CompletenessFs
  simp only [pi1FsCompletenessExperiment_kf]

/-! ## The random-permutation reading -/

/-- **A game rejecting at most as often as another, permutation by permutation.** -/
theorem eager_le {α β : Type} (X : OracleComp RandomPermutationOracles α) (Y : OracleComp RandomPermutationOracles β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ π : Equiv.Perm St, Pr{let a ← simulateQ (permImpl π) X}[p a] ≤ Pr{let b ← simulateQ (permImpl π) Y}[q b]) :
    Pr{let a ← runWithRandomPermutation X}[p a] ≤ Pr{let b ← runWithRandomPermutation Y}[q b] := by
  rw [prEvent_runWithRandomPermutation, prEvent_runWithRandomPermutation]
  exact mul_le_mul' le_rfl (Finset.sum_le_sum fun π _ ↦ h π)

section Eq

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **π1-rec3's verifier without the matrices' check is π1-rec3's deployed verifier**, at the reference shape, every
lawful monad and every hash `F` (its Fiat–Shamir and openings both over `F`): `verifyWithFs … .rec3 true`'s last check
(`r.matrices = none` with the walk) never fires, since π1-rec3's run returns no matrices' claim over any permutation
(`runWithFs_shape`). So `pi1KeccakVerifierWith` is no superset verifier (second statement review, finding 4). -/
theorem verifierFs_eq (F : KeccakState → m KeccakState) (D : Deployment) (hD : D.shape = reference)
    (roots : SetupRoots) (input : Vector UInt8 32) (p : UniProof) :
    pi1VerifierFsWith F F D roots input p = D.verifierRec3With F roots input p := by
  unfold pi1VerifierFsWith Deployment.verifierRec3With verifyWithFs
  simp only [RecStatement.pi1IvWith, Deployment.ivRec3With]
  rw [hD]
  refine bind_congr fun iv ↦ ?_
  refine bind_congr_of_holds (runWithFs_shape F iv input.toList p.stream) fun o ho ↦ ?_
  by_cases hacc : o.accepts = true
  · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases hres : o.result with e | r
    · rfl
    · simp only [(ho r hres).1, bind_pure]
      rfl
  · simp only [Bool.not_eq_true] at hacc
    simp only [hacc, Bool.not_false, ↓reduceIte]

/-- **At the real Keccak-f[1600], `pi1KeccakVerifierWith` is π1-rec3's deployed verifier** `verifierRec3With` (the
verifier of `UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`), at the reference shape and in every lawful monad:
the reduction's π1 term is about π1-rec3's own verifier. -/
theorem pi1KeccakVerifierWith_kf_eq (D : Deployment) (hD : D.shape = reference) (roots : SetupRoots)
    (input : Vector UInt8 32) (p : UniProof) :
    RecStatement.pi1KeccakVerifierWith (m := m) (fun s ↦ pure (keccakF1600 s)) D roots input p =
      D.verifierRec3With (fun s ↦ pure (keccakF1600 s)) roots input p := by
  rw [← pi1VerifierFsWith_kf]
  exact verifierFs_eq _ D hD roots input p

end Eq

/-- **The random-permutation reading of `Pi1CompletenessKeccak`, proved**: with Keccak-f[1600] read as the random
permutation (one `π` for π1's Fiat–Shamir, its trees and its openings), the recursion's π1 prover is
`uniProverRec3RP flockProve3H D.pi1` (`pi1ProverFs_rpm`) and π1-rec3's completeness holds with `deltaRec3 < 2^-167`
(`uniCompletenessRec3_end_closed`): π2's setup tree, built and unused, drops out permutation by permutation, and the
verifier without the matrices' check is π1-rec3's deployed one (`verifierFs_eq`). The Keccak
reading (`pi1CompletenessKeccak_iff`) is not proved: it is the heuristic premise. -/
theorem pi1CompletenessFs_rpm (D : RecDeployment) (hsh : D.pi1.shape = reference)
    (hiv : D.pi1.programIv.length ≤ 2 ^ 16) : Pi1CompletenessFs D queryPermutation deltaRec3 := by
  intro input rows q hfit hrel
  refine le_trans ?_ (uniCompletenessRec3_end_closed D.pi1 hsh hiv input rows q hfit hrel)
  unfold pi1FsCompletenessExperiment uniCompletenessExperimentRec3
  rw [pi1ProverFs_rpm]
  refine eager_le _ _ _ _ fun π ↦ ?_
  unfold RecDeployment.setupTreesWith
  simp only [bind_assoc, pure_bind, simulateQ_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun t1 ↦ ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun t2 ↦ ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun o ↦ ?_
  cases o with
  | none => exact le_rfl
  | some p1 => exact le_of_eq (by rw [verifierFs_eq _ D.pi1 hsh])

end RecCompose.Pi1KF

/-- info: 'RecCompose.Pi1KF.pi1VerifierFsWith_kf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.pi1VerifierFsWith_kf

/-- info: 'RecCompose.Pi1KF.pi1CompletenessKeccak_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.pi1CompletenessKeccak_iff

/-- info: 'RecCompose.Pi1KF.verifierFs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.verifierFs_eq

/-- info: 'RecCompose.Pi1KF.pi1KeccakVerifierWith_kf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.pi1KeccakVerifierWith_kf_eq

/-- info: 'RecCompose.Pi1KF.pi1CompletenessFs_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.pi1CompletenessFs_rpm
