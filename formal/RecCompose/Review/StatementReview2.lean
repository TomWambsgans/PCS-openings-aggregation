-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The second statement review's Lean evidence (`STATEMENT_REVIEW_2.md`). Run from `formal/EndToEnd` on h1:
--   systemd-run --scope -q -p MemoryMax=12G lake env lean ../RecCompose/Review/StatementReview2.lean
import RecCompose.RunShape
import RecCompose.Pi1KFRpm

/-!
# Evidence for the second statement review

1. **The "known gap" of `pi1KeccakVerifierWith` is empty** (finding 3). `pi1KeccakVerifierWith` skips the
   `r.matrices = none` check that `verifyWithFs … .rec3 true` makes, but π1-rec3's run never returns a matrices' claim
   (`RecCompose.pi1RunShape`, already proved). So:
   * `pi1KeccakVerifierStrictWith` (the same verifier with `verifyWithFs`'s walk check put back) is
     `pi1KeccakVerifierWith`, at every monad and every opening hash `F` (`strict_eq`);
   * at the real Keccak-f[1600] (Fiat–Shamir and openings), `pi1KeccakVerifierWith` **is** π1-rec3's deployed verifier
     `Deployment.verifierRec3With`, the verifier of `UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`
     (`keccak_eq_verifierRec3`).
   `Pi1KF.verifierFs_le` is therefore an equality, and the reduction's π1 term is about π1-rec3's own verifier.
-/

namespace RecCompose.StatementReview2

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- `pi1KeccakVerifierWith` with `verifyWithFs`'s check of Flock's matrices put back, its three arms verbatim (at the walk, `none` passes). -/
def pi1KeccakVerifierStrictWith (D : UniStatement.Deployment) (roots : UniStatement.SetupRoots)
    (input : Vector UInt8 32) (proof : UniStatement.UniProof) : m Bool := do
  let iv := pi1Iv D.shape D.programIv roots
  let o := UniStatement.runFs D.shape iv input.toList proof.stream (.flock UniStatement.flockMain) .point .rec3 true
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := UniStatement.layoutWords D.shape
    let callOf : UniStatement.Commitment → Digest × List UInt8 × Compile.Proof
      | .c1 => (UniStatement.rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (UniStatement.rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    let mut ok := r.openings.map (·.1) == UniStatement.commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← UniStatement.pcsOpenWith F (UniStatement.layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    match r.matrices, true with
    | some mc, false =>
      ok := ok && (← UniStatement.pcsOpenWith F (UniStatement.layoutWordVars (words.getD 3 [])) roots.a0
        [⟨mc.point, mc.a⟩] proof.a0)
      ok := ok && (← UniStatement.pcsOpenWith F (UniStatement.layoutWordVars (words.getD 4 [])) roots.b0
        [⟨mc.point, mc.b⟩] proof.b0)
    | none, true => pure ()
    | _, _ => ok := false
    return ok

end With

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The matrices' check never fires**: at π1-rec3's reference shape, the strict verifier is
`pi1KeccakVerifierWith`, at every monad and opening hash. -/
theorem strict_eq (F : KeccakState → m KeccakState) (D : UniStatement.Deployment) (hD : D.shape = reference)
    (roots : UniStatement.SetupRoots) (input : Vector UInt8 32) (proof : UniStatement.UniProof) :
    pi1KeccakVerifierStrictWith F D roots input proof = pi1KeccakVerifierWith F D roots input proof := by
  unfold pi1KeccakVerifierStrictWith pi1KeccakVerifierWith
  rw [hD]
  dsimp only
  have key : ∀ r, (runFs reference (pi1Iv reference D.programIv roots) input.toList proof.stream
      (.flock flockMain) .point .rec3 true).result = .ok r → r.matrices = none :=
    fun r hr ↦ (pi1RunShape _ _ _ r hr).1
  generalize runFs reference (pi1Iv reference D.programIv roots) input.toList proof.stream
    (.flock flockMain) .point .rec3 true = o at key ⊢
  by_cases hacc : o.accepts = true
  · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases hres : o.result with e | r
    · rfl
    · simp only [key r hres, bind_pure]
      rfl
  · simp only [Bool.not_eq_true] at hacc
    simp only [hacc, Bool.not_false, ↓reduceIte]

/-- **At the real Keccak-f[1600], `pi1KeccakVerifierWith` is π1-rec3's deployed verifier** (`verifierRec3With`, the
verifier of π1-rec3's random-permutation theorem, at `F = Keccak-f[1600]`). -/
theorem keccak_eq_verifierRec3 (D : UniStatement.Deployment) (hD : D.shape = reference)
    (roots : UniStatement.SetupRoots) (input : Vector UInt8 32) (proof : UniStatement.UniProof) :
    Id.run (pi1KeccakVerifierWith (m := Id) (fun s ↦ pure (keccakF1600 s)) D roots input proof) =
      Id.run (D.verifierRec3With (m := Id) (fun s ↦ pure (keccakF1600 s)) roots input proof) := by
  rw [← strict_eq _ D hD]
  rfl

end RecCompose.StatementReview2

/-- info: 'RecCompose.StatementReview2.strict_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.StatementReview2.strict_eq

/-- info: 'RecCompose.StatementReview2.keccak_eq_verifierRec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.StatementReview2.keccak_eq_verifierRec3
