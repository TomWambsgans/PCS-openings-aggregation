-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Pi2HonestCount
import RecCompose.Holds

/-!
# π2's honest prover: what its run leaves

**`pi2ProveStreamWith_holds`**: in any lawful monad (over any Keccak-256 `H`: the random permutation's, a simulation's,
`Id`'s), every run of the prover's stream leaves the stacks and the inputs `pi2_honest` speaks of: `W`'s stack is
`honestW`, `Q`'s is `honestQ` at the challenges it drew, and the inputs are `honestInputs` at its public scalars and
challenges (whatever the transcript answered).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest)

/-- **The prover leaves the honest stacks and inputs.** -/
theorem pi2ProveStreamWith_holds (G : RecPiop.Circuit E) (reads : List Read) (setupStack : Array K)
    (input : List UInt8) (values : List PublicValue) (w : ℕ → K) (s : UniComplete.Wr) :
    Holds ((pi2ProveStreamWith H G reads setupStack input values w).run s) fun r ↦
      (fun j ↦ r.1.wStack.getD j 0) = honestW G w ∧
        (fun j ↦ r.1.qStack.getD j 0) = honestQ G w r.1.inputs.α r.1.inputs.β r.1.inputs.γ ∧
          r.1.inputs = honestInputs G setupStack w (publicScalarsOf input values) r.1.inputs.α r.1.inputs.β
            r.1.inputs.γ r.1.inputs.t r.1.inputs.ρ := by
  unfold pi2ProveStreamWith
  rcases hl : layoutsOf G.logN with ⟨lw, lq, ls⟩
  simp only [StateT.run_bind]
  repeat' (first
    | exact holds_pure ⟨by unfold honestW; rw [hl], by unfold honestQ; rw [hl], rfl⟩
    | refine holds_bind (holds_true _) fun _ _ ↦ ?_)

/-- **Every run of the honest prover, at a setup of the deployment, leaves true claims and a passing check** off the
bad challenges it drew (`pi2_honest` at the run's own stacks and inputs). -/
theorem pi2ProveStreamWith_claims {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C)
    (hcol : Pi2SetupColumns D C) (roots : RecSetupRoots) (reads : List Read) (input : List UInt8)
    (values : List PublicValue) (w : ℕ → K)
    (hw : (C.G roots).Satisfies (Fa.pubOf roots (publicScalarsOf input values)) (RecCircuit.emb w))
    (s : UniComplete.Wr) :
    Holds ((pi2ProveStreamWith H (C.G roots) reads (D.circuitAt roots.pi1).setupStack input values w).run s)
      fun r ↦ ¬ BadCopy (C.G roots) w (Fa.pubOf roots (publicScalarsOf input values)) r.1.inputs.α r.1.inputs.β
          r.1.inputs.γ → ¬ BadT (C.G roots) w r.1.inputs.α r.1.inputs.β r.1.inputs.γ r.1.inputs.t →
        ((Spec.of (D.circuitAt roots.pi1).circuit).core.run r.1.inputs).all ≠ 0 ∧
          Pi2ClaimsHold D roots r.1.inputs (fun j ↦ r.1.wStack.getD j 0) (fun j ↦ r.1.qStack.getD j 0) := by
  refine holds_mono (pi2ProveStreamWith_holds H _ reads _ input values w s) fun r ⟨hW, hQ, hI⟩ hb ht ↦ ?_
  rw [hW, hQ, hI]
  exact pi2_honest Fa hcol roots w _ _ _ _ _ _ hw hb ht

end RecCompose

/-- info: 'RecCompose.pi2ProveStreamWith_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2ProveStreamWith_holds

/-- info: 'RecCompose.pi2ProveStreamWith_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2ProveStreamWith_claims
