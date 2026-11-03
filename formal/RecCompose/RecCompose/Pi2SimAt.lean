-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's honest prover (`RecCompose.Pi2Prover`,
-- `crates/leanvm_rec/src/pi2/prover.rs`) cut at its challenges, as `Pi2ProbStaged` stages it; leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the run at pure
-- functions (`runAt`, `totalImpl`).
import RecCompose.Pi2SimMorph

/-!
# π2's staged run at pure functions

* **`stream_split`**: π2's prover's stream (`pi2ProveStreamWith`) is `pre2`, the three chained challenges, `mid2`,
  `t`, `post2`, in any lawful monad (`UniComplete.Prob.run_sampleW`; after a challenge the next one's input is the
  answer's `32` bytes, `tInput_absorbW`).
* **`tInput_pre2_length`**: on values matching the real circuit's reads, `α`'s input has `536` bytes (the state, the
  public data's `472`, `W`'s root word), so `pi2Staged`'s `fixLen 536` keeps it.
* **`runAt_staged_none`**, **`runAt_staged_a1`**, **`runAt_staged_good`**: at pure `(Ht, Ft)` the staged run's verdict
  is `(false, false)` when π1's prover returns none, its first component π1-rec3's graph's verdict otherwise, and on an
  honest witness (`Pi2Good`) the whole verdict is the experiment's (`expW2` at `Id`), its priors and challenges the
  honest prover's (`outOf`'s inputs).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open E2ECompleteness (runAt)
open UniComplete (Wr WrM)
open Pi2S Pi2K Pi2P Pi2E Pi2G

/-! ## The stream, cut -/

theorem tInput_absorbW (w : Wr) (s : Digest) : UniComplete.Prob.tInput (absorbW w s) = digestBytes s := by
  simp [UniComplete.Prob.tInput, absorbW]

section Split

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest)

theorem run_sampleW' (w : Wr) :
    (UniComplete.sampleW H).run w = H (UniComplete.Prob.tInput w) >>= fun s ↦ pure (chalP s, absorbW w s) :=
  UniComplete.Prob.run_sampleW H w

/-- **The prover's stream, cut at its challenges.** -/
theorem stream_split (G : RecPiop.Circuit E) (reads : List Read) (setupStack : Array K) (input : List UInt8)
    (values : List PublicValue) (w : ℕ → K) (w0 : Wr) :
    (pi2ProveStreamWith H G reads setupStack input values w).run w0 =
      (pre2 H G reads values w).run w0 >>= fun p ↦
      H (UniComplete.Prob.tInput p.2) >>= fun s₁ ↦ H (digestBytes s₁) >>= fun s₂ ↦ H (digestBytes s₂) >>= fun s₃ ↦
      (mid2 H G w (chalP s₁) (chalP s₂) (chalP s₃)).run (absorbW (absorbW (absorbW p.2 s₁) s₂) s₃) >>= fun q ↦
      H (UniComplete.Prob.tInput q.2) >>= fun st ↦
      (post2 H G setupStack input values w p.1.1 p.1.2 q.1.1 q.1.2 (chalP s₁) (chalP s₂) (chalP s₃)
        (chalP st)).run (absorbW q.2 st) := by
  simp only [pi2ProveStreamWith, pre2, mid2, post2, StateT.run_bind, StateT.run_pure, StateT.run_lift,
    run_sampleW', bind_assoc, pure_bind, tInput_absorbW]

end Split

/-! ## `α`'s input -/

theorem tInput_start_append (seed : Digest) (B : List UInt8) :
    UniComplete.Prob.tInput ((Wr.start seed).append B) = digestBytes seed ++ B := by
  simp [UniComplete.Prob.tInput, Wr.start, UniComplete.Wr.append]

/-- **`pre2`'s writer**: the start's, the public data and `W`'s root word appended. -/
theorem pre2_writer (G : RecPiop.Circuit E) (reads : List Read) (values : List PublicValue) (w : ℕ → K)
    (Hk : List UInt8 → Digest) (w0 : Wr) : ∃ h : E × E,
    (Id.run ((pre2 (m := Id) (Pure.pure ∘ Hk) G reads values w).run w0)).2 =
      w0.append (publicWire (reads.zip values) ++ UniStatement.rootWord h) := by
  have hw := sendPublic_writes (reads.zip values) w0
  unfold UniComplete.Writes at hw
  refine ⟨digestScalars (Id.run (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (layoutsOf G.logN).1.logN
    (placePublic (layoutsOf G.logN).1 fun i ↦ (wTableB G w).getD i 0))).root, ?_⟩
  unfold pre2
  rw [UniComplete.wr_run_bind, hw, UniComplete.wr_run_bind, UniComplete.wr_run_bind]
  rw [← UniComplete.Wr.append_append w0 (publicWire (reads.zip values))]
  rfl

theorem tInput_pre2_length (G : RecPiop.Circuit E) (reads : List Read) (values : List PublicValue) (w : ℕ → K)
    (Hk : List UInt8 → Digest) (seed : Digest) (hm : List.Forall₂ ReadMatch reads values) :
    (UniComplete.Prob.tInput (Id.run ((pre2 (m := Id) (Pure.pure ∘ Hk) G reads values w).run
      (Wr.start seed))).2).length = 32 + (reads.map Read.bytes).sum + 32 := by
  obtain ⟨h, hw⟩ := pre2_writer G reads values w Hk (Wr.start seed)
  rw [hw, tInput_start_append]
  simp only [List.length_append, publicWire_length reads values hm, UniComplete.Prob.rootWord_length,
    E2ECompleteness.length_digestBytes]
  all_goals omega

/-! ## The staged run at pure functions -/

section At

variable (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (D : RecDeployment) (C : Pi2Circuits D)
  (Fa : Pi2Facts D C) (input : Vector UInt8 32)

/-- Stage A at `Id`, π1's prover's result `o`. -/
noncomputable def aAt (o : Option UniStatement.UniProof) : StA :=
  Id.run (stageA (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure o) input)

/-- Stage B at `Id`. -/
def bAt (a : StA) (s₁ s₂ s₃ : Digest) : StB := Id.run (stageB (m := Id) (Pure.pure ∘ Ht) D C a s₁ s₂ s₃)

/-- Stage C at `Id`. -/
noncomputable def cAt (b : StB) (st : Digest) : Bool × Bool := Id.run (stageC (m := Id) (Pure.pure ∘ Ht) Ft D C input b st)

/-- The prior of the triple, from stage A's output. -/
noncomputable def prOf (a : StA) : Pr2 := (a.roots, a.vw.2, Fa.pubOf a.roots (publicScalarsOf input.toList a.vw.1))

/-- **The staged run at `Id`**, π1's prover's result `o`. -/
noncomputable def stagedAt (o : Option UniStatement.UniProof) :
    ((Bool × Bool) × ((Pr2 × E × E × E) × E)) × (Pr2 × E × E × E) :=
  let a := aAt Ht Ft D C Fa input o
  let s₁ := Ht (fixLen 536 (UniComplete.Prob.tInput a.wr))
  let s₂ := Ht (digestBytes s₁)
  let s₃ := Ht (digestBytes s₂)
  let b := bAt Ht D C a s₁ s₂ s₃
  let st := Ht (UniComplete.Prob.tInput b.wr)
  ((cAt Ht Ft D C input b st, ((prOf D C Fa input b.a, b.α, b.β, b.γ), chalP st)),
    (prOf D C Fa input a, chalP s₁, chalP s₂, chalP s₃))

/-- **The staged run at pure `(Ht, Ft)`** is `stagedAt` at π1's prover's result. -/
theorem runAt_staged (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) :
    runAt Ht Ft (pi2Staged D C Fa P1k input).run = stagedAt Ht Ft D C Fa input (runAt Ht Ft P1k) := by
  unfold runAt
  simp only [Pi2Staged.run, staged3, Pi2Staged.tail, pi2Staged, simulateQ_bind, simulateQ_pure, simulateQ_queryH,
    sim_stageA, sim_stageB, sim_stageC]
  rfl

/-- **π1's prover returning none**: the verdict `(false, false)`. -/
theorem cAt_none (s₁ s₂ s₃ st : Digest) :
    cAt Ht Ft D C input (bAt Ht D C (aAt Ht Ft D C Fa input none) s₁ s₂ s₃) st = (false, false) := rfl

/-- **Stage C's first component is π1-rec3's graph's verdict.** -/
theorem cAt_fst (b : StB) (st : Digest) (p1 : UniStatement.UniProof) (hp : b.a.p1 = some p1) :
    (cAt Ht Ft D C input b st).1 = b.a.a1 := by
  unfold cAt stageC
  rw [hp]
  dsimp only [Id.run, bind, pure]
  split <;> rfl

/-! ### π1's prover returning a proof -/

variable (p1 : UniStatement.UniProof)

/-- The seed at the setup's roots. -/
abbrev seedAt : Digest := Ht (RecStatement.name ++ ivOf D Ht (rootsH D Ht Ft) ++ input.toList)

/-- The witness π2's prover takes. -/
noncomputable abbrev vwAt : List PublicValue × (ℕ → K) := pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream

/-- `pre2`'s run at `Id`. -/
noncomputable abbrev preAt : (Array K × LeanVM.Prover.Tree) × Wr :=
  Id.run ((pre2 (m := Id) (Pure.pure ∘ Ht) (C.G (rootsH D Ht Ft)) (D.circuitAt (rootsH D Ht Ft).pi1).circuit.reads
    (vwAt Ht Ft D C Fa input p1).1 (vwAt Ht Ft D C Fa input p1).2).run (Wr.start (seedAt Ht Ft D input)))

theorem aAt_p1 : (aAt Ht Ft D C Fa input (some p1)).p1 = some p1 := rfl
theorem aAt_a1 : (aAt Ht Ft D C Fa input (some p1)).a1 =
    Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D (rootsH D Ht Ft).pi1 input p1) := rfl
theorem aAt_roots : (aAt Ht Ft D C Fa input (some p1)).roots = rootsH D Ht Ft := rfl
theorem aAt_trees : (aAt Ht Ft D C Fa input (some p1)).trees = Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D) := rfl
theorem aAt_setupTree : (aAt Ht Ft D C Fa input (some p1)).setupTree =
    (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).pi2 := rfl
theorem aAt_vw : (aAt Ht Ft D C Fa input (some p1)).vw = vwAt Ht Ft D C Fa input p1 := rfl
theorem aAt_wS : (aAt Ht Ft D C Fa input (some p1)).wS = (preAt Ht Ft D C Fa input p1).1.1 := rfl
theorem aAt_wT : (aAt Ht Ft D C Fa input (some p1)).wT = (preAt Ht Ft D C Fa input p1).1.2 := rfl
theorem aAt_wr : (aAt Ht Ft D C Fa input (some p1)).wr = (preAt Ht Ft D C Fa input p1).2 := rfl

theorem bAt_a (a : StA) (s₁ s₂ s₃ : Digest) : (bAt Ht D C a s₁ s₂ s₃).a = a := rfl
theorem bAt_α (a : StA) (s₁ s₂ s₃ : Digest) : (bAt Ht D C a s₁ s₂ s₃).α = chalP s₁ := rfl
theorem bAt_β (a : StA) (s₁ s₂ s₃ : Digest) : (bAt Ht D C a s₁ s₂ s₃).β = chalP s₂ := rfl
theorem bAt_γ (a : StA) (s₁ s₂ s₃ : Digest) : (bAt Ht D C a s₁ s₂ s₃).γ = chalP s₃ := rfl
theorem bAt_q (a : StA) (s₁ s₂ s₃ : Digest) :
    ((bAt Ht D C a s₁ s₂ s₃).qS, (bAt Ht D C a s₁ s₂ s₃).qT) =
      (Id.run ((mid2 (m := Id) (Pure.pure ∘ Ht) (C.G a.roots) a.vw.2 (chalP s₁) (chalP s₂) (chalP s₃)).run
        (absorbW (absorbW (absorbW a.wr s₁) s₂) s₃))).1 := rfl
theorem bAt_wr (a : StA) (s₁ s₂ s₃ : Digest) : (bAt Ht D C a s₁ s₂ s₃).wr =
    (Id.run ((mid2 (m := Id) (Pure.pure ∘ Ht) (C.G a.roots) a.vw.2 (chalP s₁) (chalP s₂) (chalP s₃)).run
      (absorbW (absorbW (absorbW a.wr s₁) s₂) s₃))).2 := rfl

/-- **On an honest witness `α`'s input has `536` bytes** (at the real deployment): `fixLen` keeps it. -/
theorem fixLen_aAt (hD : D.Real)
    (hgood : Pi2Good D C Fa (rootsH D Ht Ft) input p1.stream (vwAt Ht Ft D C Fa input p1)) :
    fixLen 536 (UniComplete.Prob.tInput (aAt Ht Ft D C Fa input (some p1)).wr) =
      UniComplete.Prob.tInput (aAt Ht Ft D C Fa input (some p1)).wr := by
  unfold fixLen
  split_ifs with h
  · rfl
  · exfalso
    apply h
    rw [aAt_wr, tInput_pre2_length _ _ _ _ _ _ hgood.1]
    unfold RecDeployment.circuitAt
    rw [hD.1 _]
    decide

/-- The honest prover's output at the setup's roots (`outOf`). -/
noncomputable abbrev outAt : Pi2Out :=
  outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (vwAt Ht Ft D C Fa input p1).1 (vwAt Ht Ft D C Fa input p1).2

/-- The staged run's chained answers and stage B, on π1's proof `p1` (`fixLen` dropped). -/
noncomputable abbrev s1At : Digest := Ht (UniComplete.Prob.tInput (aAt Ht Ft D C Fa input (some p1)).wr)
noncomputable abbrev s2At : Digest := Ht (digestBytes (s1At Ht Ft D C Fa input p1))
noncomputable abbrev s3At : Digest := Ht (digestBytes (s2At Ht Ft D C Fa input p1))
noncomputable abbrev bAtP : StB := bAt Ht D C (aAt Ht Ft D C Fa input (some p1)) (s1At Ht Ft D C Fa input p1)
  (s2At Ht Ft D C Fa input p1) (s3At Ht Ft D C Fa input p1)
noncomputable abbrev stAt : Digest := Ht (UniComplete.Prob.tInput (bAtP Ht Ft D C Fa input p1).wr)

/-- **The staged run's `post2` is the honest prover's output.** -/
theorem post2_eq_outAt :
    ((post2 (m := Id) (Pure.pure ∘ Ht) (C.G (bAtP Ht Ft D C Fa input p1).a.roots)
      (D.circuitAt (bAtP Ht Ft D C Fa input p1).a.roots.pi1).setupStack input.toList
      (bAtP Ht Ft D C Fa input p1).a.vw.1 (bAtP Ht Ft D C Fa input p1).a.vw.2 (bAtP Ht Ft D C Fa input p1).a.wS
      (bAtP Ht Ft D C Fa input p1).a.wT (bAtP Ht Ft D C Fa input p1).qS (bAtP Ht Ft D C Fa input p1).qT
      (bAtP Ht Ft D C Fa input p1).α (bAtP Ht Ft D C Fa input p1).β (bAtP Ht Ft D C Fa input p1).γ
      (chalP (stAt Ht Ft D C Fa input p1))).run (absorbW (bAtP Ht Ft D C Fa input p1).wr (stAt Ht Ft D C Fa input p1)) :
      Id _) =
    (outAt Ht Ft D C Fa input p1, (Id.run ((post2 (m := Id) (Pure.pure ∘ Ht) (C.G (bAtP Ht Ft D C Fa input p1).a.roots)
      (D.circuitAt (bAtP Ht Ft D C Fa input p1).a.roots.pi1).setupStack input.toList
      (bAtP Ht Ft D C Fa input p1).a.vw.1 (bAtP Ht Ft D C Fa input p1).a.vw.2 (bAtP Ht Ft D C Fa input p1).a.wS
      (bAtP Ht Ft D C Fa input p1).a.wT (bAtP Ht Ft D C Fa input p1).qS (bAtP Ht Ft D C Fa input p1).qT
      (bAtP Ht Ft D C Fa input p1).α (bAtP Ht Ft D C Fa input p1).β (bAtP Ht Ft D C Fa input p1).γ
      (chalP (stAt Ht Ft D C Fa input p1))).run (absorbW (bAtP Ht Ft D C Fa input p1).wr
        (stAt Ht Ft D C Fa input p1)))).2) := by
  refine Prod.ext ?_ rfl
  unfold outAt outOf proverOut
  rw [stream_split]
  rfl

theorem idRun_pair {α β : Type} (a : α) (b : β) : Id.run ((a, b) : Id (α × β)) = (a, b) := rfl

theorem bAtP_p1 : (bAtP Ht Ft D C Fa input p1).a.p1 = some p1 := rfl
theorem bAtP_roots : (bAtP Ht Ft D C Fa input p1).a.roots = rootsH D Ht Ft := rfl
theorem bAtP_setupTree : (bAtP Ht Ft D C Fa input p1).a.setupTree =
    (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).pi2 := rfl
theorem bAtP_trees : (bAtP Ht Ft D C Fa input p1).a.trees = Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D) :=
  rfl

/-- **Stage C on the honest witness is the experiment's verdict.** -/
theorem cAt_good :
    cAt Ht Ft D C input (bAtP Ht Ft D C Fa input p1) (stAt Ht Ft D C Fa input p1) =
      Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure (some p1)) input) := by
  rw [expW2_some, pi2ProverWith_run, pi2ProveWith_run]
  unfold cAt stageC
  simp only [bAtP_p1]
  rw [post2_eq_outAt]
  simp only [Id.run_bind, bAtP_roots, bAtP_setupTree, bAtP_trees, idRun_pair]
  generalize E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel
    (layoutsOf (C.G (rootsH D Ht Ft)).logN).1 (outAt Ht Ft D C Fa input p1).wTree (outAt Ht Ft D C Fa input p1).wStack
    [⟨((Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit).core.run (outAt Ht Ft D C Fa input p1).inputs).witnessPoint,
      ((Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit).core.run (outAt Ht Ft D C Fa input p1).inputs).fold⟩] = rW
  generalize E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel
    (layoutsOf (C.G (rootsH D Ht Ft)).logN).2.2 (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).pi2
    (D.circuitAt (rootsH D Ht Ft).pi1).setupStack
    [⟨((Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit).core.run (outAt Ht Ft D C Fa input p1).inputs).setupPoint,
      (outAt Ht Ft D C Fa input p1).inputs.ξ⟩] = rS
  generalize E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel
    (layoutsOf (C.G (rootsH D Ht Ft)).logN).2.1 (outAt Ht Ft D C Fa input p1).qTree (outAt Ht Ft D C Fa input p1).qStack
    [⟨((Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit).core.run (outAt Ht Ft D C Fa input p1).inputs).quotientPoint,
      ((Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit).core.run (outAt Ht Ft D C Fa input p1).inputs).quotientValue⟩,
     ⟨((Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit).core.run (outAt Ht Ft D C Fa input p1).inputs).sumPoint,
      ((Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit).core.run (outAt Ht Ft D C Fa input p1).inputs).sumValue⟩] = rQ
  rcases rW with _ | x <;> rcases rS with _ | y <;> rcases rQ with _ | z <;> rfl

/-- **The staged run on π1's proof `p1` with an honest witness**: its verdict the experiment's, its priors and challenges
the honest prover's. -/
theorem stagedAt_good (hD : D.Real)
    (hgood : Pi2Good D C Fa (rootsH D Ht Ft) input p1.stream (vwAt Ht Ft D C Fa input p1)) :
    (stagedAt Ht Ft D C Fa input (some p1)).1.1 = Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure (some p1)) input) ∧
    (stagedAt Ht Ft D C Fa input (some p1)).2 =
      (((rootsH D Ht Ft), (vwAt Ht Ft D C Fa input p1).2,
          Fa.pubOf (rootsH D Ht Ft) (publicScalarsOf input.toList (vwAt Ht Ft D C Fa input p1).1)),
        (outAt Ht Ft D C Fa input p1).inputs.α, (outAt Ht Ft D C Fa input p1).inputs.β,
        (outAt Ht Ft D C Fa input p1).inputs.γ) ∧
    (stagedAt Ht Ft D C Fa input (some p1)).1.2.2 = (outAt Ht Ft D C Fa input p1).inputs.t ∧
    (stagedAt Ht Ft D C Fa input (some p1)).1.2.1 = (stagedAt Ht Ft D C Fa input (some p1)).2 := by
  have hl := fixLen_aAt Ht Ft D C Fa input p1 hD hgood
  have hout := congrArg Prod.fst (post2_eq_outAt Ht Ft D C Fa input p1)
  dsimp only at hout
  unfold stagedAt
  simp only [hl]
  refine ⟨cAt_good Ht Ft D C Fa input p1, ?_, ?_, rfl⟩
  · rw [← hout]
    rfl
  · rw [← hout]
    rfl

end At

end RecCompose.Pi2Sim
