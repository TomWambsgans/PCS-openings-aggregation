-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's staged run's facts on every outcome of its run
-- against the lazy oracles, from `Pi2SimAt`'s facts at pure functions (`aAt`, `bAt`, `cAt`, `fixLen_aAt`) through
-- `Pi2AlphaChain.runAt_read`; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls, their lazy random oracles, `simulateQ`.
import RecCompose.Pi2AlphaChain
import RecCompose.Pi2SimAt

/-!
# The graph's verdict on every outcome

`G a` (**`GAcc`**): π1's prover returned a proof and π1-rec3's graph accepted it. On every outcome of the run against
the lazy oracles (`Pi2AlphaChain.runAt_read`: the outcome is the pure run at its cache's answers):

* **`gAcc_length`**: stage A's outcome with `G` has `α`'s input of `536` bytes (`fixLen` keeps it): the graph accepting,
  the witness is honest (`Pi2WitnessComplete`), so the public values match the reads (`fixLen_aAt`);
* **`accA_pi2`**, **`accB_pi2`**: off `G` the verdict's first component is `false` (π1's none, or the graph's
  rejection: `cAt_fst`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open E2ECompleteness (ro runAt Cache)
open UniComplete (Wr WrM)
open Pi2S Pi2K Pi2P Pi2E Pi2G

/-- **The graph accepted**: π1's prover returned a proof and π1-rec3's graph accepted it. -/
def GAcc (a : StA) : Prop := a.p1.isSome = true ∧ a.a1 = true

variable {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32)

theorem runAt_stageA (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) :
    runAt Ht Ft (stageA callKeccak256 callKeccakF1600 D C Fa P1k input) =
      aAt Ht Ft D C Fa input (runAt Ht Ft P1k) := by
  unfold runAt aAt
  rw [sim_stageA]
  rfl

/-- **Off `G`, stage C's verdict's first component is `false`**, at pure functions. -/
theorem cAt_of_not (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (b : StB) (st : Digest)
    (hb : ¬ GAcc b.a) : (cAt Ht Ft D C input b st).1 = false := by
  rcases hp : b.a.p1 with _ | p1
  · unfold cAt stageC
    rw [hp]
    rfl
  · rw [cAt_fst Ht Ft D C input b st p1 hp]
    unfold GAcc at hb
    rw [hp] at hb
    simpa using hb

/-- **Stage A with `G` has `α`'s input of `536` bytes**, on every outcome. -/
theorem gAcc_length (hD : D.Real) (hwc : Pi2WitnessComplete D C Fa)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) {c : Cache} {p : StA × Cache}
    (hp : p ∈ support ((simulateQ ro (stageA callKeccak256 callKeccakF1600 D C Fa P1k input)).run c))
    (hG : GAcc p.1) : (UniComplete.Prob.tInput p.1.wr).length = 536 := by
  have e := Pi2C.runAt_read hp
  rw [runAt_stageA] at e
  rw [← e] at hG ⊢
  generalize Pi2C.readH p.2 = Ht at hG ⊢
  generalize Pi2C.readF p.2 = Ft at hG ⊢
  generalize runAt Ht Ft P1k = o at hG ⊢
  rcases o with _ | p1
  · have h0 : (aAt Ht Ft D C Fa input none).p1 = none := rfl
    exact absurd hG.1 (by rw [h0]; simp)
  · have hacc := hG.2
    rw [aAt_a1] at hacc
    obtain ⟨vw, hvw⟩ := hwc _ input p1.stream (graphChecks_of_verifierH hacc)
    have hgood := fixLen_aAt Ht Ft D C Fa input p1 hD (pi2Choice_good ⟨vw, hvw⟩)
    rw [← hgood, fixLen_length]

/-- **Off `G`, the tail's verdict's first component is `false`**, on every outcome. -/
theorem accA_pi2 (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (a : StA) (ha : ¬ GAcc a)
    (s₁ s₂ s₃ : Digest) (c : Cache) (z : ((Bool × Bool) × (Pr2 × E × E × E) × E) × Cache)
    (hz : z ∈ support ((simulateQ ro ((pi2Staged D C Fa P1k input).tail a s₁ s₂ s₃)).run c)) :
    z.1.1.1 = false := by
  have e := Pi2C.runAt_read hz
  rw [← e]
  generalize Pi2C.readH z.2 = Ht
  generalize Pi2C.readF z.2 = Ft
  have h : (runAt Ht Ft ((pi2Staged D C Fa P1k input).tail a s₁ s₂ s₃)).1.1 =
      (cAt Ht Ft D C input (bAt Ht D C a s₁ s₂ s₃)
        (Ht (UniComplete.Prob.tInput (bAt Ht D C a s₁ s₂ s₃).wr))).1 := by
    unfold runAt
    simp only [Pi2Staged.tail, pi2Staged, simulateQ_bind, simulateQ_pure, simulateQ_queryH, sim_stageB,
      sim_stageC]
    rfl
  rw [h]
  exact cAt_of_not C input Ht Ft _ _ (by rw [bAt_a]; exact ha)

/-- **Off `G` of its stage A, stage C's verdict's first component is `false`**, on every outcome. -/
theorem accB_pi2 (b : StB) (hb : ¬ GAcc b.a) (st : Digest) (c : Cache) (z : (Bool × Bool) × Cache)
    (hz : z ∈ support ((simulateQ ro (stageC callKeccak256 callKeccakF1600 D C input b st)).run c)) :
    z.1.1 = false := by
  have e := Pi2C.runAt_read hz
  rw [← e]
  generalize Pi2C.readH z.2 = Ht
  generalize Pi2C.readF z.2 = Ft
  have h : runAt Ht Ft (stageC callKeccak256 callKeccakF1600 D C input b st) = cAt Ht Ft D C input b st := by
    unfold runAt cAt
    rw [sim_stageC]
    rfl
  rw [h]
  exact cAt_of_not C input Ht Ft b st hb

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.gAcc_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.gAcc_length

/-- info: 'RecCompose.Pi2Sim.accA_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.accA_pi2

/-- info: 'RecCompose.Pi2Sim.accB_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.accB_pi2
