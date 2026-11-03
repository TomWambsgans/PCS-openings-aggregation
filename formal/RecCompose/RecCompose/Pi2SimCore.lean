-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Pi2ProbStaged.rejects_at`, `rejectGood_pi2` with the
-- staged run at pure functions proved (`Pi2SimAt`) in place of the named `Pi2RunAt`; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the logged random
-- oracle, mumbai's proof-of-work potential.
import RecCompose.Pi2SimExp

/-!
# The core at pure functions, the staged run's analysis proved

* **`rejects_at_good`**: at pure `(Ht, Ft)`, on a staged run whose graph accepts and whose contract rejects at good
  challenges, one of π2's openings fails its proof of work. As `rejects_at`, with `stagedAt`'s facts (`runAt_staged`,
  `cAt_fst`, `stagedAt_good`) for the named `Pi2RunAt`: for every π1 prover `P1k`.
* **`rejectGood_pi2_good`**: the grinding (`Holds.rejectGood`), as `rejectGood_pi2`, without `Pi2RunAt`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open E2ECompleteness (ro runAt)
open Pi2S Pi2K Pi2P Pi2E Pi2G
open scoped ENNReal

open Classical in
/-- **The core at pure `(Ht, Ft)`**, for any π1 prover: on a staged run whose graph accepts and whose contract
rejects at good challenges, one of π2's openings fails its proof of work. -/
theorem rejects_at_good {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hwc : Pi2WitnessComplete D C Fa) (hpo : Pi2Pi1Openings D C Fa)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (input : Vector UInt8 32)
    (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState)
    (z : ((Bool × Bool) × ((Pr2 × E × E × E) × E)) × (Pr2 × E × E × E))
    (hz : runAt Ht Ft (pi2Staged D C Fa P1k input).run = z)
    (hev : z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ badSet2 C.G z.2.1 ∧ ¬ badT2 C.G z.1.2.1 z.1.2.2) :
    ∃ L tree stack claims, E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel L tree
      stack claims = none := by
  rw [runAt_staged] at hz
  obtain ⟨ha1, ha2, hB, hT⟩ := hev
  cases hp1 : runAt Ht Ft P1k with
  | none =>
    rw [hp1] at hz
    subst hz
    have hf : (stagedAt Ht Ft D C Fa input none).1.1.1 = false := rfl
    rw [hf] at ha1
    cases ha1
  | some p1 =>
    rw [hp1] at hz
    have hgr : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D (rootsH D Ht Ft).pi1 input p1) =
        true := by
      rw [← hz] at ha1
      exact (cAt_fst Ht Ft D C input _ _ p1 rfl).symm.trans ha1
    have hgood := pi2Choice_good (hwc _ _ _ (graphChecks_of_verifierH hgr))
    obtain ⟨h1, hz2, hzt, hzp⟩ := stagedAt_good Ht Ft D C Fa input p1 hD hgood
    rw [hz] at h1 hz2 hzt hzp
    rw [h1, expW2_some] at ha2
    cases hpr : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C Fa PcsQuotient.nonceFuel input p1) with
    | none => exact pi2Prover_none Fa Ht Ft _ input p1 hpr
    | some proof =>
      exfalso
      rw [hpr] at ha2
      dsimp only at ha2
      rw [hzp, hz2, hzt] at hT
      rw [hz2] at hB
      have hbad : ¬ BadCopy (C.G (rootsH D Ht Ft)) (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2
          (Fa.pubOf (rootsH D Ht Ft) (publicScalarsOf input.toList (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1))
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.α
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.β
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.γ :=
        fun hb ↦ hB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      have ht : ¬ BadT (C.G (rootsH D Ht Ft)) (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.α
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.β
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.γ
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.t :=
        fun hb ↦ hT ⟨hbad, hb⟩
      have hacc := pi2_accepts D hD C Fa Ft Ht PcsQuotient.nonceFuel input p1 hgood (logN_G Fa _)
        (by rw [Fa.logW]; rfl) proof hpr hroots hbad ht (hpo Ht Ft input p1 proof hgood hgr hpr)
      exact absurd (hacc.symm.trans ha2) (by decide)

/-- **The grinding for π2** (`Holds.rejectGood`), the staged run's analysis proved: the staged run rejected at good
challenges, the graph accepting, with probability at most `N · (1 − 2^-17)^nonceFuel`. -/
theorem rejectGood_pi2_good {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hwc : Pi2WitnessComplete D C Fa) (hpo : Pi2Pi1Openings D C Fa)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (input : Vector UInt8 32) {N : ℕ}
    (hcost : Common.QueryCostAtMost (pi2Staged D C Fa P1k input).run hashBlocks N) :
    Pr{let z ← (simulateQ ro (pi2Staged D C Fa P1k input).run).run' ∅}[
      z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ badSet2 C.G z.2.1 ∧ ¬ badT2 C.G z.1.2.1 z.1.2.2] ≤
      (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel :=
  rejectGood_of_pot _ _ hcost fun ℓ z hz hev ↦
    pot_of_rejects _ (fun z : ((Bool × Bool) × ((Pr2 × E × E × E) × E)) × (Pr2 × E × E × E) ↦
      z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ badSet2 C.G z.2.1 ∧ ¬ badT2 C.G z.1.2.1 z.1.2.2)
      (fun Ht Ft hev' ↦ rejects_at_good hD C Fa hroots hwc hpo P1k input Ht Ft _ rfl hev') ℓ z hz hev

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.rejectGood_pi2_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.rejectGood_pi2_good
