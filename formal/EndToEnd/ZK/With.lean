-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Real
import ZK.Simulator

/-!
# Zero knowledge for `QuotientZk`'s simulator, named in the statement

The statement's `ZeroKnowledgeWith s₀ sim simOracle ζ` (`Security.lean`) takes the simulator as a
parameter. This file proves it for `zkSimulator`: `rpmSimulator` (`ZK/Simulator.lean`: `QuotientZk`'s
random-permutation simulator in the statement's shape, compiled) at public data of each statement, the
oracle `rpmSimOracle`.

* **What the simulator reads** (`PubProto`): of the skeleton model's prover, `QuotientZk.sim` reads
  the number of challenges `n`, when each secret table is committed (`cK`) and which positions are
  opened (`opened`): public functions of the challenges. `rpmSimulator` at a prover and at its public
  part (`PubProto.toProto`, no message, no row) are the same (`rpmSimulator_pub`), so the simulator is
  a function of the statement alone.
* **`zkSimulator pp simV skel fmt`**: for each statement, `rpmSimulator` at the public part `pp stmt`,
  the view simulator `simV stmt` and the skeleton `skel stmt`, the proof formatted by `fmt`.
* **`zeroKnowledgeWith_of_core`**: `ZeroKnowledgeWith s₀ (zkSimulator …) rpmSimOracle (εR + ε)` from,
  for each statement and witness of the relation, a prover `P stmt w` whose public part is `pp stmt`,
  the real bridge (`RealBridge`, `εR`), and `QuotientZk`'s closeness of its real and simulated games
  (`CoreClose`, `ε`: what `zk_rpm_skel` with the joint model gives). The ideal bridge is exact
  (`rpmIdeal_eq`).
-/

open OracleComp OracleSpec Common
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto View)

set_option linter.unusedSectionVars false

/-! ## What the simulator reads of the prover -/

/-- **The public part of the skeleton model's prover**: the number of challenges, when each secret
table is committed, which positions are opened. -/
structure PubProto where
  n : ℕ
  cK : Tbl → ℕ
  opened : List Out → Tbl → Pos → Bool

/-- The public part as a prover with no message and no row. -/
def PubProto.toProto (pp : PubProto) : Proto Unit Inp Out Msg Tbl Pos where
  n := pp.n
  msgFn := fun _ _ ↦ []
  cK := pp.cK
  rowFn := fun _ _ _ _ ↦ .inl []
  opened := pp.opened

/-- The public part of a prover. -/
def PubProto.of {S : Type} (P : Proto S Inp Out Msg Tbl Pos) : PubProto := ⟨P.n, P.cK, P.opened⟩

theorem sim_pub {S : Type} (P : Proto S Inp Out Msg Tbl Pos)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) {Pf : Type} (skel : OracleComp DSpec Pf)
    (c₀ : List (Inp × Out)) :
    QuotientZk.sim P simV skel c₀ = QuotientZk.sim (PubProto.of P).toProto simV skel c₀ := rfl

theorem simGameRpmD_pub {S : Type} (P : Proto S Inp Out Msg Tbl Pos)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos))
    (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (D : QuotientZk.Deployed.Proof → OracleComp (permutationOracleSpec KSt) Bool) :
    QuotientZk.DRpm.simGameRpmD P simV skel D =
      QuotientZk.DRpm.simGameRpmD (PubProto.of P).toProto simV skel D := rfl

/-! ## The simulator -/

/-- **The simulator of the end theorem**: for each statement, `rpmSimulator` (`QuotientZk`'s
random-permutation simulator in the statement's shape) at the public part `pp stmt` of the prover, the
view simulator `simV stmt`, the skeleton `skel stmt`, the proof formatted by `fmt`. A compiled
definition. -/
def zkSimulator (pp : Statement → PubProto)
    (simV : Statement → List Out → ProbComp (View Msg Inp Tbl Pos))
    (skel : Statement → OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof)) :
    Statement → StateT RpmSimState ProbComp (Option Proof) :=
  fun stmt ↦ rpmSimulator (pp stmt).toProto (simV stmt) (skel stmt) fmt

theorem coinsUniform_rpmSimOracle : CoinsUniform rpmSimOracle := fun _ ↦ rfl

/-- **`QuotientZk`'s closeness of the real and simulated games** for the prover `P`, the view
simulator `simV`, the skeleton `skel`, for every coin-free distinguisher reading the statement's proof
through `fmt`. -/
def CoreClose {S : Type} [SampleableType S] (P : Proto S Inp Out Msg Tbl Pos)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos))
    (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof)) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (D₀ : Option Proof → OracleComp PermSpec Bool) (Q : ℕ), (∀ pf, IsTotalQueryBound (D₀ pf) Q) →
    Close (QuotientZk.DRpm.realGameRpmD P skel fun pf ↦ fmt pf >>= D₀)
      (QuotientZk.DRpm.simGameRpmD P simV skel fun pf ↦ fmt pf >>= D₀) (ε Q)

/-- **Zero knowledge for `zkSimulator`**: for each statement and witness of the relation, a prover
`P stmt w` whose public part is `pp stmt` (`hpub`), within `εR` of the statement's prover
(`RealBridge`), with `QuotientZk`'s real and simulated games within `ε` (`CoreClose`), gives
`ZeroKnowledgeWith s₀ (zkSimulator pp simV skel fmt) rpmSimOracle (εR + ε)` from any initial state. -/
theorem zeroKnowledgeWith_of_core {S : Type} [SampleableType S]
    (P : Statement → Secret → Proto S Inp Out Msg Tbl Pos) (pp : Statement → PubProto)
    (simV : Statement → List Out → ProbComp (View Msg Inp Tbl Pos))
    (skel : Statement → OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof)) (s₀ : RpmSimState)
    (εR ε : ℕ → ℝ≥0∞)
    (hpub : ∀ stmt w, Relation stmt w → PubProto.of (P stmt w) = pp stmt)
    (hreal : ∀ stmt w, Relation stmt w → RealBridge stmt w (P stmt w) (skel stmt) fmt εR)
    (hcore : ∀ stmt w, Relation stmt w → CoreClose (P stmt w) (simV stmt) (skel stmt) fmt ε) :
    ZeroKnowledgeWith s₀ (zkSimulator pp simV skel fmt) rpmSimOracle fun Q ↦ εR Q + ε Q := by
  apply zeroKnowledgeWith_of_coinFree _ _ _ coinsUniform_rpmSimOracle
  intro stmt w hw D₀ Q hD₀
  have hI : idealExperimentWith s₀ (zkSimulator pp simV skel fmt) rpmSimOracle stmt
      (fun pf ↦ simulateQ liftPerm (D₀ pf)) =
      QuotientZk.DRpm.simGameRpmD (P stmt w) (simV stmt) (skel stmt) fun pf ↦ fmt pf >>= D₀ := by
    rw [simGameRpmD_pub, hpub stmt w hw]
    exact rpmIdeal_eq (pp stmt).toProto (simV stmt) (skel stmt) fmt s₀ D₀
  rw [hI]
  exact (hreal stmt w hw D₀ Q hD₀).trans (hcore stmt w hw D₀ Q hD₀)

end PcsQuotient.EndToEnd
