-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s two-oracle simulator (`Common.simulator2`), its folding of a random
-- oracle into a simulator's state (`Common.foldRO`, `Common.run'_simulateQ_foldRO`).
import ZK.Assembly

/-!
# `QuotientZk`'s simulator in the statement's shape

The statement's `idealExperiment` (`Security.lean`) is: the simulator's proof, a computation in
`StateT S ProbComp`, then the distinguisher, every query answered by an oracle
`QueryImpl RandomPermutationOracles (StateT S ProbComp)`, from an initial state. `QuotientZk`'s
simulated game in the random-permutation model (`simGameRpmD`) has that shape:

* **the state** (`RpmSimState`): the two-oracle simulator's state (the edges it has answered and the
  rooted sponge states) and the random oracle's cache of Keccak-256 and of the permutation on bytes;
* **the simulator** (`rpmSimulator`): `zk_rom`'s `sim` on the skeleton with its duplex bookkeeping
  (`skelRec`: the challenges drawn first and programmed, the view from `simV`, fresh private digests
  at the unopened leaves), which gives the skeleton's proof, the bookkeeping and the programmed cache;
  the state set to them; then the statement's proof read from the skeleton's (`fmt`), its permutation
  calls answered as the distinguisher's;
* **the oracle** (`rpmSimOracle`): coins forwarded; `π` and `π⁻¹` on lanes, asked on bytes
  (`laneToByte`), answered by `common`'s two-oracle simulator `S₂` (`simulator2`) with its `H` and `F`
  the random oracle on the state's cache (`foldRO`).

**`rpmIdeal_eq`**: its ideal experiment is `simGameRpmD`, for every coin-free distinguisher: once the
statement's `simulator` and `Simulator.simOracle` are these (at the joint-model instance), the
`IdealBridge` of `ZK/Assembly.lean` holds with `εI = 0` (`idealBridge_rpm`).
-/

open OracleComp OracleSpec Common
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto View)

set_option linter.unusedSectionVars false

/-- **The simulator's state**: the two-oracle simulator's (edges, rooted states) and the random
oracle's cache of Keccak-256 and of the permutation on bytes. -/
abbrev RpmSimState := QuotientZk.DRpm.SimSt × QuotientZk.DRpm.HF.QueryCache

/-! ### Compiled transcriptions

`common` marks `simulator2` and `foldRO` `noncomputable`; their bodies compile. The statement's
simulator must be a compiled definition (`formal/Statement`'s convention), so it is to use these
transcriptions, equal to `common`'s by definition. -/

section Compiled

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (Pd : Common.Padding Msg (Dg × E)) [Pd.Lawful]

/-- `Common.rootedAnswer2`, compiled. -/
def rootedAnswerC (β : List (Dg × E)) (x : SpState Dg E C) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) (SpState Dg E C) :=
  match Pd.unpad β with
  | some m => do
    let d ← hQuery (E := E) (C := C) m
    let ec ← (liftM ($ᵗ (E × C)) : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
    pure ((d, ec.1), ec.2)
  | none => fQuery (Dg := Dg) x

/-- `Common.simulator2`, compiled. -/
def simulator2C : QueryImpl (permutationOracleSpec (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .forward x => StateT.mk fun σ ↦
      match forwardLookup σ.edges x with
      | some y => pure (y, σ)
      | none =>
        match chainOf σ.chains x with
        | some (s, β) => do
          let y ← rootedAnswerC Pd (β ++ [blockTo s x]) x
          pure (y, ⟨(x, y) :: σ.edges, (y, β ++ [blockTo s x]) :: σ.chains⟩)
        | none => do
          let y ← fQuery (Dg := Dg) x
          pure (y, ⟨(x, y) :: σ.edges, σ.chains⟩)
  | .inverse y => StateT.mk fun σ ↦
      match inverseLookup σ.edges y with
      | some x => pure (x, σ)
      | none => do
        let x ← (liftM ($ᵗ (SpState Dg E C)) :
          OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
        pure (x, ⟨(x, y) :: σ.edges, σ.chains⟩)

theorem simulator2C_eq : simulator2C (C := C) Pd = simulator2 Pd := rfl

end Compiled

/-- `Common.foldRO`, compiled. -/
def foldROC {ι : Type} {spec : OracleSpec.{0, 0} ι} {ι' : Type} [DecidableEq ι']
    {hs : OracleSpec.{0, 0} ι'} [∀ t : hs.Domain, SampleableType (hs.Range t)] {σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp (unifSpec + hs)))) :
    QueryImpl spec (StateT (σ × hs.QueryCache) ProbComp) :=
  (hs.romImpl.mapStateTBase impl).flattenStateT

theorem foldROC_eq {ι : Type} {spec : OracleSpec.{0, 0} ι} {ι' : Type} [DecidableEq ι']
    {hs : OracleSpec.{0, 0} ι'} [∀ t : hs.Domain, SampleableType (hs.Range t)] {σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp (unifSpec + hs)))) : foldROC impl = foldRO impl :=
  rfl

/-- **The simulator's permutation**: `π` and `π⁻¹` on lanes, asked on bytes, answered by `S₂`
(`simulator2`, compiled) from the state, its `H` and `F` the random oracle on the state's cache
(`foldRO`, compiled). -/
def rpmPermOracle : QueryImpl PermSpec (StateT RpmSimState ProbComp) :=
  foldROC (simulator2C (Msg := List UInt8) keccakPadding) ∘ₛ QuotientZk.laneToByte

/-- **The simulator's oracle** (the statement's `Simulator.simOracle`'s role): coins forwarded, `π`
and `π⁻¹` by `rpmPermOracle`. -/
def rpmSimOracle : QueryImpl RandomPermutationOracles (StateT RpmSimState ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr q => rpmPermOracle q

section Sim

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos)
  (simV : List Out → ProbComp (View Msg Inp Tbl Pos))
  (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
  (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))

/-- **The simulator** (the statement's `simulator`'s role): `sim` on the skeleton with its duplex
bookkeeping, the state set to the bookkeeping and the programmed cache, then the statement's proof read
from the skeleton's by `fmt`, its permutation calls answered by `rpmPermOracle`. It uses of `P` only
its public parts (`P.n`, `P.cK`, `P.opened`: `sim` reads nothing else). -/
def rpmSimulator : StateT RpmSimState ProbComp (Option Proof) := do
  let z ← liftM (QuotientZk.sim P simV (QuotientZk.DRpm.skelRec skel) [])
  set ((z.1.2, QuotientZk.DRpm.hfOf z.2) : RpmSimState)
  simulateQ rpmPermOracle (fmt z.1.1)

/-- **The ideal experiment with this simulator**, in the statement's shape (`idealExperiment`), from
any initial state. -/
def rpmIdeal (s₀ : RpmSimState) (D : Option Proof → OracleComp RandomPermutationOracles Bool) :
    ProbComp Bool :=
  (do
    let proof ← rpmSimulator P simV skel fmt
    simulateQ rpmSimOracle (D proof)).run' s₀

theorem rpmSimOracle_liftPerm : rpmSimOracle ∘ₛ liftPerm = rpmPermOracle := by
  funext q
  simp [QueryImpl.apply_compose, liftPerm, rpmSimOracle]

theorem runS2_eq (X : OracleComp PermSpec Bool) (σ : QuotientZk.DRpm.SimSt)
    (c : QuotientZk.DRpm.HF.QueryCache) :
    QuotientZk.DRpm.runS2 X σ c = (simulateQ rpmPermOracle X).run' (σ, c) := by
  unfold QuotientZk.DRpm.runS2 rpmPermOracle
  rw [foldROC_eq, simulator2C_eq, run'_simulateQ_foldRO, QueryImpl.simulateQ_compose]

/-- **The statement-shaped ideal experiment is `QuotientZk`'s simulated game.** -/
theorem rpmIdeal_eq (s₀ : RpmSimState) (D₀ : Option Proof → OracleComp PermSpec Bool) :
    rpmIdeal P simV skel fmt s₀ (fun pf ↦ simulateQ liftPerm (D₀ pf)) =
      QuotientZk.DRpm.simGameRpmD P simV skel fun pf ↦ fmt pf >>= D₀ := by
  unfold rpmIdeal rpmSimulator QuotientZk.DRpm.simGameRpmD
  simp only [← QueryImpl.simulateQ_compose, rpmSimOracle_liftPerm, runS2_eq, simulateQ_bind,
    StateT.run'_eq, StateT.run_bind, bind_assoc, map_bind]
  simp [StateT.run, liftM, monadLift, MonadLift.monadLift, StateT.lift, set, StateT.set]

/-- **The ideal bridge holds exactly** for a statement whose ideal experiment is this simulator's
(`hI`: the statement's `simulator` and `Simulator.simOracle` defined as `rpmSimulator` and
`rpmSimOracle`, from some initial state). -/
theorem idealBridge_rpm [SampleableType S] (stmt : Statement) (s₀ : RpmSimState)
    (hI : ∀ D, idealExperiment stmt D = rpmIdeal P simV skel fmt s₀ D) :
    IdealBridge stmt P simV skel fmt fun _ ↦ 0 := by
  intro D₀ Q _
  rw [hI, rpmIdeal_eq]
  exact Close.of_evalDistEq EvalDistEq.rfl

end Sim

/-! ## The assembly with this simulator -/

section Main

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **Zero knowledge with `QuotientZk`'s simulator in the statement**: `zeroKnowledge_of_bridges`
with the ideal bridge exact (`εI = 0`), for a statement whose ideal experiment is `rpmSimulator`'s at the
joint model's public data (`hI`). -/
theorem zeroKnowledge_of_rpmSimulator
    (J : Statement → Secret → JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂)
    (skel : Statement → OracleComp DSpec QuotientZk.Deployed.Proof)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (QP Qp Qfmt : ℕ) (εFS : ℝ≥0∞) (εR : ℕ → ℝ≥0∞) (s₀ : RpmSimState)
    (hskel : ∀ stmt, IsTotalQueryBound (skel stmt) QP)
    (hfmt : ∀ pf, IsTotalQueryBound (fmt pf) Qfmt)
    (hvalid : ∀ stmt w, Relation stmt w → (J stmt w).Valid)
    (hFS : ∀ stmt w, Relation stmt w → QuotientZk.Deployed.FSFresh (J stmt w).P (skel stmt) [] εFS)
    (hduplex : ∀ stmt w, Relation stmt w →
      QuotientZk.DRpm.DuplexDiscipline (J stmt w).P (skel stmt))
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (J stmt w).P keccak256OverPermutation queryPermutation
        (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s (skel stmt))
        permutationCallCost Qp)
    (hreal : ∀ stmt w, Relation stmt w → RealBridge stmt w (J stmt w).P (skel stmt) fmt εR)
    (hI : ∀ stmt w, Relation stmt w → ∀ D,
      idealExperiment stmt D = rpmIdeal (J stmt w).P (J stmt w).simV (skel stmt) fmt s₀ D) :
    ZeroKnowledge (zkBound QP Qp Qfmt εFS εR (fun _ ↦ 0)) :=
  zeroKnowledge_of_bridges J skel fmt QP Qp Qfmt εFS εR (fun _ ↦ 0) hskel hfmt hvalid hFS hduplex
    hprover hreal fun stmt w hw ↦ idealBridge_rpm _ _ _ _ stmt s₀ (hI stmt w hw)

/-- **Zero knowledge of the membership proof with `QuotientZk`'s simulator in the statement, on the
deployed skeleton**: `zeroKnowledge_deployed` with the ideal bridge exact (`εI = 0`), for a statement
whose ideal experiment is `rpmSimulator`'s at the joint model's public data (`hI`). On the constant-root
skeleton (see `zeroKnowledge_deployed`); the end theorem is `zeroKnowledge_end` (`ZK/Main.lean`). -/
theorem zeroKnowledge_deployed_rpmSimulator
    (J : Statement → Secret → JointData K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂)
    (stmtD : Statement → QuotientZk.Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (sh : Statement → QuotientZk.Deployed.Shape)
    (hsh : ∀ stmt, sh stmt = QuotientZk.Deployed.deployedShape (stmtD stmt) idW idσ idQ rowsW)
    (fmt : QuotientZk.Deployed.Proof → OracleComp PermSpec (Option Proof))
    (Qp Qfmt : ℕ) (εR : ℕ → ℝ≥0∞) (s₀ : RpmSimState)
    (hfmt : ∀ pf, IsTotalQueryBound (fmt pf) Qfmt)
    (hvalid : ∀ stmt w, Relation stmt w → (J stmt w).Valid)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (J stmt w).P keccak256OverPermutation queryPermutation
        (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (QuotientZk.Deployed.skel (sh stmt))) permutationCallCost Qp)
    (hreal : ∀ stmt w, Relation stmt w →
      RealBridge stmt w (J stmt w).P (QuotientZk.Deployed.skel (sh stmt)) fmt εR)
    (hI : ∀ stmt w, Relation stmt w → ∀ D, idealExperiment stmt D =
      rpmIdeal (J stmt w).P (J stmt w).simV (QuotientZk.Deployed.skel (sh stmt)) fmt s₀ D) :
    ZeroKnowledge (zkBoundDeployed Qp Qfmt εR fun _ ↦ 0) :=
  zeroKnowledge_deployed J stmtD idW idσ idQ rowsW hrows sh hsh fmt Qp Qfmt εR (fun _ ↦ 0) hfmt hvalid
    hprover hreal fun stmt w hw ↦ idealBridge_rpm _ _ _ _ stmt s₀ (hI stmt w hw)

end Main

end PcsQuotient.EndToEnd
