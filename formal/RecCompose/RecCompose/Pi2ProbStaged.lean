-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's analogue of `formal/UniComplete/UniComplete/
-- ProbExp.lean` (`stagedU`, its stages) and `ProbGrind.lean` (`rejectGood_uni`, the grinding through mumbai's
-- proof-of-work potential), from π2's honest prover (`RecCompose.Pi2Prover`, `crates/leanvm_rec/src/pi2/prover.rs`) and
-- the Statement's contract (`formal/RecStatement`, written with Keccak-256 explicit in `Pi2CompleteH`). Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls, the
-- logged random oracle and its potential engine, `powPot`, `missProb`, the run at a log's answers.
import RecCompose.Pi2CompleteEnd
import RecCompose.Facts
import UniComplete.ProbGrind

/-!
# π2's completeness experiment, staged

**The P1 class**: π1-rec3's prover is a two-call program `P1k` (Keccak-256 and Keccak-f[1600] its calls) whose run over
the random permutation is `P1` (part of `Pi2ExperimentLe`).

**`pi2Staged D C Fa P1k input rows q : Pi2Staged`**, π2's experiment's stages over the two calls:

* `A` (`stageA`): the setup, `P1k`, π1-rec3's graph on its proof (`a1`), then π2's prover up to `α`: its setup, IV, the
  witness it takes, the seed, the public values, `W`'s commitment and root (`pre2`); `inp` `α`'s input, `536` bytes
  (`fixLen`: `tInput` of the writer, `536` bytes when the values match the reads);
* the three chained answers `α, β, γ`; `B` (`stageB`) `Q`'s stack, commitment and root (`mid2`); `t`'s query on the
  writer's input; `C` (`stageC`) the values at `t`, `ρ` (`post2`), the three openings and the contract
  (`Pi2H.verifierWithH`); a proof of `P1k`'s none is the pair `(false, false)`;
* the priors: `(roots, w, pub)` for the triple (`Bad`: the copy argument's `BadCopy`), with the triple for `t`
  (`badT`: `¬ BadCopy ∧ BadT`).

**Proved**: `Holds.L_ne`, `inp_length`, `badCard` (`card_badCopy_pi2`), `badTCard` (`card_badT_pi2`, a non-hole position
from the view check, `nonHole_pi2`), and `rejectGood` with `εpow = N · (1 − 2^-17)^nonceFuel`
(**`rejectGood_pi2`**: mumbai's potential, as `ProbGrind`, from the core at any pure `(H, F)`, **`rejects_at`**: on a
run the graph accepts at good challenges, the witness complete (`Pi2WitnessComplete`), π2's honest prover either fails
one opening's proof of work or its proof is accepted, `pi2_accepts`, π1's openings by `Pi2Pi1Openings`).

**Named** (each about the explicit `pi2Staged`, in `UniComplete.ProbHyp`'s style):

* `Pi2ExperimentLe`: the experiment's event is at most the staged run's against the random permutation (`P1` is `P1k`
  over it, the code commutes with the simulation, the none branch's dummy calls change nothing);
* `Pi2RunAt`: at pure `(H, F)` the staged run is the experiment at `Id`, its priors and challenges the honest prover's
  (the code's commutation and the prover's split at `α` and `t`, `runAt_stagedU`'s analogue);
* `Pi2RunDuplex`, `Pi2RunCost N`, `Pi2HashBeforeAlpha` (no `32`- or `536`-byte input hashed in `A`, `P1k`'s included),
  `Pi2TFresh εt`;
* `Pi2Pi1Openings`: at pure `(H, F)`, on a π1 proof the graph accepts with an honest witness, the contract's three π1
  openings of π2's honest proof accept (the calls' agreement, `Pi1OpeningsAgree`'s at an explicit Keccak-256);
* `Pi2WitnessComplete` (`Pi2CompleteEnd`).

**`recCompleteness2_pi2_staged`**: `RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) nonceFuel)
(delta2 N εt (N · missProb 17 ^ nonceFuel))`; **`delta2_pi2_le`**: below `2^-164` at `N ≤ 2^50`, `εt ≤ 2^-200`;
**`recCompleteness_pi2_staged_fs`**: the recursive verifier's completeness end to end.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2G

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open E2ECompleteness (ro runAt HashOK)
open UniComplete.Prob (GoodL winState one_le_powPot_of_opening_none)
open Pi2S Pi2K Pi2P Pi2E
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## π2's prover, cut at `α` and at `t` -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **Before `α`**: the public values, `W`'s stack, commitment and root (`pi2ProveStreamWith`'s first lines). -/
def pre2 (G : RecPiop.Circuit E) (reads : List Read) (values : List PublicValue) (w : ℕ → K) :
    UniComplete.WrM m (Array K × LeanVM.Prover.Tree) := do
  sendPublic (reads.zip values)
  let wStack := placePublic (layoutsOf G.logN).1 fun i ↦ (wTableB G w).getD i 0
  let wTree ← (StateT.lift (E2ECompleteness.commitWithH H (layoutsOf G.logN).1.logN wStack) :
    UniComplete.WrM m LeanVM.Prover.Tree)
  UniComplete.sendRoot (digestScalars wTree.root)
  return (wStack, wTree)

/-- **From `γ` to `t`**: `Q`'s stack, commitment and root. -/
def mid2 (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ : E) : UniComplete.WrM m (Array K × LeanVM.Prover.Tree) := do
  let qStack := placePublic (layoutsOf G.logN).2.1 (qEntry G.logN (hNovel G w α β γ) (qNovel G w α β γ))
  let qTree ← (StateT.lift (E2ECompleteness.commitWithH H (layoutsOf G.logN).2.1.logN qStack) :
    UniComplete.WrM m LeanVM.Prover.Tree)
  UniComplete.sendRoot (digestScalars qTree.root)
  return (qStack, qTree)

/-- **After `t`**: the values at `t`, `ρ`, the output. -/
def post2 (G : RecPiop.Circuit E) (setupStack : Array K) (input : List UInt8) (values : List PublicValue) (w : ℕ → K)
    (wS : Array K) (wT : LeanVM.Prover.Tree) (qS : Array K) (qT : LeanVM.Prover.Tree) (α β γ t : E) :
    UniComplete.WrM m Pi2Out := do
  let a := foldValues G.logN G.logW (wTableB G w) t
  let ξ := xiOf G.logN setupStack β t
  UniComplete.sendScalars (a ++ [ξ])
  let ρ ← UniComplete.sampleW H
  let c ← get
  return ⟨c.stream, wS, wT, qS, qT, ⟨publicScalarsOf input values, α, β, γ, t, a, ξ, ρ⟩⟩

end With

/-- The writer after a challenge whose hash is `s` (`sampleW`'s update). -/
def absorbW (w : UniComplete.Wr) (s : Digest) : UniComplete.Wr :=
  { w with absorbed := w.stream.size, state := s, challenges := w.challenges.push (chalP s) }

/-- `x` if it has `L` bytes, else `L` zeros. -/
def fixLen (L : ℕ) (x : List UInt8) : List UInt8 := if x.length = L then x else List.replicate L 0

theorem fixLen_length (L : ℕ) (x : List UInt8) : (fixLen L x).length = L := by
  unfold fixLen
  split_ifs with h
  · exact h
  · exact List.length_replicate

/-! ## The experiment with Keccak-256 explicit -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π2's completeness experiment with Keccak-256 explicit**: the setup, π1's proof `p1o`, π1-rec3's graph on it, π2's
honest prover (`nonceFuel` its search), the contract. -/
noncomputable def expW2 (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : m (Option UniStatement.UniProof)) (input : Vector UInt8 32) : m (Bool × Bool) := do
  let trees ← Pi2H.setupTreesWithH H F D
  match ← p1o with
  | none => return (false, false)
  | some p1 =>
    let a1 ← Pi2H.pi1GraphVerifierWithH H F D trees.roots.pi1 input p1
    match ← pi2ProverWith H F D C Fa PcsQuotient.nonceFuel input p1 with
    | none => return (a1, false)
    | some p2 => return (a1, ← Pi2H.verifierWithH H F D trees.roots input p2)

/-- What stage `A` carries: the setup, π1's proof and the graph's verdict, π2's prover's roots, setup tree, witness,
`W`'s stack and tree, the writer before `α`. -/
structure StA where
  trees : RecSetupTrees
  p1 : Option UniStatement.UniProof
  a1 : Bool
  roots : RecSetupRoots
  setupTree : LeanVM.Prover.Tree
  vw : List PublicValue × (ℕ → K)
  wS : Array K
  wT : LeanVM.Prover.Tree
  wr : UniComplete.Wr

/-- What stage `B` carries: `A`'s, the triple, `Q`'s stack and tree, the writer before `t`. -/
structure StB where
  a : StA
  α : E
  β : E
  γ : E
  qS : Array K
  qT : LeanVM.Prover.Tree
  wr : UniComplete.Wr

/-- **Stage A**: the setup, π1's proof, the graph, π2's prover up to `α`. -/
noncomputable def stageA (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : m (Option UniStatement.UniProof)) (input : Vector UInt8 32) : m StA := do
  let trees ← Pi2H.setupTreesWithH H F D
  match ← p1o with
  | none => return ⟨trees, none, false, trees.roots, trees.pi2, ([], fun _ ↦ 0), #[], trees.pi2, UniComplete.Wr.start default⟩
  | some p1 =>
    let a1 ← Pi2H.pi1GraphVerifierWithH H F D trees.roots.pi1 input p1
    let tr ← Pi2H.setupTreesWithH H F D
    let iv ← Pi2H.ivOfH H D tr.roots
    let vw := pi2Choice D C Fa tr.roots input p1.stream
    let seed ← H (RecStatement.name ++ iv ++ input.toList)
    let (ws, wr) ← (pre2 H (C.G tr.roots) (D.circuitAt tr.roots.pi1).circuit.reads vw.1 vw.2).run
      (UniComplete.Wr.start seed)
    return ⟨trees, some p1, a1, tr.roots, tr.pi2, vw, ws.1, ws.2, wr⟩

/-- **Stage B**: after `α, β, γ` (their hashes `s₁, s₂, s₃`), `Q`. -/
def stageB (D : RecDeployment) (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest) : m StB := do
  let w3 := absorbW (absorbW (absorbW a.wr s₁) s₂) s₃
  let (qs, wr) ← (mid2 H (C.G a.roots) a.vw.2 (chalP s₁) (chalP s₂) (chalP s₃)).run w3
  return ⟨a, chalP s₁, chalP s₂, chalP s₃, qs.1, qs.2, wr⟩

/-- **Stage C**: after `t` (its hash `st`), the rest of the prover, its openings and the contract. -/
noncomputable def stageC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB) (st : Digest) :
    m (Bool × Bool) := do
  match b.a.p1 with
  | none => return (false, false)
  | some p1 =>
    let G := C.G b.a.roots
    let c := D.circuitAt b.a.roots.pi1
    let (out, _) ← (post2 H G c.setupStack input.toList b.a.vw.1 b.a.vw.2 b.a.wS b.a.wT b.qS b.qT b.α b.β b.γ
      (chalP st)).run (absorbW b.wr st)
    let o := (Spec.of c.circuit).core.run out.inputs
    let pW ← E2ECompleteness.proveOpeningWithH H F PcsQuotient.nonceFuel (layoutsOf G.logN).1 out.wTree out.wStack
      [⟨o.witnessPoint, o.fold⟩]
    let pS ← E2ECompleteness.proveOpeningWithH H F PcsQuotient.nonceFuel (layoutsOf G.logN).2.2 b.a.setupTree
      c.setupStack [⟨o.setupPoint, out.inputs.ξ⟩]
    let pQ ← E2ECompleteness.proveOpeningWithH H F PcsQuotient.nonceFuel (layoutsOf G.logN).2.1 out.qTree out.qStack
      [⟨o.quotientPoint, o.quotientValue⟩, ⟨o.sumPoint, o.sumValue⟩]
    match pW, pS, pQ with
    | some x, some y, some z =>
      let v ← Pi2H.verifierWithH H F D b.a.trees.roots input ⟨out.stream, p1.c1, p1.c2, p1.setup, x, y, z⟩
      return (b.a.a1, v)
    | _, _, _ => return (b.a.a1, false)

end With

/-- The prior of the triple: the prover's roots, its witness, the public limbs. -/
abbrev Pr2 : Type := RecSetupRoots × (ℕ → K) × (ℕ → List E)

/-- **π2's experiment's stages over the two calls.** -/
noncomputable def pi2Staged (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (input : Vector UInt8 32) : Pi2Staged where
  α := StA
  β := StB
  ρ := Pr2
  τ := Pr2 × E × E × E
  inp a := fixLen 536 (UniComplete.Prob.tInput a.wr)
  pr a := (a.roots, a.vw.2, Fa.pubOf a.roots (publicScalarsOf input.toList a.vw.1))
  A := stageA callKeccak256 callKeccakF1600 D C Fa P1k input
  B := stageB callKeccak256 D C
  tin b := UniComplete.Prob.tInput b.wr
  prT b := ((b.a.roots, b.a.vw.2, Fa.pubOf b.a.roots (publicScalarsOf input.toList b.a.vw.1)), b.α, b.β, b.γ)
  C := stageC callKeccak256 callKeccakF1600 D C input

open Classical in
/-- **The bad triples**: the copy argument's at the prior's circuit, witness and public limbs. -/
noncomputable def badSet2 (C' : RecSetupRoots → RecPiop.Circuit E) (p : Pr2) : Finset (E × E × E) :=
  Finset.univ.filter fun v ↦ BadCopy (C' p.1) p.2.1 p.2.2 v.1 v.2.1 v.2.2

/-- **The bad `t`**: off the bad triples, `BadT`. -/
def badT2 (C' : RecSetupRoots → RecPiop.Circuit E) (fp : Pr2 × E × E × E) (t : E) : Prop :=
  ¬ BadCopy (C' fp.1.1) fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2 ∧ BadT (C' fp.1.1) fp.1.2.1 fp.2.1 fp.2.2.1 fp.2.2.2 t

/-! ## The named inputs -/

/-- The roots of the setup at a pure `(H, F)`. -/
abbrev rootsH (D : RecDeployment) (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) : RecSetupRoots :=
  (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots

/-- **Named: the experiment, staged.** π2's completeness experiment's event (the graph accepting, the contract
rejecting) is at most the staged run's against the random permutation: `P1` is `P1k` over it, the setup, the graph,
π2's prover and the contract commute with the simulation (`keccakCallsOverRandomPermutation`), and when `P1k` returns
none the staged run's dummy challenges change no verdict. -/
def Pi2ExperimentLe (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof)) :
    Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← recCompletenessExperiment2 D P1 (pi2Prover D C Fa PcsQuotient.nonceFuel) input rows q}[
      v.1 = true ∧ v.2 = false] ≤
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (pi2Staged D C Fa (P1k input rows q) input).run).run' []}[
      z.1.1.1 = true ∧ z.1.1.2 = false]

/-- **Named: the staged run at pure functions** (`UniComplete.Prob.runAt_stagedU`'s analogue: the code's commutation
with `totalImpl H F` and the prover's split at `α` and `t`): its verdict is `expW2` at `Id`, and when `P1k` gives `p1`
with an honest witness, its priors and challenges are the honest prover's (`outOf`'s inputs). -/
def Pi2RunAt (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof)) :
    Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) (Ht : List UInt8 → Digest)
    (Ft : KeccakState → KeccakState),
    (runAt Ht Ft (pi2Staged D C Fa (P1k input rows q) input).run).1.1 =
      Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure (runAt Ht Ft (P1k input rows q))) input) ∧
    ∀ p1, runAt Ht Ft (P1k input rows q) = some p1 →
      (∃ vw, Pi2Good D C Fa (rootsH D Ht Ft) input p1.stream vw) →
      (runAt Ht Ft (pi2Staged D C Fa (P1k input rows q) input).run).2 =
          (((rootsH D Ht Ft), (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2,
            Fa.pubOf (rootsH D Ht Ft) (publicScalarsOf input.toList (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1)),
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.α,
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.β,
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.γ) ∧
      (runAt Ht Ft (pi2Staged D C Fa (P1k input rows q) input).run).1.2.2 =
          (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).1
            (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream).2).inputs.t ∧
      (runAt Ht Ft (pi2Staged D C Fa (P1k input rows q) input).run).1.2.1 =
        (runAt Ht Ft (pi2Staged D C Fa (P1k input rows q) input).run).2

/-- **Named: the staged run follows the duplex discipline** (`ProverDuplex`'s, `VerifierDisc`'s, `P1k`'s). -/
def Pi2RunDuplex (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof)) :
    Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q → DuplexVm (pi2Staged D C Fa (P1k input rows q) input).run []

/-- **Named: the staged run's block count** is at most `N` (`P1k`'s, the setup's, the graph's, π2's prover's and
contract's). -/
def Pi2RunCost (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    (N : ℕ) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Common.QueryCostAtMost (pi2Staged D C Fa (P1k input rows q) input).run hashBlocks N

/-- **Named: before `α`, nothing of `32` or `536` bytes is hashed** (`hashA_stagedU`'s analogue; `P1k`'s hashes, the
setup's leaves and nodes, the graph's openings, π2's IV, digest and seed preimages, `W`'s tree). -/
def Pi2HashBeforeAlpha (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof)) :
    Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q → HashOK (GoodL 536) (pi2Staged D C Fa (P1k input rows q) input).A

/-- **Named: `t`'s input is fresh** but with probability `εt` (`TQueryFresh`'s analogue). -/
def Pi2TFresh (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    (εt : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let p ← (simulateQ ro (pi2Staged D C Fa (P1k input rows q) input).pre).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa (P1k input rows q) input).tin p.1.1)) ≠ none] ≤ εt

/-- **Named: π1's openings in the contract** (deterministic; `Couplings.Pi1OpeningsAgree`'s content at an explicit
Keccak-256): at pure `(H, F)`, on a π1 proof π1-rec3's graph accepts, its openings over `(H, F)`, the witness π2's
prover takes honest, the contract's three π1 calls on π2's honest proof decode and their openings accept. -/
def Pi2Pi1Openings (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) : Prop :=
  ∀ (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (input : Vector UInt8 32)
    (p1 : UniStatement.UniProof) (proof : RecProof),
    Pi2Good D C Fa (rootsH D Ht Ft) input p1.stream (pi2Choice D C Fa (rootsH D Ht Ft) input p1.stream) →
    Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D (rootsH D Ht Ft).pi1 input p1) = true →
    Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C Fa PcsQuotient.nonceFuel input p1) = some proof →
      ∃ ops, pi1OpsOf D (rootsH D Ht Ft) input proof.stream = some ops ∧
        Id.run (Pi2H.openSeqH (m := Id) (Pure.pure ∘ Ht) Ft (registryOf D.pi1.shape 24) ops proof) = true

/-! ## The core at pure functions -/

/-- **The graph's verdict includes its checks.** -/
theorem graphChecks_of_verifierH {H : List UInt8 → Id Digest} {F : KeccakState → Id KeccakState} {D : RecDeployment}
    {roots : UniStatement.SetupRoots} {input : Vector UInt8 32} {p1 : UniStatement.UniProof}
    (h : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) H F D roots input p1) = true) :
    pi1GraphChecks (D.pi1IvAt roots) input p1.stream = true := by
  unfold Pi2H.pi1GraphVerifierWithH at h
  unfold pi1GraphChecks
  split at h
  · exact absurd h (by simp)
  · rename_i out hout
    rw [hout]
    dsimp only
    by_contra hc
    rw [Bool.not_eq_true] at hc
    rw [hc] at h
    exact absurd h (by simp)

/-- **π2's honest prover returns none only at a failed opening.** -/
theorem pi2Prover_none {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (Hk : List UInt8 → Digest)
    (F : KeccakState → Id KeccakState) (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniStatement.UniProof)
    (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C Fa fuel input p1) = none) :
    ∃ L tree stack claims, E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel L tree stack claims =
      none := by
  rw [pi2ProverWith_run, pi2ProveWith_run, logN_G Fa] at hp
  revert hp
  generalize hW : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).1 _ _ _ = rW
  generalize hS : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).2.2 _ _ _ = rS
  generalize hQ : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).2.1 _ _ _ = rQ
  intro hp
  cases rW with
  | none => exact ⟨_, _, _, _, hW⟩
  | some a =>
    cases rS with
    | none => exact ⟨_, _, _, _, hS⟩
    | some b =>
      cases rQ with
      | none => exact ⟨_, _, _, _, hQ⟩
      | some c => simp at hp

/-- **The experiment at `Id`, π1's prover giving none.** -/
theorem expW2_none (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (D : RecDeployment)
    (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32) :
    Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure none) input) = (false, false) := rfl

/-- **The experiment at `Id`, π1's prover giving `p1`**: the graph's verdict, and the contract's on π2's proof. -/
theorem expW2_some (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (D : RecDeployment)
    (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32) (p1 : UniStatement.UniProof) :
    Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure (some p1)) input) =
      match Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C Fa PcsQuotient.nonceFuel input p1) with
      | none => (Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D
          (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots.pi1 input p1), false)
      | some p2 => (Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D
          (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots.pi1 input p1),
        (Id.run (Pi2H.contractWithH (m := Id) (Pure.pure ∘ Ht) Ft D
          (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots input p2)).1) := by
  unfold expW2
  simp only [pure_bind]
  generalize pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C Fa PcsQuotient.nonceFuel input p1 = x
  cases x with
  | none => rfl
  | some p2 => rfl

/-- **A non-hole position** in π2's circuit: `36` ports (the view check) of `2^24` positions. -/
theorem nonHole_pi2 {D : RecDeployment} (C : Pi2Circuits D) (hchk : Pi2ViewChecked C) (Fa : Pi2Facts D C)
    (roots : RecSetupRoots) : ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i := by
  obtain ⟨hview, -, -⟩ := viewChecked_at C hchk roots
  have hnP : (C.G roots).nP = 36 := by
    show ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.toList.map (·.position)).length = 36
    rw [List.length_map, Array.length_toList, viewOf_ports hview]
  have hc := RecPiop.Circuit.card_holes (Fa.valid roots)
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  have hall : (Finset.range (C.G roots).N).filter (C.G roots).IsHole = Finset.range (C.G roots).N :=
    Finset.filter_true_of_mem fun i hi ↦ hno i (Finset.mem_range.mp hi)
  rw [hall, Finset.card_range, hnP, RecPiop.Circuit.N, logN_G Fa roots] at hc
  norm_num at hc

open Classical in
/-- **The core at pure `(H, F)`**: on a staged run whose graph accepts and whose contract rejects at good challenges,
one of π2's openings fails its proof of work. From `Pi2RunAt`, the witness's completeness, π1's openings and
`pi2_accepts`. -/
theorem rejects_at {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hwc : Pi2WitnessComplete D C Fa) (hpo : Pi2Pi1Openings D C Fa)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    (hrun : Pi2RunAt D C Fa P1k) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState)
    (z : ((Bool × Bool) × ((Pr2 × E × E × E) × E)) × (Pr2 × E × E × E))
    (hz : runAt Ht Ft (pi2Staged D C Fa (P1k input rows q) input).run = z)
    (hev : z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ badSet2 C.G z.2.1 ∧ ¬ badT2 C.G z.1.2.1 z.1.2.2) :
    ∃ L tree stack claims, E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel L tree
      stack claims = none := by
  obtain ⟨h1, h2⟩ := hrun input rows q Ht Ft
  rw [hz] at h1 h2
  obtain ⟨ha1, ha2, hB, hT⟩ := hev
  rw [h1] at ha1 ha2
  cases hp1 : runAt Ht Ft (P1k input rows q) with
  | none =>
    rw [hp1, expW2_none] at ha1
    exact absurd ha1 (by decide)
  | some p1 =>
    rw [hp1, expW2_some] at ha1 ha2
    cases hpr : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C Fa PcsQuotient.nonceFuel input p1) with
    | none => exact pi2Prover_none Fa Ht Ft _ input p1 hpr
    | some proof =>
      exfalso
      rw [hpr] at ha1 ha2
      dsimp only at ha1 ha2
      have hgood := pi2Choice_good (hwc _ _ _ (graphChecks_of_verifierH ha1))
      obtain ⟨hz2, hzt, hzp⟩ := h2 p1 hp1 ⟨_, hgood⟩
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
        (by rw [Fa.logW]; rfl) proof hpr hroots hbad ht (hpo Ht Ft input p1 proof hgood ha1 hpr)
      exact absurd (hacc.symm.trans ha2) (by decide)

/-! ## The grinding -/

/-- **The grinding, from the core at the log's extension** (`ProbGrind.rejectGood_uni`'s proof): a two-call run of at
most `Q` block calls whose event puts mumbai's proof-of-work potential at one has the event with probability at most
`Q · (1 − 2^-17)^nonceFuel`. -/
theorem rejectGood_of_pot {β : Type} (X : OracleComp KeccakCalls β) (Ev : β → Prop) {Q : ℕ}
    (hQ : Common.QueryCostAtMost X hashBlocks Q)
    (hpot : ∀ (ℓ : Log) (z : β), simulateQ (lookImpl ℓ) X = some z → Ev z →
      1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ) :
    Pr{let z ← (simulateQ ro X).run' ∅}[Ev z] ≤
      (Q : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
  have hfuel : PcsQuotient.nonceFuel ≤ 2 ^ 64 := by norm_num [PcsQuotient.nonceFuel]
  have hstep : LogFreshStepBound (powPot Whir.queryGrindingBits PcsQuotient.nonceFuel)
      (missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF (by decide) (by decide) hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have e : Pr{let z ← (simulateQ ro X).run' ∅}[Ev z] = Pr{let z ← (simulateQ loggedRO X).run []}[Ev z.1] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _ (fun (z : β) _ ↦ Ev z)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ Q
    (E2ECompleteness.isTotalQueryBound_of_queryCostAtMost hQ) [] (fun (z : β) _ ↦ Ev z) fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact hpot z.2 z.1 hlook hev
  · rw [powPot_nil, zero_add]

/-- **The potential at a log**, from the core at every pure `(H, F)`: the log's extension (unseen permutation inputs
answered by the zero state, which passes every proof of work) fails one opening, so its search's inputs are in the
log, failing. -/
theorem pot_of_rejects {β : Type} (X : OracleComp KeccakCalls β) (Ev : β → Prop)
    (hcore : ∀ (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState), Ev (runAt Ht Ft X) →
      ∃ L tree stack claims, E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Ht) Ft PcsQuotient.nonceFuel L
        tree stack claims = none)
    (ℓ : Log) (z : β) (hz : simulateQ (lookImpl ℓ) X = some z) (hev : Ev z) :
    1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ := by
  let Ht : List UInt8 → Digest := fun x ↦ (lookH ℓ x).getD default
  let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD winState
  have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
  have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
  have hrun : runAt Ht Ft X = z := simulateQ_id_of_look ℓ Ht Ft hH hF _ z hz
  obtain ⟨L, tree, stack, claims, hfail⟩ := hcore Ht Ft (by rw [hrun]; exact hev)
  exact one_le_powPot_of_opening_none ℓ Ht hfail

/-- **The numbers**: at most `2^50` block calls, each completing a `17`-bit proof of work whose `2^25` nonces all
failed: below `2^-300` (`E2ECompleteness.grinding_le`'s `2^-304` at `2^48`). -/
theorem grind_le {N : ℕ} (hN : N ≤ 2 ^ 50) :
    (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel ≤ (2 : ℝ≥0∞)⁻¹ ^ 300 := by
  calc (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel
      ≤ ((2 ^ 50 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
        gcongr
    _ = 2 ^ 2 * (((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) := by
        push_cast
        ring
    _ ≤ 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (302 + 2) := by
        gcongr
        exact E2ECompleteness.grinding_le
    _ = (2 : ℝ≥0∞)⁻¹ ^ 302 := E2ECompleteness.two_pow_mul_inv_pow 2 302
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 300 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)

/-! ## π2's completeness -/

/-- **The grinding for π2** (`Holds.rejectGood`): the staged run rejected at good challenges, the graph accepting,
with probability at most `N · (1 − 2^-17)^nonceFuel`. -/
theorem rejectGood_pi2 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hwc : Pi2WitnessComplete D C Fa) (hpo : Pi2Pi1Openings D C Fa)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    (hrun : Pi2RunAt D C Fa P1k) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) {N : ℕ}
    (hcost : Common.QueryCostAtMost (pi2Staged D C Fa (P1k input rows q) input).run hashBlocks N) :
    Pr{let z ← (simulateQ ro (pi2Staged D C Fa (P1k input rows q) input).run).run' ∅}[
      z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ badSet2 C.G z.2.1 ∧ ¬ badT2 C.G z.1.2.1 z.1.2.2] ≤
      (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel :=
  rejectGood_of_pot _ _ hcost fun ℓ z hz hev ↦
    pot_of_rejects _ (fun z : ((Bool × Bool) × ((Pr2 × E × E × E) × E)) × (Pr2 × E × E × E) ↦
      z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ badSet2 C.G z.2.1 ∧ ¬ badT2 C.G z.1.2.1 z.1.2.2)
      (fun Ht Ft hev' ↦ rejects_at hD C Fa hroots hwc hpo P1k hrun input rows q Ht Ft _ rfl hev') ℓ z hz hev

/-- **The staged run's `Holds`**, at the real deployment's facts: the named facts, the lengths, the counts, the
grinding. -/
theorem holds_pi2 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hhash : Pi2HashBeforeAlpha D C (pi2Facts hD C hchk) P1k) (htf : Pi2TFresh D C (pi2Facts hD C hchk) P1k εt)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows)
    (hrel : D.pi1.HonestRelation rows input q) :
    (pi2Staged D C (pi2Facts hD C hchk) (P1k input rows q) input).Holds D P1
      (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel) input rows q 536 (badSet2 C.G) (badT2 C.G)
      (2 ^ 25 + 36) (2 ^ 27) N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := hexp input rows q hfit hrel
  duplex := hdup input rows q hfit hrel
  cost := hcost input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 536 _
  hashA := hhash input rows q hfit hrel
  badCard p := card_badCopy_pi2 (pi2Facts hD C hchk) p.1 p.2.1 p.2.2
  badTCard fp := card_badT_pi2 (pi2Facts hD C hchk) fp.1.1 fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    (nonHole_pi2 C hchk (pi2Facts hD C hchk) fp.1.1)
  tFresh := htf input rows q hfit hrel
  rejectGood := rejectGood_pi2 hD C (pi2Facts hD C hchk) hroots hwc hpo P1k hrun input rows q
    (hcost input rows q hfit hrel)

/-- **π2's completeness, from the staged run's named facts** (at the real deployment's facts `pi2Facts hD C hchk`):
`RecCompleteness2 D P1 (pi2Prover …) (delta2 N εt (N · (1 − 2^-17)^nonceFuel))`. Proved here: the lengths, the bad
sets' counts, the grinding (from `Pi2RunAt`, `Pi2Pi1Openings`, `Pi2WitnessComplete` and the core). -/
theorem recCompleteness2_pi2_staged {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hhash : Pi2HashBeforeAlpha D C (pi2Facts hD C hchk) P1k) (htf : Pi2TFresh D C (pi2Facts hD C hchk) P1k εt)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_of_staged fun input rows q hfit hrel ↦
    ⟨_, _, _, holds_pi2 hD C hchk hroots P1 P1k hexp hrun hdup hcost hhash htf hpo hwc input rows q hfit hrel⟩

/-- **`δ2` in bits**: below `2^-164` at `N ≤ 2^50` block calls and `εt ≤ 2^-200`. -/
theorem delta2_pi2_le {N : ℕ} {εt : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ht : εt ≤ (2 : ℝ≥0∞)⁻¹ ^ 200) :
    delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  delta2_le hN ht (grind_le hN)

/-- **The recursive verifier's completeness end to end**, with π2's honest prover at the real deployment's facts: from
π2's staged facts (named above), π1-rec3's completeness at Keccak-f[1600] and its honest proofs' hazard. -/
theorem recCompleteness_pi2_staged_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hhash : Pi2HashBeforeAlpha D C (pi2Facts hD C hchk) P1k) (htf : Pi2TFresh D C (pi2Facts hD C hchk) P1k εt)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD P1 _ _
    (recCompleteness2_pi2_staged hD C hchk hroots P1 P1k hexp hrun hdup hcost hhash htf hpo hwc) δ1 δh h1 hh

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2G.rejects_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.rejects_at

/-- info: 'RecCompose.Pi2G.recCompleteness2_pi2_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.recCompleteness2_pi2_staged

/-- info: 'RecCompose.Pi2G.delta2_pi2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.delta2_pi2_le

/-- info: 'RecCompose.Pi2G.recCompleteness_pi2_staged_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.recCompleteness_pi2_staged_fs
