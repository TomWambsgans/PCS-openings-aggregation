-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's analogue of `ProbExp.lean` (`expW`,
-- `experiment_eq`, `stagedU`, `experiment_staged`, `hashA_stagedU`, `duplexVm_stagedU`, `cost_stagedU`,
-- `TQueryFresh`), itself following `formal/EndToEnd/Completeness/E2ECompleteness/Experiment.lean`, `Staging.lean`,
-- `HashLen.lean`, `Assemble.lean`; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls answered over `π` (`keccakCallsOverQueryPermutation`) and the lazy
-- permutation after them (`simulateQ_lazy_keccakCallsOverQueryPermutation`), the duplex discipline (`DuplexVm`) and
-- the block cost (`hashBlocks`).
import UniComplete.Rec3Hyp
import UniComplete.Rec3ProbStaged
import UniComplete.ProbExp

/-!
# π1-rec3's experiment, staged

`uniCompletenessExperimentRec3 D (uniProverRec3RP flock D)` (the setup, π1-rec3's honest prover, π1-rec3's verifier
over `π`) is the two-call experiment `expW3` (the same three, with Keccak-256 and Keccak-f[1600] the calls: the setup
`setupTreesWithH`, the prover `uniProverRec3With`, the verdict by `Deployment.verifierRec3WithH`) answered by the
sponge over the random permutation (**`experiment_eq3`**, from `ProverCommutes3`, `VerifierCommutes3` and the
setup's commutation `simulateQ_setupTreesWithH`; at `H = keccak256With π` the setup and the verifier are
`RecSecurity.lean`'s, `setupTreesWith_eqH`, `verifierRec3With_eqH`). Its staged form **`stagedU3`** (a
`UniStaged3`): `A` the setup and the prover before the bus challenges (`proverA3`), the two answers, `B` the prover
from `γ` to `C2`'s root (`Prob.midB` on `writerAfter3`), `t`'s query on the writer's input (`Prob.tInput`), `C` the
prover after `t` (`proverD3`) and the verdict (`verdictW3`); `expW3 = (·.1.1) <$> (stagedU3 …).run`
(**`expW3_eq_staged`**, from `uniProverRec3With_split`, `proverC3_split`). Then:

* **`hashA_stagedU3`**: stage A hashes `512`-byte leaves, `64`-byte nodes, π1-rec3's IV preimage (`280 + |IV|`
  bytes and the variant's, `variantBytes`) and the seed's `80`: never `32` or `88` (`GoodL 88`);
* **`duplexVm_stagedU3`**: the duplex discipline, from `ProverDuplex3`, the setup's (`hOnly_setupTreesWithH`) and
  `VerifierDisc3`, through the map (`Prob.duplexVm_map_iff`);
* **`cost_stagedU3`**: at most `setupCost D + (NP + NV)` block calls, from `ProverCost3 NP`, `ProverStreamSize3 S`
  and `VerifierCost3 D S NV`, along the prover's outputs (`Prob.qc_bind_support`).

**`TQueryFresh3`** is `ProbExp.lean`'s `TQueryFresh` on `stagedU3`'s `pre` (a named hypothesis here).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH)
open UniStatement
open E2ECompleteness (HashOK hashOK_callKeccak256 Disc)
open UniComplete.Prob (chal ProverA firstInput midB tInput afterT GoodL goodL_of_length hashOK_commitWithH
  duplexVm_map_iff qc_bind_support FlockSimCommutes run_sampleW run_sendRoot)
open scoped ENNReal
open Common (queryPermutation)

set_option autoImplicit false

namespace UniComplete.Rec3

/-! ## The two-call experiment -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- The verdict on the prover's output: no proof is rejected, a proof goes to π1-rec3's deployed verifier. -/
def verdictW3 (D : Deployment) (trees : SetupTrees) (input : Vector UInt8 32) : Option UniProof → m Bool
  | none => pure false
  | some proof => Deployment.verifierRec3WithH H F D trees.roots input proof

/-- **π1-rec3's experiment with Keccak-256 explicit**: the setup, the honest prover, the verdict. -/
def expW3 (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    m Bool := do
  let trees ← setupTreesWithH H F D
  let o ← uniProverRec3With H F flock D input rows q
  verdictW3 H F D trees input o

end With

variable (flock : FlockProverH) (D : Deployment)

/-- **The experiment over the two calls commutes with simulation.** -/
theorem simulateQ_expW3 (hc : ProverCommutes3 flock D) (hv : VerifierCommutes3) {r : Type → Type} [Monad r]
    [LawfulMonad r] (impl : QueryImpl KeccakCalls r) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (expW3 callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) =
      expW3 (implH impl) (implF impl) (flock (implH impl)) D input rows q := by
  simp only [expW3, simulateQ_bind, simulateQ_setupTreesWithH, hc impl]
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => simp [verdictW3]
  | some proof => simp [verdictW3, hv impl]

/-- **π1-rec3's completeness experiment is the two-call experiment against the random permutation.** -/
theorem experiment_eq3 (hc : ProverCommutes3 flock D) (hv : VerifierCommutes3) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) :
    uniCompletenessExperimentRec3 D (uniProverRec3RP flock D) input rows q =
      (simulateQ keccakCallsOverRandomPermutation
        (expW3 callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)).run' [] := by
  rw [← simulateQ_lazy_keccakCallsOverQueryPermutation, simulateQ_expW3 flock D hc hv]
  unfold uniCompletenessExperimentRec3 Common.runWithRandomPermutation
  congr 2
  rw [setupTreesWith_eqH]
  unfold expW3
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => rfl
  | some proof => simp only [verdictW3, verifierRec3With_eqH]; rfl

/-! ## The staged form -/

/-- **π1-rec3's prover before the bus challenges commutes with simulation** (its trees, IV and seed only hash). -/
theorem simulateQ_proverA3 {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (proverA3 callKeccak256 D input rows q) = proverA3 (implH impl) D input rows q := by
  simp only [proverA3, setupTreesOf, contractIvRec3Of, seedOf, simulateQ_bind, simulateQ_pure,
    E2ECompleteness.simulateQ_commitWithH, simulateQ_queryH]

/-- **What the run carries to `t`**: the setup's trees, the prover before the bus challenges, the two answers, and
the stream from `γ` to `C2`'s root (`midB`'s output, the writer). -/
structure MidU3 where
  trees : SetupTrees
  a : ProverA
  s₁ : Digest
  s₂ : Digest
  mw : (E × FlockOut × Committed) × Wr

/-- `midB` over the two calls, from the writer after π1-rec3's two bus challenges. -/
def midU3 (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (a : ProverA) (s₁ s₂ : Digest) :
    OracleComp KeccakCalls ((E × FlockOut × Committed) × Wr) :=
  (midB callKeccak256 (commitReal callKeccak256) (flock callKeccak256) (honestTrace D input rows q)
    (squares (chal s₁) 4) (chal s₂)).run (writerAfter3 rows a.c1 s₁ s₂)

/-- **π1-rec3's experiment's stages**: `A` the setup and the prover before the bus challenges; `B` the prover from
`γ` to `C2`'s root (`midB`); `t`'s input the writer's (`tInput`), its prior Flock's point; `C` the prover after `t`
(`proverD3`) and the verdict. -/
def stagedU3 (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : UniStaged3 where
  α := SetupTrees × ProverA
  β := MidU3
  inp x := firstInput rows x.2
  A := do
    let trees ← setupTreesWithH callKeccak256 callKeccakF1600 D
    let a ← proverA3 callKeccak256 D input rows q
    return (trees, a)
  B x s₁ s₂ := do
    let m ← midU3 flock D input rows q x.2 s₁ s₂
    return ⟨x.1, x.2, s₁, s₂, m⟩
  tin b := tInput b.mw.2
  pr b := b.mw.1.2.1.point
  C b st := do
    let o ← proverD3 callKeccak256 callKeccakF1600 D input rows q b.a b.s₁ b.s₂ b.mw st
    verdictW3 callKeccak256 callKeccakF1600 D b.trees input o

/-- **The two-call experiment is the staged run's verdict.** -/
theorem expW3_eq_staged (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    expW3 callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q =
      (fun z ↦ z.1.1) <$> (stagedU3 flock D input rows q).run := by
  simp only [expW3, uniProverRec3With_split, proverC3_split, UniStaged3.run, UniStaged3.tail, stagedU3, midU3,
    staged2, map_bind, map_pure, bind_assoc, pure_bind, bind_pure]

/-- **The staged experiment**, against the random permutation. -/
theorem experiment_staged3 (hc : ProverCommutes3 flock D) (hv : VerifierCommutes3) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) :
    uniCompletenessExperimentRec3 D (uniProverRec3RP flock D) input rows q =
      (fun z ↦ z.1.1) <$>
        (simulateQ keccakCallsOverRandomPermutation (stagedU3 flock D input rows q).run).run' [] := by
  rw [experiment_eq3 flock D hc hv, expW3_eq_staged, simulateQ_map, StateT.run'_eq, StateT.run'_eq,
    StateT.run_map, Functor.map_map, Functor.map_map]

/-- **`midB` over the two calls commutes with simulation**, given Flock's prover's. -/
theorem simulateQ_midU3 (hf : FlockSimCommutes flock) {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (a : ProverA)
    (s₁ s₂ : Digest) :
    simulateQ impl (midU3 flock D input rows q a s₁ s₂) =
      (midB (implH impl) (commitReal (implH impl)) (flock (implH impl)) (honestTrace D input rows q)
        (squares (chal s₁) 4) (chal s₂)).run (writerAfter3 rows a.c1 s₁ s₂) := by
  simp only [midU3, midB, StateT.run_bind, run_sampleW, StateT.run_lift, run_sendRoot, commitReal, bind_assoc,
    pure_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, simulateQ_queryH, hf impl,
    E2ECompleteness.simulateQ_commitWithH]

/-- **`t`'s freshness for π1-rec3** (a named hypothesis, not proved here; `ProbExp.lean`'s `TQueryFresh` on
`stagedU3`): in the two-call random-oracle model, `t`'s input (`tInput`, the writer's state and the bytes since the
last challenge, `C2`'s root word) has been hashed before its query with probability at most `εt`. As in the main line
it is not fresh by its length (`64` bytes when Flock's prover ends with a challenge, a Merkle node's length). -/
def TQueryFresh3 (εt : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    Pr{let p ← (simulateQ E2ECompleteness.ro (stagedU3 flock D input rows q).pre).run ∅}[
      p.2 (.inl ((stagedU3 flock D input rows q).tin p.1.1)) ≠ none] ≤ εt

/-! ## What stage A hashes -/

/-- **Stage A hashes nothing of the bus chain's lengths** (π1-rec3's IV preimage is the main line's with the
variant's bytes appended: still at least `280` bytes). -/
theorem hashA_stagedU3 (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    HashOK (GoodL 88) (stagedU3 flock D input rows q).A := by
  simp only [stagedU3, proverA3, setupTreesOf, setupTreesWithH, contractIvRec3Of, seedOf, bind_assoc, pure_bind]
  refine E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_callKeccak256 (goodL_of_length (Or.inr (Or.inr (Or.inr ?_))))) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_callKeccak256 (goodL_of_length (Or.inr (Or.inr (Or.inl ?_))))) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  · simp only [List.length_append, Cost.ivTag_length, Cost.len_digestBytes, Cost.shapeBytes_length,
      Cost.layoutWords_length]
    omega
  · simp [Cost.name_length, Cost.len_digestBytes, honestTrace]

/-! ## The duplex discipline -/

/-- **The staged run follows the duplex discipline.** -/
theorem duplexVm_stagedU3 (hdup : ProverDuplex3 flock D) (hvd : VerifierDisc3) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) :
    DuplexVm (stagedU3 flock D input rows q).run [] := by
  have hd : Disc (expW3 callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) := by
    unfold expW3
    refine (E2ECompleteness.disc_of_hOnly (hOnly_setupTreesWithH D)).bind fun trees ↦
      (hdup input rows q hfit hrel).bind fun o ↦ ?_
    cases o with
    | none => exact E2ECompleteness.disc_pure _
    | some π => exact hvd D _ input π
  have h := (duplexVm_iff_duplexP _ _).mpr (hd [])
  rwa [expW3_eq_staged, duplexVm_map_iff] at h

/-! ## The block count -/

/-- **The staged run's block count**: the setup's, the prover's `NP`, the verifier's `NV` on streams of at most `S`
bytes. -/
theorem cost_stagedU3 {NP S NV : ℕ} (hcost : ProverCost3 flock D NP) (hstream : ProverStreamSize3 flock D S)
    (hvcost : VerifierCost3 D S NV) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) :
    Common.QueryCostAtMost (stagedU3 flock D input rows q).run hashBlocks (Cost.setupCost D + (NP + NV)) := by
  have h : Common.QueryCostAtMost (expW3 callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks (Cost.setupCost D + (NP + NV)) := by
    unfold expW3
    refine Common.QueryCostAtMost.bind (Cost.cost_setupTreesWithH D) fun trees ↦ ?_
    refine qc_bind_support (hcost input rows q hfit hrel) fun o ho ↦ ?_
    cases o with
    | none => trivial
    | some π => exact hvcost trees.roots input π (hstream input rows q hfit hrel π ho)
  rw [expW3_eq_staged] at h
  exact (isQueryBound_map_iff _ _ _ _ _).1 h

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.experiment_staged3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.experiment_staged3

/-- info: 'UniComplete.Rec3.hashA_stagedU3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.hashA_stagedU3

/-- info: 'UniComplete.Rec3.duplexVm_stagedU3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.duplexVm_stagedU3

/-- info: 'UniComplete.Rec3.cost_stagedU3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.cost_stagedU3
