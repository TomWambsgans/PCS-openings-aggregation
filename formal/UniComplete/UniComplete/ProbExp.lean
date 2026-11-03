-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/EndToEnd/Completeness/E2ECompleteness/Experiment.lean`, `Staging.lean`, `HashLen.lean`, `Assemble.lean`
-- for the univariate experiment; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls answered over `π` (`keccakCallsOverQueryPermutation`) and the lazy
-- permutation after them (`simulateQ_lazy_keccakCallsOverQueryPermutation`), the duplex discipline (`DuplexVm`) and
-- the block cost (`hashBlocks`).
import UniComplete.ProbHyp
import UniComplete.ProbStaged
import UniComplete.VerifierHCost
import E2ECompleteness.HashLen
import LeanVM.Protocol.ExperimentBridge

/-!
# The univariate experiment, staged

`uniCompletenessExperiment D (uniProverRP flock D)` (the setup, the honest prover, the deployed verifier over `π`) is
the two-call experiment `expW` (the same three, with Keccak-256 and Keccak-f[1600] the calls) answered by the
sponge over the random permutation (**`experiment_eq`**, from `ProverCommutes` and the verifier's and the setup's
commutations, `simulateQ_verifierWithH`, `simulateQ_setupTreesWithH`). Its staged form **`stagedU`** (a
`UniStaged`): `A` the setup and the prover before the bus challenges (`proverA`), the five answers, `C` the prover
after them (`proverC`) and the verifier (`verdictW`); `expW = (·.1) <$> (stagedU …).run` (**`expW_eq_staged`**,
from `uniProverWith_split`). Then:

* **`hashA_stagedU`**: stage A hashes `512`-byte leaves, `64`-byte nodes, the IV's `280 + |IV|` bytes and the
  seed's `80`: never `32` or `88` (`GoodL 88`);
* **`duplexVm_stagedU`**: the duplex discipline, from `ProverDuplex`, the setup's (`hOnly_setupTreesWithH`) and the
  verifier's (`disc_verifierWithH`), through the map (`duplexVm_map_iff`);
* **`cost_stagedU`**: at most `setupCost D + (N + verifierCost D S)` block calls, from `ProverCost N`,
  `ProverStreamSize S` and the verifier's count on streams of at most `S` bytes (`cost_verifierWithH`), along the
  prover's outputs (`qc_bind_support`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH)
open UniStatement
open E2ECompleteness (HashOK hashOK_callKeccak256 Disc)
open Common (queryPermutation)

set_option autoImplicit false

namespace UniComplete.Prob

/-! ## The two-call experiment -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- The verdict on the prover's output: no proof is rejected, a proof goes to the deployed verifier. -/
def verdictW (D : Deployment) (trees : SetupTrees) (input : Vector UInt8 32) : Option UniProof → m Bool
  | none => pure false
  | some proof => Deployment.verifierWithH H F D trees.roots input proof

/-- **The experiment with Keccak-256 explicit**: the setup, the honest prover, the verdict. -/
def expW (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    m Bool := do
  let trees ← setupTreesWithH H F D
  let o ← uniProverWith H F flock D input rows q
  verdictW H F D trees input o

end With

variable (flock : PolyFlock) (D : Deployment)

/-- **The experiment over the two calls commutes with simulation.** -/
theorem simulateQ_expW (hc : ProverCommutes flock D) {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) =
      expW (implH impl) (implF impl) (flock (implH impl)) D input rows q := by
  simp only [expW, simulateQ_bind, simulateQ_setupTreesWithH, hc impl]
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => simp [verdictW]
  | some proof => simp [verdictW, simulateQ_verifierWithH]

/-- **The completeness experiment is the two-call experiment against the random permutation.** -/
theorem experiment_eq (hc : ProverCommutes flock D) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    uniCompletenessExperiment D (uniProverRP flock D) input rows q =
      (simulateQ keccakCallsOverRandomPermutation
        (expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)).run' [] := by
  rw [← simulateQ_lazy_keccakCallsOverQueryPermutation, simulateQ_expW flock D hc]
  unfold uniCompletenessExperiment Common.runWithRandomPermutation
  congr 2
  rw [setupTreesWith_eqH]
  unfold expW
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => rfl
  | some proof => simp only [verdictW, verifierWith_eqH]; rfl

/-! ## The staged form -/

/-- **The experiment's stages**: `A` the setup and the prover before the bus challenges, `C` the prover after them
and the verdict. -/
def stagedU (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : UniStaged where
  α := SetupTrees × ProverA
  inp x := firstInput rows x.2
  A := do
    let trees ← setupTreesWithH callKeccak256 callKeccakF1600 D
    let a ← proverA callKeccak256 D input rows q
    return (trees, a)
  C x s₁ s₂ s₃ s₄ s₅ := do
    let o ← proverC callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q x.2 s₁ s₂ s₃ s₄ s₅
    verdictW callKeccak256 callKeccakF1600 D x.1 input o

/-- **The two-call experiment is the staged run's verdict.** -/
theorem expW_eq_staged (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q =
      (fun z ↦ z.1) <$> (stagedU flock D input rows q).run := by
  simp only [expW, uniProverWith_split, UniStaged.run, stagedU, staged5, map_bind, map_pure, bind_assoc,
    pure_bind, bind_pure]

/-- **The staged experiment**, against the random permutation. -/
theorem experiment_staged (hc : ProverCommutes flock D) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) :
    uniCompletenessExperiment D (uniProverRP flock D) input rows q =
      (fun z ↦ z.1) <$> (simulateQ keccakCallsOverRandomPermutation (stagedU flock D input rows q).run).run' [] := by
  rw [experiment_eq flock D hc, expW_eq_staged, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
    Functor.map_map, Functor.map_map]

/-! ## What stage A hashes -/

/-- Lengths other than the bus chain's. -/
theorem goodL_of_length {m : Bytes} (h : m.length = 512 ∨ m.length = 64 ∨ m.length = 80 ∨ 280 ≤ m.length) :
    GoodL 88 m := by
  refine ⟨?_, ?_⟩ <;> omega

/-- A Merkle tree of rows of `64` words hashes `512`-byte leaves and `64`-byte nodes (`E2ECompleteness.HashLen`'s
`hashOK_buildTree`, at `GoodL 88`). -/
theorem hashOK_buildTree (height : ℕ) (word : LeanVM.Protocol.Compile.Word)
    (hw : ∀ p, (word p).length = 64) :
    HashOK (GoodL 88) (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine E2ECompleteness.HashOK.bind ?_ fun leaves ↦ E2ECompleteness.HashOK.bind ?_ fun _ ↦
    E2ECompleteness.HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine E2ECompleteness.HashOK.arrayMapM _
      (fun i ↦ hashOK_callKeccak256 (goodL_of_length (Or.inl ?_))) _
    rw [E2ECompleteness.length_flatMap_kBytes, hw]
  · suffices h : ∀ k (level : Array Digest),
        HashOK (GoodL 88) (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact E2ECompleteness.HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine E2ECompleteness.HashOK.bind ?_ fun up ↦ E2ECompleteness.HashOK.bind (ih up) fun _ ↦
        E2ECompleteness.HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine E2ECompleteness.HashOK.arrayMapM _
        (fun j ↦ hashOK_callKeccak256 (goodL_of_length (Or.inr (Or.inl ?_)))) _
      rw [List.length_append, E2ECompleteness.length_digestBytes, E2ECompleteness.length_digestBytes]

theorem hashOK_commitWithH (μ : ℕ) (stack : Array K) :
    HashOK (GoodL 88) (E2ECompleteness.commitWithH callKeccak256 μ stack) :=
  hashOK_buildTree _ _ (E2ECompleteness.length_stackWordFast μ 1 stack)

/-- **Stage A hashes nothing of the bus chain's lengths.** -/
theorem hashA_stagedU (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    HashOK (GoodL 88) (stagedU flock D input rows q).A := by
  simp only [stagedU, proverA, setupTreesOf, setupTreesWithH, contractIvOf, seedOf, bind_assoc, pure_bind]
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

/-- The duplex discipline sees only the queries: a map keeps it. -/
theorem duplexVm_map_iff {α β : Type} (f : α → β) (X : OracleComp KeccakCalls α) (h : List KeccakState) :
    DuplexVm (f <$> X) h ↔ DuplexVm X h := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a =>
    rw [map_pure]
    exact ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
  | query_bind t k ih =>
    rw [map_bind, duplexVm_query_bind, duplexVm_query_bind]
    rcases t with x | x
    · exact forall_congr' fun u ↦ ih u h
    · exact and_congr Iff.rfl (forall_congr' fun y ↦ ih y _)

/-- **The staged run follows the duplex discipline.** -/
theorem duplexVm_stagedU (hdup : ProverDuplex flock D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) :
    DuplexVm (stagedU flock D input rows q).run [] := by
  have hd : Disc (expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) := by
    unfold expW
    refine (E2ECompleteness.disc_of_hOnly (hOnly_setupTreesWithH D)).bind fun trees ↦
      (hdup input rows q hfit hrel).bind fun o ↦ ?_
    cases o with
    | none => exact E2ECompleteness.disc_pure _
    | some π => exact disc_verifierWithH D _ input π
  have h := (duplexVm_iff_duplexP _ _).mpr (hd [])
  rwa [expW_eq_staged, duplexVm_map_iff] at h

/-! ## The block count -/

/-- **A bind's cost along the outputs**: the continuation bounded only on the prefix's possible outputs. -/
theorem qc_bind_support {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {a b : ℕ} (ha : Common.QueryCostAtMost X hashBlocks a)
    (hb : ∀ x ∈ support X, Common.QueryCostAtMost (f x) hashBlocks b) :
    Common.QueryCostAtMost (X >>= f) hashBlocks (a + b) := by
  induction X using OracleComp.inductionOn generalizing a with
  | pure x =>
    rw [pure_bind]
    exact (hb x (by simp)).mono (Nat.le_add_left _ _)
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [Common.isWeightBound_query_bind_iff] at ha ⊢
    refine ⟨le_trans ha.1 (Nat.le_add_right _ _), fun u ↦ ?_⟩
    have h := ih u (ha.2 u) fun x hx ↦ hb x (by
      rw [mem_support_bind_iff]
      exact ⟨u, by simp, hx⟩)
    exact h.mono (by have := ha.1; omega)

/-- **The staged run's block count**: the setup's, the prover's `N`, the verifier's on streams of at most `S`
bytes. -/
theorem cost_stagedU {N S : ℕ} (hcost : ProverCost flock D N) (hstream : ProverStreamSize flock D S)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation rows input q) :
    Common.QueryCostAtMost (stagedU flock D input rows q).run hashBlocks
      (Cost.setupCost D + (N + Cost.verifierCost D S)) := by
  have h : Common.QueryCostAtMost (expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks (Cost.setupCost D + (N + Cost.verifierCost D S)) := by
    unfold expW
    refine Common.QueryCostAtMost.bind (Cost.cost_setupTreesWithH D) fun trees ↦ ?_
    refine qc_bind_support (hcost input rows q hfit hrel) fun o ho ↦ ?_
    cases o with
    | none => trivial
    | some π => exact Cost.cost_verifierWithH D trees.roots input π S (hstream input rows q hfit hrel π ho)
  rw [expW_eq_staged] at h
  exact (isQueryBound_map_iff _ _ _ _ _).1 h

end UniComplete.Prob
