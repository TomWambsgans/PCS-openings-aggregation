-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the duplex discipline (`LeanVM.Rpm.DuplexVm`, `DuplexP`, `HOnly`, `hOnly_buildTreeM`), and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Duplex.lean`'s `Disc`, `disc_proveOpeningWithH`,
-- `hOnly_commitWithH`.
import UniComplete.ProverSim
import UniComplete.VerifierHDuplex

/-!
# The duplex discipline of the honest prover

Over the two calls, every Keccak-f[1600] call of the honest prover continues a duplex or starts one at a zero
capacity (mumbai's `DuplexVm`): **`duplexVm_uniProverWith`**, from any earlier answers (`disc_uniProverWith`), as
the verifier's (`duplexVm_verifierWithH`).

* **The stream only hashes** (`wHOnly_proveStreamWith`): every challenge is a Keccak-256 call (`sampleW`), the
  commitments of `C1` and `C2` are Merkle trees (`hOnly_commitWithH`), the writes are pure; Flock's prover is a
  parameter, and the fact used of it is named: **`FlockHashOnly`**, its run over the two calls only hashes. It
  follows from `FlockCommutes` (`flockHashOnly_of_commutes`: by naturality, as `VerifierHDuplex` reads the walk's
  hash-only-ness off its commutation, the run over `callKeccak256` is the run over the hash alone simulated).
  A writer's computation hashes only when its run from every state does (`WHOnly`); the calculus `WHOnly.bind`,
  `wHOnly_forIn_list`, … walks the stream.
* **The setup, the IV and the seed only hash** (`hOnly_setupTreesOf`, `hOnly_contractIvOf`).
* **The permutation is called by the five openings only**, each disciplined (E2ECompleteness's
  `disc_proveOpeningWithH`: each starts its own duplex at its seed).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement
open E2ECompleteness (Disc disc_pure disc_of_hOnly)

namespace UniComplete

/-- The writer's monad over the two calls. -/
abbrev PM := WrM (OracleComp KeccakCalls)

/-! ## A writer's computation that only hashes -/

/-- **From every state, the run only hashes.** -/
def WHOnly {α : Type} (x : PM α) : Prop := ∀ s, HOnly (x.run s)

section Calculus

variable {α β : Type}

theorem WHOnly.bind {x : PM α} {f : α → PM β} (hx : WHOnly x) (hf : ∀ a, WHOnly (f a)) : WHOnly (x >>= f) :=
  fun s ↦ by
    rw [StateT.run_bind]
    exact (hx s).bind fun p ↦ hf p.1 p.2

theorem wHOnly_pure (a : α) : WHOnly (pure a : PM α) := fun _ ↦ hOnly_pure _

theorem wHOnly_get : WHOnly (get : PM Wr) := fun _ ↦ hOnly_pure _

theorem wHOnly_set (s : Wr) : WHOnly (set s : PM PUnit) := fun _ ↦ hOnly_pure _

theorem wHOnly_modify (f : Wr → Wr) : WHOnly (modify f : PM PUnit) := fun _ ↦ hOnly_pure _

theorem wHOnly_lift {X : OracleComp KeccakCalls α} (hX : HOnly X) : WHOnly (StateT.lift X : PM α) :=
  fun s ↦ by
    rw [StateT.run_lift]
    exact hX.bind fun _ ↦ hOnly_pure _

theorem WHOnly.map {x : PM α} (f : α → β) (hx : WHOnly x) : WHOnly (f <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact hx.bind fun _ ↦ wHOnly_pure _

theorem wHOnly_forIn_list {γ : Type} (l : List γ) (b : β) (f : γ → β → PM (ForInStep β))
    (hf : ∀ a s, WHOnly (f a s)) : WHOnly (forIn l b f) := by
  induction l generalizing b with
  | nil => exact wHOnly_pure b
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a b).bind fun s ↦ ?_
    cases s with
    | done b => exact wHOnly_pure b
    | yield b => exact ih b

end Calculus

/-! ## The stream -/

section Stream

theorem wHOnly_sendBytes (b : List UInt8) : WHOnly (sendBytes (m := OracleComp KeccakCalls) b) :=
  wHOnly_modify _

theorem wHOnly_sendScalar (x : E) : WHOnly (sendScalar (m := OracleComp KeccakCalls) x) := wHOnly_sendBytes _

theorem wHOnly_sendScalars (xs : List E) : WHOnly (sendScalars (m := OracleComp KeccakCalls) xs) :=
  wHOnly_sendBytes _

theorem wHOnly_sendInteger (v bytes : ℕ) : WHOnly (sendInteger (m := OracleComp KeccakCalls) v bytes) :=
  wHOnly_sendBytes _

theorem wHOnly_sendRoot (halves : E × E) : WHOnly (sendRoot (m := OracleComp KeccakCalls) halves) :=
  wHOnly_sendBytes _

theorem wHOnly_sampleW : WHOnly (sampleW callKeccak256) := by
  unfold sampleW
  exact wHOnly_get.bind fun _ ↦ (wHOnly_lift (hOnly_queryH _)).bind fun _ ↦ (wHOnly_set _).bind fun _ ↦
    wHOnly_pure _

theorem wHOnly_samplesW : ∀ count : ℕ, WHOnly (samplesW callKeccak256 count)
  | 0 => wHOnly_pure _
  | count + 1 => wHOnly_sampleW.bind fun _ ↦ (wHOnly_samplesW count).bind fun _ ↦ wHOnly_pure _

theorem wHOnly_batchRound (lambda : E) (j : ℕ) (st : BatchState) : WHOnly (batchRound callKeccak256 lambda j st) := by
  unfold batchRound
  exact (wHOnly_sendScalar _).bind fun _ ↦ (wHOnly_sendScalar _).bind fun _ ↦ wHOnly_sampleW.bind fun _ ↦
    wHOnly_pure _

theorem wHOnly_batchRounds (lambda : E) (vars : ℕ) (st : BatchState) :
    WHOnly (batchRounds callKeccak256 lambda vars st) := by
  unfold batchRounds
  exact (wHOnly_forIn_list _ _ _ fun _ _ ↦ (wHOnly_batchRound _ _ _).bind fun _ ↦ wHOnly_pure _).bind fun _ ↦
    wHOnly_pure _

set_option hygiene false in
/-- One step of the stream's walk: a leaf, or a bind whose first part is a leaf (`hcommit`, `hflock` the local
hypotheses on the commitment and Flock's prover); reducible unification, so that a failed match is cheap. -/
macro "wh_step" : tactic => `(tactic| first
  | with_reducible_and_instances exact wHOnly_pure _
  | with_reducible_and_instances refine (wHOnly_forIn_list _ _ _ fun _ _ ↦
      (wHOnly_sendInteger _ _).bind fun _ ↦ wHOnly_pure _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine (wHOnly_lift (hcommit _ _ _)).bind fun _ ↦ ?_
  | with_reducible_and_instances refine (wHOnly_sendRoot _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine (wHOnly_sendScalars _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine wHOnly_sampleW.bind fun _ ↦ ?_
  | with_reducible_and_instances refine (wHOnly_samplesW _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine (wHOnly_batchRounds _ _ _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine ((hflock _ _ _).map _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine (wHOnly_pure _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine wHOnly_get.bind fun _ ↦ ?_
  | split
  | dsimp only)

/-- **The stream only hashes**, given that the commitment and Flock's prover do. -/
theorem wHOnly_proveStreamWith (commit : Commitment → ℕ → Array K → OracleComp KeccakCalls Committed)
    (hcommit : ∀ c v s, HOnly (commit c v s)) (flock : FlockProver (OracleComp KeccakCalls))
    (hflock : ∀ logN v q, WHOnly (flock logN v q)) (blake2s : Blake2s) (tr : Trace) :
    WHOnly (proveStreamWith callKeccak256 commit flock blake2s tr) := by
  unfold proveStreamWith
  rcases blake2s with variant | _ <;> repeat wh_step

theorem hOnly_commitReal (c : Commitment) (vars : ℕ) (stack : Array K) :
    HOnly (commitReal callKeccak256 c vars stack) :=
  (E2ECompleteness.hOnly_commitWithH _ _).bind fun _ ↦ hOnly_pure _

end Stream

/-! ## Flock's prover -/

/-- **Flock's prover only hashes** (`FlockHashOnly`): over the two calls, from every state. The one fact the
discipline uses of it. -/
def FlockHashOnly (flock : FlockProverH) : Prop :=
  ∀ (logN : ℕ) (variant : Flock.Variant) (words : Array K), WHOnly (flock callKeccak256 logN variant words)

/-- **A Flock prover that commutes with every morphism only hashes**: over the two calls it is its run over the
hash alone, simulated. -/
theorem flockHashOnly_of_commutes (flock : FlockProverH) (hflock : FlockCommutes flock) : FlockHashOnly flock := by
  intro logN variant words s
  have h := hflock (Morph.sim hashToCalls) callHash logN variant words
  rw [sim_callHash] at h
  rw [← h, Morph.wr_run]
  exact hOnly_simulateQ_hash _

/-! ## The prover -/

section Prover

theorem hOnly_setupTreesOf (tr : Trace) : HOnly (setupTreesOf callKeccak256 tr) := by
  unfold setupTreesOf
  exact (E2ECompleteness.hOnly_commitWithH _ _).bind fun _ ↦ (E2ECompleteness.hOnly_commitWithH _ _).bind
    fun _ ↦ (E2ECompleteness.hOnly_commitWithH _ _).bind fun _ ↦ hOnly_pure _

theorem hOnly_contractIvOf (shape : Shape) (programIv : List UInt8) (roots : SetupRoots) :
    HOnly (contractIvOf callKeccak256 shape programIv roots) :=
  (hOnly_queryH _).bind fun _ ↦ hOnly_pure _

/-- One step of the openings' walk. -/
macro "disc_step" : tactic => `(tactic| first
  | with_reducible_and_instances exact disc_pure _
  | with_reducible_and_instances refine (E2ECompleteness.disc_proveOpeningWithH _ _ _ _ _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine (disc_pure _).bind fun _ ↦ ?_
  | dsimp only)

/-- **The honest prover is disciplined**, from any earlier answers, given that Flock's prover only hashes. -/
theorem disc_proveWith (flock : FlockProverH) (hflock : FlockHashOnly flock) (fuel : ℕ) (blake2s : Blake2s)
    (programIv : List UInt8) (tr : Trace) :
    Disc (proveWith callKeccak256 callKeccakF1600 fuel (flock callKeccak256) blake2s programIv tr) := by
  unfold proveWith
  refine (disc_of_hOnly (hOnly_setupTreesOf tr)).bind fun trees ↦ ?_
  refine (disc_of_hOnly (hOnly_contractIvOf _ _ _)).bind fun iv ↦ ?_
  refine (disc_of_hOnly (hOnly_queryH _)).bind fun seed ↦ ?_
  refine (disc_of_hOnly (wHOnly_proveStreamWith _ hOnly_commitReal _ (hflock · · ·) blake2s tr _)).bind
    fun x ↦ ?_
  obtain ⟨out, _⟩ := x
  dsimp only
  generalize List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  generalize out.matrices = om
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    rcases om with _ | mc <;> repeat disc_step

/-- **The deployed honest prover is disciplined**, from any earlier answers. -/
theorem disc_uniProverWith (flock : FlockProverH) (hflock : FlockHashOnly flock) (D : Deployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    Disc (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) :=
  disc_proveWith flock hflock _ _ _ _

/-- **The deployed honest prover follows the duplex discipline** (mumbai's `DuplexVm`, from no earlier answer),
given that Flock's prover only hashes. -/
theorem duplexVm_uniProverWith (flock : FlockProverH) (hflock : FlockHashOnly flock) (D : Deployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    DuplexVm (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) [] :=
  (duplexVm_iff_duplexP _ _).mpr (disc_uniProverWith flock hflock D input rows q [])

end Prover

end UniComplete

/-- info: 'UniComplete.duplexVm_uniProverWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.duplexVm_uniProverWith

/-- info: 'UniComplete.disc_uniProverWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.disc_uniProverWith

/-- info: 'UniComplete.flockHashOnly_of_commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.flockHashOnly_of_commutes
