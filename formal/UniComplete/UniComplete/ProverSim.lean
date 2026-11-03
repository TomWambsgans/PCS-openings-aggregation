-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls` and their simulation lemmas (`implH`, `implF`, `simulateQ_queryH`), the Merkle
-- tree's runner (`buildTreeWithHash`, as `simulateQ_buildTreeM` commutes it); and
-- `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean`'s `simulateQ_proveOpeningWithH`.
import UniComplete.Witness
import UniComplete.VerifierHSim

/-!
# The honest prover commutes with simulation

The honest prover (`proveWith`, `uniProverWith`) is written over any monad, Keccak-256 `H` and the permutation `F`
explicit. Over the two calls (`callKeccak256`, `callKeccakF1600`) it commutes with any simulation `impl`:
**`simulateQ_uniProverWith`**, the prover's half of the random-oracle transfer (the verifier's is
`simulateQ_verifierWithH`).

As for the verifier (`VerifierHSim`), the commutation is proved once for **any monad morphism** (`Morph`):

* `Morph.wr` lifts a morphism `m → n` to the writer's monads `WrM m = StateT Wr m` (the state passes through) and
  keeps `pure`, `bind`, `get`, `set`, `modify`, the lift of `m`, `<$>` and the loops (`wr_…`);
* every function of the prover commutes with it, the hash `H` becoming `φ ∘ H` (`wr_sampleW`, …,
  `wr_proveStreamWith`); a commitment (`commitWithH`, a Merkle tree) commutes with any morphism
  (`app_commitWithH`), so the setup, the IV and the seed do (`app_setupTreesOf`, …);
* **Flock's prover is a parameter** (another layer writes it), polymorphic in the monad and the hash
  (`FlockProverH`). The one fact used of it is named: **`FlockCommutes`**, it commutes with every monad morphism
  (`φ.wr (flock H …) = flock (φ ∘ H) …`), as every prover written in `WrM m` from `H`, `sampleW`, `sendBytes` and
  pure code does;
* the five WHIR openings commute given that the opening does (`hopen`, which WithHash proves for `simulateQ`):
  **`app_proveWith`**, **`app_uniProverWith`**.

`Morph.sim impl` (`simulateQ impl` as a morphism) discharges `hopen` by WithHash's `simulateQ_proveOpeningWithH`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open UniStatement

namespace UniComplete

/-- **Flock's prover, generic in the monad and the hash**: what `uniProverWith` is given as its `flock`, at
`H`. -/
abbrev FlockProverH : Type 1 := ∀ {m : Type → Type} [Monad m], (List UInt8 → m Digest) → FlockProver m

namespace Morph

section Wr

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Morph m n)

/-- **The morphism on the writer's monad**: the state passes through. -/
def wr {α : Type} (x : WrM m α) : WrM n α := fun s ↦ φ.app (x.run s)

theorem wr_run {α : Type} (x : WrM m α) (s : Wr) : (φ.wr x).run s = φ.app (x.run s) := rfl

omit [Monad n] in
theorem wr_ext {α : Type} {x y : WrM n α} (h : ∀ s, x.run s = y.run s) : x = y := funext h

theorem wr_pure {α : Type} (a : α) : φ.wr (pure a : WrM m α) = pure a :=
  wr_ext fun s ↦ φ.app_pure (a, s)

theorem wr_bind {α β : Type} (x : WrM m α) (f : α → WrM m β) :
    φ.wr (x >>= f) = φ.wr x >>= fun a ↦ φ.wr (f a) :=
  wr_ext fun s ↦ by simp only [wr_run, StateT.run_bind, φ.app_bind]

theorem wr_get : φ.wr (get : WrM m Wr) = get :=
  wr_ext fun s ↦ φ.app_pure (s, s)

theorem wr_set (s' : Wr) : φ.wr (set s' : WrM m PUnit) = set s' :=
  wr_ext fun _ ↦ φ.app_pure (PUnit.unit, s')

theorem wr_modify (f : Wr → Wr) : φ.wr (modify f : WrM m PUnit) = modify f :=
  wr_ext fun s ↦ φ.app_pure (PUnit.unit, f s)

theorem wr_lift {α : Type} (y : m α) : φ.wr (StateT.lift y : WrM m α) = StateT.lift (φ.app y) :=
  wr_ext fun s ↦ by simp only [wr_run, StateT.run_lift, φ.app_bind, φ.app_pure]

theorem wr_map {α β : Type} (f : α → β) (x : WrM m α) [LawfulMonad m] [LawfulMonad n] :
    φ.wr (f <$> x) = f <$> φ.wr x := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, wr_bind]
  simp only [Function.comp_def, wr_pure]

theorem wr_ite {α : Type} (c : Prop) [Decidable c] (x y : WrM m α) :
    φ.wr (if c then x else y) = if c then φ.wr x else φ.wr y := by
  split <;> rfl

/-- A loop over a list. -/
theorem wr_forIn_list {α β : Type} (l : List α) (b : β) (f : α → β → WrM m (ForInStep β)) :
    φ.wr (forIn l b f) = forIn l b fun a s ↦ φ.wr (f a s) := by
  induction l generalizing b with
  | nil => exact φ.wr_pure b
  | cons a l ih =>
    simp only [List.forIn_cons, wr_bind]
    congr 1
    funext s
    cases s with
    | done b => exact φ.wr_pure b
    | yield b => exact ih b

end Wr

/-! ### A commitment commutes with any morphism -/

section Commit

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)

theorem app_listMapM {α β : Type} (f : α → m β) :
    ∀ l : List α, φ.app (l.mapM f) = l.mapM fun a ↦ φ.app (f a)
  | [] => by simp only [List.mapM_nil, φ.app_pure]
  | a :: l => by
    simp only [List.mapM_cons, φ.app_bind, φ.app_pure]
    congr 1; funext b; rw [app_listMapM f l]

theorem app_arrayMapM {α β : Type} (f : α → m β) (xs : Array α) :
    φ.app (xs.mapM f) = xs.mapM fun a ↦ φ.app (f a) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, app_map, app_listMapM]

variable (H : List UInt8 → m Digest)

theorem app_levelsWithHash :
    ∀ (k : ℕ) (level : Array Digest),
      φ.app (LeanVM.Prover.levelsWithHash H k level) =
        LeanVM.Prover.levelsWithHash (fun x ↦ φ.app (H x)) k level
  | 0, _ => by simp only [LeanVM.Prover.levelsWithHash, φ.app_pure]
  | k + 1, level => by
    simp only [LeanVM.Prover.levelsWithHash, LeanVM.Prover.parentsWithHash, φ.app_bind, φ.app_pure,
      app_arrayMapM]
    congr 1; funext up; rw [app_levelsWithHash k up]

theorem app_buildTreeWithHash (height : ℕ) (word : LeanVM.Protocol.Compile.Word) :
    φ.app (LeanVM.Prover.buildTreeWithHash H height word) =
      LeanVM.Prover.buildTreeWithHash (fun x ↦ φ.app (H x)) height word := by
  simp only [LeanVM.Prover.buildTreeWithHash, LeanVM.Prover.leafDigestsWithHash, φ.app_bind, app_arrayMapM,
    app_levelsWithHash, φ.app_pure]

theorem app_commitWithH (μ : ℕ) (stack : Array K) :
    φ.app (E2ECompleteness.commitWithH H μ stack) = E2ECompleteness.commitWithH (fun x ↦ φ.app (H x)) μ stack :=
  app_buildTreeWithHash φ H _ _

end Commit

/-! ### The prover's functions -/

section Prover

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest)

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_sendBytes (b : List UInt8) : φ.wr (sendBytes (m := m) b) = sendBytes b := φ.wr_modify _

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_sendScalar (x : E) : φ.wr (sendScalar (m := m) x) = sendScalar x := φ.wr_sendBytes _

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_sendScalars (xs : List E) : φ.wr (sendScalars (m := m) xs) = sendScalars xs := φ.wr_sendBytes _

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_sendInteger (v bytes : ℕ) : φ.wr (sendInteger (m := m) v bytes) = sendInteger v bytes :=
  φ.wr_sendBytes _

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_sendRoot (halves : E × E) : φ.wr (sendRoot (m := m) halves) = sendRoot halves := φ.wr_sendBytes _

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_sampleW : φ.wr (sampleW H) = sampleW fun x ↦ φ.app (H x) := by
  simp only [sampleW, wr_bind, wr_get, wr_lift, wr_set, wr_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_samplesW : ∀ count : ℕ, φ.wr (samplesW H count) = samplesW (fun x ↦ φ.app (H x)) count
  | 0 => φ.wr_pure _
  | count + 1 => by
    simp only [samplesW, wr_bind, wr_sampleW, wr_pure, wr_samplesW count]

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_batchRound (lambda : E) (j : ℕ) (st : BatchState) :
    φ.wr (batchRound H lambda j st) = batchRound (fun x ↦ φ.app (H x)) lambda j st := by
  simp only [batchRound, wr_bind, wr_sendScalar, wr_sampleW, wr_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem wr_batchRounds (lambda : E) (vars : ℕ) (st : BatchState) :
    φ.wr (batchRounds H lambda vars st) = batchRounds (fun x ↦ φ.app (H x)) lambda vars st := by
  simp only [batchRounds, wr_bind, wr_forIn_list, wr_batchRound, wr_pure]

/-- **The stream commutes with a morphism** that commutes with the commitment and with Flock's prover. -/
theorem wr_proveStreamWith (commit : Commitment → ℕ → Array K → m Committed)
    (commit' : Commitment → ℕ → Array K → n Committed) (hcommit : ∀ c v s, φ.app (commit c v s) = commit' c v s)
    (flock : FlockProver m) (flock' : FlockProver n) (hflock : ∀ logN v q, φ.wr (flock logN v q) = flock' logN v q)
    (blake2s : Blake2s) (tr : Trace) :
    φ.wr (proveStreamWith H commit flock blake2s tr) =
      proveStreamWith (fun x ↦ φ.app (H x)) commit' flock' blake2s tr := by
  rcases blake2s with variant | _ <;>
  · simp only [proveStreamWith, wr_bind, wr_forIn_list, wr_sendInteger, wr_pure, wr_lift, hcommit, wr_sendRoot,
      wr_samplesW, wr_sampleW, wr_map, hflock, wr_sendScalars, wr_batchRounds]
    repeat (with_reducible refine bind_congr fun _ ↦ ?_)
    split <;> simp only [wr_bind, wr_sendScalars, wr_pure, wr_get]

end Prover

/-! ### The setup, the IV, the seed, the prover -/

section Top

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

theorem app_commitReal (c : Commitment) (vars : ℕ) (stack : Array K) :
    φ.app (commitReal H c vars stack) = commitReal (fun x ↦ φ.app (H x)) c vars stack := by
  simp only [commitReal, φ.app_bind, app_commitWithH, φ.app_pure]

theorem app_setupTreesOf (tr : Trace) : φ.app (setupTreesOf H tr) = setupTreesOf (fun x ↦ φ.app (H x)) tr := by
  simp only [setupTreesOf, φ.app_bind, app_commitWithH, φ.app_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_seedOf (iv publicInput : List UInt8) :
    φ.app (seedOf H iv publicInput) = seedOf (fun x ↦ φ.app (H x)) iv publicInput := rfl

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_contractIvOf (shape : Shape) (programIv : List UInt8) (roots : SetupRoots) :
    φ.app (contractIvOf H shape programIv roots) = contractIvOf (fun x ↦ φ.app (H x)) shape programIv roots := by
  simp only [contractIvOf, φ.app_bind, φ.app_pure]

/-- **The honest prover commutes with a monad morphism** that commutes with Flock's prover and with the opening
(`hopen`, WithHash's `simulateQ_proveOpeningWithH` for `simulateQ`). -/
theorem app_proveWith
    (hopen : ∀ (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
      (claims : List PcsQuotient.Claim),
      φ.app (E2ECompleteness.proveOpeningWithH H F fuel L tree stack claims) =
        E2ECompleteness.proveOpeningWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel L tree stack claims)
    (flock : FlockProver m) (flock' : FlockProver n) (hflock : ∀ logN v q, φ.wr (flock logN v q) = flock' logN v q)
    (fuel : ℕ) (blake2s : Blake2s) (programIv : List UInt8) (tr : Trace) :
    φ.app (proveWith H F fuel flock blake2s programIv tr) =
      proveWith (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel flock' blake2s programIv tr := by
  have hs : ∀ seed, φ.app ((proveStreamWith H (commitReal H) flock blake2s tr).run (Wr.start seed)) =
      (proveStreamWith (fun x ↦ φ.app (H x)) (commitReal fun x ↦ φ.app (H x)) flock' blake2s tr).run
        (Wr.start seed) := fun seed ↦ by
    rw [← wr_run, wr_proveStreamWith φ H _ _ (app_commitReal φ H) flock flock' hflock]
  simp only [proveWith, φ.app_bind, app_setupTreesOf, app_contractIvOf, app_seedOf, hs]
  refine bind_congr fun trees ↦ bind_congr fun iv ↦ bind_congr fun seed ↦ bind_congr fun x ↦ ?_
  obtain ⟨out, _⟩ := x
  dsimp only
  generalize List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  generalize out.matrices = om
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    rcases om with _ | mc <;> simp only [φ.app_bind, φ.app_pure, hopen]

/-- **The deployed honest prover commutes with a monad morphism** that commutes with Flock's prover and with the
opening. -/
theorem app_uniProverWith
    (hopen : ∀ (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
      (claims : List PcsQuotient.Claim),
      φ.app (E2ECompleteness.proveOpeningWithH H F fuel L tree stack claims) =
        E2ECompleteness.proveOpeningWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel L tree stack claims)
    (flock : FlockProver m) (flock' : FlockProver n) (hflock : ∀ logN v q, φ.wr (flock logN v q) = flock' logN v q)
    (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    φ.app (uniProverWith H F flock D input rows q) =
      uniProverWith (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) flock' D input rows q :=
  app_proveWith φ H F hopen flock flock' hflock _ _ _ _

end Top

end Morph

/-- **Flock's prover commutes with every monad morphism**: at `φ ∘ H` it is the image under `φ` of its run at
`H`. The one fact the commutation uses of it. -/
def FlockCommutes (flock : FlockProverH) : Prop :=
  ∀ {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
    (H : List UInt8 → m Digest) (logN : ℕ) (variant : Flock.Variant) (words : Array K),
    φ.wr (flock H logN variant words) = flock (fun x ↦ φ.app (H x)) logN variant words

end UniComplete

/-! ## Over the two calls: `simulateQ` -/

namespace UniComplete

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- **The honest prover over the two calls commutes with any simulation**, at any fuel and Flock's mode. -/
theorem simulateQ_proveWith (flock : FlockProverH) (hflock : FlockCommutes flock) (fuel : ℕ) (blake2s : Blake2s)
    (programIv : List UInt8) (tr : Trace) :
    simulateQ impl (proveWith callKeccak256 callKeccakF1600 fuel (flock callKeccak256) blake2s programIv tr) =
      proveWith (implH impl) (implF impl) fuel (flock (implH impl)) blake2s programIv tr := by
  have h := Morph.app_proveWith (Morph.sim impl) callKeccak256 callKeccakF1600
    (fun fuel L tree stack claims ↦ by
      rw [Morph.sim_H, Morph.sim_F]
      exact E2ECompleteness.simulateQ_proveOpeningWithH impl fuel L tree stack claims)
    (flock callKeccak256) (flock (implH impl)) (fun logN v q ↦ by rw [hflock, Morph.sim_H]) fuel blake2s
    programIv tr
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

/-- **The deployed honest prover over the two calls commutes with any simulation**: simulated by `impl`, it is
the honest prover over `impl`'s two calls, Flock's prover at `impl`'s hash. -/
theorem simulateQ_uniProverWith (flock : FlockProverH) (hflock : FlockCommutes flock) (D : Deployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) =
      uniProverWith (implH impl) (implF impl) (flock (implH impl)) D input rows q :=
  simulateQ_proveWith impl flock hflock _ _ _ _

end Commute

end UniComplete

/-- info: 'UniComplete.simulateQ_uniProverWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.simulateQ_uniProverWith

/-- info: 'UniComplete.Morph.app_uniProverWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Morph.app_uniProverWith
