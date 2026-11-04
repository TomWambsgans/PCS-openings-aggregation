-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The facts transferred are `formal/UniComplete`'s
-- (`Rec3ProverDuplex.lean`'s `disc_uniProverRec3With`, `Rec3ProverCost.lean`'s `proverCost3_flockProve3H`); uses
-- leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two
-- calls `KeccakCalls`, the duplex discipline `DuplexP`, the block cost `hashBlocks`, `QueryCostAtMost`; VCVio's
-- `simulateQ`, `IsQueryBound`; and `formal/EndToEnd/Completeness/E2ECompleteness`'s `Disc`, `HashOK`,
-- `simulateQ_proveOpeningWithH`.
import RecCompose.Pi1KF
import UniComplete.Rec3ProverDuplex
import UniComplete.Rec3ProverCost

/-!
# The recursion's π1 prover inherits UniComplete's prover's per-query facts

`p1kKF D` (`Pi1KF.lean`) is UniComplete's two-call prover `uniProverRec3With callKeccak256 callKeccakF1600
(flockProve3H callKeccak256)` with its Fiat–Shamir calls answered by the pure `keccak256` instead of
`callKeccak256`. Both are simulations of **one program over three calls** (`FsCalls`: the Fiat–Shamir hash `qFs`, the
trees' hash `qH`, the permutation `qF`), `uprover D input rows q = uniProverRec3With2 qFs qH qF (flockProve3H qFs) …`:

* **`sim_uprover_old`**: answered by `implOld` (`qFs`, `qH` both `callKeccak256`), it is UniComplete's prover;
* **`sim_uprover_new`**: answered by `implNew keccak256` (`qFs` the pure `keccak256`), it is `p1kKF`.

Every fact that holds along every path and only weakens when a hash query is dropped transfers from the first to the
second, by induction on the three-call program (a `qFs` query of the first answered at `keccak256 x`):

* **`duplexP_new`** (the duplex discipline: permutation queries unchanged, the history of permutation answers
  unchanged), hence **`disc_p1kKF : Disc (p1kKF D input rows q)`** from `disc_uniProverRec3With`;
* **`qc_new`** (a block count: the dropped queries' blocks left over), hence **`qc_p1kKF`**: at most `2^47` block calls,
  from `proverCost3_flockProve3H`;
* **`hashOK_new`** (every hash query satisfies `P`), for the census of `Pi2AlphaLen` (`Pi2KF.lean`).

The opening (`proveOpeningWithH`) is written over the two calls and lifted (`liftImpl`): over three calls it is the
lift of the two-call one (`E2ECompleteness.simulateQ_proveOpeningWithH`), and either simulation undoes the lift
(`sim_old_lift`, `sim_new_lift`).
-/

set_option autoImplicit false

namespace RecCompose.Pi1KF

open UniStatement LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open UniComplete UniComplete.Rec3
open LeanVM.Protocol.Compile.Rom (implH implF)
open E2ECompleteness (Disc HashOK)

/-! ## Three calls -/

/-- **The three calls**: the Fiat–Shamir hash, then the two calls (the trees' Keccak-256, Keccak-f[1600]). -/
abbrev FsCalls : OracleSpec (List UInt8 ⊕ (List UInt8 ⊕ KeccakState)) := (List UInt8 →ₒ Digest) + KeccakCalls

/-- The Fiat–Shamir hash's call. -/
def qFs (x : List UInt8) : OracleComp FsCalls Digest := liftM (FsCalls.query (.inl x))

/-- The trees' hash's call. -/
def qH (x : List UInt8) : OracleComp FsCalls Digest := liftM (FsCalls.query (.inr (.inl x)))

/-- The permutation's call. -/
def qF (s : KeccakState) : OracleComp FsCalls KeccakState := liftM (FsCalls.query (.inr (.inr s)))

/-- The two calls inside the three. -/
def liftImpl : QueryImpl KeccakCalls (OracleComp FsCalls) := fun t ↦ liftM (FsCalls.query (.inr t))

/-- **One hash**: the Fiat–Shamir and the trees' calls both `callKeccak256`. -/
def implOld : QueryImpl FsCalls (OracleComp KeccakCalls)
  | .inl x => callKeccak256 x
  | .inr t => liftM (KeccakCalls.query t)

/-- **The Fiat–Shamir pure** (`h`), the two calls as they are. -/
def implNew (h : List UInt8 → Digest) : QueryImpl FsCalls (OracleComp KeccakCalls)
  | .inl x => pure (h x)
  | .inr t => liftM (KeccakCalls.query t)

theorem sim_old_lift {α : Type} (X : OracleComp KeccakCalls α) :
    simulateQ implOld (simulateQ liftImpl X) = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, liftImpl, implOld, ih]

theorem sim_new_lift (h : List UInt8 → Digest) {α : Type} (X : OracleComp KeccakCalls α) :
    simulateQ (implNew h) (simulateQ liftImpl X) = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, liftImpl, implNew, ih]

theorem implH_lift : implH liftImpl = qH := rfl
theorem implF_lift : implF liftImpl = qF := rfl

/-- The opening over three calls is the lifted two-call one. -/
theorem open_lift (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim) :
    E2ECompleteness.proveOpeningWithH qH qF fuel L tree stack claims =
      simulateQ liftImpl (E2ECompleteness.proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims) := by
  rw [E2ECompleteness.simulateQ_proveOpeningWithH liftImpl]
  rfl

theorem sim_old_qFs : (fun x ↦ (Morph.sim implOld).app (qFs x)) = callKeccak256 := by
  funext x
  exact simulateQ_spec_query implOld (.inl x)

theorem sim_old_qH : (fun x ↦ (Morph.sim implOld).app (qH x)) = callKeccak256 := by
  funext x
  exact simulateQ_spec_query implOld (.inr (.inl x))

theorem sim_old_qF : (fun s ↦ (Morph.sim implOld).app (qF s)) = callKeccakF1600 := by
  funext s
  exact simulateQ_spec_query implOld (.inr (.inr s))

theorem sim_new_qFs (h : List UInt8 → Digest) :
    (fun x ↦ (Morph.sim (implNew h)).app (qFs x)) = fun x ↦ (pure (h x) : OracleComp KeccakCalls Digest) := by
  funext x
  exact simulateQ_spec_query (implNew h) (.inl x)

theorem sim_new_qH (h : List UInt8 → Digest) : (fun x ↦ (Morph.sim (implNew h)).app (qH x)) = callKeccak256 := by
  funext x
  exact simulateQ_spec_query (implNew h) (.inr (.inl x))

theorem sim_new_qF (h : List UInt8 → Digest) :
    (fun s ↦ (Morph.sim (implNew h)).app (qF s)) = callKeccakF1600 := by
  funext s
  exact simulateQ_spec_query (implNew h) (.inr (.inr s))

/-! ## The program over three calls -/

/-- **π1-rec3's honest prover over three calls.** -/
def uprover (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    OracleComp FsCalls (Option UniProof) :=
  uniProverRec3With2 qFs qH qF (flockProve3H qFs) D input rows q

/-- **Answered with one hash, UniComplete's two-call prover.** -/
theorem sim_uprover_old (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ implOld (uprover D input rows q) =
      uniProverRec3With callKeccak256 callKeccakF1600 (flockProve3H callKeccak256) D input rows q := by
  have h := app_proveRec3With2 (Morph.sim implOld) qFs qH qF
    (fun fuel L tree stack claims ↦ by
      rw [sim_old_qH, sim_old_qF, open_lift]
      exact sim_old_lift _)
    (flockProve3H qFs) (flockProve3H callKeccak256)
    (fun logN v q ↦ by rw [flockCommutes_flockProve3H, sim_old_qFs]) PcsQuotient.nonceFuel D.programIv
    (honestTrace D input rows q)
  rw [sim_old_qFs, sim_old_qH, sim_old_qF] at h
  exact h

/-- **Answered with the Fiat–Shamir pure (`h`)**, the two-hash prover over the two calls. -/
theorem sim_uprover_new (h : List UInt8 → Digest) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) :
    simulateQ (implNew h) (uprover D input rows q) =
      uniProverRec3With2 (fun x ↦ (pure (h x) : OracleComp KeccakCalls Digest)) callKeccak256 callKeccakF1600
        (flockProve3H fun x ↦ (pure (h x) : OracleComp KeccakCalls Digest)) D input rows q := by
  have e := app_proveRec3With2 (Morph.sim (implNew h)) qFs qH qF
    (fun fuel L tree stack claims ↦ by
      rw [sim_new_qH, sim_new_qF, open_lift]
      exact sim_new_lift h _)
    (flockProve3H qFs) (flockProve3H fun x ↦ (pure (h x) : OracleComp KeccakCalls Digest))
    (fun logN v q ↦ by rw [flockCommutes_flockProve3H, sim_new_qFs]) PcsQuotient.nonceFuel D.programIv
    (honestTrace D input rows q)
  rw [sim_new_qFs, sim_new_qH, sim_new_qF] at e
  exact e

/-- `p1kKF` is the three-call program answered with the Fiat–Shamir pure. -/
theorem p1kKF_eq_sim (D : RecStatement.RecDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) : p1kKF D input rows q = simulateQ (implNew keccak256) (uprover D.pi1 input rows q) := by
  rw [sim_uprover_new]
  rfl

/-! ## The transfers -/

section Transfer

variable {α : Type} (h : List UInt8 → Digest)

/-- **The duplex discipline transfers** (the hash queries change no history). -/
theorem duplexP_new (X : OracleComp FsCalls α) :
    ∀ (hist : List KeccakState) (Q : α → List KeccakState → Prop),
      DuplexP (simulateQ implOld X) hist Q → DuplexP (simulateQ (implNew h) X) hist Q := by
  induction X using OracleComp.inductionOn with
  | pure a => intro hist Q hX; simpa using hX
  | query_bind t k ih =>
    intro hist Q hX
    rw [simulateQ_bind, simulateQ_spec_query] at hX ⊢
    rcases t with x | (x | s)
    · exact ih (h x) hist Q (hX (h x))
    · exact fun u ↦ ih u hist Q (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (y :: hist) Q (hX.2 y)⟩

/-- **A block count transfers**: a dropped query's blocks are left over. -/
theorem qc_new (X : OracleComp FsCalls α) :
    ∀ (n n' : ℕ), Common.QueryCostAtMost (simulateQ implOld X) hashBlocks n → n ≤ n' →
      Common.QueryCostAtMost (simulateQ (implNew h) X) hashBlocks n' := by
  induction X using OracleComp.inductionOn with
  | pure a => intro _ _ _ _; simp only [simulateQ_pure]; trivial
  | query_bind t k ih =>
    intro n n' hX hn
    rw [simulateQ_bind, simulateQ_spec_query] at hX ⊢
    rcases t with x | (x | s)
    · rw [implOld, callKeccak256, Common.isWeightBound_query_bind_iff] at hX
      rw [implNew, pure_bind]
      exact ih (h x) _ _ (hX.2 (h x)) (by omega)
    · rw [implOld, Common.isWeightBound_query_bind_iff] at hX
      rw [implNew, Common.isWeightBound_query_bind_iff]
      exact ⟨hX.1.trans hn, fun u ↦ ih u _ _ (hX.2 u) (by omega)⟩
    · rw [implOld, Common.isWeightBound_query_bind_iff] at hX
      rw [implNew, Common.isWeightBound_query_bind_iff]
      exact ⟨hX.1.trans hn, fun u ↦ ih u _ _ (hX.2 u) (by omega)⟩

/-- **Every hash query satisfying `P` transfers.** -/
theorem hashOK_new (P : List UInt8 → Prop) (X : OracleComp FsCalls α) :
    HashOK P (simulateQ implOld X) → HashOK P (simulateQ (implNew h) X) := by
  induction X using OracleComp.inductionOn with
  | pure a => intro _; simp only [simulateQ_pure]; trivial
  | query_bind t k ih =>
    intro hX
    rw [simulateQ_bind, simulateQ_spec_query] at hX ⊢
    rcases t with x | (x | s)
    · rw [implOld, callKeccak256, E2ECompleteness.HashOK, isQueryBound_query_bind_iff] at hX
      rw [implNew, pure_bind]
      exact ih (h x) (hX.2 (h x))
    · rw [implOld, E2ECompleteness.HashOK, isQueryBound_query_bind_iff] at hX
      rw [implNew, E2ECompleteness.HashOK, isQueryBound_query_bind_iff]
      exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩
    · rw [implOld, E2ECompleteness.HashOK, isQueryBound_query_bind_iff] at hX
      rw [implNew, E2ECompleteness.HashOK, isQueryBound_query_bind_iff]
      exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

end Transfer

/-! ## The recursion's π1 prover's facts -/

/-- **The recursion's π1 prover is disciplined**, from any earlier answers (UniComplete's prover's discipline,
`disc_uniProverRec3With`, transferred). -/
theorem disc_p1kKF (D : RecStatement.RecDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) : Disc (p1kKF D input rows q) := by
  intro hist
  rw [p1kKF_eq_sim]
  refine duplexP_new keccak256 _ hist _ ?_
  rw [sim_uprover_old]
  exact disc_uniProverRec3With flockProve3H (flockHashOnly_of_commutes _ flockCommutes_flockProve3H) D.pi1 input
    rows q hist

/-- **The recursion's π1 prover makes at most `2^47` block calls** at the reference shape (UniComplete's prover's
count, `proverCost3_flockProve3H`, transferred: its Fiat–Shamir hashes are no calls). -/
theorem qc_p1kKF (D : RecStatement.RecDeployment) (hD : D.pi1.shape = reference)
    (hIv : D.pi1.programIv.length ≤ 2 ^ 16) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (hfit : D.pi1.shape.RowsFit rows) (hrel : D.pi1.HonestRelation rows input q) :
    Common.QueryCostAtMost (p1kKF D input rows q) hashBlocks (2 ^ 47) := by
  rw [p1kKF_eq_sim]
  refine qc_new keccak256 _ _ _ ?_ le_rfl
  rw [sim_uprover_old]
  exact proverCost3_flockProve3H D.pi1 hD hIv input rows q hfit hrel

/-- **Every hash query of the recursion's π1 prover satisfies `P`** when every one of UniComplete's prover's does. -/
theorem hashOK_p1kKF_of (D : RecStatement.RecDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) (P : List UInt8 → Prop)
    (h : HashOK P (uniProverRec3With callKeccak256 callKeccakF1600 (flockProve3H callKeccak256) D.pi1 input rows q)) :
    HashOK P (p1kKF D input rows q) := by
  rw [p1kKF_eq_sim]
  refine hashOK_new keccak256 P _ ?_
  rw [sim_uprover_old]
  exact h

end RecCompose.Pi1KF

/-- info: 'RecCompose.Pi1KF.disc_p1kKF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.disc_p1kKF

/-- info: 'RecCompose.Pi1KF.qc_p1kKF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.qc_p1kKF

/-- info: 'RecCompose.Pi1KF.hashOK_p1kKF_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.hashOK_p1kKF_of
