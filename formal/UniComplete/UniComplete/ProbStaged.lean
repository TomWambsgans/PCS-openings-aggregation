-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/EndToEnd/Completeness/E2ECompleteness/End.lean` (`Staged`, `Staged.Holds`, `completeness_of_staged`)
-- for the univariate verifier; uses its `rpm_le_rom` (`Transfer.lean`, mumbai's indifferentiability transfer) and
-- leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two
-- calls and their random-permutation model, `rpmError`, the duplex discipline `DuplexVm` and the block cost
-- `hashBlocks`.
import UniComplete.ProbChain
import E2ECompleteness.Transfer
import UniStatement.Security

/-!
# `UniCompletenessWith`, from the staged two-call experiment

The end statement `UniCompletenessWith D P δ` (`formal/UniStatement`, `Security.lean`) is about the completeness
experiment in one random permutation: the setup, the prover `P`, the deployed verifier, all over `π`. **What is
proved here** (`uniCompleteness_of_staged`): if for every honest witness the experiment is the verdict of a two-call
computation of the bus challenges' shape (`UniStaged`, `UniStaged.Holds`), then

  `δ = Nbad / 2^192 + 6 / 2^256 + εpow + N² / 2^508`:

* `N² / 2^508` (`rpmError N`): the random permutation is two random oracles to an honest computation of at most `N`
  block calls following the duplex discipline (`E2ECompleteness.rpm_le_rom`);
* `Nbad / 2^192 + 6 / 2^256`: the bus challenges `(α, β)` are bad (`bad`, at most `Nbad` values of `β` for each `α`)
  with at most that probability (`prEvent_staged5_le`, the queries fresh by their lengths, `GoodL 88`);
* `εpow`: in the two-call random-oracle model the honest proof is rejected at good challenges with probability at
  most `εpow` (`Holds.rejectGood`, the grinding).

Decisions: no coins (the univariate prover is deterministic, `uniProverWith`), so the experiment is an equality, not a
distributional one; the bad set is a parameter of `Holds` (the univariate `BadFp` of the honest trace in the end
theorem); the first chain input is `88` bytes (the state, six 4-byte row counts, `C1`'s root word).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement
open E2ECompleteness (ro HashOK)
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Prob

/-- **The experiment's stages** (no coins): `A` up to the first bus-challenge input (`inp`, `88` bytes), the five
chained answers, `C` the rest (the prover's tail and the verifier), its output the verdict. -/
structure UniStaged where
  α : Type
  inp : α → Bytes
  A : OracleComp KeccakCalls α
  C : α → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls Bool

/-- The two-call run: the verdict and the bus challenges `(α, β)` (`challengeOf` of the five answers). -/
def UniStaged.run (S : UniStaged) : OracleComp KeccakCalls (Bool × (List E × E)) :=
  staged5 PcsQuotient.Transcript.challengeOf S.inp S.A S.C

/-- **The code-level bridge** of the univariate experiment for `(input, rows, q)`, at a bad set `bad` of at most
`Nbad` values of `β` per `α`, `N` block calls and a proof-of-work error `εpow`. -/
structure UniStaged.Holds (S : UniStaged) (D : Deployment) (P : UniProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (bad : List E → E → Prop) (Nbad N : ℕ) (εpow : ℝ≥0∞) : Prop where
  /-- The experiment is the verdict of the two-call run against the random permutation. -/
  experiment : uniCompletenessExperiment D P input rows q =
    (fun z ↦ z.1) <$> (simulateQ keccakCallsOverRandomPermutation S.run).run' []
  /-- Every permutation call continues a duplex or starts one (`DuplexVm`). -/
  duplex : DuplexVm S.run []
  /-- At most `N` block calls (`hashBlocks`). -/
  cost : Common.QueryCostAtMost S.run hashBlocks N
  /-- The first bus-challenge input has `88` bytes. -/
  inp_length : ∀ a, (S.inp a).length = 88
  /-- Before it, nothing of the chain's lengths (`32`, `88`) is hashed. -/
  hashA : HashOK (GoodL 88) S.A
  /-- At most `Nbad` bad values of `β` for each `α`. -/
  badCard : ∀ alphas, ∃ T : Finset E, T.card ≤ Nbad ∧ ∀ b, bad alphas b → b ∈ T
  /-- **Grinding**: in the two-call random-oracle model the honest proof is rejected at good challenges with
  probability at most `εpow`. -/
  rejectGood : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1 = false ∧ ¬ bad z.2.1 z.2.2] ≤ εpow

/-- **One witness**: the run is rejected with probability at most the bad challenges' `Nbad / 2^192 + 6 / 2^256`,
`εpow` and the transfer's `rpmError N`. -/
theorem prEvent_run_false_le (S : UniStaged) {D : Deployment} {P : UniProver D} {input : Vector UInt8 32}
    {rows : List ℕ} {q : D.Stack rows} {bad : List E → E → Prop} {Nbad N : ℕ} {εpow : ℝ≥0∞}
    (h : S.Holds D P input rows q bad Nbad N εpow) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1 = false] ≤
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + εpow) + rpmError N := by
  refine E2ECompleteness.rpm_le_rom S.run h.duplex h.cost (fun z ↦ z.1 = false) ?_
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _ (fun z : Bool × (List E × E) ↦ bad z.2.1 z.2.2)).trans ?_
  refine add_le_add ?_ h.rejectGood
  have hc : Pr{let z ← (simulateQ ro S.run).run' ∅}[bad z.2.1 z.2.2] =
      Pr{let z ← (simulateQ ro S.run).run ∅}[bad z.1.2.1 z.1.2.2] := by
    rw [StateT.run'_eq, prEvent_map]
  rw [hc]
  refine (prEvent_staged5_le _ E2ECompleteness.challengeOf_regular (by norm_num) bad Nbad h.badCard S.inp
    h.inp_length S.A S.C h.hashA ∅ fun m hm ↦ absurd rfl hm).trans ?_
  rw [add_comm]

/-- **`UniCompletenessWith` in the random-permutation model, from the staged experiment.** -/
theorem uniCompleteness_of_staged {D : Deployment} {P : UniProver D} {Nbad N : ℕ} {εpow : ℝ≥0∞}
    (hS : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
      D.HonestRelation rows input q →
      ∃ (S : UniStaged) (bad : List E → E → Prop), S.Holds D P input rows q bad Nbad N εpow) :
    UniCompletenessWith D P ((Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + εpow + rpmError N) := by
  intro input rows q hfit hrel
  obtain ⟨S, bad, h⟩ := hS input rows q hfit hrel
  rw [h.experiment, prEvent_map]
  exact prEvent_run_false_le S h

end UniComplete.Prob

/-- info: 'UniComplete.Prob.uniCompleteness_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Prob.uniCompleteness_of_staged
