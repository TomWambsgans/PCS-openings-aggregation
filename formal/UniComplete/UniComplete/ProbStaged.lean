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

  `δ = Nbad / 2^192 + 6 / 2^256 + (ct / 2^192 + εt) + εpow + N² / 2^508`:

* `N² / 2^508` (`rpmError N`): the random permutation is two random oracles to an honest computation of at most `N`
  block calls following the duplex discipline (`E2ECompleteness.rpm_le_rom`);
* `Nbad / 2^192 + 6 / 2^256`: the bus challenges `(α, β)` are bad (`bad`, at most `Nbad` values of `β` for each `α`)
  with at most that probability (`prEvent_staged5_le`, the queries fresh by their lengths, `GoodL 88`);
* `ct / 2^192 + εt`: the point challenge `t` is bad (`badT`, at most `ct` values for each prior, Flock's point) with
  at most that probability (`prEvent_tquery_le`), `εt` the probability that `t`'s input was hashed before its query
  (`Holds.tFresh`: not fresh by its length, `64` bytes being a Merkle node's);
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
chained answers, `B` up to `t`'s input (`tin`; `pr` the prior `t`'s bad set depends on, Flock's point), `t`'s answer,
`C` the rest (the prover's tail and the verifier), its output the verdict. -/
structure UniStaged where
  α : Type
  β : Type
  inp : α → Bytes
  A : OracleComp KeccakCalls α
  B : α → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls β
  tin : β → Bytes
  pr : β → List E
  C : β → Digest → OracleComp KeccakCalls Bool

/-- After the bus challenges: `B`, `t`'s query, `C`; the verdict and `(pr b, t)`. -/
def UniStaged.tail (S : UniStaged) (a : S.α) (s₁ s₂ s₃ s₄ s₅ : Digest) :
    OracleComp KeccakCalls (Bool × (List E × E)) := do
  let b ← S.B a s₁ s₂ s₃ s₄ s₅
  let st ← callKeccak256 (S.tin b)
  let z ← S.C b st
  return (z, (S.pr b, PcsQuotient.Transcript.challengeOf st))

/-- The two-call run: the verdict with `t`'s stage, and the bus challenges `(α, β)`. -/
def UniStaged.run (S : UniStaged) : OracleComp KeccakCalls ((Bool × (List E × E)) × (List E × E)) :=
  staged5 PcsQuotient.Transcript.challengeOf S.inp S.A S.tail

/-- **The run up to `t`'s query**: `B`'s output and the bus challenges. -/
def UniStaged.pre (S : UniStaged) : OracleComp KeccakCalls (S.β × (List E × E)) := do
  let a ← S.A
  let s₁ ← callKeccak256 (S.inp a)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let s₄ ← callKeccak256 (digestBytes s₃)
  let s₅ ← callKeccak256 (digestBytes s₄)
  let b ← S.B a s₁ s₂ s₃ s₄ s₅
  return (b, ([PcsQuotient.Transcript.challengeOf s₁, PcsQuotient.Transcript.challengeOf s₂,
    PcsQuotient.Transcript.challengeOf s₃, PcsQuotient.Transcript.challengeOf s₄],
    PcsQuotient.Transcript.challengeOf s₅))

/-- **The run, cut at `t`.** -/
theorem UniStaged.run_eq_pre (S : UniStaged) :
    S.run = S.pre >>= fun x ↦ callKeccak256 (S.tin x.1) >>= fun st ↦ S.C x.1 st >>= fun z ↦
      pure ((z, (S.pr x.1, PcsQuotient.Transcript.challengeOf st)), x.2) := by
  simp only [UniStaged.run, staged5, UniStaged.tail, UniStaged.pre, bind_assoc, pure_bind]

/-- **The code-level bridge** of the univariate experiment for `(input, rows, q)`: bad sets `bad` (bus challenges, at
most `Nbad` values of `β` per `α`) and `badT` (`t`, at most `ct` values per prior), `N` block calls, `t`'s cache-hit
probability `εt` and a proof-of-work error `εpow`. -/
structure UniStaged.Holds (S : UniStaged) (D : Deployment) (P : UniProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (bad badT : List E → E → Prop) (Nbad ct N : ℕ) (εt εpow : ℝ≥0∞) :
    Prop where
  /-- The experiment is the verdict of the two-call run against the random permutation. -/
  experiment : uniCompletenessExperiment D P input rows q =
    (fun z ↦ z.1.1) <$> (simulateQ keccakCallsOverRandomPermutation S.run).run' []
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
  /-- At most `ct` bad values of `t` for each prior. -/
  badTCard : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ t, badT fp t → t ∈ T
  /-- `t`'s input is already hashed before its query with probability at most `εt`. -/
  tFresh : Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none] ≤ εt
  /-- **Grinding**: in the two-call random-oracle model the honest proof is rejected at good challenges with
  probability at most `εpow`. -/
  rejectGood : Pr{let z ← (simulateQ ro S.run).run' ∅}[
    z.1.1 = false ∧ ¬ bad z.2.1 z.2.2 ∧ ¬ badT z.1.2.1 z.1.2.2] ≤ εpow

/-- **One witness**: the run is rejected with probability at most the bus challenges' `Nbad / 2^192 + 6 / 2^256`,
`t`'s `ct / 2^192 + εt`, `εpow` and the transfer's `rpmError N`. -/
theorem prEvent_run_false_le (S : UniStaged) {D : Deployment} {P : UniProver D} {input : Vector UInt8 32}
    {rows : List ℕ} {q : D.Stack rows} {bad badT : List E → E → Prop} {Nbad ct N : ℕ} {εt εpow : ℝ≥0∞}
    (h : S.Holds D P input rows q bad badT Nbad ct N εt εpow) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1 = false] ≤
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow) + rpmError N := by
  refine E2ECompleteness.rpm_le_rom S.run h.duplex h.cost (fun z ↦ z.1.1 = false) ?_
  -- The bus challenges.
  have hab : Pr{let z ← (simulateQ ro S.run).run' ∅}[bad z.2.1 z.2.2] ≤
      6 / 2 ^ 256 + (Nbad : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_staged5_le _ E2ECompleteness.challengeOf_regular (by norm_num) bad Nbad h.badCard S.inp
      h.inp_length S.A S.tail h.hashA ∅ fun m hm ↦ absurd rfl hm
  -- `t`.
  have ht : Pr{let z ← (simulateQ ro S.run).run' ∅}[badT z.1.2.1 z.1.2.2] ≤
      εt + (ct : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map, S.run_eq_pre]
    refine (prEvent_tquery_le _ E2ECompleteness.challengeOf_regular badT ct h.badTCard S.pre
      (fun x ↦ S.tin x.1) (fun x ↦ S.pr x.1) (fun x st ↦ S.C x.1 st)
      (fun x st z ↦ ((z, (S.pr x.1, PcsQuotient.Transcript.challengeOf st)), x.2))
      (fun w ↦ badT w.1.2.1 w.1.2.2) (fun _ _ _ hw ↦ hw) ∅).trans ?_
    exact add_le_add h.tFresh le_rfl
  have hsplit : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1 = false] ≤
      Pr{let z ← (simulateQ ro S.run).run' ∅}[bad z.2.1 z.2.2] +
        (Pr{let z ← (simulateQ ro S.run).run' ∅}[badT z.1.2.1 z.1.2.2] +
          Pr{let z ← (simulateQ ro S.run).run' ∅}[
            z.1.1 = false ∧ ¬ bad z.2.1 z.2.2 ∧ ¬ badT z.1.2.1 z.1.2.2]) := by
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _ (fun z : (Bool × (List E × E)) × (List E × E) ↦
      bad z.2.1 z.2.2)).trans (add_le_add le_rfl ?_)
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _ (fun z : (Bool × (List E × E)) × (List E × E) ↦
      badT z.1.2.1 z.1.2.2)).trans (add_le_add le_rfl (le_of_eq ?_))
    simp only [and_assoc]
  refine hsplit.trans ?_
  calc _ ≤ (6 / 2 ^ 256 + (Nbad : ℝ≥0∞) / 2 ^ 192) + ((εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow) :=
        add_le_add hab (add_le_add ht h.rejectGood)
    _ = (Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow := by
        rw [add_comm (6 / 2 ^ 256 : ℝ≥0∞), add_comm εt]
        ac_rfl

/-- **`UniCompletenessWith` in the random-permutation model, from the staged experiment.** -/
theorem uniCompleteness_of_staged {D : Deployment} {P : UniProver D} {Nbad ct N : ℕ} {εt εpow : ℝ≥0∞}
    (hS : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
      D.HonestRelation rows input q →
      ∃ (S : UniStaged) (bad badT : List E → E → Prop), S.Holds D P input rows q bad badT Nbad ct N εt εpow) :
    UniCompletenessWith D P
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow + rpmError N) := by
  intro input rows q hfit hrel
  obtain ⟨S, bad, badT, h⟩ := hS input rows q hfit hrel
  rw [h.experiment, prEvent_map]
  exact prEvent_run_false_le S h

end UniComplete.Prob

/-- info: 'UniComplete.Prob.uniCompleteness_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Prob.uniCompleteness_of_staged
