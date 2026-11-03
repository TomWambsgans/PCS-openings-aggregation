-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's analogue of `ProbStaged.lean` (`UniStaged`,
-- `UniStaged.Holds`, `uniCompleteness_of_staged`), itself following
-- `formal/EndToEnd/Completeness/E2ECompleteness/End.lean`; uses its `rpm_le_rom` (`Transfer.lean`, mumbai's
-- indifferentiability transfer) and leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls and their random-permutation model, `rpmError`, the duplex discipline
-- `DuplexVm` and the block cost `hashBlocks`.
import UniComplete.Rec3ProbChain
import UniComplete.ProbStaged
import UniStatement.RecSecurity

/-!
# `UniCompletenessRec3`, from the staged two-call experiment

The end statement `UniCompletenessRec3 D P δ` (`formal/UniStatement`, `RecSecurity.lean`) is `UniCompletenessWith`'s
form with π1-rec3's experiment (`uniCompletenessExperimentRec3`: the setup, the prover `P`, π1-rec3's verifier
`Deployment.verifierRec3With`, all over `π`). **What is proved here** (`uniCompletenessRec3_of_staged`): if for every
honest witness the experiment is the verdict of a two-call computation of π1-rec3's bus challenges' shape
(`UniStaged3`, `UniStaged3.Holds`), then

  `δ = Nbad / 2^192 + (ct / 2^192 + εt) + εpow + N² / 2^508`:

* `N² / 2^508` (`rpmError N`): the random permutation is two random oracles to an honest computation of at most `N`
  block calls following the duplex discipline (`E2ECompleteness.rpm_le_rom`);
* `Nbad / 2^192`: the bus challenges `(α, β)` are bad (`bad`, at most `Nbad` values of `β` for each `α`) with at
  most that probability (`prEvent_staged2_le`: two chained answers, the second's `32`-byte query always fresh, so no
  repetition term, unlike the main line's `6 / 2^256`);
* `ct / 2^192 + εt`: the point challenge `t` is bad (`badT`, at most `ct` values for each prior, Flock's point) with
  at most that probability (`Prob.prEvent_tquery_le`), `εt` the probability that `t`'s input was hashed before its
  query (`Holds.tFresh`);
* `εpow`: in the two-call random-oracle model the honest proof is rejected at good challenges with probability at
  most `εpow` (`Holds.rejectGood`, the grinding).

Decisions: as `ProbStaged.lean` (no coins, the experiment an equality; the bad sets parameters of `Holds`; the first
chain input `88` bytes); `α` is `alphaOf3 s₁ = squares (chal s₁) 4`, π1-rec3's draw (`drawRunW … 4`,
`drawRunH .rec3 4`), so the staged run's bus challenges are the prover's `proverChallenges3`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement
open E2ECompleteness (ro HashOK)
open UniComplete.Prob (GoodL prEvent_tquery_le)
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Rec3

/-- **π1-rec3's `α`** from the first bus answer: `squares (chal s₁) 4 = (c, c², c⁴, c⁸)`. -/
def alphaOf3 (s : Digest) : List E := squares (PcsQuotient.Transcript.challengeOf s) 4

/-- **The experiment's stages** (no coins): `A` up to the first bus-challenge input (`inp`, `88` bytes), the two
chained answers, `B` up to `t`'s input (`tin`; `pr` the prior `t`'s bad set depends on, Flock's point), `t`'s answer,
`C` the rest (the prover's tail and the verifier), its output the verdict. -/
structure UniStaged3 where
  α : Type
  β : Type
  inp : α → Bytes
  A : OracleComp KeccakCalls α
  B : α → Digest → Digest → OracleComp KeccakCalls β
  tin : β → Bytes
  pr : β → List E
  C : β → Digest → OracleComp KeccakCalls Bool

/-- After the bus challenges: `B`, `t`'s query, `C`; the verdict and `(pr b, t)`. -/
def UniStaged3.tail (S : UniStaged3) (a : S.α) (s₁ s₂ : Digest) :
    OracleComp KeccakCalls (Bool × (List E × E)) := do
  let b ← S.B a s₁ s₂
  let st ← callKeccak256 (S.tin b)
  let z ← S.C b st
  return (z, (S.pr b, PcsQuotient.Transcript.challengeOf st))

/-- The two-call run: the verdict with `t`'s stage, and the bus challenges `(α, β)`. -/
def UniStaged3.run (S : UniStaged3) : OracleComp KeccakCalls ((Bool × (List E × E)) × (List E × E)) :=
  staged2 PcsQuotient.Transcript.challengeOf alphaOf3 S.inp S.A S.tail

/-- **The run up to `t`'s query**: `B`'s output and the bus challenges. -/
def UniStaged3.pre (S : UniStaged3) : OracleComp KeccakCalls (S.β × (List E × E)) := do
  let a ← S.A
  let s₁ ← callKeccak256 (S.inp a)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let b ← S.B a s₁ s₂
  return (b, (alphaOf3 s₁, PcsQuotient.Transcript.challengeOf s₂))

/-- **The run, cut at `t`.** -/
theorem UniStaged3.run_eq_pre (S : UniStaged3) :
    S.run = S.pre >>= fun x ↦ callKeccak256 (S.tin x.1) >>= fun st ↦ S.C x.1 st >>= fun z ↦
      pure ((z, (S.pr x.1, PcsQuotient.Transcript.challengeOf st)), x.2) := by
  simp only [UniStaged3.run, staged2, UniStaged3.tail, UniStaged3.pre, bind_assoc, pure_bind]

/-- **The code-level bridge** of π1-rec3's experiment for `(input, rows, q)`: bad sets `bad` (bus challenges, at most
`Nbad` values of `β` per `α`) and `badT` (`t`, at most `ct` values per prior), `N` block calls, `t`'s cache-hit
probability `εt` and a proof-of-work error `εpow`. -/
structure UniStaged3.Holds (S : UniStaged3) (D : Deployment) (P : UniProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (bad badT : List E → E → Prop) (Nbad ct N : ℕ) (εt εpow : ℝ≥0∞) :
    Prop where
  /-- The experiment is the verdict of the two-call run against the random permutation. -/
  experiment : uniCompletenessExperimentRec3 D P input rows q =
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

/-- **One witness**: the run is rejected with probability at most the bus challenges' `Nbad / 2^192`, `t`'s
`ct / 2^192 + εt`, `εpow` and the transfer's `rpmError N`. -/
theorem prEvent_run_false_le3 (S : UniStaged3) {D : Deployment} {P : UniProver D} {input : Vector UInt8 32}
    {rows : List ℕ} {q : D.Stack rows} {bad badT : List E → E → Prop} {Nbad ct N : ℕ} {εt εpow : ℝ≥0∞}
    (h : S.Holds D P input rows q bad badT Nbad ct N εt εpow) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1 = false] ≤
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow) + rpmError N := by
  refine E2ECompleteness.rpm_le_rom S.run h.duplex h.cost (fun z ↦ z.1.1 = false) ?_
  -- The bus challenges.
  have hab : Pr{let z ← (simulateQ ro S.run).run' ∅}[bad z.2.1 z.2.2] ≤ (Nbad : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_staged2_le _ E2ECompleteness.challengeOf_regular alphaOf3 (by norm_num) bad Nbad h.badCard
      S.inp h.inp_length S.A S.tail h.hashA ∅ fun m hm ↦ absurd rfl hm
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
  calc _ ≤ (Nbad : ℝ≥0∞) / 2 ^ 192 + ((εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow) :=
        add_le_add hab (add_le_add ht h.rejectGood)
    _ = (Nbad : ℝ≥0∞) / 2 ^ 192 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow := by
        rw [add_comm εt]
        ac_rfl

/-- **`UniCompletenessRec3` in the random-permutation model, from the staged experiment.** -/
theorem uniCompletenessRec3_of_staged {D : Deployment} {P : UniProver D} {Nbad ct N : ℕ} {εt εpow : ℝ≥0∞}
    (hS : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
      D.HonestRelation rows input q →
      ∃ (S : UniStaged3) (bad badT : List E → E → Prop), S.Holds D P input rows q bad badT Nbad ct N εt εpow) :
    UniCompletenessRec3 D P
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow + rpmError N) := by
  intro input rows q hfit hrel
  obtain ⟨S, bad, badT, h⟩ := hS input rows q hfit hrel
  rw [h.experiment, prEvent_map]
  exact prEvent_run_false_le3 S h

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.uniCompletenessRec3_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.uniCompletenessRec3_of_staged
