-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's analogue of `ProbGrind.lean`
-- (`runAt_stagedU`, `one_le_powPot_of_rejectedU`, `rejectGood_uni`), itself following
-- `formal/EndToEnd/Completeness/E2ECompleteness/Grinding.lean`. Uses `ProbGrind.lean`'s `winState` and
-- `one_le_powPot_of_opening_none`, and leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the proof-of-work potential `powPot` and its step (`powPot_stepF`,
-- `powPot_append_inl`), the logged random oracle and its potential engine
-- (`prEvent_run_loggedRO_le_of_freshStepBound`, `prEvent_run_randomOracle_eq_loggedRO`), the run at a log's answers
-- (`simulateQ_look_of_mem_support`, `simulateQ_id_of_look`).
import UniComplete.Rec3ProbExp
import UniComplete.ProbGrind

/-!
# π1-rec3's grinding at good bus challenges

**`rejectGood3`**: in the two-call random-oracle model π1-rec3's staged run (`stagedU3`) is rejected while its bus
challenges avoid `BadFp` of the honest trace and its point challenge avoids `BadT` with probability at most
`Q · (1 − 2^-17)^(2^25)`, `Q` its block count, from the named hypotheses `ProverCommutes3`, `VerifierCommutes3`,
`FlockSimCommutes`, `CoreAccepts3`, `CoreFailsOnlyAtPow3` (at every pure `H`, `F`).

The proof is `ProbGrind.lean`'s: the run against the random oracles is the run against the logged random oracle, on
every outcome the pure run at any `(H, F)` extending the final log `ℓ`; the extension `(Ht, Ft)` answers every
permutation input the log lacks by `winState` (which passes every proof of work). At `(Ht, Ft)` the staged run is the
prover and the verifier at `Id` and its bus challenges and `t` stage are the prover's (`runAt_stagedU3`: from
`ProverCommutes3` and `VerifierCommutes3` for the verdict, `FlockSimCommutes` for the stage up to `t`). On an outcome
rejected at good challenges, `CoreAccepts3` says the prover returned no proof, `CoreFailsOnlyAtPow3` that one of its
(three) openings did; then mumbai's potential `powPot` of `ℓ` is at least `1` (`Prob.one_le_powPot_of_opening_none`),
and it rises by at most `(1 − 2^-17)^(2^25)` in expectation per fresh query.

Decisions: `VerifierCommutes3` is a hypothesis here (the main line's `rejectGood_uni` uses the proved
`simulateQ_verifierWithH`); π1-rec3 has three openings instead of five, which changes nothing in the argument (one
failing opening suffices).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open UniStatement
open E2ECompleteness (ro runAt)
open UniComplete.Prob (winState one_le_powPot_of_opening_none FlockSimCommutes BadT)
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Rec3

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

variable (flock : FlockProverH) (D : Deployment)

/-- The good outcomes: neither the bus challenges nor `t` bad. -/
abbrev GoodU3 (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (z : (Bool × (List E × E)) × (List E × E)) : Prop :=
  ¬ BadFp (honestTrace D input rows q) z.2.1 z.2.2 ∧ ¬ BadT D.shape z.1.2.1 z.1.2.2

/-- **The staged run at a pure `(H, F)`**: the experiment at `Id` (π1-rec3's prover and verifier at `H`, `F`), the
prover's point challenge with Flock's point, and its bus challenges. -/
theorem runAt_stagedU3 (hc : ProverCommutes3 flock D) (hv : VerifierCommutes3) (hf : FlockSimCommutes flock)
    (H : Bytes → Digest) (F : KeccakState → KeccakState) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) :
    runAt H F (stagedU3 flock D input rows q).run =
      ((expW3 (m := Id) H F (flock H) D input rows q, proverTChallenge3 H (flock H) D input rows q),
        proverChallenges3 H D input rows q) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · have h := congrArg (fun X ↦ simulateQ (totalImpl H F) X) (expW3_eq_staged flock D input rows q)
    simp only [simulateQ_map, simulateQ_expW3 flock D hc hv] at h
    exact h.symm
  · simp only [runAt, UniStaged3.run, UniStaged3.tail, stagedU3, staged2, simulateQ_bind, simulateQ_pure,
      simulateQ_queryH, simulateQ_setupTreesWithH, simulateQ_proverA3, simulateQ_midU3 flock D hf]
    rfl
  · simp only [runAt, UniStaged3.run, stagedU3, staged2, simulateQ_bind, simulateQ_pure, simulateQ_queryH,
      simulateQ_setupTreesWithH, simulateQ_proverA3]
    rfl

/-- **A run rejected at good challenges puts the potential at one.** -/
theorem one_le_powPot_of_rejectedU3 (hc : ProverCommutes3 flock D) (hv : VerifierCommutes3)
    (hf : FlockSimCommutes flock) (hacc : CoreAccepts3 D flock) (hpow : CoreFailsOnlyAtPow3 D flock)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation rows input q) {ℓ : Log} {z : (Bool × (List E × E)) × (List E × E)}
    (hz : simulateQ (lookImpl ℓ) (stagedU3 flock D input rows q).run = some z)
    (hrej : z.1.1 = false) (hgood : GoodU3 D input rows q z) :
    1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ := by
  let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
  let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD winState
  have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
  have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
  have hrun : runAt Ht Ft (stagedU3 flock D input rows q).run = z := simulateQ_id_of_look ℓ Ht Ft hH hF _ z hz
  rw [runAt_stagedU3 flock D hc hv hf] at hrun
  subst hrun
  obtain ⟨hab, ht⟩ := hgood
  dsimp only at hrej hab ht
  cases hπ : uniProverRec3With (m := Id) Ht Ft (flock Ht) D input rows q with
  | none =>
    obtain ⟨L, tree, stack, claims, hfail⟩ := hpow input rows q hfit hrel Ht Ft hab ht hπ
    exact one_le_powPot_of_opening_none ℓ Ht hfail
  | some π =>
    exfalso
    have hacc' := hacc input rows q hfit hrel Ht Ft π hπ hab ht
    have hexp : expW3 (m := Id) Ht Ft (flock Ht) D input rows q = true := by
      show verdictW3 (m := Id) Ht Ft D (setupTreesWithH (m := Id) Ht Ft D) input
        (uniProverRec3With (m := Id) Ht Ft (flock Ht) D input rows q) = true
      rw [hπ]
      exact hacc'
    rw [hexp] at hrej
    cases hrej

/-- **π1-rec3's grinding at good challenges**: in the two-call random-oracle model the staged run is rejected while
its bus challenges avoid `BadFp` and `t` avoids `BadT` with probability at most `Q · (1 − 2^-17)^(2^25)`, `Q` its
block count. -/
theorem rejectGood3 (hc : ProverCommutes3 flock D) (hv : VerifierCommutes3) (hf : FlockSimCommutes flock)
    (hacc : CoreAccepts3 D flock) (hpow : CoreFailsOnlyAtPow3 D flock) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) {Q : ℕ}
    (hQ : Common.QueryCostAtMost (stagedU3 flock D input rows q).run hashBlocks Q) :
    Pr{let z ← (simulateQ ro (stagedU3 flock D input rows q).run).run' ∅}[
      z.1.1 = false ∧ ¬ BadFp (honestTrace D input rows q) z.2.1 z.2.2 ∧ ¬ BadT D.shape z.1.2.1 z.1.2.2] ≤
      (Q : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
  have hfuel : PcsQuotient.nonceFuel ≤ 2 ^ 64 := by norm_num [PcsQuotient.nonceFuel]
  have hstep : LogFreshStepBound (powPot Whir.queryGrindingBits PcsQuotient.nonceFuel)
      (missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF (by decide) (by decide) hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have e : Pr{let z ← (simulateQ ro (stagedU3 flock D input rows q).run).run' ∅}[
      z.1.1 = false ∧ ¬ BadFp (honestTrace D input rows q) z.2.1 z.2.2 ∧ ¬ BadT D.shape z.1.2.1 z.1.2.2] =
      Pr{let z ← (simulateQ loggedRO (stagedU3 flock D input rows q).run).run []}[
        z.1.1.1 = false ∧ GoodU3 D input rows q z.1] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _
      (fun (z : (Bool × (List E × E)) × (List E × E)) _ ↦ z.1.1 = false ∧ GoodU3 D input rows q z)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ Q
    (E2ECompleteness.isTotalQueryBound_of_queryCostAtMost hQ) []
    (fun (z : (Bool × (List E × E)) × (List E × E)) _ ↦ z.1.1 = false ∧ GoodU3 D input rows q z)
    fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact one_le_powPot_of_rejectedU3 flock D hc hv hf hacc hpow input rows q hfit hrel hlook hev.1 hev.2
  · rw [powPot_nil, zero_add]

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.runAt_stagedU3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.runAt_stagedU3

/-- info: 'UniComplete.Rec3.rejectGood3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.rejectGood3
