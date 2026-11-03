-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/EndToEnd/Completeness/E2ECompleteness/Grinding.lean` (`rejectGood_of_tail`, `one_le_powPot_of_rejected`,
-- `one_le_powPot_of_findNonceM`, `proveOpeningWithH_eq_some_none`) for the univariate run. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the proof-of-work
-- potential `powPot` and its step (`powPot_stepF`, `powPot_append_inl`, `Compile/Rom/Complete.lean`), the logged random
-- oracle and its potential engine (`ToVCVio/Rom/LoggedOracle.lean`, `prEvent_run_loggedRO_le_of_freshStepBound`,
-- `prEvent_run_randomOracle_eq_loggedRO`), the run at a log's answers (`simulateQ_look_of_mem_support`,
-- `simulateQ_id_of_look`), the proof-of-work search (`findNonceM_eq_some_none`, `powStepM_option`).
import UniComplete.ProbExp
import E2ECompleteness.Grinding

/-!
# The grinding at good bus challenges

**`rejectGood_uni`**: in the two-call random-oracle model the staged univariate run (`stagedU`) is rejected while its
bus challenges avoid `BadFp` of the honest trace and its point challenge avoids `BadT` with probability at most
`Q · (1 − 2^-17)^(2^25)`, `Q` its block count, from the named hypotheses `ProverCommutes`, `FlockCommutes`,
`CoreAccepts`, `CoreFailsOnlyAtPow` (at every pure `H`, `F`).

## The proof (`E2ECompleteness.Grinding`'s)

The run against the random oracles is the run against the logged random oracle; on every outcome it is the run at
the final log `ℓ`, so the pure run at any `(H, F)` extending `ℓ` (`simulateQ_id_of_look`). Here the extension
answers every permutation input the log lacks by **a state that passes every proof of work** (`winState`, the zero
state: its challenge's low bits are zero, `powOk_winState`), Keccak-256 by `default`. At that `(Ht, Ft)` the staged
run is the prover and the verifier at `Id` and its bus challenges are the prover's (`runAt_stagedU`, from
`ProverCommutes`). On an outcome rejected at good challenges, `CoreAccepts` says the prover returned no proof,
`CoreFailsOnlyAtPow` that one of its openings did; at `Option` that opening fails at a `17`-bit search
(`E2ECompleteness.proveOpeningWithH_eq_some_none`, through `simulateQ_someImpl`) at a sponge the prover keeps
(`ProverSp`). Every nonce below `2^25` fails there at `Ft`, so its permutation input is in the log (else `Ft` answers
`winState`, which passes) with a failing answer: mumbai's potential `powPot` of `ℓ` is at least `1`
(`one_le_powPot_of_findNonce_ext`). The potential starts at `0` and a fresh query raises it by at most
`(1 − 2^-17)^(2^25)` in expectation.

Decisions: the extension's choice (`winState`) replaces the template's reading of the failed search in the log, so
`CoreFailsOnlyAtPow` can be stated at pure functions, as the PIOP proves it; `ProverSp` is recovered here, at `Option`,
from the opening prover's code, not asked of the hypothesis.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open LeanVM.Prover (Tree findNonceM powStepM)
open UniStatement
open E2ECompleteness (ro runAt)
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Prob

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## A state that passes every proof of work -/

/-- **The zero state**: its challenge's first limb is zero, so it passes every proof of work. -/
def winState : KeccakState := Vector.replicate 25 0

theorem winState_lane : ((Compile.challengeOf winState).limb 0).lane = 0 := by
  decide

theorem powOk_winState {bits : ℕ} (hb : bits ≠ 0) (n : E) : powOk bits n (Compile.challengeOf winState) = true := by
  simp only [powOk, hb, ↓reduceIte, winState_lane, decide_eq_true_eq]
  simp

/-! ## The pure run in `Option` -/

/-- A hash function and a permutation, answered in `Option` (always `some`). -/
def someImpl (H : Bytes → Digest) (F : KeccakState → KeccakState) : QueryImpl KeccakCalls Option :=
  fun t ↦ some (totalImpl H F t)

/-- **The run in `Option` of total functions is `some` of the pure run.** -/
theorem simulateQ_someImpl {α : Type} (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (X : OracleComp KeccakCalls α) : simulateQ (someImpl H F) X = some (simulateQ (totalImpl H F) X) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; rfl
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, OracleQuery.cont_query]
    exact ih (totalImpl H F t)

/-- **An opening that fails at a pure `(H, F)` fails at `Option`.** -/
theorem proveOpeningWithH_some_none {H : Bytes → Digest} {F : KeccakState → KeccakState} {fuel : ℕ}
    {L : PcsQuotient.Layout} {tree : Tree} {stack : Array K} {claims : List PcsQuotient.Claim}
    (h : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel L tree stack claims = none) :
    E2ECompleteness.proveOpeningWithH (m := Option) (fun x ↦ some (H x)) (fun s ↦ some (F s)) fuel L tree stack
      claims = some none := by
  have e1 := E2ECompleteness.simulateQ_proveOpeningWithH (someImpl H F) fuel L tree stack claims
  have e2 := E2ECompleteness.simulateQ_proveOpeningWithH (totalImpl H F) fuel L tree stack claims
  rw [simulateQ_someImpl, e2] at e1
  rw [← h]
  exact e1.symm

/-! ## A failed search puts the potential at one -/

/-- **A search failing at the extension `Ft` of the log** (every input the log lacks answered by `winState`) puts the
potential at least at `1`: every nonce's permutation input is in the log, with a failing answer. -/
theorem one_le_powPot_of_findNonce_ext {ℓ : Log} {bits fuel : ℕ} (hb : bits ≠ 0) (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0) {sp : Sponge} (hsp : ProverSp sp)
    (hf : findNonceM (fun s ↦ some ((lookF ℓ s).getD winState)) bits sp fuel = some none) :
    1 ≤ powPot bits fuel ℓ := by
  obtain ⟨-, hall⟩ := findNonceM_eq_some_none hf
  -- A failing nonce's input is in the log.
  have hlog : ∀ {c ps n u}, (fun s ↦ some ((lookF ℓ s).getD winState)) (nonceInput c ps n) = some u →
      powOk bits (nonceOf n) (challengeOf u) = false → lookF ℓ (nonceInput c ps n) = some u := by
    intro c ps n u hu hp
    simp only [Option.some.injEq] at hu
    cases hl : lookF ℓ (nonceInput c ps n) with
    | none =>
      rw [hl, Option.getD_none] at hu
      subst hu
      rw [powOk_winState hb] at hp
      cases hp
    | some v =>
      rw [hl, Option.getD_some] at hu
      rw [hu]
  -- The position of the search, the same for every nonce.
  obtain ⟨κ, hκ, hnon⟩ : ∃ κ : PowKey, KeyOk κ ∧ ∀ n < fuel, ∃ u,
      lookF ℓ (nonceInput κ.1 κ.2 n) = some u ∧ powOk bits (nonceOf n) (challengeOf u) = false := by
    by_cases h4 : sp.pending.length = 4
    · obtain ⟨r0, hr0, -⟩ := hall 0 (Nat.pos_of_ne_zero hfuel0)
      obtain ⟨c0, ps0, u0, -, -, hif⟩ := powStepM_option hr0
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨-, v, hv, -⟩ := hif
      refine ⟨(capOf v, []), ⟨by simp, by simp⟩, fun n hn ↦ ?_⟩
      obtain ⟨r, hr, hp⟩ := hall n hn
      obtain ⟨c, ps, u, hu, hru, hif⟩ := powStepM_option hr
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨rfl, v', hv', rfl⟩ := hif
      rw [hv] at hv'
      cases hv'
      rw [hru] at hp
      exact ⟨u, hlog hu hp, hp⟩
    · refine ⟨(capOf sp.state, sp.pending), ⟨by dsimp only; have := hsp.1; omega, hsp.2⟩,
        fun n hn ↦ ?_⟩
      obtain ⟨r, hr, hp⟩ := hall n hn
      obtain ⟨c, ps, u, hu, hru, hif⟩ := powStepM_option hr
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨rfl, rfl⟩ := hif
      rw [hru] at hp
      exact ⟨u, hlog hu hp, hp⟩
  -- Its term is `1`.
  have hS : ¬ Solved bits fuel ℓ κ := by
    rintro ⟨n, hn, d, hd, hp⟩
    obtain ⟨d', hd', hp'⟩ := hnon n hn
    rw [hd'] at hd
    cases hd
    rw [hp'] at hp
    cases hp
  have hT : (tried fuel ℓ κ).card = fuel := by
    have : tried fuel ℓ κ = Finset.range fuel := by
      refine Finset.filter_true_of_mem fun n hn ↦ ?_
      obtain ⟨d, hd, -⟩ := hnon n (Finset.mem_range.mp hn)
      simp [hd]
    rw [this, Finset.card_range]
  have hterm : powTerm bits fuel ℓ κ = 1 := by
    simp [powTerm, hS, hT]
  have hmem : κ ∈ keys fuel ℓ := by
    obtain ⟨u, hu, -⟩ := hnon 0 (Nat.pos_of_ne_zero hfuel0)
    obtain ⟨i, hi, hei, -⟩ := (lookF_eq_some_iff ℓ _ u).mp hu
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, mem_fIns_of_getElem hi hei,
      keyOf_nonceInput hfuel hκ (Nat.pos_of_ne_zero hfuel0)⟩)
  rw [← hterm]
  exact Finset.single_le_sum (fun _ _ ↦ bot_le) hmem

/-- **An opening failing at the log's extension** puts the potential at least at `1`. -/
theorem one_le_powPot_of_opening_none (ℓ : Log) (Ht : Bytes → Digest) {L : PcsQuotient.Layout} {tree : Tree}
    {stack : Array K} {claims : List PcsQuotient.Claim}
    (h : E2ECompleteness.proveOpeningWithH (m := Id) Ht (fun s ↦ (lookF ℓ s).getD winState)
      PcsQuotient.nonceFuel L tree stack claims = none) :
    1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ := by
  obtain ⟨sp, hsp, hf⟩ := E2ECompleteness.proveOpeningWithH_eq_some_none (proveOpeningWithH_some_none h)
  exact one_le_powPot_of_findNonce_ext (by decide) (by norm_num [PcsQuotient.nonceFuel])
    (by norm_num [PcsQuotient.nonceFuel]) hsp hf

/-! ## The staged run at a hash function and a permutation -/

variable (flock : PolyFlock) (D : Deployment)

/-- The good outcomes: neither the bus challenges nor `t` bad. -/
abbrev GoodU (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (z : (Bool × (List E × E)) × (List E × E)) : Prop :=
  ¬ BadFp (honestTrace D input rows q) z.2.1 z.2.2 ∧ ¬ BadT D.shape z.1.2.1 z.1.2.2

/-- **The staged run at a pure `(H, F)`**: the experiment at `Id` (the prover and the verifier at `H`, `F`), the
prover's point challenge with Flock's point, and its bus challenges. -/
theorem runAt_stagedU (hc : ProverCommutes flock D) (hf : FlockCommutes flock) (H : Bytes → Digest)
    (F : KeccakState → KeccakState) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    runAt H F (stagedU flock D input rows q).run =
      ((expW (m := Id) H F (flock H) D input rows q, proverTChallenge H (flock H) D input rows q),
        proverChallenges H D input rows q) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · have h := congrArg (fun X ↦ simulateQ (totalImpl H F) X) (expW_eq_staged flock D input rows q)
    simp only [simulateQ_map, simulateQ_expW flock D hc] at h
    exact h.symm
  · simp only [runAt, UniStaged.run, UniStaged.tail, stagedU, staged5, simulateQ_bind, simulateQ_pure,
      simulateQ_queryH, simulateQ_setupTreesWithH, simulateQ_proverA, simulateQ_midU flock D hf]
    rfl
  · simp only [runAt, UniStaged.run, stagedU, staged5, simulateQ_bind, simulateQ_pure, simulateQ_queryH,
      simulateQ_setupTreesWithH, simulateQ_proverA]
    rfl

/-- **A run rejected at good challenges puts the potential at one.** -/
theorem one_le_powPot_of_rejectedU (hc : ProverCommutes flock D) (hf : FlockCommutes flock)
    (hacc : CoreAccepts D flock) (hpow : CoreFailsOnlyAtPow D flock) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) {ℓ : Log}
    {z : (Bool × (List E × E)) × (List E × E)}
    (hz : simulateQ (lookImpl ℓ) (stagedU flock D input rows q).run = some z)
    (hrej : z.1.1 = false) (hgood : GoodU D input rows q z) :
    1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ := by
  let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
  let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD winState
  have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
  have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
  have hrun : runAt Ht Ft (stagedU flock D input rows q).run = z := simulateQ_id_of_look ℓ Ht Ft hH hF _ z hz
  rw [runAt_stagedU flock D hc hf] at hrun
  subst hrun
  obtain ⟨hab, ht⟩ := hgood
  dsimp only at hrej hab ht
  cases hπ : uniProverWith (m := Id) Ht Ft (flock Ht) D input rows q with
  | none =>
    obtain ⟨L, tree, stack, claims, hfail⟩ := hpow input rows q hfit hrel Ht Ft hab ht hπ
    exact one_le_powPot_of_opening_none ℓ Ht hfail
  | some π =>
    exfalso
    have hv := hacc input rows q hfit hrel Ht Ft π hπ hab ht
    have hexp : expW (m := Id) Ht Ft (flock Ht) D input rows q = true := by
      show verdictW (m := Id) Ht Ft D (setupTreesWithH (m := Id) Ht Ft D) input
        (uniProverWith (m := Id) Ht Ft (flock Ht) D input rows q) = true
      rw [hπ]
      exact hv
    rw [hexp] at hrej
    cases hrej

/-! ## The bound -/

/-- **The grinding at good challenges**: in the two-call random-oracle model the staged run is rejected while its bus
challenges avoid `BadFp` and `t` avoids `BadT` with probability at most `Q · (1 − 2^-17)^(2^25)`, `Q` its block
count. -/
theorem rejectGood_uni (hc : ProverCommutes flock D) (hf : FlockCommutes flock) (hacc : CoreAccepts D flock)
    (hpow : CoreFailsOnlyAtPow D flock) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) {Q : ℕ}
    (hQ : Common.QueryCostAtMost (stagedU flock D input rows q).run hashBlocks Q) :
    Pr{let z ← (simulateQ ro (stagedU flock D input rows q).run).run' ∅}[
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
  have e : Pr{let z ← (simulateQ ro (stagedU flock D input rows q).run).run' ∅}[
      z.1.1 = false ∧ ¬ BadFp (honestTrace D input rows q) z.2.1 z.2.2 ∧ ¬ BadT D.shape z.1.2.1 z.1.2.2] =
      Pr{let z ← (simulateQ loggedRO (stagedU flock D input rows q).run).run []}[
        z.1.1.1 = false ∧ GoodU D input rows q z.1] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _
      (fun (z : (Bool × (List E × E)) × (List E × E)) _ ↦ z.1.1 = false ∧ GoodU D input rows q z)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ Q
    (E2ECompleteness.isTotalQueryBound_of_queryCostAtMost hQ) []
    (fun (z : (Bool × (List E × E)) × (List E × E)) _ ↦ z.1.1 = false ∧ GoodU D input rows q z)
    fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact one_le_powPot_of_rejectedU flock D hc hf hacc hpow input rows q hfit hrel hlook hev.1 hev.2
  · rw [powPot_nil, zero_add]

end UniComplete.Prob
