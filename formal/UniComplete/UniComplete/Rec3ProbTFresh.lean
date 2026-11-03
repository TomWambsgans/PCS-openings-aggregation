-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's analogue of `ProbTFresh.lean`
-- (`tQueryFresh_flockProve`, `tQueryFresh_reference`), reusing its chain calculus (`Prob.TFresh`: `ChainF`, `EndsT`,
-- `WCh`, `WEnd`, `prHit_le`, the writer's and Flock's steps), itself following
-- `formal/EndToEnd/Completeness/E2ECompleteness/Chain.lean`; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls`, their lazy random oracles, the
-- weight calculus `Common.QueryCostAtMost`.
import UniComplete.Rec3Prob
import UniComplete.ProbTFresh

/-!
# `t`'s query is fresh for π1-rec3 (`TQueryFresh3`), for π1-rec3's Flock prover

`TQueryFresh3 flock D εt` (`Rec3ProbExp.lean`): in the two-call random-oracle model, the input of the query that draws
`t` (`tInput` of the writer after `C2`'s root) is already cached when it is asked with probability at most `εt`.
Proved here for π1-rec3's honest Flock prover `flockProve3H`:

* **`tQueryFresh3_flockProve3`**: for every deployment, `εt = tFreshBound3 D = (n + 1) · M / 2^256`,
  `n = tSteps3 D` the challenges after the first bus challenge (`β`, `γ`, Flock's), `M = tCache3 D` (the main line's
  stage A count `stageACost`, the chain's, `C2`'s tree's `c2Cost`, one);
* **`tQueryFresh3_reference`**: at the reference shape, `εt = 2^-200` (`n = 48`, `M ≤ 2^28`: `49 · 2^28 / 2^256 <
  2^-200`);
* **`uniCompletenessRec3_reference_flockProve3`**: `uniCompletenessRec3_reference` at `flockProve3H` with
  `TQueryFresh3` discharged.

**The chain still holds at π1-rec3.** The argument is `ProbTFresh.lean`'s (a chain of challenges, each hashing the
previous answer's `32` bytes first; `C2`'s tree between Flock's last `32`-byte challenge and `t`): what changes is the
chain's content, not its shape.

* The bus challenges: after the first (`88` bytes, fresh by its length, `hashA_stagedU3`) only **one** more (`β`,
  `s₂ = H(s₁)`, `preTail3`), instead of four;
* Flock's prover (`flockProve3`): its zerocheck's eq coordinates after the seven fixed ones are `squares c'` of **one**
  drawn challenge (`drawRunW`, at most one step, `wch_drawRunW`) instead of `log_n − k − 7`; the skip's `z`, the
  rounds, `α`, the lincheck's rounds, the slices sent and the ring map's six challenges are the main line's
  (`FlockP.skipW`, `zcRounds`, `lcRounds`, `sendSlices`, `endW`): it is a chain ending with a `32`-byte challenge
  (the ring map's last, `wend_flockProve3`), with `flockSteps3 = 2 + (7 + (log_n − k − 7)) + 1 + 8 + 6` challenges.

So `n = 1 + 1 + flockSteps3 = 48` at the reference shape (main line: `72`).

Decisions: the chains reuse `Prob.TFresh` as they are (`ChainF`, `WCh`, `WEnd`, `prHit_le`, `run_midB`,
`hashOK_commitReal`, `stageACost`, `c2Cost`); only π1-rec3's steps (`zcSteps3`, `frontSteps3`, `flockSteps3`,
`tSteps3`) and π1-rec3's staged run (`preTail3`) are new. Flock's prover is used only through its code
(`FlockCommutes` is not used here).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement
open E2ECompleteness (ro Cache HashOK cache_of_hashOK simulateQ_callKeccak256)
open UniComplete.Prob (firstInput_length ProverA)
open UniComplete.Prob.TFresh
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Rec3

namespace TFresh3

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## π1-rec3's draw and Flock's prover are chains -/

/-- `squares x n` has `n` terms. -/
theorem length_squares : ∀ (x : E) (n : ℕ), (squares x n).length = n
  | _, 0 => rfl
  | x, n + 1 => by rw [squares, List.length_cons, length_squares (x * x) n]

/-- **A run of squares** (`drawRunW`): at most one challenge, `count` values. -/
theorem wch_drawRunW (count : ℕ) :
    WCh (drawRunW callKeccak256 count) 1 1 (fun _ ↦ True) (fun xs _ ↦ xs.length = count) := by
  unfold drawRunW
  split_ifs with h
  · exact wch_ret _ fun _ _ ↦ by simp [h]
  · refine wch_seq wch_sampleW (fun c ↦ ?_) le_rfl le_rfl
    exact wch_ret _ fun _ _ ↦ length_squares c count

/-- π1-rec3's zerocheck's challenges: the drawn one (at most), the skip's `z`, one per round. -/
def zcSteps3 (logN k : ℕ) : ℕ := 1 + 1 + (Flock.nFixed + (logN - k - Flock.nFixed))

/-- The front's: the zerocheck's, `α`, the lincheck's. -/
def frontSteps3 (logN k : ℕ) : ℕ := zcSteps3 logN k + 1 + Flock.lincheckRounds

/-- Flock's at π1-rec3: the front's, the ring map's six. -/
def flockSteps3 (logN k : ℕ) : ℕ := frontSteps3 logN k + 6

theorem wch_zerocheckW3 (logN k : ℕ) (wit : FlockP.Wit) :
    WCh (zerocheckW3 callKeccak256 logN k wit) (zcSteps3 logN k) (zcSteps3 logN k) (fun _ ↦ True)
      (fun _ _ ↦ True) := by
  unfold zerocheckW3
  refine wch_seq (wch_drawRunW _) (fun sampled ↦ WCh.const_pre fun hw ↦ ?_) (by unfold zcSteps3; omega)
    (by unfold zcSteps3; omega)
  have hlen : (Flock.fixedChallenges ++ sampled).length = Flock.nFixed + (logN - k - Flock.nFixed) := by
    rw [List.length_append, hw]
    rfl
  refine wch_seq (wch_skipW _ _ _) (fun st ↦ ?_) (by unfold zcSteps3; omega) (by unfold zcSteps3; omega)
  refine wch_seq (wch_zcRounds _ _ _ _ _) (fun zc ↦ ?_) (by rw [hlen]; unfold zcSteps3; omega)
    (by rw [hlen]; unfold zcSteps3; omega)
  refine wch_seq (wch_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  refine wch_seq (wch_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  exact wch_ret _ fun _ _ ↦ trivial

theorem wch_frontW3 (logN : ℕ) (variant : Flock.Variant) (q : Array K) (hv : variant.slices ≠ .claim) :
    WCh (frontW3 callKeccak256 logN variant q) (frontSteps3 logN variant.skip)
      (frontSteps3 logN variant.skip) (fun _ ↦ True) (fun frs _ ↦ ∃ s, frs.1.slices = some s) := by
  unfold frontW3
  refine wch_seq (wch_zerocheckW3 _ _ _) (fun zc ↦ ?_) (by unfold frontSteps3; omega)
    (by unfold frontSteps3; omega)
  refine wch_seq wch_sampleW (fun alpha ↦ ?_) (by unfold frontSteps3; omega) (by unfold frontSteps3; omega)
  refine wch_seq (wch_lcRounds _ _ _ _).weaken (fun lc ↦ ?_) (by unfold frontSteps3; omega)
    (by unfold frontSteps3; omega)
  refine wch_seq (wch_sendSlices _ _ hv).weaken (fun slices ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  exact wch_ret _ fun _ hw ↦ ⟨_, hw⟩

/-- **π1-rec3's Flock prover is a chain of `flockSteps3` challenges ending with a `32`-byte one** (the ring map's
last), at every variant whose slices are sent. -/
theorem wend_flockProve3 (logN : ℕ) (variant : Flock.Variant) (q : Array K) (hv : variant.slices ≠ .claim) :
    WEnd (flockProve3 callKeccak256 logN variant q) (flockSteps3 logN variant.skip)
      (flockSteps3 logN variant.skip) (fun _ ↦ True) (fun _ _ ↦ True) := by
  simp only [flockProve3]
  refine wend_seq (wch_frontW3 logN variant q hv) (fun frs ↦ WEnd.const_pre fun h ↦ ?_)
    (by unfold flockSteps3; omega) (by unfold flockSteps3; omega)
  obtain ⟨s, hs⟩ := h
  rw [hs]
  simp only [FlockP.endW, FlockP.ringEndW, bind_assoc, pure_bind]
  rw [show Flock.ringMapShifts.length = 4 + 1 + 1 from rfl]
  exact (wend_map _ (wend_samplesW2 4)).mono (by unfold flockSteps3; omega) (by unfold flockSteps3; omega)
    fun _ _ _ ↦ trivial

/-! ## The staged run -/

/-- Flock's challenges at the deployment (`flockMain`). -/
def flockStepsD3 (D : Deployment) : ℕ := flockSteps3 (Cost.flockLogN D.shape) flockMain.skip

/-- **The challenges after the first bus challenge**: `β`, `γ`, Flock's. -/
def tSteps3 (D : Deployment) : ℕ := flockStepsD3 D + 2

/-- **The hashed inputs before `t`**, at most (and one). -/
def tCache3 (D : Deployment) : ℕ := stageACost D + (tSteps3 D + c2Cost D) + 1

/-- **`t`'s cache-hit bound**: `(tSteps3 + 1) · tCache3 / 2^256`. -/
noncomputable def tFreshBound3 (D : Deployment) : ℝ≥0∞ :=
  ((tSteps3 D + 1 : ℕ) : ℝ≥0∞) * ((tCache3 D : ℝ≥0∞) / 2 ^ 256)

/-- **Stage A hashes at most `stageACost` inputs** (π1-rec3's IV is one query, as the main line's). -/
theorem hc_stageA3 (flock : FlockProverH) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : HC (stagedU3 flock D input rows q).A (stageACost D) := by
  have hcm : ∀ (μ : ℕ) (stack : Array K),
      HC (E2ECompleteness.commitWithH callKeccak256 μ stack) (5 * 2 ^ (μ - 6 + 1)) :=
    fun μ stack ↦ hc_of_qc (E2ECompleteness.Cost.qc_commitWithH μ stack)
  simp only [stagedU3, proverA3, setupTreesOf, setupTreesWithH, contractIvRec3Of, seedOf, bind_assoc, pure_bind]
  refine Common.QueryCostAtMost.mono (Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦ Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦ Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦ Common.QueryCostAtMost.bind (hc_H _) fun _ ↦
    Common.QueryCostAtMost.bind (hc_H _) fun _ ↦ Common.QueryCostAtMost.bind (b := 0) (hcm _ _) fun _ ↦
    trivial) ?_
  simp only [stageACost, Cost.setupCost, E2ECompleteness.Cost.treeCost, honestTrace_shape]
  omega

/-- **π1-rec3's staged run after the first bus challenge**: `s₂`, then `B` (`γ`, Flock, `C2`). -/
def preTail3 (S : UniStaged3) (a : S.α) (s₁ : Digest) : OracleComp KeccakCalls (S.β × (List E × E)) := do
  let s₂ ← callKeccak256 (digestBytes s₁)
  let b ← S.B a s₁ s₂
  return (b, (alphaOf3 s₁, PcsQuotient.Transcript.challengeOf s₂))

theorem pre_eq3 (S : UniStaged3) : S.pre = S.A >>= fun a ↦ callKeccak256 (S.inp a) >>= preTail3 S a := rfl

/-- **π1-rec3's staged run after the first bus challenge is a chain** of `tSteps3` challenges and
`tSteps3 + c2Cost` hashed inputs, its final state the writer's before `t`. -/
theorem chainF_preTail3 (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (a : SetupTrees × ProverA) (s₁ : Digest) :
    ChainF (fun (z : MidU3 × (List E × E)) s ↦ z.1.mw.2.state = s) (tSteps3 D) (tSteps3 D + c2Cost D) s₁
      (preTail3 (stagedU3 flockProve3H D input rows q) a s₁) := by
  unfold preTail3
  refine .step (n := flockStepsD3 D + 1) (N := flockStepsD3 D + c2Cost D + 1) _ _ (take_digestBytes' s₁)
    (by unfold tSteps3; omega) (by unfold tSteps3; omega) fun s₂ ↦ ?_
  simp only [stagedU3, midU3, bind_assoc, pure_bind]
  rw [run_midB]
  simp only [bind_assoc, pure_bind]
  have h1 := wch_sampleW (pre := fun _ ↦ True) (writerAfter3 rows a.2.c1 s₁ s₂) trivial
  refine ChainF.mono (n := 1 + flockStepsD3 D) (N := 1 + (flockStepsD3 D + c2Cost D))
    (n' := flockStepsD3 D + 1) (N' := flockStepsD3 D + c2Cost D + 1)
    (ChainF.bind (n₂ := flockStepsD3 D) (N₂ := flockStepsD3 D + c2Cost D) (fun p s hp ↦ ?_) h1) (by omega)
    (by omega)
  obtain ⟨hs, -⟩ := hp
  subst hs
  have h := wend_flockProve3 (Cost.flockLogN D.shape) flockMain (honestTrace D input rows q).qflock (by decide)
    p.2 trivial
  refine ChainF.mono (n := flockSteps3 (Cost.flockLogN D.shape) flockMain.skip + 0)
    (N := flockSteps3 (Cost.flockLogN D.shape) flockMain.skip + c2Cost D + 0)
    (n' := flockStepsD3 D) (N' := flockStepsD3 D + c2Cost D)
    (h _ _ _ (c2Cost D) _ _ 0 0 (hashOK_commitReal _ _ _) (hc_of_qc (Cost.qc_commitReal _ _ _)) ?_)
    (by unfold flockStepsD3; omega) (by unfold flockStepsD3; omega)
  intro b s' d hb
  exact .ret _ hb.1

end TFresh3

open TFresh3

/-- **`t`'s query is fresh for π1-rec3's Flock prover**, at every deployment: its input is cached when asked with
probability at most `tFreshBound3 D = (tSteps3 D + 1) · tCache3 D / 2^256`. -/
theorem tQueryFresh3_flockProve3 (D : Deployment) : TQueryFresh3 flockProve3H D (tFreshBound3 D) := by
  intro input rows q hfit _
  have hmono := prEvent_mono ((simulateQ ro (stagedU3 flockProve3H D input rows q).pre).run ∅)
    (fun p ↦ p.2 (.inl ((stagedU3 flockProve3H D input rows q).tin p.1.1)) ≠ none)
    (fun (p : (MidU3 × (List E × E)) × Cache) ↦ Hit p.2 p.1.1.mw.2.state)
    (fun p hp ↦ ⟨_, hp, take_digestBytes _ _⟩)
  refine hmono.trans ?_
  rw [pre_eq3, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind]
  have hc : CacheBound p.2 (stageACost D) :=
    (cacheBound_run (hc_stageA3 flockProve3H D input rows q) cacheBound_empty hp).mono (by omega)
  have hx : p.2 (.inl ((stagedU3 flockProve3H D input rows q).inp p.1)) = none := by
    by_contra h
    rcases cache_of_hashOK (hashA_stagedU3 flockProve3H D input rows q) ∅ hp _ h with h' | h'
    · exact h' rfl
    · exact h'.2 (firstInput_length hfit.1 p.1.2)
  exact prHit_le _ (fun (z : MidU3 × (List E × E)) ↦ z.1.mw.2.state) (fun _ _ h ↦ h) (tCache3 D) (tSteps3 D)
    (tSteps3 D + c2Cost D) (stageACost D) _ _ _ (fun s₁ ↦ chainF_preTail3 D input rows q p.1 s₁) hc
    (by unfold tCache3; omega) hx

/-! ## At the reference shape -/

theorem tSteps3_reference (D : Deployment) (hD : D.shape = reference) : tSteps3 D = 48 := by
  unfold tSteps3 flockStepsD3 flockSteps3 frontSteps3 zcSteps3
  rw [hD, Cost.reference_flockLogN]
  rfl

theorem tCache3_reference (D : Deployment) (hD : D.shape = reference) : tCache3 D ≤ 2 ^ 28 := by
  obtain ⟨h1, h2, h3, -⟩ := Cost.reference_vars
  have hs := tSteps3_reference D hD
  have hc1 : E2ECompleteness.Cost.treeCost (c1Layout D.shape).vars ≤ 20971520 := by
    rw [hD]
    exact (Cost.treeCost_mono h1).trans (by decide)
  have hc2 : c2Cost D ≤ 41943040 := by
    unfold c2Cost
    rw [hD]
    exact (Cost.treeCost_mono h2).trans (by decide)
  have hset : Cost.setupCost D ≤ 86507520 := by
    have h19 : 2 ^ ((setupLayout D.shape).vars - 6 + 1) ≤ 2 ^ 19 := by
      rw [hD]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : 2 ^ (matrixVars - 6 + 1) = 2 ^ 23 := rfl
    unfold Cost.setupCost
    omega
  unfold tCache3 stageACost
  omega

/-- **The reference bound**: `tFreshBound3 D ≤ 2^-200` (`(48 + 1) · 2^28 / 2^256 < 2^-200`). -/
theorem tFreshBound3_reference (D : Deployment) (hD : D.shape = reference) :
    tFreshBound3 D ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := by
  have hN : (tSteps3 D + 1) * tCache3 D ≤ 2 ^ 56 := by
    rw [tSteps3_reference D hD]
    have := tCache3_reference D hD
    omega
  unfold tFreshBound3
  rw [← mul_div_assoc, ← Nat.cast_mul]
  calc (((tSteps3 D + 1) * tCache3 D : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 ^ 56 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
        ENNReal.div_le_div_right (by exact_mod_cast hN) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ 200 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_eq_inv_mul, ENNReal.inv_pow, mul_comm,
          show (256 : ℕ) = 200 + 56 from rfl]
        exact E2ECompleteness.two_pow_mul_inv_pow 56 200

/-- **`t`'s query is fresh at the reference shape** for π1-rec3's Flock prover, with probability of a cache hit at
most `2^-200`: the hypothesis `TQueryFresh3` of `uniCompletenessRec3_reference`. -/
theorem tQueryFresh3_reference (D : Deployment) (hD : D.shape = reference) :
    TQueryFresh3 flockProve3H D ((2 : ℝ≥0∞)⁻¹ ^ 200) :=
  fun input rows q hfit hrel ↦
    (tQueryFresh3_flockProve3 D input rows q hfit hrel).trans (tFreshBound3_reference D hD)

/-- **`UniCompletenessRec3` at the reference shape for π1-rec3's Flock prover**: `uniCompletenessRec3_reference` with
`TQueryFresh3` discharged (`tQueryFresh3_reference`). -/
theorem uniCompletenessRec3_reference_flockProve3 (D : Deployment) (hD : D.shape = reference)
    (hflock : FlockCommutes flockProve3H) (hc : ProverCommutes3 flockProve3H D)
    (hdup : ProverDuplex3 flockProve3H D) (hcost : ProverCost3 flockProve3H D (2 ^ 47))
    (hstream : ProverStreamSize3 flockProve3H D (2 ^ 40)) (hv : VerifierCommutes3) (hvd : VerifierDisc3)
    {NV : ℕ} (hvcost : VerifierCost3 D (2 ^ 40) NV) (hNV : NV ≤ 2 ^ 43) (hacc : CoreAccepts3 D flockProve3H)
    (hpow : CoreFailsOnlyAtPow3 D flockProve3H) :
    UniCompletenessRec3 D (uniProverRec3RP flockProve3H D) deltaRec3 :=
  uniCompletenessRec3_reference flockProve3H D hD hflock hc hdup hcost hstream hv hvd hvcost hNV hacc hpow
    (tQueryFresh3_reference D hD)

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.TFresh3.wend_flockProve3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.TFresh3.wend_flockProve3

/-- info: 'UniComplete.Rec3.tQueryFresh3_flockProve3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.tQueryFresh3_flockProve3

/-- info: 'UniComplete.Rec3.tQueryFresh3_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.tQueryFresh3_reference

/-- info: 'UniComplete.Rec3.uniCompletenessRec3_reference_flockProve3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.uniCompletenessRec3_reference_flockProve3
