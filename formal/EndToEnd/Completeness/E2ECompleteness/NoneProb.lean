-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the two calls over the lazy permutation
-- (`simulateQ_lazy_keccakCallsOverQueryPermutation`), the duplex discipline (`DuplexVm`) and the
-- block cost (`hashBlocks`), and, as `Grinding.lean`, the logged random oracle and mumbai's
-- proof-of-work potential (`powPot`, `prEvent_run_loggedRO_le_of_freshStepBound`).
import E2ECompleteness.Done

/-!
# The honest prover makes a proof, for every coins

The zero-knowledge end theorem (`zeroKnowledge_deployed_whir`, `ZK/ProverBridge.lean`) assumes
`hnone`: for a statement and a witness of the relation, the Statement's honest prover makes no proof
(a proof of work exhausting its `2^25` nonces, or the reduction rejecting its own challenges) with
probability at most `δ`, **for every coins** (masks and paddings), the probability over the random
permutation alone. **`hnone_deployed`** proves it at

  `deltaNone = (17 · 2^24 + 8) / 2^192 + 2 / 2^256 + 2^-304 + (2^48)² / 2^508`

(`deltaNone ≤ deltaDeployed < 2^-162`, `deltaNone_lt`), from the ingredients of completeness:

* **the prover alone, staged** (`proverStaged`, `proverWithH_eq_staged`): the honest prover with
  two calls is the chain's shape `staged` (`Chain.lean`) of stage A without a setup, stage B, and the
  prover's tail (`proverTail`) as stage C, its output the first component;
* **`noneProb_eq_staged`**: `noneProb` (`PcsQuotient.prover` over `queryPermutation`, run with the
  random permutation; restated verbatim from `ZK/ProverBridge.lean`) is the staged prover's
  probability of no proof against the sponge over the random permutation;
* **the random permutation to two random oracles** (`rpm_le_rom`): the staged prover follows the
  duplex discipline (`duplexVm_proverStaged`) and makes at most `2^48` block calls
  (`cost_proverStaged`), so `rpmError (2^48) = 2^-412`;
* **the challenges** `(α, β, t)` fall in the degenerate set `badSet w masks` with probability at
  most its density and `2 / 2^256` (`prEvent_staged_le`, `badSet_density`);
* **outside it, the reduction returns claims** (`red_staged`, through `tailReducesG_pure`: the
  prover's stages without a setup are the completeness run's stages at every hash function and
  permutation, but for the setup's root), so a missing proof is a failed nonce search
  (`opening_fails_of_proverTail`), which puts mumbai's proof-of-work potential at `1`
  (`one_le_powPot_of_none`); at most `2^48` queries make that `≤ 2^-304` (`grinding_le`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.Protocol.Verifier
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The probability of no proof -/

/-- **The probability that the Statement's prover makes no proof** at the coins `c` (verbatim
`PcsQuotient.EndToEnd.noneProb`, `ZK/ProverBridge.lean`): the honest prover `PcsQuotient.prover`
over `queryPermutation`, run with the random permutation. -/
noncomputable def noneProb (stmt : PcsQuotient.Statement) (w : PcsQuotient.Secret)
    (c : Masks × Padding × Padding) : ℝ≥0∞ :=
  Pr{let r ← Common.runWithRandomPermutation (PcsQuotient.prover Common.queryPermutation stmt w c)}[
    r = none]

/-! ## The prover alone, staged -/

section Generic

variable (circuit : Circuit) (cells : Array K) (masks : Masks) (witnessPad quotientPad : Padding)
  (fuel : ℕ) (stmt : Statement)

/-- **The prover alone in the chain's shape**: stage A with no setup (`pure default` in place of
the setup's root), stage B, and the prover's tail from `t` as stage C. -/
def proverStagedG : OracleComp KeccakCalls (Option PcsQuotient.Proof × (E × E × E)) :=
  staged challengeOf (stageAG (pure default) circuit cells masks witnessPad stmt)
    (stageBG circuit cells quotientPad)
    fun a bq _ _ _ s₄ ↦ proverTail circuit fuel stmt a bq (challengeOf s₄)

/-- **For any circuit and cells, the prover with two calls is the staged prover's output.** -/
theorem proveWithH_eq_staged :
    proveWithH callKeccak256 callKeccakF1600 fuel circuit stmt cells masks witnessPad quotientPad =
      (·.1) <$> proverStagedG circuit cells masks witnessPad quotientPad fuel stmt := by
  simp only [proveWithH, proverStagedG, staged, stageAG, stageBG, proverTail,
    quotientStackOf, startWithH, squeezeWithH, bind_assoc, pure_bind, map_bind, map_pure, chainIn,
    Chain.absorb, List.nil_append, List.append_nil, List.flatMap_nil, List.cons_append,
    List.flatMap_cons, bind_pure]
  refine bind_congr fun indexTree ↦ ?_
  refine bind_congr fun witnessTree ↦ ?_
  refine bind_congr fun s₀ ↦ ?_
  refine bind_congr fun s₁ ↦ ?_
  refine bind_congr fun s₂ ↦ ?_
  refine bind_congr fun s₃ ↦ ?_
  refine bind_congr fun qt ↦ ?_
  refine bind_congr fun s₄ ↦ ?_
  rfl

/-- At a hash function and a permutation, stage A with a setup is stage A with no setup but for
the setup's root. -/
theorem runAt_stageAG (setup : OracleComp KeccakCalls Digest) (H : Bytes → Digest)
    (F : KeccakState → KeccakState) :
    runAt H F (stageAG setup circuit cells masks witnessPad stmt) =
      ((runAt H F setup, (runAt H F (stageAG (pure default) circuit cells masks witnessPad stmt)).1.2),
        (runAt H F (stageAG (pure default) circuit cells masks witnessPad stmt)).2) := by
  simp only [runAt, stageAG, simulateQ_bind, simulateQ_pure, pure_bind]
  rfl

/-- Stage B reads nothing of the setup's root. -/
theorem stageBG_root (a : AuxA) (idx : Digest) (s₁ s₂ s₃ : Digest) :
    stageBG circuit cells quotientPad (idx, a.2) s₁ s₂ s₃ =
      stageBG circuit cells quotientPad a s₁ s₂ s₃ := rfl

/-- The prover's reduction proof reads nothing of the setup's root. -/
theorem tailProof_root (a : AuxA) (idx : Digest) (bq : Tree × Array K) (t : E) :
    tailProof circuit (idx, a.2) bq t = tailProof circuit a bq t := rfl

/-- **(Red) without a setup**, from (Red) with any setup: the stages agree but for the setup's
root, which neither stage B nor the reduction reads. -/
theorem tailReducesG_pure (setup : OracleComp KeccakCalls Digest) (bad : Finset (E × E × E))
    (hred : TailReducesG setup circuit cells masks witnessPad quotientPad stmt bad) :
    TailReducesG (pure default) circuit cells masks witnessPad quotientPad stmt bad := by
  intro H F x s₁ s₂ s₃ y s₄ hst hgood
  have hA : runAt H F (stageAG setup circuit cells masks witnessPad stmt) =
      ((runAt H F setup, x.1.2), x.2) := by
    rw [runAt_stageAG, hst.hA]
  have hB : runAt H F (stageBG circuit cells quotientPad (runAt H F setup, x.1.2) s₁ s₂ s₃) = y := by
    rw [stageBG_root]
    exact hst.hB
  have h := hred H F ((runAt H F setup, x.1.2), x.2) s₁ s₂ s₃ y s₄
    ⟨hA, hst.h₁, hst.h₂, hst.h₃, hB, hst.h₄⟩ hgood
  rwa [tailProof_root] at h

/-- **A run with no proof at non-degenerate challenges puts the potential at one.** On a log at
which the staged prover makes no proof while its challenges avoid `bad`, given (Red), one of the
prover's openings failed at a `17`-bit proof of work whose nonces below `fuel` all fail in the log. -/
theorem one_le_powPot_of_none {bad : Finset (E × E × E)} (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0)
    (hred : TailReducesG (pure default) circuit cells masks witnessPad quotientPad stmt bad)
    {ℓ : Log} {z : Option PcsQuotient.Proof × (E × E × E)}
    (hz : simulateQ (lookImpl ℓ) (proverStagedG circuit cells masks witnessPad quotientPad fuel stmt) =
      some z)
    (hnone : z.1 = none) (hgood : z.2 ∉ bad) :
    1 ≤ powPot Whir.queryGrindingBits fuel ℓ := by
  -- A hash function and a permutation extending the log.
  let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
  let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD default
  have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
  have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
  have hid : ∀ {β : Type} (oa : OracleComp KeccakCalls β) (r : β),
      simulateQ (lookImpl ℓ) oa = some r → runAt Ht Ft oa = r :=
    fun oa r h ↦ simulateQ_id_of_look ℓ Ht Ft hH hF oa r h
  -- The staged prover at the log.
  unfold proverStagedG staged at hz
  obtain ⟨x, hx, hz⟩ := look_bind hz
  obtain ⟨s₁, hs₁, hz⟩ := look_bind hz
  obtain ⟨s₂, hs₂, hz⟩ := look_bind hz
  obtain ⟨s₃, hs₃, hz⟩ := look_bind hz
  obtain ⟨y, hy, hz⟩ := look_bind hz
  obtain ⟨s₄, hs₄, hz⟩ := look_bind hz
  obtain ⟨o, ho, hz⟩ := look_bind hz
  obtain rfl := look_pure hz
  have hst : StagesAt (pure default) circuit cells masks witnessPad quotientPad stmt Ht Ft x s₁ s₂
      s₃ y s₄ :=
    ⟨hid _ _ hx, hH _ _ (look_callKeccak256 hs₁), hH _ _ (look_callKeccak256 hs₂),
      hH _ _ (look_callKeccak256 hs₃), hid _ _ hy, hH _ _ (look_callKeccak256 hs₄)⟩
  have ho' : simulateQ (lookImpl ℓ) (proverTail circuit fuel stmt x.1 y.1 (challengeOf s₄)) =
      some none :=
    ho.trans (congrArg some hnone)
  -- The prover's tail returned no proof while its reduction returned claims: an opening failed.
  obtain ⟨L, tree, stack, claims, hfail⟩ :=
    opening_fails_of_proverTail circuit fuel stmt x.1 y.1 _ ho' fun hr ↦
      hred Ht Ft x s₁ s₂ s₃ y s₄ hst hgood (by
        have h := hid _ _ hr
        rw [runAt, simulateQ_reduceWithH] at h
        exact h)
  exact one_le_powPot_of_proveOpening hfuel hfuel0 hfail

/-- **The staged prover follows the duplex discipline**, for any circuit and cells. -/
theorem disc_proverStagedG :
    Disc (proverStagedG circuit cells masks witnessPad quotientPad fuel stmt) :=
  disc_staged _ _ _ _ (disc_of_hOnly (hOnly_stageAG _ (hOnly_pure _) _ _ _ _ _))
    (fun _ _ _ _ ↦ disc_of_hOnly (hOnly_stageBG _ _ _ _ _ _ _))
    (fun _ _ _ _ _ _ ↦ disc_proverTail _ _ _ _ _ _)

open Cost in
/-- **The staged prover's block count**, for any circuit and cells: the index, witness and
quotient trees, the chain's five hashes, the reduction and the three openings. -/
theorem cost_proverStagedG (hr : cellVars circuit.logRows ≤ 24) :
    QC (proverStagedG circuit cells masks witnessPad quotientPad fuel stmt)
      (treeCost (cellVars circuit.logRows) + treeCost (cellVars circuit.logRows + 1) +
        treeCost (cellVars circuit.logRows + 4) + 5 + proverCost fuel) := by
  unfold proverStagedG
  refine (cost_staged _ _ _ _ _ _ _
    (cost_stageAG (pure default) 0 (qc_pure _ 0) circuit cells masks witnessPad stmt)
    (fun a s₁ s₂ s₃ ↦ cost_stageBG circuit cells quotientPad a s₁ s₂ s₃)
    (fun a bq _ _ _ s₄ ↦ cost_proverTail circuit hr fuel stmt a bq (challengeOf s₄))).mono ?_
  omega

/-- **The challenges of the staged prover** fall in `bad` with probability at most
`2 / 2^256 + |bad| / 2^576` in the two-call random-oracle model (`prEvent_staged_le`). -/
theorem prEvent_proverStagedG_mem_le (bad : Finset (E × E × E)) :
    Pr{let z ← (simulateQ ro (proverStagedG circuit cells masks witnessPad quotientPad fuel
      stmt)).run' ∅}[z.2 ∈ bad] ≤ 2 / 2 ^ 256 + (bad.card : ℝ≥0∞) / 2 ^ 576 := by
  rw [StateT.run'_eq, prEvent_map]
  exact prEvent_staged_le _ challengeOf_regular _ _ _ _
    (hashOK_stageAG _ (HashOK.pure _ _) _ _ _ _ _)
    (fun a s₁ s₂ s₃ ↦ hashOK_stageBG _ _ _ a s₁ s₂ s₃) ∅ fun m hm ↦ absurd rfl hm

/-- **No proof at challenges outside `bad`**, given (Red), has probability at most
`Q · (1 - 2^-17)^fuel` in the two-call random-oracle model, for a staged prover of at most `Q`
queries: mumbai's proof-of-work potential over the logged random oracle. -/
theorem prEvent_proverStagedG_none_le {bad : Finset (E × E × E)} (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0)
    (hred : TailReducesG (pure default) circuit cells masks witnessPad quotientPad stmt bad)
    {Q : ℕ} (hQ : IsTotalQueryBound (proverStagedG circuit cells masks witnessPad quotientPad fuel
      stmt) Q) :
    Pr{let z ← (simulateQ ro (proverStagedG circuit cells masks witnessPad quotientPad fuel
      stmt)).run' ∅}[z.1 = none ∧ z.2 ∉ bad] ≤
      (Q : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ fuel := by
  have hstep : LogFreshStepBound (powPot Whir.queryGrindingBits fuel)
      (missProb Whir.queryGrindingBits ^ fuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF (by decide) (by decide) hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have e : Pr{let z ← (simulateQ ro (proverStagedG circuit cells masks witnessPad quotientPad fuel
      stmt)).run' ∅}[z.1 = none ∧ z.2 ∉ bad] =
      Pr{let z ← (simulateQ loggedRO (proverStagedG circuit cells masks witnessPad quotientPad fuel
        stmt)).run []}[z.1.1 = none ∧ z.1.2 ∉ bad] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _
      (fun (z : Option PcsQuotient.Proof × (E × E × E)) _ ↦ z.1 = none ∧ z.2 ∉ bad)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ Q hQ []
    (fun (z : Option PcsQuotient.Proof × (E × E × E)) _ ↦ z.1 = none ∧ z.2 ∉ bad)
    fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact one_le_powPot_of_none _ _ _ _ _ _ _ hfuel hfuel0 hred hlook hev.1 hev.2
  · rw [powPot_nil, zero_add]

end Generic

/-! ## The deployed instance -/

/-- **The deployed prover alone, staged.** -/
def proverStaged (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding) :
    OracleComp KeccakCalls (Option PcsQuotient.Proof × (E × E × E)) :=
  proverStagedG (membership logRows) (cellsOf w) coins.1 coins.2.1 coins.2.2 nonceFuel stmt

/-- **The deployed prover with two calls is the staged prover's output.** -/
theorem proverWithH_eq_staged (stmt : Statement) (w : Secret)
    (coins : Masks × Padding × Padding) :
    proverWithH callKeccak256 callKeccakF1600 nonceFuel stmt w coins.1 coins.2.1 coins.2.2 =
      (·.1) <$> proverStaged stmt w coins :=
  proveWithH_eq_staged _ _ _ _ _ _ _

/-- **`noneProb` is the staged prover's probability of no proof** against the sponge over the
random permutation. -/
theorem noneProb_eq_staged (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding) :
    noneProb stmt w c =
      Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (proverStaged stmt w c)).run' []}[
        z.1 = none] := by
  have e : PcsQuotient.prover Common.queryPermutation stmt w c =
      simulateQ keccakCallsOverQueryPermutation
        (proverWithH callKeccak256 callKeccakF1600 nonceFuel stmt w c.1 c.2.1 c.2.2) := by
    simp only [PcsQuotient.prover, proverWith_eqH, simulateQ_proverWithH,
      implH_keccakCallsOverQueryPermutation, implF_keccakCallsOverQueryPermutation]
  rw [noneProb, e, Common.runWithRandomPermutation, simulateQ_lazy_keccakCallsOverQueryPermutation,
    proverWithH_eq_staged, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
    Functor.map_map, prEvent_map, prEvent_map]

/-- **The staged prover follows the duplex discipline.** -/
theorem duplexVm_proverStaged (stmt : Statement) (w : Secret)
    (coins : Masks × Padding × Padding) : DuplexVm (proverStaged stmt w coins) [] :=
  (duplexVm_iff_duplexP _ _).mpr (disc_proverStagedG _ _ _ _ _ _ _ [])

open Cost in
/-- **The staged prover makes at most `2^48` block calls.** -/
theorem cost_proverStaged (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding) :
    Common.QueryCostAtMost (proverStaged stmt w coins) hashBlocks (2 ^ 48) := by
  have hm : (membership logRows).logRows = 22 := rfl
  refine (cost_proverStagedG (membership logRows) (cellsOf w) coins.1 coins.2.1 coins.2.2
    nonceFuel stmt (by rw [hm]; decide)).mono ?_
  rw [hm]
  norm_num [treeCost, proverCost, blockFactor, whirBound, costHeight, nonceFuel, cellVars]

/-- **(Red) for the staged prover**: at every hash function and permutation, when the challenges
avoid `badSet`, the reduction returns claims on the prover's reduction proof. -/
theorem tailReduces_proverStaged (stmt : Statement) (w : Secret) (hrel : Relation stmt w)
    (coins : Masks × Padding × Padding) :
    TailReducesG (pure default) (membership logRows) (cellsOf w) coins.1 coins.2.1 coins.2.2 stmt
      (badSet w coins.1) :=
  tailReducesG_pure _ _ _ _ _ _ _ _
    (tailReduces constants claimsMatch circuitMatch tablesMatch stmt w hrel coins)

/-! ## The bound -/

/-- **The bound on no proof**: the degenerate challenges' density, the chain's two repetitions,
the grinding, and the transfer from the random permutation at `2^48` block calls. -/
noncomputable def deltaNone : ℝ≥0∞ :=
  (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 + 2 / 2 ^ 256 + (2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)

/-- `deltaNone` is at most completeness's `deltaDeployed` (`2^-304 ≤ 3 · 2^-277`). -/
theorem deltaNone_le : deltaNone ≤ deltaDeployed := by
  have h : (2 : ℝ≥0∞)⁻¹ ^ 304 ≤ 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 :=
    calc (2 : ℝ≥0∞)⁻¹ ^ 304 ≤ (2 : ℝ≥0∞)⁻¹ ^ 277 := inv_pow_le_inv_pow (by norm_num)
      _ ≤ 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 := le_mul_of_one_le_left bot_le (by norm_num)
  unfold deltaNone deltaDeployed
  exact add_le_add (add_le_add le_rfl h) le_rfl

/-- **`deltaNone < 2^-162`.** -/
theorem deltaNone_lt : deltaNone < (2 : ℝ≥0∞)⁻¹ ^ 162 :=
  deltaNone_le.trans_lt deltaDeployed_lt

/-- **For fixed coins, the staged prover makes no proof with probability at most `deltaNone`.** -/
theorem prEvent_proverStaged_none_le (stmt : Statement) (w : Secret) (hrel : Relation stmt w)
    (c : Masks × Padding × Padding) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (proverStaged stmt w c)).run' []}[
      z.1 = none] ≤ deltaNone := by
  unfold deltaNone
  refine rpm_le_rom _ (duplexVm_proverStaged stmt w c) (cost_proverStaged stmt w c)
    (fun z ↦ z.1 = none) ?_
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _
    (fun z : Option PcsQuotient.Proof × (E × E × E) ↦ z.2 ∈ badSet w c.1)).trans
    (add_le_add ?_ ?_)
  · -- The challenges in the degenerate set.
    refine (prEvent_proverStagedG_mem_le (membership logRows) (cellsOf w) c.1 c.2.1 c.2.2 nonceFuel
      stmt (badSet w c.1)).trans ?_
    rw [add_comm]
    exact add_le_add (badSet_density w c.1) le_rfl
  · -- Outside it, a failed nonce search.
    have hfuel : nonceFuel ≤ 2 ^ 64 := by norm_num [nonceFuel]
    have hfuel0 : nonceFuel ≠ 0 := by norm_num [nonceFuel]
    exact (prEvent_proverStagedG_none_le (membership logRows) (cellsOf w) c.1 c.2.1 c.2.2 nonceFuel
      stmt hfuel hfuel0 (tailReduces_proverStaged stmt w hrel c)
      (isTotalQueryBound_of_queryCostAtMost (cost_proverStaged stmt w c))).trans grinding_le

/-- **`hnone` of the zero-knowledge end theorem**: for a statement and a witness of the relation,
for every coins `c` (masks and paddings), the Statement's honest prover makes no proof with
probability at most `deltaNone < 2^-162`. -/
theorem hnone_deployed :
    ∀ stmt w, Relation stmt w → ∀ c, noneProb stmt w c ≤ deltaNone := by
  intro stmt w hrel c
  rw [noneProb_eq_staged]
  exact prEvent_proverStaged_none_le stmt w hrel c

end E2ECompleteness

/-- info: 'E2ECompleteness.proverWithH_eq_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.proverWithH_eq_staged

/-- info: 'E2ECompleteness.noneProb_eq_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.noneProb_eq_staged

/-- info: 'E2ECompleteness.deltaNone_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.deltaNone_lt

/-- info: 'E2ECompleteness.hnone_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.hnone_deployed
