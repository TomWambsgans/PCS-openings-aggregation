-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/EndToEnd/Completeness/E2ECompleteness/End.lean`, `Assemble.lean`, `Final.lean` (`deltaDeployed`,
-- `deltaDeployed_lt`, `grinding_le`) for the univariate verifier. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): `rpmError`, the
-- proof-of-work miss probability `missProb`, WHIR's verifier bound `whirBound`.
import UniComplete.ProbGrind

/-!
# `UniCompleteness`, from the named hypotheses

**`uniCompleteness_of_core`**: for every deployment `D`, `UniCompleteness D (uniProverRP flock D) δ` with

  `δ = Nbad / 2^192 + 6 / 2^256 + (ct / 2^192 + εt) + N · (1 − 2^-17)^(2^25) + N² / 2^508`,
  `N = setupCost D + (NP + verifierCost D S)`,

from the named hypotheses of `ProbHyp.lean` and `ProbExp.lean` (`ProverCommutes`, `FlockCommutes`, `ProverDuplex`,
`ProverCost NP`, `ProverStreamSize S`, `CoreAccepts`, `CoreFailsOnlyAtPow`, `BadFpCard Nbad`, `BadTCard ct`,
`TQueryFresh εt`): the staged experiment (`stagedU`, `UniStaged.Holds`: `experiment_staged`, `duplexVm_stagedU`,
`cost_stagedU`, `firstInput_length`, `hashA_stagedU`, `rejectGood_uni`) and `uniCompleteness_of_staged`.

**`uniCompleteness_reference`**: at the reference shape (`D.shape = reference`), with a program IV of at most `2^40`
bytes (the deployed one has `32`), `NP = 2^47` block calls for the prover, `S = 2^40` stream bytes, `Nbad < 2^24`
bad `β` per `α`, `ct = 3 · 2^17` bad `t` per Flock point and `εt = 2^-200`:
`UniCompleteness D (uniProverRP flock D) deltaUni`, where

  `deltaUni = (2^24 − 1) / 2^192 + 6 / 2^256 + (3 · 2^17 / 2^192 + 2^-200) + 2^-304 + (2^48)² / 2^508 < 2^-167`
  (`deltaUni_lt`; about `2^-167.95`: the bus challenges' `2^-168`, `t`'s `2^-173.4`).

The block count at the reference shape (`totalCost_le`): the setup's `5 · 2^19 + 10 · 2^23` (its layout has at most
`24` variables, `setupLayout_reference_vars`, through `List.mergeSort_perm`: the layout's offset is the sum of its
pieces' sizes), the prover's `2^47`, the verifier's on `2^40` bytes (`< 2^43`): below `2^48`. The grinding at
`2^48` queries is `E2ECompleteness.grinding_le`'s `2^-304`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile.Rom (missProb)
open UniStatement
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Prob

variable (flock : PolyFlock) (D : Deployment)

/-! ## The staged experiment holds -/

/-- **The univariate experiment's code-level bridge**, from the named hypotheses. -/
theorem stagedU_holds {Nbad ct NP S : ℕ} {εt : ℝ≥0∞} (hc : ProverCommutes flock D) (hf : FlockCommutes flock)
    (hdup : ProverDuplex flock D) (hcost : ProverCost flock D NP) (hstream : ProverStreamSize flock D S)
    (hacc : CoreAccepts D flock) (hpow : CoreFailsOnlyAtPow D flock) (hbad : BadFpCard D Nbad)
    (hbadT : BadTCard D.shape ct) (htf : TQueryFresh flock D εt) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation rows input q) :
    (stagedU flock D input rows q).Holds D (uniProverRP flock D) input rows q (BadFp (honestTrace D input rows q))
      (BadT D.shape) Nbad ct (Cost.setupCost D + (NP + Cost.verifierCost D S)) εt
      (((Cost.setupCost D + (NP + Cost.verifierCost D S) : ℕ) : ℝ≥0∞) *
        missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := experiment_staged flock D hc input rows q
  duplex := duplexVm_stagedU flock D hdup input rows q hfit hrel
  cost := cost_stagedU flock D hcost hstream input rows q hfit hrel
  inp_length a := firstInput_length hfit.1 a.2
  hashA := hashA_stagedU flock D input rows q
  badCard := hbad input rows q hfit hrel
  badTCard := hbadT
  tFresh := htf input rows q hfit hrel
  rejectGood := rejectGood_uni flock D hc hf hacc hpow input rows q hfit hrel
    (cost_stagedU flock D hcost hstream input rows q hfit hrel)

/-- **`UniCompleteness` from the named hypotheses**, for every deployment. -/
theorem uniCompleteness_of_core {Nbad ct NP S : ℕ} {εt : ℝ≥0∞} (hc : ProverCommutes flock D)
    (hf : FlockCommutes flock) (hdup : ProverDuplex flock D) (hcost : ProverCost flock D NP)
    (hstream : ProverStreamSize flock D S) (hacc : CoreAccepts D flock) (hpow : CoreFailsOnlyAtPow D flock)
    (hbad : BadFpCard D Nbad) (hbadT : BadTCard D.shape ct) (htf : TQueryFresh flock D εt) :
    UniCompleteness D (uniProverRP flock D)
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) +
        ((Cost.setupCost D + (NP + Cost.verifierCost D S) : ℕ) : ℝ≥0∞) *
          missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel +
        rpmError (Cost.setupCost D + (NP + Cost.verifierCost D S))) :=
  uniCompleteness_of_staged fun input rows q hfit hrel ↦
    ⟨stagedU flock D input rows q, _, _,
      stagedU_holds flock D hc hf hdup hcost hstream hacc hpow hbad hbadT htf input rows q hfit hrel⟩

/-- A larger error is still an error. -/
theorem UniCompletenessWith.mono {P : UniProver D} {δ δ' : ℝ≥0∞} (h : UniCompletenessWith D P δ) (hδ : δ ≤ δ') :
    UniCompletenessWith D P δ' :=
  fun input rows q hfit hrel ↦ (h input rows q hfit hrel).trans hδ

/-! ## The block count at the reference shape -/

theorem log2Ceil_le {v k : ℕ} (h : v ≤ 2 ^ k) : log2Ceil v ≤ k := by
  unfold log2Ceil
  split_ifs with hv
  · exact Nat.zero_le _
  · have hne : v - 1 ≠ 0 := by omega
    have : Nat.log2 (v - 1) < k := (Nat.log2_lt hne).2 (by omega)
    omega

/-- A fold that adds `w x` to its second component adds their sum. -/
theorem foldl_snd {β γ : Type} (g : β × ℕ → γ → β × ℕ) (w : γ → ℕ) (hg : ∀ acc x, (g acc x).2 = acc.2 + w x) :
    ∀ (l : List γ) (acc : β × ℕ), (l.foldl g acc).2 = acc.2 + (l.map w).sum
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_snd g w hg l, hg, List.map_cons, List.sum_cons]
    ring

/-- **The setup's layout at the reference shape has at most `24` variables** (`2^23` tuple words, `2^21`
addresses). -/
theorem setupLayout_reference_vars : (setupLayout reference).vars ≤ 24 := by
  have hs : setupLayout reference =
      StackLayout.new [(.bytecodeTuple, 23, false), (.address, 21, false)] := rfl
  rw [hs]
  unfold StackLayout.new
  dsimp only
  rw [foldl_snd _ (fun p : Column × ℕ × ℕ ↦ 2 ^ p.2.2) (fun acc x ↦ rfl),
    (List.Perm.map _ (List.mergeSort_perm _ _)).sum_eq]
  refine max_le (log2Ceil_le ?_) (by norm_num)
  norm_num [List.range_one]

theorem walkCost_le (s : UniStatement.Shape) (v : UniStatement.Flock.Variant) :
    Cost.walkCost s v ≤ 2 * (blake2sR1csLogSize + s.heights.getD opBlake2s 0) + 34 := by
  unfold Cost.walkCost
  omega

theorem reference_blake2s_height : reference.heights.getD opBlake2s 0 ≤ 18 := by
  have : reference.heights.getD opBlake2s 0 = log2Ceil 202025 := rfl
  rw [this]
  exact log2Ceil_le (by norm_num)

theorem openCost_le : Cost.openCost ≤ 121492 := by
  unfold Cost.openCost E2ECompleteness.Cost.vOpen LeanVM.Protocol.Verifier.whirBound
  norm_num

/-- **The block count at the reference shape**: below `2^48`, for a prover of `2^47` block calls and streams of
`2^40` bytes, and a program IV of at most `2^40` bytes. -/
theorem totalCost_le (hD : D.shape = reference) (hiv : D.programIv.length ≤ 2 ^ 40) :
    Cost.setupCost D + (2 ^ 47 + Cost.verifierCost D (2 ^ 40)) ≤ 2 ^ 48 := by
  have h1 : Cost.setupCost D ≤ 5 * 2 ^ 19 + 2 * (5 * 2 ^ 23) := by
    have hv := setupLayout_reference_vars
    have hp : 2 ^ ((setupLayout D.shape).vars - 6 + 1) ≤ 2 ^ 19 := by
      rw [hD]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : 2 ^ (matrixVars - 6 + 1) = 2 ^ 23 := rfl
    unfold Cost.setupCost
    omega
  have h2 : Cost.verifierCost D (2 ^ 40) ≤ (280 + 2 ^ 40) + 1 + (2 * (14 + 18) + 34) + 3 * 2 ^ 40 + 5 * 121492 := by
    unfold Cost.verifierCost Cost.ivCost
    have hw : Cost.walkCost D.shape flockMain ≤ 2 * (14 + 18) + 34 := by
      have h := walkCost_le D.shape flockMain
      rw [hD] at h ⊢
      have hb := reference_blake2s_height
      have hR : blake2sR1csLogSize = 14 := rfl
      rw [hR] at h
      omega
    have hivc : (280 + D.programIv.length) / 136 ≤ 280 + 2 ^ 40 :=
      (Nat.div_le_self _ _).trans (by omega)
    have ho := openCost_le
    omega
  omega

/-! ## The numbers -/

/-- **The deployed bound**: `Nbad < 2^24` bad `β` per `α`, `3 · 2^17` bad `t` per Flock point, `t`'s cache hit
`2^-200`, `2^48` block calls (the grinding's `2^-304`, the transfer's `(2^48)² / 2^508`). -/
noncomputable def deltaUni : ℝ≥0∞ :=
  ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 +
    (((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) + (2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)

theorem rpmError_mono {a b : ℕ} (h : a ≤ b) : rpmError a ≤ rpmError b := by
  unfold rpmError
  gcongr

theorem deltaUni_lt : deltaUni < (2 : ℝ≥0∞)⁻¹ ^ 167 := by
  have ha : ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 168 := by
    calc ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 24 * (2 : ℝ≥0∞)⁻¹ ^ (168 + 24) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 168 := E2ECompleteness.two_pow_mul_inv_pow 24 168
  have hb : (6 : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := by
    calc (6 : ℝ≥0∞) / 2 ^ 256 ≤ 2 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ (253 + 3) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 253 := E2ECompleteness.two_pow_mul_inv_pow 3 253
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hct : ((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := by
    calc ((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 19 * (2 : ℝ≥0∞)⁻¹ ^ (173 + 19) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.two_pow_mul_inv_pow 19 173
  have he : (2 : ℝ≥0∞)⁻¹ ^ 200 ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hc : (2 : ℝ≥0∞)⁻¹ ^ 304 ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hd : rpmError (2 ^ 48) ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := by
    calc rpmError (2 ^ 48) = 2 ^ (48 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (412 + 48 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul,
            ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 412 := E2ECompleteness.two_pow_mul_inv_pow _ 412
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hrest : 6 / 2 ^ 256 + ((((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) +
      ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48))) ≤ (2 : ℝ≥0∞)⁻¹ ^ 170 := by
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 + (((2 : ℝ≥0∞)⁻¹ ^ 173 + (2 : ℝ≥0∞)⁻¹ ^ 173) +
          ((2 : ℝ≥0∞)⁻¹ ^ 173 + (2 : ℝ≥0∞)⁻¹ ^ 173)) :=
          add_le_add hb (add_le_add (add_le_add hct he) (add_le_add hc hd))
      _ = 5 * (2 : ℝ≥0∞)⁻¹ ^ (170 + 3) := by ring
      _ ≤ 2 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ (170 + 3) := by
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 170 := E2ECompleteness.two_pow_mul_inv_pow 3 170
  have e169 : (2 : ℝ≥0∞)⁻¹ ^ 169 + (2 : ℝ≥0∞)⁻¹ ^ 169 = (2 : ℝ≥0∞)⁻¹ ^ 168 := by
    calc (2 : ℝ≥0∞)⁻¹ ^ 169 + (2 : ℝ≥0∞)⁻¹ ^ 169 = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (168 + 1) := by
          rw [← two_mul, pow_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 168 := E2ECompleteness.two_pow_mul_inv_pow 1 168
  have e168 : (2 : ℝ≥0∞)⁻¹ ^ 168 + (2 : ℝ≥0∞)⁻¹ ^ 168 = (2 : ℝ≥0∞)⁻¹ ^ 167 := by
    calc (2 : ℝ≥0∞)⁻¹ ^ 168 + (2 : ℝ≥0∞)⁻¹ ^ 168 = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (167 + 1) := by
          rw [← two_mul, pow_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 167 := E2ECompleteness.two_pow_mul_inv_pow 1 167
  have h168 : (2 : ℝ≥0∞)⁻¹ ^ 170 < (2 : ℝ≥0∞)⁻¹ ^ 168 := by
    calc (2 : ℝ≥0∞)⁻¹ ^ 170 ≤ (2 : ℝ≥0∞)⁻¹ ^ 169 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
      _ < (2 : ℝ≥0∞)⁻¹ ^ 169 + (2 : ℝ≥0∞)⁻¹ ^ 169 := ENNReal.lt_add_right (by simp) (by simp)
      _ = (2 : ℝ≥0∞)⁻¹ ^ 168 := e169
  have hne : ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≠ ⊤ := ne_top_of_le_ne_top (by simp) ha
  have hsum : deltaUni = ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (6 / 2 ^ 256 +
      ((((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) +
        ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)))) := by
    unfold deltaUni
    ac_rfl
  rw [hsum, ← e168]
  exact ENNReal.add_lt_add_of_le_of_lt hne ha (hrest.trans_lt h168)

/-! ## The end theorem -/

/-- **`UniCompleteness` at the reference shape**, `deltaUni < 2^-167`, from the named hypotheses at `NP = 2^47` prover
block calls, `S = 2^40` stream bytes, `Nbad = 2^24 − 1` bad `β` per `α`, `ct = 3 · 2^17` bad `t` per Flock point and
`t`'s cache hit `εt = 2^-200`, for a program IV of at most `2^40` bytes. -/
theorem uniCompleteness_reference (hD : D.shape = reference) (hiv : D.programIv.length ≤ 2 ^ 40)
    (hc : ProverCommutes flock D) (hf : FlockCommutes flock) (hdup : ProverDuplex flock D)
    (hcost : ProverCost flock D (2 ^ 47)) (hstream : ProverStreamSize flock D (2 ^ 40))
    (hacc : CoreAccepts D flock) (hpow : CoreFailsOnlyAtPow D flock) (hbad : BadFpCard D (2 ^ 24 - 1))
    (hbadT : BadTCard reference (3 * 2 ^ 17)) (htf : TQueryFresh flock D ((2 : ℝ≥0∞)⁻¹ ^ 200)) :
    UniCompleteness D (uniProverRP flock D) deltaUni := by
  rw [← hD] at hbadT
  refine UniCompletenessWith.mono D
    (uniCompleteness_of_core flock D hc hf hdup hcost hstream hacc hpow hbad hbadT htf) ?_
  have hN := totalCost_le D hD hiv
  set N := Cost.setupCost D + (2 ^ 47 + Cost.verifierCost D (2 ^ 40))
  unfold deltaUni
  gcongr
  · calc (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel
        ≤ ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
          gcongr
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 304 := E2ECompleteness.grinding_le
  · exact rpmError_mono hN

end UniComplete.Prob

/-! ## Axioms -/

/-- info: 'UniComplete.Prob.prEvent_staged5_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.prEvent_staged5_le

/-- info: 'UniComplete.Prob.prEvent_tquery_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.prEvent_tquery_le

/-- info: 'UniComplete.Prob.proverC_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.proverC_split

/-- info: 'UniComplete.Prob.simulateQ_midU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.simulateQ_midU

/-- info: 'UniComplete.Prob.runAt_stagedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.runAt_stagedU

/-- info: 'UniComplete.Prob.uniCompleteness_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.uniCompleteness_of_staged

/-- info: 'UniComplete.Prob.uniProverWith_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.uniProverWith_split

/-- info: 'UniComplete.Prob.experiment_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.experiment_staged

/-- info: 'UniComplete.Prob.duplexVm_stagedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.duplexVm_stagedU

/-- info: 'UniComplete.Prob.cost_stagedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.cost_stagedU

/-- info: 'UniComplete.Prob.hashA_stagedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.hashA_stagedU

/-- info: 'UniComplete.Prob.rejectGood_uni' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.rejectGood_uni

/-- info: 'UniComplete.Prob.uniCompleteness_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.uniCompleteness_of_core

/-- info: 'UniComplete.Prob.deltaUni_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.deltaUni_lt

/-- info: 'UniComplete.Prob.uniCompleteness_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.uniCompleteness_reference
