-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's analogue of `Prob.lean`
-- (`stagedU_holds`, `uniCompleteness_of_core`, `deltaUni`, `deltaUni_lt`, `uniCompleteness_reference`), itself
-- following `formal/EndToEnd/Completeness/E2ECompleteness/End.lean`, `Assemble.lean`, `Final.lean`. Uses the main
-- line's bad sets' counts (`Core.badFpCard_reference`, `Prob.badTCard_reference`), its setup's layout bound
-- (`Prob.setupLayout_reference_vars`), and leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0): `rpmError`, the proof-of-work miss probability `missProb`.
import UniComplete.Rec3ProbGrind
import UniComplete.Prob
import UniComplete.Core
import UniComplete.ProbBadT

/-!
# `UniCompletenessRec3`, from the named hypotheses

**`uniCompletenessRec3_of_core`**: for every deployment `D`, `UniCompletenessRec3 D (uniProverRec3RP flock D) δ`
with

  `δ = Nbad / 2^192 + (ct / 2^192 + εt) + N · (1 − 2^-17)^(2^25) + N² / 2^508`,  `N = setupCost D + (NP + NV)`,

from the named hypotheses of `Rec3Hyp.lean`, `ProbHyp.lean` and `Rec3ProbExp.lean` (`ProverCommutes3`,
`FlockSimCommutes`, `ProverDuplex3`, `ProverCost3 NP`, `ProverStreamSize3 S`, `VerifierCommutes3`, `VerifierDisc3`,
`VerifierCost3 D S NV`, `CoreAccepts3`, `CoreFailsOnlyAtPow3`, `BadFpCard Nbad`, `BadTCard ct`, `TQueryFresh3 εt`):
the staged experiment (`stagedU3`, `UniStaged3.Holds`: `experiment_staged3`, `duplexVm_stagedU3`, `cost_stagedU3`,
`Prob.firstInput_length`, `hashA_stagedU3`, `rejectGood3`) and `uniCompletenessRec3_of_staged`.

**`uniCompletenessRec3_reference`**: at the reference shape (`D.shape = reference`), with Flock's prover's
commutation `FlockCommutes` (giving `FlockSimCommutes`), `NP = 2^47` prover block calls, `S = 2^40` stream bytes, a
verifier bound `NV ≤ 2^43` on such streams, the main line's bad sets' counts (proved: `Core.badFpCard_reference`,
`Nbad = 2^24 − 1` bad `β` per `α`, for **every** `α`, so for π1-rec3's squares too; `Prob.badTCard_reference`,
`ct = 3 · 2^17` bad `t` per Flock point) and `t`'s cache hit `εt = 2^-200`:
`UniCompletenessRec3 D (uniProverRec3RP flock D) deltaRec3`, where

| term | event |
|---|---|
| `(2^24 − 1)/2^192` | a bus challenge `β` makes a divided fingerprint vanish (`BadFp`, `Core.badFpCard_reference`) |
| `3·2^17/2^192` | `y(t)` is a proper prefix of another point on `C1` (`BadT`, `Prob.badTCard_reference`) |
| `2^-200` | `t`'s query is not fresh (`TQueryFresh3`) |
| `2^-304` | an opening's proof of work fails for every nonce below `nonceFuel` (`rejectGood3`, `grinding_le` at `2^48`) |
| `rpmError (2^48)` | the permutation as two random oracles at `≤ 2^48` blocks: `(2^48)²/2^508 = 2^-412` |

  `deltaRec3 < 2^-168 + 2^-173 < 2^-167` (`deltaRec3_lt_fine`, `deltaRec3_lt`; about `2^-167.967`).

**No `6 / 2^256` term**: π1-rec3 draws its bus challenges from two chained answers (`α = squares (chal s₁) 4`,
`β = chal s₂`), and `s₂`'s `32`-byte query is always fresh (`prEvent_staged2_le`).

The block count at the reference shape (`totalCost3_le`): the setup's `5 · 2^19 + 10 · 2^23` (`setupCost_le`, the
main line's), the prover's `2^47`, the verifier's `NV ≤ 2^43`: below `2^48`.

Decisions: `ProverCommutes3`, `ProverDuplex3`, `VerifierCommutes3`, `VerifierDisc3`, `VerifierCost3`, `CoreAccepts3`,
`CoreFailsOnlyAtPow3`, `ProverCost3`, `ProverStreamSize3`, `TQueryFresh3` are hypotheses of the end theorem (proved
in other modules, or not yet). The verifier's block count enters as `VerifierCost3 D (2^40) NV` with `NV ≤ 2^43`, so
the program IV's length (which bounds the IV hash's blocks, the main line's `hiv`) is not a hypothesis here: it is
what a proof of `VerifierCost3 D (2^40) NV` with `NV ≤ 2^43` needs.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile.Rom (missProb)
open UniStatement
open UniComplete.Prob (BadT BadTCard BadFpCard FlockSimCommutes flockSimCommutes_of_commutes firstInput_length)
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Rec3

variable (flock : FlockProverH) (D : Deployment)

/-! ## The staged experiment holds -/

/-- **π1-rec3's experiment's code-level bridge**, from the named hypotheses. -/
theorem stagedU3_holds {Nbad ct NP S NV : ℕ} {εt : ℝ≥0∞} (hc : ProverCommutes3 flock D)
    (hf : FlockSimCommutes flock) (hdup : ProverDuplex3 flock D) (hcost : ProverCost3 flock D NP)
    (hstream : ProverStreamSize3 flock D S) (hv : VerifierCommutes3) (hvd : VerifierDisc3)
    (hvcost : VerifierCost3 D S NV) (hacc : CoreAccepts3 D flock) (hpow : CoreFailsOnlyAtPow3 D flock)
    (hbad : BadFpCard D Nbad) (hbadT : BadTCard D.shape ct) (htf : TQueryFresh3 flock D εt)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation rows input q) :
    (stagedU3 flock D input rows q).Holds D (uniProverRec3RP flock D) input rows q
      (BadFp (honestTrace D input rows q)) (BadT D.shape) Nbad ct (Cost.setupCost D + (NP + NV)) εt
      (((Cost.setupCost D + (NP + NV) : ℕ) : ℝ≥0∞) *
        missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := experiment_staged3 flock D hc hv input rows q
  duplex := duplexVm_stagedU3 flock D hdup hvd input rows q hfit hrel
  cost := cost_stagedU3 flock D hcost hstream hvcost input rows q hfit hrel
  inp_length a := firstInput_length hfit.1 a.2
  hashA := hashA_stagedU3 flock D input rows q
  badCard := hbad input rows q hfit hrel
  badTCard := hbadT
  tFresh := htf input rows q hfit hrel
  rejectGood := rejectGood3 flock D hc hv hf hacc hpow input rows q hfit hrel
    (cost_stagedU3 flock D hcost hstream hvcost input rows q hfit hrel)

/-- **`UniCompletenessRec3` from the named hypotheses**, for every deployment. -/
theorem uniCompletenessRec3_of_core {Nbad ct NP S NV : ℕ} {εt : ℝ≥0∞} (hc : ProverCommutes3 flock D)
    (hf : FlockSimCommutes flock) (hdup : ProverDuplex3 flock D) (hcost : ProverCost3 flock D NP)
    (hstream : ProverStreamSize3 flock D S) (hv : VerifierCommutes3) (hvd : VerifierDisc3)
    (hvcost : VerifierCost3 D S NV) (hacc : CoreAccepts3 D flock) (hpow : CoreFailsOnlyAtPow3 D flock)
    (hbad : BadFpCard D Nbad) (hbadT : BadTCard D.shape ct) (htf : TQueryFresh3 flock D εt) :
    UniCompletenessRec3 D (uniProverRec3RP flock D)
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) +
        ((Cost.setupCost D + (NP + NV) : ℕ) : ℝ≥0∞) *
          missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel +
        rpmError (Cost.setupCost D + (NP + NV))) :=
  uniCompletenessRec3_of_staged fun input rows q hfit hrel ↦
    ⟨stagedU3 flock D input rows q, _, _,
      stagedU3_holds flock D hc hf hdup hcost hstream hv hvd hvcost hacc hpow hbad hbadT htf input rows q hfit
        hrel⟩

/-- A larger error is still an error. -/
theorem UniCompletenessRec3.mono {P : UniProver D} {δ δ' : ℝ≥0∞} (h : UniCompletenessRec3 D P δ)
    (hδ : δ ≤ δ') : UniCompletenessRec3 D P δ' :=
  fun input rows q hfit hrel ↦ (h input rows q hfit hrel).trans hδ

/-! ## The block count at the reference shape -/

/-- **The setup's block count at the reference shape** (the main line's `totalCost_le`'s first step: its layout has
at most `24` variables, `Prob.setupLayout_reference_vars`). -/
theorem setupCost_le (hD : D.shape = reference) : Cost.setupCost D ≤ 5 * 2 ^ 19 + 2 * (5 * 2 ^ 23) := by
  have hv := Prob.setupLayout_reference_vars
  have hp : 2 ^ ((setupLayout D.shape).vars - 6 + 1) ≤ 2 ^ 19 := by
    rw [hD]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : 2 ^ (matrixVars - 6 + 1) = 2 ^ 23 := rfl
  unfold Cost.setupCost
  omega

/-- **The block count at the reference shape**: below `2^48`, for a prover of `2^47` block calls and a verifier of
at most `2^43`. -/
theorem totalCost3_le (hD : D.shape = reference) {NV : ℕ} (hNV : NV ≤ 2 ^ 43) :
    Cost.setupCost D + (2 ^ 47 + NV) ≤ 2 ^ 48 := by
  have := setupCost_le D hD
  omega

/-! ## The numbers -/

/-- **π1-rec3's deployed bound**: `Nbad = 2^24 − 1` bad `β` per `α`, `3 · 2^17` bad `t` per Flock point, `t`'s cache
hit `2^-200`, `2^48` block calls (the grinding's `2^-304`, the transfer's `(2^48)² / 2^508`). -/
noncomputable def deltaRec3 : ℝ≥0∞ :=
  ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) +
    (2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)

/-- `2⁻¹ ^ (n + 1) + 2⁻¹ ^ (n + 1) = 2⁻¹ ^ n`. -/
theorem inv_pow_succ_add_self (n : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 1) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  calc (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 1) = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
        rw [← two_mul, pow_one]
    _ = (2 : ℝ≥0∞)⁻¹ ^ n := E2ECompleteness.two_pow_mul_inv_pow 1 n

/-- **The bound, finely**: `deltaRec3 < 2^-168 + 2^-173` (the bus challenges' `(2^24 − 1)/2^192 ≤ 2^-168`; `t`'s
`3 · 2^-175`, the rest below `2^-175`). -/
theorem deltaRec3_lt_fine : deltaRec3 < (2 : ℝ≥0∞)⁻¹ ^ 168 + (2 : ℝ≥0∞)⁻¹ ^ 173 := by
  have ha : ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 168 := by
    calc ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 24 * (2 : ℝ≥0∞)⁻¹ ^ (168 + 24) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 168 := E2ECompleteness.two_pow_mul_inv_pow 24 168
  have hct : ((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 = 3 * (2 : ℝ≥0∞)⁻¹ ^ 175 := by
    calc ((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 = 3 * (2 ^ 17 * (2 : ℝ≥0∞)⁻¹ ^ (175 + 17)) := by
          rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
          push_cast
          ring
      _ = 3 * (2 : ℝ≥0∞)⁻¹ ^ 175 := by rw [E2ECompleteness.two_pow_mul_inv_pow 17 175]
  have hc : (2 : ℝ≥0∞)⁻¹ ^ 304 ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hd : rpmError (2 ^ 48) ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := by
    calc rpmError (2 ^ 48) = 2 ^ (48 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (412 + 48 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul,
            ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 412 := E2ECompleteness.two_pow_mul_inv_pow _ 412
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  -- The rest, below `2^-175`.
  have hrest : (2 : ℝ≥0∞)⁻¹ ^ 200 + ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)) < (2 : ℝ≥0∞)⁻¹ ^ 175 := by
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 + ((2 : ℝ≥0∞)⁻¹ ^ 200 + (2 : ℝ≥0∞)⁻¹ ^ 200) := add_le_add le_rfl (add_le_add hc hd)
      _ = 3 * (2 : ℝ≥0∞)⁻¹ ^ (198 + 2) := by ring
      _ ≤ 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (198 + 2) := by
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 198 := E2ECompleteness.two_pow_mul_inv_pow 2 198
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (175 + 1) := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
      _ < (2 : ℝ≥0∞)⁻¹ ^ (175 + 1) + (2 : ℝ≥0∞)⁻¹ ^ (175 + 1) := ENNReal.lt_add_right (by simp) (by simp)
      _ = (2 : ℝ≥0∞)⁻¹ ^ 175 := inv_pow_succ_add_self 175
  -- `t`'s term and the rest, below `4 · 2^-175 = 2^-173`.
  have hne3 : 3 * (2 : ℝ≥0∞)⁻¹ ^ 175 ≠ ⊤ := ENNReal.mul_ne_top (by simp) (by simp)
  have hmid : ((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 + ((2 : ℝ≥0∞)⁻¹ ^ 200 +
      ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48))) < (2 : ℝ≥0∞)⁻¹ ^ 173 := by
    rw [hct]
    calc _ < 3 * (2 : ℝ≥0∞)⁻¹ ^ 175 + (2 : ℝ≥0∞)⁻¹ ^ 175 :=
          ENNReal.add_lt_add_of_le_of_lt hne3 le_rfl hrest
      _ = 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (173 + 2) := by ring
      _ = (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.two_pow_mul_inv_pow 2 173
  have hne : ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≠ ⊤ := ne_top_of_le_ne_top (by simp) ha
  have hsum : deltaRec3 = ((2 ^ 24 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 +
      ((2 : ℝ≥0∞)⁻¹ ^ 200 + ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)))) := by
    unfold deltaRec3
    ac_rfl
  rw [hsum]
  exact ENNReal.add_lt_add_of_le_of_lt hne ha hmid

/-- **The bound**: `deltaRec3 < 2^-167` (about `2^-167.967`). -/
theorem deltaRec3_lt : deltaRec3 < (2 : ℝ≥0∞)⁻¹ ^ 167 := by
  refine deltaRec3_lt_fine.trans_le ?_
  calc (2 : ℝ≥0∞)⁻¹ ^ 168 + (2 : ℝ≥0∞)⁻¹ ^ 173 ≤ (2 : ℝ≥0∞)⁻¹ ^ (167 + 1) + (2 : ℝ≥0∞)⁻¹ ^ (167 + 1) :=
        add_le_add le_rfl (E2ECompleteness.inv_pow_le_inv_pow (by norm_num))
    _ = (2 : ℝ≥0∞)⁻¹ ^ 167 := inv_pow_succ_add_self 167

/-! ## The end theorem -/

/-- **`UniCompletenessRec3` at the reference shape**, `deltaRec3 < 2^-167`, from the named hypotheses (Flock's
prover's commutation `FlockCommutes` giving `FlockSimCommutes`) at `NP = 2^47` prover block calls, `S = 2^40` stream
bytes, a verifier of `NV ≤ 2^43` block calls on such streams, `t`'s cache hit `εt = 2^-200`; the bad sets' counts are
the main line's, proved (`Core.badFpCard_reference`: `2^24 − 1` bad `β` per `α`; `Prob.badTCard_reference`:
`3 · 2^17` bad `t` per Flock point). -/
theorem uniCompletenessRec3_reference (hD : D.shape = reference) (hflock : FlockCommutes flock)
    (hc : ProverCommutes3 flock D) (hdup : ProverDuplex3 flock D) (hcost : ProverCost3 flock D (2 ^ 47))
    (hstream : ProverStreamSize3 flock D (2 ^ 40)) (hv : VerifierCommutes3) (hvd : VerifierDisc3) {NV : ℕ}
    (hvcost : VerifierCost3 D (2 ^ 40) NV) (hNV : NV ≤ 2 ^ 43) (hacc : CoreAccepts3 D flock)
    (hpow : CoreFailsOnlyAtPow3 D flock) (htf : TQueryFresh3 flock D ((2 : ℝ≥0∞)⁻¹ ^ 200)) :
    UniCompletenessRec3 D (uniProverRec3RP flock D) deltaRec3 := by
  have hbadT : BadTCard D.shape (3 * 2 ^ 17) := hD ▸ Prob.badTCard_reference
  refine UniCompletenessRec3.mono D
    (uniCompletenessRec3_of_core flock D hc (flockSimCommutes_of_commutes hflock) hdup hcost hstream hv hvd
      hvcost hacc hpow (Core.badFpCard_reference D hD) hbadT htf) ?_
  have hN := totalCost3_le D hD hNV
  set N := Cost.setupCost D + (2 ^ 47 + NV)
  unfold deltaRec3
  gcongr
  · calc (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel
        ≤ ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
          gcongr
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 304 := E2ECompleteness.grinding_le
  · exact Prob.rpmError_mono hN

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.prEvent_staged2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.prEvent_staged2_le

/-- info: 'UniComplete.Rec3.uniCompletenessRec3_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.uniCompletenessRec3_of_staged

/-- info: 'UniComplete.Rec3.experiment_staged3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.experiment_staged3

/-- info: 'UniComplete.Rec3.duplexVm_stagedU3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.duplexVm_stagedU3

/-- info: 'UniComplete.Rec3.cost_stagedU3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.cost_stagedU3

/-- info: 'UniComplete.Rec3.hashA_stagedU3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.hashA_stagedU3

/-- info: 'UniComplete.Rec3.rejectGood3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.rejectGood3

/-- info: 'UniComplete.Rec3.uniCompletenessRec3_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.uniCompletenessRec3_of_core

/-- info: 'UniComplete.Rec3.deltaRec3_lt_fine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.deltaRec3_lt_fine

/-- info: 'UniComplete.Rec3.deltaRec3_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.deltaRec3_lt

/-- info: 'UniComplete.Rec3.uniCompletenessRec3_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.uniCompletenessRec3_reference
