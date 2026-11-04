-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at the recursion's π1 prover (`Pi1KF.pi1Rec3ProverKF`: its Fiat–Shamir over
-- the real Keccak-f[1600], its trees and openings over `π`), redone on `Pi2AlphaEnd`'s ingredients: `Pi2SimExp`
-- (`expW2_event_staged`, `perm_kc`), `Pi2AlphaFresh` (`prA_le`), `Pi2RunDuplex` (`disc_pi2Staged`), `Pi2RunCost`
-- (`qc_pi2Staged`), `Pi2AlphaG`, `Pi2AlphaSupport`; the prover's facts from `Pi1KFTransfer`.
import RecCompose.Pi2AlphaEnd
import RecCompose.Pi2SimExp
import RecCompose.Pi1KFTransfer

/-!
# π2's completeness at the recursion's π1 prover (statement review, finding 4)

`Pi2Alpha.recCompleteness2_pi2_rec3_closed` is stated at `Pi2G.pi1Rec3Prover D`, whose Fiat–Shamir is over the random
permutation; π1-rec3's graph hashes with the real Keccak-f[1600], so its event "the graph accepts" has probability
about `2^-180` there (`Review/STATEMENT_REVIEW.md`, finding 4). Here the same theorems at `Pi1KF.pi1Rec3ProverKF D`, the
prover the recursion runs: its Fiat–Shamir the pure `keccak256` (the graph's), its trees and WHIR openings over `π`. Its
honest proofs are the ones the graph accepts (`Pi1KFCore`), so the event bounded is the contract's rejection of an honest
proof.

The staged argument is unchanged: every piece of `pi2Staged` is generic in π1's two-call program, which is now
`Pi1KF.p1kKF D` (`Pi1KF.pi1Rec3ProverKF_eq`). Its facts:

* **`experiment_eq_kf`**, **`pi2ExperimentLe_kf`**: π2's experiment at `pi1Rec3ProverKF` is `expW2` over the two calls
  at `p1kKF`, answered over `π` (`Pi1KF.simulateQ_p1kKF`); the rest is `Pi2SimExp`'s.
* the duplex discipline (`Pi1KF.disc_p1kKF`), the block count (`Pi1KF.qc_p1kKF`: at most `2^47`, UniComplete's
  prover's, its Fiat–Shamir now no call), the census before `σ` (`Pi1KF.hashOK_p1kKF_of` of `Pi2A.hashOK_p1k`): each
  transferred from UniComplete's prover (`Pi1KFTransfer`).
* **`alphaFresh_kf`**: `α`'s input cached while the graph accepted, at most `alphaBound`, as before. **The census is
  simpler**: π1's Fiat–Shamir hashes (its IV, seed, stream challenges, Flock's) are no queries of the random oracle now;
  the inputs hashed before `σ` are the setup's trees (twice), π1's trees and WHIR openings, the graph's three
  `PCS_OPEN`s. The bound `K ≤ 2 · setupR + 2^47 + 3 · gOpen + 4` is kept (the prover's `2^47` is nearly all its three
  WHIR provers', about `2^46.70`; its Fiat–Shamir was about `150` blocks of it).

**The numbers** (`εα`, `εt`, `δ2`) are the ones of `Pi2AlphaEnd`, since every count they use bounds the new prover's:
`εα = alphaBound = 4 · (2 · setupR + 2^47 + 3 · gOpen + 4) / 2^256 ≈ 2^-207.0` (`alphaBound_le`: `≤ 2^-204`),
`εt = tFreshBound2 pi2RunN alphaBound ≤ 2^-200`, `δ2 = delta2' … ≤ 2^-164` (**`delta2_kf_le`**; about `2^-164.7`).

* **`recCompleteness2_pi2_rec3_kf`**: `RecCompleteness2 D (pi1Rec3ProverKF D) (pi2Prover …) δ2` from `Pi2Circuits D`,
  `hroots`, `GraphsAgree`, `Pi2ViewChecked C` only;
* **`recCompleteness_pi2_rec3_kf_fs`**: the recursive verifier's completeness end to end at `pi1Rec3ProverKF`, with the
  Fiat–Shamir premises `Pi1CompletenessKeccak D (pi1Rec3ProverKF D) δ1` (now the honest-prover Fiat–Shamir heuristic:
  prover and verifier at the same Keccak-f[1600], `Pi1KFRpm`) and `Pi1HazardKeccakHonest D (pi1Rec3ProverKF D) δh`.

`Pi2Alpha.recCompleteness2_pi2_rec3_closed` and `recCompleteness_pi2_rec3_closed_fs` (at `Pi2G.pi1Rec3Prover`) are
kept, **superseded** by these.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2KF

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open E2ECompleteness (runAt)
open PcsQuotient.EndToEnd.Eager
open UniComplete.Prob.TFresh (hc_of_qc)
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2O Pi2Sim
open Pi1KF (pi1Rec3ProverKF p1kKF)
open scoped ENNReal

/-! ## The experiment -/

/-- **π2's experiment at the recursion's π1 prover is `expW2` over the two calls at `p1kKF`, answered over `π`.** -/
theorem experiment_eq_kf (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) :
    recCompletenessExperiment2 D (pi1Rec3ProverKF D) (pi2Prover D C Fa PcsQuotient.nonceFuel) input rows q =
      runWithRandomPermutation (simulateQ keccakCallsOverQueryPermutation
        (expW2 callKeccak256 callKeccakF1600 D C Fa (p1kKF D input rows q) input)) := by
  rw [sim_expW2, implH_kc, implF_kc, ← Pi1KF.pi1Rec3ProverKF_eq]
  unfold recCompletenessExperiment2 expW2
  congr 1
  rw [Pi2H.setupTreesWith_eqH]
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => rfl
  | some p1 =>
    simp only [Pi2H.pi1GraphVerifierWith_eqH]
    refine bind_congr fun a1 ↦ ?_
    unfold pi2Prover
    refine bind_congr fun r ↦ ?_
    cases r with
    | none => rfl
    | some p2 => simp only [Pi2H.verifierWith_eqH]

/-- **`Pi2ExperimentLe` at the recursion's π1 prover**, from the witness's completeness. -/
theorem pi2ExperimentLe_kf {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hwc : Pi2WitnessComplete D C Fa) : Pi2ExperimentLe D C Fa (pi1Rec3ProverKF D) (p1kKF D) := by
  intro input rows q _ _
  rw [experiment_eq_kf, staged_eq_kc, prEvent_runWithRandomPermutation, prEvent_runWithRandomPermutation]
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun π _ ↦ ?_)
  rw [perm_kc, perm_kc, prEvent_pure, prEvent_pure]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (expW2_event_staged hD C Fa hwc input (p1kKF D input rows q) (hOf π) (⇑π) h1) h2
  · exact zero_le
  · exact le_rfl

/-! ## The staged run's facts -/

theorem hIv_real {D : RecDeployment} (hD : D.Real) : D.pi1.programIv.length ≤ 2 ^ 16 := by
  rw [hD.2.2.2.1, Cost2.programIv_length]
  norm_num

/-- **The staged run at the recursion's π1 prover is disciplined.** -/
theorem pi2RunDuplex_kf (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) :
    Pi2RunDuplex D C Fa (p1kKF D) := fun input rows q _ _ ↦
  (duplexVm_iff_duplexP _ _).mpr (disc_pi2Staged D C Fa _ (Pi1KF.disc_p1kKF D input rows q) input [])

/-- **The staged run at the recursion's π1 prover makes at most `pi2RunN ≤ 2^50` block calls.** -/
theorem pi2RunCost_kf {D : RecDeployment} (hD : D.Real) (hg : GraphsAgree) (C : Pi2Circuits D) (Fa : Pi2Facts D C) :
    Pi2RunCost D C Fa (p1kKF D) Cost2.pi2RunN := fun input rows q hfit hrel ↦
  Cost2.qc_pi2Staged hD hg C Fa _ (Pi1KF.qc_p1kKF D hD.2.2.1 (hIv_real hD) input rows q hfit hrel) input

/-- **`α`'s input is fresh while the graph accepts**, at the recursion's π1 prover: at most `alphaBound ≤ 2^-204`. -/
theorem alphaFresh_kf {D : RecDeployment} (hD : D.Real) (hg : GraphsAgree) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (hfit : D.pi1.shape.RowsFit rows) (hrel : D.pi1.HonestRelation rows input q) :
    Pr{let p ← (simulateQ E2ECompleteness.ro (pi2Staged D C (pi2Facts hD C hchk) (p1kKF D input rows q) input).A).run ∅}[
      p.2 (.inl ((pi2Staged D C (pi2Facts hD C hchk) (p1kKF D input rows q) input).inp p.1)) ≠ none ∧ GAcc p.1] ≤
      alphaBound := by
  have hwc := Pi2W.pi2WitnessComplete hD C hchk
  refine (prEvent_mono_of_support _ _ (fun p ↦ p.2 (.inl (rawInp p.1)) ≠ none ∧ (rawInp p.1).length = 536)
    fun p hp hev ↦ ?_).trans ?_
  · have hl := gAcc_length C (pi2Facts hD C hchk) input hD hwc _ hp hev.2
    have e : (pi2Staged D C (pi2Facts hD C hchk) (p1kKF D input rows q) input).inp p.1 = rawInp p.1 := by
      show fixLen 536 (UniComplete.Prob.tInput p.1.wr) = _
      unfold fixLen
      simp only [hl, ↓reduceIte]
    have h1 := hev.1
    rw [e] at h1
    exact ⟨h1, hl⟩
  · exact prA_le hD hg C _ _ input
      (Pi1KF.hashOK_p1kKF_of D input rows q _ (Pi2A.hashOK_p1k hD input rows q hfit hrel))
      (hc_of_qc (Pi1KF.qc_p1kKF D hD.2.2.1 (hIv_real hD) input rows q hfit hrel))

/-- **The staged run's `Holds3`** at the recursion's π1 prover, `α`'s and `t`'s freshness where the graph accepted. -/
theorem holds3_pi2_kf {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows) (hrel : D.pi1.HonestRelation rows input q) :
    (pi2Staged D C (pi2Facts hD C hchk) (p1kKF D input rows q) input).Holds3 D (pi1Rec3ProverKF D)
      (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel) input rows q 536 (badSet2 C.G) (badT2 C.G)
      GAcc (fun b : StB ↦ GAcc b.a) (2 ^ 25 + 36) (2 ^ 27) Cost2.pi2RunN alphaBound
      (tFreshBound2 Cost2.pi2RunN alphaBound)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := pi2ExperimentLe_kf hD C (pi2Facts hD C hchk) (Pi2W.pi2WitnessComplete hD C hchk) input rows q
    hfit hrel
  duplex := pi2RunDuplex_kf D C _ input rows q hfit hrel
  cost := pi2RunCost_kf hD hg C _ input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 536 _
  alphaFresh := alphaFresh_kf hD hg C hchk input rows q hfit hrel
  accA := fun a ha s₁ s₂ s₃ c z hz ↦ accA_pi2 C (pi2Facts hD C hchk) input (p1kKF D input rows q) a ha s₁ s₂ s₃ c z hz
  accB := fun b hb st c z hz ↦ accB_pi2 C input b hb st c z hz
  badCard p := card_badCopy_pi2 (pi2Facts hD C hchk) p.1 p.2.1 p.2.2
  badTCard fp := card_badT_pi2 (pi2Facts hD C hchk) fp.1.1 fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    (nonHole_pi2 C hchk (pi2Facts hD C hchk) fp.1.1)
  tFresh := pi2TFresh_ofG C (pi2Facts hD C hchk) (p1kKF D input rows q) input
    (pi2RunCost_kf hD hg C _ input rows q hfit hrel) GAcc (alphaFresh_kf hD hg C hchk input rows q hfit hrel)
  rejectGood := rejectGood_pi2_good hD C (pi2Facts hD C hchk) hroots (Pi2W.pi2WitnessComplete hD C hchk)
    (pi2Pi1Openings hD C hchk hroots hg) (p1kKF D input rows q) input (pi2RunCost_kf hD hg C _ input rows q hfit hrel)

/-! ## The end theorems -/

/-- **π2's completeness at the recursion's π1 prover** (its Fiat–Shamir over Keccak-f[1600], its openings over `π`),
from the run-checked inputs only (`Pi2Circuits D`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C`). -/
theorem recCompleteness2_pi2_rec3_kf {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) :
    RecCompleteness2 D (pi1Rec3ProverKF D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN alphaBound (tFreshBound2 Cost2.pi2RunN alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_of_staged3 fun input rows q hfit hrel ↦
    ⟨_, _, _, _, _, holds3_pi2_kf hD C hchk hroots hg input rows q hfit hrel⟩

/-- **δ2 in bits**: below `2^-164` (as `Pi2Alpha.delta2_alpha_le`: the same bound). -/
theorem delta2_kf_le :
    delta2' Cost2.pi2RunN alphaBound (tFreshBound2 Cost2.pi2RunN alphaBound)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  Pi2Alpha.delta2_alpha_le

/-- **The recursive verifier's completeness end to end** at the recursion's π1 prover, from the run-checked inputs and
the Fiat–Shamir premises (π1-rec3's completeness at Keccak-f[1600] for this prover, its honest proofs off the merge
hazard). -/
theorem recCompleteness_pi2_rec3_kf_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D (pi1Rec3ProverKF D) δ1)
    (hh : Pi1HazardKeccakHonest D (pi1Rec3ProverKF D) δh) :
    RecCompletenessWith D (composeProver D (pi1Rec3ProverKF D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN alphaBound (tFreshBound2 Cost2.pi2RunN alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD (pi1Rec3ProverKF D) _ _
    (recCompleteness2_pi2_rec3_kf hD C hchk hroots hg) δ1 δh h1 hh

end RecCompose.Pi2KF

/-- info: 'RecCompose.Pi2KF.recCompleteness2_pi2_rec3_kf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2KF.recCompleteness2_pi2_rec3_kf

/-- info: 'RecCompose.Pi2KF.delta2_kf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2KF.delta2_kf_le

/-- info: 'RecCompose.Pi2KF.recCompleteness_pi2_rec3_kf_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2KF.recCompleteness_pi2_rec3_kf_fs
