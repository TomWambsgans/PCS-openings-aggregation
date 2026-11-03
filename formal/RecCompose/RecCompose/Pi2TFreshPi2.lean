-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Pi2TFresh.lean`'s `tFresh_of` at π2's staged run
-- (`RecCompose.Pi2ProbStaged`'s `pi2Staged`: `stageB`, `mid2`, `crates/leanvm_rec/src/pi2/prover.rs`'s `Q` and `t`);
-- uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0).
import RecCompose.Pi2TFresh

/-!
# `Pi2TFresh`, proved from `α`'s freshness

* **`Pi2AlphaFresh D C Fa P1k εα`** (named, replacing `Pi2HashBeforeAlpha`, which is false at `p1k`, `Pi2Chain`): in
  the two-call random-oracle model, `α`'s input (`inp`, the state after the seed and π1's public data and `W`'s root,
  `536` bytes) is already hashed after stage A with probability at most `εα`.
* **`stageB_eq`**: stage B is `Q`'s tree (`commitWithH`) then a pure writer, whose `t` input is `s₃`'s bytes and `Q`'s
  root word (**`tin_stageB`**, `64` bytes).
* **`pi2TFresh_of`**: `Pi2TFresh D C Fa P1k (tFreshBound2 N εα)`, `tFreshBound2 N εα = εα + (4N + 6 + treeCost μQ) /
  2^256`, for every `P1k`, from `Pi2RunCost D C Fa P1k N` and `Pi2AlphaFresh D C Fa P1k εα`;
  **`tFreshBound2_le`**: below `2^-200` at `N ≤ 2^50`, `εα ≤ 2^-201`.
* **`recCompleteness2_pi2_staged2`**: π2's completeness from `Pi2ProbStaged`'s named facts with `Pi2HashBeforeAlpha` and
  `Pi2TFresh` replaced by `Pi2AlphaFresh`, error `delta2' N εα (tFreshBound2 N εα) εpow`; **`delta2_pi2_le2`**: below
  `2^-164` at `N ≤ 2^50`, `εα ≤ 2^-201`. **`recCompleteness_pi2_staged2_fs`**: end to end.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2G

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open E2ECompleteness (ro HashOK)
open UniComplete.Prob.TFresh (HC hc_of_qc take_digestBytes)
open Pi2S Pi2K Pi2P Pi2E
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Stage B -/

/-- `Q`'s stack at stage A's output and the triple's hashes. -/
noncomputable def qStackOf {D : RecDeployment} (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest) : Array K :=
  placePublic (layoutsOf (C.G a.roots).logN).2.1 (qEntry (C.G a.roots).logN
    (hNovel (C.G a.roots) a.vw.2 (chalP s₁) (chalP s₂) (chalP s₃))
    (qNovel (C.G a.roots) a.vw.2 (chalP s₁) (chalP s₂) (chalP s₃)))

/-- **Stage B's tree**: `Q`'s commitment. -/
noncomputable def treeB {D : RecDeployment} (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest) :
    OracleComp KeccakCalls LeanVM.Prover.Tree :=
  E2ECompleteness.commitWithH callKeccak256 (layoutsOf (C.G a.roots).logN).2.1.logN (qStackOf C a s₁ s₂ s₃)

/-- **Stage B's writer** after the tree. -/
noncomputable def outB {D : RecDeployment} (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest)
    (qT : LeanVM.Prover.Tree) : StB :=
  ⟨a, chalP s₁, chalP s₂, chalP s₃, qStackOf C a s₁ s₂ s₃, qT,
    { absorbW (absorbW (absorbW a.wr s₁) s₂) s₃ with
      stream := (absorbW (absorbW (absorbW a.wr s₁) s₂) s₃).stream ++ (UniStatement.rootWord (digestScalars qT.root)).toArray }⟩

/-- **Stage B is `Q`'s tree, then a pure writer.** -/
theorem stageB_eq (D : RecDeployment) (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest) :
    stageB callKeccak256 D C a s₁ s₂ s₃ = treeB C a s₁ s₂ s₃ >>= fun qT ↦ pure (outB C a s₁ s₂ s₃ qT) := by
  unfold stageB mid2 treeB outB qStackOf
  simp only [StateT.run_bind, StateT.run_lift, UniComplete.Prob.run_sendRoot, bind_assoc, pure_bind, StateT.run_pure]

/-- **`t`'s input after stage B**: `s₃`'s bytes, then `Q`'s root word. -/
theorem tin_stageB {D : RecDeployment} (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest) (qT : LeanVM.Prover.Tree) :
    UniComplete.Prob.tInput (outB C a s₁ s₂ s₃ qT).wr = digestBytes s₃ ++ UniStatement.rootWord (digestScalars qT.root) := by
  simp [UniComplete.Prob.tInput, outB, absorbW]

theorem tin_stageB_length {D : RecDeployment} (C : Pi2Circuits D) (a : StA) (s₁ s₂ s₃ : Digest)
    (qT : LeanVM.Prover.Tree) : (UniComplete.Prob.tInput (outB C a s₁ s₂ s₃ qT).wr).length = 64 ∧
      (UniComplete.Prob.tInput (outB C a s₁ s₂ s₃ qT).wr).take 32 = digestBytes s₃ := by
  rw [tin_stageB]
  refine ⟨?_, take_digestBytes _ _⟩
  rw [List.length_append, E2ECompleteness.length_digestBytes, UniComplete.Prob.rootWord_length]

/-! ## The named input and `t`'s freshness -/

/-- **Named: `α`'s input is fresh** (replaces `Pi2HashBeforeAlpha`, false at π1-rec3's prover, which hashes `32`-byte
inputs, `Pi2Chain`): in the two-call random-oracle model, `α`'s input (`536` bytes: the state after the seed, π1's
public data, `W`'s root) is already hashed after stage A (the setup, `P1k`, π1-rec3's graph and its openings, π2's
prover up to `W`'s root) with probability at most `εα`. -/
def Pi2AlphaFresh (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    (εα : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let p ← (simulateQ ro (pi2Staged D C Fa (P1k input rows q) input).A).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa (P1k input rows q) input).inp p.1)) ≠ none] ≤ εα

/-- `Q`'s tree's height parameter. -/
abbrev muQ : ℕ := (layoutsOf 24).2.1.logN

/-- **`t`'s cache-hit bound**: `εα` and `(4N + 6 + |Q's tree|) / 2^256`. -/
noncomputable def tFreshBound2 (N : ℕ) (εα : ℝ≥0∞) : ℝ≥0∞ :=
  εα + ((4 * N + 6 + E2ECompleteness.Cost.treeCost muQ : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- **`Pi2TFresh`, from the run's cost and `α`'s freshness**, for every `P1k`. -/
theorem pi2TFresh_of {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εα : ℝ≥0∞} (hcost : Pi2RunCost D C Fa P1k N) (hα : Pi2AlphaFresh D C Fa P1k εα) :
    Pi2TFresh D C Fa P1k (tFreshBound2 N εα) := by
  intro input rows q hfit hrel
  refine TF.tFresh_of (pi2Staged D C Fa (P1k input rows q) input) (fun a s₁ s₂ s₃ ↦ treeB C a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ qT ↦ outB C a s₁ s₂ s₃ qT) (fun a s₁ s₂ s₃ ↦ stageB_eq D C a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ ↦ TF.apq_commitWithH _ _ _ (List.mem_singleton_self _))
    (fun a s₁ s₂ s₃ ↦ UniComplete.Prob.HashOK.mono (fun m h ↦ h.1) (E2ECompleteness.hashOK_commitWithH _ _))
    (NT := E2ECompleteness.Cost.treeCost muQ)
    (fun a s₁ s₂ s₃ ↦ by
      unfold treeB E2ECompleteness.Cost.treeCost
      rw [logN_G Fa]
      exact hc_of_qc (E2ECompleteness.Cost.qc_commitWithH _ _))
    (fun a s₁ s₂ s₃ qT ↦ tin_stageB_length C a s₁ s₂ s₃ qT) (by norm_num : (536 : ℕ) ≠ 32)
    (fun a ↦ fixLen_length 536 _) ((pi2Staged D C Fa (P1k input rows q) input).hc_A (hcost input rows q hfit hrel))
    (hα input rows q hfit hrel) |>.trans (le_of_eq ?_)
  unfold tFreshBound2
  rfl

theorem muQ_le : muQ ≤ 40 := by decide

/-- **`t`'s bound in bits**: below `2^-200` at `N ≤ 2^50`, `εα ≤ 2^-201`. -/
theorem tFreshBound2_le {N : ℕ} {εα : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 201) :
    tFreshBound2 N εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := by
  have hT : E2ECompleteness.Cost.treeCost muQ ≤ 2 ^ 38 := by
    unfold E2ECompleteness.Cost.treeCost
    calc 5 * 2 ^ (muQ - 6 + 1) ≤ 2 ^ 3 * 2 ^ 35 := by
          gcongr
          · norm_num
          · have := muQ_le; omega
      _ = 2 ^ 38 := by norm_num
  have hb : ((4 * N + 6 + E2ECompleteness.Cost.treeCost muQ : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 := by
    calc ((4 * N + 6 + E2ECompleteness.Cost.treeCost muQ : ℕ) : ℝ≥0∞) / 2 ^ 256
        ≤ ((2 ^ 55 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (201 + 55) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          exact_mod_cast (show 4 * N + 6 + E2ECompleteness.Cost.treeCost muQ ≤ 2 ^ 55 by omega)
      _ = (2 : ℝ≥0∞)⁻¹ ^ 201 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact E2ECompleteness.two_pow_mul_inv_pow 55 201
  unfold tFreshBound2
  calc εα + _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 + (2 : ℝ≥0∞)⁻¹ ^ 201 := add_le_add ha hb
    _ = (2 : ℝ≥0∞)⁻¹ ^ 200 := by
        rw [← two_mul, show (201 : ℕ) = 1 + 200 from rfl, pow_add, ← mul_assoc, pow_one,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-! ## π2's completeness, `α`'s input fresh -/

/-- **The staged run's `Holds2`**, at the real deployment's facts: `holds_pi2`'s fields, `α`'s freshness for `hashA`,
`t`'s freshness proved. -/
theorem holds2_pi2 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εα : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows)
    (hrel : D.pi1.HonestRelation rows input q) :
    (pi2Staged D C (pi2Facts hD C hchk) (P1k input rows q) input).Holds2 D P1
      (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel) input rows q 536 (badSet2 C.G) (badT2 C.G)
      (2 ^ 25 + 36) (2 ^ 27) N εα (tFreshBound2 N εα)
      ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := hexp input rows q hfit hrel
  duplex := hdup input rows q hfit hrel
  cost := hcost input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 536 _
  alphaFresh := hal input rows q hfit hrel
  badCard p := card_badCopy_pi2 (pi2Facts hD C hchk) p.1 p.2.1 p.2.2
  badTCard fp := card_badT_pi2 (pi2Facts hD C hchk) fp.1.1 fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    (nonHole_pi2 C hchk (pi2Facts hD C hchk) fp.1.1)
  tFresh := pi2TFresh_of C (pi2Facts hD C hchk) P1k hcost hal input rows q hfit hrel
  rejectGood := rejectGood_pi2 hD C (pi2Facts hD C hchk) hroots hwc hpo P1k hrun input rows q
    (hcost input rows q hfit hrel)

/-- **π2's completeness, `α`'s input fresh** (`recCompleteness2_pi2_staged` with `Pi2HashBeforeAlpha`, false at
`p1k`, replaced by `Pi2AlphaFresh εα`, and `Pi2TFresh` proved). -/
theorem recCompleteness2_pi2_staged2 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εα : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' N εα (tFreshBound2 N εα) ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_of_staged2 fun input rows q hfit hrel ↦
    ⟨_, _, _, holds2_pi2 hD C hchk hroots P1 P1k hexp hrun hdup hcost hal hpo hwc input rows q hfit hrel⟩

/-- **`δ2` in bits**, `α`'s input fresh: below `2^-164` at `N ≤ 2^50` block calls and `εα ≤ 2^-201`. -/
theorem delta2_pi2_le2 {N : ℕ} {εα : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 201) :
    delta2' N εα (tFreshBound2 N εα) ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  delta2'_le hN (ha.trans (E2ECompleteness.inv_pow_le_inv_pow (by norm_num))) (tFreshBound2_le hN ha) (grind_le hN)

/-- **The recursive verifier's completeness end to end**, `α`'s input fresh. -/
theorem recCompleteness_pi2_staged2_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εα : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' N εα (tFreshBound2 N εα)
        ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD P1 _ _
    (recCompleteness2_pi2_staged2 hD C hchk hroots P1 P1k hexp hrun hdup hcost hal hpo hwc) δ1 δh h1 hh

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2G.pi2TFresh_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.pi2TFresh_of

/-- info: 'RecCompose.Pi2G.recCompleteness2_pi2_staged2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.recCompleteness2_pi2_staged2

/-- info: 'RecCompose.Pi2G.delta2_pi2_le2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.delta2_pi2_le2

/-- info: 'RecCompose.Pi2G.recCompleteness_pi2_staged2_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.recCompleteness_pi2_staged2_fs
