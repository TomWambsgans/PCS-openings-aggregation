-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.Cost

/-!
# Compose's random-permutation theorem, the verifier's cost as a whole

`Compose/Rpm.lean`'s `rpm_le_wired` and `knowledgeSoundness_wired_setup_rpm_bits` take the openings'
calls of `π` as `hOπ : ∀ (L : Layout) w, QueryCostAtMost (ourVerifier L D.R w) hashBlocks QOπ`, for
**every** layout and statement, which no bound meets (a statement may hold `2^46` claims of any
length). Their proofs use it only through `cost_verifyD`, the deployed verifier's cost. Here the same
theorems take that cost directly (`hV`, met at the deployed claim maps by `cost_verifyD_deployD`),
their proofs `Rpm.lean`'s with `cost_verifyD` replaced:

* `cost_gameB_V`, `rpm_le_wired_V`: `cost_gameB`, `rpm_le_wired` with `hV`;
* **`knowledgeSoundness_rust_rpm`**: the random-permutation statement at the deployed claim maps
  (`deployD c 22`), F1's instance of `beta()` (`rustInstance`), the deployed wiring and the wiring
  stack `q₀`: `knowledgeSoundness_deployed_concrete` (`Compose/Claims.lean`) for the
  derandomized adversary, plus the transfer's `(2^52 + Q + verifierPermCalls)² / 2^508`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge
open LeanVM.Rpm (HOnly hashBlocks)

section Generic

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) (D : Deploy F)

/-- **The permutation calls of the transfer game**, the verifier's as a whole: the setup's `QSπ`,
the adversary's `Q`, the verifier's `QV` (`Rpm.lean`'s `cost_gameB`). -/
theorem cost_gameB_V (setup : OracleComp KeccakCalls Bytes32) (hS : HOnly setup) (QSπ : ℕ)
    (hSπ : Common.QueryCostAtMost setup hashBlocks QSπ)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs))
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q) (QV : ℕ)
    (hV : ∀ po, Common.QueryCostAtMost (verifyD W D po) hashBlocks QV) :
    Common.QueryCostAtMost (gameB W D setup A)
      (Common.queryCost2 (Dg := Common.DigestBytes) Common.keccakPadding)
      (QSπ + Q + QV) := by
  have h : Common.QueryCostAtMost (gameB W D setup A) LeanVM.Rpm.gameCost (QSπ + (Q + QV)) := by
    rw [gameB, Common.rpmGame2, preB, hEmbed2_toRH (loggedKC setup) (hOnly_loggedKC_run setup hS [])]
    refine (LeanVM.Rpm.isWeightBound_hfEmbed_toRHF (cost_loggedKC setup QSπ hSπ [])).bind
      fun x => ?_
    refine (LeanVM.Rpm.isWeightBound_advEmbed (cost_advB A Q hA x)).bind fun a => ?_
    rw [postB, simulateQ_map]
    exact Common.isWeightBound_map _ (LeanVM.Rpm.isWeightBound_hfEmbed_toRHF (hV _))
  exact h.mono (by omega)

/-- **From the random-permutation model to mumbai's two-oracle model** (`Rpm.lean`'s
`rpm_le_wired`), the verifier's cost as a whole. -/
theorem rpm_le_wired_V (c₁ : TableCode B.Msg₁) (setup : OracleComp KeccakCalls Bytes32)
    (hSH : HOnly setup) (QS QSπ : ℕ) (hS : IsTotalQueryBound setup QS)
    (hSπ : Common.QueryCostAtMost setup hashBlocks QSπ)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs))
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q) (QV : ℕ)
    (hV : ∀ po, Common.QueryCostAtMost (verifyD W D po) hashBlocks QV) :
    ∃ A' : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs),
      (∀ ir, IsTotalQueryBound (A' ir) (QS + Q)) ∧
        Pr{let z ← Common.runWithRandomPermutation (rpmGame W D setup A)}[BreaksRpm W c₁ z] ≤
          Pr{let z ← (simulateQ randomOracle (wiredExp W D (withSetup setup A'))).run' ∅}[
            BreaksW W c₁ z] + ((QSπ + Q + QV : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by
  obtain ⟨A', hA', hle⟩ := exists_det_setup setup QS hS (romAdvC A) Q (cost_romAdvC A Q hA)
    (gL W D) (BreaksC W c₁)
  refine ⟨A', hA', ?_⟩
  rw [prEvent_rpmGame, (rpmThreaded_evalDistEq W D setup hSH A).prEvent_eq]
  obtain ⟨ht, -⟩ := Common.keccak256_transfer2 (preB setup) (advB A) (postB W D)
    (duplex_postB W D) (QSπ + Q + QV) (cost_gameB_V W D setup hSH QSπ hSπ A Q hA QV hV)
    (BreaksT W c₁)
  exact ht.trans (add_le_add ((rom_le W D c₁ setup hSH A).trans
    (hle.trans (le_wiredExp W D c₁ setup A'))) le_rfl)

end Generic

/-! ## At the deployed claim maps -/

/-- The setup's calls of `π`: `2^20` short hashes of at most `2^32` calls each. -/
def setupPermCalls : ℕ := 2 ^ 20 * 2 ^ 32

/-- **The error of the random-permutation statement** for an adversary of `Q` calls of `π`:
the three openings' `ours_sound` terms and the reduction's list game for the derandomized
adversary (`2^20 + Q` queries, the public setup recomputed), and the transfer's term. -/
noncomputable def ksBound (Q : ℕ) : ℝ≥0∞ :=
  openingBound (2 ^ 20 + (2 ^ 20 + Q) + 6) + openingBound (2 ^ 20 + (2 ^ 20 + Q) + 6 + 10122) +
    openingBound (2 ^ 20 + (2 ^ 20 + Q) + 6 + 10122 + 10122) +
    ((2 ^ 20 + (2 ^ 20 + Q) + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) *
      (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
      5 * ((2 ^ 20 + (2 ^ 20 + Q) + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    ((setupPermCalls + Q + verifierPermCalls : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

/-- **Knowledge soundness of the deployed verifier in the random-permutation model, at the deployed
claim maps.** F1's instance of `beta()`'s Cantor basis, `coordinate_weight`'s weights and the wiring
`σ` (`rustInstance`); a wire reading the statement as its halves then `1, 0, 0, 0`; `tau` solving
`row_vanishing`'s system; the setup the wiring stack `q₀`'s commitment, `q₀`'s table carrying `σ`
(`hq₀`). For an adversary of at most `Q` calls of `π`, `π⁻¹`, the verifier (the chain and the three
openings of `deployD c 22`, over `π`) accepts while the extractor's list (`rpmExtractor` with the
deployed witness decoder) holds no witness with probability at most `ksBound Q`. -/
theorem knowledgeSoundness_rust_rpm (c : Consts) (h : IsCantor c.beta) (hτ : RowVanishing c 22)
    (σ : Equiv.Perm (Fin (22 + 2) → Bool))
    (W : Wire (rustInstance c h σ).params (rustInstance c h σ).bounds)
    (hdec : ∀ sb, W.decode sb = stmtWords sb) (q₀ : Column (wiringLayout 22).logN)
    (hq₀ : ∀ x, (tablePoly (wiringFn 22 (tabOf (wiringLayout 22) q₀))).eval
      ((rustInstance c h σ).basis.point x) = (rustInstance c h σ).basis.point ((rustInstance c h σ).wiring x))
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof E × OpenProofs))
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q) :
    Pr{let z ← Common.runWithRandomPermutation
        (rpmGame W (deployD c 22) (stackSetup (deployD c 22) q₀) A)}[
        BreaksRpm W (witnessDecoder (rustInstance c h σ) c) z] ≤ ksBound Q := by
  have hS := setupQueries_deployD c
  obtain ⟨A', hA', hle⟩ := rpm_le_wired_V W (deployD c 22)
    (witnessDecoder (rustInstance c h σ) c) (stackSetup (deployD c 22) q₀)
    (hOnly_stackSetup (deployD c 22) q₀) (setupQueries (deployD c 22))
    (setupQueries (deployD c 22) * 2 ^ 32) (isTotalQueryBound_stackSetup (deployD c 22) q₀)
    (cost_stackSetup (deployD c 22) q₀) A Q hA verifierPermCalls (cost_verifyD_deployD c W)
  rw [hS] at hA' hle
  refine hle.trans ?_
  unfold ksBound setupPermCalls
  exact add_le_add (knowledgeSoundness_deployed_concrete (rustInstance c h σ) c
    (rustInstance_basis c h σ) (rustInstance_weights c h σ) hτ W hdec q₀ hq₀ A' (2 ^ 20 + Q)
    hA') le_rfl

/-- info: 'Soundness.knowledgeSoundness_rust_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.knowledgeSoundness_rust_rpm

end Soundness
