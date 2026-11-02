-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.TwoOracle
import Compose.Bits
import Compose.Final

/-!
# The composed statement in mumbai's two-oracle model

`Openings.lean`'s composition, with the experiment of `TwoOracle.lean`: the adversary and every
part of the verifier ask leanerVM `mumbai`'s `KeccakCalls` (Keccak-256 and Keccak-f[1600],
independent random oracles), F2's oracle model. The openings' doomed events are events in that
model, **still to be reduced to F2's `ours_sound`** here (`Deployed.lean` does it for the deployed
openings, `ourVerifier`): the openings' verifier `openings` is any computation of both oracles of
at most `QV` queries. The extractor reads every Keccak-256 query of the run (`AdversaryLog.lean`:
the adversary's only).

**`knowledgeSoundness_composed_kc`** and, with the Merkle extractor at the sizes of
`quotient::protocol`, **`knowledgeSoundness_merkle_kc`**.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) (C₁ : ListCommit B.Msg₁)
  (C₂ : ListCommit B.Msg₂) {O : Type}

/-- **Knowledge soundness of the reduction composed with the openings, in mumbai's two-oracle
model.** For every adversary making at most `Q` queries of Keccak-256 and Keccak-f[1600] that
outputs a statement, the two roots, the five values and the openings, and every openings'
verifier of at most `QV` queries: if the three openings' doomed events have probabilities at most
`εW`, `εσ`, `εQ`, the verifier accepts while the extractor's list (the witness root's candidates,
read off the transcript of the Keccak-256 queries) holds no witness of the statement with
probability at most `εW + εσ + εQ + (Q + 6 + QV) (max L₁ (L₁ L₂) · roundError +
4 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_composed_kc (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WitnessDoomed C₁ z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      QuotientDoomed W C₂ z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[Breaks W C₁ z] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * ((listFactor C₁.bound C₂.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) + 4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set mx := (simulateQ randomOracle (kcExperiment W A openings)).run' ∅
  have hL := knowledgeSoundness_list_kc W C₁ C₂ A openings Q QV hQ hV
  refine (prEvent_mono mx _ _ (breaks_imp W C₁ C₂)).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add hW ((prEvent_or_le _ _ _).trans (add_le_add hσ
    ((prEvent_or_le _ _ _).trans (add_le_add hQd hL))))).trans ?_
  simp only [add_assoc, le_refl]

/-- **The composed statement in mumbai's model, with the Merkle extractor, at the sizes of
`quotient::protocol`** (lists of at most `2^18`, identities of degree at most `2^28`): the
openings' terms plus `(Q + 6 + QV) (2^-128 + 4 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_merkle_kc (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) (h₁ : c₁.bound ≤ 2 ^ 18)
    (h₂ : c₂.bound ≤ 2 ^ 18)
    (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WitnessDoomed c₁.commit z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      QuotientDoomed W c₂.commit z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
        Accepted (P := P) z ∧
          ∀ g ∈ witnessExtractor c₁ z, ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
        4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_composed_kc W c₁.commit c₂.commit A openings Q QV hQ hV εW εσ εQ hW
    hσ hQd).trans ?_
  gcongr
  exact listError_le_generic hq hN hw hd h₁ h₂

end Compose
