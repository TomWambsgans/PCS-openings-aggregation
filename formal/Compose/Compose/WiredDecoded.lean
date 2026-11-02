-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.DeployedWired
import Compose.DecoderDeployed

/-!
# The wired composition with the decoders

`knowledgeSoundness_wired` (all three openings' terms F2's `ours_sound`, the wiring opening's
discharged through `WiringMatch`) with the decoders of `DecoderDeployed.lean` for the witness and
quotient openings: what remains is `WitnessClaims`, `QuotientClaims` (tables to F1's messages) and
`WiringMatch` (the setup's word and the wiring claim).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}
variable (W : Wire P B) (D : Deploy F)

/-- **Knowledge soundness of the deployed verifier with the setup and the decoders, every
opening's term `ours_sound`'s**: `knowledgeSoundness_wired` with the computable decoders of the
witness and quotient layouts. -/
theorem knowledgeSoundness_wired_decoded (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows) (hLw : D.Lw = witnessLayout r)
    (hLσ : D.Lσ = wiringLayout r) (hLQ : D.LQ = quotientLayout r) (hR : D.R = logInvRate)
    (read₁ : Tab D.Lw → B.Msg₁) (read₂ : Tab D.LQ → B.Msg₂)
    (hcl₁ : WitnessClaims D read₁) (hcl₂ : QuotientClaims W D read₂)
    (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs))
    (wm : WiringMatch (P := P) D setup) (QS Q : ℕ)
    (hS : IsTotalQueryBound setup QS) (hQ : ∀ ir, IsTotalQueryBound (A ir) Q) :
    Pr{let z ← (simulateQ randomOracle (wiredExp W D (withSetup setup A))).run' ∅}[
        BreaksW W (tableCode D.Lw D.R
          (admissible_of_eq hLw hR (layouts_ok r h1 h2).1) read₁) z] ≤
      openingBound (QS + Q + 6) + openingBound (QS + Q + 6 + 10122) +
        openingBound (QS + Q + 6 + 10122 + 10122) +
        ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) *
          ((listFactor (Whir.Params.certOf D.Lw.logN D.R 0).listHi
              (Whir.Params.certOf D.LQ.logN D.R 0).listHi : ℝ≥0∞) * (roundError P B : ℝ≥0∞) +
          5 * ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  knowledgeSoundness_wired W D _ _
    (witnessMatch D (admissible_of_eq hLw hR (layouts_ok r h1 h2).1) read₁ hcl₁)
    (quotientMatch W D (admissible_of_eq hLQ hR (layouts_ok r h1 h2).2.2) read₂ hcl₂)
    setup A wm QS Q hS hQ r h1 h2 hLw hLσ hLQ hR

/-- **The same at the sizes of `quotient::protocol`**: the list term at most `2^-128`. -/
theorem knowledgeSoundness_wired_decoded_bits (hq : Fintype.card F = 2 ^ 192)
    (hN : P.nCells = 2 ^ 24) (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows)
    (hLw : D.Lw = witnessLayout r) (hLσ : D.Lσ = wiringLayout r)
    (hLQ : D.LQ = quotientLayout r) (hR : D.R = logInvRate)
    (read₁ : Tab D.Lw → B.Msg₁) (read₂ : Tab D.LQ → B.Msg₂)
    (hcl₁ : WitnessClaims D read₁) (hcl₂ : QuotientClaims W D read₂)
    (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs))
    (wm : WiringMatch (P := P) D setup) (QS Q : ℕ)
    (hS : IsTotalQueryBound setup QS) (hQ : ∀ ir, IsTotalQueryBound (A ir) Q) :
    Pr{let z ← (simulateQ randomOracle (wiredExp W D (withSetup setup A))).run' ∅}[
        BreaksW W (tableCode D.Lw D.R
          (admissible_of_eq hLw hR (layouts_ok r h1 h2).1) read₁) z] ≤
      openingBound (QS + Q + 6) + openingBound (QS + Q + 6 + 10122) +
        openingBound (QS + Q + 6 + 10122 + 10122) +
        ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
          5 * ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_wired_decoded W D r h1 h2 hLw hLσ hLQ hR read₁ read₂ hcl₁ hcl₂ setup
    A wm QS Q hS hQ).trans ?_
  have hb := listHi_le_of_eq D r h1 h2 hLw hLQ hR
  gcongr
  exact listError_le_generic hq hN hw hd hb.1 hb.2

end Compose
