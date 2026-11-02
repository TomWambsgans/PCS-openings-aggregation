-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Decoder
import Compose.Deployed

/-!
# The decoder in the deployed composition: `WitnessMatch`, `QuotientMatch`

`Deployed.lean`'s `knowledgeSoundness_deployed_setup` takes the two decoders as `TableCode`s with
`WitnessMatch D c₁` and `QuotientMatch W D c₂`: the decoder lists every candidate of mumbai's
extraction (`Candidates` of `wordOfMerkle` of the Merkle word, F2's `OpeningDoomed` list), read
back as F1's message, and a candidate whose table satisfies the opening's claims
(`Layout.tableEval`) reads back as a message satisfying F1's claim.

Here the decoders are `Decoder.lean`'s computable `tableCode`, for **any** F2 layout `D.Lw`,
`D.LQ` at an admissible shape (the read-back is `Layout.table`: `Layout.readHidden` for a hidden
layout, the gadget layout included once `WhirBridge` transcribes it), and:

* **`witnessMatch`**, **`quotientMatch`**: `WitnessMatch` and `QuotientMatch` for them, the
  height, the leaf length and the completeness proved (`mem_decodeTables`: the decoder lists
  *exactly* the candidates), the claims reduced to **tables**: `read` is any map from a table (its
  `2^vars` entries, `Tab`) to F1's message, and what remains (`WitnessClaims`, `QuotientClaims`)
  is that a table whose multilinear extension (`tabEval`, `Table::eval`) satisfies the opening's
  claims reads as a message satisfying F1's claim: a statement about the claim maps `D.clW`,
  `D.clQ` and F1's tables only (`Concrete.lean`'s `witness_claim`, `quotient_mle`,
  `claims_iff_accepts_ofCantor`, with `F = E`), with no stack, layout or decoder in it.
* **`knowledgeSoundness_deployed_decoded`**: `knowledgeSoundness_deployed_setup` with these
  decoders, for `D.Lw = witnessLayout r`, `D.LQ = quotientLayout r`, `17 ≤ r ≤ 22`, rate `1/2`;
  **`_bits`**: its list term at most `2^-128` (`listError_le_generic`: both lists at most
  `2^18`, `listHi_ours`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) (D : Deploy F)

/-! ## The claims, on tables -/

/-- **The witness claims, on tables**: a table of the witness layout whose multilinear extension
satisfies the witness opening's claims reads (`read`) as a first message satisfying F1's witness
claim. -/
def WitnessClaims (read : Tab D.Lw → B.Msg₁) : Prop :=
  ∀ (π : RootProof F) (ch : Chals F) (T : Tab D.Lw),
    (∀ cl ∈ (D.clW π ch).claims, tabEval D.Lw T cl.point = cl.value) →
      witnessClaim (read T).1 ch.t ch.ρ π.v.1

/-- **The quotient claims, on tables**: a table of the quotient layout satisfying both claims of
the quotient opening reads as a second message satisfying F1's two quotient claims. -/
def QuotientClaims (read : Tab D.LQ → B.Msg₂) : Prop :=
  ∀ (π : RootProof F) (ch : Chals F) (T : Tab D.LQ),
    (∀ cl ∈ (D.clQ π ch).claims, tabEval D.LQ T cl.point = cl.value) →
      quotientClaims P (W.decode π.stmt) (read T).1 ch.α ch.β ch.γ ch.t π.v.1 π.v.2 ch.ρ

/-! ## The matches -/

/-- The decoder's completeness against `WitnessMatch.complete`'s word. -/
theorem read_mem_tableCode_dec {L : Layout} {R : ℕ} (hw : Whir.Admissible L.logN R) {M : Type}
    (read : Tab L → M) (w : Fin (2 ^ rootHeight L.logN R) → Option (List UInt8))
    (q : Column L.logN)
    (hq : q ∈ Candidates L.logN R (code₀ L.logN R).thr
      (wordOfMerkle (rootHeight L.logN R) (2 ^ laneFold) w)) :
    read (tabOf L q) ∈ (tableCode L R hw read).dec w := by
  rw [tableCode_dec]
  exact List.mem_map.mpr ⟨tabOf L q, (mem_decodeTables hw _ _).mpr ⟨q, hq, rfl⟩, rfl⟩

/-- **`WitnessMatch` for the decoder**, at any admissible witness layout: what remains is the
claims on tables. -/
def witnessMatch (hw : Whir.Admissible D.Lw.logN D.R) (rd : Tab D.Lw → B.Msg₁)
    (hcl : WitnessClaims D rd) : WitnessMatch D (tableCode D.Lw D.R hw rd) where
  read q := rd (tabOf D.Lw q)
  height := rfl
  leaf := rfl
  complete w q hq := read_mem_tableCode_dec hw rd w q hq
  claims π ch q h := hcl π ch (tabOf D.Lw q) fun cl hcl' => (tabEval_tabOf _ _ _).trans (h cl hcl')

/-- **`QuotientMatch` for the decoder**, at any admissible quotient layout. -/
def quotientMatch (hw : Whir.Admissible D.LQ.logN D.R) (rd : Tab D.LQ → B.Msg₂)
    (hcl : QuotientClaims W D rd) : QuotientMatch W D (tableCode D.LQ D.R hw rd) where
  read q := rd (tabOf D.LQ q)
  height := rfl
  leaf := rfl
  complete w q hq := read_mem_tableCode_dec hw rd w q hq
  claims π ch q h := hcl π ch (tabOf D.LQ q) fun cl hcl' => (tabEval_tabOf _ _ _).trans (h cl hcl')

/-- The witness match's read is the table's read. -/
theorem witnessMatch_read (hw : Whir.Admissible D.Lw.logN D.R) (read : Tab D.Lw → B.Msg₁)
    (hcl : WitnessClaims D read) (q : Column D.Lw.logN) :
    (witnessMatch D hw read hcl).read q = read (tabOf D.Lw q) :=
  rfl

/-! ## The deployed statement with the decoder -/

theorem admissible_of_eq {L L' : Layout} {R : ℕ} (h : L = L') (hR : R = logInvRate)
    (hw : Whir.Admissible L'.logN logInvRate) : Whir.Admissible L.logN R := by
  subst h hR
  exact hw

/-- **Knowledge soundness of the deployed verifier with the decoder**: `knowledgeSoundness_deployed
_setup` with `c₁`, `c₂` the computable decoders of the witness and quotient layouts (any supported
size `17 ≤ log_rows ≤ 22`, rate `1/2`), `WitnessMatch` and `QuotientMatch` discharged but for the
claims on tables (`WitnessClaims`, `QuotientClaims`). -/
theorem knowledgeSoundness_deployed_decoded (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows) (hLw : D.Lw = witnessLayout r)
    (hLQ : D.LQ = quotientLayout r) (hR : D.R = logInvRate)
    (read₁ : Tab D.Lw → B.Msg₁) (read₂ : Tab D.LQ → B.Msg₂)
    (hcl₁ : WitnessClaims D read₁) (hcl₂ : QuotientClaims W D read₂)
    (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs)) (QS Q QO : ℕ)
    (hS : IsTotalQueryBound setup QS) (hQ : ∀ ir, IsTotalQueryBound (A ir) Q)
    (hO : ∀ (L : Layout) w, IsTotalQueryBound (ourVerifier L D.R w) QO) (εσ : ℝ≥0∞)
    (hσ : Pr{let z ← (simulateQ randomOracle (deployedExp W D (withSetup setup A))).run' ∅}[
      WDd (P := P) z] ≤ εσ) :
    Pr{let z ← (simulateQ randomOracle (deployedExp W D (withSetup setup A))).run' ∅}[
        BreaksD W (tableCode D.Lw D.R
          (admissible_of_eq hLw hR (layouts_ok r h1 h2).1) read₁) z] ≤
      openingBound (QS + Q + 6) + εσ + openingBound (QS + Q + 6 + QO + QO) +
        ((QS + Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) *
          ((listFactor (Whir.Params.certOf D.Lw.logN D.R 0).listHi
              (Whir.Params.certOf D.LQ.logN D.R 0).listHi : ℝ≥0∞) * (roundError P B : ℝ≥0∞) +
          5 * ((QS + Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  knowledgeSoundness_deployed_setup W D _ _
    (witnessMatch D (admissible_of_eq hLw hR (layouts_ok r h1 h2).1) read₁ hcl₁)
    (quotientMatch W D (admissible_of_eq hLQ hR (layouts_ok r h1 h2).2.2) read₂ hcl₂)
    setup A QS Q QO hS hQ hO r h1 h2 (Or.inl hLw) (Or.inr (Or.inr hLQ)) hR εσ hσ

/-- The decoders' certified lists at our layouts are at most `2^18`. -/
theorem listHi_le_of_eq (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows)
    (hLw : D.Lw = witnessLayout r) (hLQ : D.LQ = quotientLayout r) (hR : D.R = logInvRate) :
    (Whir.Params.certOf D.Lw.logN D.R 0).listHi ≤ 2 ^ 18 ∧
      (Whir.Params.certOf D.LQ.logN D.R 0).listHi ≤ 2 ^ 18 := by
  rw [hLw, hLQ, hR]
  exact ⟨(listHi_ours r h1 h2).1, (listHi_ours r h1 h2).2.1⟩

/-- **The same at the sizes of `quotient::protocol`**: the list term at most `2^-128`. -/
theorem knowledgeSoundness_deployed_decoded_bits (hq : Fintype.card F = 2 ^ 192)
    (hN : P.nCells = 2 ^ 24) (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows) (hLw : D.Lw = witnessLayout r)
    (hLQ : D.LQ = quotientLayout r) (hR : D.R = logInvRate)
    (read₁ : Tab D.Lw → B.Msg₁) (read₂ : Tab D.LQ → B.Msg₂)
    (hcl₁ : WitnessClaims D read₁) (hcl₂ : QuotientClaims W D read₂)
    (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs)) (QS Q QO : ℕ)
    (hS : IsTotalQueryBound setup QS) (hQ : ∀ ir, IsTotalQueryBound (A ir) Q)
    (hO : ∀ (L : Layout) w, IsTotalQueryBound (ourVerifier L D.R w) QO) (εσ : ℝ≥0∞)
    (hσ : Pr{let z ← (simulateQ randomOracle (deployedExp W D (withSetup setup A))).run' ∅}[
      WDd (P := P) z] ≤ εσ) :
    Pr{let z ← (simulateQ randomOracle (deployedExp W D (withSetup setup A))).run' ∅}[
        BreaksD W (tableCode D.Lw D.R
          (admissible_of_eq hLw hR (layouts_ok r h1 h2).1) read₁) z] ≤
      openingBound (QS + Q + 6) + εσ + openingBound (QS + Q + 6 + QO + QO) +
        ((QS + Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
          5 * ((QS + Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_deployed_decoded W D r h1 h2 hLw hLQ hR read₁ read₂ hcl₁ hcl₂ setup
    A QS Q QO hS hQ hO εσ hσ).trans ?_
  have hb := listHi_le_of_eq D r h1 h2 hLw hLQ hR
  gcongr
  exact listError_le_generic hq hN hw hd hb.1 hb.2

end Compose
