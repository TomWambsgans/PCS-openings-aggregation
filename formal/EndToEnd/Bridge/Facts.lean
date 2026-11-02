-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Verifier
import Bridge.Extractor
import Bridge.Circuit
import Bridge.Claims
import Bridge.Setup
import Bridge.Circuit.Secret

/-!
# The bridge facts knowledge soundness takes, at the statement's constants

`formal/EndToEnd/Soundness/Hypotheses.lean` states three facts about the definitions
(`Soundness.SetupBridge`, `Soundness.VerifierBridge`, `Soundness.ReadsSecret`), at constants `c`
(`Compose.Reduce.Consts`) and a proof `h` that `c.beta` is a Cantor basis. Here `c` is the statement's
own constants (`Bridge.statementConsts`: `PcsQuotient.Domain.betaAt` and `rowVanishing 24`), and:

* **`claimsMatch_statementConsts`**: the statement's claims are `Compose.Reduce.reduce`'s
  (`Bridge.claimsAt_eq_reduce`);
* **`verifierBridge`**: `Soundness.VerifierBridge statementConsts h`;
* **`setupBridge_statementConsts`**: `Soundness.SetupBridge statementConsts h` (the circuit's
  commitment: `Bridge.Setup.setupBridge` with the circuit's `σ`, `Bridge.Circuit.membership_sigma`);
* **`readsSecret`**: `Soundness.ReadsSecret statementConsts h` (`readsSecret_of_secretMatches` with the
  circuit's `Bridge.Circuit.secretMatches`);
* **`setupBridge_final`**, **`verifierBridge_final`**, **`readsSecret_final`**: the three at
  `h := isCantor_statementConsts` (`Bridge/Claims/Constants.lean`; `RowVanishing statementConsts 22`
  is `rowVanishing_statementConsts` there).
-/

namespace Bridge

theorem claimsTr_reducedTr (r : Compose.Reduce.Reduced) : claimsTr (reducedTr r) = r := by
  obtain ⟨w, σ, q, s⟩ := r
  rfl

/-- **The statement's claims are `reduce`'s at its constants.** -/
theorem claimsMatch_statementConsts : ClaimsMatch statementConsts := by
  intro stmt α β γ t ρ a next
  rw [claimsAt_eq_reduce, Option.map_map]
  have hid : claimsTr ∘ reducedTr = id := funext claimsTr_reducedTr
  rw [hid, Option.map_id, id]

/-- **`Soundness.VerifierBridge` at the statement's constants.** -/
theorem verifierBridge (h : Compose.IsCantor statementConsts.beta) :
    Soundness.VerifierBridge statementConsts h :=
  verifierBridge_of_claims statementConsts h claimsMatch_statementConsts

/-- **`Soundness.ReadsSecret` at the statement's constants**, given the circuit's `SecretMatches`. -/
theorem readsSecret_of_secretMatches (h : Compose.IsCantor statementConsts.beta)
    (hsec : SecretMatches) : Soundness.ReadsSecret statementConsts h :=
  readsSecret_of statementConsts rfl h Circuit.membership_inputs_lt hsec

/-- **`Soundness.SetupBridge` at the statement's constants.** -/
theorem setupBridge_statementConsts (h : Compose.IsCantor statementConsts.beta) :
    Soundness.SetupBridge statementConsts h :=
  Setup.setupBridge statementConsts rfl h Circuit.membership_sigma

/-- **`Soundness.ReadsSecret` at the statement's constants.** -/
theorem readsSecret (h : Compose.IsCantor statementConsts.beta) :
    Soundness.ReadsSecret statementConsts h :=
  readsSecret_of_secretMatches h Circuit.secretMatches

/-! ## At the statement's constants, with their Cantor property -/

/-- **SETUP**, with nothing left: `Soundness.SetupBridge` at the statement's constants and their
Cantor property (`isCantor_statementConsts`). -/
theorem setupBridge_final : Soundness.SetupBridge statementConsts isCantor_statementConsts :=
  setupBridge_statementConsts isCantor_statementConsts

/-- **VERIFIER**, with nothing left. -/
theorem verifierBridge_final : Soundness.VerifierBridge statementConsts isCantor_statementConsts :=
  verifierBridge isCantor_statementConsts

/-- **EXTRACTOR READING**, with nothing left. -/
theorem readsSecret_final : Soundness.ReadsSecret statementConsts isCantor_statementConsts :=
  readsSecret isCantor_statementConsts

end Bridge

/-- info: 'Bridge.claimsMatch_statementConsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.claimsMatch_statementConsts

/-- info: 'Bridge.verifierBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.verifierBridge

/-- info: 'Bridge.readsSecret_of_secretMatches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.readsSecret_of_secretMatches

/-- info: 'Bridge.setupBridge_statementConsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.setupBridge_statementConsts

/-- info: 'Bridge.readsSecret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.readsSecret

/-- info: 'Bridge.setupBridge_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.setupBridge_final

/-- info: 'Bridge.verifierBridge_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.verifierBridge_final

/-- info: 'Bridge.readsSecret_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.readsSecret_final
