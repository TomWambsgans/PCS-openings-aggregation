-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Verifier
import Bridge.Extractor
import Bridge.Circuit
import Bridge.Claims.Reduce

/-!
# The bridge facts knowledge soundness takes, at the statement's constants

`formal/EndToEnd/Soundness/Hypotheses.lean` states three facts about the definitions
(`Soundness.SetupBridge`, `Soundness.VerifierBridge`, `Soundness.ReadsSecret`), at constants `c`
(`Compose.Reduce.Consts`) and a proof `h` that `c.beta` is a Cantor basis. Here `c` is the statement's
own constants (`Bridge.statementConsts`: `PcsQuotient.Domain.betaAt` and `rowVanishing 24`), and:

* **`claimsMatch_statementConsts`**: the statement's claims are `Compose.Reduce.reduce`'s
  (`Bridge.claimsAt_eq_reduce`);
* **`verifierBridge`**: `Soundness.VerifierBridge statementConsts h`;
* **`readsSecret_of_secretMatches`**: `Soundness.ReadsSecret statementConsts h`, from the circuit's
  `SecretMatches`.
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
