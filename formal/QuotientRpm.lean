-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientRpm.Bytes
import QuotientRpm.FreshBad
import QuotientRpm.Chain
import QuotientRpm.Uniform
import QuotientRpm.ChainRom
import QuotientRpm.Rpm

/-!
# The reduction with the deployed transcript

The Keccak-256 chain of `crates/quotient/src/transcript.rs`, in the random-oracle model
(`knowledgeSoundness_chain`, `ChainRom.lean`) and in leanerVM's random-permutation model
(`knowledgeSoundness_rpm`, `knowledgeSoundness_rpm_bits`, `Instance.soundness_rpm`, `Rpm.lean`),
with ideal commitments. The end theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/

/-- info: 'QuotientRpm.stateLimbs_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.stateLimbs_fiber

/-- info: 'QuotientRpm.rootWords_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.rootWords_eq

/-- info: 'QuotientRpm.prEvent_chal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.prEvent_chal

/-- info: 'QuotientRpm.prEvent_randomOracle_le_of_freshBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.prEvent_randomOracle_le_of_freshBad

/-- info: 'QuotientRpm.prob_chainBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.prob_chainBad

/-- info: 'QuotientRpm.trace_chainBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.trace_chainBad

/-- info: 'QuotientRpm.knowledgeSoundness_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.knowledgeSoundness_chain

/-- info: 'QuotientRpm.knowledgeSoundness_chain_coins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.knowledgeSoundness_chain_coins

/-- info: 'QuotientRpm.knowledgeSoundness_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.knowledgeSoundness_rpm

/-- info: 'QuotientRpm.knowledgeSoundness_rpm_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.knowledgeSoundness_rpm_bits

/-- info: 'QuotientRpm.Instance.soundness_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientRpm.Instance.soundness_rpm
