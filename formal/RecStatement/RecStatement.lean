-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Basic
import RecStatement.Data
import RecStatement.Spec
import RecStatement.Core
import RecStatement.Verifier
import RecStatement.Calls
import RecStatement.Security

/-!
# RecStatement: π2's verifier, transcribed

`crates/leanvm_rec`'s π2 verifier (`pi2/verifier.rs`, `contract.rs`; `PI2.md` §2, §8–§9) as computable Lean
(`README.md` here: the reading order, the correspondence with the Rust, what is tested).
-/

/-- info: 'RecStatement.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.run

/-- info: 'RecStatement.pcsCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.pcsCalls

/-- info: 'RecStatement.RecDeployment.verifierWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecDeployment.verifierWith

/-- info: 'RecStatement.recExtractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.recExtractor

/-- info: 'RecStatement.RecDeployment.Real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecDeployment.Real

/-- info: 'RecStatement.RecKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecKnowledgeSoundness

/-- info: 'RecStatement.RecCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecCompleteness
