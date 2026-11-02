-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniStatement.Run
import UniStatement.Opening
import UniStatement.Mapping
import UniStatement.Security

/-!
# UniStatement: the univariate PIOP for leanVM 42422001, transcribed

`crates/leanvm_univariate`'s verifier as computable Lean (`README.md` here: the reading order, the
correspondence with the Rust, what is tested), and its end statements against leanVM 42422001's relation
(`Lv42`'s `M3Holds`): `UniKnowledgeSoundness`, `UniCompleteness` (`Security.lean`), stated, not proved.

The build fails if a definition the statements rest on uses an axiom beyond Lean's three standard ones.
-/

/-- info: 'UniStatement.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.run

/-- info: 'UniStatement.verifyWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.verifyWith

/-- info: 'UniStatement.lv42Stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.lv42Stack

/-- info: 'UniStatement.uniExtractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.uniExtractor

/-- info: 'UniStatement.UniKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.UniKnowledgeSoundness

/-- info: 'UniStatement.UniCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniStatement.UniCompleteness
