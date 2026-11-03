-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Basic
import RecStatement.Data
import RecStatement.Spec
import RecStatement.Core
import RecStatement.Verifier
import RecStatement.Calls
import RecStatement.Security
import RecStatement.Lemmas.Main

/-!
# RecStatement: π2's verifier, transcribed, and the recursive verifier's statements

`crates/leanvm_rec`'s π2 verifier (`pi2/verifier.rs`, `contract.rs`; `PI2.md` §2, §8–§9) as computable Lean
(`README.md` here: the reading order, the correspondence with the Rust, what is tested):

* **the verifier** (`run`, `runWith`): the seed of π2's IV (`iv`: π1's contract IV, the setup root, the circuit's
  digest, the layout words), the public data in the stream, `W`'s root then `α, β, γ`, `Q`'s root then `t`, the 17
  values then `ρ`, and the arithmetic at `t` (`CoreSpec.run`, over any field), its constants `Spec.of` of the
  circuit's tables (`Data`, emitted by the Rust); the six `PCS_OPEN` calls word for word (`pcsCalls`);
* **the verifier-arithmetic lemmas** (`Lemmas`), over any field of characteristic two, under `SpecOf` (the constants
  are `RecPiop`'s circuit's on a Cantor basis): the indicators' closed form (`ind_eval_closed`), the zero coset's
  (`coset_closed`), the siblings' fold (`cellsList_eq_cellsOf`), `W`'s fold (`foldW_eq_foldAt`), the push side
  (`push_side`), the public side (`publicSide_eq`), the one inversion's two nonzero conditions (`all_ne_zero_iff`), and
  **`checks_claims_iff`**/**`checks_claims_iff_post2`**: the checks pass and the claims hold iff `t ∉ V_{m+2}`,
  `c_h + c_q ≠ 0` and `RecPiop.Post2`;
* **the end statements** (`Security`): `RecKnowledgeSoundness` (for the explicit extractor `recExtractor`) and
  `RecCompleteness` of the recursive verifier (π2's verifier and the six openings) against leanVM 42422001's relation
  (`Lv42.Protocol.M3Holds`), stated, not proved.

The build fails if a headline definition or theorem uses an axiom beyond Lean's three standard ones.
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

/-- info: 'RecStatement.ind_eval_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.ind_eval_closed

/-- info: 'RecStatement.coset_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.coset_closed

/-- info: 'RecStatement.cellsList_eq_cellsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.cellsList_eq_cellsOf

/-- info: 'RecStatement.foldW_eq_foldAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.foldW_eq_foldAt

/-- info: 'RecStatement.push_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.push_side

/-- info: 'RecStatement.publicSide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.publicSide_eq

/-- info: 'RecStatement.all_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.all_ne_zero_iff

/-- info: 'RecStatement.checks_claims_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.checks_claims_iff

/-- info: 'RecStatement.checks_claims_iff_post2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.checks_claims_iff_post2

/-- info: 'RecStatement.run_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.run_u

/-- info: 'RecStatement.run_digitsScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.run_digitsScale
