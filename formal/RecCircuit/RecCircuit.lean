-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.KeccakMath
import RecCircuit.Spec
import RecCircuit.Graph
import RecCircuit.Layout
import RecCircuit.Templates
import RecCircuit.Expand
import RecCircuit.Compile

/-!
# π2's circuit, formally (`crates/leanvm_rec/src/circuit`)

See `RecCircuit/README.md`.
-/

/-- info: 'RecCircuit.d16_keccakF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.d16_keccakF

/-- info: 'RecCircuit.keccak256_bits_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.keccak256_bits_multi
