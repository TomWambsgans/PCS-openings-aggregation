-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.KeccakMath
import RecCircuit.Spec
import RecCircuit.Graph
import RecCircuit.Layout
import RecCircuit.Templates
import RecCircuit.Expand
import RecCircuit.Compile
import RecCircuit.Check
import RecCircuit.Sat
import RecCircuit.PolySem
import RecCircuit.Gates
import RecCircuit.Sponge
import RecCircuit.Pack
import RecCircuit.Words
import RecCircuit.Decode
import RecCircuit.Nodes
import RecCircuit.Ports
import RecCircuit.Piop
import RecCircuit.Sound
import RecCircuit.Agree
import RecCircuit.SoundRG

/-!
# π2's circuit, formally (`crates/leanvm_rec/src/circuit`)

See `formal/RecCircuit/README.md`. The build fails if a headline theorem's axioms grow beyond Lean's three standard
ones.
-/

/-- info: 'RecCircuit.compile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.compile_sound

/-- info: 'RecCircuit.compile_sound_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.compile_sound_flow

/-- info: 'RecCircuit.compile_sound_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.compile_sound_zero

/-- info: 'RecCircuit.Compiled.ports_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Compiled.ports_carry

/-- info: 'RecCircuit.Compiled.node_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Compiled.node_inv

/-- info: 'RecCircuit.satisfied_of_piop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.satisfied_of_piop

/-- info: 'RecCircuit.d16_keccakF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.d16_keccakF

/-- info: 'RecCircuit.keccak256_bits_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.keccak256_bits_multi

/-- info: 'RecCircuit.Ctx.keccak_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Ctx.keccak_out

/-- info: 'RecCircuit.Ctx.sponge_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Ctx.sponge_digest

/-- info: 'RecCircuit.Ctx.pack_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Ctx.pack_val

/-- info: 'RecCircuit.Compiled.unit_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Compiled.unit_val

/-- info: 'RecCircuit.Ctx.gate_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Ctx.gate_val

/-- info: 'RecCircuit.Compiled.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Compiled.agree

/-- info: 'RecCircuit.step_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.step_corr

/-- info: 'RecCircuit.Compiled.compile_sound_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Compiled.compile_sound_statement

/-- info: 'RecCircuit.Compiled.compile_sound_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Compiled.compile_sound_root

/-- info: 'RecCircuit.Compiled.compile_sound_element' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Compiled.compile_sound_element

/-- info: 'RecCircuit.Compiled.compile_sound_zero_rg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCircuit.Compiled.compile_sound_zero_rg
