-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Lv42.Arithmetization.Boundary
import Lv42.Arithmetization.Bytecode
import Lv42.Arithmetization.Channels
import Lv42.Arithmetization.Completeness.Balance
import Lv42.Arithmetization.Completeness.Basics
import Lv42.Arithmetization.Completeness.Bus
import Lv42.Arithmetization.Completeness.Messages
import Lv42.Arithmetization.Completeness.Rows
import Lv42.Arithmetization.Completeness.Satisfied
import Lv42.Arithmetization.Completeness.Skeletons
import Lv42.Arithmetization.Completeness.Theorem
import Lv42.Arithmetization.Completeness.Witness
import Lv42.Arithmetization.Soundness.Bus
import Lv42.Arithmetization.Soundness.BytecodeChannel
import Lv42.Arithmetization.Soundness.Lookup
import Lv42.Arithmetization.Soundness.MemChannel
import Lv42.Arithmetization.Soundness.Rows
import Lv42.Arithmetization.Soundness.StateWalk
import Lv42.Arithmetization.Soundness.Theorem
import Lv42.Arithmetization.Soundness.Walk
import Lv42.Arithmetization.Statement
import Lv42.Arithmetization.Tables.Basic
import Lv42.Arithmetization.Tables.Blake2s
import Lv42.Arithmetization.Tables.Deref
import Lv42.Arithmetization.Tables.Jump
import Lv42.Arithmetization.Tables.MulNative
import Lv42.Arithmetization.Tables.SetConstant
import Lv42.Arithmetization.Tables.Xor
import Lv42.Parameters.Flock
import Lv42.Parameters.Isa
import Lv42.Protocol.Blake2sCircuit
import Lv42.Protocol.Blake2sHash
import Lv42.Protocol.FixedColumns
import Lv42.Protocol.FlockSpec
import Lv42.Protocol.LeanIsa
import Lv42.Protocol.LeanIsa.Bus
import Lv42.Protocol.LeanIsa.Complete
import Lv42.Protocol.LeanIsa.Read
import Lv42.Protocol.LeanIsa.Relation
import Lv42.Protocol.LeanIsa.Sound
import Lv42.Protocol.Spine.Instance
import Lv42.Protocol.Stack
import Lv42.Protocol.ToArkLib.Flock.BlockR1CS
import Lv42.Protocol.ToArkLib.Flock.Builder
import Lv42.Protocol.ToArkLib.Flock.Circuit
import Lv42.Protocol.ToArkLib.Flock.Words
import Lv42.Protocol.ToCompPoly.AmbientStacking
import Lv42.Protocol.ToCompPoly.Stacking
import Lv42.Protocol.VerifierTables
import Lv42.Semantics.Lemmas
import Lv42.Spec.Blake2s
import Lv42.Spec.Isa
import Lv42.Spec.IsaWith

/-!
# Lv42: leanVM 42422001's VM, arithmetization and leanISA adaptor

Ported from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch `mumbai`, commit
`f0393df4`, the last before its switch to Keccak: its `lean_vm/LeanVM` formalizes leanVM
`3f7dc219`, whose verifier, Flock, Python verifier and specification are leanVM `42422001`'s.
The namespace `LeanVM` is renamed `Lv42`, so that this library and leanerVM `6175f1a0`'s
Keccak-era `LeanVM` (which `formal/WhirBridge` imports, `Statement.LeanIsa` included) can be
imported together; the field, multilinear and Clean-bridge modules are `6175f1a0`'s, imported as
they are, so `M3Holds` is a relation on `LeanVM.Protocol.Column`, the type `WhirBridge` opens.

* The VM (`Lv42.Spec.Isa`): leanISA with `BLAKE2S`, the run halting at `pc_final` and failing
  there unless `fp = 1` (`run`, `ValidExecution`; `crates/leanvm_core/src/cpu/execute.rs:541-546`
  at leanVM `42422001`), and `SentinelSafe`, the one condition soundness puts on a program.
* The arithmetization (`Lv42.Arithmetization`): Clean's ensemble of the six opcode tables and
  the memory and bytecode blocks; `constraintSoundness` (under `SentinelSafe`) and
  `constraintCompleteness`.
* The abstract instance (`Lv42.Protocol.Spine.Instance`): `M3Instance`, `M3Holds`, `M3Honest`,
  with the Flock region and its predicate (`FlockRegion.Holds`).
* The Flock region's meaning (`Lv42.Protocol.FlockSpec`): `FlockSpec`, `compress_of_region`,
  `region_holds_gen`, and the BLAKE2s inhabitant `blake2sFlockSpec`.
* The adaptor (`Lv42.Protocol.LeanIsa`): `leanIsaInstance F prog s`, `witnessOf`, `stackOf`,
  `satisfiedBy_witnessOf` (soundness) and `m3Honest_stackOf` (completeness).

The build fails if the axiom footprint of these theorems grows beyond Lean's three standard
axioms.
-/

-- The VM: distinct opcodes have distinct codes.
/-- info: 'Lv42.Parameters.Opcode.code_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Parameters.Opcode.code_injective

/-- info: 'Lv42.Semantics.validExecutionB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Semantics.validExecutionB_deployed

-- The arithmetization: constraint soundness and completeness (Clean's ensemble of the six tables).
/-- info: 'Lv42.Arithmetization.constraintSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Arithmetization.constraintSoundness

/-- info: 'Lv42.Arithmetization.constraintCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Arithmetization.constraintCompleteness

-- The bus: the run inside a balanced state channel, the sentinel, the memory and bytecode lookups.
/-- info: 'Lv42.Arithmetization.exists_run_of_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Arithmetization.exists_run_of_balanced

/-- info: 'Lv42.Arithmetization.no_row_at_sentinel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Arithmetization.no_row_at_sentinel

/-- info: 'Lv42.Arithmetization.mem_channel_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Arithmetization.mem_channel_sound

/-- info: 'Lv42.Arithmetization.bytecode_channel_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Arithmetization.bytecode_channel_sound

/-- info: 'Lv42.Arithmetization.lookup_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Arithmetization.lookup_sound

-- The BLAKE2s circuit and the Flock region's meaning.
/-- info: 'Lv42.Protocol.Blake2sCircuit.bounded_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.Blake2sCircuit.bounded_blake2s

/-- info: 'Lv42.Protocol.Blake2sCircuit.blake2s_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.Blake2sCircuit.blake2s_sound

/-- info: 'Lv42.Protocol.Blake2sCircuit.blake2s_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.Blake2sCircuit.blake2s_complete

/-- info: 'Lv42.Protocol.FlockSpec.compress_of_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.FlockSpec.compress_of_region

/-- info: 'Lv42.Protocol.FlockSpec.region_holds_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.FlockSpec.region_holds_gen

/-- info: 'Lv42.Protocol.Blake2sFlock.compress_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.Blake2sFlock.compress_of_holds

/-- info: 'Lv42.Protocol.Blake2sFlock.holds_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.Blake2sFlock.holds_gen

/-- info: 'Lv42.Protocol.Blake2sFlock.slots_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.Blake2sFlock.slots_gen

/-- info: 'Lv42.Protocol.Blake2sFlock.blake2sFlockSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.Blake2sFlock.blake2sFlockSpec

-- The leanISA adaptor: `M3Holds` of the instance gives the constraint system's witness, and back.
/-- info: 'Lv42.Protocol.LeanIsa.satisfiedBy_witnessOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.LeanIsa.satisfiedBy_witnessOf

/-- info: 'Lv42.Protocol.LeanIsa.m3Holds_stackOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.LeanIsa.m3Holds_stackOf

/-- info: 'Lv42.Protocol.LeanIsa.m3Honest_stackOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.LeanIsa.m3Honest_stackOf

/-- info: 'Lv42.Protocol.LeanIsa.witnessOf_stackOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.LeanIsa.witnessOf_stackOf

/-- info: 'Lv42.Protocol.LeanIsa.padLimbs_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.LeanIsa.padLimbs_compress

/-- info: 'Lv42.Protocol.LeanIsa.counts_le_pushes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.LeanIsa.counts_le_pushes

/-- info: 'Lv42.Protocol.LeanIsa.constrained_pushes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.LeanIsa.constrained_pushes

/-- info: 'Lv42.Protocol.LeanIsa.flushes_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lv42.Protocol.LeanIsa.flushes_separator
