-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Decoder
import Compose.DecoderCost
import Compose.DecoderDeployed

/-!
# The decoder's axioms

`#print axioms` of the decoder's theorems: `propext`, `Classical.choice`, `Quot.sound` only.

**The decoder's definitions.** `#print axioms decodeColumns` (and of mumbai's `decodeStacks`)
lists `Classical.choice` too, and so does that of any definition computing in `K = GF(2^64)`
through its `Field` instance: `#print axioms` follows every constant a term mentions, proofs
included, and the instance `BF64.instField` holds proofs (`mul_inv_cancel`, through Mathlib's
`AdjoinRoot`) that use it, while its operations are explicit (the inverse is Itoh–Tsujii's).
`#print axioms BF64.instField` shows it.

So the definitions are audited the way the compiler sees them (`computationalAxioms`): every
constant their values reach **outside proofs and types** (the positions the compiler erases),
followed through every definition it unfolds to. For `decodeColumns`, `decodeTables`,
`merkleTables` and `tableCode`'s decoder that is **no axiom at all**: `Classical.choice` appears
only in erased positions. The audit also lists the reached constants whose compiled code is not
their definition (`@[implemented_by]`, `@[extern]`, `opaque`, `partial`) outside Lean's core
library (`Init`, `Std`, `Lean`): none.
-/

open Lean Meta Elab Command

namespace Compose.Audit

/-- Whether a constant comes from Lean's core library. -/
def isCore (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`Init).isPrefixOf m || (`Std).isPrefixOf m || (`Lean).isPrefixOf m
  | none => false

/-- The constants a term mentions outside proofs and types (the positions the compiler erases). -/
def computationalConsts (v : Expr) : MetaM (Array Name) := do
  let ref ← IO.mkRef (#[] : Array Name)
  let _ ← Meta.transform v (pre := fun e => do
    if e.isSort then return .done e
    if (← isProof e) || (← isType e) || (← isTypeFormer e) then return .done e
    if let .const n _ := e then ref.modify (·.push n)
    return .continue)
  ref.get

/-- **The computational axioms of a definition**: the axioms reached from its value through
computational positions only, following every definition and `opaque`; and the non-core
constants reached whose compiled code is not their definition (`implemented_by`, `extern`,
`opaque`). Returns the axioms, those constants, and the number of constants visited. -/
partial def computationalAxioms (root : Name) : MetaM (Array Name × Array Name × Nat) := do
  let env ← getEnv
  let mut todo : Array Name := #[root]
  let mut seen : NameSet := {}
  let mut axs : Array Name := #[]
  let mut special : Array Name := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | continue
    let core := isCore env n
    if !core && ((Compiler.getImplementedBy? env n).isSome || isExtern env n) then
      special := special.push n
    match info with
    | .axiomInfo _ => axs := axs.push n
    | .defnInfo v =>
      for c in ← computationalConsts v.value do
        unless seen.contains c do todo := todo.push c
    | .opaqueInfo v =>
      unless core do special := special.push n
      for c in ← computationalConsts v.value do
        unless seen.contains c do todo := todo.push c
    | _ => pure ()
  return (axs, special, seen.size)

/-- Print the computational audit of a definition. -/
elab "#computational_axioms " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let (axs, special, _) ← withOptions (fun o => maxRecDepth.set o 100000) <|
    computationalAxioms n
  logInfo m!"{n}: computational axioms {axs.toList}, non-core implemented_by/extern/opaque \
    {special.toList}"

end Compose.Audit

/-! ## The decoder's definitions -/

/--
info: Compose.decodeColumns: computational axioms [], non-core implemented_by/extern/opaque []
-/
#guard_msgs in
#computational_axioms Compose.decodeColumns

/--
info: Compose.decodeTables: computational axioms [], non-core implemented_by/extern/opaque []
-/
#guard_msgs in
#computational_axioms Compose.decodeTables

/--
info: Compose.merkleTables: computational axioms [], non-core implemented_by/extern/opaque []
-/
#guard_msgs in
#computational_axioms Compose.merkleTables

/--
info: Compose.tableCode: computational axioms [], non-core implemented_by/extern/opaque []
-/
#guard_msgs in
#computational_axioms Compose.tableCode

/-- info: 'Compose.decodeColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.decodeColumns

/-- info: 'BF64.instField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BF64.instField

/-! ## The theorems -/

/-- info: 'Compose.mem_decodeColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.mem_decodeColumns

/--
info: 'Compose.nodup_decodeColumns' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.nodup_decodeColumns

/--
info: 'Compose.length_decodeColumns' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.length_decodeColumns

/--
info: 'Compose.length_decodeColumns_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.length_decodeColumns_le

/-- info: 'Compose.mem_decodeTables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.mem_decodeTables

/--
info: 'Compose.doomed_iff_decodeTables' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.doomed_iff_decodeTables

/--
info: 'Compose.candidates_wordOfMerkle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.candidates_wordOfMerkle

/-- info: 'Compose.mem_merkleTables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.mem_merkleTables

/-- info: 'Compose.mem_tableCode_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.mem_tableCode_dec

/-- info: 'Compose.listHi_ours' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.listHi_ours

/-- info: 'Compose.listHi_deployed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Compose.listHi_deployed

/--
info: 'Compose.mem_witnessExtractor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.mem_witnessExtractor

/--
info: 'Compose.knowledgeSoundness_decoded_kc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_decoded_kc

/--
info: 'Compose.knowledgeSoundness_merkle_kc_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_merkle_kc_certified

/--
info: 'Compose.knowledgeSoundness_decoded_kc_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_decoded_kc_certified

/--
info: 'Compose.length_pruneUpTo_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.length_pruneUpTo_le

/--
info: 'Compose.length_laneListAt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.length_laneListAt_le

/-- info: 'Compose.gsShape_witness' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Compose.gsShape_witness

/-- info: 'Compose.gsShape_quotient' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Compose.gsShape_quotient

/-- info: 'Compose.gsShape_wiring' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Compose.gsShape_wiring

/-! ## In the deployed composition -/

/-- info: 'Compose.witnessMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.witnessMatch

/-- info: 'Compose.quotientMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.quotientMatch

/--
info: 'Compose.knowledgeSoundness_deployed_decoded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_deployed_decoded

/--
info: 'Compose.knowledgeSoundness_deployed_decoded_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_deployed_decoded_bits
