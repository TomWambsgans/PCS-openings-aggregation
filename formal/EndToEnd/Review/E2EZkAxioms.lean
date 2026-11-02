-- Review experiment (adversarial ZK review): axioms of the zero-knowledge headline theorems and a
-- sweep of every constant of this repository's modules reachable from them.
import ZK.Final
import ZK.ProverBridge
import ZK.ProverBridgeDuplex
import ZK.ProverBridgeMerkle
import ZK.Axioms

open Lean Elab Command

/-- The axioms a constant depends on, memoized (type and value). -/
partial def axiomsOfM (env : Environment) (memo : IO.Ref (Std.HashMap Name (Array Name)))
    (c : Name) : IO (Array Name) := do
  if let some r := (← memo.get)[c]? then return r
  memo.modify (·.insert c #[])
  let some ci := env.find? c | return #[]
  let mut acc : Std.HashSet Name := {}
  if let .axiomInfo _ := ci then acc := acc.insert c
  for d in ci.getUsedConstantsAsSet.toList do
    for a in (← axiomsOfM env memo d) do acc := acc.insert a
  let r := acc.toArray
  memo.modify (·.insert c r)
  return r

def ourRoots : List String :=
  ["ZK", "QuotientZk", "QuotientSecurity", "QuotientRpm", "PcsQuotient", "Field", "Completeness",
    "Bridge", "Implementation", "Circuit", "Compose", "WhirBridge"]

def isOurModule (m : Name) : Bool :=
  ourRoots.any fun r ↦ m.getRoot == r.toName

elab "#sweep_axioms" : command => do
  let env ← getEnv
  let memo ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut nThm : Nat := 0
  let mut nOur : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut opaques : Array Name := #[]
  let mut implBy : Array Name := #[]
  for (c, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless isOurModule m do continue
    nOur := nOur + 1
    if let .opaqueInfo _ := ci then
      unless c.isInternal do opaques := opaques.push c
    if (Compiler.implementedByAttr.getParam? env c).isSome || isExtern env c then
      implBy := implBy.push c
    if let .thmInfo _ := ci then
      nThm := nThm + 1
      let ax ← axiomsOfM env memo c
      let extra := ax.filter fun a ↦ !std.contains a
      unless extra.isEmpty do bad := bad.push (c, extra)
  logInfo m!"constants of our modules: {nOur}, theorems swept: {nThm}"
  logInfo m!"theorems with an axiom beyond propext/choice/Quot.sound: {bad.size}: {bad.toList.take 50}"
  logInfo m!"opaque constants of our modules: {opaques.size}: {opaques.toList.take 50}"
  logInfo m!"implemented_by/extern constants of our modules: {implBy.size}: {implBy.toList.take 50}"

#sweep_axioms

-- The headline theorems.
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed_final
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed_whir
#print axioms PcsQuotient.EndToEnd.proverBridge_whir
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed_end
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_end
#print axioms PcsQuotient.EndToEnd.coreClose_of_joint
#print axioms PcsQuotient.EndToEnd.deployedJointData_valid
#print axioms PcsQuotient.EndToEnd.zeroKnowledgeWith_of_core
#print axioms PcsQuotient.EndToEnd.rpmIdeal_eq
#print axioms PcsQuotient.EndToEnd.zeroKnowledgeWith_of_coinFree
#print axioms PcsQuotient.EndToEnd.hTWD
#print axioms PcsQuotient.EndToEnd.hTQD
#print axioms PcsQuotient.EndToEnd.hsatD
#print axioms PcsQuotient.EndToEnd.eD_bijective
#print axioms QuotientZk.zk_rom
#print axioms QuotientZk.zk_rom_approx
#print axioms QuotientZk.DRpm.zk_rpm_skel_approx
#print axioms QuotientZk.Deployed.Fresh.fsFresh_setup_deployed_bits
#print axioms QuotientZk.Instance.jointHVZKε_of_linkV
#print axioms QuotientZk.Instance.claims_simTW
#print axioms QuotientZk.Instance.claims_simTQ

-- Is the deployed simulator a compiled definition? (Expected to fail if any part is noncomputable.)
open PcsQuotient PcsQuotient.EndToEnd QuotientZk.Instance in
def deployedSimulatorCompiled (R : Renderer LeanVM.Parameters.K LeanVM.Parameters.E)
    (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) :=
  zkSimulator (fun _ ↦ deployedPub deployedRep)
    (fun stmt ↦ deployedSimV deployedRep P₀D (stmtWD stmt) Primitives.F192.Y R inKD sigmaAtD)
    (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt
