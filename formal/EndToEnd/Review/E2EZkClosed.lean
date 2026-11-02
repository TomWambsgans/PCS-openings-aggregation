-- Review experiment (adversarial ZK review, after the ZK core 40f1150): the axioms of
-- `zeroKnowledge_closed` and of every theorem of this repository's modules in the `ZK` library's
-- closure; which proofs the end theorem rests on (the `ClaimsND` chain, not the legacy all-masks
-- `hTW`/`hTQ` theorems); the simulator reads no witness.
import ZK

open Lean Elab Command

/-- The axioms a constant depends on, memoized (type and value). -/
partial def axiomsOfC (env : Environment) (memo : IO.Ref (Std.HashMap Name (Array Name)))
    (c : Name) : IO (Array Name) := do
  if let some r := (← memo.get)[c]? then return r
  memo.modify (·.insert c #[])
  let some ci := env.find? c | return #[]
  let mut acc : Std.HashSet Name := {}
  if let .axiomInfo _ := ci then acc := acc.insert c
  for d in ci.getUsedConstantsAsSet.toList do
    for a in (← axiomsOfC env memo d) do acc := acc.insert a
  let r := acc.toArray
  memo.modify (·.insert c r)
  return r

def ourRootsC : List String :=
  ["ZK", "QuotientZk", "QuotientSecurity", "QuotientRpm", "PcsQuotient", "Field", "Completeness",
    "E2ECompleteness", "Bridge", "Implementation", "Circuit", "Compose", "WhirBridge"]

elab "#sweep_axioms_closed" : command => do
  let env ← getEnv
  let memo ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut nThm : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut odd : Array Name := #[]
  for (c, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless ourRootsC.any (fun r ↦ m.getRoot == r.toName) do continue
    if let .opaqueInfo _ := ci then
      unless c.isInternal do odd := odd.push c
    if (Compiler.implementedByAttr.getParam? env c).isSome || isExtern env c then
      odd := odd.push c
    if let .thmInfo _ := ci then
      nThm := nThm + 1
      let ax ← axiomsOfC env memo c
      let extra := ax.filter fun a ↦ !std.contains a
      unless extra.isEmpty do bad := bad.push (c, extra)
  logInfo m!"theorems swept: {nThm}; with another axiom: {bad.size}: {bad.toList.take 50}; \
    opaque/implemented_by/extern: {odd.size}: {odd.toList.take 50}"

#sweep_axioms_closed

/-- Does `n` use `target` (transitively)? -/
partial def usesConstC (target : Name) (n : Name) : StateT NameSet CoreM Bool := do
  if n == target then return true
  if (← get).contains n then return false
  modify (·.insert n)
  let some ci := (← getEnv).find? n | return false
  for r in ci.getUsedConstantsAsSet.toList do
    if ← usesConstC target r then return true
  return false

-- Expected: the legacy all-masks theorems unused, the `ClaimsND` chain used.
#eval show CoreM (List (Name × Bool)) from do
  let e := ``PcsQuotient.EndToEnd.zeroKnowledge_closed
  let ts := [``QuotientZk.Instance.jointHVZK_of_linkV, ``QuotientZk.Instance.zk_rpm_deployed_instance,
    ``QuotientZk.Instance.joint_hzkV, ``QuotientZk.Instance.jointHVZKε_of_linkV,
    ``QuotientZk.Instance.prob_not_claimsND_le, ``QuotientZk.Instance.prob_not_goodT_bits,
    ``PcsQuotient.EndToEnd.proverBridge_of_detG, ``PcsQuotient.EndToEnd.hbad_deployed,
    ``PcsQuotient.EndToEnd.coreD, ``QuotientZk.DRpm.zk_rpm_skel_approx,
    ``QuotientZk.Deployed.Fresh.fsFresh_setup_deployed_bits]
  ts.mapM fun t ↦ return (t, ← (usesConstC t e).run' {})

#print axioms PcsQuotient.EndToEnd.zeroKnowledge_closed
#print axioms PcsQuotient.EndToEnd.coreD
#print axioms PcsQuotient.EndToEnd.hbad_deployed
#print axioms PcsQuotient.EndToEnd.hprover_whir

-- The end theorem's statement, as elaborated.
#check @PcsQuotient.EndToEnd.zeroKnowledge_closed

-- The simulator reads no witness: in `zeroKnowledge_closed`'s statement (above) the simulator is
-- `zkSimulator` at `deployedPub deployedRep` and `deployedSimV …`, whose arguments hold no witness,
-- and `ZeroKnowledgeWith` quantifies the witness after the simulator. (Restating `simV_deployed` at
-- the deployed instance exceeds the elaborator's recursion depth, so it is not repeated here.)
