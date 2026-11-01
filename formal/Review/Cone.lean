import QuotientSecurity
open Lean Elab Command

/-! Review experiment 3: the dependency cone of the end theorems, by package. -/

/-- The constants a declaration reaches, transitively (types and values). -/
partial def cone (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.type.getUsedConstants do
        if !seen.contains c then todo := todo.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do
          if !seen.contains c then todo := todo.push c
  return seen

elab "#cone " id:ident : command => do
  let env ← getEnv
  let s := cone env id.getId
  let mut ark : Array Name := #[]
  let mut vcv : Nat := 0
  let mut tot : Nat := 0
  for n in s.toList do
    tot := tot + 1
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`ArkLib).isPrefixOf mod then ark := ark.push n
      if (`VCVio).isPrefixOf mod then vcv := vcv + 1
  let rbr := s.contains `QuotientSecurity.verifier_rbrKnowledgeSoundness
  let chi := s.contains `QuotientSecurity.ChiCircuit.determined ||
    s.contains `QuotientSecurity.cells_determined
  logInfo m!"{id.getId}: {tot} constants, {vcv} from VCVio, ArkLib: {ark}; \
    reaches verifier_rbrKnowledgeSoundness: {rbr}; reaches the circuit argument: {chi}"

#cone QuotientSecurity.Instance.soundness
#cone QuotientSecurity.Instance.zero_knowledge
#cone QuotientSecurity.Instance.completeness
