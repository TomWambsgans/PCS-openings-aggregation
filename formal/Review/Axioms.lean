import QuotientSecurity
open Lean Elab Command

/-! Review experiment 1: axiom sweep over every declaration of the namespace. -/

/-- Every declaration of the `QuotientSecurity` namespace, and the axioms it reaches beyond the
three standard ones. -/
elab "#sweep" : command => do
  let env ← getEnv
  let mut bad : Array (Name × Array Name) := #[]
  let mut n : Nat := 0
  for (name, _) in env.constants.toList do
    if (`QuotientSecurity).isPrefixOf name && !name.isInternal then
      n := n + 1
      let axs ← liftCoreM (Lean.collectAxioms name)
      let extra := axs.filter fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]
      if !extra.isEmpty then bad := bad.push (name, extra)
  logInfo m!"checked {n} declarations; outside the three standard axioms: {bad}"

#sweep

/-- Opaque constants or axioms declared in the namespace. -/
elab "#opaques" : command => do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if (`QuotientSecurity).isPrefixOf name then
      match ci with
      | .opaqueInfo _ => out := out.push name
      | .axiomInfo _ => out := out.push name
      | _ => pure ()
  logInfo m!"opaque/axiom constants in the namespace: {out}"

#opaques
#print QuotientSecurity.le24
