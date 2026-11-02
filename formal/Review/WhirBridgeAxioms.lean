/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

Review of layer F2 (`formal/WhirBridge`), experiment 1: what the bridge rests on, and which layouts it
is about. Run from `formal/WhirBridge` (built as its README says):

  lake env lean ../Review/WhirBridgeAxioms.lean
-/
import WhirBridge
open Lean Elab Command

/-! ## Axioms -/

/-- Every declaration of a namespace, and the axioms it reaches beyond the three standard ones. -/
elab "#sweep " ns:ident : command => do
  let env ← getEnv
  let mut bad : Array (Name × Array Name) := #[]
  let mut n : Nat := 0
  for (name, _) in env.constants.toList do
    if ns.getId.isPrefixOf name && !name.isInternal then
      n := n + 1
      let axs ← liftCoreM (Lean.collectAxioms name)
      let extra := axs.filter fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]
      if !extra.isEmpty then bad := bad.push (name, extra)
  logInfo m!"{ns.getId}: checked {n} declarations; outside the three standard axioms: {bad}"

/-- Opaque constants, axioms and `implemented_by` overrides declared under a namespace prefix. -/
elab "#escapes " ns:ident : command => do
  let env ← getEnv
  let mut out : Array (Name × String) := #[]
  for (name, ci) in env.constants.toList do
    if ns.getId.isPrefixOf name then
      match ci with
      | .opaqueInfo _ => out := out.push (name, "opaque")
      | .axiomInfo _ => out := out.push (name, "axiom")
      | _ => pure ()
      if (Lean.Compiler.implementedByAttr.getParam? env name).isSome then
        out := out.push (name, "implemented_by")
  logInfo m!"{ns.getId}: opaque / axiom / implemented_by constants: {out}"

#sweep WhirBridge
#escapes WhirBridge
#escapes LeanVM.Protocol
#escapes LeanVM.Parameters

#print axioms WhirBridge.Layout.check_eq
#print axioms WhirBridge.isMultiaffine_layoutClaimWeight
#print axioms WhirBridge.isMultiaffine_gadgetWeight
#print axioms WhirBridge.openingSpec
#print axioms WhirBridge.whirEps_le
#print axioms WhirBridge.eBatch_two
#print axioms WhirBridge.eBatch_three
#print axioms WhirBridge.listMax_ours
#print axioms WhirBridge.layouts_ok
#print axioms WhirBridge.layouts_valid
#print axioms WhirBridge.layouts_shape
#print axioms WhirBridge.holds_iff
#print axioms WhirBridge.holds_iff_hidden
#print axioms WhirBridge.Layout.holds_iff
#print axioms WhirBridge.gadget_holds_iff
#print axioms WhirBridge.Layout.extra_holds_iff
#print axioms WhirBridge.Layout.openingDoom_iff
#print axioms WhirBridge.Layout.joint_of_not_doom
#print axioms WhirBridge.candidates_ours
#print axioms WhirBridge.variant_sound
#print axioms WhirBridge.variant_bound_le
#print axioms WhirBridge.family_sound
#print axioms WhirBridge.family_bound_le
#print axioms WhirBridge.openingVerify_imp
#print axioms WhirBridge.opening_sound
#print axioms WhirBridge.opening_bound_le
#print axioms WhirBridge.ours_sound

/-! ## Which layouts the bridge is about

(Updated with the fix.) The review found that `WhirBridge.Layout` was `Layout::new`'s public layout only
and that the bridge's `witnessLayout` / `quotientLayout` were the pre-hiding ones (33 and 59 block lanes),
so the deployed witness and quotient openings were outside it. `WhirBridge.Layout` now has every field of
the Rust struct, `Layout.check` transcribes both branches of the closure, and the protocol's layouts are
built by `Layout.hidden` (`WhirBridge/Layouts.lean`). Since the hidden layout's redesign for condition
(R) (no share lane; the overflow lane `32`, seven random lanes after it; the gadget batched as one more
stack claim of value zero) the bridge transcribes that layout: -/

/-- The bridge's witness and quotient layouts have the deployed lane counts `40` and `63`. -/
example : ∀ r, 17 ≤ r → r ≤ 22 →
    (WhirBridge.witnessLayout r).lanes.length = 40 ∧ (WhirBridge.quotientLayout r).lanes.length = 63 := by
  decide +kernel

/-- In the deployed witness and quotient layouts lanes `33 .. 39` are random and lane `32` holds the
overflow (`review_f2f3.rs`, `f3_design_facts_hold_at_every_size`). -/
example : ((WhirBridge.witnessLayout 17).lanes.zipIdx.filter (·.1 = .random)).map (·.2) =
      [33, 34, 35, 36, 37, 38, 39] ∧ (WhirBridge.witnessLayout 17).lanes[32]? = some .overflow ∧
    ((WhirBridge.quotientLayout 17).lanes.zipIdx.filter (·.1 = .random)).map (·.2) =
      [33, 34, 35, 36, 37, 38, 39] ∧ (WhirBridge.quotientLayout 17).lanes[32]? = some .overflow := by
  decide +kernel

/-! `Test/Check.lean` accepts deployed witness and quotient openings of the redesigned layouts (the
vectors of `crates/quotient/tests/whir_bridge_vector.rs`), rejects them against the weight without the
gadget's term, and recomputes the 18 layouts' prefixes. -/
