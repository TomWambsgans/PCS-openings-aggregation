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

#print axioms WhirBridge.openingCheck_eq
#print axioms WhirBridge.isMultiaffine_claimWeight
#print axioms WhirBridge.openingSpec
#print axioms WhirBridge.whirEps_le
#print axioms WhirBridge.eBatch_two
#print axioms WhirBridge.listMax_ours
#print axioms WhirBridge.layouts_ok
#print axioms WhirBridge.holds_iff
#print axioms WhirBridge.openingDoom_iff
#print axioms WhirBridge.joint_of_not_doom
#print axioms WhirBridge.candidates_ours
#print axioms WhirBridge.variant_sound
#print axioms WhirBridge.variant_sound_table
#print axioms WhirBridge.variant_bound_le
#print axioms WhirBridge.family_sound
#print axioms WhirBridge.family_bound_le
#print axioms WhirBridge.layouts_nodup

/-! ## Which layouts the bridge is about

`WhirBridge.Layout` is `Layout::new`'s public layout only (`blocks : List ℕ`, every lane a block of the
table): it has no overflow lane, no share lane, no random lanes, no first pieces and no odd-lane swaps,
and `weight` transcribes only the `piece = None` branch of `opening::verify`'s closure
(`opening.rs:699-701`). The deployed witness and quotient layouts are `Layout::hidden`
(`protocol.rs:116-129`, 40 and 63 lanes; `crates/quotient/tests/review_f2f3.rs` checks it), so the
bridge's `witnessLayout` and `quotientLayout` are the pre-hiding layouts. -/

/-- The bridge's witness and quotient layouts have the pre-hiding lane counts `33` and `59`; the
deployed ones have `40` and `63` (`protocol::witness_layout`, `protocol::quotient_layout`). -/
example : ∀ r, 17 ≤ r → r ≤ 22 →
    (WhirBridge.witnessLayout r).lanes = 33 ∧ (WhirBridge.quotientLayout r).lanes = 59 := by
  decide +kernel

example : ∀ r, 17 ≤ r → r ≤ 22 →
    (WhirBridge.witnessLayout r).lanes ≠ 40 ∧ (WhirBridge.quotientLayout r).lanes ≠ 63 := by
  decide +kernel

/-- In the bridge, every lane of the witness layout holds a block of the table (the first `32` the
row polynomials, the `33`rd the masks' chunk); in the deployed layout lanes `1, 7, 13, 19, 25, 31, 39`
are random and lane `38` holds the overflow. -/
example : WhirBridge.witnessLayout 17 =
    ⟨20, 20, (List.range 32) ++ [32]⟩ := by
  decide +kernel

/-- The bridge's `weight` at a point is the public layout's closure: on the cube it reads lane `l`'s
entry `o` with `eq(p_high, block_l) · eq(p_low, o)`, so a weight that is zero on every lane's first
piece (the hidden layouts' `first_share` correction, `opening.rs:705-710`) is not among the weights the
bridge's `openingCheck` builds for a nonzero claim point. -/
example : WhirBridge.Layout.logLane (WhirBridge.witnessLayout 17) = 14 := by decide
