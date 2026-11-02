/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

Review of layer F3 (`formal/QuotientSecurity/Hiding`): what its theorems rest on, what their view
leaves out, and the size of the (S) term. Run from `formal/`:

  lake build QuotientSecurity.Hiding && lake env lean Review/HidingReview.lean
-/
import QuotientSecurity.Hiding
open Lean Elab Command

/-! ## Axioms -/

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

#sweep QuotientSecurity.Hiding
#escapes QuotientSecurity.Hiding

namespace QuotientSecurity.Hiding.Review

open QuotientSecurity.Hiding
open scoped ENNReal

set_option exponentiation.threshold 1024

/-! ## The (S) term is not below `2^-127`

`hidden_prEvent_le_bound`'s docstring (`Layout.lean:404-406`) says its (S) term
`((2k + |K| + 1)·|E| + |K|^4)/|E|^2` is "below `2^-127` at `k = 6`, `|K| = 2^64`, `|E| = 2^192`". It is
`2^-127 + 13·2^-192`: above `2^-127` (by `13·2^-192`; `formal/README.md`'s "~2^-127" is right). -/

theorem sTerm_eq : ((2 * 6 + 2 ^ 64 + 1) * 2 ^ 192 + (2 ^ 64) ^ 4 : ℕ) = 2 ^ 257 + 13 * 2 ^ 192 := by
  norm_num

/-- The numerator over `|E|^2 = 2^384`, against `2^-127 = 2^257 / 2^384`. -/
theorem sTerm_gt : (2 ^ 257 : ℕ) < (2 * 6 + 2 ^ 64 + 1) * 2 ^ 192 + (2 ^ 64) ^ 4 := by
  norm_num

theorem sTerm_not_below :
    ¬ ((((2 * 6 + 2 ^ 64 + 1) * 2 ^ 192 + (2 ^ 64) ^ 4 : ℕ) : ℝ≥0∞) / (((2 ^ 192) ^ 2 : ℕ) : ℝ≥0∞) <
      (((2 ^ 257 : ℕ) : ℝ≥0∞) / (((2 ^ 192) ^ 2 : ℕ) : ℝ≥0∞))) := by
  refine not_lt.mpr (ENNReal.div_le_div_right ?_ _)
  exact_mod_cast sTerm_gt.le

/-! ## The view leaves out what the root hashes

`hidden_view_evalDistEq` and `hidden_prEvent_le_bound` are about `viewMap`: the six lane rounds, `f¹`,
and the rows at `Q`. The root in the calldata and the Merkle siblings of the opening hash **every** row of
the first commitment, and every row together is the whole stack. For two tables that differ at one entry
the layout does not randomize (a block lane past its first piece, or the overflow lane off `held`'s
share), the whole stacks never agree, whatever the two paddings: so the distribution of everything the
root is computed from is disjoint for the two tables, and the hiding of the root and the siblings rests
entirely on the random-oracle step (`HIDING.md`, step 3; `Merkle.lean`'s docstring: "the oracle exchange
itself is not formalized here"), which no theorem of the layer states. -/

variable {K : Type} [Field K] {ι Y : Type} [DecidableEq ι] [DecidableEq Y]

theorem stack_ne_of_entry_ne (L : HiddenLayout ι Y) {d d' : ι → Y → K} {l : ι} {y : Y}
    (hr : ¬ L.randPos l y) (hs : ¬ (l = L.ov ∧ y ∈ L.held)) (hd : d l y ≠ d' l y)
    (r r' : ι → Y → K) :
    L.stackD d + L.stackR r ≠ L.stackD d' + L.stackR r' := by
  intro h
  have := congrFun (congrFun h l) y
  simp only [Pi.add_apply, HiddenLayout.stackD, HiddenLayout.stackR, LinearMap.coe_mk,
    AddHom.coe_mk, hr, hs, ite_false, add_zero] at this
  exact hd this

end QuotientSecurity.Hiding.Review

/-! ## Headline theorems -/

#print axioms QuotientSecurity.Hiding.HiddenLayout.hidden_view_evalDistEq
#print axioms QuotientSecurity.Hiding.HiddenLayout.hidden_prEvent_le_bound
#print axioms QuotientSecurity.Hiding.HiddenLayout.unopened_row_le
#print axioms QuotientSecurity.Hiding.firstEval_surjective_of_degrees
#print axioms QuotientSecurity.Hiding.exists_unopened_vector
#print axioms QuotientSecurity.Hiding.card_not_span_four_le
#print axioms QuotientSecurity.Hiding.witness_lane_pattern
#print axioms QuotientSecurity.Hiding.quotient_lane_pattern
#print axioms QuotientSecurity.Hiding.Review.sTerm_not_below
#print axioms QuotientSecurity.Hiding.Review.stack_ne_of_entry_ne

/-! ## What the end theorem assumes

The signature of the layer's end theorem: (Q) (`hQ`), the weights' fit (`hW`) and the lane pattern are
hypotheses about an abstract `HiddenLayout`, an abstract code `enc`, abstract weights `Wc`; nothing in the
layer builds the deployed layout (`Layout::hidden` with 40 / 63 lanes), its weights (`Layout::tensors`), or
leanVM's code, and nothing instantiates the theorem with them. (R) stays in the bound as
`Pr[¬ RoundsReached]`, bounded by nothing. -/
#check @QuotientSecurity.Hiding.HiddenLayout.hidden_prEvent_le_bound
