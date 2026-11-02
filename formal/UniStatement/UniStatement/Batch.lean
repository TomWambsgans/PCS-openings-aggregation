-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/verifier.rs` (`batch`, `Opening`).
-- MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Transcript
public import UniStatement.Stacks

/-!
# The batching sumcheck (`batch`, SPEC.md §8 and §13): `PCS_OPEN`'s point-claim ABI

**A swappable module.** The verifier hands it one combined (weighted) claim per commitment and the stacks'
layouts; it returns one **point claim** per commitment. `λ` batches the commitments; a sumcheck of degree 2
over the longest stack's variables (the others zero-extended) takes `Σ_k λ^k Σ_u W_k(u) C_k(u)` to its point
`r`; the prover sends each `C_k(r[..vars_k])`; the verifier checks the sum with `W_k(r)` (`weightAt`, over
all of `r`, the ring-switch term by its map) and the zero extension `Π_{j ≥ vars_k} (1 + r_j)` (collected,
`StackBatchTerminal`). With Flock's bit-slice end (extension B), `C1`'s call also carries the bit-slice claim.
Extension W (`Claims.weighted`) skips this module: the weighted claims go to `PCS_OPEN` as they are.

**Flock's matrices' reduction runs here** (iteration 2, lever 4a; `Flock.Pending`): its sum
`Σ_(x, y) G(x, y) L̂(x) ŝ(y)` over `k + 6` variables joins the batch as the next power of `λ` (`λ³`, after the
three stacks), zero-extended by `eq(·, 0)` on the batch's other variables, so its rounds are the batch's first
`k + 6`. After the stacks' values the prover sends `a = Â0`, `b = B̂0` at `(ρ, row_low, chi_in, σ, chi_in')`,
`(ρ, σ)` the batch's first coordinates, and the terminal adds `λ³ (a + α b) L̂(ρ) ŝ(σ) Π_{j ≥ k+6} (1 + r_j)`
(`Pending.terminal`). Without the slices (lever 5a, extension B) the terminal is not collected: it becomes the
bit-slice claim `Σ_i μ_i ẑ(i, p) = Σ (stack terms) + last` (`Pending.combination`), which joins `C1`'s call.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics

/-- **What a commitment's one `PCS_OPEN` call carries** (`Opening`). -/
inductive Opening where
  /-- One weighted claim (extension W). -/
  | weighted (claim : Combined)
  /-- One point claim (the ABI), and on `C1` with Flock's bit-slice end the bit-slice claim. -/
  | point (pt : List E) (value : E) (bitSlice : Option Combined)
  deriving Inhabited

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`batch(combined, layouts, bit_slice, ring_map, pending)`**: `λ`, the sumcheck over the longest stack (its
target with Flock's pending matrices' claim at the next power of `λ`), the stacks' values at its point, then
`a`, `b` if the matrices are pending; the terminal collected, but for the pending matrices without their slices,
whose terminal is the bit-slice claim on `C1`. One point claim per commitment, in `combined`'s order, and the
claims on `A0`, `B0` the pending matrices leave (`flockPoint`: `q_flock`'s point of the slices). -/
def batch (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E) := none)
    (pending : Option (Flock.Pending × List E) := none) :
    ChanM m (List (Commitment × Opening) × Option Flock.MatrixClaim) := do
  let lambda ← sample F
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, scale) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let target := match pending with
    | some (p, _) => target + scale * p.claim
    | none => target
  let (r, last) ← sumcheck F target 3 (List.replicate vars none)
  let values ← nextScalars (m := m) combined.length
  let matrices ← match pending with
    | some _ => do
      let a ← nextScalar (m := m)
      let b ← nextScalar (m := m)
      pure (some (a, b))
    | none => pure none
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  let (sum, scale, openings, _) := (combined.zip values).foldl
    (fun (acc : E × E × Array (Commitment × Opening) × Option Combined) ((commitment, claim), value) ↦
      let (sum, scale, openings, bitSlice) := acc
      let layout := layoutOf commitment
      let weight := weightAt claim layout r ringMap
      let extension := (List.range' layout.vars (vars - layout.vars)).foldl
        (fun e j ↦ e * (1 + r.getD j 0)) 1
      let (mine, rest) := if commitment == .c1 then (bitSlice, none) else (none, bitSlice)
      (sum + scale * weight * extension * value, scale * lambda,
        openings.push (commitment, .point (r.take layout.vars) value mine), rest))
    (0, 1, #[], bitSlice)
  match pending, matrices with
  | some (p, flockPoint), some (a, b) =>
    let extension := (List.range' p.rounds (vars - p.rounds)).foldl (fun e j ↦ e * (1 + r.getD j 0)) 1
    if p.hasSlices then
      let (value, claim) := p.terminal r a b
      requireZero (m := m) (sum + scale * value * extension + last)
      return (openings.toList, some claim)
    else
      -- Flock (a): the terminal leaves `Σ_i μ_i ẑ(i, p) = sum + last`, a bit-slice claim joining C1's call.
      let (weights, claim) := p.combination r a b extension scale
      let relation : Relation := ⟨(weights.zip (List.range weights.length)).map
        (fun (c, i) ↦ ⟨.qflockBits, flockPoint, i, c⟩), sum + last⟩
      let combination := combine [relation] .c1 1
      let openings := openings.map fun (c, o) ↦ match c, o with
        | .c1, .point pt v _ => (c, .point pt v combination)
        | _, _ => (c, o)
      return (openings.toList, some claim)
  | _, _ =>
    requireZero (m := m) (sum + last)
    return (openings.toList, none)

end With

end UniStatement

end
