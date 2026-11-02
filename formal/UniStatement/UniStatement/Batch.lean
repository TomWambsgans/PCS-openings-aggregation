-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/verifier.rs` (`batch`, `Opening`).
-- MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Transcript
public import UniStatement.Stacks

/-!
# The batching sumcheck (`batch`, SPEC.md §8): `PCS_OPEN`'s point-claim ABI

**A swappable module.** The verifier hands it one combined (weighted) claim per commitment and the stacks'
layouts; it returns one **point claim** per commitment. `λ` batches the commitments; a sumcheck of degree 2
over the longest stack's variables (the others zero-extended) takes `Σ_k λ^k Σ_u W_k(u) C_k(u)` to its point
`r`; the prover sends each `C_k(r[..vars_k])`; the verifier checks the sum with `W_k(r)` (`weightAt`, over
all of `r`) and the zero extension `Π_{j ≥ vars_k} (1 + r_j)` (collected, `StackBatchTerminal`). With Flock's
bit-slice end (extension B), `C1`'s call also carries the bit-slice claim. Extension W (`Claims.weighted`)
skips this module: the weighted claims go to `PCS_OPEN` as they are.
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

/-- **`batch(combined, layouts, bit_slice)`**: `λ`, the sumcheck over the longest stack, the stacks'
values at its point, the terminal collected; one point claim per commitment, in `combined`'s order. -/
def batch (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) : ChanM m (List (Commitment × Opening)) := do
  let lambda ← sample F
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, _) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let (r, last) ← sumcheck F target 3 (List.replicate vars none)
  let values ← nextScalars (m := m) combined.length
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  let (sum, _, openings, _) := (combined.zip values).foldl
    (fun (acc : E × E × Array (Commitment × Opening) × Option Combined) ((commitment, claim), value) ↦
      let (sum, scale, openings, bitSlice) := acc
      let layout := layoutOf commitment
      let weight := weightAt claim layout r
      let extension := (List.range' layout.vars (vars - layout.vars)).foldl
        (fun e j ↦ e * (1 + r.getD j 0)) 1
      let (mine, rest) := if commitment == .c1 then (bitSlice, none) else (none, bitSlice)
      (sum + scale * weight * extension * value, scale * lambda,
        openings.push (commitment, .point (r.take layout.vars) value mine), rest))
    (0, 1, #[], bitSlice)
  requireZero (m := m) (sum + last)
  return openings.toList

end With

end UniStatement

end
