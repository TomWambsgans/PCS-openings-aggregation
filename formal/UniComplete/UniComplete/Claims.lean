-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Batch

/-!
# What the verifier's relations and claims mean on the stacks

The verifier states its relations as terms `coefficient · column(point)` (`UniStatement.Term`) and combines each
commitment's by the powers of `ρ` (`combine`); `PCS_OPEN`, through the batching sumcheck, checks each combined claim
against its committed stack. Their meaning on a stack (`2^vars` words of `K`, read in `E`):

* **a term's value** (`termEval`): the pairing of its weight on the stack (`denseWeight` of the one-term claim: its
  column's `eq(point, ·)` on the column's blocks, a limb scaled by `(1, y, y²)`, Frobenius twists as `eq^(2^k)`,
  the ring-switch term as `Φ(eq(p, ·))`, `q_flock`'s slot `j` at the words `j + 256 u`) with the stack's words;
* **a relation holds** (`Relation.Holds`): its terms' values add up to its value, each term on its own commitment's
  stack and layout;
* **a combined claim holds** (`Combined.Holds`): the pairing of its weight (`denseWeight`) with the stack is its
  value. This is what the batching sumcheck reduces to its point claim (and what `PCS_OPEN`'s weighted claim,
  extension W, would check directly).
-/

namespace UniComplete

open UniStatement LeanVM.Parameters

/-- The pairing `Σ_u w_u · s_u` of a weight with a stack's words (over the weight's length). -/
def dotK (w : Array E) (s : Array K) : E :=
  (List.range w.size).foldl (fun acc u ↦ acc + w.getD u 0 * ofK (s.getD u 0)) 0

/-- A term as a one-term combined claim. -/
def termClaim (t : Term) : Combined := ⟨[t.point], [(t.column, 0, t.twist, t.coefficient)], 0, 1⟩

/-- **A term's value** on a stack: its weight paired with the stack. -/
def termEval (layout : StackLayout) (stack : Array K) (ringMap : Option (List E)) (t : Term) : E :=
  dotK (denseWeight (termClaim t) layout ringMap) stack

/-- **A relation holds** of the three stacks: its terms' values (each on its column's commitment) add up to its
value. -/
def Relation.Holds (layoutOf : Commitment → StackLayout) (stackOf : Commitment → Array K)
    (ringMap : Option (List E)) (rel : Relation) : Prop :=
  (rel.terms.map fun t ↦ termEval (layoutOf t.column.commitment) (stackOf t.column.commitment) ringMap t).sum =
    rel.value

/-- **A combined claim holds** of its stack: its weight paired with the stack is its value. -/
def Combined.Holds (layout : StackLayout) (stack : Array K) (ringMap : Option (List E)) (claim : Combined) :
    Prop :=
  dotK (denseWeight claim layout ringMap) stack = claim.value

end UniComplete
