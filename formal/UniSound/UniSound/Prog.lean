-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniStatement.Security
import Compose.ListChainKDoom

/-!
# Chain programs: a verifier phase as rounds of reads, checks and challenges

Every phase of the univariate verifier (`UniStatement.reduceWith`, `Flock.verify`, `batch`) reads
the stream and draws challenges in an order that the shape fixes, not the values. Such a phase is a
**chain program** (`ChainProg`): a list of rounds (`Compose.RoundSpec`: a root if `root`, `nv`
scalars, then `ns + 1` challenges), the values it requires to be zero in each round (pushed after
the round's message, before its challenges: `zeros`), a tail of scalars read after the last
challenge (and its zeros), and its result, each a **pure function of the transcript so far** (the
messages and challenges of the rounds before, `Done`).

`ChainProg.run F P` is the canonical channel program of `P` over the permutation `F`: round by
round `nextRoot` (if the round has a root), `nextScalars nv`, `requireZero` of `zeros`, `samples F
(ns + 1)`; then the tail; then the result. **That a phase of the verifier is a chain program** is
an equation of channel programs (`Flock.verify F logN flockMain = P.run F`, for every monad and
permutation): an unfolding of the phase's code, the code-level link between `UniStatement` and the
round-by-round argument. The protocol's states and errors are then stated on `Done`, the
transcript as the chain sees it, and the Fiat–Shamir chain of `Compose.ListChainK` is the chain of
`P.rounds`.

A round's message as the channel reads it is `UMsg`: the root's two halves (`nextRoot`) and the
scalars. `UMsg.Fits` is `Compose.RMsg.Fits` for it.
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics UniStatement

/-- **A round's message as the channel reads it**: the root's two halves if the round has one,
then its scalars. -/
abbrev UMsg := Option (E × E) × List E

/-- **The transcript so far**: each completed round's message and its challenges. -/
abbrev Done := List (UMsg × List E)

/-- A message fits its round: a root exactly when the round has one, and `nv` scalars. -/
def UMsg.Fits (s : Compose.RoundSpec) (m : UMsg) : Prop := m.1.isSome = s.root ∧ m.2.length = s.nv

/-- **The rounds are completed** by `done`: one message fitting each round, `ns + 1` challenges
each. -/
def DoneFits : List Compose.RoundSpec → Done → Prop
  | [], [] => True
  | s :: rs, (m, c) :: d => m.Fits s ∧ c.length = s.ns + 1 ∧ DoneFits rs d
  | _, _ => False

/-- **A chain program**: its rounds, the values each round requires zero (after its message,
before its challenges), the tail of scalars read after the last challenge and the values it
requires zero, and the result; each a function of the transcript so far. -/
structure ChainProg (α : Type) where
  rounds : List Compose.RoundSpec
  zeros : Done → UMsg → List E
  tail : ℕ
  tailZeros : Done → List E → List E
  out : Done → List E → α

namespace ChainProg

variable {α : Type} (P : ChainProg α)

/-- **Every value the program requires zero is zero**, on a completed transcript and its tail:
each round's, given the rounds before it, and the tail's. -/
def ZerosVanish (done : Done) (tl : List E) : Prop :=
  (∀ j (h : j < done.length), ∀ z ∈ P.zeros (done.take j) (done[j]'h).1, z = 0) ∧
    ∀ z ∈ P.tailZeros done tl, z = 0

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- Require every value of a list zero, in order. -/
def requireZeros : List E → ChanM m Unit
  | [] => pure ()
  | z :: zs => do requireZero (m := m) z; requireZeros zs

/-- The rounds from `rs` on, after the transcript `done`. -/
def runRounds : List Compose.RoundSpec → Done → ChanM m Done
  | [], done => pure done
  | s :: rs, done => do
    let root ← if s.root then some <$> nextRoot (m := m) else pure none
    let vals ← nextScalars (m := m) s.nv
    requireZeros (P.zeros done (root, vals))
    let chs ← samples F (s.ns + 1)
    runRounds rs (done ++ [((root, vals), chs)])

/-- **The canonical channel program** of `P` over `F`: its rounds, its tail, its result. -/
def run : ChanM m α := do
  let done ← P.runRounds F P.rounds []
  let tl ← nextScalars (m := m) P.tail
  requireZeros (P.tailZeros done tl)
  return P.out done tl

end With

end ChainProg

end UniSound
