-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.ListChainUDoom

/-!
# The composed run with its whole Keccak-256 transcript

The names the `≥ 128`-bit composition shares (`FirstDoom.lean`, `ListChainUDoom128.lean`,
`SeedPair.lean`):

* **`expL view X ops`**: the run before the openings `X` (for the composition, `preU`: the
  adversary, its queries logged, then the chain), then the openings one after the other
  (`opsRun`), **every Keccak-256 query of the whole run logged**; `expU` is that run with the log
  dropped (`expU_eq`).
* **`DoomF view ops z`**: some opening accepts while doomed **at the end of the run**: every
  candidate of the word extracted under its root from the whole run's transcript violates one of its
  claims. (`ListChainKDoom.lean`'s `EOp` reads each opening's doom at the end of its own stage.)
* **`PairTr tag tr`**: two answers of the transcript, the first `tag` followed by the second's first
  `32 − |tag|` bytes (the univariate seed's `name ‖ iv[0:16]`, `iv` an answer).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

section Defs

variable {F St M Pf : Type} [SampleableType F]

/-- The outcome after the openings: the proof, the challenges, the verdicts, the adversary's
transcript. -/
def opsOut (x : PreK Pf F) (bs : List Bool) : OutK Pf F (List Bool) := ((x.1, (x.2.1, bs)), x.2.2)

/-- **The run with its whole Keccak-256 transcript**: `X`, then the openings, every Keccak-256 query
logged. -/
def expL (view : Pf → St × List (RMsg F)) (X : OracleComp KeccakCalls (PreK Pf F))
    (ops : List (WhirOp Pf F M)) : OracleComp KeccakCalls (OutK Pf F (List Bool) × Transcript) :=
  (simulateQ logImplKC (X >>= fun x => opsOut x <$> opsRun view ops x.1 x.2.1)).run []

/-- **`expU` is the run before the openings (`preU`), then the openings.** -/
theorem expU_eq (U : ChainSpecU F St) (view : Pf → St × List (RMsg F))
    (A : OracleComp KeccakCalls Pf) (ops : List (WhirOp Pf F M)) :
    expU U view A (opsRun view ops) =
      preU U view A >>= fun x => opsOut x <$> opsRun view ops x.1 x.2.1 := by
  simp only [expU, verU, preU, opsOut, bind_assoc, pure_bind, map_eq_bind_pure_comp,
    Function.comp_def]

/-- **Some opening accepts while doomed at the end of the run**: its verdict is `true` and every
candidate of the word extracted under its root from the whole transcript violates one of its
claims. -/
def DoomF (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
    (z : OutK Pf F (List Bool) × Transcript) : Prop :=
  ∃ k, ∃ hk : k < ops.length, z.1.1.2.2.getD k false = true ∧
    OpeningDoomed ops[k].S.L ops[k].S.R (WhirOp.input view ops[k] z.1.1.1 z.1.1.2.1)
      (cacheOfTr z.2)

end Defs

/-- **Two answers of a transcript, the first `tag ‖` the second's first `32 − |tag|` bytes.** -/
def PairTr (tag : List UInt8) (tr : Transcript) : Prop :=
  ∃ e ∈ tr, ∃ e' ∈ tr, e.2.toList = tag ++ e'.2.toList.take (32 - tag.length)

end Compose
