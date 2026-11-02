-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.ComputableClosed

/-!
# Running the compiled wiring value `σ(t)`

`lake env lean Review/ZkSigmaEval.lean` (from `formal/EndToEnd`; about an hour interpreted): the
simulator's wiring value `sigmaAtC` (`ZK/ComputableFacts.lean`, the barycentric accumulation over the
`2^24` cells of the deployed circuit) at cell `5` is the point of cell `5`'s successor under the deployed
wiring (`membership.sigma`), as `sigmaAtC_eq` and `sigmaPoly_eval_cell` say it must be (at a cell every
term but one vanishes, and that one's barycentric weight is `1`). It prints `true` and the time.
-/

open PcsQuotient.EndToEnd Primitives LeanVM.Parameters

/-- `σ` at cell `5`, against its successor's point, timed. -/
def runSigma : IO Unit := do
  let t0 ← IO.monoMsNow
  let ok := sigmaAtC (nodeE 5) == succE 5
  IO.println s!"sigmaAtC (cell 5) = point of sigma(5): {ok}"
  let t1 ← IO.monoMsNow
  IO.println s!"{t1 - t0} ms"

#eval runSigma
