-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniStatement.Opening

/-!
# The reference shape's constants

The reference deployment (`UniStatement.reference`: 1,000 signatures, memory `2^21`, bytecode `2^19`, heights
18 18 18 18 17 18) as numbers the end theorem needs, each by kernel evaluation of the shape's small objects (lists of
a few hundred natural numbers; no stack is evaluated):

* `reference_valid`: the shape is valid (`Shape.Valid`: six heights, `validate` with Flock);
* `reference_vars`: the three stacks have `27`, `27`, `24` variables (`layoutsOf`), so `C1`, `C2` and the setup are
  opened at `2^27`, `2^27`, `2^24` words, and the five `PCS_OPEN` layout words name `27, 27, 24, 28, 28`
  (`reference_wordVars`): every opening is within WHIR's `2^24 … 2^28` (`Whir.lean`'s `pcsOpen_honest`).
-/

namespace UniComplete

open UniStatement

theorem reference_heights : reference.heights = [18, 18, 18, 18, 17, 18] := by decide +kernel

theorem reference_valid : reference.Valid := by decide +kernel

end UniComplete

/-- info: 'UniComplete.reference_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms UniComplete.reference_valid
