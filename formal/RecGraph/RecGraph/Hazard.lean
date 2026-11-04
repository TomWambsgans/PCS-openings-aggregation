-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Z_bad`, its degree and its nonvanishing are
-- `formal/UniSound`'s (`UniSound.Ids.zBad`, `natDegree_zBad_le`, `zBad_ne_zero`; the main line's merge hazard).
import RecGraph.Semantics
import UniSound.Ids.Main
import UniSound.Ids.Build
import UniSound.Ids.Deployed
import UniSound.Ids.Eval

/-!
# The merge hazard, and its probability

`combine` merges a relation's points that are equal and a point into a longer one it is a prefix of; the verifier on
`E` (`UniStatement`) compares values, the recorded graph symbols. The one merge that changes a weight is of `y(t)`,
the BLAKE2S table's `q_flock` slot point (its terms read as many coordinates as their point has): into a `C1` point
`w.take k` (first coordinate `w_0 = t`) or into Flock's point (first coordinate `p_0`). **The hazard** is that
`y(t)`'s first coordinate is one of these: `Z_bad(t) = 0`, `Z_bad = (y_0 + X)(y_0 + p_0)`, the main line's
(`UniSound.Ids.zBad`, `NoMerge`). Off it, no `C1` point extends `y(t)` (`UniSound.Ids.Eval.y_self`).

* `MergeHazard`: the hazard at a run of π1-rec3's verifier that draws `t` (its challenge 49; `p_0` its challenge 42,
  the lincheck's last round: the first coordinate of Flock's point, the lincheck's rounds reversed). A run that stops
  before drawing `t` (a short stream, a malformed one) is not on the hazard: `Hazard p_0 0` holds for every `p_0`
  (`y_0` is linearised, so `Z_bad(0) = 0`), and reading an undrawn challenge as `0` would put every such run on it
  (`formal/RecCompose/Review/STATEMENT_REVIEW.md`, finding 2).
* `hazard_card`: **for every `p_0`, at most `2^19` values of `t` are hazardous** (`Z_bad` is a nonzero polynomial of
  degree at most `2^19`: Schwartz–Zippel in `t`).
* `hazard_prob`: so, `t` uniform and `p_0` fixed (Flock's point is drawn before `C2`'s root, `t` after it): the hazard
  has probability at most `2^19 / |E| = 2^-173`. This is the form the composition's union bound takes: per candidate
  `C1`, `C2` tables, the challenges before `t` fixed.
-/

namespace RecGraph

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement Polynomial
open scoped ENNReal

/-- **The hazard polynomial at π1-rec3's shape**: `Z_bad = (y_0 + X)(y_0 + p_0)` (`UniSound.Ids.zBad`). -/
noncomputable def hazardPoly (p0 : E) : Polynomial E := UniSound.Ids.zBad reference p0

/-- `t` is hazardous for `p_0`: `y(t)`'s first coordinate is `t` (so `y(t)` starts like `w`) or `p_0` (like Flock's
point). -/
def Hazard (p0 t : E) : Prop := (hazardPoly p0).eval t = 0

noncomputable instance (p0 : E) : DecidablePred (Hazard p0) := fun t ↦ inferInstanceAs (Decidable ((hazardPoly p0).eval t = 0))

/-- **The hazard at a run of π1-rec3's verifier** over `π`: the run draws `t` (challenge 49: at least 50 challenges),
and `t` is hazardous for Flock's point's first coordinate (challenge 42). -/
def MergeHazard (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) : Prop :=
  let ch := (Id.run (runWithFs (m := Id) (fun s ↦ pure (π s)) reference iv publicInput stream (.flock flockMain) .point
    .rec3 true)).chan.challenges
  50 ≤ ch.size ∧ Hazard (ch.getD 42 0) (ch.getD 49 0)

/-- **The hazard needs `t` drawn**: a run on the hazard has drawn at least 50 challenges. -/
theorem MergeHazard.drawn {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}
    (h : MergeHazard π iv publicInput stream) :
    50 ≤ (Id.run (runWithFs (m := Id) (fun s ↦ pure (π s)) reference iv publicInput stream (.flock flockMain) .point
      .rec3 true)).chan.challenges.size := h.1

theorem reference_blake2s_height : reference.heights.getD opBlake2s 0 = 18 := by
  rw [UniSound.Ids.reference_eq]; decide

/-- `Z_bad` at π1-rec3's shape is nonzero. -/
theorem hazardPoly_ne_zero (p0 : E) : hazardPoly p0 ≠ 0 :=
  UniSound.Ids.zBad_ne_zero reference UniSound.Ids.betaCantor
    (by rw [reference_blake2s_height]; exact UniSound.Ids.functionalsCorrect18)
    (by rw [reference_blake2s_height]; decide) p0

/-- `Z_bad`'s degree at π1-rec3's shape: at most `2^19`. -/
theorem hazardPoly_natDegree (p0 : E) : (hazardPoly p0).natDegree ≤ 2 ^ 19 := by
  have h := UniSound.Ids.natDegree_zBad_le reference p0
  unfold UniSound.Ids.zBadDeg at h
  rw [UniSound.Ids.Eval.coordinateFunctionals_size, reference_blake2s_height] at h
  exact h

/-- **Schwartz–Zippel in `t`**: for every `p_0`, at most `2^19` values of `t` are hazardous. -/
theorem hazard_card (p0 : E) : (Finset.univ.filter fun t : E ↦ Hazard p0 t).card ≤ 2 ^ 19 := by
  have hne := hazardPoly_ne_zero p0
  have hsub : (Finset.univ.filter fun t : E ↦ Hazard p0 t) ⊆ (hazardPoly p0).roots.toFinset := by
    intro t ht
    have ht' : (hazardPoly p0).eval t = 0 := (Finset.mem_filter.mp ht).2
    simp only [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    exact ht'
  calc (Finset.univ.filter fun t : E ↦ Hazard p0 t).card
      ≤ (hazardPoly p0).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (hazardPoly p0).roots := Multiset.toFinset_card_le _
    _ ≤ (hazardPoly p0).natDegree := card_roots' _
    _ ≤ 2 ^ 19 := hazardPoly_natDegree p0

/-- **The hazard's probability**: `t` uniform in `E`, `p_0` fixed (drawn before `t`), at most `2^19 / |E|`
(`|E| = 2^192`: `2^-173`). -/
theorem hazard_prob (p0 : E) :
    ((Finset.univ.filter fun t : E ↦ Hazard p0 t).card : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤
      (2 ^ 19 : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  gcongr
  exact_mod_cast hazard_card p0

end RecGraph
