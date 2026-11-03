-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The predicate is `formal/UniSound`'s
-- `Ids.FlockGood` (`Ids/Model.lean`); the instance is `Instance.lean`'s `flockSoundInstance`.
import FlockSoundUni.PendingShape
import UniSound.Ids.Build

/-!
# Flock's result is the main line's: `FlockGood` for `flockSoundInstance`

The identity model of `formal/UniSound/UniSound/Ids` is degenerate unless Flock's result is the main
line's (`Ids.FlockGood κ V`): a ring end, a point of `q_flock`'s `8 + κ` coordinates, its pending
reduction's rounds within the batch's `V`. For `flockSoundInstance κ` (`flockProg κ`, its result
`flockOut`) on a completed transcript: the end is always `.ring`; the point is the lincheck's `8`
coordinates (reversed) and the zerocheck's after its `3 + 8` first (`11 + κ` rounds, `7` fixed and
`4 + κ` sampled challenges: `decodeSC`'s point has one coordinate per round); the pending reduction has
at most `15` rounds (`flockPendingShaped`), and the batch has at least `15` variables.
**`flockGood`**.
-/

namespace FlockSound.Uni

open UniSound UniStatement LeanVM.Parameters

/-- **`decodeSC`'s point** has one coordinate per round it decodes. -/
theorem decodeSC_length : ∀ (c : E) (es : List (Option E)) (d : Done),
    (decodeSC c es d).1.length = min es.length d.length
  | _, [], _ => by simp [decodeSC]
  | c, e :: es, r :: d => by
    simp only [decodeSC, List.length_cons, decodeSC_length _ es d]
    omega
  | _, _ :: _, [] => by simp [decodeSC]

/-- The batch has at least `15` variables (`C1`'s stack has; `batchVars` is `varsOf`). -/
theorem batchVars_ge (S : Shape) : 15 ≤ Ids.batchVars S := varsOf_ge S

/-- **Flock's result is the main line's** (`Ids.FlockGood`) on every completed transcript of
`flockSoundInstance κ`, for a batch of at least `15` variables. -/
theorem flockGood (κ V : ℕ) (hV : 15 ≤ V) (fd : Done)
    (hfd : DoneFits (flockSoundInstance κ).prog.rounds fd) :
    Ids.FlockGood κ V ((flockSoundInstance κ).prog.out fd []) := by
  have hR := (flockPendingShaped κ fd hfd).2.2
  rw [flockSoundInstance_prog] at hfd hR ⊢
  change DoneFits (flockRounds κ) fd at hfd
  have hl : fd.length = 23 + κ := by
    rw [UniSound.doneFits_length _ _ hfd]
    simp [flockRounds]
    omega
  obtain ⟨x, d, rfl⟩ : ∃ x d, fd = x :: d := by
    rcases fd with _ | ⟨x, d⟩
    · exact absurd hl (by simp only [List.length_nil]; omega)
    · exact ⟨x, d, rfl⟩
  have hx : x.2.length = 3 + κ + 1 := hfd.2.1
  refine ⟨⟨_, _, rfl⟩, ?_, hR.trans hV⟩
  show (outOf κ (x :: d)).1.length = 8 + κ
  simp only [List.length_cons] at hl
  unfold outOf flockOut
  simp only [List.length_append, List.length_reverse, List.length_drop, decodeSC_length,
    List.length_map, List.length_replicate, List.length_take, length_fixedChallenges, rd,
    List.getD_cons_zero, hx, List.length_cons]
  omega

end FlockSound.Uni

/-- info: 'FlockSound.Uni.flockGood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockGood
