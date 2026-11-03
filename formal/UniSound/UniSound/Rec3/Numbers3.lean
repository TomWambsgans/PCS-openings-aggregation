-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The numbers follow `FlockSoundUni/GameNumbers.lean`'s
-- (the main line's).
import UniSound.Rec3.FsFinal3
import UniSound.Rec3.Ref3

/-!
# π1-rec3's chain numbers at the reference deployment

The Fiat–Shamir layer's numbers (`fsLayer3_holds`): **the chain makes `36 + κ + np` queries** (`nQ_rec3`: the label;
`C1` and `c, β, γ`, `3`; Flock's `28 + κ`, the squares' round one query; `C2` and `t`, `1`; the values and `ρ, λ`,
`2`; the batch's `np + 1` rounds), `67` at the reference (`κ = 18`, `np = 13`), at most `2^10`; **every round reads at
most `2^30` scalars** (`hnv_rec3`: Flock's at most `64`, the values at `t` at most `122`, a pair `8`); **the program
IV** of `32` bytes fits `UniIv3` (`uniIv3_of`).
-/

namespace UniSound.Rec3Ref

open UniStatement LeanVM.Parameters FlockSound.Uni UniSound.Ids

theorem nSteps_flockRounds3 (κ : ℕ) : Compose.nSteps (flockRounds3 κ) = 28 + κ := by
  simp only [flockRounds3, flockRounds3Pre, nSteps_append, nSteps_replicate, Compose.nSteps]
  ring

/-- **π1-rec3's chain makes `36 + κ + np` queries.** -/
theorem nQ_rec3 (κ nV np : ℕ) :
    (uniSpec (rec3Rounds (flockRounds3 κ) nV np)).K.nQ = 36 + κ + np := by
  show Compose.nSteps (rec3Rounds (flockRounds3 κ) nV np) + 1 = _
  simp only [rec3Rounds, nSteps_append, nSteps_replicate, nSteps_flockRounds3, Compose.nSteps]
  ring

/-- **`hnQ`** for `κ + np ≤ 988`. -/
theorem hnQ_rec3 (κ nV np : ℕ) (h : κ + np ≤ 988) :
    (uniSpec (rec3Rounds (flockRounds3 κ) nV np)).K.nQ ≤ 2 ^ 10 := by
  rw [nQ_rec3]
  omega

/-- **`hnv`**: every round of π1-rec3 reads at most `2^30` scalars. -/
theorem hnv_rec3 (κ nV np : ℕ) (hnV : nV ≤ 2 ^ 30) :
    ∀ r ∈ rec3Rounds (flockRounds3 κ) nV np, r.nv ≤ 2 ^ 30 := by
  intro r hr
  simp only [rec3Rounds, flockRounds3, flockRounds3Pre, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hr
  rcases hr with (((h | ((((h | h) | ⟨_, h⟩) | h) | ⟨_, h⟩) | h) | (h | h)) | ⟨_, h⟩) | h <;> subst h <;>
    dsimp only <;> omega

/-- **`UniIv3` for the reference program IV** (`32` bytes). -/
theorem uniIv3_of (D : Deployment) (h : D.programIv = programIv) : UniIv3 D :=
  ⟨by rw [h, programIv_length]; decide, by rw [h, programIv_length]; decide⟩

end UniSound.Rec3Ref

/-- info: 'UniSound.Rec3Ref.hnv_rec3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Rec3Ref.hnv_rec3
