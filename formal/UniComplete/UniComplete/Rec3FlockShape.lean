-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `FlockProverShape.lean` to π1-rec3's
-- honest Flock prover (`Rec3Prover.lean`'s `flockProve3`).
import UniComplete.Rec3FlockDefs
import UniComplete.FlockProverShape

/-!
# π1-rec3's honest Flock prover's run: its output and its shapes

`FlockProverShape.lean`'s facts for `flockProve3` (`Rec3Prover.lean`), whose only change from the main line's
`FlockP.flockProve` is the zerocheck's draw: the `log_n − k − 7` eq coordinates after the seven fixed ones are
`squares c' (log_n − k − 7)` of **one** challenge `c'` (`drawRunW`), not `log_n − k − 7` challenges (`samplesW`).
At a pure Keccak-256 (`Id`), for every writer:

* `drawRunW_length`: the run of squares has `count` terms (as `FlockP.samplesW_length`);
* **`zerocheckW3_eq`**: the zerocheck's output is the skip's start and the rounds' (`FlockP.zerocheckW_eq`'s form: the
  eq coordinates `fixedChallenges ++ sampled` with `|sampled| = log_n − k − 7`, the skip's start at some writer,
  the rounds at some writer), so the main line's generic lemmas (`FlockP.skip_start`, `FlockP.zcRounds_complete`,
  `FlockP.zc_table_value`) apply unchanged;
* **`frontW3_eq`**: the front is `FlockP.frontOf` of the zerocheck's output, `α` and the lincheck's output;
  **`frontW3_slices`**: the front holds the slices it sent;
* **`flockProve3_eq`**: the output is `FlockP.assemble` of the front and the end; `flockProve3_point`,
  `flockProve3_end`;
* **`zerocheckW3_shape`**, **`frontW3_shape`**: at `log_n ≥ 14`, `k ≤ 6`, the main line's `frontW_shape`: `row_low`
  has `6 − k` coordinates, `chi_in` and `chi_in'` `8`, the point `log_n − 6`; the `64` slices sent as they are; the
  skip's point present exactly when `k > 0`.

Decision (the main line's, `FlockProverShape.lean`): the programs are unfolded one bind at a time into existentials
with equations (`…_eq`), never by `simp` through a whole run. The main line's names are written `FlockP.…` (no
`open`: several, e.g. `run_bind_id`, also exist at other types in `UniComplete`).
-/

namespace UniComplete.Rec3

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Protocol.KeccakHash

set_option linter.deprecated false

variable (H : List UInt8 → Id LeanVM.Protocol.Digest)

/-! ## The run of squares -/

/-- `squares c n` has `n` terms. -/
theorem squares_length3 : ∀ (c : E) (n : ℕ), (squares c n).length = n
  | _, 0 => rfl
  | c, n + 1 => by rw [squares, List.length_cons, squares_length3 (c * c) n]

/-- **The run of squares has `count` terms**, for every writer. -/
theorem drawRunW_length (n : ℕ) (w : Wr) : ((drawRunW H n).run w).1.length = n := by
  unfold drawRunW
  by_cases hn : n = 0
  · rw [if_pos hn, hn]
    rfl
  · rw [if_neg hn]
    simp only [FlockP.run_bind_id, FlockP.run_pure_id, squares_length3]

/-! ## The programs, bind by bind -/

/-- **The zerocheck at π1-rec3** is the skip's start and the rounds' output, its eq coordinates after the fixed ones
`log_n − k − 7` of them (the run of squares). -/
theorem zerocheckW3_eq (logN k : ℕ) (wit : FlockP.Wit) (w : Wr) :
    ∃ (sampled : List E) (st : FlockP.ZcStart) (zc : FlockP.ZcOut), sampled.length = logN - k - nFixed ∧
      (∃ w1, st = ((FlockP.skipW H k (fixedChallenges ++ sampled) wit).run w1).1) ∧
      (∃ w2, zc = ((FlockP.zcRounds H (fixedChallenges ++ sampled) st.claim st.a st.b st.c).run w2).1) ∧
      ((zerocheckW3 H logN k wit).run w).1 = (st.zSkip, zc.chi, zc.va, zc.vb, zc.running + zc.va * zc.vb) := by
  refine ⟨_, _, _, drawRunW_length H _ w, ⟨((drawRunW H (logN - k - nFixed)).run w).2, rfl⟩,
    ⟨((FlockP.skipW H k (fixedChallenges ++ ((drawRunW H (logN - k - nFixed)).run w).1) wit).run
      ((drawRunW H (logN - k - nFixed)).run w).2).2, rfl⟩, ?_⟩
  simp only [zerocheckW3, FlockP.run_bind_id, FlockP.run_pure_id]

/-- **The front at π1-rec3** is `frontOf` of the zerocheck's output, `α`, the lincheck's output and the slices. -/
theorem frontW3_eq (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) :
    ∃ (zc : Option E × List E × E × E × E) (alpha : E) (lc : FlockP.LcOut),
      zc = ((zerocheckW3 H logN variant.skip (FlockP.witOf logN q)).run w).1 ∧
      (∃ w2, lc = ((FlockP.lcRounds H lincheckRounds (FlockP.lcClaim zc alpha)
        (FlockP.lcWeightsOf variant.skip zc alpha) (FlockP.lcWitnessOf variant.skip q zc)).run w2).1) ∧
      ((frontW3 H logN variant q).run w).1 =
        FlockP.frontOf variant zc alpha lc (if variant.slices = .claim then none else some lc.z.toList) := by
  refine ⟨_, ((sampleW H).run ((zerocheckW3 H logN variant.skip (FlockP.witOf logN q)).run w).2).1, _, rfl,
    ⟨((sampleW H).run ((zerocheckW3 H logN variant.skip (FlockP.witOf logN q)).run w).2).2, rfl⟩, ?_⟩
  simp only [frontW3, FlockP.run_bind_id, FlockP.run_pure_id, FlockP.sendSlices_fst]

/-- **The front at π1-rec3 holds the slices it sent** (with the slices sent). -/
theorem frontW3_slices (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (hc : variant.slices ≠ .claim) :
    ((frontW3 H logN variant q).run w).1.1.slices = some ((frontW3 H logN variant q).run w).1.2 := by
  obtain ⟨zc, alpha, lc, _, _, hfr⟩ := frontW3_eq H logN variant q w
  rw [hfr]
  show (if variant.slices = .claim then none else some lc.z.toList) = some lc.z.toList
  simp [hc]

/-- **The prover's output at π1-rec3** is `assemble` of its front and its end. -/
theorem flockProve3_eq (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) :
    ∃ (frs : Front × List E) (e : End), frs = ((frontW3 H logN variant q).run w).1 ∧
      ((flockProve3 H logN variant q).run w).1 = FlockP.assemble frs.1 frs.2 e := by
  refine ⟨_, ((FlockP.endW H variant ((frontW3 H logN variant q).run w).1.1.slices).run
    ((frontW3 H logN variant q).run w).2).1, rfl, ?_⟩
  simp only [flockProve3, FlockP.run_bind_id, FlockP.run_pure_id]

/-- The output's point is the front's. -/
theorem flockProve3_point (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) :
    ((flockProve3 H logN variant q).run w).1.point = ((frontW3 H logN variant q).run w).1.1.point := by
  simp only [flockProve3, FlockP.run_bind_id, FlockP.run_pure_id, FlockP.assemble]

/-- The output's end is the end's run after the front. -/
theorem flockProve3_end (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) :
    ((flockProve3 H logN variant q).run w).1.end_ =
      ((FlockP.endW H variant ((frontW3 H logN variant q).run w).1.1.slices).run
        ((frontW3 H logN variant q).run w).2).1 := by
  simp only [flockProve3, FlockP.run_bind_id, FlockP.run_pure_id, FlockP.assemble]

/-! ## The shapes -/

/-- **The zerocheck's shape at π1-rec3**: its point has `log_n − k` coordinates (`log_n ≥ k + 7`), the skip's point
is present exactly when `k > 0`. -/
theorem zerocheckW3_shape (logN k : ℕ) (wit : FlockP.Wit) (w : Wr) (hN : k + nFixed ≤ logN) :
    ((zerocheckW3 H logN k wit).run w).1.2.1.length = logN - k ∧
      (k = 0 → ((zerocheckW3 H logN k wit).run w).1.1 = none) ∧
      (0 < k → ((zerocheckW3 H logN k wit).run w).1.1.isSome) := by
  obtain ⟨sampled, st, zc, hlen, ⟨w1, hst⟩, ⟨w2, hzc⟩, heq⟩ := zerocheckW3_eq H logN k wit w
  rw [heq]
  refine ⟨?_, fun hk ↦ ?_, fun hk ↦ ?_⟩
  · show zc.chi.length = _
    rw [hzc, FlockP.zcRounds_chi_length, List.length_append, FlockP.fixedChallenges_length, hlen]
    omega
  · show st.zSkip = none
    rw [hst, (FlockP.skipW_eq H k _ wit w1).2 hk]
    rfl
  · show st.zSkip.isSome
    obtain ⟨z, hz⟩ := (FlockP.skipW_eq H k _ wit w1).1 hk
    rw [hst, hz]
    rfl

/-- **The front's shape at π1-rec3** (`FlockP.frontW_shape`'s), at `log_n ≥ 14`, `k ≤ 6`. -/
theorem frontW3_shape (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (hk : variant.skip ≤ 6)
    (hN : 14 ≤ logN) :
    ((frontW3 H logN variant q).run w).1.1.rowLow.length = 6 - variant.skip ∧
      ((frontW3 H logN variant q).run w).1.1.chiIn.length = 8 ∧
      ((frontW3 H logN variant q).run w).1.1.chiInPrime.length = 8 ∧
      ((frontW3 H logN variant q).run w).1.2.length = 64 ∧
      (variant.slices ≠ .claim →
        ((frontW3 H logN variant q).run w).1.1.slices = some ((frontW3 H logN variant q).run w).1.2) ∧
      (variant.skip = 0 → ((frontW3 H logN variant q).run w).1.1.zSkip = none) ∧
      (0 < variant.skip → ((frontW3 H logN variant q).run w).1.1.zSkip.isSome) ∧
      ((frontW3 H logN variant q).run w).1.1.point.length = logN - 6 := by
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW3_eq H logN variant q w
  obtain ⟨hchi, hnone, hsome⟩ :=
    zerocheckW3_shape H logN variant.skip (FlockP.witOf logN q) w (by unfold nFixed; omega)
  rw [← hzc] at hchi hnone hsome
  have hlen : lc.challenges.length = 8 := by rw [hlc, FlockP.lcRounds_length]; rfl
  have hsz : lc.z.size = 64 := by
    rw [hlc, FlockP.lcRounds_z]
    refine FlockP.foldl_foldHigh_size _ 6 _ ?_
    rw [FlockP.lcRounds_length, FlockP.lcWitnessOf_size]
    rfl
  have hsl' : variant.slices ≠ .claim →
      (if variant.slices = .claim then none else some lc.z.toList) = some lc.z.toList := fun hc ↦ by
    simp [hc]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := FlockP.frontOf_shape variant zc alpha lc _ logN hk hN hchi hlen hsz hsl'
  rw [hfr]
  exact ⟨h1, h2, h3, h4, h5, fun h ↦ h6.trans (hnone h), fun h ↦ h6 ▸ hsome h, h7⟩

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.frontW3_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.frontW3_shape

/-- info: 'UniComplete.Rec3.flockProve3_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.flockProve3_eq
