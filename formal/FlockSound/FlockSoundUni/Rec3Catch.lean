-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The catch follows `Catch.lean`'s `catches_of_tx` (the
-- main line's), with `FlockSound.FlockSq`'s `flock_front_sq`.
import FlockSoundUni.Instance
import FlockSoundUni.Rec3Link
import FlockSound.FlockSq
import UniSound.Rec3.BusSq

/-!
# π1-rec3's Flock bad family catches

π1-rec3's Flock transcript `done` (rounds `flockRounds3 κ`) is read as the main line's (`expandFd κ done`: the first
round's one challenge `c` written out as `squares c (4 + κ)`), whose parse (`parse κ`) is `FlockSound`'s run with
`τs = sqPt (4 + κ) c` (`parse_expandFd_τs`).

**The bad family** (`flockBad3 κ`): round `0`'s one challenge is bad when the residual's sampled tables vanish at its
squares (`kronBad (4 + κ)`, at most `2^(4 + κ) − 1` values: Kronecker); every later challenge is bad as the main
line's (`flockBad κ`) on the expanded transcript. Sizes `dBound3`: `2^(4 + κ) − 1` for `c`, the main line's after.

**`catches3`**: on a completed transcript whose ring claim holds of the column and whose pending claim (the main
line's reading's, which π1-rec3's walk checks) is its sum, the column satisfies Flock's relation or a challenge is
bad: `flock_front_sq` at leanVM's constants on the expanded parse, each event of `Front.BadSq` a hit of `flockBad3`
(`hit_of_badSq`).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-! ## The expanded transcript -/

theorem length_expandFd (κ : ℕ) (d : Done) : (expandFd κ d).length = d.length := by
  cases d <;> rfl

theorem expandFd_take (κ : ℕ) (d : Done) (j : ℕ) (hj : 1 ≤ j) : expandFd κ (d.take j) = (expandFd κ d).take j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  cases d <;> rfl

theorem doneFits_expandFd {d : Done} (h : DoneFits (flockRounds3 κ) d) : DoneFits (flockRounds κ) (expandFd κ d) := by
  rcases d with _ | ⟨⟨msg, c⟩, d⟩
  · exact h.elim
  · obtain ⟨hm, hc, hd⟩ := h
    refine ⟨hm, ?_, ?_⟩
    · show (squares (c.headD 0) (4 + κ)).length = 3 + κ + 1
      rw [length_squares]
      omega
    · exact hd

theorem getD_ofFn_sq (n : ℕ) (c : E) (a : ℕ) (ha : a < n) :
    (List.ofFn (FlockSound.sqPt n c)).getD a 0 = FlockSound.sqPt n c ⟨a, ha⟩ := by
  simp [List.getD_eq_getElem?_getD, ha]

/-- **The expanded parse's sampled coordinates are the squares of the first challenge.** -/
theorem parse_expandFd_τs (d : Done) (hd : d ≠ []) :
    (parse κ (expandFd κ d)).τs = FlockSound.sqPt (4 + κ) ((rd d 0).2.headD 0) := by
  funext a
  show (rd (expandFd κ d) 0).2.getD a 0 = _
  rw [rd_expandFd_zero κ d hd, squares_eq_ofFn, getD_ofFn_sq _ _ _ a.isLt]

/-! ## The bad family -/

/-- **π1-rec3's Flock bad family**: round `0`'s challenge the Kronecker bad set of the residual's sampled tables;
the later ones the main line's on the expanded transcript. -/
noncomputable def flockBad3 (κ : ℕ) : BadFamily κ := fun qf done msg pre ↦
  if done.length = 0 then
    FlockSound.kronBad (4 + κ) (FlockSound.sampledTables (mainSetup κ).hsize (mainSetup κ).fixed
      (FlockSound.Front.zRes (mainSetup κ) (zOf qf)))
  else flockBad κ qf (expandFd κ done) msg pre

/-- **The bad sets' sizes**: `2^(4 + κ) − 1` for the squares' challenge, the main line's after. -/
def dBound3 (κ : ℕ) (j i : ℕ) : ℕ := if j = 0 then 2 ^ (4 + κ) - 1 else dBound κ j i

theorem card_flockBad3 (κ : ℕ) : ∀ qf done msg pre,
    (flockBad3 κ qf done msg pre).card ≤ dBound3 κ done.length pre.length := by
  intro qf done msg pre
  unfold flockBad3 dBound3
  by_cases h : done.length = 0
  · rw [ite_eq_left h, ite_eq_left h]
    exact FlockSound.card_kronBad_le _ _
  · rw [ite_eq_right h, ite_eq_right h, ← length_expandFd κ done]
    exact card_flockBad κ qf _ msg pre

/-- **A later challenge in the expanded parse's bad set is a hit of `flockBad3`.** -/
theorem hitIn3_of_mem (qf : Column (8 + κ)) {done : Done} {j i : ℕ} (h1 : 1 ≤ j) (hj : j < done.length)
    (hi : i < (rd (expandFd κ done) j).2.length)
    (hmem : (rd (expandFd κ done) j).2.getD i 0 ∈ badAt qf (parse κ (expandFd κ done)) j i) :
    HitIn (flockBad3 κ) qf done := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hrd : rd (expandFd κ done) (j' + 1) = rd done (j' + 1) := rd_expandFd_succ κ done j'
  rw [hrd] at hi hmem
  obtain ⟨r, ds, rfl⟩ : ∃ r ds, done = r :: ds :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega))
  have hr := rd_eq_getElem hj
  refine ⟨j' + 1, hj, i, by rw [← hr]; exact hi, ?_⟩
  show _ ∈ flockBad3 κ qf ((r :: ds).take (j' + 1)) ((r :: ds)[j' + 1]).1 (((r :: ds)[j' + 1]).2.take i)
  rw [← hr]
  unfold flockBad3
  rw [ite_eq_right (by simp), expandFd_take κ _ _ (by omega)]
  unfold flockBad
  have hA := agree_pfx (done := expandFd κ (r :: ds)) (j := j' + 1) (by rw [length_expandFd]; exact hj) i
  rw [hrd] at hA
  rw [List.length_take, length_expandFd, min_eq_left hj.le, List.length_take, min_eq_left hi.le,
    badAt_congr qf hA]
  exact hmem

/-- **Each of `Front.BadSq`'s events on the expanded parse is a hit of `flockBad3`.** -/
theorem hit_of_badSq (qf : Column (8 + κ)) {done : Done} (hd : done ≠ []) (h0 : (rd done 0).2.length = 1)
    (hF : Fits κ (expandFd κ done))
    (hbad : FlockSound.Front.BadSq (mainSetup κ) (parse κ (expandFd κ done)) (zOf qf) ((rd done 0).2.headD 0)) :
    HitIn (flockBad3 κ) qf done := by
  have hl : done.length = 23 + κ := by rw [← length_expandFd κ done]; exact hF.len
  rcases hbad with hk | hz | ⟨t, ht⟩ | hα | ⟨t, ht⟩ | ⟨a, ha⟩
  · obtain ⟨r, ds, rfl⟩ := List.exists_cons_of_ne_nil hd
    refine ⟨0, by simp, 0, ?_, ?_⟩
    · show 0 < r.2.length
      have h0' : r.2.length = 1 := h0
      omega
    · show r.2.getD 0 0 ∈ flockBad3 κ qf ((r :: ds).take 0) (r :: ds)[0].1 ((r :: ds)[0].2.take 0)
      unfold flockBad3
      rw [ite_eq_left (by simp), ← headD_eq_getD']
      exact hk
  · refine hitIn3_of_mem qf (j := 1) (i := 0) le_rfl (by omega) (by rw [hF.r1c]; omega) ?_
    rw [badAt_z, ← headD_eq_getD']
    exact hz
  · have ht2 := t.isLt
    refine hitIn3_of_mem qf (j := 2 + t) (i := 0) (by omega) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAt_zc, ← headD_eq_getD', ← rd_drop]
    exact ht
  · refine hitIn3_of_mem qf (j := 13 + κ) (i := 0) (by omega) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAt_α, ← headD_eq_getD']
    exact hα
  · have ht8 := t.isLt
    refine hitIn3_of_mem qf (j := 14 + κ + t) (i := 0) (by omega) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAt_lin, ← headD_eq_getD', ← rd_drop]
    exact ht
  · refine hitIn3_of_mem qf (j := 22 + κ) (i := a) (by omega) (by omega)
      (by rw [hF.r6c]; exact (show (a : ℕ) < 6 from a.isLt)) ?_
    rw [badAt_ring]
    exact ha

end FlockSound.Uni

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-! ## The catch -/

/-- **π1-rec3's bad family catches, given the evaluator transcription**: on a completed transcript of its rounds
whose ring claim holds of the column and whose pending claim (the main line's reading's) is its sum, the column
satisfies Flock's relation or a challenge is in its bad set (`flock_front_sq` at leanVM's constants on the expanded
parse). -/
theorem catches3 (tx : Tx κ) (qf : Column (8 + κ)) (done : Done) (hfit : DoneFits (flockRounds3 κ) done)
    (hend : FlockEndHolds qf (outOf κ (expandFd κ done)))
    (hpend : PendingHolds (outOf κ (expandFd κ done)).2.2) :
    FlockHolds κ qf ∨ HitIn (flockBad3 κ) qf done := by
  have hF := fits_of_doneFits (doneFits_expandFd hfit)
  have hd : done ≠ [] := by
    rintro rfl
    exact hfit
  have h0 : (rd done 0).2.length = 1 := by
    have := ((doneFits_rd hfit).2 0 (by rw [length_flockRounds3]; omega)).2
    simpa [flockRounds3, flockRounds3Pre] using this
  by_cases hold : FlockHolds κ qf
  · exact Or.inl hold
  right
  have hend' := hend
  have hpend' := hpend
  rw [outOf_parse tx hF] at hend' hpend'
  have hring : ∑ u, stagedMap (mainSetup κ).sh (parse κ (expandFd κ done)).f
      (eqP (Front.p (mainSetup κ) (parse κ (expandFd κ done))) u) * colWord qf u =
      Front.target (mainSetup κ) (parse κ (expandFd κ done)) := by
    have h := hend'
    simp only [FlockEndHolds] at h
    rw [tx.ring, tx.target] at h
    exact h
  have hnot : ¬ R1CSHolds (mainSetup κ).A (mainSetup κ).B (zOf qf) (mainSetup κ).cpos :=
    fun h ↦ hold ((r1csHolds_iff rfl _ qf).mp h)
  rcases flock_front_sq (mainSetup κ)
      (leanvmSetup_valid 3 3 κ (4 + κ) rfl (by decide) (by omega) towerShifts (Or.inr rfl) _ _ _)
      (zOf qf) (colBits_bool rfl qf) (colWord qf) (colPack rfl qf) (parse κ (expandFd κ done))
      ((rd done 0).2.headD 0) (parse_expandFd_τs done hd) (zc_consistent tx hF).2 (lin_consistent tx hF).2
      hring hnot with hbad | hfalse
  · exact hit_of_badSq qf hd h0 hF hbad
  · exfalso
    apply hfalse
    have h := hpend'
    unfold PendingHolds at h
    rw [tx.sum, tx.claim] at h
    exact h

/-! ## The rounds' errors -/

theorem flockRounds3_ns_le (κ : ℕ) : ∀ s ∈ flockRounds3 κ, s.ns ≤ 5 := by
  intro s hs
  simp only [flockRounds3, flockRounds3Pre, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hs
  aesop

theorem dBound_le (κ j i : ℕ) : dBound κ j i ≤ 15 := by
  unfold dBound
  split_ifs <;> omega

/-- **Round `j`'s error, times `|E|`**: `2^(4 + κ) − 1` for the squares' challenge, at most `90` after. -/
theorem sum_dBound3_le (κ j : ℕ) :
    ∑ i ∈ range ((((flockRounds3 κ)[j]?).map (·.ns)).getD 0 + 1), dBound3 κ j i ≤ 2 ^ (4 + κ) + 90 := by
  by_cases h0 : j = 0
  · subst h0
    have e : ((((flockRounds3 κ)[0]?).map (·.ns)).getD 0) = 0 := by
      simp [flockRounds3, flockRounds3Pre]
    rw [e]
    simp [dBound3]
    omega
  · have hns : (((flockRounds3 κ)[j]?).map (·.ns)).getD 0 ≤ 5 := by
      cases h : (flockRounds3 κ)[j]? with
      | none => simp
      | some s => exact flockRounds3_ns_le κ s (List.mem_of_getElem? h)
    generalize (((flockRounds3 κ)[j]?).map (·.ns)).getD 0 = n at hns ⊢
    calc ∑ i ∈ range (n + 1), dBound3 κ j i
        ≤ ∑ _i ∈ range (n + 1), 15 :=
          Finset.sum_le_sum fun i _ ↦ by unfold dBound3; rw [ite_eq_right h0]; exact dBound_le κ j i
      _ ≤ 2 ^ (4 + κ) + 90 := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          exact le_trans (by omega : (n + 1) * 15 ≤ 90) (Nat.le_add_left 90 _)

end FlockSound.Uni
