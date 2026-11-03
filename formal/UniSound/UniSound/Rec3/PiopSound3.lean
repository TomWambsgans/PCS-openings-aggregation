-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proof follows `PiopSound.lean` (the main line's).
import UniSound.PiopSound
import UniSound.Rec3.Piop3

/-!
# π1-rec3's PIOP is round-by-round sound

**`uniPiop3 F3 I BR`**: the states `uniPre3`, `uniPost3` and the errors `uniErr3` form a `RbrPiop` on π1-rec3's
rounds (`rec3Rounds`), for π1-rec3's Flock phase `F3`, any identity model `I` and any batch `BR`: round `0` by
`mainSound` (three challenges); Flock's rounds by Flock's `step`; `t` by Schwartz–Zippel for every identity and the
merge polynomial; `ρ, λ` by the two combinations, the batch's start (`batch_start`) under the pending claim the
states carry from `C2`'s round on; the batch's rounds by `BR.step`. `pre_post` from `main_of_polys` and Flock's
`finish` at `C2`'s round, the pending claim there one of `uniPre3`'s.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

variable {D : Deployment} {κ : ℕ} (F3 : FlockSound3 κ) {np : ℕ} (I : UniIds3 D F3 np) (BR : PairBatch np)

theorem uniPre3_pre_post (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E)
    (m' : Option Stk × List E) (h : uniPre3 F3 I BR s (p ++ [(m, c)]) m') : uniPost3 F3 I BR s p m c := by
  unfold uniPre3 at h
  unfold uniPost3
  have hl : (p ++ [(m, c)]).length ≠ 0 := by simp
  rw [ite_eq_right hl] at h
  by_cases hq : (p ++ [(m, c)]).length = F3.prog.rounds.length + 1
  · rw [ite_eq_left hq] at h
    obtain ⟨c1, c2, h1, -, hP, hEnd, hPend, hDone⟩ := h
    refine ⟨c1, h1, ?_⟩
    rw [ite_eq_left (le_of_eq hq), hq, Nat.add_sub_cancel, List.take_length]
    exact ⟨I.main_of_polys _ _ _ _ _ hP, hDone, F3.finish _ _ hDone hEnd hPend⟩
  · rw [ite_eq_right hq] at h
    exact h

theorem uniPre3_ne (s : USt) (p : Op Stk) (m : Option Stk × List E) (h0 : p.length ≠ 0)
    (h1 : p.length ≠ F3.prog.rounds.length + 1) : uniPre3 F3 I BR s p m = uniS3 F3 I BR s p := by
  unfold uniPre3
  rw [ite_eq_right h0, ite_eq_right h1]

/-- **Round `0`**: the bus at `α = (c, c², c⁴, c⁸)` and the constraints (`mainSound`, three challenges). -/
theorem uniSound3_zero (s : USt) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 3}[¬ uniPre3 F3 I BR s [] m ∧ uniPost3 F3 I BR s [] m c] ≤ I.errMain := by
  have hpre : uniPre3 F3 I BR s [] m = ∃ c, m.1 = some c ∧ Rel D s c := by
    unfold uniPre3
    rw [ite_eq_left (List.length_nil : ([] : Op Stk).length = 0)]
  rcases hm : m.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, h1, -⟩ := hpost
    simp [rd, hm] at h1
  · refine (prEvent_mono _ _ _ fun c ⟨hn, hpost⟩ => ?_).trans (I.mainSound s c1)
    obtain ⟨c1', h1, hpost⟩ := hpost
    have hx : rd ([] ++ [(m, c)] : Op Stk) 0 = (m, c) := rfl
    rw [hx, hm] at h1
    cases h1
    rw [ite_eq_left (by simp)] at hpost
    obtain ⟨hOK, -, hS⟩ := hpost
    rw [hx] at hOK
    rw [show fdOf F3.prog.rounds.length ([] ++ [(m, c)] : Op Stk) = [] by simp [fdOf]] at hS
    rw [hpre] at hn
    exact ⟨fun hmain => hn ⟨c1, hm, I.rel_of s c1 hmain (F3.S_nil _ hS)⟩, hOK⟩

/-- **Flock's round `j − 1`**: Flock's `step`. -/
theorem uniSound3_flock (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ F3.prog.rounds.length) (s : USt) (p : Op Stk)
    (hp : p.length = j) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E ((F3.prog.rounds[j - 1]'(by omega)).ns + 1)}[
      ¬ uniPre3 F3 I BR s p m ∧ uniPost3 F3 I BR s p m c] ≤ F3.err (j - 1) := by
  rw [uniPre3_ne F3 I BR s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  have hfd : ∀ c : List E, fdOf F3.prog.rounds.length (p ++ [(m, c)]) =
      fdOf F3.prog.rounds.length p ++ [((none, m.2), c)] := fun c =>
    fdOf_append_le _ p _ (by omega) (by omega)
  by_cases hfit : DoneFits (F3.prog.rounds.take (j - 1)) (fdOf F3.prog.rounds.length p) ∧
      UMsg.Fits (F3.prog.rounds[j - 1]'(by omega)) (none, m.2)
  · have hb := F3.step (j - 1) (by omega) (I.qf c1) _ (none, m.2) hfit.1 hfit.2
    refine (prEvent_mono _ _ _ ?_).trans hb
    rintro c ⟨hn, hpost⟩
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_left (by simp; omega)] at hpost
    obtain ⟨hOK, -, hS⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt] at hOK
    rw [hfd] at hS
    refine ⟨fun hS0 => hn ⟨c1, h0, ?_⟩, hS⟩
    rw [ite_eq_left (by omega), hp]
    exact ⟨hOK, hfit.1, hS0⟩
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => hfit ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_left (by simp; omega)] at hpost
    obtain ⟨-, hfits, -⟩ := hpost
    rw [hfd, List.length_append, List.length_singleton, hp, Nat.add_sub_cancel,
      show j = (j - 1) + 1 by omega] at hfits
    exact doneFits_take_succ _ (j - 1) (by omega) _ _ hfits

/-- **`C2`'s round, the point `t`**: Schwartz–Zippel for every identity and the merge polynomial. -/
theorem uniSound3_c2 (s : USt) (p : Op Stk) (hp : p.length = F3.prog.rounds.length + 1)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 1}[¬ uniPre3 F3 I BR s p m ∧ uniPost3 F3 I BR s p m c] ≤
      ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have hpre : uniPre3 F3 I BR s p m = ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2, P = 0) ∧
      FlockEndHolds (I.qf c1) (F3.outM (fdOf F3.prog.rounds.length p)) ∧
      PendingHolds (F3.outM (fdOf F3.prog.rounds.length p)).2.2 ∧
      FlockDone3 F3 (fdOf F3.prog.rounds.length p) := by
    unfold uniPre3
    rw [ite_eq_right (by omega), ite_eq_left hp]
  rw [hpre]
  have hlt : 0 < p.length := by omega
  have hx : ∀ c : List E, rd (p ++ [(m, c)]) (F3.prog.rounds.length + 1) = (m, c) := fun c => by
    rw [← hp, rd_append_self]
  have hfd : ∀ c : List E, fdOf F3.prog.rounds.length (p ++ [(m, c)]) =
      fdOf F3.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  rcases hm : m.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -⟩ := hpost
    rw [hx, hm] at hc2
    cases hc2
  have hb : Pr{let c ← Compose.draws E 1}[∃ P ∈ I.polys s c1 (rd p 0).2
      (fdOf F3.prog.rounds.length p) c2 ++ [I.zb (fdOf F3.prog.rounds.length p)], P ≠ 0 ∧
        P.eval (c.headD 0) = 0] ≤
      ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
    refine (prEvent_root_le (I.polys s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2 ++
      [I.zb (fdOf F3.prog.rounds.length p)])).trans
        (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _)
    rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    exact Nat.add_le_add (I.deg_le s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2) (I.zb_deg _)
  refine (prEvent_mono _ _ _ ?_).trans hb
  rintro c ⟨hn, hpost⟩
  obtain ⟨c1', hc1, hpost⟩ := hpost
  rw [rd_append_lt _ _ 0 hlt, h0] at hc1
  cases hc1
  rw [ite_eq_right (by simp; omega)] at hpost
  obtain ⟨c2', hc2, hDone, hPend, hrest⟩ := hpost
  rw [hx, hm] at hc2
  cases hc2
  rw [ite_eq_left (by simp; omega)] at hrest
  rcases hrest with hzb | hrest
  · rw [hfd, hx] at hzb
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), I.zb_ne _, hzb⟩
  obtain ⟨vals, hz⟩ := hrest
  rw [rd_append_lt _ _ 0 hlt, hfd, hx] at hz
  rw [hfd] at hDone hPend
  have hev := I.diffs_eval _ _ _ _ _ _ _ hz
  have hEnd := I.diffs_flock _ _ _ _ _ _ _ hz
  by_contra hno
  refine hn ⟨c1, c2, rfl, rfl, fun P hP => ?_, hEnd, hPend, hDone⟩
  by_contra hP0
  exact hno ⟨P, List.mem_append_left _ hP, hP0, hev P hP⟩

/-- **The values' round, `ρ` and `λ`**: the two combinations, the batch's start under the pending claim. -/
theorem uniSound3_vals (s : USt) (p : Op Stk) (hp : p.length = F3.prog.rounds.length + 2)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 2}[¬ uniPre3 F3 I BR s p m ∧ uniPost3 F3 I BR s p m c] ≤
      ((I.nRel - 1 + (4 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  rw [uniPre3_ne F3 I BR s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  have hlt1 : F3.prog.rounds.length + 1 < p.length := by omega
  have hx : ∀ c : List E, rd (p ++ [(m, c)]) (F3.prog.rounds.length + 2) = (m, c) := fun c => by
    rw [← hp, rd_append_self]
  have hfd : ∀ c : List E, fdOf F3.prog.rounds.length (p ++ [(m, c)]) =
      fdOf F3.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
  have hbr : ∀ c : List E, brOf F3.prog.rounds.length (p ++ [(m, c)]) = [] := fun c =>
    brOf_of_length _ _ (by simp; omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  rcases h2 : (rd p (F3.prog.rounds.length + 1)).1.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
  by_cases hzb : (I.zb (fdOf F3.prog.rounds.length p)).eval
      ((rd p (F3.prog.rounds.length + 1)).2.headD 0) = 0
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨hn, hpost⟩ => hn ?_
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, hDone, hPend, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
    refine ⟨c1, h0, ?_⟩
    rw [ite_eq_right (by omega)]
    exact ⟨c2, h2, by rwa [hfd] at hDone, by rwa [hfd] at hPend, Or.inl hzb⟩
  by_cases hbad : ∃ d ∈ I.diffs s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2
      ((rd p (F3.prog.rounds.length + 1)).2.headD 0) m.2, ∃ x ∈ d, x ≠ 0
  · have hb := prEvent_twoLevel_le (I.diffs s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2
      ((rd p (F3.prog.rounds.length + 1)).2.headD 0) m.2) I.nRel 4
      (I.diffs_len s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2
        ((rd p (F3.prog.rounds.length + 1)).2.headD 0) m.2)
      (I.diffs_count s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2
        ((rd p (F3.prog.rounds.length + 1)).2.headD 0) m.2) hbad
    refine (prEvent_mono _ _ _ ?_).trans hb
    rintro c ⟨-, hpost⟩
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -, hPend, hrest⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
    rw [ite_eq_right (by simp; omega)] at hrest
    rcases hrest with hz | hrest
    · rw [rd_append_lt _ _ _ hlt1, hfd] at hz
      exact absurd hz hzb
    rw [hbr, rd_append_lt _ _ 0 hlt, rd_append_lt _ _ _ hlt1, hfd, hx, BR.St_nil] at hrest
    rw [hfd] at hPend
    rw [← I.batch_start _ _ _ _ _ _ _ _ _ hPend, ← hrest]
    exact CharTwo.add_self_eq_zero _
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨hn, hpost⟩ => hn ?_
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, hDone, hPend, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
    refine ⟨c1, h0, ?_⟩
    rw [ite_eq_right (by omega)]
    refine ⟨c2, h2, by rwa [hfd] at hDone, by rwa [hfd] at hPend, Or.inr ?_⟩
    rw [ite_eq_left hp]
    refine ⟨m.2, fun d hd x hx => ?_⟩
    by_contra hx0
    exact hbad ⟨d, hd, x, hx, hx0⟩

/-- **A round of the batching sumcheck**: a pair's `errPair`, the last plain round's `errLast`. -/
theorem uniSound3_batch (j : ℕ) (h1 : F3.prog.rounds.length + 3 ≤ j)
    (h2 : j ≤ F3.prog.rounds.length + 3 + np) (s : USt) (p : Op Stk) (hp : p.length = j)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 1}[¬ uniPre3 F3 I BR s p m ∧ uniPost3 F3 I BR s p m c] ≤
      if j < F3.prog.rounds.length + 3 + np then BR.errPair else BR.errLast := by
  rw [uniPre3_ne F3 I BR s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  have hlt1 : F3.prog.rounds.length + 1 < p.length := by omega
  have hlt2 : F3.prog.rounds.length + 2 < p.length := by omega
  have hfd : ∀ c : List E, fdOf F3.prog.rounds.length (p ++ [(m, c)]) =
      fdOf F3.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
  have hbr : ∀ c : List E, brOf F3.prog.rounds.length (p ++ [(m, c)]) =
      brOf F3.prog.rounds.length p ++ [(m.2, c)] := fun c => brOf_append _ _ _ (by omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  rcases hc2' : (rd p (F3.prog.rounds.length + 1)).1.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, hc2'] at hc2
    cases hc2
  by_cases hzb : (I.zb (fdOf F3.prog.rounds.length p)).eval
      ((rd p (F3.prog.rounds.length + 1)).2.headD 0) = 0
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨hn, hpost⟩ => hn ?_
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, hDone, hPend, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, hc2'] at hc2
    cases hc2
    refine ⟨c1, h0, ?_⟩
    rw [ite_eq_right (by omega)]
    exact ⟨c2, hc2', by rwa [hfd] at hDone, by rwa [hfd] at hPend, Or.inl hzb⟩
  set P := I.prod s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2
    ((rd p (F3.prog.rounds.length + 1)).2.headD 0) (rd p (F3.prog.rounds.length + 2)).1.2
    ((rd p (F3.prog.rounds.length + 2)).2.headD 0)
    ((rd p (F3.prog.rounds.length + 2)).2.getD 1 0) with hP
  set tg := I.target s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2
    ((rd p (F3.prog.rounds.length + 1)).2.headD 0) (rd p (F3.prog.rounds.length + 2)).1.2
    ((rd p (F3.prog.rounds.length + 2)).2.headD 0)
    ((rd p (F3.prog.rounds.length + 2)).2.getD 1 0) with htg
  have hlen : (brOf F3.prog.rounds.length p).length = j - (F3.prog.rounds.length + 3) := by
    rw [length_brOf, hp]
  have hb := BR.step P tg (brOf F3.prog.rounds.length p) m.2 (I.prod_vars _ _ _ _ _ _ _ _ _)
    (by rw [hlen]; omega)
  have hif : (if (brOf F3.prog.rounds.length p).length < np then BR.errPair else BR.errLast) =
      if j < F3.prog.rounds.length + 3 + np then BR.errPair else BR.errLast := by
    rw [hlen]
    by_cases hj : j < F3.prog.rounds.length + 3 + np
    · rw [ite_eq_left hj, ite_eq_left (by omega)]
    · rw [ite_eq_right hj, ite_eq_right (by omega)]
  rw [hif] at hb
  refine (prEvent_mono _ _ _ ?_).trans hb
  rintro c ⟨hn, hpost⟩
  obtain ⟨c1', hc1, hpost⟩ := hpost
  rw [rd_append_lt _ _ 0 hlt, h0] at hc1
  cases hc1
  rw [ite_eq_right (by simp; omega)] at hpost
  obtain ⟨c2', hc2, hDone, hPend, hrest⟩ := hpost
  rw [rd_append_lt _ _ _ hlt1, hc2'] at hc2
  cases hc2
  rw [ite_eq_right (by simp; omega)] at hrest
  rcases hrest with hz | hrest
  · rw [rd_append_lt _ _ _ hlt1, hfd] at hz
    exact absurd hz hzb
  rw [hbr, rd_append_lt _ _ 0 hlt, rd_append_lt _ _ _ hlt1, rd_append_lt _ _ _ hlt2, hfd] at hrest
  refine ⟨fun hS => hn ⟨c1, h0, ?_⟩, hrest⟩
  rw [ite_eq_right (by omega)]
  refine ⟨c2, hc2', by rwa [hfd] at hDone, by rwa [hfd] at hPend, Or.inr ?_⟩
  rw [ite_eq_right (by omega)]
  exact hS

/-! ## The protocol -/

/-- **π1-rec3's PIOP, round by round**, for its Flock phase `F3`, the identity model `I` and the batch `BR`. -/
noncomputable def uniPiop3 : RbrPiop (rec3Rounds F3.prog.rounds I.nV np) USt Stk where
  pre := uniPre3 F3 I BR
  post := uniPost3 F3 I BR
  pre_post := uniPre3_pre_post F3 I BR
  err := uniErr3 F3 I BR
  sound j s p m hj hp := by
    rw [length_rec3Rounds] at hj
    unfold uniErr3
    by_cases h0 : j = 0
    · subst h0
      rw [ite_eq_left rfl, rec3Rounds_zero]
      obtain rfl : p = [] := List.length_eq_zero_iff.mp hp
      exact uniSound3_zero F3 I BR s m
    rw [ite_eq_right h0]
    by_cases h1 : j ≤ F3.prog.rounds.length
    · rw [ite_eq_left h1, rec3Rounds_flock _ _ _ j (by omega) h1,
        List.getD_eq_getElem _ _ (by omega)]
      exact uniSound3_flock F3 I BR j (by omega) h1 s p hp m
    rw [ite_eq_right h1]
    by_cases h2 : j = F3.prog.rounds.length + 1
    · subst h2
      rw [ite_eq_left rfl, rec3Rounds_c2]
      exact uniSound3_c2 F3 I BR s p hp m
    rw [ite_eq_right h2]
    by_cases h3 : j = F3.prog.rounds.length + 2
    · subst h3
      rw [ite_eq_left rfl, rec3Rounds_vals]
      exact uniSound3_vals F3 I BR s p hp m
    rw [ite_eq_right h3]
    have hb := uniSound3_batch F3 I BR j (by omega) (by omega) s p hp m
    by_cases h4 : j < F3.prog.rounds.length + 3 + np
    · rw [ite_eq_left h4] at hb ⊢
      rw [rec3Rounds_pair _ _ _ j (by omega) h4]
      exact hb
    · rw [ite_eq_right h4] at hb ⊢
      rw [show j = F3.prog.rounds.length + 3 + np by omega, rec3Rounds_last]
      exact hb

/-- **The first state is leanVM 42422001's relation.** -/
theorem hpre_uniPiop3 (s : USt) (c : Stk) (m : List E) (h : (uniPiop3 F3 I BR).pre s [] (some c, m)) :
    Rel D s c := by
  change uniPre3 F3 I BR s [] (some c, m) at h
  unfold uniPre3 at h
  rw [ite_eq_left (List.length_nil : ([] : Op Stk).length = 0)] at h
  obtain ⟨c', hc', hr⟩ := h
  cases hc'
  exact hr

end UniSound

/-- info: 'UniSound.uniPiop3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniPiop3
