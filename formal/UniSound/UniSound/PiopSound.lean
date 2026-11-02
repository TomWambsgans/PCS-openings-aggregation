-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Piop

/-!
# The univariate PIOP is round-by-round sound

**`uniPiop Fl I`**: the states `uniPre`, `uniPost` and the errors `uniErr` of `Piop.lean` form a
`RbrPiop` on the main line's rounds (`uniRounds`), for the Flock phase `Fl` and any identity model
`I`: each round's soundness from its lemma (`mainSound`; Flock's `step`; Schwartz–Zippel,
`prEvent_root_le`; the two combinations, `prEvent_twoLevel_le`; the sumcheck's rounds,
`SumOracle.step_sound`), and `pre_post` from `main_of_polys` and Flock's `finish` at the boundary
of `C2`'s round.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

variable {D : Deployment} {κ : ℕ} (Fl : FlockSound κ) (I : UniIds D Fl)

theorem prEvent_le_of_forall_not {α : Type} (mx : ProbComp α) (P : α → Prop) (ε : ℝ≥0∞)
    (h : ∀ x, ¬ P x) : Pr{let x ← mx}[P x] ≤ ε :=
  (le_of_eq (prEvent_eq_zero_of_forall_not mx P h)).trans zero_le

theorem DoneFits.length_eq : ∀ {rs : List Compose.RoundSpec} {d : Done}, DoneFits rs d →
    d.length = rs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [h.2.2.length_eq]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem doneFits_append_single : ∀ (rs : List Compose.RoundSpec) (d : Done) (s : Compose.RoundSpec)
    (x : UMsg × List E), d.length = rs.length →
      (DoneFits (rs ++ [s]) (d ++ [x]) ↔ DoneFits rs d ∧ x.1.Fits s ∧ x.2.length = s.ns + 1)
  | [], [], s, x, _ => by simp [DoneFits]
  | r :: rs, y :: d, s, x, h => by
    simp only [List.cons_append, DoneFits]
    rw [doneFits_append_single rs d s x (by simpa using h)]
    tauto
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem doneFits_take_succ (rs : List Compose.RoundSpec) (j : ℕ) (h : j < rs.length)
    (done : Done) (x : UMsg × List E) (hd : DoneFits (rs.take (j + 1)) (done ++ [x])) :
    DoneFits (rs.take j) done ∧ x.1.Fits (rs[j]'h) := by
  have ht : rs.take (j + 1) = rs.take j ++ [rs[j]'h] := List.take_succ_eq_append_getElem h
  rw [ht] at hd
  have hl := hd.length_eq
  simp only [List.length_append, List.length_singleton, List.length_take] at hl
  have hl' : done.length = (rs.take j).length := by simp; omega
  obtain ⟨h1, h2, -⟩ := (doneFits_append_single _ done _ x hl').mp hd
  exact ⟨h1, h2⟩

theorem uniPre_pre_post (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E)
    (m' : Option Stk × List E) (h : uniPre Fl I s (p ++ [(m, c)]) m') : uniPost Fl I s p m c := by
  unfold uniPre at h
  unfold uniPost
  have hl : (p ++ [(m, c)]).length ≠ 0 := by simp
  rw [ite_eq_right hl] at h
  by_cases hq : (p ++ [(m, c)]).length = Fl.prog.rounds.length + 1
  · rw [ite_eq_left hq] at h
    obtain ⟨c1, c2, h1, -, hP, hEnd, hPend, hDone⟩ := h
    refine ⟨c1, h1, ?_⟩
    rw [ite_eq_left (le_of_eq hq), hq, Nat.add_sub_cancel, List.take_length]
    exact ⟨I.main_of_polys _ _ _ _ _ hP, hDone, Fl.finish _ _ hDone hEnd hPend⟩
  · rw [ite_eq_right hq] at h
    exact h

/-! ## Each round -/

theorem uniPre_ne (s : USt) (p : Op Stk) (m : Option Stk × List E) (h0 : p.length ≠ 0)
    (h1 : p.length ≠ Fl.prog.rounds.length + 1) : uniPre Fl I s p m = uniS Fl I s p := by
  unfold uniPre
  rw [ite_eq_right h0, ite_eq_right h1]

/-- **Round `0`**: the bus and the constraints (`mainSound`), Flock's predicate from its state's
start (`S_nil`). -/
theorem uniSound_zero (s : USt) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 6}[¬ uniPre Fl I s [] m ∧ uniPost Fl I s [] m c] ≤ I.errMain := by
  have hpre : uniPre Fl I s [] m = ∃ c, m.1 = some c ∧ Rel D s c := by
    unfold uniPre
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
    rw [show fdOf Fl.prog.rounds.length ([] ++ [(m, c)] : Op Stk) = [] by simp [fdOf]] at hS
    rw [hpre] at hn
    exact ⟨fun hmain => hn ⟨c1, hm, I.rel_of s c1 hmain (Fl.S_nil _ hS)⟩, hOK⟩

/-- **Flock's round `j − 1`**: Flock's `step`. -/
theorem uniSound_flock (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ Fl.prog.rounds.length) (s : USt) (p : Op Stk)
    (hp : p.length = j) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E ((Fl.prog.rounds[j - 1]'(by omega)).ns + 1)}[
      ¬ uniPre Fl I s p m ∧ uniPost Fl I s p m c] ≤ Fl.err (j - 1) := by
  rw [uniPre_ne Fl I s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  have hfd : ∀ c : List E, fdOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      fdOf Fl.prog.rounds.length p ++ [((none, m.2), c)] := fun c =>
    fdOf_append_le _ p _ (by omega) (by omega)
  by_cases hfit : DoneFits (Fl.prog.rounds.take (j - 1)) (fdOf Fl.prog.rounds.length p) ∧
      UMsg.Fits (Fl.prog.rounds[j - 1]'(by omega)) (none, m.2)
  · have hb := Fl.step (j - 1) (by omega) (I.qf c1) _ (none, m.2) hfit.1 hfit.2
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

/-- **`C2`'s round, the point `t`**: Schwartz–Zippel for every identity. -/
theorem uniSound_c2 (s : USt) (p : Op Stk) (hp : p.length = Fl.prog.rounds.length + 1)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 1}[¬ uniPre Fl I s p m ∧ uniPost Fl I s p m c] ≤
      (I.degSum : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have hpre : uniPre Fl I s p m = ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2, P = 0) ∧
      FlockEndHolds (I.qf c1) (Fl.prog.out (fdOf Fl.prog.rounds.length p) []) ∧
      PendingHolds (Fl.prog.out (fdOf Fl.prog.rounds.length p) []).2.2 ∧
      FlockDone Fl (fdOf Fl.prog.rounds.length p) := by
    unfold uniPre
    rw [ite_eq_right (by omega), ite_eq_left hp]
  rw [hpre]
  have hlt : 0 < p.length := by omega
  have hx : ∀ c : List E, rd (p ++ [(m, c)]) (Fl.prog.rounds.length + 1) = (m, c) := fun c => by
    rw [← hp, rd_append_self]
  have hfd : ∀ c : List E, fdOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      fdOf Fl.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
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
      (fdOf Fl.prog.rounds.length p) c2, P ≠ 0 ∧ P.eval (c.headD 0) = 0] ≤
      (I.degSum : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
    (prEvent_root_le (I.polys s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2)).trans
      (ENNReal.div_le_div_right (Nat.cast_le.mpr
        (I.deg_le s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2)) _)
  refine (prEvent_mono _ _ _ ?_).trans hb
  rintro c ⟨hn, hpost⟩
  obtain ⟨c1', hc1, hpost⟩ := hpost
  rw [rd_append_lt _ _ 0 hlt, h0] at hc1
  cases hc1
  rw [ite_eq_right (by simp; omega)] at hpost
  obtain ⟨c2', hc2, hDone, hrest⟩ := hpost
  rw [hx, hm] at hc2
  cases hc2
  rw [ite_eq_left (by simp; omega)] at hrest
  obtain ⟨vals, hz⟩ := hrest
  rw [rd_append_lt _ _ 0 hlt, hfd, hx] at hz
  rw [hfd] at hDone
  have hev := I.diffs_eval _ _ _ _ _ _ _ hz
  have hEnd := I.diffs_flock _ _ _ _ _ _ _ hz
  have hPend := I.diffs_pending _ _ _ _ _ _ _ hz
  by_contra hno
  refine hn ⟨c1, c2, rfl, rfl, fun P hP => ?_, hEnd, hPend, hDone⟩
  by_contra hP0
  exact hno ⟨P, hP, hP0, hev P hP⟩

/-- **The values' round, `ρ` and `λ`**: the two combinations. -/
theorem uniSound_vals (s : USt) (p : Op Stk) (hp : p.length = Fl.prog.rounds.length + 2)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 2}[¬ uniPre Fl I s p m ∧ uniPost Fl I s p m c] ≤
      ((I.nRel - 1 + (4 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  rw [uniPre_ne Fl I s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  have hlt1 : Fl.prog.rounds.length + 1 < p.length := by omega
  have hx : ∀ c : List E, rd (p ++ [(m, c)]) (Fl.prog.rounds.length + 2) = (m, c) := fun c => by
    rw [← hp, rd_append_self]
  have hfd : ∀ c : List E, fdOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      fdOf Fl.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
  have hbr : ∀ c : List E, brOf Fl.prog.rounds.length (p ++ [(m, c)]) = [] := fun c =>
    brOf_of_length _ _ (by simp; omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  rcases h2 : (rd p (Fl.prog.rounds.length + 1)).1.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
  by_cases hbad : ∃ d ∈ I.diffs s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
      ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) m.2, ∃ x ∈ d, x ≠ 0
  · have hb := prEvent_twoLevel_le (I.diffs s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
      ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) m.2) I.nRel 4
      (I.diffs_len s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
        ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) m.2)
      (I.diffs_count s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
        ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) m.2) hbad
    refine (prEvent_mono _ _ _ ?_).trans hb
    rintro c ⟨-, hpost⟩
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -, hrest⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
    rw [ite_eq_right (by simp; omega)] at hrest
    rw [hbr, rd_append_lt _ _ 0 hlt, rd_append_lt _ _ _ hlt1, hfd, hx] at hrest
    unfold SumState claimAfter pointAfter at hrest
    simp only [List.map_nil] at hrest
    rw [← I.batch_start, show (I.prod _ _ _ _ _ _ _ _ _).T [] = _ from hrest.symm]
    exact CharTwo.add_self_eq_zero _
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨hn, hpost⟩ => hn ?_
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, hDone, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
    refine ⟨c1, h0, ?_⟩
    rw [ite_eq_right (by omega)]
    refine ⟨c2, h2, by rwa [hfd] at hDone, ?_⟩
    rw [ite_eq_left hp]
    refine ⟨m.2, fun d hd x hx => ?_⟩
    by_contra hx0
    exact hbad ⟨d, hd, x, hx, hx0⟩

/-- **A round of the batching sumcheck**: `2 / |E|`. -/
theorem uniSound_batch (j : ℕ) (h1 : Fl.prog.rounds.length + 3 ≤ j)
    (h2 : j < Fl.prog.rounds.length + 3 + I.V) (s : USt) (p : Op Stk) (hp : p.length = j)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 1}[¬ uniPre Fl I s p m ∧ uniPost Fl I s p m c] ≤
      ((2 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  rw [uniPre_ne Fl I s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  have hlt1 : Fl.prog.rounds.length + 1 < p.length := by omega
  have hlt2 : Fl.prog.rounds.length + 2 < p.length := by omega
  have hfd : ∀ c : List E, fdOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      fdOf Fl.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
  have hbr : ∀ c : List E, brOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      brOf Fl.prog.rounds.length p ++ [(m.2, c)] := fun c => brOf_append _ _ _ (by omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  rcases hc2' : (rd p (Fl.prog.rounds.length + 1)).1.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, hc2'] at hc2
    cases hc2
  set O := (I.prod s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
    ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) (rd p (Fl.prog.rounds.length + 2)).1.2
    ((rd p (Fl.prog.rounds.length + 2)).2.headD 0)
    ((rd p (Fl.prog.rounds.length + 2)).2.getD 1 0)).oracle with hO
  set tg := I.target s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
    ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) (rd p (Fl.prog.rounds.length + 2)).1.2
    ((rd p (Fl.prog.rounds.length + 2)).2.headD 0)
    ((rd p (Fl.prog.rounds.length + 2)).2.getD 1 0) with htg
  have hvars : (brOf Fl.prog.rounds.length p).length < O.vars := by
    rw [length_brOf, hO]
    show _ < (I.prod _ _ _ _ _ _ _ _ _).vars
    rw [I.prod_vars]
    omega
  have hb := O.step_sound tg (brOf Fl.prog.rounds.length p) hvars m.2
  refine (prEvent_mono _ _ _ ?_).trans hb
  rintro c ⟨hn, hpost⟩
  obtain ⟨c1', hc1, hpost⟩ := hpost
  rw [rd_append_lt _ _ 0 hlt, h0] at hc1
  cases hc1
  rw [ite_eq_right (by simp; omega)] at hpost
  obtain ⟨c2', hc2, hDone, hrest⟩ := hpost
  rw [rd_append_lt _ _ _ hlt1, hc2'] at hc2
  cases hc2
  rw [ite_eq_right (by simp; omega)] at hrest
  rw [hbr, rd_append_lt _ _ 0 hlt, rd_append_lt _ _ _ hlt1, rd_append_lt _ _ _ hlt2, hfd] at hrest
  refine ⟨fun hS => hn ⟨c1, h0, ?_⟩, hrest⟩
  rw [ite_eq_right (by omega)]
  refine ⟨c2, hc2', by rwa [hfd] at hDone, ?_⟩
  rw [ite_eq_right (by omega)]
  exact hS

/-! ## The protocol -/

/-- **The univariate PIOP, round by round** (main line), for the Flock phase `Fl` and the identity
model `I`. -/
noncomputable def uniPiop : RbrPiop (uniRounds Fl.prog.rounds I.nV I.V) USt Stk where
  pre := uniPre Fl I
  post := uniPost Fl I
  pre_post := uniPre_pre_post Fl I
  err := uniErr Fl I
  sound j s p m hj hp := by
    rw [length_uniRounds] at hj
    unfold uniErr
    by_cases h0 : j = 0
    · subst h0
      rw [ite_eq_left rfl, uniRounds_zero]
      obtain rfl : p = [] := List.length_eq_zero_iff.mp hp
      exact uniSound_zero Fl I s m
    rw [ite_eq_right h0]
    by_cases h1 : j ≤ Fl.prog.rounds.length
    · rw [ite_eq_left h1, uniRounds_flock _ _ _ j (by omega) h1,
        List.getD_eq_getElem _ _ (by omega)]
      exact uniSound_flock Fl I j (by omega) h1 s p hp m
    rw [ite_eq_right h1]
    by_cases h2 : j = Fl.prog.rounds.length + 1
    · subst h2
      rw [ite_eq_left rfl, uniRounds_c2]
      exact uniSound_c2 Fl I s p hp m
    rw [ite_eq_right h2]
    by_cases h3 : j = Fl.prog.rounds.length + 2
    · subst h3
      rw [ite_eq_left rfl, uniRounds_vals]
      exact uniSound_vals Fl I s p hp m
    rw [ite_eq_right h3, uniRounds_batch _ _ _ j (by omega) hj]
    exact uniSound_batch Fl I j (by omega) hj s p hp m

end UniSound
