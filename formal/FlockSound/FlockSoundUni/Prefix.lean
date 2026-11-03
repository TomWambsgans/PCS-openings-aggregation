-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.Parse

/-!
# The bad family's prefix property

The bad set at challenge `i` of round `j` (`badAt` of a parse) reads only the rounds before `j`,
round `j`'s message and its challenges before `i`: two transcripts that agree there (`AgreeAt`)
have the same bad set there (**`badAt_congr`**). A completed transcript agrees at `(j, i)` with
its prefix (`agree_pfx`: the rounds before `j`, round `j`'s message, its first `i` challenges), which
is what `flockBad` parses; so a challenge of the transcript in the bad set of the transcript's own
parse at its position is a hit of `flockBad` (**`hitIn_of_mem`**).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-- **Two transcripts agree at challenge `i` of round `j`**: on the rounds before `j`, round `j`'s
message and its challenges before `i`. -/
def AgreeAt (d d' : Done) (j i : ℕ) : Prop :=
  (∀ a < j, rd d a = rd d' a) ∧ (rd d j).1 = (rd d' j).1 ∧
    ∀ b < i, (rd d j).2.getD b 0 = (rd d' j).2.getD b 0

/-! ## The parse's fields read their rounds -/

section Fields

variable {d d' : Done}

theorem parse_τs (h : rd d 0 = rd d' 0) : (parse κ d).τs = (parse κ d').τs := by
  funext a
  show (rd d 0).2.getD a 0 = (rd d' 0).2.getD a 0
  rw [h]

theorem parse_cv (h : (rd d 1).1 = (rd d' 1).1) : (parse κ d).cv = (parse κ d').cv := by
  funext b
  show (rd d 1).1.2.getD _ 0 = (rd d' 1).1.2.getD _ 0
  rw [h]

theorem parse_z (h : rd d 1 = rd d' 1) : (parse κ d).z = (parse κ d').z := by
  show (rd d 1).2.headD 0 = (rd d' 1).2.headD 0
  rw [h]

theorem pEs_congr (h : rd d 0 = rd d' 0) : pEs d = pEs d' := by
  simp only [pEs, pSampled, h]

theorem pC0_congr (h : rd d 1 = rd d' 1) : pC0 d = pC0 d' := by
  simp only [pC0, pCoset, pZ, h]

theorem parse_zq (t : Fin (3 + 8 + κ)) (h : ∀ a < 2 + t.val, rd d a = rd d' a)
    (h1 : (rd d (2 + t.val)).1 = (rd d' (2 + t.val)).1) : (parse κ d).zq t = (parse κ d').zq t := by
  show msgPoly (decodeMsg (scClaim (pC0 d) (pEs d) (d.drop 2) t) ((pEs d).getD t none)
      (rd (d.drop 2) t).1.2) =
    msgPoly (decodeMsg (scClaim (pC0 d') (pEs d') (d'.drop 2) t) ((pEs d').getD t none)
      (rd (d'.drop 2) t).1.2)
  rw [pC0_congr (h 1 (by omega)), pEs_congr (h 0 (by omega)),
    scClaim_congr (d := d.drop 2) (d' := d'.drop 2) _ _ t fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega), rd_drop, rd_drop, h1]

theorem parse_zχ (t : Fin (3 + 8 + κ)) (h : rd d (2 + t.val) = rd d' (2 + t.val)) :
    (parse κ d).zχ t = (parse κ d').zχ t := by
  show (rd (d.drop 2) t).2.headD 0 = (rd (d'.drop 2) t).2.headD 0
  rw [rd_drop, rd_drop, h]

theorem parse_zq_eq (h : ∀ a < 13 + κ, rd d a = rd d' a) : (parse κ d).zq = (parse κ d').zq := by
  funext t
  have := t.isLt
  exact parse_zq t (fun a ha ↦ h a (by omega)) (by rw [h _ (by omega)])

theorem parse_zχ_eq (h : ∀ a < 13 + κ, rd d a = rd d' a) : (parse κ d).zχ = (parse κ d').zχ := by
  funext t
  have := t.isLt
  exact parse_zχ t (h _ (by omega))

theorem parse_va (h : (rd d (13 + κ)).1 = (rd d' (13 + κ)).1) : (parse κ d).va = (parse κ d').va := by
  show (rd d (13 + κ)).1.2.getD 0 0 = (rd d' (13 + κ)).1.2.getD 0 0
  rw [h]

theorem parse_vb (h : (rd d (13 + κ)).1 = (rd d' (13 + κ)).1) : (parse κ d).vb = (parse κ d').vb := by
  show (rd d (13 + κ)).1.2.getD 1 0 = (rd d' (13 + κ)).1.2.getD 1 0
  rw [h]

theorem parse_α (h : rd d (13 + κ) = rd d' (13 + κ)) : (parse κ d).α = (parse κ d').α := by
  show (rd d (13 + κ)).2.headD 0 = (rd d' (13 + κ)).2.headD 0
  rw [h]

theorem pRunning_congr (h : ∀ a < 13 + κ, rd d a = rd d' a) : pRunning κ d = pRunning κ d' := by
  unfold pRunning
  rw [pC0_congr (h 1 (by omega)), pEs_congr (h 0 (by omega)),
    scClaim_congr (d := d.drop 2) (d' := d'.drop 2) _ _ _ fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega)]

theorem pLc0_congr (h : ∀ a < 14 + κ, rd d a = rd d' a) : pLc0 κ d = pLc0 κ d' := by
  unfold pLc0 pVa pVb pAlpha
  rw [pRunning_congr fun a ha ↦ h a (by omega), h (13 + κ) (by omega)]

theorem parse_lq (t : Fin 8) (h : ∀ a < 14 + κ + t.val, rd d a = rd d' a)
    (h1 : (rd d (14 + κ + t.val)).1 = (rd d' (14 + κ + t.val)).1) :
    (parse κ d).lq t = (parse κ d').lq t := by
  show msgPoly (decodeMsg (scClaim (pLc0 κ d) (List.replicate 8 none) (d.drop (14 + κ)) t) none
      (rd (d.drop (14 + κ)) t).1.2) =
    msgPoly (decodeMsg (scClaim (pLc0 κ d') (List.replicate 8 none) (d'.drop (14 + κ)) t) none
      (rd (d'.drop (14 + κ)) t).1.2)
  rw [pLc0_congr fun a ha ↦ h a (by omega),
    scClaim_congr (d := d.drop (14 + κ)) (d' := d'.drop (14 + κ)) _ _ t fun v hv ↦ by
      rw [rd_drop, rd_drop]; exact h _ (by omega), rd_drop, rd_drop, h1]

theorem parse_lχ (t : Fin 8) (h : rd d (14 + κ + t.val) = rd d' (14 + κ + t.val)) :
    (parse κ d).lχ t = (parse κ d').lχ t := by
  show (rd (d.drop (14 + κ)) t).2.headD 0 = (rd (d'.drop (14 + κ)) t).2.headD 0
  rw [rd_drop, rd_drop, h]

theorem parse_lχ_eq (h : ∀ a < 22 + κ, rd d a = rd d' a) : (parse κ d).lχ = (parse κ d').lχ := by
  funext t
  have := t.isLt
  exact parse_lχ t (h _ (by omega))

theorem parse_s (h : (rd d (22 + κ)).1 = (rd d' (22 + κ)).1) : (parse κ d).s = (parse κ d').s := by
  funext cy
  show (rd d (22 + κ)).1.2.getD _ 0 = (rd d' (22 + κ)).1.2.getD _ 0
  rw [h]

/-! The derived values. -/

theorem τ_congr (h : rd d 0 = rd d' 0) :
    Front.τ (mainSetup κ) (parse κ d) = Front.τ (mainSetup κ) (parse κ d') := by
  show fullPoint _ _ (parse κ d).τs = fullPoint _ _ (parse κ d').τs
  rw [parse_τs h]

theorem c₀_congr (h : rd d 1 = rd d' 1) :
    Front.c₀ (mainSetup κ) (parse κ d) = Front.c₀ (mainSetup κ) (parse κ d') := by
  show (FlockSound.interp _ (parse κ d).cv).eval (parse κ d).z =
    (FlockSound.interp _ (parse κ d').cv).eval (parse κ d').z
  rw [parse_cv (congrArg Prod.fst h), parse_z h]

theorem vc_congr (h : ∀ a < 13 + κ, rd d a = rd d' a) (h1 : (rd d (13 + κ)).1 = (rd d' (13 + κ)).1) :
    Front.vc (mainSetup κ) (parse κ d) = Front.vc (mainSetup κ) (parse κ d') := by
  show claimAt (Front.c₀ (mainSetup κ) (parse κ d)) (parse κ d).zq (parse κ d).zχ (Fin.last _) +
      (parse κ d).va * (parse κ d).vb =
    claimAt (Front.c₀ (mainSetup κ) (parse κ d')) (parse κ d').zq (parse κ d').zχ (Fin.last _) +
      (parse κ d').va * (parse κ d').vb
  rw [c₀_congr (h 1 (by omega)), parse_zq_eq h, parse_zχ_eq h, parse_va h1, parse_vb h1]

theorem rl_congr (h : ∀ a < 13 + κ, rd d a = rd d' a) :
    Front.rl (mainSetup κ) (parse κ d) = Front.rl (mainSetup κ) (parse κ d') := by
  show lowPart (lowPart (parse κ d).zχ) = lowPart (lowPart (parse κ d').zχ)
  rw [parse_zχ_eq h]

theorem rh_congr (h : ∀ a < 13 + κ, rd d a = rd d' a) :
    Front.rh (mainSetup κ) (parse κ d) = Front.rh (mainSetup κ) (parse κ d') := by
  show highPart (lowPart (parse κ d).zχ) = highPart (lowPart (parse κ d').zχ)
  rw [parse_zχ_eq h]

theorem rt_congr (h : ∀ a < 13 + κ, rd d a = rd d' a) :
    Front.rt (mainSetup κ) (parse κ d) = Front.rt (mainSetup κ) (parse κ d') := by
  show highPart (parse κ d).zχ = highPart (parse κ d').zχ
  rw [parse_zχ_eq h]

theorem χ'_congr (h : ∀ a < 22 + κ, rd d a = rd d' a) :
    Front.χ' (mainSetup κ) (parse κ d) = Front.χ' (mainSetup κ) (parse κ d') := by
  show (fun j ↦ (parse κ d).lχ (Fin.rev j)) = fun j ↦ (parse κ d').lχ (Fin.rev j)
  rw [parse_lχ_eq h]

end Fields

/-! ## The prefix property -/

/-- **The bad set at `(j, i)` reads the transcript before `(j, i)` only.** -/
theorem badAt_congr (qf : Column (8 + κ)) {d d' : Done} {j i : ℕ} (hA : AgreeAt d d' j i) :
    badAt qf (parse κ d) j i = badAt qf (parse κ d') j i := by
  obtain ⟨hlt, hmsg, hch⟩ := hA
  unfold badAt
  by_cases h0 : j = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    subst h0
    split_ifs with hi
    · exact pointBad_congr _ _ _ _ _ fun a ha ↦ hch a (by simpa using ha)
    · rfl
  simp only [ite_eq_right h0]
  by_cases h1 : j = 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    subst h1
    split_ifs
    · rw [τ_congr (hlt 0 (by omega)), parse_cv hmsg]
    · rfl
  simp only [ite_eq_right h1]
  by_cases h2 : j < 13 + κ
  · simp only [dite_eq_left h2]
    split_ifs
    · have hj : 2 + (j - 2) = j := by omega
      rw [τ_congr (hlt 0 (by omega)), c₀_congr (hlt 1 (by omega)), parse_z (hlt 1 (by omega))]
      refine zcBad_congr _ _ _ _ _ _ _ _ _ _ _ _ _ (fun u hu ↦ ?_) (fun u hu ↦ ?_)
      · simp only at hu
        refine parse_zq u (fun a ha ↦ hlt a (by omega)) ?_
        rcases Nat.lt_or_ge (2 + u.val) j with hl | hl
        · rw [hlt _ hl]
        · rw [show 2 + u.val = j by omega]
          exact hmsg
      · simp only at hu
        exact parse_zχ u (hlt _ (by omega))
    · rfl
  simp only [dite_eq_right h2]
  by_cases h3 : j = 13 + κ
  · rw [ite_eq_left h3, ite_eq_left h3]
    subst h3
    split_ifs
    · rw [vc_congr hlt hmsg, rt_congr hlt, parse_va hmsg, parse_vb hmsg, parse_z (hlt 1 (by omega)),
        parse_zχ_eq hlt]
    · rfl
  simp only [ite_eq_right h3]
  by_cases h4 : j < 22 + κ
  · simp only [dite_eq_left h4]
    split_ifs
    · have h13 : ∀ a < 13 + κ, rd d a = rd d' a := fun a ha ↦ hlt a (by omega)
      rw [rl_congr h13, rh_congr h13, rt_congr h13, parse_z (hlt 1 (by omega)),
        parse_α (hlt (13 + κ) (by omega))]
      refine sumBad_congr' 2 8 _ _ _ _ _ _ _ ?_ fun u hu ↦ ?_
      · refine parse_lq _ (fun a ha ↦ hlt a (by simp only at ha; omega)) ?_
        simp only
        rw [show 14 + κ + (j - (14 + κ)) = j by omega]
        exact hmsg
      · simp only at hu
        exact parse_lχ u (hlt _ (by omega))
    · rfl
  simp only [dite_eq_right h4]
  by_cases h5 : j = 22 + κ
  · rw [ite_eq_left h5, ite_eq_left h5]
    subst h5
    split_ifs
    · rw [rt_congr fun a ha ↦ hlt a (by omega), χ'_congr hlt, parse_s hmsg]
      exact ringBad_congr _ _ _ _ _ _ _ fun a ha ↦ hch a (by simpa using ha)
    · rfl
  simp only [ite_eq_right h5]

/-- **A transcript agrees with its prefix** at `(j, i)`: its rounds before `j`, round `j`'s message
and its first `i` challenges. -/
theorem agree_pfx {done : Done} {j : ℕ} (hj : j < done.length) (i : ℕ) :
    AgreeAt (done.take j ++ [((rd done j).1, (rd done j).2.take i)]) done j i := by
  have hl : (done.take j).length = j := by simp only [List.length_take]; omega
  refine ⟨fun a ha ↦ ?_, ?_, fun b hb ↦ ?_⟩
  · rw [rd_append_left (by omega), rd_take ha]
  · rw [rd_append_right (by omega), hl, Nat.sub_self]
    rfl
  · rw [rd_append_right (by omega), hl, Nat.sub_self]
    show ((rd done j).2.take i).getD b 0 = (rd done j).2.getD b 0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hb, ite_true]

/-- **A challenge in its own parse's bad set is a hit of `flockBad`.** -/
theorem hitIn_of_mem (qf : Column (8 + κ)) {done : Done} {j i : ℕ} (hj : j < done.length)
    (hi : i < (rd done j).2.length)
    (hmem : (rd done j).2.getD i 0 ∈ badAt qf (parse κ done) j i) : HitIn (flockBad κ) qf done := by
  obtain ⟨r, ds, rfl⟩ : ∃ r ds, done = r :: ds :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega))
  have hr := rd_eq_getElem hj
  refine ⟨j, hj, i, by rw [← hr]; exact hi, ?_⟩
  show _ ∈ flockBad κ qf ((r :: ds).take j) ((r :: ds)[j]).1 (((r :: ds)[j]).2.take i)
  rw [← hr]
  unfold flockBad
  rw [List.length_take, min_eq_left hj.le, List.length_take, min_eq_left hi.le,
    badAt_congr qf (agree_pfx hj i)]
  exact hmem

end FlockSound.Uni
