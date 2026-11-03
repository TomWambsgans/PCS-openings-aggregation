-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.Rec3Instance

/-!
# π1-rec3's walk on the transcript: `WalkSpec` from the walk's lemma

`walkSpec_of`: `WalkSpec κ` (on a completed transcript of π1-rec3's Flock rounds whose walk's zero vanishes, the main
line's reading's pending claim is its sum) from **the walk's lemma at the front's shape** (`WalkLemma`: for a skip
point, a row point of `3` coordinates, lincheck points of `8`, `64` slices, `walkedTerminal … + r_lc = 0` gives
`PendingHolds (Pending.new …)`). The program's zero is `walkOf` of the rounds before the slices (`walkOf_take`), whose
decoded front is the one the main line's `outOf` hands `Pending.new` (`outOf_expandFd_eq`).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics

variable {κ : ℕ}

/-- **The walk's lemma at the main line's front shape.** -/
def WalkLemma : Prop :=
  ∀ (z : E) (rowLow chiIn chiInPrime s : List E) (alpha rLc : E), rowLow.length = 3 → chiIn.length = 8 →
    chiInPrime.length = 8 → s.length = 64 →
    Flock.walkedTerminal (some z) rowLow chiIn chiInPrime s alpha + rLc = 0 →
      PendingHolds (Flock.Pending.new (some z) rowLow chiIn chiInPrime alpha rLc (some s))

theorem outOf_expandFd_eq (κ : ℕ) (d : Done) (h : d ≠ []) :
    outOf κ (expandFd κ d) = flockOut (squares ((rd d 0).2.headD 0) (4 + κ)) (rd d 1).1.2
      ((rd d 1).2.headD 0) ((d.drop 2).take (11 + κ))
      ((rd (d.drop (13 + κ)) 0).1.2.getD 0 0) ((rd (d.drop (13 + κ)) 0).1.2.getD 1 0)
      ((rd (d.drop (13 + κ)) 0).2.headD 0) ((d.drop (14 + κ)).take 8) (rd (d.drop (22 + κ)) 0).1.2
      (rd (d.drop (22 + κ)) 0).2 := by
  rw [outOf, rd_expandFd_zero κ d h, rd_expandFd_succ, drop_expandFd,
    show 13 + κ = (12 + κ) + 1 by omega, drop_expandFd, show 14 + κ = (13 + κ) + 1 by omega, drop_expandFd,
    show 22 + κ = (21 + κ) + 1 by omega, drop_expandFd]

/-- **The walk reads the rounds before the slices only.** -/
theorem walkOf_take (d : Done) (s : List E) : walkOf κ (d.take (22 + κ)) s = walkOf κ d s := by
  unfold walkOf
  have h0 : rd (d.take (22 + κ)) 0 = rd d 0 := rd_take (by omega)
  have h1 : rd (d.take (22 + κ)) 1 = rd d 1 := rd_take (by omega)
  have h2 : ((d.take (22 + κ)).drop 2).take (11 + κ) = (d.drop 2).take (11 + κ) := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  have h13 : rd ((d.take (22 + κ)).drop (13 + κ)) 0 = rd (d.drop (13 + κ)) 0 := by
    rw [rd_drop, rd_drop, rd_take (by omega)]
  have h14 : ((d.take (22 + κ)).drop (14 + κ)).take 8 = (d.drop (14 + κ)).take 8 := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  rw [h0, h1, h2, h13, h14]

theorem flockProg3_zeros (d : Done) (msg : UMsg) (h : d.length = 22 + κ) :
    (flockProg3 κ).zeros d msg = [walkOf κ d msg.2] := by
  show (if d.length = 22 + κ then [walkOf κ d msg.2] else []) = _
  rw [ite_eq_left h]

theorem length_decodeSC_fst (c : E) (es : List (Option E)) (d : Done) (h : d.length = es.length) :
    (decodeSC c es d).1.length = d.length := by
  rw [decodeSC_eq c es d h, List.length_map]

/-- **`WalkSpec` from the walk's lemma.** -/
theorem walkSpec_of (hW : WalkLemma) : WalkSpec κ := by
  intro done tl hfit hz
  have hd : done ≠ [] := by
    rintro rfl
    exact hfit
  have hF := fits_of_doneFits (doneFits_expandFd hfit)
  have hl : done.length = 23 + κ := by rw [← length_expandFd κ done]; exact hF.len
  -- The program's zero, in the slices' round.
  have hzero : walkOf κ done (rd done (22 + κ)).1.2 = 0 := by
    have hlt : 22 + κ < done.length := by omega
    have h := hz.1 (22 + κ) hlt
    have hlen : (done.take (22 + κ)).length = 22 + κ := by rw [List.length_take]; omega
    rw [flockProg3_zeros _ _ hlen] at h
    have h' := h _ (List.mem_singleton_self _)
    rw [walkOf_take, ← rd_eq_getElem hlt] at h'
    exact h'
  -- The reading's pending reduction, at the same decoded front.
  rw [outOf_expandFd_eq κ done hd]
  have hzc : ((done.drop 2).take (11 + κ)).length = 11 + κ := by
    rw [List.length_take, List.length_drop]; omega
  have hlc : ((done.drop (14 + κ)).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; omega
  have hes : ((Flock.fixedChallenges ++ squares ((rd done 0).2.headD 0) (4 + κ)).map some).length = 11 + κ := by
    rw [List.length_map, List.length_append, length_fixedChallenges, length_squares]
    omega
  have hzr := length_decodeSC_fst (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ (rd done 1).1.2)
    ((rd done 1).2.headD 0)) _ _ (hzc.trans hes.symm)
  rw [hzc] at hzr
  set zr := decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ (rd done 1).1.2)
    ((rd done 1).2.headD 0)) ((Flock.fixedChallenges ++ squares ((rd done 0).2.headD 0) (4 + κ)).map some)
    ((done.drop 2).take (11 + κ)) with hzr_def
  have hlr := length_decodeSC_fst ((rd (done.drop (13 + κ)) 0).1.2.getD 0 0 +
    (rd (done.drop (13 + κ)) 0).2.headD 0 * (rd (done.drop (13 + κ)) 0).1.2.getD 1 0 +
    epow ((rd (done.drop (13 + κ)) 0).2.headD 0) 2 *
      (zr.2 + (rd (done.drop (13 + κ)) 0).1.2.getD 0 0 * (rd (done.drop (13 + κ)) 0).1.2.getD 1 0) +
    epow ((rd (done.drop (13 + κ)) 0).2.headD 0) 3) (List.replicate 8 none) ((done.drop (14 + κ)).take 8)
    (by rw [hlc, List.length_replicate])
  rw [hlc] at hlr
  have hs : (rd (done.drop (22 + κ)) 0).1.2.length = 64 := by
    have h6 := hF.r6v
    rw [show 22 + κ = (21 + κ) + 1 by omega, rd_expandFd_succ] at h6
    rw [rd_drop, Nat.add_zero, show 22 + κ = (21 + κ) + 1 by omega]
    exact h6
  refine hW _ _ _ _ _ _ _ (by rw [List.length_take, hzr]; omega)
    (by rw [List.length_take, List.length_drop, hzr]; omega) (by rw [List.length_reverse, hlr]) hs ?_
  have e : (rd (done.drop (22 + κ)) 0).1.2 = (rd done (22 + κ)).1.2 := by rw [rd_drop, Nat.add_zero]
  rw [e]
  exact hzero

end FlockSound.Uni

/-- info: 'FlockSound.Uni.walkSpec_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.walkSpec_of
