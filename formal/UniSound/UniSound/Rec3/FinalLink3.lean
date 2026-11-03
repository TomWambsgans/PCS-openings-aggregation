-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `Rec3/Fs3.lean`'s `UniFinal3`; the
-- proof follows `FinalLink.lean`'s `uniFinal` (the main line's), without the pending matrices' term.
import UniSound.Rec3.CodeLink3
import UniSound.Rec3.Ids3
import UniSound.Rec3.Batch3
import UniSound.Ids.Align
import FlockSoundUni.Good

/-!
# The last link at π1-rec3 (`UniFinal3`)

**`uniFinal3`**: for π1-rec3's identity model `ids3Of D N h d n g tx hw np hV` (the main line's at the expanded
transcripts, `Rec3/Ids3.lean`), Flock's phase `flockSound3_of tx hw`, the paired batch `pairBatchRec3 np` and the
code-level link `uniCode3At`, on a completed transcript whose zeros vanish and whose three claims are true:

* **the pending claim is its sum**: Flock's segment of the transcript has its zeros among the chain program's
  (`zeros3`: rounds `1 … nF`, and the tail zeros in `C2`'s round), so the walk (`FlockSound3.walk`) applies;
* **the batch's last state holds** (`BatchState3 cantorBeta1 narrowE` at the batch's point `pointAfter3`), unless `t`
  is a root of the merge polynomial: the terminal zero `sum + last = 0` is `last = Σ_k λ^k W_k(r) ext_k(r) v_k`, the
  claims give `v_k = Ĉ_k(r)`, the weights are multilinear at `r` (`WeightMle`, the main line's, at the expanded
  transcripts: the batch's point is any point of `E^V`), so `last` is the products' partial sum at the full point
  (`batchState3_full_np`, `terminal3`). The identity model's batch is the verifier's (`main3Out_aligned`: the run's
  claims are `combAt` at `expandCh`, `expandFd`, `runClaims_eq`; Flock's result the main line's, `flockGood`), so the
  main line's `BatchIsVerifiers` is not a hypothesis here.

**Hypotheses** (the main line's, unchanged): `WeightMle` at the main line's Flock instance and merge polynomial, and
`LayoutVarsSmall`. Both are discharged at the reference deployment (`Rec3/FinalRef3.lean`).
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics Finset FlockSound.Uni UniSound.Ids

/-! ## The terminal -/

/-- The batch's target over one claim per commitment. -/
theorem batchTarget_commitments (f : Commitment → Combined) (lam : E) :
    (batchTarget (commitments.map fun c => (c, f c)) lam).1 = ∑ k ∈ range 3, lam ^ k * (f (cm k)).value := by
  simp only [batchTarget, commitments, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Finset.sum_range_succ, Finset.sum_range_zero, cm, List.getD_cons_zero, List.getD_cons_succ]
  ring

/-- **The batch's terminal check with true claims is the last claim's value** (the algebra of `UniFinal3`): the
terminal `sum + last = 0` with the stacks' point claims and the weights multilinear at the point makes `last` the
products' value there. -/
theorem terminal3 (f : Commitment → Combined) (L : List (Commitment × StackLayout)) (bs : Option Combined)
    (rm : Option (List E)) (lam : E) (brs : Done) (tl : List E) (stk : Commitment → Stk) (np : ℕ)
    (hnp : varsOf L / 2 = np) (htl : tl.length = 3)
    (hrl : (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)).length = varsOf L)
    (hz : ∀ z ∈ (batchPureW narrowE (commitments.map fun c => (c, f c)) L bs rm lam brs tl).1, z = 0)
    (hclaims : ∀ o ∈ (batchPureW narrowE (commitments.map fun c => (c, f c)) L bs rm lam brs tl).2,
      ∀ pt v bs', o.2 = .point pt v bs' → mleStk (stk o.1) (layoutOf L o.1).vars pt = v)
    (hW : ∀ c, foldAll (fun u => weightAt (f c) (layoutOf L c) (bitsE u (varsOf L)) rm)
        (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0 =
      weightAt (f c) (layoutOf L c) (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) rm) :
    claimAfter3 narrowE np (batchTarget (commitments.map fun c => (c, f c)) lam).1 (roundsOf brs) =
      ∑ k ∈ range 3, lam ^ k *
        (foldAll (fun u => weightAt (f (cm k)) (layoutOf L (cm k)) (bitsE u (varsOf L)) rm)
            (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0 *
          foldAll (fun u => stE (stk (cm k)) (layoutOf L (cm k)).vars u)
            (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0) := by
  subst hnp
  unfold batchPureW at hz hclaims
  generalize pointAfter3 cantorBeta1 narrowE (varsOf L / 2) (roundsOf brs) = r at hz hclaims hrl hW ⊢
  generalize claimAfter3 narrowE (varsOf L / 2) (batchTarget (commitments.map fun c => (c, f c)) lam).1
    (roundsOf brs) = cl at hz ⊢
  rcases tl with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, tl'⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at htl <;> try omega
  simp only [commitments, List.map_cons, List.map_nil, batchFold, List.length_cons, List.length_nil,
    List.take_succ_cons, List.take_zero, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
    List.foldl_nil] at hz hclaims
  have hcl := eq_of_add_eq_zero_char2 (hz _ (List.mem_singleton_self _))
  simp only [Array.toList_push, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hclaims
  obtain ⟨hc1, hc2, hc3⟩ := hclaims
  have hc1 := hc1 _ _ _ rfl
  have hc2 := hc2 _ _ _ rfl
  have hc3 := hc3 _ _ _ rfl
  have hv1 := layoutOf_vars_le L .c1
  have hv2 := layoutOf_vars_le L .c2
  have hv3 := layoutOf_vars_le L .setup
  rw [hcl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cm, commitments, List.getD_cons_zero,
    List.getD_cons_succ, zero_add]
  rw [hW .c1, hW .c2, hW .setup]
  unfold stE
  rw [foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega),
    hc1, hc2, hc3, ← hrl, extension_eq_cubeEq, extension_eq_cubeEq, extension_eq_cubeEq]
  ring

/-! ## The run's claims are the identity model's -/

/-- `flockClaim` reads only Flock's point and end. -/
theorem flockClaim_congr (rels : Array Relation) {fl fl' : List E × Option Flock.End × Flock.Pending}
    (h1 : fl.1 = fl'.1) (h2 : fl.2.1 = fl'.2.1) : flockClaim rels fl = flockClaim rels fl' := by
  obtain ⟨a, b, p⟩ := fl
  obtain ⟨a', b', p'⟩ := fl'
  simp only at h1 h2
  subst h1 h2
  rfl

section Model

variable (D : Deployment) (tx : Tx (D.shape.heights.getD opBlake2s 0))
  (hw : WalkSpec (D.shape.heights.getD opBlake2s 0))

/-- **π1-rec3's Flock claim is the main line's** at the expanded transcript, on a completed one. -/
theorem flockClaim3_eq (rels : Array Relation) (G : Done)
    (hG : DoneFits (flockSound3_of tx hw).prog.rounds G) :
    flockClaim3 rels ((flockSound3_of tx hw).prog.out G []) =
      flockClaim rels ((flockSoundInstance (D.shape.heights.getD opBlake2s 0)).prog.out
        (expandFd (D.shape.heights.getD opBlake2s 0) G) []) := by
  obtain ⟨h1, h2⟩ := (flockSound3_of tx hw).out_end G [] hG
  exact flockClaim_congr rels h1.symm h2.symm

/-- **The run's result is the identity model's batch**: its terminal zero and its openings are `batchPureW` of the
commitments' combined claims `combAt` (at `expandCh`, `expandFd`), the shape's layouts and Flock's ring map. -/
theorem main3Out_aligned (s : USt) (m0 : UMsg) (cc bb gg : E) (G : Done) (r2 r3 : UMsg × List E) (brs : Done)
    (tl : List E) (hG : DoneFits (flockSound3_of tx hw).prog.rounds G) :
    ∃ bs, (main3Out D (flockSound3_of tx hw) s.1 s.2 (m0, [cc, bb, gg]) G r2 r3 brs tl).1 =
        (batchPureW narrowE (commitments.map fun c => (c, combAt D
            (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s (expandCh [cc, bb, gg])
            (expandFd (D.shape.heights.getD opBlake2s 0) G) (r2.2.headD 0) r3.1.2 (r3.2.headD 0) c))
          (layoutsOf D.shape) bs (ringMapAt (flockSoundInstance (D.shape.heights.getD opBlake2s 0))
            (expandFd (D.shape.heights.getD opBlake2s 0) G))
          (r3.2.getD 1 0) brs tl).1 ∧
      (main3Out D (flockSound3_of tx hw) s.1 s.2 (m0, [cc, bb, gg]) G r2 r3 brs tl).2.openings =
        (batchPureW narrowE (commitments.map fun c => (c, combAt D
            (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s (expandCh [cc, bb, gg])
            (expandFd (D.shape.heights.getD opBlake2s 0) G) (r2.2.headD 0) r3.1.2 (r3.2.headD 0) c))
          (layoutsOf D.shape) bs (ringMapAt (flockSoundInstance (D.shape.heights.getD opBlake2s 0))
            (expandFd (D.shape.heights.getD opBlake2s 0) G))
          (r3.2.getD 1 0) brs tl).2 := by
  have hcl := runClaims_eq D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s (expandCh [cc, bb, gg])
    (expandFd (D.shape.heights.getD opBlake2s 0) G) (r2.2.headD 0) r3.1.2 (r3.2.headD 0) (by simp [expandCh])
  have he4 : (expandCh [cc, bb, gg]).getD 4 0 = bb := rfl
  have he5 : (expandCh [cc, bb, gg]).getD 5 0 = gg := rfl
  unfold runClaims at hcl
  rw [expandCh_take, he4, he5, ← flockClaim3_eq D tx hw _ G hG] at hcl
  have hc2 := mainRels_c2 D (publicWordsOf s.1.toList) (countsBits D.shape.heights s.2) (squares cc 4) bb gg
    (r2.2.headD 0) r3.1.2
  obtain ⟨hcl1, hcl2⟩ := hcl
  dsimp only at hcl1 hcl2
  refine ⟨combine (flockClaim3 (mainRels D.shape (publicWordsOf s.1.toList) (countsBits D.shape.heights s.2)
    (squares cc 4) bb gg (r2.2.headD 0) r3.1.2).1 ((flockSound3_of tx hw).prog.out G [])).2.1 .c1 1, ?_, ?_⟩
  · simp only [main3Out, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero, hc2, hcl1, hcl2]
    rfl
  · simp only [main3Out, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero, hc2, hcl1, hcl2]
    rfl

end Model

/-! ## Flock's zeros in the chain program's -/

/-- **Flock's segment's zeros are the chain program's** there: a program whose zeros after `x0 :: e` are Flock's after
`e` (for `e` shorter than Flock's rounds) and whose zeros after `x0 :: G` are Flock's tail zeros has, on a transcript
`x0 :: (G ++ x2 :: R)` whose zeros vanish, Flock's zeros vanishing on `G`. -/
theorem zerosVanish_flock {α β : Type} (P : ChainProg α) (Pf : ChainProg β) (x0 x2 : UMsg × List E) (G R : Done)
    (hG : G.length = Pf.rounds.length)
    (hzf : ∀ e msg, e.length < Pf.rounds.length → P.zeros (x0 :: e) msg = Pf.zeros e msg)
    (hzt : ∀ msg, P.zeros (x0 :: G) msg = Pf.tailZeros G [])
    (hz : ∀ j (h : j < (x0 :: (G ++ x2 :: R)).length),
      ∀ z ∈ P.zeros ((x0 :: (G ++ x2 :: R)).take j) ((x0 :: (G ++ x2 :: R))[j]'h).1, z = 0) :
    Pf.ZerosVanish G [] := by
  refine ⟨fun j hj z hzj => ?_, fun z hzt' => ?_⟩
  · have h1 := hz (j + 1) (by simp; omega) z
    simp only [List.take_succ_cons, List.getElem_cons_succ] at h1
    rw [List.take_append_of_le_length (by omega), List.getElem_append_left hj,
      hzf _ _ (by rw [List.length_take]; omega)] at h1
    exact h1 hzj
  · have h1 := hz (G.length + 1) (by simp) z
    simp only [List.take_succ_cons, List.getElem_cons_succ] at h1
    rw [List.take_append_of_le_length le_rfl, List.take_length, hzt] at h1
    exact h1 hzt'

/-! ## The last link -/

/-- **π1-rec3's last link** (`UniFinal3`) for its identity model `ids3Of` (the main line's at the expanded
transcripts), Flock's phase `flockSound3_of tx hw`, the paired batch `pairBatchRec3 np` and the code-level link
`uniCode3At`: under the main line's `WeightMle` (at Flock's main-line instance and its merge polynomial) and
`LayoutVarsSmall`. -/
theorem uniFinal3 (D : Deployment) (N : ℕ) (h : IdsHyps D N) (d n : ℕ)
    (g : IdsGaps D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) d n)
    (tx : Tx (D.shape.heights.getD opBlake2s 0)) (hw : WalkSpec (D.shape.heights.getD opBlake2s 0)) (np : ℕ)
    (hV : batchVars D.shape = 2 * np + 1) (hnV : nVOf D.shape = valsCount)
    (hW : WeightMle D (flockSoundInstance (D.shape.heights.getD opBlake2s 0))
      (idsRestOf D N h (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) d n g).zb)
    (hsmall : LayoutVarsSmall D) :
    UniFinal3 D (flockSound3_of tx hw) (ids3Of D N h d n g tx hw np hV) (pairBatchRec3 np)
      (uniCode3At D (flockSound3_of tx hw) rfl (ids3Of D N h d n g tx hw np hV).nV np hnV hV) := by
  intro s done tl c1 c2 hd htl hz hc
  change (main3Prog D (flockSound3_of tx hw) np s.1 s.2).ZerosVanish done tl at hz
  change ClaimsHold D ((main3Prog D (flockSound3_of tx hw) np s.1 s.2).out done tl) c1 c2 at hc
  have hd' : DoneFits ([⟨true, 0, 2⟩] ++ (flockSound3_of tx hw).prog.rounds ++
      [⟨true, 0, 0⟩, ⟨false, valsCount, 1⟩] ++ (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩])) done := by
    have e : (ids3Of D N h d n g tx hw np hV).nV = valsCount := hnV
    rw [e, rec3Rounds, List.append_assoc] at hd
    exact hd
  obtain ⟨d012, brs, rfl, h012, hbr⟩ := doneFits_append_split _ _ _ hd'
  obtain ⟨d01, d23, rfl, h01, h23⟩ := doneFits_append_split _ _ _ h012
  obtain ⟨d0, G, rfl, h0, hG⟩ := doneFits_append_split _ _ _ h01
  rcases d0 with _ | ⟨x0, _ | ⟨y0, d0⟩⟩ <;> simp only [DoneFits, and_false] at h0
  rcases d23 with _ | ⟨x2, _ | ⟨x3, _ | ⟨y3, d23⟩⟩⟩ <;> simp only [DoneFits, and_false] at h23
  obtain ⟨m0, ch0⟩ := x0
  obtain ⟨cc, bb, gg, rfl⟩ := List.length_eq_three.mp h0.2.1
  have hGl : G.length = (flockSound3_of tx hw).prog.rounds.length := doneFits_length _ _ hG
  have hbl : brs.length = np + 1 := by simpa using doneFits_length _ _ hbr
  have hvl : x3.1.2.length = valsCount := h23.2.2.1.2
  -- The counts, from round `0`'s zero.
  have hcf : CountsInRange D.shape.heights s.2 := by
    have h0z := hz.1 0 (by simp)
    rw [List.take_zero, main3Prog_zeros_nil] at h0z
    have h1 := h0z _ (List.mem_singleton_self _)
    by_contra hc'
    simp [countsZeroOf, hc'] at h1
  -- The opened transcript's reads.
  have hpre : ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3]).length = (flockSound3_of tx hw).prog.rounds.length + 3 := by
    simp [hGl]
  have hr0 : (rd (openedOf (flockSound3_of tx hw).prog.rounds.length c1 c2
      ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs)) 0).2 = [cc, bb, gg] := by
    rw [rd_openedOf _ _ _ _ 0 (by simp)]
    simp
  have hr2 : (rd (openedOf (flockSound3_of tx hw).prog.rounds.length c1 c2
      ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs)) ((flockSound3_of tx hw).prog.rounds.length + 1)).2 = x2.2 := by
    rw [rd_openedOf _ _ _ _ _ (by simp [hGl])]
    simp [List.getElem_append_right, hGl]
  have hr3 : rd (openedOf (flockSound3_of tx hw).prog.rounds.length c1 c2
      ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs)) ((flockSound3_of tx hw).prog.rounds.length + 2) =
      ((none, x3.1.2), x3.2) := by
    rw [rd_openedOf _ _ _ _ _ (by simp [hGl])]
    simp [List.getElem_append_right, hGl]
  have hfd : fdOf (flockSound3_of tx hw).prog.rounds.length (openedOf (flockSound3_of tx hw).prog.rounds.length c1 c2
      ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs)) = G := by
    rw [fdOf_openedOf]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_one, List.tail_cons]
    rw [List.take_left' hGl]
    exact doneFits_noRoot_eq _ _ (flockSound3_of tx hw).rounds_root hG
  rw [hr0, hfd, hr2, hr3, brOf_openedOf _ _ _ _ _ hpre]
  -- The pending claim: Flock's zeros are among the program's, and the walk.
  have hzv : (flockSound3_of tx hw).prog.ZerosVanish G [] := by
    have e : [(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs = (m0, [cc, bb, gg]) :: (G ++ x2 :: (x3 :: brs)) := by
      simp
    have hz1 := hz.1
    rw [e] at hz1
    refine zerosVanish_flock _ _ (m0, [cc, bb, gg]) x2 G (x3 :: brs) hGl (fun e msg he => ?_) (fun msg => ?_) hz1
    · exact (congrFun (withHead_zeros_ne (main3Prog0 D (flockSound3_of tx hw) np s.1 s.2) [countsZeroOf D s.2]
        (List.cons_ne_nil (m0, [cc, bb, gg]) e)) msg).trans (zeros3_flock _ _ e msg he)
    · exact (congrFun (withHead_zeros_ne (main3Prog0 D (flockSound3_of tx hw) np s.1 s.2) [countsZeroOf D s.2]
        (List.cons_ne_nil (m0, [cc, bb, gg]) G)) msg).trans (zeros3_c2 _ _ G hGl msg)
  refine ⟨(flockSound3_of tx hw).walk G [] hG hzv, ?_⟩
  by_cases hzb : ((ids3Of D N h d n g tx hw np hV).zb G).eval (x2.2.headD 0) = 0
  · exact Or.inl hzb
  refine Or.inr ?_
  -- The program's zeros and result at this transcript.
  have e : [(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs = [(m0, [cc, bb, gg])] ++ G ++ [x2] ++ [x3] ++ brs := by
    simp
  rw [e] at hz hc
  have hz' := hz.2
  simp only [main3Prog, ChainProg.withHead, main3Prog0, decode_r0, decode_fd _ _ _ _ _ _ hGl,
    decode_r2 _ _ _ _ _ _ hGl, decode_r3 _ _ _ _ _ _ hGl, decode_brs _ _ _ _ _ _ hGl] at hz' hc
  obtain ⟨bs, hb1, hb2⟩ := main3Out_aligned D tx hw s m0 cc bb gg G x2 x3 brs tl hG
  rw [hb1] at hz'
  have hc1 := hc.1
  rw [hb2] at hc1
  -- Flock's result is the main line's.
  have hGm := doneFits_expandFd (κ := D.shape.heights.getD opBlake2s 0) hG
  have hgood := flockGood (D.shape.heights.getD opBlake2s 0) (batchVars D.shape) (batchVars_ge D.shape) _ hGm
  have hg : CountsFit D.shape s.2 ∧ FlockGood (D.shape.heights.getD opBlake2s 0) (batchVars D.shape)
      ((flockSoundInstance (D.shape.heights.getD opBlake2s 0)).prog.out
        (expandFd (D.shape.heights.getD opBlake2s 0) G) []) := ⟨hcf, hgood⟩
  have hnp : varsOf (layoutsOf D.shape) / 2 = np := by
    show batchVars D.shape / 2 = np
    omega
  -- The batch's last state.
  change BatchState3 cantorBeta1 narrowE
    (prod3Of D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s c1 (expandCh [cc, bb, gg])
      (expandFd (D.shape.heights.getD opBlake2s 0) G) c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0))
    (target3Of D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s c1 (expandCh [cc, bb, gg])
      (expandFd (D.shape.heights.getD opBlake2s 0) G) c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0))
    (roundsOf brs)
  have hBS := batchState3_full_np
    (prod3Of D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s c1 (expandCh [cc, bb, gg])
      (expandFd (D.shape.heights.getD opBlake2s 0) G) c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0))
    np cantorBeta1 narrowE
    (target3Of D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s c1 (expandCh [cc, bb, gg])
      (expandFd (D.shape.heights.getD opBlake2s 0) G) c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0))
    (roundsOf brs) (by rw [prod3Of_vars, hV]) (by simp [roundsOf, hbl])
  have hrl := hBS.1
  rw [prod3Of_vars] at hrl
  rw [hBS.2]
  unfold prod3Of target3Of
  rw [ite_eq_left hg, ite_eq_left hg]
  dsimp only
  have htg : ∑ k ∈ range 3, x3.2.getD 1 0 ^ k *
      (combAt D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s (expandCh [cc, bb, gg])
        (expandFd (D.shape.heights.getD opBlake2s 0) G) (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (cm k)).value =
      (batchTarget (commitments.map fun c => (c, combAt D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s
        (expandCh [cc, bb, gg]) (expandFd (D.shape.heights.getD opBlake2s 0) G) (x2.2.headD 0) x3.1.2
        (x3.2.headD 0) c)) (x3.2.getD 1 0)).1 :=
    (batchTarget_commitments _ _).symm
  rw [htg]
  obtain ⟨hcl1, hcl2⟩ := runClaims_eq D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s
    (expandCh [cc, bb, gg]) (expandFd (D.shape.heights.getD opBlake2s 0) G) (x2.2.headD 0) x3.1.2 (x3.2.headD 0)
    (by simp [expandCh])
  refine terminal3 _ (layoutsOf D.shape) bs _ (x3.2.getD 1 0) brs tl (stackFor D c1 c2) np hnp htl hrl hz'
    (fun o ho pt v bs' hob => ?_) (fun c => ?_)
  · have h1 := hc1 o ho pt v bs' hob
    rwa [claimVars D hsmall] at h1
  · have key := hW s (expandCh [cc, bb, gg]) (expandFd (D.shape.heights.getD opBlake2s 0) G) (x2.2.headD 0) x3.1.2
      (x3.2.headD 0) (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) hcf hGm rfl hvl hzb hrl
      (c, combAt D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s (expandCh [cc, bb, gg])
        (expandFd (D.shape.heights.getD opBlake2s 0) G) (x2.2.headD 0) x3.1.2 (x3.2.headD 0) c)
      (by rw [hcl1]; exact List.mem_map_of_mem (by cases c <;> simp [commitments]))
    rw [hcl2] at key
    show foldAll (fun u => weightAt (combAt D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s
        (expandCh [cc, bb, gg]) (expandFd (D.shape.heights.getD opBlake2s 0) G) (x2.2.headD 0) x3.1.2 (x3.2.headD 0) c)
        (layoutOf (layoutsOf D.shape) c) (bitsE u (varsOf (layoutsOf D.shape)))
        (ringMapAt (flockSoundInstance (D.shape.heights.getD opBlake2s 0))
          (expandFd (D.shape.heights.getD opBlake2s 0) G))) (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0 =
      weightAt (combAt D (flockSoundInstance (D.shape.heights.getD opBlake2s 0)) s
        (expandCh [cc, bb, gg]) (expandFd (D.shape.heights.getD opBlake2s 0) G) (x2.2.headD 0) x3.1.2 (x3.2.headD 0) c)
        (layoutOf (layoutsOf D.shape) c) (pointAfter3 cantorBeta1 narrowE np (roundsOf brs))
        (ringMapAt (flockSoundInstance (D.shape.heights.getD opBlake2s 0))
          (expandFd (D.shape.heights.getD opBlake2s 0) G))
    dsimp only at key
    exact key

end UniSound

/-- info: 'UniSound.uniFinal3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniFinal3

/-- info: 'UniSound.terminal3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.terminal3
