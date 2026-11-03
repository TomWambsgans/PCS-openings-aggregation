-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.CvecOk
import UniSound.Ids.Weights

/-!
# `DiffsFlockP`: the ring-switch relation gives Flock's claim on `q_flock`

The main line's ring-switch relation `⟨[q_flock at p, twist ringTwist], target⟩` is one of `C1`'s
relations (`relsOf`'s `ringRels`); `combine` may merge its point into a longer one, which changes nothing
(`termWExtend`: the ring term reads `vars = 8 + (D.shape.heights.getD opBlake2s 0) = |p|` coordinates). Its weight on the cube is the tower
weight (`ringInner`), which is `Σ_k d_k eq(φ^k(p), ·)` (`TowerWeight`), so its difference is
`Σ_k d_k q̂(φ^k(p)) + target` (`FlockEndHolds`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset

theorem sqn_zero : ∀ k, sqn (0 : E) k = 0
  | 0 => rfl
  | k + 1 => by rw [sqn, mul_zero]; exact sqn_zero k

theorem twist_getD (p : List E) (k n : ℕ) : (twist p k).getD n 0 = sqn (p.getD n 0) k := by
  unfold twist
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases p[n]? with
  | none => simp only [Option.map_none, Option.getD_none]; exact (sqn_zero k).symm
  | some a => rfl

theorem bitsE_getD (x n i : ℕ) (hi : i < n) : (bitsE x n).getD i 0 = if x.testBit i then 1 else 0 := by
  unfold bitsE
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

/-- **The ring-switch relation gives Flock's claim.** -/
theorem diffsFlock (D : Deployment) (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (hr : C1Reading D)
    (hT : TowerWeight) : DiffsFlockP D Fl := by
  intro s c1 ch fd c2 t vals hz
  unfold diffsOf at hz
  split_ifs at hz with hg
  swap
  · exact absurd (hz [1] (List.mem_singleton_self _) 1 (List.mem_singleton_self _)) one_ne_zero
  obtain ⟨⟨map, target, hend⟩, hlen, -⟩ := hg.2
  set fl := Fl.prog.out fd []
  set rels := relsAt D Fl s ch fd t vals
  -- The ring relation is one of C1's.
  have hmem : (⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩ : Relation) ∈ mine rels .c1 := by
    refine List.mem_filter.mpr ⟨?_, rfl⟩
    show (⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩ : Relation) ∈ relsOf (relInput D s ch fl t vals)
    unfold relsOf
    refine List.mem_append_right _ ?_
    show (⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩ : Relation) ∈ (relInput D s ch fl t vals).ringRels
    unfold RelInput.ringRels
    rw [show (relInput D s ch fl t vals).flockEnd = fl.2.1 from rfl, hend]
    exact List.mem_singleton_self _
  have hrm : ringMapAt Fl fd = some map := by
    unfold ringMapAt
    rw [show (Fl.prog.out fd []).2.1 = some (.ring map target) from hend]
  have h0 := hz _ (List.mem_append_left _ (List.mem_map.mpr ⟨.c1, List.mem_cons_self .., rfl⟩)) _
    (List.mem_map_of_mem hmem)
  unfold relDiff at h0
  rw [hrm] at h0
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul] at h0
  -- The merged point changes nothing.
  obtain ⟨off, hl⟩ := hr.limbs.2.2.2.2
  have hext : ∀ u, termW (layoutOf D.shape .c1) (some map) (batchVars D.shape) .qflock (mergedPoint (mine rels .c1) fl.1) ringTwist u =
      termW (layoutOf D.shape .c1) (some map) (batchVars D.shape) .qflock fl.1 ringTwist u := by
    intro u
    refine termWExtend (layoutOf D.shape .c1) (some map) (batchVars D.shape) .qflock fl.1 _ ringTwist u (fun j h ↦ by cases h) ?_ ?_
    · intro b hb
      rw [hl] at hb
      rw [List.mem_singleton.mp hb, hlen]
      simp [add_comm]
    · exact (mergedPrefix (mine rels .c1) fl.1 ⟨(⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩ : Relation), hmem, _, List.mem_singleton_self _, rfl⟩).1
  rw [show stackFor D c1 c2 .c1 = c1 from rfl] at h0
  simp only [hext] at h0
  have hbl := hr.aligned _ (limbs_mem_blocks (b := (0, (D.shape.heights.getD opBlake2s 0) + 8, off)) (by rw [hl]; exact List.mem_singleton_self _))
  have hvV : (D.shape.heights.getD opBlake2s 0) + 8 ≤ (batchVars D.shape) := by
    have h1 := hbl.2
    have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hr.vars
    have h3 : 2 ^ ((D.shape.heights.getD opBlake2s 0) + 8) ≤ 2 ^ (batchVars D.shape) := by simp only at h1; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
  rw [ringInner (layoutOf D.shape .c1) map (batchVars D.shape) c1 fl.1 (fun b hb ↦ by rw [hl] at hb; rw [List.mem_singleton.mp hb]; exact hvV), hl]
    at h0
  have hoff : off < 2 ^ (batchVars D.shape) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hr.vars
    have := Nat.two_pow_pos ((D.shape.heights.getD opBlake2s 0) + 8)
    simp only at hbl
    omega
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, limbScale, ite_true, one_mul,
    blockBase_of_aligned hbl.1 hoff] at h0
  -- The tower weight.
  have htw : ∀ x ∈ range (2 ^ ((D.shape.heights.getD opBlake2s 0) + 8)), Flock.towerWeightAt (fl.1.take ((D.shape.heights.getD opBlake2s 0) + 8))
      ((bitsE x ((D.shape.heights.getD opBlake2s 0) + 8)).map (1 + ·)) map * stE c1 (layoutOf D.shape .c1).vars (off + x) =
      ∑ k ∈ range 64, (Flock.towerCoefficients map).getD k 0 *
        (cubeEq (twist fl.1 k) (8 + (D.shape.heights.getD opBlake2s 0)) x * ofK (c1 (qfOff D + x))) := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [hT _ _ map (by simp [bitsE, hlen]; omega), Finset.sum_mul]
    have hst : stE c1 (layoutOf D.shape .c1).vars (off + x) = ofK (c1 (qfOff D + x)) := by
      have hq : qfOff D = off := by unfold qfOff; rw [c1Layout_eq, hl]; rfl
      rw [hq]
      unfold stE
      rw [ite_eq_left (by simp only at hbl; omega)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hst, mul_assoc]
    refine congrArg (_ * ·) (congrArg (· * ofK (c1 (qfOff D + x))) ?_)
    unfold cubeEq
    rw [show (List.take ((D.shape.heights.getD opBlake2s 0) + 8) fl.1).length = (D.shape.heights.getD opBlake2s 0) + 8 by simp [hlen]; omega, show 8 + (D.shape.heights.getD opBlake2s 0) = (D.shape.heights.getD opBlake2s 0) + 8 by ring]
    refine Finset.prod_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_range] at hn
    rw [bitsE_getD x _ n hn, twist_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left hn, ← List.getD_eq_getElem?_getD]
    ring
  rw [Finset.sum_congr rfl htw, Finset.sum_comm] at h0
  have hmle : ∀ k ∈ range 64, ∑ x ∈ range (2 ^ ((D.shape.heights.getD opBlake2s 0) + 8)),
      (Flock.towerCoefficients map).getD k 0 *
        (cubeEq (twist fl.1 k) (8 + (D.shape.heights.getD opBlake2s 0)) x * ofK (c1 (qfOff D + x))) =
      (Flock.towerCoefficients map).getD k 0 *
        mleE (qfOf D c1 (D.shape.heights.getD opBlake2s 0)) (twist fl.1 k) := by
    intro k _
    rw [← Finset.mul_sum]
    refine congrArg ((Flock.towerCoefficients map).getD k 0 * ·) ?_
    unfold mleE qfOf
    simp only [Vector.get_ofFn]
    rw [show (D.shape.heights.getD opBlake2s 0) + 8 = 8 + (D.shape.heights.getD opBlake2s 0) from
      Nat.add_comm _ _]
    exact (Fin.sum_univ_eq_sum_range (fun x ↦ cubeEq (twist fl.1 k) (8 + (D.shape.heights.getD opBlake2s 0)) x *
      ofK (c1 (qfOff D + x))) _).symm
  rw [Finset.sum_congr rfl hmle] at h0
  show FlockEndHolds (qfOf D c1 (D.shape.heights.getD opBlake2s 0)) fl
  unfold FlockEndHolds
  rw [hend]
  exact CharTwo.add_eq_zero.mp h0

end UniSound.Ids
