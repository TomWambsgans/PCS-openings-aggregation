-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proof follows `Flock.lean`'s `flock_front`.
import FlockSound.Flock
import FlockSound.Kronecker

/-!
# Flock's front with the zerocheck's coordinates as squares (π1-rec3)

π1-rec3 draws the zerocheck point's `ns` sampled coordinates as `c, c², c⁴, …` of **one** challenge `c`
(`sqPt ns c`). Flock's front (`Flock.lean`'s `flock_front`) holds with the point's bad event replaced by the
Kronecker one (`kronBad`, at most `2^ns − 1` values of `c`, `Kronecker.lean`):

* `Front.BadSq C R Z c`: `c ∈ kronBad ns …` (the residual's sampled tables vanish at `sqPt ns c`), or one of
  `Front.Bad`'s other events (the skip's `z`, a zerocheck round's, `α`, a lincheck round's, a ring stage's);
* **`flock_front_sq`**: if the R1CS fails, the zerocheck and lincheck rounds are consistent, the ring claim holds and
  `R.τs = sqPt ns c`, then a challenge is bad (`BadSq`) or the matrices' product-sum claim `matClaim` is false;
* **`flock_sound_walked`**: with the product-sum claim **true** (π1-rec3's walk checks it exactly, so no matrices'
  rounds follow), the R1CS holds or a challenge is bad.
-/

namespace FlockSound

open Polynomial Finset

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F] {k l m κ f₀ ns : ℕ}

namespace Front

variable (C : Setup F k l m κ f₀ ns) (R : Front F k l m κ ns C.sh.length)
  (Z : Cube (k + l) → Cube m → Cube κ → F)

/-- **The bad challenges with the zerocheck's squares**: `c` in the Kronecker bad set, or one of `Front.Bad`'s other
events. -/
def BadSq (c : F) : Prop :=
  c ∈ kronBad ns (sampledTables C.hsize C.fixed (zRes C Z)) ∨
    R.z ∈ skipBad C.node (zA C Z) (zB C Z) (zZ Z) (τ C R) R.cv ∨
    (∃ j, R.zχ j ∈ zcBad C.node (zA C Z) (zB C Z) (zZ Z) (pinTab Z C.cpos) (τ C R) R.z (c₀ C R)
      R.zq R.zχ j) ∨
    R.α ∈ alphaBad R.va R.vb (vc C R) (skipVal C.node (zA C Z) R.z R.zχ)
      (skipVal C.node (zB C Z) R.z R.zχ) (skipVal C.node (zZ Z) R.z R.zχ)
      (zhat Z (rt C R) C.cpos) ∨
    (∃ j, R.lχ j ∈ sumBad 2 m (fun _ ↦ none)
      (linRev (linFun C.A C.B Z C.cpos C.node R.z (rl C R) (rh C R) (rt C R) R.α)) R.lq R.lχ j) ∨
    (∃ j, R.f j ∈ ringBad univ C.w C.sh (fun cy ↦ R.s cy - strue Z (rt C R) (χ' C R) cy) R.f j)

end Front

/-- **Flock's front's soundness with the zerocheck's squares**: a failing R1CS, consistent zerocheck and lincheck
rounds, a true ring claim on the packed column, and the sampled coordinates the squares of `c`, leave a bad
challenge or a false product-sum claim. -/
theorem flock_front_sq (C : Setup F k l m κ f₀ ns) (hC : C.Valid)
    (Z : Cube (k + l) → Cube m → Cube κ → F) (hZ : ∀ y c t, Z y c t = 0 ∨ Z y c t = 1)
    (Q : Cube (m + κ) → F) (hpack : ∀ u, Q u = ∑ cy, C.w cy * wordBits Z cy u)
    (R : Front F k l m κ ns C.sh.length) (c : F) (hτs : R.τs = sqPt ns c)
    (hzc : Consistent 2 (fun i ↦ some (Front.τ C R i)) (Front.c₀ C R) R.zq R.zχ)
    (hlin : Consistent 2 (fun _ ↦ none) (Front.linC₀ C R) R.lq R.lχ)
    (hring : ∑ u, stagedMap C.sh R.f (eqP (Front.p C R) u) * Q u = Front.target C R)
    (hnot : ¬ R1CSHolds C.A C.B Z C.cpos) :
    Front.BadSq C R Z c ∨
      Front.matClaim C R ≠ ∑ cy, matPart C.A C.B C.node R.z (Front.rl C R) (Front.rh C R) (Front.χ' C R)
        R.α cy * R.s cy := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hgood, hmat⟩ := hcon
  rw [not_not] at hmat
  unfold Front.BadSq at hgood
  simp only [not_or, not_exists] at hgood
  obtain ⟨hτ, hz, hχ, hα, hl, hf⟩ := hgood
  have hτ' : Front.τ C R = fullPoint C.hsize C.fixed (sqPt ns c) := by
    rw [Front.τ, hτs]
  have hpt : R.zχ = Fin.append (Fin.append (Front.rl C R) (Front.rh C R)) (Front.rt C R) := by
    simp only [Front.rl, Front.rh, Front.rt, append_lowPart_highPart]
  have hend : claimAt (Front.c₀ C R) R.zq R.zχ (Fin.last _) = R.va * R.vb + Front.vc C R := by
    unfold Front.vc Front.running
    rw [add_left_comm (R.va * R.vb), CharTwo.add_self_eq_zero, add_zero]
  rw [hτ'] at hzc hz hχ
  have hzero := zerocheck_sound_sq C.hsize hC.node_injective hC.fixed (Front.zA C Z) (Front.zB C Z)
    (Front.zZ Z) (pinTab Z C.cpos) (zc_bool C.A C.B hZ) c R.cv R.z R.zq R.zχ R.va R.vb
    (Front.vc C R) hzc hend (r1cs_doom hnot) hτ hz hχ
  rw [mle_pinTab] at hzero
  have hne : ¬ (R.va = skipVal C.node (Front.zA C Z) R.z R.zχ ∧
      R.vb = skipVal C.node (Front.zB C Z) R.z R.zχ ∧
      Front.vc C R = skipVal C.node (Front.zZ Z) R.z R.zχ ∧ zhat Z (Front.rt C R) C.cpos = 1) := by
    rintro ⟨h1, h2, h3, h4⟩
    rcases hzero with h | h
    · exact h ⟨h1, h2, h3⟩
    · exact h (by rw [show highPart R.zχ = Front.rt C R from rfl, h4, sub_self])
  rw [hpt] at hne hα
  have hlc := lincheck_sound C.A C.B Z C.cpos C.node R.z (Front.rl C R) (Front.rh C R) (Front.rt C R)
    hne hα R.lq R.lχ hlin hl
  rw [linFun_eq_colW, sum_colW] at hlc
  have hs : R.s = strue Z (Front.rt C R) (fun j ↦ R.lχ (Fin.rev j)) := by
    refine ring_sound C.sh R.f C.w C.twists hC.ring_injective hC.twists_covered _ _ ?_ hf
    rw [← Front.target, ← hring, ringClaim_eq C.sh R.f C.w Z hZ Q hpack]
    exact Finset.sum_congr rfl fun cy _ ↦ by rw [strue_eq]; rfl
  rw [← hs] at hlc
  exact add_ne_of_ne hlc hmat

/-- **Flock's soundness, π1-rec3** (`verify_walked`: the lincheck's terminal walked, so the product-sum claim is
checked exactly): if the rounds are consistent, the ring claim holds, the sampled coordinates are the squares of `c`
and the product-sum claim is true, the R1CS holds or a challenge is bad. -/
theorem flock_sound_walked (C : Setup F k l m κ f₀ ns) (hC : C.Valid)
    (Z : Cube (k + l) → Cube m → Cube κ → F) (hZ : ∀ y c t, Z y c t = 0 ∨ Z y c t = 1)
    (Q : Cube (m + κ) → F) (hpack : ∀ u, Q u = ∑ cy, C.w cy * wordBits Z cy u)
    (R : Front F k l m κ ns C.sh.length) (c : F) (hτs : R.τs = sqPt ns c)
    (hzc : Consistent 2 (fun i ↦ some (Front.τ C R i)) (Front.c₀ C R) R.zq R.zχ)
    (hlin : Consistent 2 (fun _ ↦ none) (Front.linC₀ C R) R.lq R.lχ)
    (hring : ∑ u, stagedMap C.sh R.f (eqP (Front.p C R) u) * Q u = Front.target C R)
    (hmat : Front.matClaim C R = ∑ cy, matPart C.A C.B C.node R.z (Front.rl C R) (Front.rh C R)
      (Front.χ' C R) R.α cy * R.s cy) :
    R1CSHolds C.A C.B Z C.cpos ∨ Front.BadSq C R Z c := by
  by_cases hold : R1CSHolds C.A C.B Z C.cpos
  · exact Or.inl hold
  rcases flock_front_sq C hC Z hZ Q hpack R c hτs hzc hlin hring hold with hbad | hfalse
  · exact Or.inr hbad
  · exact absurd hmat hfalse

end FlockSound

/-- info: 'FlockSound.flock_front_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.flock_front_sq

/-- info: 'FlockSound.flock_sound_walked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.flock_sound_walked
