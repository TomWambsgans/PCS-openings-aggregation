-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.RingSwitch

/-!
# Flock's soundness, generic: its checks and claims give the R1CS, but for bad challenges

Flock's verifier (`flock_min::verify` with the slices sent) at any sizes: `k` skipped packing bits,
`l` other packing bits, `m` slot bits (the lincheck's rounds), `κ` batch bits, `f₀` fixed
coordinates of the zerocheck point and `ns` sampled ones, the ring map's shifts `sh` in any order.

**The constants** (`Setup`): the R1CS (`A`, `B`, the constant position), the skip's nodes, the
fixed coordinates, the ring map's shifts and the packing weights `w(cy) = x^cy`. They must satisfy
(`Setup.Valid`) injective nodes, `F_2`-independent fixed weights, and ring-switching injectivity on
twists the shifts cover: the facts `Fields.lean` proves for leanVM's constants.

**The run** (`Front`): every value the verifier reads or draws up to the slices and the ring map,
in the transcript's order: `τ` (sampled), the skip's coset values, `z`, the zerocheck's rounds and
challenges, `v_a`, `v_b`, `α`, the lincheck's rounds and challenges, the slices, the ring map's
challenges. What the verifier derives from it (`Front.c₀`, `vc`, `rlc`, `χ'`, `p`, `target`,
`known`, `matClaim`) is as `flock_min` computes it, in characteristic two.

**The bad challenges** (`Front.Bad`), each a function of the run before it: a sampled coordinate
of `τ` (`1` value each), `z` (`2^(k+1) - 1`), a zerocheck round's (`2`), `α` (`3`), a lincheck
round's (`2`), a ring-map stage's (`1`).

* **`flock_front`**: if the R1CS fails (`R1CSHolds`), the zerocheck and lincheck rounds are
  consistent and the ring claim holds of the committed column, then a challenge is bad or the
  matrices' product-sum claim `matClaim` is false. Where the product sum is then proved is
  separate:
* **`flock_sound_v1`** (milestone 1, `reduce_terminal` with the slices): its own `k + (k + l)`
  rounds, the terminal check, true `a`, `b`: the R1CS holds or a challenge is bad;
* iteration 2 (lever 4a) proves it as one component of the batching sumcheck
  (`Matrices.batched_sound`), its claim `matClaim`, its terminal `(a + αb) L̂(ρ) ŝ(σ) eq(r_rest, 0)`.
-/

namespace FlockSound

open Polynomial Finset

/-- **Flock's constants.** -/
structure Setup (F : Type*) [Field F] (k l m κ f₀ ns : ℕ) where
  A : Pos k l m → Pos k l m → Bool
  B : Pos k l m → Pos k l m → Bool
  cpos : Pos k l m
  node : Bool × Cube k → F
  fixed : Fin f₀ → F
  hsize : l + m + κ = f₀ + ns
  sh : List ℕ
  w : Cube (k + l) → F
  twists : Finset ℕ

/-- **The constants' facts** Flock's soundness needs. -/
structure Setup.Valid {F : Type*} [Field F] {k l m κ f₀ ns : ℕ} (C : Setup F k l m κ f₀ ns) : Prop where
  node_injective : Function.Injective C.node
  fixed : HFixed C.fixed
  ring_injective : ∀ δ : Cube (k + l) → F, (∀ j ∈ C.twists, frobPair univ C.w δ j = 0) → δ = 0
  twists_covered : C.twists ⊆ rel C.sh

/-- **Flock's run up to the slices and the ring map**, in the transcript's order. -/
structure Front (F : Type*) [Field F] (k l m κ ns S : ℕ) where
  τs : Fin ns → F
  cv : Cube k → F
  z : F
  zq : Fin (l + m + κ) → F[X]
  zχ : Fin (l + m + κ) → F
  va : F
  vb : F
  α : F
  lq : Fin m → F[X]
  lχ : Fin m → F
  s : Cube (k + l) → F
  f : Fin S → F

namespace Front

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F] {k l m κ f₀ ns : ℕ}
  (C : Setup F k l m κ f₀ ns) (R : Front F k l m κ ns C.sh.length)

/-- The zerocheck point: the fixed coordinates, then the sampled. -/
def τ : Fin (l + m + κ) → F := fullPoint C.hsize C.fixed R.τs

/-- The zerocheck's starting claim: the interpolant of zeros and the coset values at `z`. -/
noncomputable def c₀ : F := (interp C.node R.cv).eval R.z

/-- The zerocheck's last claim. -/
noncomputable def running : F := claimAt (c₀ C R) R.zq R.zχ (Fin.last _)

/-- `v_c = running + v_a v_b`. -/
noncomputable def vc : F := running C R + R.va * R.vb

/-- The row point's low packing bits, slot bits, and the batch point. -/
def rl : Fin l → F := lowPart (lowPart R.zχ)
def rh : Fin m → F := highPart (lowPart R.zχ)
def rt : Fin κ → F := highPart R.zχ

/-- The lincheck's starting claim `v_a + α v_b + α² v_c + α³`. -/
noncomputable def linC₀ : F := R.va + R.α * R.vb + R.α ^ 2 * vc C R + R.α ^ 3

/-- The lincheck's terminal `r_lc`. -/
noncomputable def rlc : F := claimAt (linC₀ C R) R.lq R.lχ (Fin.last m)

/-- The lincheck's point, its challenges reversed (`chi_in_prime`). -/
def χ' : Fin m → F := fun j ↦ R.lχ (Fin.rev j)

/-- The point of the words: `(χ', χ_rest)`. -/
def p : Fin (m + κ) → F := Fin.append (χ' C R) (rt C R)

/-- The ring switch's target `Σ_cy x^cy Φ(s_cy)`. -/
def target : F := ∑ cy, C.w cy * stagedMap C.sh R.f (R.s cy)

/-- The terminal's two known terms (`reduce_terminal`'s `known`). -/
noncomputable def known (x : Cube (k + l) → F) : F :=
  R.α ^ 2 * eqEval (rh C R) (χ' C R) * ∑ cy, lowW C.node R.z (rl C R) cy * x cy +
    R.α ^ 3 * eqP (χ' C R) C.cpos.2 * x C.cpos.1

/-- **The matrices' product-sum claim**: `r_lc + known`. -/
noncomputable def matClaim : F := rlc C R + known C R R.s

section Witness

variable (Z : Cube (k + l) → Cube m → Cube κ → F)

/-- The zerocheck's tables of the witness. -/
def zA : Cube k → Cube (l + m + κ) → F := zcTab (rowProd C.A Z)
def zB : Cube k → Cube (l + m + κ) → F := zcTab (rowProd C.B Z)
def zZ : Cube k → Cube (l + m + κ) → F := zcTab fun r t ↦ Z r.1 r.2 t
def zRes : Cube k → Cube (l + m + κ) → F := fun i x ↦ zA C Z i x * zB C Z i x + zZ Z i x

/-- **The bad challenges**, each a function of the run before it. -/
def Bad : Prop :=
  (∃ j, R.τs j ∈ pointBad ns (sampledTables C.hsize C.fixed (zRes C Z)) R.τs j) ∨
    R.z ∈ skipBad C.node (zA C Z) (zB C Z) (zZ Z) (τ C R) R.cv ∨
    (∃ j, R.zχ j ∈ zcBad C.node (zA C Z) (zB C Z) (zZ Z) (pinTab Z C.cpos) (τ C R) R.z (c₀ C R)
      R.zq R.zχ j) ∨
    R.α ∈ alphaBad R.va R.vb (vc C R) (skipVal C.node (zA C Z) R.z R.zχ)
      (skipVal C.node (zB C Z) R.z R.zχ) (skipVal C.node (zZ Z) R.z R.zχ)
      (zhat Z (rt C R) C.cpos) ∨
    (∃ j, R.lχ j ∈ sumBad 2 m (fun _ ↦ none)
      (linRev (linFun C.A C.B Z C.cpos C.node R.z (rl C R) (rh C R) (rt C R) R.α)) R.lq R.lχ j) ∨
    (∃ j, R.f j ∈ ringBad univ C.w C.sh (fun cy ↦ R.s cy - strue Z (rt C R) (χ' C R) cy) R.f j)

end Witness

end Front

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F] {k l m κ f₀ ns : ℕ}

theorem mle_pinTab (Z : Cube (k + l) → Cube m → Cube κ → F) (cpos : Pos k l m)
    (x : Fin (l + m + κ) → F) : mle (pinTab Z cpos) x = zhat Z (highPart x) cpos - 1 := by
  have e : pinTab Z cpos = fun c ↦ (fun t ↦ Z cpos.1 cpos.2 t) (highPart c) - 1 := rfl
  rw [e, mle_sub, mle_const, mle_split]
  congr 1
  rw [zhat]
  simp only [highPart_append, mle_const]

theorem sum_colW (A B : Pos k l m → Pos k l m → Bool) (cpos : Pos k l m) (node : Bool × Cube k → F)
    (z : F) (rl : Fin l → F) (rh : Fin m → F) (χ' : Fin m → F) (α : F) (x : Cube (k + l) → F) :
    ∑ cy, colW A B cpos node z rl rh χ' α cy * x cy =
      ∑ cy, matPart A B node z rl rh χ' α cy * x cy +
        (α ^ 2 * eqEval rh χ' * ∑ cy, lowW node z rl cy * x cy + α ^ 3 * eqP χ' cpos.2 * x cpos.1) := by
  simp only [colW_eq, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  have hpin : ∑ cy : Cube (k + l), α ^ 3 * (if cy = cpos.1 then eqP χ' cpos.2 else 0) * x cy =
      α ^ 3 * eqP χ' cpos.2 * x cpos.1 := by
    rw [Finset.sum_eq_single cpos.1]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hpin, add_assoc]
  congr 2
  exact Finset.sum_congr rfl fun cy _ ↦ by ring

theorem add_ne_of_ne {a b c : F} (h : a ≠ b + c) : a + c ≠ b := by
  intro h'
  apply h
  rw [← h', add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **Flock's front's soundness**: a failing R1CS, consistent zerocheck and lincheck rounds and a
true ring claim on the packed column leave a bad challenge or a false product-sum claim. -/
theorem flock_front (C : Setup F k l m κ f₀ ns) (hC : C.Valid)
    (Z : Cube (k + l) → Cube m → Cube κ → F) (hZ : ∀ y c t, Z y c t = 0 ∨ Z y c t = 1)
    (Q : Cube (m + κ) → F) (hpack : ∀ u, Q u = ∑ cy, C.w cy * wordBits Z cy u)
    (R : Front F k l m κ ns C.sh.length)
    (hzc : Consistent 2 (fun i ↦ some (Front.τ C R i)) (Front.c₀ C R) R.zq R.zχ)
    (hlin : Consistent 2 (fun _ ↦ none) (Front.linC₀ C R) R.lq R.lχ)
    (hring : ∑ u, stagedMap C.sh R.f (eqP (Front.p C R) u) * Q u = Front.target C R)
    (hnot : ¬ R1CSHolds C.A C.B Z C.cpos) :
    Front.Bad C R Z ∨
      Front.matClaim C R ≠ ∑ cy, matPart C.A C.B C.node R.z (Front.rl C R) (Front.rh C R) (Front.χ' C R)
        R.α cy * R.s cy := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hgood, hmat⟩ := hcon
  rw [not_not] at hmat
  unfold Front.Bad at hgood
  simp only [not_or, not_exists] at hgood
  obtain ⟨hτ, hz, hχ, hα, hl, hf⟩ := hgood
  -- The zerocheck.
  have hpt : R.zχ = Fin.append (Fin.append (Front.rl C R) (Front.rh C R)) (Front.rt C R) := by
    simp only [Front.rl, Front.rh, Front.rt, append_lowPart_highPart]
  have hend : claimAt (Front.c₀ C R) R.zq R.zχ (Fin.last _) = R.va * R.vb + Front.vc C R := by
    unfold Front.vc Front.running
    rw [add_left_comm (R.va * R.vb), CharTwo.add_self_eq_zero, add_zero]
  have hzero := zerocheck_sound C.hsize hC.node_injective hC.fixed (Front.zA C Z) (Front.zB C Z)
    (Front.zZ Z) (pinTab Z C.cpos) (zc_bool C.A C.B hZ) R.τs R.cv R.z R.zq R.zχ R.va R.vb
    (Front.vc C R) hzc hend (r1cs_doom hnot) hτ hz hχ
  rw [mle_pinTab] at hzero
  have hne : ¬ (R.va = skipVal C.node (Front.zA C Z) R.z R.zχ ∧
      R.vb = skipVal C.node (Front.zB C Z) R.z R.zχ ∧
      Front.vc C R = skipVal C.node (Front.zZ Z) R.z R.zχ ∧ zhat Z (Front.rt C R) C.cpos = 1) := by
    rintro ⟨h1, h2, h3, h4⟩
    rcases hzero with h | h
    · exact h ⟨h1, h2, h3⟩
    · exact h (by rw [show highPart R.zχ = Front.rt C R from rfl, h4, sub_self])
  -- The lincheck.
  rw [hpt] at hne hα
  have hlc := lincheck_sound C.A C.B Z C.cpos C.node R.z (Front.rl C R) (Front.rh C R) (Front.rt C R)
    hne hα R.lq R.lχ hlin hl
  rw [linFun_eq_colW, sum_colW] at hlc
  -- The ring switch: the sent slices are the true ones.
  have hs : R.s = strue Z (Front.rt C R) (fun j ↦ R.lχ (Fin.rev j)) := by
    refine ring_sound C.sh R.f C.w C.twists hC.ring_injective hC.twists_covered _ _ ?_ hf
    rw [← Front.target, ← hring, ringClaim_eq C.sh R.f C.w Z hZ Q hpack]
    exact Finset.sum_congr rfl fun cy _ ↦ by rw [strue_eq]; rfl
  rw [← hs] at hlc
  exact add_ne_of_ne hlc hmat

/-- **Flock's soundness, milestone 1** (`flock_min::verify` with the slices sent: the matrices'
reduction in its own `k + (k + l)` rounds, `reduce_terminal`'s check `factor · ŝ(σ) + running = 0`
with `factor = (a + α b) L̂(ρ)`): if the rounds are consistent, the check holds and the claims on
`q_flock` (the ring claim), `A0` and `B0` (`a`, `b`) are true, the R1CS holds or a challenge is
bad. -/
theorem flock_sound_v1 (C : Setup F k l m κ f₀ ns) (hC : C.Valid)
    (Z : Cube (k + l) → Cube m → Cube κ → F) (hZ : ∀ y c t, Z y c t = 0 ∨ Z y c t = 1)
    (Q : Cube (m + κ) → F) (hpack : ∀ u, Q u = ∑ cy, C.w cy * wordBits Z cy u)
    (R : Front F k l m κ ns C.sh.length) (mq : Fin (k + (k + l)) → F[X])
    (mχ : Fin (k + (k + l)) → F) (a b : F)
    (hzc : Consistent 2 (fun i ↦ some (Front.τ C R i)) (Front.c₀ C R) R.zq R.zχ)
    (hlin : Consistent 2 (fun _ ↦ none) (Front.linC₀ C R) R.lq R.lχ)
    (hmat : Consistent 2 (fun _ ↦ none) (Front.matClaim C R) mq mχ)
    (hcheck : claimAt (Front.matClaim C R) mq mχ (Fin.last _) =
      (a + R.α * b) * mle (fun bx ↦ (lag C.node bx).eval R.z) (lowPart mχ) * mle R.s (highPart mχ))
    (ha : a = matMle (Front.rl C R) (Front.rh C R) (Front.χ' C R) C.A (lowPart mχ) (highPart mχ))
    (hb : b = matMle (Front.rl C R) (Front.rh C R) (Front.χ' C R) C.B (lowPart mχ) (highPart mχ))
    (hring : ∑ u, stagedMap C.sh R.f (eqP (Front.p C R) u) * Q u = Front.target C R) :
    R1CSHolds C.A C.B Z C.cpos ∨ Front.Bad C R Z ∨
      ∃ j, mχ j ∈ sumBad 2 _ (fun _ ↦ none)
        (matFun C.A C.B C.node R.z (Front.rl C R) (Front.rh C R) (Front.χ' C R) R.s R.α) mq mχ j := by
  by_cases hold : R1CSHolds C.A C.B Z C.cpos
  · exact Or.inl hold
  rcases flock_front C hC Z hZ Q hpack R hzc hlin hring hold with hbad | hfalse
  · exact Or.inr (Or.inl hbad)
  · exact Or.inr (Or.inr (matrices_sound C.A C.B C.node R.z _ _ _ R.s R.α _ a b mq mχ hmat hfalse
      hcheck ha hb))

/-- **Flock's soundness, iteration 2** (lever 4a): the product sum is component `iM` of a
`λ`-combined sumcheck over `n = k + (k + l) + e` variables, zero-extended (`extFun`), its claim
`matClaim`, its terminal `(a + α b) L̂(ρ) ŝ(σ) eq(r_rest, 0)`. If every component's terminal claim
is true (the other components' are the stacks' claims), the R1CS holds or a challenge is bad. -/
theorem flock_sound_merged (C : Setup F k l m κ f₀ ns) (hC : C.Valid)
    (Z : Cube (k + l) → Cube m → Cube κ → F) (hZ : ∀ y c t, Z y c t = 0 ∨ Z y c t = 1)
    (Q : Cube (m + κ) → F) (hpack : ∀ u, Q u = ∑ cy, C.w cy * wordBits Z cy u)
    (R : Front F k l m κ ns C.sh.length) {K e d : ℕ} (iM : Fin K)
    (Φ : Fin K → (Fin (k + (k + l) + e) → F) → F) (hΦ : ∀ i, IndDeg (Φ i) d)
    (hΦM : Φ iM = extFun (lsTab C.node R.z R.s)
      (gTab C.A C.B (Front.rl C R) (Front.rh C R) (Front.χ' C R) R.α))
    (c v : Fin K → F) (hcM : c iM = Front.matClaim C R) (lam : F)
    (bq : Fin (k + (k + l) + e) → F[X]) (bχ : Fin (k + (k + l) + e) → F) (a b : F)
    (hzc : Consistent 2 (fun i ↦ some (Front.τ C R i)) (Front.c₀ C R) R.zq R.zχ)
    (hlin : Consistent 2 (fun _ ↦ none) (Front.linC₀ C R) R.lq R.lχ)
    (hbatch : Consistent d (fun _ ↦ none) (∑ i : Fin K, lam ^ (i : ℕ) * c i) bq bχ)
    (hend : claimAt (∑ i : Fin K, lam ^ (i : ℕ) * c i) bq bχ (Fin.last _) =
      ∑ i : Fin K, lam ^ (i : ℕ) * v i)
    (hvM : v iM = (a + R.α * b) * mle (fun bx ↦ (lag C.node bx).eval R.z) (lowPart (lowPart bχ)) *
      mle R.s (highPart (lowPart bχ)) * eqP (highPart bχ) (fun _ ↦ false))
    (hv : ∀ i, i ≠ iM → v i = Φ i bχ)
    (ha : a = matMle (Front.rl C R) (Front.rh C R) (Front.χ' C R) C.A (lowPart (lowPart bχ))
      (highPart (lowPart bχ)))
    (hb : b = matMle (Front.rl C R) (Front.rh C R) (Front.χ' C R) C.B (lowPart (lowPart bχ))
      (highPart (lowPart bχ)))
    (hring : ∑ u, stagedMap C.sh R.f (eqP (Front.p C R) u) * Q u = Front.target C R) :
    R1CSHolds C.A C.B Z C.cpos ∨ Front.Bad C R Z ∨
      lam ∈ lambdaBad c (fun i ↦ cubeSum (fun _ ↦ none) (Φ i)) ∨
      ∃ j, bχ j ∈ sumBad d _ (fun _ ↦ none) (fun r ↦ ∑ i : Fin K, lam ^ (i : ℕ) * Φ i r) bq bχ j := by
  by_cases hold : R1CSHolds C.A C.B Z C.cpos
  · exact Or.inl hold
  rcases flock_front C hC Z hZ Q hpack R hzc hlin hring hold with hbad | hfalse
  · exact Or.inr (Or.inl hbad)
  right; right
  refine batched_sound Φ hΦ c v lam bq bχ ⟨iM, ?_⟩ hbatch hend fun i ↦ ?_
  · rw [hcM, hΦM, cubeSum_extFun]
    intro h
    apply hfalse
    rw [h, ← cubeSum_matFun]
    simp only [cubeSum, eqW_none, one_mul, matFun, mle_cube]
  · by_cases hi : i = iM
    · subst hi
      rw [hvM, hΦM, ← append_lowPart_highPart bχ, extFun_append, lowPart_append, highPart_append]
      have := matFun_append C.A C.B C.node R.z (Front.rl C R) (Front.rh C R) (Front.χ' C R) R.s R.α
        (lowPart (lowPart bχ)) (highPart (lowPart bχ))
      rw [append_lowPart_highPart] at this
      simp only [matFun] at this
      rw [this, ha, hb]
      ring
    · exact hv i hi

end FlockSound
