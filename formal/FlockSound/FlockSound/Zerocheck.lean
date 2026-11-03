-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Sumcheck
import FlockSound.Point
import FlockSound.Skip
import FlockSound.Split

/-!
# The zerocheck with a univariate skip, a partially fixed point and the constant position

The zerocheck of Flock (`flock_min::zerocheck`), generic: tables `A_i, B_i, Z_i` on the cube
`Cube n'` for each skip index `i : ι`, residuals `R_i = A_i B_i + Z_i`, Boolean (characteristic
two, Boolean witness and matrices). Its point `τ` has `f₀` fixed coordinates then `ns` sampled
ones (`fullPoint`); after the skip (`Skip.lean`) the `n'` rounds are an `eq`-weighted sumcheck of
`zcFun z` (degree `2`), ending in `v_a, v_b, v_c` with `running = v_a v_b + v_c`.

**The constant position** is a second track: a table `pin` on the same cube (in Flock, the
constant wire's bit minus one, a function of the batch coordinates), which the zerocheck's
challenges evaluate; the lincheck reads it. A zerocheck round's challenge is bad
(`zcBad`) as the sumcheck's when its claim is false, as the point lemma's for `pin` when it is
true: at most `2` values either way.

* `point_phase`: with `F_2`-independent fixed weights (`HFixed`) and Boolean residuals, a nonzero
  residual stays nonzero at `τ` unless a sampled coordinate is bad (one value each).
* `zc_rounds`: from a false starting claim or a nonzero `pin`, the last claim is wrong or `pin`
  is nonzero at the challenges, unless a round's challenge is bad.
* **`zerocheck_sound`**: a nonzero residual or a nonzero `pin` leaves the zerocheck's terminal
  values wrong or `pin` nonzero at its challenges, unless one of `ns + 1 + n'` challenges is bad:
  `ns` coordinates of one value each, the skip's `2|ι| - 1`, and `2` for each round.

Nothing here transcribes a source.
-/

namespace FlockSound

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The partially fixed point -/

/-- The zerocheck point: `f₀` fixed coordinates, then `ns` sampled ones. -/
def fullPoint {n' f₀ ns : ℕ} (h : n' = f₀ + ns) (fixed : Fin f₀ → F) (τs : Fin ns → F) :
    Fin n' → F :=
  fun i ↦ Fin.append fixed τs (Fin.cast h i)

/-- The tables on the sampled coordinates: each with its fixed coordinates bound. -/
def sampledTables {n' f₀ ns : ℕ} (h : n' = f₀ + ns) (fixed : Fin f₀ → F) (R : ι → Cube n' → F) :
    ι → Cube ns → F :=
  fun i hb ↦ ∑ v : Cube f₀, eqP fixed v * R i fun j ↦ Fin.append v hb (Fin.cast h j)

theorem mle_fullPoint {n' f₀ ns : ℕ} (h : n' = f₀ + ns) (fixed : Fin f₀ → F) (τs : Fin ns → F)
    (R : ι → Cube n' → F) (i : ι) :
    mle (R i) (fullPoint h fixed τs) = mle (sampledTables h fixed R i) τs := by
  subst h
  have hp : fullPoint rfl fixed τs = Fin.append fixed τs := funext fun j ↦ rfl
  rw [hp, mle_append]
  simp only [sampledTables, mle, Fin.cast_eq_self]
  refine Finset.sum_congr rfl fun hb _ ↦ ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ ↦ by ring

/-- **The fixed coordinates' weights are `F_2`-independent**: a vanishing `0/1` combination of
the `2^f₀` weights `eq(fixed, v)` is zero. -/
def HFixed {f₀ : ℕ} (fixed : Fin f₀ → F) : Prop :=
  ∀ c : Cube f₀ → F, (∀ v, c v = 0 ∨ c v = 1) → ∑ v, eqP fixed v * c v = 0 → ∀ v, c v = 0

theorem sampledTables_ne {n' f₀ ns : ℕ} (h : n' = f₀ + ns) {fixed : Fin f₀ → F}
    (hf : HFixed fixed) {R : ι → Cube n' → F} (hbool : ∀ i b, R i b = 0 ∨ R i b = 1)
    (hne : ∃ i b, R i b ≠ 0) : ∃ i, sampledTables h fixed R i ≠ 0 := by
  obtain ⟨i, b, hb⟩ := hne
  refine ⟨i, fun h0 ↦ ?_⟩
  subst h
  have hb' : b = Fin.append (lowPart b) (highPart b) := (append_lowPart_highPart b).symm
  have := hf (fun v ↦ R i (Fin.append v (highPart b))) (fun v ↦ hbool i _)
    (by simpa [sampledTables] using congrFun h0 (highPart b)) (lowPart b)
  rw [← hb'] at this
  exact hb this

/-- **The point**: Boolean residuals, not all zero, stay so at `τ` unless a sampled coordinate is
bad. -/
theorem point_phase {n' f₀ ns : ℕ} (h : n' = f₀ + ns) {fixed : Fin f₀ → F} (hf : HFixed fixed)
    {R : ι → Cube n' → F} (hbool : ∀ i b, R i b = 0 ∨ R i b = 1) (hne : ∃ i b, R i b ≠ 0)
    {τs : Fin ns → F} (hgood : ∀ j, τs j ∉ pointBad ns (sampledTables h fixed R) τs j) :
    ∃ i, mle (R i) (fullPoint h fixed τs) ≠ 0 := by
  obtain ⟨i, hi⟩ := point_escape ns _ τs (sampledTables_ne h hf hbool hne) hgood
  exact ⟨i, by rwa [mle_fullPoint]⟩

/-! ## The rounds and the constant position -/

/-- **A zerocheck round's bad challenges**: the sumcheck's when the round's claim is false, the
constant position's when it is true. -/
noncomputable def zcBad {n : ℕ} (node : Bool × ι → F) (A B Z : ι → Cube n → F) (pin : Cube n → F)
    (τ : Fin n → F) (z c₀ : F) (q : Fin n → F[X]) (χ : Fin n → F) (j : Fin n) : Finset F :=
  if claimAt c₀ q χ j.castSucc = trueAt n (fun i ↦ some (τ i)) (zcFun node A B Z z) χ j.castSucc then
    pointBad n (fun _ : Unit ↦ pin) χ j
  else sumBad 2 n (fun i ↦ some (τ i)) (zcFun node A B Z z) q χ j

theorem card_zcBad_le {n : ℕ} (node : Bool × ι → F) (A B Z : ι → Cube n → F) (pin : Cube n → F)
    (τ : Fin n → F) (z c₀ : F) (q : Fin n → F[X]) (χ : Fin n → F) (j : Fin n) :
    (zcBad node A B Z pin τ z c₀ q χ j).card ≤ 2 := by
  unfold zcBad
  split_ifs
  · exact (card_pointBad_le n _ χ j).trans (by norm_num)
  · exact card_sumBad_le 2 n _ _ q χ (indDeg_zcFun node A B Z z) j

/-- **The rounds**: from a false starting claim or a nonzero constant-position table, the last
claim is wrong or the table is nonzero at the challenges, unless a round's challenge is bad. -/
theorem zc_rounds {n : ℕ} (node : Bool × ι → F) (A B Z : ι → Cube n → F) (pin : Cube n → F)
    (τ : Fin n → F) (z c₀ : F) (q : Fin n → F[X]) (χ : Fin n → F)
    (hc : Consistent 2 (fun i ↦ some (τ i)) c₀ q χ)
    (hdoom : c₀ ≠ cubeSum (fun i ↦ some (τ i)) (zcFun node A B Z z) ∨ pin ≠ 0)
    (hgood : ∀ j, χ j ∉ zcBad node A B Z pin τ z c₀ q χ j) :
    claimAt c₀ q χ (Fin.last n) ≠ zcFun node A B Z z χ ∨ mle pin χ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hlast, hpin⟩ := hcon
  have hΦ := indDeg_zcFun node A B Z z
  -- A false claim at round `j` escapes at a bad challenge of a round `j' ≥ j` with a false claim.
  have escape : ∀ j : Fin (n + 1), claimAt c₀ q χ j ≠
      trueAt n (fun i ↦ some (τ i)) (zcFun node A B Z z) χ j → False := by
    intro j hj
    obtain ⟨j', -, hne, hbad⟩ := sumcheck_escape 2 n _ _ c₀ q χ hΦ hc j hj hlast
    apply hgood j'
    rw [zcBad, if_neg hne]
    exact hbad
  rcases hdoom with h0 | hp
  · exact escape 0 (by rw [trueAt_zero]; exact h0)
  · -- The constant position escapes at some round; there the claim is true, or it escapes later.
    obtain ⟨j, hj⟩ : ∃ j, χ j ∈ pointBad n (fun _ : Unit ↦ pin) χ j := by
      by_contra hall
      push Not at hall
      obtain ⟨_, h⟩ := point_escape n (fun _ : Unit ↦ pin) χ ⟨(), hp⟩ hall
      exact h hpin
    by_cases hcl : claimAt c₀ q χ j.castSucc =
        trueAt n (fun i ↦ some (τ i)) (zcFun node A B Z z) χ j.castSucc
    · apply hgood j
      rw [zcBad, if_pos hcl]
      exact hj
    · exact escape j.castSucc hcl

/-- **The zerocheck's soundness.** A nonzero residual (Boolean, with `F_2`-independent fixed
weights) or a nonzero constant-position table leaves the terminal values wrong or the table
nonzero at the challenges, unless a sampled coordinate, the skip challenge or a round's challenge
is bad. -/
theorem zerocheck_sound {n' f₀ ns : ℕ} (h : n' = f₀ + ns) {node : Bool × ι → F}
    (hinj : Function.Injective node) {fixed : Fin f₀ → F} (hf : HFixed fixed)
    (A B Z : ι → Cube n' → F) (pin : Cube n' → F)
    (hbool : ∀ i b, A i b * B i b + Z i b = 0 ∨ A i b * B i b + Z i b = 1)
    (τs : Fin ns → F) (cv : ι → F) (z : F) (q : Fin n' → F[X]) (χ : Fin n' → F) (va vb vc : F)
    (hc : Consistent 2 (fun i ↦ some (fullPoint h fixed τs i)) ((interp node cv).eval z) q χ)
    (hend : claimAt ((interp node cv).eval z) q χ (Fin.last n') = va * vb + vc)
    (hdoom : (∃ i b, A i b * B i b + Z i b ≠ 0) ∨ pin ≠ 0)
    (hτ : ∀ j, τs j ∉ pointBad ns
      (sampledTables h fixed fun i b ↦ A i b * B i b + Z i b) τs j)
    (hz : z ∉ skipBad node A B Z (fullPoint h fixed τs) cv)
    (hχ : ∀ j, χ j ∉ zcBad node A B Z pin (fullPoint h fixed τs) z ((interp node cv).eval z) q χ j) :
    ¬ (va = skipVal node A z χ ∧ vb = skipVal node B z χ ∧ vc = skipVal node Z z χ) ∨
      mle pin χ ≠ 0 := by
  have hdoom' : (interp node cv).eval z ≠
      cubeSum (fun i ↦ some (fullPoint h fixed τs i)) (zcFun node A B Z z) ∨ pin ≠ 0 := by
    rcases hdoom with hr | hp
    · exact Or.inl (skip_escape hinj A B Z _ cv (point_phase h hf hbool hr hτ) hz)
    · exact Or.inr hp
  rcases zc_rounds node A B Z pin _ z _ q χ hc hdoom' hχ with hl | hp
  · refine Or.inl fun ⟨ha, hb, hz⟩ ↦ hl ?_
    rw [hend, ha, hb, hz]
    rfl
  · exact Or.inr hp

end FlockSound
