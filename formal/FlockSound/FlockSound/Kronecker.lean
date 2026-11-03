-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Zerocheck
import Mathlib.Algebra.Polynomial.Expand

/-!
# A run of squares of one challenge: the Kronecker substitution

π1-rec3 (`crates/leanvm_rec/SPEC-REC.md` §1.4; `crates/leanvm_flock_gas/src/transcript.rs`,
`FsShape::draw`, `squares`) derives a run of `m` challenges from one: `c, c², c⁴, …, c^(2^(m-1))`
(`sqPt m c`). A multilinear extension at such a point is a polynomial in `c`: the base-2 Kronecker
substitution `r_i ↦ c^(2^i)` sends the monomial `Π_{i ∈ S} r_i` to `c^(Σ_{i ∈ S} 2^i)`, distinct
monomials to distinct powers, so a table that is not zero on the cube stays a nonzero polynomial,
of degree at most `2^m − 1`, and vanishes at at most `2^m − 1` values of `c`.

* `kron m t` is that polynomial, defined on the lowest coordinate: with `t₀`, `t₁` the halves of
  `t` (`Fin.cons false`, `Fin.cons true`),
  `kron (m+1) t = expand 2 (kron m t₀) + X · expand 2 (kron m t₁ − kron m t₀)`, the even part
  and the odd part (`sqPt (m+1) c = (c, sqPt m (c²))`, `mle_cons`).
* `eval_kron`: `(kron m t).eval c = mle t (sqPt m c)`; `natDegree_kron_le`: degree at most
  `2^m − 1`; `kron_eq_zero_iff`: `kron m t = 0 ↔ t = 0` (the even and odd coefficients,
  `coeff_expand`), so `kron m` is injective (`kron_sub`, `kron_injective`).
* `kronBad m t`, the family version of `Point.lean`'s `pointBad`: the challenges `c` at which every
  table of a family not all zero has a zero extension at `sqPt m c`; at most `2^m − 1` of them
  (`card_kronBad_le`), and outside them some extension is nonzero (`kron_escape`).
* `point_phase_sq`, `zerocheck_sound_sq`: `Zerocheck.lean`'s `point_phase` and `zerocheck_sound`
  with the sampled coordinates `τs := sqPt ns c` of one challenge `c` (Flock's zerocheck eq point
  in π1-rec3, after its fixed coordinates). The `ns` bad sets of one value each become one bad set
  of at most `2^ns − 1` values of `c`.

Decisions: `kron 0 t` is the constant `t` at the empty cube point; the bad set is a `Finset F`
defined classically (as `pointBad`), the family index type `ι` arbitrary. Nothing here transcribes
a source.
-/

namespace FlockSound

open Polynomial Finset

section Ring

variable {F : Type*} [CommRing F]

/-- **The point of squares**: `(c, c², c⁴, …, c^(2^(m-1)))`. -/
def sqPt (m : ℕ) (c : F) : Fin m → F := fun i ↦ c ^ (2 ^ (i : ℕ))

/-- The squares of `c` are `c`, then the squares of `c²`. -/
theorem sqPt_succ (m : ℕ) (c : F) : sqPt (m + 1) c = Fin.cons c (sqPt m (c ^ 2)) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [sqPt]
  · simp only [sqPt, Fin.cons_succ, Fin.val_succ]
    rw [← pow_mul, ← pow_succ']

/-- **The Kronecker substitution of a table**: the polynomial `c ↦ mle t (sqPt m c)`, built on the
lowest coordinate, its even part from the low half and its odd part from the difference of the
halves. -/
noncomputable def kron : (m : ℕ) → (Cube m → F) → F[X]
  | 0, t => C (t fun i ↦ i.elim0)
  | m + 1, t => expand F 2 (kron m fun b ↦ t (Fin.cons false b)) +
      X * expand F 2 (kron m (fun b ↦ t (Fin.cons true b)) - kron m fun b ↦ t (Fin.cons false b))

/-- **The substitution evaluates to the extension at the squares.** -/
theorem eval_kron : ∀ (m : ℕ) (t : Cube m → F) (c : F), (kron m t).eval c = mle t (sqPt m c)
  | 0, t, c => by
    have hc : sqPt 0 c = cube (fun i ↦ i.elim0 : Cube 0) := funext fun i ↦ i.elim0
    rw [hc, mle_cube]
    simp [kron]
  | m + 1, t, c => by
    rw [sqPt_succ, mle_cons, ← eval_kron m, ← eval_kron m]
    simp only [kron, eval_add, eval_mul, eval_X, eval_sub, expand_eval]
    ring

/-- **The substitution has degree at most `2^m − 1`.** -/
theorem natDegree_kron_le : ∀ (m : ℕ) (t : Cube m → F), (kron m t).natDegree ≤ 2 ^ m - 1
  | 0, t => by simp [kron]
  | m + 1, t => by
    have h0 := natDegree_kron_le m (fun b ↦ t (Fin.cons false b))
    have h1 := natDegree_kron_le m (fun b ↦ t (Fin.cons true b))
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hs := (natDegree_sub_le (kron m fun b ↦ t (Fin.cons true b))
      (kron m fun b ↦ t (Fin.cons false b))).trans (max_le h1 h0)
    have hX := natDegree_X_le (R := F)
    rw [kron, pow_succ]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_expand]
      omega
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_expand]
      omega

/-- The coefficients of `expand 2 p` at the even exponents are `p`'s. -/
theorem coeff_expand_two_mul (p : F[X]) (k : ℕ) : (expand F 2 p).coeff (2 * k) = p.coeff k :=
  coeff_expand_mul' (by norm_num) p k

/-- The coefficients of `expand 2 p` at the odd exponents are zero. -/
theorem coeff_expand_two_mul_add_one (p : F[X]) (k : ℕ) :
    (expand F 2 p).coeff (2 * k + 1) = 0 := by
  rw [coeff_expand (by norm_num)]
  exact ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)

/-- **An even part plus `X` times an odd part is zero only if both are.** -/
theorem eq_zero_of_expand_add_X_mul {p q : F[X]} (h : expand F 2 p + X * expand F 2 q = 0) :
    p = 0 ∧ q = 0 := by
  constructor
  · ext k
    have hk := congrArg (fun r ↦ r.coeff (2 * k)) h
    simp only [coeff_add, coeff_zero] at hk
    rw [coeff_expand_two_mul] at hk
    rcases k with _ | k
    · simpa using hk
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, coeff_X_mul,
        coeff_expand_two_mul_add_one, add_zero] at hk
      simpa using hk
  · ext k
    have hk := congrArg (fun r ↦ r.coeff (2 * k + 1)) h
    simp only [coeff_add, coeff_zero, coeff_X_mul] at hk
    rw [coeff_expand_two_mul_add_one, coeff_expand_two_mul, zero_add] at hk
    simpa using hk

/-- **The substitution of a table is zero exactly when the table is.** -/
theorem kron_eq_zero_iff : ∀ {m : ℕ} {t : Cube m → F}, kron m t = 0 ↔ t = 0
  | 0, t => by
    simp only [kron, C_eq_zero]
    constructor
    · intro h
      funext b
      have hb : b = fun i ↦ i.elim0 := funext fun i ↦ i.elim0
      rw [hb]
      exact h
    · intro h
      rw [h]
      rfl
  | m + 1, t => by
    constructor
    · intro h
      obtain ⟨h0, h1⟩ := eq_zero_of_expand_add_X_mul h
      rw [h0, sub_zero] at h1
      have e0 := kron_eq_zero_iff.mp h0
      have e1 := kron_eq_zero_iff.mp h1
      funext b
      obtain ⟨b₀, b', rfl⟩ : ∃ b₀ b', b = Fin.cons b₀ b' :=
        ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
      cases b₀
      · exact congrFun e0 b'
      · exact congrFun e1 b'
    · rintro rfl
      have e0 : kron m (fun b ↦ (0 : Cube (m + 1) → F) (Fin.cons false b)) = 0 :=
        kron_eq_zero_iff.mpr rfl
      have e1 : kron m (fun b ↦ (0 : Cube (m + 1) → F) (Fin.cons true b)) = 0 :=
        kron_eq_zero_iff.mpr rfl
      rw [kron, e0, e1, sub_zero, map_zero, mul_zero, add_zero]

/-- The substitution is additive: of a difference, the difference. -/
theorem kron_sub : ∀ (m : ℕ) (s t : Cube m → F), kron m (s - t) = kron m s - kron m t
  | 0, s, t => by simp [kron]
  | m + 1, s, t => by
    have e0 : kron m (fun b ↦ (s - t) (Fin.cons false b)) =
        kron m (fun b ↦ s (Fin.cons false b)) - kron m (fun b ↦ t (Fin.cons false b)) :=
      kron_sub m (fun b ↦ s (Fin.cons false b)) (fun b ↦ t (Fin.cons false b))
    have e1 : kron m (fun b ↦ (s - t) (Fin.cons true b)) =
        kron m (fun b ↦ s (Fin.cons true b)) - kron m (fun b ↦ t (Fin.cons true b)) :=
      kron_sub m (fun b ↦ s (Fin.cons true b)) (fun b ↦ t (Fin.cons true b))
    rw [kron, kron, kron, e0, e1]
    simp only [map_sub]
    ring

/-- **The substitution is injective.** -/
theorem kron_injective (m : ℕ) : Function.Injective (kron (F := F) m) := fun s t h ↦ by
  have h0 : kron m (s - t) = 0 := by rw [kron_sub, h, sub_self]
  exact sub_eq_zero.mp (kron_eq_zero_iff.mp h0)

end Ring

/-! ## A family of tables at the squares of one challenge -/

section Bad

variable {F : Type*} [Field F] [Fintype F] {ι : Type*}

/-- **The bad challenges of a run of squares**: for a family of tables not all zero, the `c` at
which every table's extension vanishes at `sqPt m c`; empty for a zero family. -/
noncomputable def kronBad (m : ℕ) (t : ι → Cube m → F) : Finset F := by
  classical exact
    if ∃ i, t i ≠ 0 then univ.filter fun c ↦ ∀ i, mle (t i) (sqPt m c) = 0 else ∅

/-- **At most `2^m − 1` bad challenges**: the roots of one nonzero table's substitution. -/
theorem card_kronBad_le (m : ℕ) (t : ι → Cube m → F) : (kronBad m t).card ≤ 2 ^ m - 1 := by
  classical
  unfold kronBad
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    have hk : kron m (t i) ≠ 0 := fun h0 ↦ hi (kron_eq_zero_iff.mp h0)
    refine (card_le_degree_of_subset_roots fun c hc ↦ ?_).trans (natDegree_kron_le m (t i))
    simp only [Finset.mem_val, mem_filter, mem_univ, true_and] at hc
    exact (mem_roots hk).mpr ((eval_kron m (t i) c).trans (hc i))
  · simp

/-- **A family not all zero stays so at the squares** unless the challenge is bad. -/
theorem kron_escape {m : ℕ} {t : ι → Cube m → F} (hne : ∃ i, t i ≠ 0) {c : F}
    (hc : c ∉ kronBad m t) : ∃ i, mle (t i) (sqPt m c) ≠ 0 := by
  classical
  unfold kronBad at hc
  split_ifs at hc
  simp only [mem_filter, mem_univ, true_and] at hc
  push Not at hc
  exact hc

end Bad

/-! ## The zerocheck with its sampled coordinates the squares of one challenge -/

section Zerocheck

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- **The point, with squares**: Boolean residuals, not all zero, stay so at the point whose
sampled coordinates are `sqPt ns c` unless `c` is bad (at most `2^ns − 1` values). -/
theorem point_phase_sq {n' f₀ ns : ℕ} (h : n' = f₀ + ns) {fixed : Fin f₀ → F} (hf : HFixed fixed)
    {R : ι → Cube n' → F} (hbool : ∀ i b, R i b = 0 ∨ R i b = 1) (hne : ∃ i b, R i b ≠ 0)
    {c : F} (hgood : c ∉ kronBad ns (sampledTables h fixed R)) :
    ∃ i, mle (R i) (fullPoint h fixed (sqPt ns c)) ≠ 0 := by
  obtain ⟨i, hi⟩ := kron_escape (sampledTables_ne h hf hbool hne) hgood
  exact ⟨i, by rwa [mle_fullPoint]⟩

/-- **The zerocheck's soundness, with squares.** `zerocheck_sound` with the sampled coordinates
`τs := sqPt ns c`: a nonzero residual (Boolean, with `F_2`-independent fixed weights) or a nonzero
constant-position table leaves the terminal values wrong or the table nonzero at the challenges,
unless `c` (at most `2^ns − 1` values), the skip challenge or a round's challenge is bad. -/
theorem zerocheck_sound_sq {n' f₀ ns : ℕ} (h : n' = f₀ + ns) {node : Bool × ι → F}
    (hinj : Function.Injective node) {fixed : Fin f₀ → F} (hf : HFixed fixed)
    (A B Z : ι → Cube n' → F) (pin : Cube n' → F)
    (hbool : ∀ i b, A i b * B i b + Z i b = 0 ∨ A i b * B i b + Z i b = 1)
    (c : F) (cv : ι → F) (z : F) (q : Fin n' → F[X]) (χ : Fin n' → F) (va vb vc : F)
    (hc : Consistent 2 (fun i ↦ some (fullPoint h fixed (sqPt ns c) i))
      ((interp node cv).eval z) q χ)
    (hend : claimAt ((interp node cv).eval z) q χ (Fin.last n') = va * vb + vc)
    (hdoom : (∃ i b, A i b * B i b + Z i b ≠ 0) ∨ pin ≠ 0)
    (hτ : c ∉ kronBad ns (sampledTables h fixed fun i b ↦ A i b * B i b + Z i b))
    (hz : z ∉ skipBad node A B Z (fullPoint h fixed (sqPt ns c)) cv)
    (hχ : ∀ j, χ j ∉ zcBad node A B Z pin (fullPoint h fixed (sqPt ns c)) z
      ((interp node cv).eval z) q χ j) :
    ¬ (va = skipVal node A z χ ∧ vb = skipVal node B z χ ∧ vc = skipVal node Z z χ) ∨
      mle pin χ ≠ 0 := by
  have hdoom' : (interp node cv).eval z ≠
      cubeSum (fun i ↦ some (fullPoint h fixed (sqPt ns c) i)) (zcFun node A B Z z) ∨
        pin ≠ 0 := by
    rcases hdoom with hr | hp
    · exact Or.inl (skip_escape hinj A B Z _ cv (point_phase_sq h hf hbool hr hτ) hz)
    · exact Or.inr hp
  rcases zc_rounds node A B Z pin _ z _ q χ hc hdoom' hχ with hl | hp
  · refine Or.inl fun ⟨ha, hb, hz⟩ ↦ hl ?_
    rw [hend, ha, hb, hz]
    rfl
  · exact Or.inr hp

end Zerocheck

end FlockSound

/-- info: 'FlockSound.eval_kron' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.eval_kron

/-- info: 'FlockSound.natDegree_kron_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.natDegree_kron_le

/-- info: 'FlockSound.kron_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.kron_eq_zero_iff

/-- info: 'FlockSound.kron_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.kron_injective

/-- info: 'FlockSound.card_kronBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.card_kronBad_le

/-- info: 'FlockSound.kron_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.kron_escape

/-- info: 'FlockSound.point_phase_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.point_phase_sq

/-- info: 'FlockSound.zerocheck_sound_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.zerocheck_sound_sq
