-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Cube
import Mathlib.LinearAlgebra.Lagrange

/-!
# The univariate skip

A zerocheck of `A ∘ B + C = 0` on the cube `ι × Cube n` whose `ι` part (`k` variables, `|ι| = N`)
is *skipped*: instead of `k` multilinear rounds, the prover sends the polynomial
`P(X) = Σ_b eq(τ, b) (Ã(X, b) B̃(X, b) + C̃(X, b))`, `Ã(X, b) = Σ_i L_i(X) A_i(b)` over the skip
domain `λ_i = node(false, i)` (`L_i` its Lagrange basis), on the coset `node(true, i)`: `N` values.
`P` has degree at most `2(N - 1)` and vanishes on the skip domain when every residual
`R_i = A_i B_i + C_i` vanishes at `τ`; the verifier interpolates zeros on the domain and the sent
values on the coset over the `2N` nodes (`interp`, degree below `2N`), draws `z`, and the
remaining `n` variables are a sumcheck of `zcFun z` (individual degree `2`) from `interp(z)`.

* `eval_skipPoly`: `P(z)` is the cube sum the rounds prove; `eval_skipPoly_node`: `P(λ_j)` is the
  residual's extension at `τ`.
* `skipBad`: the challenges `z` at which `interp` and `P` agree, when they differ; at most
  `2N - 1` (`card_skipBad_le`): the skip's error, `(2^(k+1) - 1)/|F|`.
* **`skip_escape`**: if some residual is nonzero at `τ`, then outside `skipBad` the claim the
  rounds start from is false.

Nothing here transcribes a source.
-/

namespace FlockSound

open Polynomial Finset

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The Lagrange basis over the skip domain `node(false, ·)`. -/
noncomputable def lag (node : Bool × ι → F) (i : ι) : F[X] :=
  Lagrange.basis univ (fun j ↦ node (false, j)) i

/-- The skip variable's extension of a family of tables at a cube point of the other variables. -/
noncomputable def skipExt (node : Bool × ι → F) (t : ι → Cube n → F) (b : Cube n) : F[X] :=
  ∑ i, C (t i b) * lag node i

/-- `Σ_i L_i(z) · t̂_i(x)`: the family at the skip challenge `z` and a point `x`. -/
noncomputable def skipVal (node : Bool × ι → F) (t : ι → Cube n → F) (z : F) (x : Fin n → F) : F :=
  ∑ i, (lag node i).eval z * mle (t i) x

/-- **The zerocheck's function after the skip**: `Ã(z, x) B̃(z, x) + C̃(z, x)`. -/
noncomputable def zcFun (node : Bool × ι → F) (A B Z : ι → Cube n → F) (z : F) (x : Fin n → F) : F :=
  skipVal node A z x * skipVal node B z x + skipVal node Z z x

/-- **The skip polynomial** `P` the honest prover sends on the coset. -/
noncomputable def skipPoly (node : Bool × ι → F) (A B Z : ι → Cube n → F) (τ : Fin n → F) : F[X] :=
  ∑ b, C (eqP τ b) * (skipExt node A b * skipExt node B b + skipExt node Z b)

/-- **The verifier's interpolant**: zeros on the skip domain, the sent values `cv` on the coset. -/
noncomputable def interp (node : Bool × ι → F) (cv : ι → F) : F[X] :=
  Lagrange.interpolate univ node fun p ↦ if p.1 then cv p.2 else 0

theorem eval_skipExt (node : Bool × ι → F) (t : ι → Cube n → F) (b : Cube n) (z : F) :
    (skipExt node t b).eval z = skipVal node t z (cube b) := by
  simp only [skipExt, skipVal, eval_finsetSum, eval_mul, eval_C, mle_cube]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- `P(z)` is the cube sum of `zcFun z`. -/
theorem eval_skipPoly (node : Bool × ι → F) (A B Z : ι → Cube n → F) (τ : Fin n → F) (z : F) :
    (skipPoly node A B Z τ).eval z = cubeSum (fun i ↦ some (τ i)) (zcFun node A B Z z) := by
  simp only [skipPoly, cubeSum, eval_finsetSum, eval_mul, eval_add, eval_C, eval_skipExt, eqW_some,
    zcFun]

theorem eval_lag_node {node : Bool × ι → F} (hinj : Function.Injective node) (i j : ι) :
    (lag node i).eval (node (false, j)) = if i = j then 1 else 0 := by
  have hv : Set.InjOn (fun j ↦ node (false, j)) ((univ : Finset ι) : Set ι) :=
    fun a _ b _ h ↦ (Prod.mk.inj (hinj h)).2
  split_ifs with h
  · subst h
    exact Lagrange.eval_basis_self hv (mem_univ _)
  · exact Lagrange.eval_basis_of_ne (s := univ) (v := fun j ↦ node (false, j)) h (mem_univ _)

/-- `P(λ_j)`: the residual's extension at `τ`. -/
theorem eval_skipPoly_node {node : Bool × ι → F} (hinj : Function.Injective node)
    (A B Z : ι → Cube n → F) (τ : Fin n → F) (j : ι) :
    (skipPoly node A B Z τ).eval (node (false, j)) = mle (fun b ↦ A j b * B j b + Z j b) τ := by
  have he : ∀ (t : ι → Cube n → F) (b : Cube n), (skipExt node t b).eval (node (false, j)) = t j b := by
    intro t b
    simp only [skipExt, eval_finsetSum, eval_mul, eval_C, eval_lag_node hinj]
    simp
  simp only [skipPoly, eval_finsetSum, eval_mul, eval_add, eval_C, he, mle]
  exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _

theorem natDegree_lag_le {node : Bool × ι → F} (hinj : Function.Injective node) (i : ι) :
    (lag node i).natDegree ≤ Fintype.card ι - 1 := by
  have hv : Set.InjOn (fun j ↦ node (false, j)) ((univ : Finset ι) : Set ι) :=
    fun a _ b _ h ↦ (Prod.mk.inj (hinj h)).2
  rw [lag, Lagrange.natDegree_basis hv (mem_univ _), card_univ]

theorem natDegree_skipExt_le {node : Bool × ι → F} (hinj : Function.Injective node)
    (t : ι → Cube n → F) (b : Cube n) : (skipExt node t b).natDegree ≤ Fintype.card ι - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_le _ _).trans (natDegree_lag_le hinj i)

theorem natDegree_skipPoly_le {node : Bool × ι → F} (hinj : Function.Injective node)
    (A B Z : ι → Cube n → F) (τ : Fin n → F) :
    (skipPoly node A B Z τ).natDegree ≤ 2 * (Fintype.card ι - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun b _ ↦ (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    have := natDegree_skipExt_le hinj A b
    have := natDegree_skipExt_le hinj B b
    omega
  · have := natDegree_skipExt_le hinj Z b
    omega

theorem natDegree_interp_le (node : Bool × ι → F) (hinj : Function.Injective node) (cv : ι → F) :
    (interp node cv).natDegree ≤ 2 * Fintype.card ι - 1 := by
  have h := Lagrange.degree_interpolate_le (s := (univ : Finset (Bool × ι))) (v := node)
    (fun p ↦ if p.1 then cv p.2 else 0) (fun a _ b _ h ↦ hinj h)
  rw [card_univ, Fintype.card_prod, Fintype.card_bool] at h
  exact natDegree_le_of_degree_le h

section Bad

variable [Fintype F] [DecidableEq F]

/-- **The skip's bad challenges**: where the interpolant and the skip polynomial agree, when they
differ. -/
noncomputable def skipBad (node : Bool × ι → F) (A B Z : ι → Cube n → F) (τ : Fin n → F)
    (cv : ι → F) : Finset F :=
  if interp node cv ≠ skipPoly node A B Z τ then
    univ.filter fun z ↦ (interp node cv).eval z = (skipPoly node A B Z τ).eval z
  else ∅

theorem card_skipBad_le {node : Bool × ι → F} (hinj : Function.Injective node)
    (A B Z : ι → Cube n → F) (τ : Fin n → F) (cv : ι → F) :
    (skipBad node A B Z τ cv).card ≤ 2 * Fintype.card ι - 1 := by
  unfold skipBad
  split_ifs with hne
  · have hne' : interp node cv - skipPoly node A B Z τ ≠ 0 := sub_ne_zero.mpr hne
    refine (card_le_degree_of_subset_roots
      (p := interp node cv - skipPoly node A B Z τ) fun x hx ↦ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (natDegree_interp_le node hinj cv) ?_))
    · rw [Finset.mem_val, Finset.mem_filter] at hx
      rw [mem_roots hne', IsRoot, eval_sub, hx.2, sub_self]
    · have := natDegree_skipPoly_le hinj A B Z τ
      omega
  · simp

/-- **The skip's soundness**: a residual nonzero at `τ` makes the rounds' starting claim false,
but at the bad challenges. -/
theorem skip_escape {node : Bool × ι → F} (hinj : Function.Injective node) (A B Z : ι → Cube n → F)
    (τ : Fin n → F) (cv : ι → F) (hres : ∃ j, mle (fun b ↦ A j b * B j b + Z j b) τ ≠ 0) {z : F}
    (hz : z ∉ skipBad node A B Z τ cv) :
    (interp node cv).eval z ≠ cubeSum (fun i ↦ some (τ i)) (zcFun node A B Z z) := by
  obtain ⟨j, hj⟩ := hres
  have hne : interp node cv ≠ skipPoly node A B Z τ := by
    intro h
    apply hj
    rw [← eval_skipPoly_node hinj, ← h, interp,
      Lagrange.eval_interpolate_at_node _ (fun a _ b _ h ↦ hinj h) (mem_univ _)]
    simp
  rw [← eval_skipPoly]
  intro h
  apply hz
  rw [skipBad, if_pos hne]
  simp [h]

end Bad

/-- `zcFun z` has individual degree `2`. -/
theorem indDeg_zcFun (node : Bool × ι → F) (A B Z : ι → Cube n → F) (z : F) :
    IndDeg (zcFun node A B Z z) 2 := by
  have hv : ∀ t : ι → Cube n → F, IndDeg (skipVal node t z) 1 := fun t ↦
    IndDeg.sum univ fun i _ ↦ (indDeg_mle (t i)).const_mul _
  exact ((hv A).mul (hv B)).add ((hv Z).mono (by norm_num))

end FlockSound
