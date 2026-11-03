-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Lincheck

/-!
# The lincheck's terminal, the matrices' reduction, and its merged form

The lincheck's terminal at its point `χ'` is `Σ_cy colW(cy) s(cy)` (`colW`, the column weight's
extension at `χ'`), which splits (`colW_eq`) into the matrices' part `matPart(cy)`, the identity's
`α² eq(χ_in, χ') e(cy)` and the constant position's `α³ eq(χ', cpos.2) [cy = cpos.1]`. The two
known terms are the verifier's (`reduce_terminal`'s `known`); the matrices' part is the **product
sum** `Σ_(x, y) L(x) s(y) G(x, y)` over the skip's `k` row bits and the column's `k + l` packing
bits (`matSum`, `cubeSum_matFun`), a sumcheck of the product of two multilinear functions
(`matFun`, degree `2`), whose terminal at `(ρ, σ)` is `L̂(ρ) ŝ(σ) (Â0 + α B̂0)(ρ, r_l, r_h, σ, χ')`
(`matFun_append`): the claims `a`, `b` on the setup matrices (`matMle`).

* **`matrices_sound`** (milestone 1): its own `k + (k + l)` rounds; a false product-sum claim and
  true `a`, `b` make the verifier's terminal check fail, unless a round's challenge is bad.
* **`batched_sound`** (iteration 2, lever 4a): the same sum as one component of a `λ`-combined
  sumcheck of several (`Σ_i λ^i Φ_i`), zero-extended to the batch's variables (`zeroExt`); a false
  component claim makes some component's terminal claim false, unless `λ` (at most `K - 1`
  values, `lambdaBad`) or a round's challenge is bad.

Nothing here transcribes a source.
-/

namespace FlockSound

open Polynomial Finset

variable {F : Type*} [Field F] {k l m κ : ℕ}

section Defs

variable (A B : Pos k l m → Pos k l m → Bool) (cpos : Pos k l m) (node : Bool × Cube k → F) (z : F)
  (rl : Fin l → F) (rh : Fin m → F) (χ' : Fin m → F)

/-- The column weight at the lincheck's point. -/
noncomputable def colW (α : F) (cy : Cube (k + l)) : F :=
  mle (fun ch ↦ linW A B cpos node z rl rh α (cy, ch)) χ'

/-- The matrices' part of the column weight. -/
noncomputable def matPart (α : F) (cy : Cube (k + l)) : F :=
  mle (fun ch ↦ ∑ row, rowW node z rl rh row * (bit (A row (cy, ch)) + α * bit (B row (cy, ch)))) χ'

/-- The low weights `e(cy)`: the skip's Lagrange weight at `z`, `eq` on the other packing bits. -/
noncomputable def lowW (cy : Cube (k + l)) : F := (lag node (lowPart cy)).eval z * eqP rl (highPart cy)

/-- The product sum's first table: the skip's weights times the slices. -/
noncomputable def lsTab (s : Cube (k + l) → F) (b : Cube (k + (k + l))) : F :=
  (lag node (lowPart b)).eval z * s (highPart b)

/-- A matrix's table on the product sum's cube: its extension over the row's other coordinates
and the column's slot bits, at Boolean `(x, y)`. -/
def matTab (M : Pos k l m → Pos k l m → Bool) (b : Cube (k + (k + l))) : F :=
  ∑ bl : Cube l, ∑ bh : Cube m, ∑ ch : Cube m, eqP rl bl * eqP rh bh * eqP χ' ch *
    bit (M (Fin.append (lowPart b) bl, bh) (highPart b, ch))

/-- **The matrix's extension** at `(x, r_l, r_h, y, χ')`: the row's coordinates `(x, r_l, r_h)`,
then the column's `(y, χ')` (`matrixStack`'s word `row + 2^(k+l+m) col`); at Boolean `(x, y)` the
table `matTab`. -/
noncomputable def matMle (M : Pos k l m → Pos k l m → Bool) (x : Fin k → F) (y : Fin (k + l) → F) : F :=
  mle (matTab rl rh χ' M) (Fin.append x y)

/-- The product sum's second table: `Â0 + α B̂0` at Boolean `(x, y)`. -/
noncomputable def gTab (α : F) (b : Cube (k + (k + l))) : F :=
  matTab rl rh χ' A b + α * matTab rl rh χ' B b

/-- **The matrices' sumcheck function**: the product of the two tables' extensions. -/
noncomputable def matFun (s : Cube (k + l) → F) (α : F) (r : Fin (k + (k + l)) → F) : F :=
  mle (lsTab node z s) r * mle (gTab A B rl rh χ' α) r

end Defs

theorem colW_eq (A B : Pos k l m → Pos k l m → Bool) (cpos : Pos k l m) (node : Bool × Cube k → F)
    (z : F) (rl : Fin l → F) (rh : Fin m → F) (χ' : Fin m → F) (α : F) (cy : Cube (k + l)) :
    colW A B cpos node z rl rh χ' α cy = matPart A B node z rl rh χ' α cy +
      α ^ 2 * eqEval rh χ' * lowW node z rl cy +
      α ^ 3 * (if cy = cpos.1 then eqP χ' cpos.2 else 0) := by
  have hrow : ∀ ch : Cube m, rowW node z rl rh (cy, ch) = lowW node z rl cy * eqP rh ch := fun ch ↦ rfl
  have hpin : mle (fun ch : Cube m ↦ if ((cy, ch) : Pos k l m) = cpos then (1 : F) else 0) χ' =
      if cy = cpos.1 then eqP χ' cpos.2 else 0 := by
    rw [mle]
    split_ifs with h
    · rw [Finset.sum_eq_single cpos.2]
      · simp [h]
      · intro b _ hb
        simp [Prod.ext_iff, hb]
      · simp
    · refine Finset.sum_eq_zero fun b _ ↦ ?_
      simp [Prod.ext_iff, h]
  unfold colW linW
  rw [mle_add, mle_add, mle_smul, mle_smul, hpin]
  simp only [hrow, mle_smul, mle_eqP]
  unfold matPart
  ring

/-- The lincheck's terminal is the column weights against the slices. -/
theorem linFun_eq_colW (A B : Pos k l m → Pos k l m → Bool) (Z : Cube (k + l) → Cube m → Cube κ → F)
    (cpos : Pos k l m) (node : Bool × Cube k → F) (z : F) (rl : Fin l → F) (rh : Fin m → F)
    (rt : Fin κ → F) (α : F) (χ' : Fin m → F) :
    linFun A B Z cpos node z rl rh rt α χ' =
      ∑ cy, colW A B cpos node z rl rh χ' α cy * strue Z rt χ' cy := rfl

/-- The matrices' part is the skip's weights against the product sum's second table. -/
theorem matPart_eq (A B : Pos k l m → Pos k l m → Bool) (node : Bool × Cube k → F) (z : F)
    (rl : Fin l → F) (rh : Fin m → F) (χ' : Fin m → F) (α : F) (cy : Cube (k + l)) :
    matPart A B node z rl rh χ' α cy =
      ∑ bx : Cube k, (lag node bx).eval z * gTab A B rl rh χ' α (Fin.append bx cy) := by
  simp only [matPart, mle, sum_pos, rowW, gTab, matTab, lowPart_append, highPart_append,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [sum_comm_in3]
  refine Finset.sum_congr rfl fun bx _ ↦ Finset.sum_congr rfl fun bl _ ↦
    Finset.sum_congr rfl fun bh _ ↦ Finset.sum_congr rfl fun ch _ ↦ ?_
  ring

/-- **The product sum is the matrices' part against the slices.** -/
theorem cubeSum_matFun (A B : Pos k l m → Pos k l m → Bool) (node : Bool × Cube k → F) (z : F)
    (rl : Fin l → F) (rh : Fin m → F) (χ' : Fin m → F) (s : Cube (k + l) → F) (α : F) :
    cubeSum (fun _ ↦ none) (matFun A B node z rl rh χ' s α) =
      ∑ cy, matPart A B node z rl rh χ' α cy * s cy := by
  simp only [cubeSum, eqW_none, one_mul, matFun, mle_cube, matPart_eq, Finset.sum_mul]
  rw [sum_cube_append, Finset.sum_comm]
  refine Finset.sum_congr rfl fun cy _ ↦ Finset.sum_congr rfl fun bx _ ↦ ?_
  simp only [lsTab, lowPart_append, highPart_append]
  ring

/-- The two tables' extensions at a split point: the skip's weights' and the slices'
extensions, and the matrices' (`Â0 + α B̂0`). -/
theorem matFun_append (A B : Pos k l m → Pos k l m → Bool) (node : Bool × Cube k → F) (z : F)
    (rl : Fin l → F) (rh : Fin m → F) (χ' : Fin m → F) (s : Cube (k + l) → F) (α : F)
    (ρ : Fin k → F) (σ : Fin (k + l) → F) :
    matFun A B node z rl rh χ' s α (Fin.append ρ σ) =
      mle (fun bx ↦ (lag node bx).eval z) ρ * mle s σ *
        (matMle rl rh χ' A ρ σ + α * matMle rl rh χ' B ρ σ) := by
  have h1 : mle (lsTab node z s) (Fin.append ρ σ) = mle (fun bx ↦ (lag node bx).eval z) ρ * mle s σ := by
    rw [mle_append]
    simp only [lsTab, lowPart_append, highPart_append]
    have e : ∀ by' : Cube (k + l), mle (fun bx ↦ (lag node bx).eval z * s by') ρ =
        s by' * mle (fun bx ↦ (lag node bx).eval z) ρ := fun by' ↦ by
      rw [← mle_smul]
      congr 1
      funext bx
      ring
    simp only [e]
    rw [mle_smul_right]
    ring
  have h2 : ∀ M : Pos k l m → Pos k l m → Bool,
      mle (matTab rl rh χ' M) (Fin.append ρ σ) = matMle rl rh χ' M ρ σ := fun _ ↦ rfl
  unfold matFun gTab
  rw [h1, mle_add, mle_smul, h2, h2]

/-! ## Milestone 1: the matrices' own sumcheck -/

section Bad

variable [Fintype F] [DecidableEq F]

/-- **The matrices' reduction's soundness** (its own rounds): from a false product-sum claim, with
true claims `a`, `b` on the matrices, the verifier's terminal check
`running = (a + α b) L̂(ρ) ŝ(σ)` fails, unless a round's challenge is bad. -/
theorem matrices_sound (A B : Pos k l m → Pos k l m → Bool) (node : Bool × Cube k → F) (z : F)
    (rl : Fin l → F) (rh : Fin m → F) (χ' : Fin m → F) (s : Cube (k + l) → F) (α c a b : F)
    (q : Fin (k + (k + l)) → F[X]) (χ : Fin (k + (k + l)) → F)
    (hc : Consistent 2 (fun _ ↦ none) c q χ)
    (hclaim : c ≠ ∑ cy, matPart A B node z rl rh χ' α cy * s cy)
    (hend : claimAt c q χ (Fin.last _) =
      (a + α * b) * mle (fun bx ↦ (lag node bx).eval z) (lowPart χ) * mle s (highPart χ))
    (ha : a = matMle rl rh χ' A (lowPart χ) (highPart χ))
    (hb : b = matMle rl rh χ' B (lowPart χ) (highPart χ)) :
    ∃ j, χ j ∈ sumBad 2 _ (fun _ ↦ none) (matFun A B node z rl rh χ' s α) q χ j := by
  refine sumcheck_sound ((indDeg_mle _).mul (indDeg_mle _)) hc (by rwa [cubeSum_matFun]) ?_
  rw [hend, ← append_lowPart_highPart χ, matFun_append, lowPart_append, highPart_append] at *
  rw [ha, hb]
  ring

/-! ## Iteration 2: merged into a `λ`-combined sumcheck -/

/-- The polynomial in `λ` the components' errors make. -/
noncomputable def lambdaPoly {K : ℕ} (c t : Fin K → F) : F[X] :=
  ∑ i : Fin K, C (c i - t i) * X ^ (i : ℕ)

theorem eval_lambdaPoly {K : ℕ} (c t : Fin K → F) (x : F) :
    (lambdaPoly c t).eval x = ∑ i : Fin K, x ^ (i : ℕ) * c i - ∑ i : Fin K, x ^ (i : ℕ) * t i := by
  simp only [lambdaPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem lambdaPoly_ne_zero {K : ℕ} {c t : Fin K → F} (h : ∃ i, c i ≠ t i) : lambdaPoly c t ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  intro h0
  have := congrArg (·.coeff i) h0
  simp only [lambdaPoly, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simp only [if_true] at this
    exact hi (sub_eq_zero.mp this)
  · intro j _ hj
    rw [if_neg (fun h ↦ hj (Fin.ext h.symm))]
  · simp

theorem natDegree_lambdaPoly_le {K : ℕ} (c t : Fin K → F) : (lambdaPoly c t).natDegree ≤ K - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_X_pow_le _ _).trans (by have := i.isLt; omega)

/-- **`λ`'s bad values**: the roots of the components' error polynomial, when it is nonzero. -/
noncomputable def lambdaBad {K : ℕ} (c t : Fin K → F) : Finset F :=
  if lambdaPoly c t ≠ 0 then (lambdaPoly c t).roots.toFinset else ∅

theorem card_lambdaBad_le {K : ℕ} (c t : Fin K → F) : (lambdaBad c t).card ≤ K - 1 := by
  unfold lambdaBad
  split_ifs
  · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_lambdaPoly_le c t))
  · simp

/-- **A `λ`-combined sumcheck's soundness**: if a component's claim is false and every component's
terminal claim is true, `λ` or a round's challenge is bad. -/
theorem batched_sound {K n d : ℕ} (Φ : Fin K → (Fin n → F) → F) (hΦ : ∀ i, IndDeg (Φ i) d)
    (c v : Fin K → F) (lam : F) (q : Fin n → F[X]) (χ : Fin n → F)
    (hfalse : ∃ i, c i ≠ cubeSum (fun _ ↦ none) (Φ i))
    (hc : Consistent d (fun _ ↦ none) (∑ i : Fin K, lam ^ (i : ℕ) * c i) q χ)
    (hend : claimAt (∑ i : Fin K, lam ^ (i : ℕ) * c i) q χ (Fin.last n) =
      ∑ i : Fin K, lam ^ (i : ℕ) * v i)
    (hv : ∀ i, v i = Φ i χ) :
    lam ∈ lambdaBad c (fun i ↦ cubeSum (fun _ ↦ none) (Φ i)) ∨
      ∃ j, χ j ∈ sumBad d n (fun _ ↦ none) (fun r ↦ ∑ i : Fin K, lam ^ (i : ℕ) * Φ i r) q χ j := by
  by_cases hlam : lam ∈ lambdaBad c (fun i ↦ cubeSum (fun _ ↦ none) (Φ i))
  · exact Or.inl hlam
  · refine Or.inr (sumcheck_sound (IndDeg.sum univ fun i _ ↦ (hΦ i).const_mul _) hc ?_ ?_)
    · intro h0
      apply hlam
      have hne := lambdaPoly_ne_zero hfalse
      rw [lambdaBad, if_pos hne, Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_lambdaPoly]
      rw [sub_eq_zero, h0]
      simp only [cubeSum, eqW_none, one_mul, Finset.mul_sum]
      exact Finset.sum_comm
    · rw [hend]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hv i]

end Bad

/-! ## Zero extension -/

/-- A table on the low `a` coordinates, zero-extended by `eq(·, 0)` on `b` more. -/
def zeroExt {a b : ℕ} (t : Cube a → F) (c : Cube (a + b)) : F :=
  if highPart c = (fun _ ↦ false) then t (lowPart c) else 0

theorem mle_zeroExt {a b : ℕ} (t : Cube a → F) (x : Fin a → F) (y : Fin b → F) :
    mle (zeroExt (b := b) t) (Fin.append x y) = mle t x * eqP y (fun _ ↦ false) := by
  rw [mle_append]
  simp only [zeroExt, lowPart_append, highPart_append]
  rw [mle, Finset.sum_eq_single (fun _ ↦ false)]
  · simp
  · intro c _ hc
    simp [hc, mle_const]
  · simp

/-- The zero-extended sum is the sum: only the zero high block counts. -/
theorem sum_zeroExt {a b : ℕ} (t s : Cube a → F) :
    ∑ c : Cube (a + b), zeroExt (b := b) t c * s (lowPart c) = ∑ c : Cube a, t c * s c := by
  rw [sum_cube_append]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.sum_eq_single (fun _ ↦ false)]
  · simp [zeroExt]
  · intro y _ hy
    simp [zeroExt, hy]
  · simp

/-- **A product sum zero-extended** to `b` more variables: `t̂ · ŝ` with `t` zero-extended and
`s` read on the low block. Its cube sum is the product sum's; at a split point it is the
product's value times `eq(y, 0)`. -/
noncomputable def extFun {a b : ℕ} (t s : Cube a → F) (r : Fin (a + b) → F) : F :=
  mle (zeroExt (b := b) t) r * mle (fun c : Cube (a + b) ↦ s (lowPart c)) r

theorem cubeSum_extFun {a b : ℕ} (t s : Cube a → F) :
    cubeSum (fun _ ↦ none) (extFun (b := b) t s) = ∑ c : Cube a, t c * s c := by
  simp only [cubeSum, eqW_none, one_mul, extFun, mle_cube]
  exact sum_zeroExt t s

theorem extFun_append {a b : ℕ} (t s : Cube a → F) (x : Fin a → F) (y : Fin b → F) :
    extFun t s (Fin.append x y) = mle t x * mle s x * eqP y (fun _ ↦ false) := by
  rw [extFun, mle_zeroExt, mle_low]
  ring

theorem indDeg_extFun {a b : ℕ} (t s : Cube a → F) : IndDeg (extFun (b := b) t s) 2 :=
  (indDeg_mle _).mul (indDeg_mle _)

end FlockSound
