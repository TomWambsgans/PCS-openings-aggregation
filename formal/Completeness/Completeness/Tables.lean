-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Statement

/-!
# The honest prover's tables

The tables the honest prover commits (`prove_with_randomness`: `domain::coefficients` of the cells,
the masks, the quotients' coefficients) are the coefficients of its polynomials in the basis of
products of digits (`tablePoly`, the novel basis), over the base field `K`, with the extension's
polynomials split into limbs. This file builds them and proves what the completeness theorem
needs of them, for any field `F` with a subfield `K` (`ι : K →+* F`):

* `exists_table_support`: **every polynomial over `K` of degree below `D ≤ 2^M` is the polynomial
  of a table on `M` digits that vanishes from index `D` on** (`idx`: the cube point's number, bit
  `k` of weight `2^k`, as Rust indexes a table). By induction on `M`: divide by the top digit
  (`tablePoly_snoc`).
* `tablePoly_map`: a table over `K` read in `F` holds the polynomial mapped to `F`.
* `cellsOf_witnessOfTable`: the cells of the first message a witness table holds
  (`witnessOfTable`) are its polynomial at the cells' points (the row polynomials' digit
  expansion, `digitsEval_cons`), so a table whose first chunk's polynomial takes the cells' values
  holds those cells whatever its masks (`cellsOf_witnessTable`).
* `LimbSystem`, `exists_limbs`: an element of `F` is `Σ_{e<3} ι(limb_e) Y^e` (`F192`'s
  `(c0, c1, c2)` on `1, Y, Y^2`); a polynomial over `F` is `Σ_e Y^e p_e` with `p_e` over `K` of no
  larger degree, so a slot of the quotient table holds it in three limb tables.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Completeness

open QuotientSecurity

/-! ## Indices -/

/-- **The index of a cube point**: bit `k` of weight `2^k` (`Table`'s entry order: coordinate `k`
of a claim weighs bit `k` of an entry's index). -/
def idx {M : ℕ} (b : Fin M → Bool) : ℕ := ∑ k : Fin M, if b k then 2 ^ (k : ℕ) else 0

theorem idx_snoc {M : ℕ} (b : Fin M → Bool) (x : Bool) :
    idx (Fin.snoc b x : Fin (M + 1) → Bool) = idx b + if x then 2 ^ M else 0 := by
  unfold idx
  rw [Fin.sum_univ_castSucc]
  simp

theorem idx_lt : ∀ {M : ℕ} (b : Fin M → Bool), idx b < 2 ^ M
  | 0, b => by simp [idx]
  | M + 1, b => by
    have h := idx_lt (M := M) (Fin.init b)
    have e : b = Fin.snoc (Fin.init b) (b (Fin.last M)) := (Fin.snoc_init_self b).symm
    rw [e, idx_snoc]
    split_ifs <;> rw [pow_succ] <;> omega

/-! ## Tables of polynomials -/

section Field

variable {K : Type*} [Field K] [CharP K 2]

/-- A table on `M + 1` digits from its two halves. -/
def joinTable {M : ℕ} (c₀ c₁ : (Fin M → Bool) → K) : (Fin (M + 1) → Bool) → K :=
  fun b => if b (Fin.last M) then c₁ (Fin.init b) else c₀ (Fin.init b)

theorem tablePoly_joinTable {M : ℕ} (c₀ c₁ : (Fin M → Bool) → K) :
    tablePoly (joinTable c₀ c₁) = tablePoly c₀ + digitPoly M * tablePoly c₁ := by
  rw [tablePoly_snoc]
  simp [joinTable, Fin.init_snoc]

theorem tablePoly_zero {M : ℕ} : tablePoly (fun _ : Fin M → Bool => (0 : K)) = 0 := by
  simp [tablePoly]

/-- **Every polynomial of degree below `D ≤ 2^M` is a table's**, the table vanishing from index
`D` on. -/
theorem exists_table_support : ∀ (M : ℕ) (p : K[X]) (D : ℕ), D ≤ 2 ^ M →
    (p = 0 ∨ p.natDegree < D) →
    ∃ c : (Fin M → Bool) → K, tablePoly c = p ∧ ∀ b, D ≤ idx b → c b = 0
  | 0, p, D, hD, hp => by
    refine ⟨fun _ => p.coeff 0, ?_, fun b hb => ?_⟩
    · have hc : p = C (p.coeff 0) := by
        rcases hp with rfl | h
        · simp
        · exact eq_C_of_natDegree_eq_zero (by omega)
      conv_rhs => rw [hc]
      simp [tablePoly]
    · have : D = 0 := by simp [idx] at hb; omega
      subst this
      rcases hp with rfl | h
      · simp
      · omega
  | M + 1, p, D, hD, hp => by
    obtain ⟨hmon, hdeg⟩ := digitPoly_monic_natDegree (F := K) M
    set w : K[X] := digitPoly M
    have hsplit : p %ₘ w + w * (p /ₘ w) = p := modByMonic_add_div p w
    have hlow : p %ₘ w = 0 ∨ (p %ₘ w).natDegree < 2 ^ M := by
      by_cases h0 : p %ₘ w = 0
      · exact Or.inl h0
      · right
        have := natDegree_modByMonic_lt p hmon (fun h1 => by
          rw [h1, natDegree_one] at hdeg; exact absurd hdeg.symm (by positivity))
        omega
    by_cases hDM : D ≤ 2 ^ M
    · -- The top half is empty.
      have hq : p /ₘ w = 0 := by
        rcases hp with rfl | h
        · simp
        · rw [divByMonic_eq_zero_iff hmon, degree_eq_natDegree hmon.ne_zero, hdeg]
          exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (by omega : p.natDegree < 2 ^ M))
      have hp0 : p %ₘ w = p := by
        have := hsplit
        rw [hq, mul_zero, add_zero] at this
        exact this
      obtain ⟨c₀, hc₀, hs₀⟩ := exists_table_support M (p %ₘ w) D hDM (by
        rw [hp0]; exact hp)
      refine ⟨joinTable c₀ fun _ => 0, ?_, fun b hb => ?_⟩
      · rw [tablePoly_joinTable, tablePoly_zero, mul_zero, add_zero, hc₀, hp0]
      · have e : b = Fin.snoc (Fin.init b) (b (Fin.last M)) := (Fin.snoc_init_self b).symm
        unfold joinTable
        split_ifs with hl
        · rfl
        · refine hs₀ _ ?_
          rw [Bool.not_eq_true] at hl
          rw [e, idx_snoc, hl] at hb
          simpa using hb
    · -- Both halves.
      push Not at hDM
      have hhigh : p /ₘ w = 0 ∨ (p /ₘ w).natDegree < D - 2 ^ M := by
        by_cases h0 : p /ₘ w = 0
        · exact Or.inl h0
        · right
          rcases hp with rfl | h
          · simp at h0
          · rw [natDegree_divByMonic p hmon, hdeg]
            have : 2 ^ M ≤ p.natDegree := by
              by_contra hlt
              push Not at hlt
              apply h0
              rw [divByMonic_eq_zero_iff hmon, degree_eq_natDegree hmon.ne_zero, hdeg]
              exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hlt)
            omega
      obtain ⟨c₀, hc₀, -⟩ := exists_table_support M (p %ₘ w) (2 ^ M) le_rfl hlow
      obtain ⟨c₁, hc₁, hs₁⟩ := exists_table_support M (p /ₘ w) (D - 2 ^ M)
        (by rw [pow_succ] at hD; omega) hhigh
      refine ⟨joinTable c₀ c₁, ?_, fun b hb => ?_⟩
      · rw [tablePoly_joinTable, hc₀, hc₁, hsplit]
      · have e : b = Fin.snoc (Fin.init b) (b (Fin.last M)) := (Fin.snoc_init_self b).symm
        have hlt := idx_lt (Fin.init b)
        unfold joinTable
        rw [e, idx_snoc] at hb
        split_ifs with hl
        · rw [hl] at hb
          exact hs₁ _ (by simp at hb; omega)
        · rw [Bool.not_eq_true] at hl
          rw [hl] at hb
          simp at hb
          omega

end Field

/-! ## Tables read in a larger field -/

section Map

variable {K F : Type*} [Field K] [Field F] (ι : K →+* F)

/-- **A table over `K`, read in `F`, holds the polynomial mapped to `F`.** -/
theorem tablePoly_map {M : ℕ} (c : (Fin M → Bool) → K) :
    tablePoly (fun b => ι (c b)) = (tablePoly c).map ι := by
  unfold tablePoly
  rw [Polynomial.map_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  congr 1
  refine prod_congr rfl fun k _ => ?_
  split_ifs
  · exact (digitPoly_map ι k).symm
  · simp

/-- A polynomial over `F` that is the image of one over `K`, of degree below `D ≤ 2^M`, is a
`K`-table's, vanishing from index `D` on. -/
theorem exists_table_of_lifts [CharP K 2] {M : ℕ} (p : F[X]) (hp : p ∈ lifts ι) (D : ℕ)
    (hD : D ≤ 2 ^ M) (hdeg : p = 0 ∨ p.natDegree < D) :
    ∃ c : (Fin M → Bool) → K, tablePoly (fun b => ι (c b)) = p ∧ ∀ b, D ≤ idx b → c b = 0 := by
  obtain ⟨pK, hpK⟩ := (lifts_iff_set_range p).mp hp
  have hdK : pK = 0 ∨ pK.natDegree < D := by
    rcases hdeg with h | h
    · left
      rw [← hpK] at h
      exact (Polynomial.map_eq_zero_iff ι.injective).mp h
    · right
      rw [← hpK, natDegree_map_eq_of_injective ι.injective] at h
      exact h
  obtain ⟨c, hc, hs⟩ := exists_table_support M pK D hD hdK
  exact ⟨c, by rw [tablePoly_map, hc, hpK], hs⟩

end Map

/-! ## The witness table's cells -/

section Witness

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

/-- **A first coordinate splits a polynomial's digit expansion**, as `mle_cons` does a claim. -/
theorem digitsEval_cons {m : ℕ} (c : (Fin (m + 1) → Bool) → F) (w : Fin (m + 1) → F) :
    digitsEval c w = digitsEval (fun b => c (Fin.cons false b)) (fun k => w k.succ)
      + w 0 * digitsEval (fun b => c (Fin.cons true b)) (fun k => w k.succ) := by
  unfold digitsEval
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => Bool), Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  rw [Finset.mul_sum, add_comm]
  congr 1
  · exact sum_congr rfl fun b _ => by ring
  · exact sum_congr rfl fun b _ => by ring

/-- `w_{k+2}(t) = w_k(w_2(t))`. -/
theorem sq_iterate_succ_succ (k : ℕ) (t : F) : sq^[k + 2] t = sq^[k] (sq^[2] t) :=
  Function.iterate_add_apply sq k 2 t

/-- Two first coordinates: the four quarters of a digit expansion. -/
theorem digitsEval_cons_cons {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → F) (w : Fin (k + 1 + 1) → F) :
    digitsEval c w =
      digitsEval (fun b => c (Fin.cons false (Fin.cons false b))) (fun i => w i.succ.succ)
        + w 0 * digitsEval (fun b => c (Fin.cons true (Fin.cons false b))) (fun i => w i.succ.succ)
        + w 1 * digitsEval (fun b => c (Fin.cons false (Fin.cons true b))) (fun i => w i.succ.succ)
        + w 0 * w 1 *
          digitsEval (fun b => c (Fin.cons true (Fin.cons true b))) (fun i => w i.succ.succ) := by
  rw [digitsEval_cons, digitsEval_cons (fun b => c (Fin.cons false b)),
    digitsEval_cons (fun b => c (Fin.cons true b))]
  simp only [Fin.succ_zero_eq_one]
  ring

/-- **The witness polynomial of the first message a table holds is the table's polynomial**, at
every point: the four row polynomials on `1, X, X^2 + X, (X^2 + X) X`. -/
theorem witnessPoly_witnessOfTable_eval {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → F) (t : F) :
    (Instance.witnessPoly (witnessOfTable c)).eval t = (tablePoly c).eval t := by
  have hw : (fun i : Fin k => (fun j : Fin (k + 1 + 1) => sq^[(j : ℕ)] t) i.succ.succ) =
      fun i : Fin k => sq^[(i : ℕ)] (sq^[2] t) :=
    funext fun i => by
      show sq^[(i.succ.succ : ℕ)] t = _
      rw [Fin.val_succ, Fin.val_succ]
      exact sq_iterate_succ_succ i t
  rw [tablePoly_eval, digitsEval_cons_cons, hw]
  have h0 : sq^[((0 : Fin (k + 1 + 1)) : ℕ)] t = t := rfl
  have h1 : sq^[((1 : Fin (k + 1 + 1)) : ℕ)] t = t ^ 2 + t := by
    show QuotientSecurity.sq t = t ^ 2 + t
    unfold QuotientSecurity.sq
    ring
  simp only [h0, h1]
  unfold Instance.witnessPoly
  rw [eval_finsetSum, Fin.sum_univ_four]
  have hg : ∀ (g : F[X]), (g.comp rowPoly).eval t = g.eval (sq^[2] t) := fun g => by
    rw [eval_comp, rowPoly_eval]
  simp only [eval_mul, hg]
  have d0 : (digit 0 : F[X]).eval t = 1 := by simp [digit]
  have d1 : (digit 1 : F[X]).eval t = t := by simp [digit]
  have d2 : (digit 2 : F[X]).eval t = t ^ 2 + t := by simp [digit]
  have d3 : (digit 3 : F[X]).eval t = (t ^ 2 + t) * t := by simp [digit]
  rw [d0, d1, d2, d3]
  simp only [witnessOfTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    tablePoly_eval]
  ring

variable (I : Instance F)

/-- **The cells of the first message a table holds** are the table's polynomial at the cells. -/
theorem cellsOf_witnessOfTable (c : (Fin (22 + 1 + 1 + 1) → Bool) → F)
    (x : Fin (22 + 2) → Bool) :
    I.cellsOf (witnessOfTable c) x = (tablePoly c).eval (I.basis.point x) :=
  witnessPoly_witnessOfTable_eval c _

/-- **Its masks do not reach the cells**: the cells are the first chunk's polynomial there. -/
theorem cellsOf_witnessTable (c : (Fin (22 + 1 + 1 + 1) → Bool) → F)
    (x : Fin (22 + 2) → Bool) :
    I.cellsOf (witnessOfTable c) x =
      (tablePoly fun b => c (Fin.snoc b false)).eval (I.basis.point x) := by
  rw [cellsOf_witnessOfTable, tablePoly_snoc, eval_add, eval_mul, digitPoly_eval,
    I.basis.iterate_point le24 x, zero_mul, add_zero]

end Witness

/-! ## Limbs -/

/-- **The extension over the base field**: `ι : K → F` and `Y`, every element being
`Σ_{e<3} ι(limb_e) Y^e` (`F192 = (c0, c1, c2)` on `1, Y, Y^2`). -/
structure LimbSystem (K F : Type*) [Field K] [Field F] where
  ι : K →+* F
  Y : F
  limb : F → Fin 3 → K
  decomp : ∀ x, x = ∑ e : Fin 3, ι (limb x e) * Y ^ (e : ℕ)

namespace LimbSystem

variable {K F : Type*} [Field K] [Field F] (S : LimbSystem K F)

/-- The limb polynomials of a polynomial over `F`: coefficient by coefficient. -/
noncomputable def limbPoly (p : F[X]) (e : Fin 3) : K[X] :=
  ∑ i ∈ range (p.natDegree + 1), C (S.limb (p.coeff i) e) * X ^ i

theorem coeff_limbPoly (p : F[X]) (e : Fin 3) (n : ℕ) :
    (S.limbPoly p e).coeff n = if n ≤ p.natDegree then S.limb (p.coeff n) e else 0 := by
  unfold limbPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem natDegree_limbPoly_le (p : F[X]) (e : Fin 3) : (S.limbPoly p e).natDegree ≤ p.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
    rw [coeff_limbPoly, ite_eq_right_iff.mpr fun h => absurd h (by omega)]

/-- **A polynomial is the sum of its limbs**: `p = Σ_e Y^e p_e`. -/
theorem sum_limbPoly (p : F[X]) :
    ∑ e : Fin 3, C (S.Y ^ (e : ℕ)) * (S.limbPoly p e).map S.ι = p := by
  ext n
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_map, coeff_limbPoly]
  by_cases hn : n ≤ p.natDegree
  · simp only [hn, ↓reduceIte]
    conv_rhs => rw [S.decomp (p.coeff n)]
    exact sum_congr rfl fun e _ => by ring
  · simp only [hn, ↓reduceIte, map_zero, mul_zero, sum_const_zero]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

end LimbSystem

end Completeness
