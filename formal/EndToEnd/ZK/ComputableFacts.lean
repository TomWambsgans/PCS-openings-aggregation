-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses Mathlib's Lagrange interpolation (`Mathlib/LinearAlgebra/Lagrange.lean`, Apache-2.0):
-- `Lagrange.interpolate`, `Lagrange.nodal`, `eq_interpolate_of_eval_eq`,
-- `eval_nodal_derivative_eval_node_eq`. `bitsN`, `idx_bitsN`, `bitsN_idx` transcribe `bitsOf`, `idx_bitsOf`,
-- `bitsOf_idx` of `formal/Completeness/Completeness/Read.lean` (whose imports this workspace does not build).
import ZK.FactsF1
import QuotientZk.Instance.Compiled

/-!
# The deployed parameters' public polynomials, evaluated by compiled definitions

The view simulator evaluates five public polynomials of the deployed parameters `P₀D` (Mathlib
polynomials, so `noncomputable`): `v_cells`, `v_rows`, the public weight `pub(γ)` at the challenge
`t`, `θ`, and **the wiring polynomial `σ(t)`** (the simulated wiring value). Each is given here by a
compiled definition with its cost, and proved equal to the polynomial's evaluation:

* `θ = β₁` (`peD_matches.θ`, by definition) and `v_cells(t) = S^24(t)` (`digitPoly_eval`): `24`
  squarings;
* **`rowsAtC`**: `v_rows(t) = Π_{x ∈ T} (t − x)` over the `2^22` rows `x` (the `X` cells, role bits
  zero), a left fold of `2^22` products; each row's point is `24` additions in `K` (`rowsAtC_eq`);
* **`pubAtC`**: `pub(γ)(t) = Π_{j ∈ [11, 24)} (1 + S^j(t)) · Π_{k < 11} (1 + (Σ_{j ∈ [k, 11)}
  b_{j−k} S^j(t)) (1 + μ_k(γ)))`, the region's coordinates `b = invSeq β` (`invSeqC`) and weights
  `μ` (`regionMu`); about `2·10^3` operations (`pubAtC_eq`);
* **`sigmaAtC`**: `σ(t)`. The wiring polynomial has degree `< 2^24` and takes, at the point `v_p` of
  each cell `p < 2^24`, the point `r_p` of its successor (`membership.sigma`); it is the Lagrange
  interpolant on the cells (`eq_interpolate_of_eval_eq`), and on the span of a Cantor basis the
  nodal polynomial is `S^24` (`nodal_cells`), whose derivative is `1` (characteristic two,
  `derivative_digitPoly`): every barycentric weight is `1` (`prod_cell_sub`). So
  `σ(t) = Σ_p r_p Π_{q ≠ p} (t − v_q)`, accumulated as `(N, D) ↦ (N (t − v_p) + r_p D, D (t − v_p))`
  over the `2^24` cells (`lagAcc`, `lagAcc_eq`, `eval_eq_lagAcc`): `3 · 2^24` products in `E`, the
  cells' points `2 · 24 · 2^24` additions in `K`, no inversion (`sigmaAtC_eq`).

The interpolation is proved for any cube of `m` bits of a Cantor basis of any field of
characteristic two, and instantiated. The heavy definitions are `@[irreducible]`: their bodies are
loops over `2^22` or `2^24` entries, which elaboration must never unfold.
-/

open Polynomial QuotientSecurity Primitives Finset
open LeanVM.Parameters

namespace PcsQuotient.EndToEnd

set_option linter.unusedSectionVars false

/-! ## Products as left folds -/

section Folds

variable {F : Type} [CommMonoid F]

/-- `Π_{i < n} f i`, a left fold over `0 … n − 1` (no recursion depth). -/
@[irreducible] def prodRange (n : ℕ) (f : ℕ → F) : F := (List.range n).foldl (fun a i => a * f i) 1

theorem prodRange_succ (n : ℕ) (f : ℕ → F) : prodRange (n + 1) f = prodRange n f * f n := by
  simp only [prodRange, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem prodRange_eq (n : ℕ) (f : ℕ → F) : prodRange n f = ∏ i ∈ range n, f i := by
  induction n with
  | zero => rw [prodRange]; rfl
  | succ n ih => rw [prodRange_succ, ih, prod_range_succ]

end Folds

/-! ## Cube points by numbers -/

/-- The cube point of a number: its bits (`bitsN`). -/
def bitsN (V n : ℕ) : Fin V → Bool := fun k => n.testBit k

theorem bitsN_succ (V n : ℕ) :
    bitsN (V + 1) n = Fin.cons (n.testBit 0) (bitsN V (n / 2)) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · simp only [bitsN, Fin.cons_succ, Fin.val_succ]
    rw [← Nat.testBit_div_two]

theorem idx_bitsN : ∀ (V n : ℕ), n < 2 ^ V → Completeness.idx (bitsN V n) = n
  | 0, n, h => by simp [Completeness.idx]; omega
  | V + 1, n, h => by
    have h2 : n / 2 < 2 ^ V := by
      rw [pow_succ, mul_comm] at h
      exact Nat.div_lt_of_lt_mul h
    rw [bitsN_succ, Completeness.idx_cons, idx_bitsN V (n / 2) h2]
    have := Nat.mod_add_div n 2
    simp only [Nat.testBit_zero, decide_eq_true_eq]
    split_ifs with h1 <;> omega

theorem testBit_idxN : ∀ {V : ℕ} (b : Fin V → Bool) (k : Fin V), (Completeness.idx b).testBit k = b k
  | 0, _, k => k.elim0
  | V + 1, b, k => by
    obtain ⟨x, c, rfl⟩ : ∃ x c, b = Fin.cons x c := ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
    rw [Completeness.idx_cons]
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Fin.val_zero, Fin.cons_zero, Nat.testBit_zero]
      cases x <;> simp
    · simp only [Fin.val_succ, Fin.cons_succ, Nat.testBit_succ]
      have : ((if x = true then 1 else 0) + 2 * Completeness.idx c) / 2 = Completeness.idx c := by
        split_ifs <;> omega
      rw [this, testBit_idxN]

theorem bitsN_idx {V : ℕ} (b : Fin V → Bool) : bitsN V (Completeness.idx b) = b :=
  funext fun k => testBit_idxN b k

/-! ## The points of the deployed basis -/

/-- A cube point of the basis `deployedBasis.map ι` is the image of the point over `K`. -/
theorem point_map_K {m : ℕ} (x : Fin m → Bool) :
    (deployedBasis.map (algebraMap K E)).point x = algebraMap K E (deployedBasis.point x) := by
  unfold CantorBasis.point
  rw [map_sum]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [CantorBasis.map]

theorem instD_basis_eq : instD.basis = deployedBasis.map (algebraMap K E) := rfl

/-! ## `θ`, `v_cells` -/

theorem P₀D_θ : P₀D.θ = algebraMap K E (betaF64 1) := rfl

theorem P₀D_vCells (t : E) : P₀D.vCells.eval t = sq^[22 + 2] t := digitPoly_eval (22 + 2) t

/-! ## `v_rows` -/

/-- **Row `r`'s point** over `K` (the `X` cell of row `r`). -/
def rowPtK (r : ℕ) : K := deployedBasis.point (cellBits (bitsN 22 r, 0))

/-- **`v_rows(t)`, compiled**: `Π_{r < 2^22} (t − x_r)`. -/
@[irreducible] def rowsAtC (t : E) : E := prodRange (2 ^ 22) fun r => t - algebraMap K E (rowPtK r)

theorem prod_cube_eq_range {M : ℕ} (g : (Fin M → Bool) → E) :
    ∏ y : Fin M → Bool, g y = ∏ r ∈ range (2 ^ M), g (bitsN M r) := by
  refine (prod_nbij' (fun y => Completeness.idx y) (fun r => bitsN M r) ?_ ?_ ?_ ?_ ?_)
  · intro y _
    exact mem_range.mpr (Completeness.idx_lt y)
  · intro r _
    exact mem_univ _
  · intro y _
    exact bitsN_idx y
  · intro r hr
    exact idx_bitsN M r (mem_range.mp hr)
  · intro y _
    rw [bitsN_idx]

/-- **`rowsAtC` is `v_rows(t)`.** -/
theorem rowsAtC_eq (t : E) : rowsAtC t = P₀D.vRows.eval t := by
  have hv : P₀D.vRows = ∏ x : cantorT instD.basis 22, (X - C (x : E)) :=
    Completeness.Instance'.vRows_eq instD
  have hinj : Set.InjOn (fun y : Fin 22 → Bool => instD.basis.point (cellBits (y, 0)))
      (univ : Finset (Fin 22 → Bool)) := by
    intro y _ y' _ h
    have h' := instD.basis.point_injective (m := 22 + 2) le_rfl h
    exact (Prod.mk.inj (cellBits.injective h')).1
  rw [hv, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [prod_coe_sort (cantorT instD.basis 22) (fun x => t - x), cantorT, prod_image hinj,
    prod_cube_eq_range, rowsAtC, prodRange_eq]
  refine prod_congr rfl fun r _ => ?_
  rw [rowPtK, ← point_map_K, instD_basis_eq]

/-! ## The public weight -/

/-- `invSeq`, compiled (the region's coordinates `b`, `domain::coordinates`). -/
def invSeqC (β : ℕ → E) : ℕ → E
  | 0 => 1
  | d + 1 => ∑ e : Fin (d + 1), invSeqC β e * β (d + 1 - e)
decreasing_by exact e.2

theorem invSeqC_eq (β : ℕ → E) : invSeqC β = invSeq β := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [invSeqC, invSeq]
    | succ d =>
      rw [invSeqC, invSeq]
      exact sum_congr rfl fun e _ => by rw [ih e (by omega)]

/-- The basis's vectors in `E`. -/
def betaE (k : ℕ) : E := algebraMap K E (betaF64 k)

/-- **The public weight `pub(γ)(t)`, compiled.** -/
@[irreducible] def pubAtC (γ t : E) : E :=
  (∏ j ∈ Ico 11 (22 + 2), (1 + sq^[j] t)) *
    ∏ k ∈ range 11, (1 + (∑ j ∈ Ico k 11, invSeqC betaE (j - k) * sq^[j] t) *
      (1 + regionMu (coordWeight F192.G F192.Y) k γ))

/-- **`pubAtC` is `pub(γ)` at `t`.** -/
theorem pubAtC_eq (γ t : E) : pubAtC γ t = (P₀D.pub γ).eval t := by
  show _ = (pubProd (invSeq instD.basis.β) (regionMu instD.c) 11 (22 + 2) γ).eval t
  rw [pubProd, eval_mul, hiPoly, eval_prod, eval_prod]
  simp only [eval_add, eval_one, eval_mul, eval_C, digitPoly_eval, coordPoly_eval]
  have hb : instD.basis.β = betaE := rfl
  have hc : instD.c = coordWeight F192.G F192.Y := rfl
  rw [pubAtC, invSeqC_eq, hb, hc]

/-! ## The wiring polynomial

The interpolation is proved over any field `F` of characteristic two with a Cantor basis `B` (every
instance then comes from the one `Field F`), and applied to `E` and the deployed basis. -/

section Lagrange

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

/-- **The barycentric accumulation**: over `i < n`, `(N, D) ↦ (N (t − v_i) + r_i D, D (t − v_i))`
from `(0, 1)`. -/
@[irreducible] def lagAcc (t : F) (v r : ℕ → F) (n : ℕ) : F × F :=
  (List.range n).foldl (fun a i => (a.1 * (t - v i) + r i * a.2, a.2 * (t - v i))) (0, 1)

theorem lagAcc_eq (t : F) (v r : ℕ → F) : ∀ n, lagAcc t v r n =
    (∑ i ∈ range n, r i * ∏ j ∈ (range n).erase i, (t - v j), ∏ j ∈ range n, (t - v j))
  | 0 => by rw [lagAcc]; rfl
  | n + 1 => by
    have hstep : lagAcc t v r (n + 1) =
        ((lagAcc t v r n).1 * (t - v n) + r n * (lagAcc t v r n).2,
          (lagAcc t v r n).2 * (t - v n)) := by
      simp only [lagAcc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlast : (range (n + 1)).erase n = range n := by
      rw [range_add_one, erase_insert (by simp)]
    have hrest : ∀ i ∈ range n, ∏ j ∈ (range (n + 1)).erase i, (t - v j) =
        (∏ j ∈ (range n).erase i, (t - v j)) * (t - v n) := by
      intro i hi
      have hin : i ≠ n := (mem_range.mp hi).ne
      rw [range_add_one, erase_insert_of_ne hin.symm, prod_insert (by simp), mul_comm]
    have hsum : ∑ i ∈ range (n + 1), r i * ∏ j ∈ (range (n + 1)).erase i, (t - v j) =
        (∑ i ∈ range n, r i * ∏ j ∈ (range n).erase i, (t - v j)) * (t - v n) +
          r n * ∏ j ∈ range n, (t - v j) := by
      rw [sum_range_succ, hlast, sum_mul]
      refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) rfl
      rw [hrest i hi, mul_assoc]
    rw [hstep, lagAcc_eq t v r n, hsum, prod_range_succ]

/-- In characteristic two, `S^k` has derivative `1`. -/
theorem derivative_digitPoly : ∀ k, derivative (digitPoly k : F[X]) = 1
  | 0 => by simp [digitPoly]
  | k + 1 => by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [digitPoly, derivative_comp, derivative_digitPoly k, one_mul, derivative_add,
      derivative_X_pow, derivative_X]
    simp [h2]

theorem cellOf_eq_bitsN (p : ℕ) : cellOf p = bitsN (22 + 2) p := rfl

/-! The cube's size `m` is a variable here: at a numeral (`2^24` cells) the kernel would unfold
`range (2^24)` when it compares the lemmas' statements. -/

variable {N : ℕ} (B : CantorBasis F N) (m : ℕ) (hm : m ≤ N)
include hm

/-- The cells' points `v_p = B(bits p)`, `p < 2^m`, are distinct. -/
theorem cell_injOn :
    Set.InjOn (fun p => B.point (bitsN m p)) (range (2 ^ m) : Finset ℕ) := by
  intro p hp q hq h
  have h' := B.point_injective hm h
  have := congrArg Completeness.idx h'
  rwa [idx_bitsN _ _ (mem_range.mp hp), idx_bitsN _ _ (mem_range.mp hq)] at this

/-- **The nodal polynomial of the cells is `S^m`**: both monic of degree `2^m`, both zero at the
`2^m` cells. -/
theorem nodal_cells :
    Lagrange.nodal (range (2 ^ m)) (fun p => B.point (bitsN m p)) = digitPoly m := by
  have hdd := digitPoly_monic_natDegree (F := F) m
  refine eq_of_degree_sub_lt_of_eval_index_eq _ (cell_injOn B m hm) ?_ ?_
  · refine lt_of_lt_of_eq (degree_sub_lt ?_ Lagrange.nodal_ne_zero ?_) Lagrange.degree_nodal
    · rw [Lagrange.degree_nodal, degree_eq_natDegree hdd.1.ne_zero, hdd.2, card_range]
    · rw [Lagrange.nodal_monic.leadingCoeff, hdd.1.leadingCoeff]
  · intro p hp
    rw [show (Lagrange.nodal (range (2 ^ m)) fun p => B.point (bitsN m p)).eval
        (B.point (bitsN m p)) = 0 from
        Lagrange.eval_nodal_at_node (v := fun p => B.point (bitsN m p)) hp,
      digitPoly_eval, B.iterate_point hm]

/-- **Every barycentric weight is one**: `Π_{q ≠ p} (v_p − v_q) = 1`. -/
theorem prod_cell_sub (p : ℕ) (hp : p ∈ range (2 ^ m)) :
    ∏ q ∈ (range (2 ^ m)).erase p, (B.point (bitsN m p) - B.point (bitsN m q)) = 1 := by
  have h := Lagrange.eval_nodal_derivative_eval_node_eq (v := fun p => B.point (bitsN m p)) hp
  rw [nodal_cells B m hm, derivative_digitPoly, eval_one, Lagrange.eval_nodal] at h
  exact h.symm

theorem eval_basis_cells (t : F) (p : ℕ) (hp : p ∈ range (2 ^ m)) :
    (Lagrange.basis (range (2 ^ m)) (fun p => B.point (bitsN m p)) p).eval t =
      ∏ q ∈ (range (2 ^ m)).erase p, (t - B.point (bitsN m q)) := by
  rw [Lagrange.basis, eval_prod]
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  rw [prod_mul_distrib, prod_inv_distrib, prod_cell_sub B m hm p hp, inv_one, one_mul]

/-- **A polynomial of degree `< 2^m` is the barycentric accumulation of its values at the cells.** -/
theorem eval_eq_lagAcc (f : F[X]) (hf : f.natDegree < 2 ^ m) (r : ℕ → F)
    (hr : ∀ p ∈ range (2 ^ m), f.eval (B.point (bitsN m p)) = r p) (t : F) :
    f.eval t = (lagAcc t (fun p => B.point (bitsN m p)) r (2 ^ m)).1 := by
  have hdeg : f.degree < ↑(range (2 ^ m)).card :=
    (degree_le_natDegree).trans_lt (by rw [card_range]; exact_mod_cast hf)
  rw [Lagrange.eq_interpolate_of_eval_eq (r := r) (cell_injOn B m hm) hdeg hr, lagAcc_eq,
    Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun p hp => ?_
  rw [eval_mul, eval_C, eval_basis_cells B m hm t p hp]

end Lagrange

/-! ### The deployed wiring -/

/-- The cells' points: cell `p`'s, `p < 2^24`. -/
def nodeE (p : ℕ) : E := algebraMap K E (deployedBasis.point (cellOf p))

theorem nodeE_fun : nodeE = fun p => instD.basis.point (bitsN (22 + 2) p) := by
  funext p
  rw [nodeE, ← point_map_K, instD_basis_eq, cellOf_eq_bitsN]

/-- The successors' points: `r_p`, the point of `σ(p)` (`membership.sigma`). -/
def succE (p : ℕ) : E :=
  algebraMap K E (deployedBasis.point (cellOf (PcsCircuit.membership.sigma.getD p 0)))

/-- A pair's first component, opaque: `sigmaAtC`'s body is not a projection, which the equation
compiler would reduce (running the accumulation) when it states `sigmaAtC`'s equation. -/
@[irreducible] def accNum (a : E × E) : E := a.1

/-- **`σ(t)`, compiled**: the barycentric accumulation over the `2^24` cells. -/
@[irreducible] def sigmaAtC (t : E) : E := accNum (lagAcc t nodeE succE (2 ^ (22 + 2)))

theorem sigmaPoly_eq_table :
    P₀D.sigmaPoly = tablePoly (wiringTable instD.basis le24 deployedSigma) :=
  Completeness.Instance'.sigmaPoly_eq instD

theorem sigmaPoly_natDegree_lt : P₀D.sigmaPoly.natDegree < 2 ^ (22 + 2) := by
  rw [sigmaPoly_eq_table]
  exact natDegree_tablePoly_lt _

theorem sigmaPoly_eval_cell (p : ℕ) (hp : p ∈ range (2 ^ (22 + 2))) :
    P₀D.sigmaPoly.eval (instD.basis.point (bitsN (22 + 2) p)) = succE p := by
  rw [← cellOf_eq_bitsN, sigmaPoly_eq_table, wiringTable_eval,
    deployedSigma_cellOf (mem_range.mp hp), succE, ← point_map_K, instD_basis_eq]

/-- **`sigmaAtC` is the wiring polynomial's value.** -/
theorem sigmaAtC_eq (t : E) : sigmaAtC t = P₀D.sigmaPoly.eval t := by
  rw [sigmaAtC, accNum, nodeE_fun]
  exact (eval_eq_lagAcc instD.basis (22 + 2) le_rfl P₀D.sigmaPoly sigmaPoly_natDegree_lt succE
    sigmaPoly_eval_cell t).symm


/-! ## The public evaluations of `P₀D` -/

/-- **The deployed public evaluations.** -/
def peD : QuotientZk.Instance.Compiled.PubEval E :=
  ⟨algebraMap K E (betaF64 1), fun t => sq^[22 + 2] t, rowsAtC, pubAtC⟩

theorem peD_matches : peD.Matches P₀D where
  θ := P₀D_θ.symm
  vCells t := (P₀D_vCells t).symm
  vRows := rowsAtC_eq
  pub := pubAtC_eq

/-- **The statement's words, compiled** (`stmtWD`). -/
def stmtWDc (stmt : Statement) : Fin 8 → E :=
  QuotientSecurity.statementWords F192.G F192.Y (fun i => stmt.y[i]) (fun i => stmt.root[i])

theorem stmtWDc_eq (stmt : Statement) : stmtWDc stmt = stmtWD stmt := rfl

/-- **The statement's target** `Σ_J γ^J w_J`. -/
def tgtD (stmt : Statement) (γ : E) : E := ∑ J : Fin 8, γ ^ (J : ℕ) * stmtWDc stmt J

theorem tgtD_eq (stmt : Statement) (γ : E) : tgtD stmt γ = P₀D.target (stmtWD stmt) γ := rfl

end PcsQuotient.EndToEnd

/-! ## Axioms -/

/-- info: 'PcsQuotient.EndToEnd.rowsAtC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.rowsAtC_eq

/-- info: 'PcsQuotient.EndToEnd.pubAtC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.pubAtC_eq

/-- info: 'PcsQuotient.EndToEnd.sigmaAtC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.sigmaAtC_eq

/-- info: 'PcsQuotient.EndToEnd.peD_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.peD_matches
