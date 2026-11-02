-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Reduce
import QuotientSecurity.PublicWeight

/-!
# `reduce`'s formulas are the model's claims

`Formula` (what the graph's outputs hold, `Reduce.lean`) against the model of
`QuotientSecurity`: on the protocol's parameters (`membershipParams`: the cells of a Cantor basis
`B`, a wiring `σ`, the region's constants `b` and weights `c`), the four claims that
`claims_iff_accepts_ofCantor` equates with `Params.Accepts`, the product the contract requires
nonzero, and the public weight, the cells, the gate and the target are `Formula`'s, given that
the graph's constants are the basis's, `b`'s, `c`'s, the rows' polynomial's and the extension's
(`Consts`; `Constants.lean` checks them by computation).

This turns the comparison written out above `claims_iff_accepts_ofCantor` (`Concrete.lean`), which
was checked by reading, into a theorem about the graph the contract is compiled from.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open Program Emitted QuotientSecurity Polynomial

local notation "SQ" => QuotientSecurity.sq

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

theorem listProd_range (f : ℕ → F) : ∀ n, ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, listProd_range f n, Finset.prod_range_succ]
    simp

theorem listSum_range (f : ℕ → F) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, listSum_range f n, Finset.sum_range_succ]
    simp

theorem foldl_add_eq {α : Type} (f : α → F) : ∀ (l : List α) (a : F),
    l.foldl (fun acc k => acc + f k) a = a + (l.map f).sum
  | [], a => by simp
  | k :: l, a => by rw [List.foldl_cons, foldl_add_eq f l, List.map_cons, List.sum_cons, add_assoc]

theorem prod_map_inv' {α : Type} (f : α → F) : ∀ l : List α,
    (l.map fun k => (f k)⁻¹).prod = ((l.map f).prod)⁻¹
  | [] => by simp
  | k :: l => by simp [prod_map_inv' f l, mul_comm]

theorem invProd_eq (I : Vals F) (s n : ℕ) :
    Formula.invProd I (List.range' s n) = (∏ i ∈ Finset.range n, (1 + SQ^[i + s] I.t))⁻¹ := by
  rw [Formula.invProd, prod_map_inv' (fun k => 1 + Formula.w I k), List.range'_eq_map_range,
    List.map_map, listProd_range]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Formula.w, Nat.add_comm]

/-- The graph's constants, as the model has them: the Cantor basis's second vector `θ`, the
region's constants `b` and weights `c`, the rows' polynomial, and the extension's `Y`. -/
structure Consts (limbs : F ≃ QuotientRpm.Limbs) {N : ℕ} (B : CantorBasis F N) (b c : ℕ → F)
    (Y : F) : Prop where
  zero : elem limbs 0 = 0
  one : elem limbs 1 = 1
  theta : elem limbs (beta.getD 1 0) = B.β 1
  theta1 : elem limbs (beta.getD 1 0 ^^^ 1) = B.β 1 + 1
  coords : ∀ e < 11, elem limbs (coords.getD e 0) = b e
  slopes : ∀ k < 8, elem limbs (slopeConst k) = 1 + c k
  tauLast : elem limbs (tau.getD 22 0) = 1
  tauSys : ∀ j : Fin (22 + 2), 2 ≤ (j : ℕ) →
    ∑ k : Fin (22 + 1), elem limbs (tau.getD k 0) * SQ^[(k : ℕ)] (B.β j) = 0
  y0 : elem limbs y0 = Y / (1 + Y)
  y1 : elem limbs y1 = Y ^ 2 / (1 + Y ^ 2)
  scale : elem limbs scale = ((1 + Y) * (1 + Y ^ 2))⁻¹
  hY : 1 + Y ≠ 0
  hY2 : 1 + Y ^ 2 ≠ 0

variable {limbs : F ≃ QuotientRpm.Limbs} {N : ℕ} {B : CantorBasis F N} {b c : ℕ → F} {Y : F}
variable (hK : Consts limbs B b c Y) (I : Vals F)
include hK

omit hK in
theorem theta_sq (hN : 2 ≤ N) : SQ (B.β 1) = 1 := by
  have h := cantor_theta B hN
  unfold QuotientSecurity.sq
  linear_combination h - (CharTwo.two_eq_zero : (2 : F) = 0)

omit hK in
theorem cellF_eq (sh : F) (second : Bool) (hsh : SQ sh = if second then 1 else 0) (n : Nat)
    (hn : elem limbs n = sh) :
    Formula.cellF limbs I n second = ∑ j, (digit j).eval (I.t + sh) * I.a j := by
  have hsq : SQ (I.t + sh) = (if second then Formula.w I 1 + 1 else Formula.w I 1) := by
    rw [sq_add, hsh]
    cases second <;> simp [Formula.w]
  have e0 : (digit (0 : Fin 4) : F[X]).eval (I.t + sh) = 1 := by simp [digit]
  have e1 : (digit (1 : Fin 4) : F[X]).eval (I.t + sh) = I.t + sh := by simp [digit]
  have e2 : (digit (2 : Fin 4) : F[X]).eval (I.t + sh) = SQ (I.t + sh) := by
    simp [digit, QuotientSecurity.sq]; ring
  have e3 : (digit (3 : Fin 4) : F[X]).eval (I.t + sh) = SQ (I.t + sh) * (I.t + sh) := by
    simp only [digit, QuotientSecurity.sq]
    simp only [Matrix.cons_val, eval_mul, eval_add, eval_pow, eval_X]
    ring
  rw [Fin.sum_univ_four, e0, e1, e2, e3, hsq, Formula.cellF, hn]
  ring

variable (hm : 22 + 2 ≤ N) (σ : Equiv.Perm (Fin (22 + 2) → Bool)) (hb0 : b 0 = 1)
  (hb : ∀ d, 1 ≤ d → d < 11 → ∑ e ∈ Finset.range (d + 1), b e * B.β (d - e) = 0)

local notation "P" => membershipParams B hm σ b c hb0 hb

theorem cells_eq : ∀ k : Fin 4, (P).cellAt I.a I.t k =
    [Formula.x limbs I, Formula.c1 limbs I, Formula.c2 limbs I, Formula.c3 limbs I].getD k 0 := by
  have hθ : (P).θ = B.β 1 := rfl
  have h2 : 2 ≤ N := by omega
  intro k
  fin_cases k
  · rw [Formula.x, cellF_eq I 0 false (by simp [QuotientSecurity.sq]) 0 hK.zero]
    simp [Params.cellAt, shift]
  · rw [Formula.c1, cellF_eq I 1 false (by simp [QuotientSecurity.sq, CharTwo.add_self_eq_zero]) 1
      hK.one]
    simp [Params.cellAt, shift]
  · rw [Formula.c2, cellF_eq I (B.β 1) true (by simpa using theta_sq h2) _ hK.theta]
    simp [Params.cellAt, shift, hθ]
  · rw [Formula.c3, cellF_eq I (B.β 1 + 1) true
      (by rw [sq_add, theta_sq h2]; simp [QuotientSecurity.sq, CharTwo.add_self_eq_zero]) _ hK.theta1]
    simp [Params.cellAt, shift, hθ]

theorem gate_eq : gate ((P).cellAt I.a I.t 0) ((P).cellAt I.a I.t 1) ((P).cellAt I.a I.t 2)
    ((P).cellAt I.a I.t 3) = Formula.gate limbs I := by
  simp only [cells_eq hK I hm σ hb0 hb]
  simp [gate, Formula.gate]

include hb0 in
omit hK in
theorem coord_eq' (hc : ∀ e < 11, elem limbs (coords.getD e 0) = b e) (k : ℕ) (hk : k < 11) :
    Formula.coord limbs I k = (coordPoly b 11 k).eval I.t := by
  rw [coordPoly_eval, Formula.coord, foldl_add_eq, Finset.sum_eq_sum_Ico_succ_bot hk]
  rw [Nat.sub_self, hb0, one_mul]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range, List.range'_eq_map_range, List.map_map, listSum_range]
  refine Finset.sum_congr (by congr 1) fun j hj => ?_
  have hj' : j < 11 - (k + 1) := Finset.mem_range.mp hj
  simp only [Function.comp, Formula.w]
  rw [hc _ (by omega), show k + 1 + j - k = j + 1 by omega]

theorem pub_eq : Formula.pub limbs I = ((P).pub I.γ).eval I.t := by
  show _ = (pubProd b (regionMu c) 11 (22 + 2) I.γ).eval I.t
  rw [pubProd, eval_mul, hiPoly, eval_prod, eval_prod, Formula.pub, foldl_mul_eq, foldl_mul_eq,
    one_mul, ← listProd_range, Finset.prod_Ico_eq_prod_range, ← listProd_range,
    List.range'_eq_map_range, List.map_map]
  congr 1
  · refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
    simp [Formula.w, digitPoly_eval]
  · refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
    have hk' : k < 11 := List.mem_range.mp hk
    rw [eval_add, eval_one, eval_mul, eval_C, ← coord_eq' I hb0 hK.coords k hk', Formula.slope,
      regionMu]
    split_ifs with h8
    · rw [hK.slopes k h8]
    · have : k - 8 < 3 := by omega
      interval_cases hk8 : k - 8 <;>
        simp only [Formula.gammas, List.getD_cons_zero, List.getD_cons_succ] <;> ring

omit hK in
theorem target_eq : (P).target ![I.s 0, I.s 1, I.s 2, I.s 3, 1, 0, 0, 0] I.γ = Formula.target I := by
  rw [membership_target, Formula.target]
  ring

theorem rows_eq : Formula.rows limbs I = (P).vRows.eval I.t := by
  have e := rowsPoly_eq_vRows B hm σ 8 _ _ (membershipPub_hPub B b c hm hb0 hb)
    (fun k => elem limbs (tau.getD k 0)) hK.tauLast (fun j hj => by
      rw [rowsPoly_eval]; exact hK.tauSys j hj)
  rw [show (P).vRows = rowsPoly (n := 22) (fun k => elem limbs (tau.getD k 0)) from e.symm,
    rowsPoly_eval, Formula.rows, foldl_add_eq, zero_add, listSum_range,
    ← Fin.sum_univ_eq_sum_range (fun k => elem limbs (tau.getD k 0) * Formula.w I k)]
  rfl

/-- **The product the contract requires nonzero** is that of every `1 + w_k(t)` and the
denominator `Params.Accepts` asks nonzero. -/
theorem check_eq : Formula.check limbs I =
    (∏ k ∈ Finset.range 26, (1 + SQ^[k] I.t)) * ((P).claimDen I.α I.β I.t I.a I.next *
      (P).vRows.eval I.t) := by
  rw [Formula.check, Formula.dens, List.prod_append, listProd_range, ← rows_eq hK I hm σ hb0 hb]
  simp only [List.prod_cons, List.prod_nil, mul_one, Params.claimDen, Formula.product, Formula.d,
    Formula.dNext, Formula.w]
  have hx := cells_eq hK I hm σ hb0 hb 0
  simp only [List.getD_cons_zero, Fin.isValue, Fin.val_zero] at hx
  have hv : (P).vCells = digitPoly 24 := rfl
  rw [hx, hv, digitPoly_eval]
  try ring

/-! ## The four claims -/

omit hK [DecidableEq F] [CharP F 2] in
theorem ofFn_snoc {n : ℕ} (g : Fin n → F) (x : F) :
    List.ofFn (Fin.snoc g x : Fin (n + 1) → F) = List.ofFn g ++ [x] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

omit hK [DecidableEq F] [CharP F 2] in
theorem ofFn_cons {n : ℕ} (g : Fin n → F) (x : F) :
    List.ofFn (Fin.cons x g : Fin (n + 1) → F) = x :: List.ofFn g := by
  rw [List.ofFn_succ]
  simp

omit hK in
theorem ofFn_claimPoint (s n : ℕ) (t : F) :
    List.ofFn (claimPoint s n t) = (List.range n).map fun k => SQ^[k + s] t / (1 + SQ^[k + s] t) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [claimPoint]

omit hK in
theorem claimScale_eq (s n : ℕ) (t : F) :
    claimScale s n t = ∏ i ∈ Finset.range n, (1 + SQ^[i + s] t) := by
  rw [claimScale, Fin.prod_univ_eq_prod_range (fun i => 1 + SQ^[i + s] t)]

variable (P' : Params F)

/-- The witness table's claim, as `claims_iff_accepts_ofCantor` states it: point, then value. -/
noncomputable def modelWitness (t ρ : F) (a : Fin 4 → F) : List F :=
  List.ofFn (Fin.cons ρ (Fin.cons (ρ ^ 2) (claimPoint 2 (22 + 1) t)) : Fin (22 + 1 + 1 + 1) → F) ++
    [(∑ j, Params.opening ρ j * a j) / claimScale 2 (22 + 1) t]

/-- The wiring table's claim. -/
noncomputable def modelWiring (t s : F) : List F :=
  List.ofFn (claimPoint 0 (22 + 2) t) ++ [s / claimScale 0 (22 + 2) t]

/-- The quotient table's first claim. -/
noncomputable def modelQuotient (α β γ t ρ s Y : F) (a : Fin 4 → F) : List F :=
  List.ofFn (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) t)
      (P'.vCells.eval t / P'.claimDen α β t a s)) ρ) (Y / (1 + Y))) (Y ^ 2 / (1 + Y ^ 2)) :
      Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → F) ++
    [P'.claimValue α β γ t ρ a s / ((1 + Y) * (1 + Y ^ 2)) / claimScale 0 (22 + 2 + 1 + 1) t]

/-- The quotient table's claim at the fixed point. -/
noncomputable def modelSum (stmt : Fin P'.words → F) (γ Y : F) : List F :=
  List.ofFn (sumPoint (22 + 2) Y) ++ [P'.target stmt γ / ((1 + Y) * (1 + Y ^ 2))]

omit hK in
theorem u_eq (k : ℕ) : Formula.u I k = SQ^[k] I.t / (1 + SQ^[k] I.t) := by
  rw [Formula.u, div_eq_mul_inv]; rfl

omit hK in
theorem opened_eq : Formula.opened I = ∑ j, Params.opening I.ρ j * I.a j := by
  simp only [Formula.opened, Fin.sum_univ_four, Params.opening]
  simp
  ring

omit hK in
/-- **The witness claim the graph passes is the model's.** -/
theorem witness_eq : Formula.witness I = modelWitness I.t I.ρ I.a := by
  rw [Formula.witness, modelWitness, ofFn_cons, ofFn_cons, ofFn_claimPoint, claimScale_eq,
    invProd_eq, opened_eq, div_eq_mul_inv]
  simp only [u_eq, pow_two]
  rfl

omit hK in
/-- **The wiring claim the graph passes is the model's.** -/
theorem wiring_eq : Formula.wiring I = modelWiring I.t I.next := by
  rw [Formula.wiring, modelWiring, ofFn_claimPoint, claimScale_eq, List.range_eq_range' (n := 24),
    invProd_eq, div_eq_mul_inv]
  simp only [Nat.add_zero, ← List.range_eq_range']
  exact congrArg₂ (· ++ ·) (List.map_congr_left fun k _ => by rw [u_eq]) rfl

/-- **The quotient table's first claim the graph passes is the model's.** -/
theorem quotient_eq : Formula.quotient limbs I =
    modelQuotient (P) I.α I.β I.γ I.t I.ρ I.next Y I.a := by
  have hx := cells_eq hK I hm σ hb0 hb 0
  simp only [List.getD_cons_zero, Fin.isValue, Fin.val_zero] at hx
  have hv : (P).vCells = digitPoly 24 := rfl
  have hden : (P).claimDen I.α I.β I.t I.a I.next = Formula.product limbs I + Formula.w I 24 := by
    rw [Params.claimDen, hx, hv, digitPoly_eval]; rfl
  have hc : (P).claimValue I.α I.β I.γ I.t I.ρ I.a I.next = Formula.identities limbs I /
      ((Formula.product limbs I + Formula.w I 24) * Formula.rows limbs I) := by
    rw [Params.claimValue, gate_eq hK I hm σ hb0 hb, hden, ← rows_eq hK I hm σ hb0 hb, hx,
      ← pub_eq hK I hm σ hb0 hb]
    simp only [Formula.identities, Formula.copies, Formula.product, Formula.d, Formula.dNext]
  have hval : (P).claimValue I.α I.β I.γ I.t I.ρ I.a I.next / ((1 + Y) * (1 + Y ^ 2)) /
      claimScale 0 (22 + 2 + 1 + 1) I.t = elem limbs scale * Formula.invProd I (List.range 26) *
        (Formula.product limbs I + Formula.w I 24)⁻¹ * (Formula.rows limbs I)⁻¹ *
          Formula.identities limbs I := by
    rw [claimScale_eq, List.range_eq_range' (n := 26), invProd_eq, hK.scale, hc]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hpt : Formula.w I 24 * (Formula.product limbs I + Formula.w I 24)⁻¹ =
      (P).vCells.eval I.t / (P).claimDen I.α I.β I.t I.a I.next := by
    rw [hden, hv, digitPoly_eval, div_eq_mul_inv]; rfl
  rw [Formula.quotient, modelQuotient, ofFn_snoc, ofFn_snoc, ofFn_snoc, ofFn_snoc, ofFn_claimPoint,
    hval, hpt, hK.y0, hK.y1]
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  rw [u_eq, Nat.add_zero]

omit hK in
/-- **The sum's value the graph passes is the model's.** -/
theorem sum_eq (hs : elem limbs scale = ((1 + Y) * (1 + Y ^ 2))⁻¹) :
    Formula.sum limbs I =
      (P).target ![I.s 0, I.s 1, I.s 2, I.s 3, 1, 0, 0, 0] I.γ / ((1 + Y) * (1 + Y ^ 2)) := by
  rw [Formula.sum, target_eq, hs, div_eq_mul_inv, mul_comm]

end Implementation
