-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Concrete.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Assembly
import QuotientSecurity.Instance
import QuotientSecurity.CantorExists
import QuotientSecurity.RandomOracle

/-!
# The parameters of `flock::quotient` on a Cantor basis

The cells are the span of the first `n + 2` vectors of a Cantor basis, a row's four cells the
shifts by `0, 1, θ, θ + 1` with `θ` the second vector. This file builds `Params` on them, with
the cells' vanishing polynomial the basis's digit and the wiring polynomial the one a table
holds, so the hypotheses of `claims_iff_accepts` and the sizes of the `_bits` theorems are met by
an instance rather than assumed.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]

/-! ## Points of a Cantor basis -/

section Basis

variable {N : ℕ} (B : CantorBasis F N)

/-- Distinct bits are distinct points. -/
theorem CantorBasis.point_injective {m : ℕ} (hm : m ≤ N) :
    Function.Injective (B.point : (Fin m → Bool) → F) := by
  intro x x' h
  by_contra hne
  have hS : (univ.filter fun k : Fin m => x k ≠ x' k).Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    refine hne (funext fun k => ?_)
    by_contra hk
    have : k ∈ univ.filter fun k : Fin m => x k ≠ x' k := by simp [hk]
    rw [he] at this
    exact absurd this (Finset.notMem_empty _)
  set k := (univ.filter fun k : Fin m => x k ≠ x' k).max' hS with hk
  have hmem := Finset.max'_mem _ hS
  rw [← hk, Finset.mem_filter] at hmem
  have habove : ∀ j, k < j → x j = x' j := by
    intro j hj
    by_contra hj'
    have : j ∈ univ.filter fun k : Fin m => x k ≠ x' k := by simp [hj']
    exact absurd (Finset.le_max' _ j this) (not_le.mpr hj)
  have h1 := B.digit_eq hm k x
  have h2 := B.digit_eq hm k x'
  rw [h, h2, B.above_congr k x x' habove] at h1
  have h3 := add_right_cancel h1
  refine hmem.2 ?_
  cases hx : x k <;> cases hx' : x' k <;> simp [hx, hx'] at h3 ⊢

/-- **A table's polynomial is determined by its values on the cells.** -/
theorem CantorBasis.tablePoly_ext {m : ℕ} (hm : m ≤ N) (c c' : (Fin m → Bool) → F)
    (h : ∀ x : Fin m → Bool,
      (tablePoly c).eval (B.point x) = (tablePoly c').eval (B.point x)) :
    tablePoly c = tablePoly c' := by
  rw [← sub_eq_zero, ← tablePoly_sub]
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (B.point_injective hm) (fun x => ?_) ?_
  · rw [tablePoly_sub, eval_sub, h, sub_self]
  · simpa using natDegree_tablePoly_lt (c - c')

/-- The digit above the last vanishes on the points. -/
theorem CantorBasis.iterate_point {m : ℕ} (hm : m ≤ N) (x : Fin m → Bool) :
    sq^[m] (B.point x) = 0 := by
  unfold CantorBasis.point
  rw [sq_iterate_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs
  · rw [B.iterate _ _ (lt_of_lt_of_le j.2 hm)]
    simp [not_le.mpr j.2]
  · exact sq_iterate_zero _

end Basis

/-- A digit is monic, of degree its power of two. -/
theorem digitPoly_monic_natDegree (k : ℕ) :
    (digitPoly k : F[X]).Monic ∧ (digitPoly k : F[X]).natDegree = 2 ^ k := by
  induction k with
  | zero => exact ⟨by simp [digitPoly, monic_X], by simp [digitPoly]⟩
  | succ k ih =>
    obtain ⟨hmon, hdeg⟩ := ih
    have e : (digitPoly (k + 1) : F[X]) = digitPoly k ^ 2 + digitPoly k := by simp [digitPoly]
    have h2 : (digitPoly k ^ 2 : F[X]).natDegree = 2 ^ (k + 1) := by
      rw [hmon.natDegree_pow, hdeg]; ring
    have hlt : (digitPoly k : F[X]).natDegree < (digitPoly k ^ 2 : F[X]).natDegree := by
      rw [h2, hdeg]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [e]
    exact ⟨(hmon.pow 2).add_of_left (degree_lt_degree hlt),
      by rw [natDegree_add_eq_left_of_natDegree_lt hlt, h2]⟩

/-! ## Every function on the cells is a table's polynomial -/

/-- Triangular digits interpolate: any values on the cells are those of some coefficients. -/
theorem exists_digitsEval : ∀ (m : ℕ) (g : Fin m → (Fin m → Bool) → F)
    (_hg : ∀ k x x', (∀ j, k < j → x j = x' j) → g k x = g k x') (f : (Fin m → Bool) → F),
    ∃ c : (Fin m → Bool) → F,
      ∀ x, digitsEval c (fun k => (if x k then 1 else 0) + g k x) = f x
  | 0, _, _, f => ⟨f, fun x => by
      unfold digitsEval
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Fintype.sum_unique]
      exact congrArg f (Subsingleton.elim _ _)⟩
  | m + 1, g, hg, f => by
    have hrest : ∀ (x0 : Bool) (xs : Fin m → Bool) (k : Fin m),
        g k.succ (Fin.cons x0 xs) = g k.succ (Fin.cons false xs) := by
      intro x0 xs k
      refine hg k.succ _ _ fun j hj => ?_
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp
        (lt_of_le_of_lt (Fin.zero_le _) hj))
      simp
    have hzero : ∀ (x0 : Bool) (xs : Fin m → Bool),
        g 0 (Fin.cons x0 xs) = g 0 (Fin.cons false xs) := by
      intro x0 xs
      refine hg 0 _ _ fun j hj => ?_
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp hj)
      simp
    have htri : ∀ (k : Fin m) (x x' : Fin m → Bool), (∀ j, k < j → x j = x' j) →
        g k.succ (Fin.cons false x) = g k.succ (Fin.cons false x') := fun k x x' h =>
      hg k.succ _ _ fun j hj => by
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp
          (lt_of_le_of_lt (Fin.zero_le _) hj))
        simpa using h j' (Fin.succ_lt_succ_iff.mp hj)
    obtain ⟨c1, h1⟩ := exists_digitsEval m (fun k xs => g k.succ (Fin.cons false xs)) htri
      (fun xs => f (Fin.cons true xs) + f (Fin.cons false xs))
    obtain ⟨c0, h0⟩ := exists_digitsEval m (fun k xs => g k.succ (Fin.cons false xs)) htri
      (fun xs => f (Fin.cons false xs)
        + g 0 (Fin.cons false xs) * (f (Fin.cons true xs) + f (Fin.cons false xs)))
    refine ⟨fun b => if b 0 then c1 (Fin.tail b) else c0 (Fin.tail b), fun x => ?_⟩
    obtain ⟨x0, xs, rfl⟩ : ∃ x0 xs, x = Fin.cons x0 xs := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have e1 := h1 xs
    have e0 := h0 xs
    unfold digitsEval at e0 e1 ⊢
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => Bool), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fintype.sum_bool, Fin.tail_cons, ite_true, Bool.false_eq_true, ite_false, one_mul, hrest x0,
      hzero x0]
    have hfac : ∀ d : F, ∑ bs : Fin m → Bool, c1 bs * (d * ∏ k : Fin m,
        (if bs k then (if xs k then 1 else 0) + g k.succ (Fin.cons false xs) else 1))
          = d * (f (Fin.cons true xs) + f (Fin.cons false xs)) := by
      intro d
      rw [← e1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun bs _ => by ring
    rw [hfac, e0]
    cases x0
    · simp only [Bool.false_eq_true, ite_false, zero_add]
      have key : ∀ p q : F, p + (q + p) = q := fun p q => by
        rw [add_comm q p, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      exact key _ _
    · simp only [ite_true]
      have : ∀ a b u : F, (1 + u) * (a + b) + (b + u * (a + b)) = a + (b + b) + (u * (a + b) + u * (a + b)) := by
        intros; ring
      rw [this, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, add_zero]

/-- **Every function on the cells of a Cantor basis is a table's polynomial.** -/
theorem CantorBasis.exists_table {N : ℕ} (B : CantorBasis F N) {m : ℕ} (hm : m ≤ N)
    (f : (Fin m → Bool) → F) :
    ∃ c : (Fin m → Bool) → F, ∀ x, (tablePoly c).eval (B.point x) = f x := by
  obtain ⟨c, hc⟩ := exists_digitsEval m (fun k x => B.above k x)
    (fun k x x' h => B.above_congr k x x' h) f
  refine ⟨c, fun x => ?_⟩
  rw [tablePoly_eval, ← hc x]
  congr 1
  funext k
  exact B.digit_eq hm k x

/-! ## The cells -/

def roleBit0 : Fin 4 → Bool := ![false, true, false, true]

def roleBit1 : Fin 4 → Bool := ![false, false, true, true]

def roleOf (b0 b1 : Bool) : Fin 4 := if b1 then (if b0 then 3 else 2) else (if b0 then 1 else 0)

/-- The bits of a cell: its role's two, then its row's. -/
def cellBits {n : ℕ} : (Fin n → Bool) × Fin 4 ≃ (Fin (n + 1 + 1) → Bool) where
  toFun p := Fin.cons (roleBit0 p.2) (Fin.cons (roleBit1 p.2) p.1)
  invFun x := (Fin.tail (Fin.tail x), roleOf (x 0) (x (Fin.succ 0)))
  left_inv := by
    rintro ⟨y, c⟩
    fin_cases c <;> simp [roleBit0, roleBit1, roleOf, Fin.tail_cons]
  right_inv := by
    intro x
    have h0 : ∀ a b, roleBit0 (roleOf a b) = a := by decide
    have h1 : ∀ a b, roleBit1 (roleOf a b) = b := by decide
    simp only [h0, h1]
    have e : (Fin.cons (x (Fin.succ 0)) (Fin.tail (Fin.tail x)) : Fin (n + 1) → Bool)
        = Fin.tail x := Fin.cons_self_tail (Fin.tail x)
    rw [e]
    exact Fin.cons_self_tail x

section Cells

variable [DecidableEq F] {N : ℕ} (B : CantorBasis F N) {n : ℕ}

/-- A cell's point is its row's first cell's, shifted by its role. -/
theorem point_cellBits (y : Fin n → Bool) (c : Fin 4) :
    B.point (cellBits (y, c)) = B.point (cellBits (y, 0)) + shift (B.β 1) c := by
  unfold CantorBasis.point
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  fin_cases c <;> simp [cellBits, roleBit0, roleBit1, shift, B.zero] <;> ring

theorem cantor_theta (hN : 2 ≤ N) : B.β 1 * B.β 1 + B.β 1 + 1 = 0 := by
  have h : B.β 1 * B.β 1 + B.β 1 = 1 := by simpa [sq, B.zero] using B.succ 0 (by omega)
  rw [h]
  exact CharTwo.add_self_eq_zero 1

variable (n) in
/-- The `X` cells: the span of the basis vectors from the third on. -/
def cantorT : Finset F := univ.image fun y : Fin n → Bool => B.point (cellBits (y, 0))

theorem cantor_hT (hm : n + 2 ≤ N) : ∀ x ∈ cantorT B n, ∀ y ∈ cantorT B n, ∀ c d : Fin 4,
    x + shift (B.β 1) c = y + shift (B.β 1) d → x = y ∧ c = d := by
  intro x hx y hy c d h
  obtain ⟨y1, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y2, -, rfl⟩ := Finset.mem_image.mp hy
  rw [← point_cellBits, ← point_cellBits] at h
  have := cellBits.injective (B.point_injective hm h)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
  exact ⟨rfl, rfl⟩

theorem cantor_hCells (hm : n + 2 ≤ N) : ∀ x ∈ cantorT B n, ∀ c : Fin 4,
    (digitPoly (n + 2) : F[X]).eval (x + shift (B.β 1) c) = 0 := by
  intro x hx c
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
  rw [← point_cellBits, digitPoly_eval]
  exact B.iterate_point hm _

/-- The rows, by their bits. -/
noncomputable def cantorRows (hm : n + 2 ≤ N) : (Fin n → Bool) ≃ cantorT B n :=
  Equiv.ofBijective
    (fun y => ⟨B.point (cellBits (y, 0)), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    ⟨fun y y' h => (Prod.mk.inj (cellBits.injective
        (B.point_injective hm (Subtype.ext_iff.mp h)))).1,
      fun ⟨t, ht⟩ => by
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ht
        exact ⟨y, rfl⟩⟩

/-- The cells, by their bits. -/
noncomputable def cantorCells (hm : n + 2 ≤ N) : (Fin (n + 2) → Bool) ≃ cantorT B n × Fin 4 :=
  cellBits.symm.trans (Equiv.prodCongr (cantorRows B hm) (Equiv.refl _))

theorem cantorCells_point (hm : n + 2 ≤ N) (x : Fin (n + 2) → Bool) :
    ((cantorCells B hm x).1 : F) + shift (B.β 1) (cantorCells B hm x).2 = B.point x := by
  have h := point_cellBits B (cellBits.symm x).1 (cellBits.symm x).2
  rw [Prod.mk.eta, Equiv.apply_symm_apply] at h
  exact h.symm

theorem cantorCells_symm_point (hm : n + 2 ≤ N) (i : cantorT B n × Fin 4) :
    (i.1 : F) + shift (B.β 1) i.2 = B.point ((cantorCells B hm).symm i) := by
  have h := cantorCells_point B hm ((cantorCells B hm).symm i)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- The wiring table: coefficients of a polynomial that carries the wiring. -/
noncomputable def wiringTable (hm : n + 2 ≤ N) (σ : Equiv.Perm (Fin (n + 2) → Bool)) :
    (Fin (n + 2) → Bool) → F :=
  (B.exists_table hm fun x => B.point (σ x)).choose

theorem wiringTable_eval (hm : n + 2 ≤ N) (σ : Equiv.Perm (Fin (n + 2) → Bool))
    (x : Fin (n + 2) → Bool) :
    (tablePoly (wiringTable B hm σ)).eval (B.point x) = B.point (σ x) :=
  (B.exists_table hm fun x => B.point (σ x)).choose_spec x

/-- A public weight exists for any public words, within the cells' size: a table's polynomial. -/
theorem exists_pub (hm : n + 2 ≤ N) (words : ℕ)
    (wordSum : Fin words → ((Fin (n + 2) → Bool) → F) →ₗ[F] F) :
    ∃ pub : F → F[X], (∀ (γ : F) (w : (Fin (n + 2) → Bool) → F),
        ∑ x, (pub γ).eval (B.point x) * w x = ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J w) ∧
      ∀ γ, (pub γ).natDegree ≤ 2 ^ (n + 2) := by
  choose c hc using fun γ : F => B.exists_table hm fun x : Fin (n + 2) → Bool =>
    ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J (fun j => if x = j then 1 else 0)
  refine ⟨fun γ => tablePoly (c γ), fun γ w => ?_, fun γ => natDegree_tablePoly_le _⟩
  simp only [hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [(wordSum J).pi_apply_eq_sum_univ w, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  ring

/-- **The parameters of the protocol on a Cantor basis**, for any wiring of the cells, any
public words, and any public weight that carries them. -/
noncomputable def Params.ofCantor (hm : n + 2 ≤ N) (σ : Equiv.Perm (Fin (n + 2) → Bool))
    (words : ℕ) (wordSum : Fin words → ((Fin (n + 2) → Bool) → F) →ₗ[F] F) (pub : F → F[X])
    (hPub : ∀ (γ : F) (w : (Fin (n + 2) → Bool) → F),
      ∑ x, (pub γ).eval (B.point x) * w x = ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J w) :
    Params F where
  θ := B.β 1
  hθ := cantor_theta B (by omega)
  T := cantorT B n
  hT := cantor_hT B hm
  vCells := digitPoly (n + 2)
  vRows := ∏ x : cantorT B n, (X - C (x : F))
  hCells := cantor_hCells B hm
  hRows := fun x hx => by
    rw [eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨x, hx⟩ : cantorT B n)) (by simp)
  σ := (cantorCells B hm).permCongr σ
  sigmaPoly := tablePoly (wiringTable B hm σ)
  hσ := fun i => by
    rw [cantorCells_symm_point B hm i, cantorCells_symm_point B hm, wiringTable_eval]
    simp [Equiv.permCongr_apply]
  words := words
  wordSum := fun J => (wordSum J).comp (LinearMap.funLeft F F (cantorCells B hm))
  pub := pub
  hPub := fun γ w => by
    refine ((Equiv.sum_comp (cantorCells B hm) _).symm.trans ?_).trans
      (hPub γ fun x => w (cantorCells B hm x))
    exact Finset.sum_congr rfl fun x _ => by rw [cantorCells_point]

variable (hm : n + 2 ≤ N) (σ : Equiv.Perm (Fin (n + 2) → Bool)) (words : ℕ)
  (wordSum : Fin words → ((Fin (n + 2) → Bool) → F) →ₗ[F] F) (pub : F → F[X])
  (hPub : ∀ (γ : F) (w : (Fin (n + 2) → Bool) → F),
    ∑ x, (pub γ).eval (B.point x) * w x = ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J w)

theorem Params.ofCantor_pt (x : Fin (n + 2) → Bool) :
    (Params.ofCantor B hm σ words wordSum pub hPub).pt (cantorCells B hm x) = B.point x :=
  cantorCells_point B hm x

theorem Params.ofCantor_nCells : (Params.ofCantor B hm σ words wordSum pub hPub).nCells = 2 ^ (n + 2) := by
  show Fintype.card (cantorT B n × Fin 4) = _
  rw [← Fintype.card_congr (cantorCells B hm)]
  simp

include hm in
theorem card_cantorT : Fintype.card (cantorT B n) = 2 ^ n := by
  rw [← Fintype.card_congr (cantorRows B hm)]
  simp

/-- The degrees of the instance: every table's polynomial within its table's size, and the
public weight within a given bound. -/
noncomputable def Params.ofCantorBounds (d : ℕ) (hd : ∀ γ, (pub γ).natDegree ≤ d) :
    (Params.ofCantor B hm σ words wordSum pub hPub).Bounds where
  witness := 2 ^ (n + 1)
  quotient := 2 ^ (n + 2 + 2)
  sigma := 2 ^ (n + 2)
  pub := d
  cells := 2 ^ (n + 2)
  rows := 2 ^ n
  hSigma := natDegree_tablePoly_le _
  hPub := hd
  hCells := natDegree_digitPoly_le _
  hRows := by
    show (∏ x : cantorT B n, (X - C (x : F))).natDegree ≤ 2 ^ n
    refine (natDegree_prod_le _ _).trans ?_
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    exact (card_cantorT B hm).le

/-- **The four claims are the model's acceptance, on the instance**: `claims_iff_accepts` with
its hypotheses on the cells and the vanishing polynomial met, for any wiring table whose
polynomial carries the wiring. -/
theorem claims_iff_accepts_ofCantor (cF : (Fin (n + 2) → Bool) → F)
    (hcF : ∀ x, (tablePoly cF).eval (B.point x) = B.point (σ x))
    (cW : (Fin (n + 1 + 1 + 1) → Bool) → F)
    (cQ : (Fin (n + 2 + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → F)
    (Y : F) (hY : 1 + Y ≠ 0) (hY2 : 1 + Y ^ 2 ≠ 0)
    (stmt : Fin words → F) (α β γ t ρ s : F) (a : Fin 4 → F)
    (ht : ∀ i : Fin (n + 2 + 1 + 1), 1 + sq^[(i : ℕ)] t ≠ 0)
    (hnz : (Params.ofCantor B hm σ words wordSum pub hPub).claimDen α β t a s * (Params.ofCantor B hm σ words wordSum pub hPub).vRows.eval t ≠ 0) :
    (mle cW (Fin.cons ρ (Fin.cons (ρ ^ 2) (claimPoint 2 (n + 1) t)))
          = (∑ j, Params.opening ρ j * a j) / claimScale 2 (n + 1) t ∧
        mle cF (claimPoint 0 (n + 2) t) = s / claimScale 0 (n + 2) t ∧
        mle cQ (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (n + 2 + 1 + 1) t)
            ((Params.ofCantor B hm σ words wordSum pub hPub).vCells.eval t / (Params.ofCantor B hm σ words wordSum pub hPub).claimDen α β t a s)) ρ) (Y / (1 + Y))) (Y ^ 2 / (1 + Y ^ 2)))
          = (Params.ofCantor B hm σ words wordSum pub hPub).claimValue α β γ t ρ a s / ((1 + Y) * (1 + Y ^ 2))
            / claimScale 0 (n + 2 + 1 + 1) t ∧
        mle cQ (sumPoint (n + 2) Y) = (Params.ofCantor B hm σ words wordSum pub hPub).target stmt γ / ((1 + Y) * (1 + Y ^ 2)))
      ↔ (Params.ofCantor B hm σ words wordSum pub hPub).Accepts stmt (witnessOfTable cW) (quotientsOfTable Y cQ) α β γ t a s ρ :=
  claims_iff_accepts (Params.ofCantor B hm σ words wordSum pub hPub) B hm (cantorCells B hm)
    (Params.ofCantor_pt B hm σ words wordSum pub hPub) rfl cW cF
    (B.tablePoly_ext hm _ _ fun x => by rw [wiringTable_eval, hcF]) cQ Y hY hY2 stmt
    α β γ t ρ s a ht hnz

/-- **The instance's vanishing polynomials are the exact ones**, so the honest prover's quotients
exist on it (`Params.honest_consistent`). -/
theorem Params.ofCantor_exact : (Params.ofCantor B hm σ words wordSum pub hPub).Exact := by
  refine ⟨?_, rfl⟩
  obtain ⟨hmon, hdeg⟩ := digitPoly_monic_natDegree (F := F) (n + 2)
  exact eq_prod_of_monic_of_roots hmon
    (hdeg.trans (Params.ofCantor_nCells B hm σ words wordSum pub hPub).symm)
    (Params.ofCantor B hm σ words wordSum pub hPub).pt_injective
    fun i => (Params.ofCantor B hm σ words wordSum pub hPub).hCells i.1.1 i.1.2 i.2

/-! ## The rows' vanishing polynomial, as the verifier evaluates it -/

/-- A sum of digits with constant coefficients. -/
noncomputable def rowsPoly (τ : Fin (n + 1) → F) : F[X] := ∑ k, C (τ k) * digitPoly (k : ℕ)

theorem rowsPoly_eval (τ : Fin (n + 1) → F) (t : F) :
    (rowsPoly τ).eval t = ∑ k, τ k * sq^[(k : ℕ)] t := by
  simp [rowsPoly, eval_finsetSum, digitPoly_eval]

theorem rowsPoly_monic (τ : Fin (n + 1) → F) (hτ : τ (Fin.last n) = 1) :
    (rowsPoly τ).Monic ∧ (rowsPoly τ).natDegree = 2 ^ n := by
  obtain ⟨hmon, hdeg⟩ := digitPoly_monic_natDegree (F := F) n
  have hlow : (∑ k : Fin n, C (τ k.castSucc) * digitPoly (k : ℕ) : F[X]).natDegree
      < (digitPoly n : F[X]).natDegree := by
    rw [hdeg]
    have hpos : 0 < 2 ^ n := by positivity
    refine lt_of_le_of_lt (b := 2 ^ n - 1) (natDegree_sum_le_of_forall_le _ _ fun k _ => ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ((natDegree_digitPoly_le _).trans ?_)
    exact Nat.le_sub_one_of_lt (Nat.pow_lt_pow_right (by norm_num) k.2)
  have e : rowsPoly τ = ∑ k : Fin n, C (τ k.castSucc) * digitPoly (k : ℕ) + digitPoly n := by
    simp [rowsPoly, Fin.sum_univ_castSucc, hτ]
  rw [e]
  exact ⟨hmon.add_of_right (degree_lt_degree hlow),
    by rw [natDegree_add_eq_right_of_natDegree_lt hlow, hdeg]⟩

/-- **The verifier's rows' polynomial is the instance's.** A sum of digits with constant
coefficients, the last one, that vanishes on the basis vectors of the rows (the linear system
`quotient::domain::row_vanishing` solves) is the product over the rows. -/
theorem rowsPoly_eq_vRows (τ : Fin (n + 1) → F) (hτ : τ (Fin.last n) = 1)
    (hsys : ∀ j : Fin (n + 2), 2 ≤ (j : ℕ) → (rowsPoly τ).eval (B.β j) = 0) :
    rowsPoly τ = (Params.ofCantor B hm σ words wordSum pub hPub).vRows := by
  obtain ⟨hmon, hdeg⟩ := rowsPoly_monic τ hτ
  refine eq_prod_of_monic_of_roots hmon (hdeg.trans (card_cantorT B hm).symm)
    Subtype.val_injective fun x => ?_
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp x.2
  rw [← hy, rowsPoly_eval]
  have hadd : ∀ z : Fin (n + 2) → Bool, (∀ j : Fin (n + 2), (j : ℕ) < 2 → z j = false) →
      ∑ k, τ k * sq^[(k : ℕ)] (B.point z) = 0 := by
    intro z hz
    unfold CantorBasis.point
    simp only [sq_iterate_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : z j = true
    · have h2 : 2 ≤ (j : ℕ) := by
        by_contra h
        rw [hz j (by omega)] at hj
        exact Bool.false_ne_true hj
      simp only [hj, ite_true]
      rw [← rowsPoly_eval]
      exact hsys j h2
    · simp [hj, sq_iterate_zero]
  refine hadd _ fun j hj => ?_
  obtain ⟨j, hjlt⟩ := j
  interval_cases j <;> rfl

end Cells

/-! ## At the protocol's sizes -/

section Sizes

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {N : ℕ} (B : CantorBasis F N) (hm : 20 + 2 ≤ N)
  (σ : Equiv.Perm (Fin (20 + 2) → Bool))
  (wordSum : Fin 8 → ((Fin (20 + 2) → Bool) → F) →ₗ[F] F) (pub : F → F[X])
  (hPub : ∀ (γ : F) (w : (Fin (20 + 2) → Bool) → F),
    ∑ x, (pub γ).eval (B.point x) * w x = ∑ J : Fin 8, γ ^ (J : ℕ) * wordSum J w)
  (hd : ∀ γ, (pub γ).natDegree ≤ 2 ^ 22 + 9 * 2 ^ 10)

theorem Params.ofCantor_identity :
    (Params.ofCantorBounds B hm σ 8 wordSum pub hPub _ hd).identity ≤ 2 ^ 27 := by
  norm_num [Params.Bounds.identity, Params.Bounds.denominator, Params.Bounds.cell,
    Params.ofCantorBounds]

open OracleComp OracleSpec in
/-- **128 bits on the instance.** With `2^20` rows and eight public words over a field of `2^192`
elements, and a public weight of degree at most `2^22 + 9 * 2^10`, an adversary making `Q`
queries wins with probability at most `(Q + 3) / 2^128`. -/
theorem knowledgeSoundness_ofCantor (hq : Fintype.card F = 2 ^ 192)
    (adv : OracleComp (ofFn (Answer (Params.ofCantor B hm σ 8 wordSum pub hPub)
      (Params.ofCantorBounds B hm σ 8 wordSum pub hPub _ hd)))
      (Proof (Params.ofCantor B hm σ 8 wordSum pub hPub)
        (Params.ofCantorBounds B hm σ 8 wordSum pub hPub _ hd)))
    (Q : ℕ) (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experiment adv)).run' ∅}[
        r.2 = true ∧ ¬ (Params.ofCantor B hm σ 8 wordSum pub hPub).Sat r.1.stmt
          ((Params.ofCantor B hm σ 8 wordSum pub hPub).cells r.1.g.1)]
      ≤ ((Q + 3 : ℕ) : ENNReal) * (((1 / 2 ^ 128 : NNReal) : NNReal) : ENNReal) :=
  knowledgeSoundness_bits (P := Params.ofCantor B hm σ 8 wordSum pub hPub)
    (B := Params.ofCantorBounds B hm σ 8 wordSum pub hPub _ hd) hq
    (Params.ofCantor_nCells B hm σ 8 wordSum pub hPub) rfl
    (Params.ofCantor_identity B hm σ wordSum pub hPub hd) adv Q hQ

omit [SampleableType F] in
/-- **The instance exists** in every field of `2^192` elements: a Cantor basis and, for any
wiring and public words, a public weight within the degree the theorem above asks. -/
theorem exists_instance (hq : Fintype.card F = 2 ^ 192) :
    ∃ B : CantorBasis F (20 + 2), ∀ wordSum : Fin 8 → ((Fin (20 + 2) → Bool) → F) →ₗ[F] F,
      ∃ pub : F → F[X], (∀ (γ : F) (w : (Fin (20 + 2) → Bool) → F),
          ∑ x, (pub γ).eval (B.point x) * w x = ∑ J : Fin 8, γ ^ (J : ℕ) * wordSum J w) ∧
        ∀ γ, (pub γ).natDegree ≤ 2 ^ 22 + 9 * 2 ^ 10 := by
  obtain ⟨B⟩ := exists_cantorBasis_big hq (20 + 2) (by norm_num) (by norm_num)
  refine ⟨B, fun wordSum => ?_⟩
  obtain ⟨pub, h1, h2⟩ := exists_pub B le_rfl 8 wordSum
  exact ⟨pub, h1, fun γ => (h2 γ).trans (by norm_num)⟩

end Sizes

end QuotientSecurity
