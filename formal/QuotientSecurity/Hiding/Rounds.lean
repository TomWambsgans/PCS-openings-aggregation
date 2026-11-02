-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib

/-!
# The lane rounds

WHIR's opening of a stack of `2^k` lanes (`k = 6`) starts with `k` sumcheck rounds that fold the
lane variables, variable `0` first, of `Σ_{b, y} w(b, y)·t(b, y)`: `t` is the stack (lane `b`,
entry `y`), `w` the claims' combined weight. Round `j` sends two values of its quadratic
`h_j(X) = Σ_{b', y} w̃(φ_{<j}, X, b', y)·t̃(φ_{<j}, X, b', y)`, its value at `0` and its quadratic
coefficient (`msg`); the verifier gets `h_j(1)` from its running claim, and the next running claim is
`h_j(φ_j)` (`nextClaim`).

This file defines the rounds on tables over `E` (`laneRounds`), proves the sumcheck identity: after
the `k` rounds the running claim is `Σ_y w¹(y)·f¹(y)`, the folded weight against the folded table
(`lastClaim_laneRounds`), and packages the rounds as a `K`-linear map of a `K`-valued stack whose
lanes sit at some of the `2^k` lane indices (`roundsMap`). The consequence the hiding argument uses
(`roundsMap_mem_ker`): a change of the stack that keeps the claim and the folded table (where the
weight lives) leaves the last running claim alone, so its round values lie in a fixed subspace
`ker lastMap` of `K`-dimension `3·(2k - 1)` (`33` for `k = 6`).
-/

namespace QuotientSecurity.Hiding

open Finset

section Tables

set_option linter.unusedSectionVars false

variable {E Y : Type} [Field E] [Fintype Y]

/-- A table of `2^k` lanes (lane `b : Fin k → Bool`, variable `0` folded first) of entries `Y`. -/
abbrev LTable (E Y : Type) (k : ℕ) := (Fin k → Bool) → Y → E

/-- A sum over the lanes of `k + 1` variables, split on the first. -/
theorem sum_cons {M : Type} [AddCommMonoid M] {k : ℕ} (f : (Fin (k + 1) → Bool) → M) :
    ∑ b, f b = ∑ b : Fin k → Bool, (f (Fin.cons false b) + f (Fin.cons true b)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    add_comm, ← sum_add_distrib]
  rfl

/-- Fold the first lane variable at `r`: lane `b` becomes `(1 - r)·t(0b) + r·t(1b)`. -/
def foldFirst {k : ℕ} (r : E) (t : LTable E Y (k + 1)) : LTable E Y k :=
  fun b y => (1 - r) * t (Fin.cons false b) y + r * t (Fin.cons true b) y

/-- A round's message: `h(0)` and the quadratic coefficient of
`h(X) = Σ_{b, y} w̃(X, b, y)·t̃(X, b, y)`. -/
def msg {k : ℕ} (w t : LTable E Y (k + 1)) : E × E :=
  (∑ b, ∑ y, w (Fin.cons false b) y * t (Fin.cons false b) y,
    ∑ b, ∑ y, (w (Fin.cons true b) y - w (Fin.cons false b) y) *
      (t (Fin.cons true b) y - t (Fin.cons false b) y))

/-- The `k` lane rounds' messages at challenges `φ`. -/
def laneRounds : (k : ℕ) → (Fin k → E) → LTable E Y k → LTable E Y k → (Fin k → E × E)
  | 0, _, _, _ => fun i => Fin.elim0 i
  | k + 1, φ, w, t =>
      Fin.cons (msg w t) (laneRounds k (Fin.tail φ) (foldFirst (φ 0) w) (foldFirst (φ 0) t))

/-- The weighted sum the rounds prove. -/
def ip {k : ℕ} (w t : LTable E Y k) : E := ∑ b, ∑ y, w b y * t b y

/-- The verifier's next running claim, `h(r)`, from the message and the running claim
`s = h(0) + h(1)`. -/
def nextClaim (r : E) (m : E × E) (s : E) : E := m.1 + (s - 2 * m.1 - m.2) * r + m.2 * r ^ 2

/-- The running claim after all the rounds. -/
def lastClaim : (k : ℕ) → (Fin k → E) → (Fin k → E × E) → E → E
  | 0, _, _, s => s
  | k + 1, φ, v, s => lastClaim k (Fin.tail φ) (Fin.tail v) (nextClaim (φ 0) (v 0) s)

/-- The table with every lane variable folded: `f¹`. -/
def foldAll : (k : ℕ) → (Fin k → E) → LTable E Y k → Y → E
  | 0, _, t => t (fun i => Fin.elim0 i)
  | k + 1, φ, t => foldAll k (Fin.tail φ) (foldFirst (φ 0) t)

/-- Lane `b`'s weight in the fold: `eq(φ, b)`. -/
def eqW {k : ℕ} (φ : Fin k → E) (b : Fin k → Bool) : E :=
  ∏ i, if b i then φ i else 1 - φ i

theorem eqW_cons {k : ℕ} (φ : Fin (k + 1) → E) (c : Bool) (b : Fin k → Bool) :
    eqW φ (Fin.cons c b) = (if c then φ 0 else 1 - φ 0) * eqW (Fin.tail φ) b := by
  unfold eqW
  rw [Fin.prod_univ_succ]
  simp [Fin.tail]

/-- The folded table is the `eq`-weighted sum of the lanes. -/
theorem foldAll_eq : ∀ (k : ℕ) (φ : Fin k → E) (t : LTable E Y k) (y : Y),
    foldAll k φ t y = ∑ b, eqW φ b * t b y
  | 0, φ, t, y => by
    rw [foldAll, Fintype.sum_unique]
    simp only [eqW, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact congrFun (congrArg t (Subsingleton.elim _ _)) y
  | k + 1, φ, t, y => by
    rw [foldAll, foldAll_eq k, sum_cons]
    refine sum_congr rfl fun b _ => ?_
    simp only [foldFirst, eqW_cons, ite_false, ite_true, Bool.false_eq_true]
    ring

/-- **One round of the sumcheck.** The next running claim, from the message and the weighted sum,
is the weighted sum of the folded tables. -/
theorem nextClaim_msg {k : ℕ} (r : E) (w t : LTable E Y (k + 1)) :
    nextClaim r (msg w t) (ip w t) = ip (foldFirst r w) (foldFirst r t) := by
  have hn : ∀ m s, nextClaim r m s = (1 - 2 * r) * m.1 + (r ^ 2 - r) * m.2 + r * s := by
    intro m s
    unfold nextClaim
    ring
  rw [hn]
  unfold msg ip
  rw [sum_cons]
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => sum_congr rfl fun y _ => ?_
  simp only [foldFirst]
  ring

/-- **The sumcheck identity.** After the rounds, the running claim that started at the weighted
sum is the folded weight against the folded table. -/
theorem lastClaim_laneRounds : ∀ (k : ℕ) (φ : Fin k → E) (w t : LTable E Y k),
    lastClaim k φ (laneRounds k φ w t) (ip w t) = ∑ y, foldAll k φ w y * foldAll k φ t y
  | 0, φ, w, t => by
    have h0 : (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Bool) = default := Subsingleton.elim _ _
    simp only [lastClaim, ip, foldAll, h0]
    rw [Fintype.sum_unique]
    refine sum_congr rfl fun y _ => ?_
    congr 2
  | k + 1, φ, w, t => by
    simp only [lastClaim, laneRounds, Fin.tail_cons, Fin.cons_zero, nextClaim_msg]
    exact lastClaim_laneRounds k _ _ _

/-! ### Linearity -/

theorem foldFirst_add {k : ℕ} (r : E) (t t' : LTable E Y (k + 1)) :
    foldFirst r (t + t') = foldFirst r t + foldFirst r t' := by
  funext b y
  simp only [foldFirst, Pi.add_apply]
  ring

theorem foldFirst_smul {k : ℕ} (r c : E) (t : LTable E Y (k + 1)) :
    foldFirst r (c • t) = c • foldFirst r t := by
  funext b y
  simp only [foldFirst, Pi.smul_apply, smul_eq_mul]
  ring

theorem msg_add {k : ℕ} (w t t' : LTable E Y (k + 1)) : msg w (t + t') = msg w t + msg w t' := by
  simp only [msg, Pi.add_apply, Prod.mk_add_mk, ← sum_add_distrib]
  congr 1 <;> refine sum_congr rfl fun b _ => sum_congr rfl fun y _ => ?_ <;> ring

theorem msg_smul {k : ℕ} (c : E) (w t : LTable E Y (k + 1)) : msg w (c • t) = c • msg w t := by
  simp only [msg, Pi.smul_apply, smul_eq_mul, Prod.smul_mk, mul_sum]
  congr 1 <;> refine sum_congr rfl fun b _ => sum_congr rfl fun y _ => ?_ <;> ring

theorem laneRounds_add : ∀ (k : ℕ) (φ : Fin k → E) (w t t' : LTable E Y k),
    laneRounds k φ w (t + t') = laneRounds k φ w t + laneRounds k φ w t'
  | 0, _, _, _, _ => funext fun i => Fin.elim0 i
  | k + 1, φ, w, t, t' => by
    simp only [laneRounds, foldFirst_add, laneRounds_add k, msg_add]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Pi.add_apply, Fin.cons_zero, Fin.cons_zero, Fin.cons_zero]
    · rw [Pi.add_apply, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Pi.add_apply]

theorem laneRounds_smul : ∀ (k : ℕ) (φ : Fin k → E) (c : E) (w t : LTable E Y k),
    laneRounds k φ w (c • t) = c • laneRounds k φ w t
  | 0, _, _, _, _ => funext fun i => Fin.elim0 i
  | k + 1, φ, c, w, t => by
    simp only [laneRounds, foldFirst_smul, laneRounds_smul k, msg_smul]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Pi.smul_apply, Fin.cons_zero, Fin.cons_zero]
    · rw [Pi.smul_apply, Fin.cons_succ, Fin.cons_succ, Pi.smul_apply]

theorem lastClaim_add : ∀ (k : ℕ) (φ : Fin k → E) (v v' : Fin k → E × E) (s s' : E),
    lastClaim k φ (v + v') (s + s') = lastClaim k φ v s + lastClaim k φ v' s'
  | 0, _, _, _, _, _ => rfl
  | k + 1, φ, v, v', s, s' => by
    simp only [lastClaim]
    rw [← lastClaim_add k]
    congr 1
    simp only [nextClaim, Pi.add_apply, Prod.fst_add, Prod.snd_add]
    ring

theorem lastClaim_smul : ∀ (k : ℕ) (φ : Fin k → E) (c : E) (v : Fin k → E × E) (s : E),
    lastClaim k φ (c • v) (c • s) = c • lastClaim k φ v s
  | 0, _, _, _, _ => rfl
  | k + 1, φ, c, v, s => by
    simp only [lastClaim]
    rw [← lastClaim_smul k]
    congr 1
    simp only [nextClaim, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-! ### Weightless entries -/

/-- At every entry, the weight or the table is zero on all lanes. -/
def Disjoint' {k : ℕ} (w t : LTable E Y k) : Prop := ∀ y, (∀ b, w b y = 0) ∨ (∀ b, t b y = 0)

theorem disjoint_foldFirst {k : ℕ} (r : E) {w t : LTable E Y (k + 1)} (h : Disjoint' w t) :
    Disjoint' (foldFirst r w) (foldFirst r t) := by
  intro y
  rcases h y with hw | ht
  · exact Or.inl fun b => by simp [foldFirst, hw]
  · exact Or.inr fun b => by simp [foldFirst, ht]

/-- Where the weight and the table never meet, the rounds see nothing. -/
theorem laneRounds_eq_zero_of_disjoint : ∀ (k : ℕ) (φ : Fin k → E) (w t : LTable E Y k),
    Disjoint' w t → laneRounds k φ w t = 0
  | 0, _, _, _, _ => funext fun i => Fin.elim0 i
  | k + 1, φ, w, t, h => by
    have hm : msg w t = 0 := by
      have hz : ∀ b y, w (Fin.cons false b) y * t (Fin.cons false b) y = 0 ∧
          (w (Fin.cons true b) y - w (Fin.cons false b) y) *
            (t (Fin.cons true b) y - t (Fin.cons false b) y) = 0 := by
        intro b y
        rcases h y with hw | ht
        · simp [hw]
        · simp [ht]
      simp only [msg, (hz _ _).1, (hz _ _).2, sum_const_zero, Prod.mk_zero_zero]
    simp only [laneRounds, hm, laneRounds_eq_zero_of_disjoint k _ _ _ (disjoint_foldFirst _ h)]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero, Pi.zero_apply]
    · rw [Fin.cons_succ, Pi.zero_apply, Pi.zero_apply]

end Tables

/-! ## The rounds as a `K`-linear map of the stack -/

section Stack

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y]

/-- The stack's lanes put at their lane indices (`pos`), the other indices zero, over `E`. -/
def lift {k : ℕ} (pos : ι → (Fin k → Bool)) (T : ι → Y → K) : LTable E Y k :=
  fun b y => ∑ l, if pos l = b then algebraMap K E (T l y) else 0

theorem lift_add {k : ℕ} (pos : ι → (Fin k → Bool)) (T T' : ι → Y → K) :
    lift (E := E) pos (T + T') = lift pos T + lift pos T' := by
  funext b y
  simp only [lift, Pi.add_apply, map_add, ← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem lift_smul {k : ℕ} (pos : ι → (Fin k → Bool)) (c : K) (T : ι → Y → K) :
    lift (E := E) pos (c • T) = algebraMap K E c • lift pos T := by
  funext b y
  simp only [lift, Pi.smul_apply, smul_eq_mul, map_mul, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/-- The folded table of a lifted stack: the stack's lanes weighed by `eq(φ, pos l)`. -/
theorem foldAll_lift {k : ℕ} (pos : ι → (Fin k → Bool)) (φ : Fin k → E) (T : ι → Y → K) (y : Y) :
    foldAll k φ (lift pos T) y = ∑ l, eqW φ (pos l) * algebraMap K E (T l y) := by
  rw [foldAll_eq]
  simp only [lift, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  simp [mul_ite]

/-- The lane rounds at challenges `φ` for the combined weight `W`, as a `K`-linear map of the
stack. -/
def roundsMap {k : ℕ} (pos : ι → (Fin k → Bool)) (φ : Fin k → E) (W : LTable E Y k) :
    (ι → Y → K) →ₗ[K] (Fin k → E × E) where
  toFun T := laneRounds k φ W (lift pos T)
  map_add' T T' := by rw [lift_add, laneRounds_add]
  map_smul' c T := by
    rw [lift_smul, laneRounds_smul]
    funext i
    simp [Algebra.smul_def]

/-- The last running claim of round values that start from a zero claim, `K`-linearly. -/
def lastMap {k : ℕ} (φ : Fin k → E) : (Fin k → E × E) →ₗ[K] E where
  toFun v := lastClaim k φ v 0
  map_add' v v' := by rw [← lastClaim_add, add_zero]
  map_smul' c v := by
    have hv : c • v = (algebraMap K E c) • v := (algebraMap_smul E c v).symm
    show lastClaim k φ (c • v) 0 = c • lastClaim k φ v 0
    have h := lastClaim_smul k φ (algebraMap K E c) v 0
    rw [smul_zero] at h
    rw [hv, h, algebraMap_smul]

/-- **What a change keeping the claim and the folded table does to the rounds.** If the weight is
zero on the entries of `first`, a change `T` of the stack with zero weighted sum whose folded table
is zero off `first` gives round values whose last running claim (from zero) is zero. -/
theorem roundsMap_mem_ker {k : ℕ} (pos : ι → (Fin k → Bool)) (φ : Fin k → E) (W : LTable E Y k)
    (first : Finset Y) (hW : ∀ b, ∀ y ∈ first, W b y = 0) (T : ι → Y → K)
    (hclaim : ip W (lift pos T) = 0)
    (hfold : ∀ y ∉ first, ∑ l, eqW φ (pos l) * algebraMap K E (T l y) = 0) :
    roundsMap pos φ W T ∈ LinearMap.ker (lastMap (K := K) φ) := by
  rw [LinearMap.mem_ker]
  show lastClaim k φ (laneRounds k φ W (lift pos T)) 0 = 0
  have h := lastClaim_laneRounds k φ W (lift pos T)
  rw [hclaim] at h
  rw [h]
  refine sum_eq_zero fun y _ => ?_
  by_cases hy : y ∈ first
  · rw [foldAll_eq]
    simp [hW _ y hy]
  · rw [foldAll_lift, hfold y hy, mul_zero]

/-- The rounds do not see a change on weightless entries. -/
theorem roundsMap_eq_zero {k : ℕ} (pos : ι → (Fin k → Bool)) (φ : Fin k → E) (W : LTable E Y k)
    (first : Finset Y) (hW : ∀ b, ∀ y ∈ first, W b y = 0) (T : ι → Y → K)
    (hT : ∀ l, ∀ y ∉ first, T l y = 0) : roundsMap pos φ W T = 0 := by
  refine laneRounds_eq_zero_of_disjoint k φ W _ fun y => ?_
  by_cases hy : y ∈ first
  · exact Or.inl fun b => hW b y hy
  · exact Or.inr fun b => by simp [lift, hT _ y hy]

end Stack

end QuotientSecurity.Hiding
