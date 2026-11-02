-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.Openings
import QuotientZk.Instance.RankGood

/-!
# The simulator's tables, computed

The joint simulator opens, for each secret table, a public table with the verifier's claimed values
(`hsimT`). This file builds those tables by a computable solver and proves that they meet the claims
at every challenge the builder needs (`RankGood`, `RankGood.lean`: `ρ ≠ 1`, and `ρ` or the row of
`t` outside `K`).

**The solver** (`Generic`). A claim is `E`-linear in the table's `K`-valued entries, so over `K` it
is three linear equations. The builder fixes a few **non-random entries** (the table's own: no
padding, no gadget entry) and **virtual columns** on them (`K`-combinations of entries, `Fin 3 →
List`), computes what the claim's weight gives each column (`sparseVal`, three or four evaluations of
the weight), and solves the `3 × 3` system in `E`'s coordinates over `K` (`rep.coords`: the limbs) by
Cramer's rule (`solve3`, `det3`). Among candidate column triples it takes the first whose determinant
is not zero (`pick`); the table is the solution's combination of the columns (`sparse`), zero
everywhere else. Two claims on one table (the quotient table's) are solved one after the other: the
second's on a triple where the first may weigh (`solveTwo`), then the first's, less what that gave
it, on a triple where the second weighs nothing.

* `solveOne_spec`, `solveTwo_spec`: **the table meets the claims** whenever some candidate triple
  has a nonzero determinant (and, for two claims, the second weighs nothing on the first's
  candidates);
* `colDet_ne_zero`: a triple of independent values has a nonzero determinant.

**The deployed tables** (`Deployed`).

* **Witness table** (one claim at `pointW = (ρ, ρ², u_2, …, u_24)`): entries `256 + j` of the
  overflow lane `32` (the first piece of block `0`, held there). On entries `256 + j`, `j < 4`, the
  weight is `R·eq(ρ, j₀)·eq(ρ², j₁)` (`R` the other coordinates' product, never zero), so the columns
  `e₀+e₁+e₂+e₃`, `e₁+e₃`, `e₂+e₃` give `R·(1, ρ, ρ²)`: independent when `ρ ∉ K`. On entries
  `256 + 4j` the weight is `R'·eq(u₂, j₀)·eq(u₃, j₁)`, `u_k = s_k/(1 + s_k)`, `s₃ = s₂² + s₂`, `s₂` the
  row of `t`; the columns `e₀`, `e₁`, `e₁+e₂` give `R'·D·(1, s₂, s₂²)`: independent when `ρ ≠ 1` and
  `s₂ ∉ K`.
* **Quotient table** (claims at `pointQ = (u_0, …, u_25, z, ρ, Y', Y'')`, `z` reading the five values,
  and at the fixed `pointS = (1, …, 1, 0, 0, 0, 0, Y', Y'')`, `Y' = Y/(1+Y)`, `Y'' = Y²/(1+Y²)`): the
  sum claim on entry `2^22 - 1` of the lanes holding blocks `3, 67, 131` (`pointS` weighs
  `g·(1, Y, Y²)` there, `g = (1+Y')(1+Y'')`: always independent); then the first claim on the
  overflow lane's pieces `1, 17, 33` (blocks `0, 64, 128`: weights `U(1+z)(1+ρ)g·(1, Y, Y²)`) or
  `5, 21, 37` (blocks `16, 80, 144`: `U z (1+ρ) g·(1, Y, Y²)`), where `pointS` weighs nothing (its
  first eight coordinates are `1`): one of them is independent when `ρ ≠ 1`.

**`hsimTW`, `hsimTQ`**: at every challenge with `RankGood`, for all five values, the claims of
`simTW rep Y c v` and `simTQ rep P₀ stmt Y c v` are the verifier's (`valsW`, `valsQ`).

**Cost** (`K`- and `E`-operations; `L = 40` or `63` lanes, `H = 33` or `167` held pieces, `n = 25`
or `30` coordinates). One evaluation of a claim's weight at an entry (`Layout.claimW`) is
`O(L·6 + H·n + n)` field operations (the lanes' and pieces' scales, `≈ 4·10^3`). The witness table:
at most `8` weight evaluations, `2` determinants (`12` products each, on `6` coordinate vectors),
one Cramer solve (`4` determinants, `3` divisions), `≤ 4` products for the entries. The quotient
table: `3 + 3 + 6` weight evaluations, `≤ 3` determinants, `2` Cramer solves. In all, `O(m² · f)`
`K`-operations for `m ≤ 2` claims (`3m` equations) on `f ≤ 6` free entries, plus `O(m·f)` weight
evaluations, and the verifier's point and values; reading an entry of the table compares it with
the `≤ 12` listed entries. Nothing here is `noncomputable` (`Test/Builder.lean` runs it).
-/

open Finset Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

namespace Builder

/-! ## The solver -/

section Linear

variable {K : Type} [Field K]

/-- **The determinant of a `3 × 3` matrix**, expanded (`Matrix.det_fin_three`). -/
def det3 (M : Fin 3 → Fin 3 → K) : K :=
  M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
    M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0

/-- Column `j` of `M` replaced by `b`. -/
def setCol (M : Fin 3 → Fin 3 → K) (j : Fin 3) (b : Fin 3 → K) : Fin 3 → Fin 3 → K :=
  fun r c => if c = j then b r else M r c

/-- **Cramer's rule**: `x_j = det(M, column j replaced by b) / det M`. -/
def solve3 (M : Fin 3 → Fin 3 → K) (b : Fin 3 → K) : Fin 3 → K :=
  fun j => det3 (setCol M j b) / det3 M

theorem det3_eq (M : Fin 3 → Fin 3 → K) : det3 M = (Matrix.of M).det := by
  rw [Matrix.det_fin_three]
  rfl

theorem solve3_eq (M : Fin 3 → Fin 3 → K) (b : Fin 3 → K) :
    solve3 M b = (det3 M)⁻¹ • (Matrix.of M).cramer b := by
  funext j
  simp only [solve3, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, det3_eq, div_eq_inv_mul]
  congr 2
  ext r c
  simp [setCol, Matrix.updateCol_apply]

/-- **Cramer's rule solves the system** when the determinant is not zero. -/
theorem mulVec_solve3 {M : Fin 3 → Fin 3 → K} (b : Fin 3 → K) (h : det3 M ≠ 0) (r : Fin 3) :
    ∑ c, M r c * solve3 M b c = b r := by
  have hc : Matrix.mulVec (Matrix.of M) (solve3 M b) = b := by
    rw [solve3_eq, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, ← det3_eq,
      inv_mul_cancel₀ h, one_smul]
  have := congrFun hc r
  simpa [Matrix.mulVec, dotProduct] using this

variable {E : Type} [Field E] [Algebra K E] (co : E ≃ₗ[K] (Fin 3 → K))

/-- **The solution of `Σ_i x_i c_i = v`** over `K` (`c_i`, `v` in `E`), in the coordinates `co`. -/
def solveE (co : E → Fin 3 → K) (c : Fin 3 → E) (v : E) : Fin 3 → K :=
  solve3 (fun r i => co (c i) r) (co v)

/-- The system's determinant. -/
def colDet (co : E → Fin 3 → K) (c : Fin 3 → E) : K := det3 fun r i => co (c i) r

theorem co_sum (x : Fin 3 → K) (c : Fin 3 → E) :
    co (∑ i, x i • c i) = fun r => ∑ i, co (c i) r * x i := by
  funext r
  simp [map_sum, map_smul, mul_comm]

theorem solveE_spec {c : Fin 3 → E} (v : E) (h : colDet co c ≠ 0) :
    ∑ i, solveE co c v i • c i = v := by
  refine co.injective ?_
  rw [co_sum]
  funext r
  exact mulVec_solve3 (co v) h r

/-- **Independent values have a nonzero determinant.** -/
theorem colDet_ne_zero {c : Fin 3 → E} (hc : LinearIndependent K c) : colDet co c ≠ 0 := by
  intro h0
  rw [colDet, det3_eq, ← Matrix.exists_mulVec_eq_zero_iff] at h0
  obtain ⟨x, hx, hMx⟩ := h0
  refine hx (funext fun i => Fintype.linearIndependent_iff.mp hc x ?_ i)
  refine co.injective ?_
  rw [co_sum, map_zero]
  funext r
  have := congrFun hMx r
  simpa [Matrix.mulVec, dotProduct] using this

/-- A nonzero multiple of independent values. -/
theorem indep_mul {v : Fin 3 → E} (hv : LinearIndependent K v) {C : E} (hC : C ≠ 0) :
    LinearIndependent K fun i => C * v i :=
  hv.map' (LinearMap.mulLeft K C) (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hC))

/-- **`C, Ca, Ca²` are independent** when `a ∉ K` and `C ≠ 0` (`[E : K] = 3`). -/
theorem indep_powers [FiniteDimensional K E] (h3 : finrank K E = 3) {a : E}
    (ha : a ∉ Set.range (algebraMap K E)) {C : E} (hC : C ≠ 0) :
    LinearIndependent K ![C, C * a, C * a ^ 2] := by
  have hdeg := natDegree_minpoly_eq_three h3 ha
  have hli : LinearIndependent K fun i : Fin 3 => a ^ (i : ℕ) := hdeg ▸ linearIndependent_pow a
  convert indep_mul hli hC using 1
  funext i
  fin_cases i <;> simp

/-- **`C, CY, CY²` are independent** when `1, Y, Y²` are and `C ≠ 0`. -/
theorem indep_basis {Y : E} (hY : LinearIndependent K ![1, Y, Y ^ 2]) {C : E} (hC : C ≠ 0) :
    LinearIndependent K ![C, C * Y, C * Y ^ 2] := by
  convert indep_mul hY hC using 1
  funext i
  fin_cases i <;> simp

end Linear

/-! ### Sparse tables -/

section Sparse

variable {K E ι Y : Type} [Field K] [Field E] [Algebra K E] [DecidableEq ι] [DecidableEq Y]

/-- **A sparse table**: listed entries and values (a repeated entry adds), zero elsewhere. -/
def sparse (es : List ((ι × Y) × K)) : ι → Y → K :=
  fun l y => (es.map fun p => if p.1 = (l, y) then p.2 else 0).sum

/-- What a weight gives a sparse table. -/
def sparseVal (w : ι → Y → E) (es : List ((ι × Y) × K)) : E :=
  (es.map fun p => p.2 • w p.1.1 p.1.2).sum

/-- A column scaled. -/
def scaleCol (a : K) (V : List ((ι × Y) × K)) : List ((ι × Y) × K) :=
  V.map fun p => (p.1, a * p.2)

/-- **`Σ_i x_i V_i`**, as one list. -/
def comb (x : Fin 3 → K) (V : Fin 3 → List ((ι × Y) × K)) : List ((ι × Y) × K) :=
  scaleCol (x 0) (V 0) ++ scaleCol (x 1) (V 1) ++ scaleCol (x 2) (V 2)

theorem sparseVal_append (w : ι → Y → E) (a b : List ((ι × Y) × K)) :
    sparseVal w (a ++ b) = sparseVal w a + sparseVal w b := by
  simp [sparseVal]

theorem sparseVal_scaleCol (w : ι → Y → E) (a : K) (V : List ((ι × Y) × K)) :
    sparseVal w (scaleCol a V) = a • sparseVal w V := by
  induction V with
  | nil => simp [sparseVal, scaleCol]
  | cons p V ih =>
    simp only [sparseVal, scaleCol, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add, mul_smul]

theorem sparseVal_comb (w : ι → Y → E) (x : Fin 3 → K) (V : Fin 3 → List ((ι × Y) × K)) :
    sparseVal w (comb x V) = ∑ i, x i • sparseVal w (V i) := by
  simp only [comb, sparseVal_append, sparseVal_scaleCol, Fin.sum_univ_three]

theorem sparseVal_eq_zero (w : ι → Y → E) {es : List ((ι × Y) × K)}
    (h : ∀ p ∈ es, w p.1.1 p.1.2 = 0) : sparseVal w es = 0 := by
  induction es with
  | nil => simp [sparseVal]
  | cons p es ih =>
    simp only [sparseVal, List.map_cons, List.sum_cons] at ih ⊢
    rw [h p List.mem_cons_self, smul_zero, zero_add,
      ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem mem_comb {x : Fin 3 → K} {V : Fin 3 → List ((ι × Y) × K)} {p : (ι × Y) × K}
    (hp : p ∈ comb x V) : ∃ i, ∃ q ∈ V i, q.1 = p.1 := by
  simp only [comb, scaleCol, List.mem_append, List.mem_map] at hp
  rcases hp with (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
  · exact ⟨0, q, hq, rfl⟩
  · exact ⟨1, q, hq, rfl⟩
  · exact ⟨2, q, hq, rfl⟩

variable [Fintype ι] [Fintype Y]

theorem sparse_cons (p : (ι × Y) × K) (es : List ((ι × Y) × K)) :
    sparse (p :: es) = (fun l y => if p.1 = (l, y) then p.2 else 0) + sparse es := by
  funext l y
  simp [sparse]

/-- **The claims of a sparse table on non-random entries**: each claim is what its weight gives
the list. -/
theorem claimsMap_stackD_sparse (L : GadgetLayout ι Y) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (es : List ((ι × Y) × K)) (hes : ∀ p ∈ es, ¬ L.randPos p.1.1 p.1.2) (j : Fin m) :
    HiddenLayout.claimsMap Wc (L.stackD (sparse es)) j = sparseVal (Wc j) es := by
  induction es with
  | nil =>
    have h0 : sparse ([] : List ((ι × Y) × K)) = 0 := by funext l y; simp [sparse]
    rw [h0, map_zero, map_zero]
    simp [sparseVal]
  | cons p es ih =>
    rw [sparse_cons, map_add, map_add, Pi.add_apply,
      ih fun q hq => hes q (List.mem_cons_of_mem _ hq)]
    simp only [sparseVal, List.map_cons, List.sum_cons]
    congr 1
    have hp := hes p List.mem_cons_self
    show ∑ l, ∑ y, Wc j l y * algebraMap K E
        (if L.randPos l y then 0 else (if p.1 = (l, y) then p.2 else 0)) = p.2 • Wc j p.1.1 p.1.2
    rw [Finset.sum_eq_single p.1.1, Finset.sum_eq_single p.1.2]
    · rw [if_neg hp, if_pos rfl, Algebra.smul_def, mul_comm]
    · intro y _ hy
      have : p.1 ≠ (p.1.1, y) := fun h => hy (congrArg Prod.snd h).symm
      simp [this]
    · simp
    · intro l _ hl
      refine Finset.sum_eq_zero fun y _ => ?_
      have : p.1 ≠ (l, y) := fun h => hl (congrArg Prod.fst h).symm
      simp [this]
    · simp

end Sparse

/-! ### The builder -/

section Build

variable {K E ι Y : Type} [Field K] [DecidableEq K] [Field E] [Algebra K E] [DecidableEq ι]
  [DecidableEq Y]

/-- A triple of virtual columns. -/
abbrev Cols (ι Y K : Type) := Fin 3 → List ((ι × Y) × K)

/-- What a weight gives each column of a triple. -/
def colVals (w : ι → Y → E) (V : Cols ι Y K) : Fin 3 → E := fun i => sparseVal w (V i)

/-- **The first candidate triple with a nonzero determinant.** -/
def pick (co : E → Fin 3 → K) (w : ι → Y → E) : List (Cols ι Y K) → Option (Cols ι Y K)
  | [] => none
  | V :: Vs => if colDet co (colVals w V) ≠ 0 then some V else pick co w Vs

/-- **One claim**: the first good candidate's columns, combined by Cramer's solution. -/
def solveOne (co : E → Fin 3 → K) (w : ι → Y → E) (cands : List (Cols ι Y K)) (v : E) :
    List ((ι × Y) × K) :=
  match pick co w cands with
  | none => []
  | some V => comb (solveE co (colVals w V) v) V

/-- **Two claims**: the second's on `S`, then the first's, less what `S`'s part gives it, on a
candidate where the second weighs nothing. -/
def solveTwo (co : E → Fin 3 → K) (w₁ w₂ : ι → Y → E) (S : Cols ι Y K)
    (cands : List (Cols ι Y K)) (v₁ v₂ : E) : List ((ι × Y) × K) :=
  let xs := comb (solveE co (colVals w₂ S) v₂) S
  xs ++ solveOne co w₁ cands (v₁ - sparseVal w₁ xs)

theorem pick_some (co : E → Fin 3 → K) (w : ι → Y → E) {cands : List (Cols ι Y K)}
    (h : ∃ V ∈ cands, colDet co (colVals w V) ≠ 0) :
    ∃ V ∈ cands, pick co w cands = some V ∧ colDet co (colVals w V) ≠ 0 := by
  induction cands with
  | nil => simp at h
  | cons V Vs ih =>
    by_cases hV : colDet co (colVals w V) ≠ 0
    · exact ⟨V, List.mem_cons_self, by simp [pick, hV], hV⟩
    · obtain ⟨V', hV', hd⟩ := h
      rcases List.mem_cons.mp hV' with rfl | hm
      · exact absurd hd hV
      · obtain ⟨W, hW, hp, hdW⟩ := ih ⟨V', hm, hd⟩
        exact ⟨W, List.mem_cons_of_mem _ hW, by simp [pick, hV, hp], hdW⟩

theorem mem_of_pick (co : E → Fin 3 → K) (w : ι → Y → E) {cands : List (Cols ι Y K)}
    {V : Cols ι Y K} (h : pick co w cands = some V) : V ∈ cands := by
  induction cands with
  | nil => simp [pick] at h
  | cons W Ws ih =>
    by_cases hW : colDet co (colVals w W) ≠ 0
    · simp only [pick, hW, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq] at h
      exact h ▸ List.mem_cons_self
    · simp only [pick, hW, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- **One claim is met** when some candidate has a nonzero determinant. -/
theorem solveOne_spec (co : E ≃ₗ[K] (Fin 3 → K)) (w : ι → Y → E) {cands : List (Cols ι Y K)}
    (h : ∃ V ∈ cands, colDet co (colVals w V) ≠ 0) (v : E) :
    sparseVal w (solveOne co w cands v) = v := by
  obtain ⟨V, -, hp, hd⟩ := pick_some co w h
  simp only [solveOne, hp, sparseVal_comb]
  exact solveE_spec co v hd

/-- The entries `solveOne` lists are its candidates'. -/
theorem mem_solveOne (co : E → Fin 3 → K) (w : ι → Y → E) {cands : List (Cols ι Y K)} {v : E}
    {p : (ι × Y) × K} (hp : p ∈ solveOne co w cands v) :
    ∃ V ∈ cands, ∃ i, ∃ q ∈ V i, q.1 = p.1 := by
  unfold solveOne at hp
  split at hp
  · simp at hp
  · rename_i V hV
    exact ⟨V, mem_of_pick co w hV, mem_comb hp⟩

/-- **Two claims are met**: the second's triple has a nonzero determinant, some candidate for the
first has one, and the second weighs nothing on the candidates. -/
theorem solveTwo_spec (co : E ≃ₗ[K] (Fin 3 → K)) (w₁ w₂ : ι → Y → E) {S : Cols ι Y K}
    {cands : List (Cols ι Y K)} (hS : colDet co (colVals w₂ S) ≠ 0)
    (h : ∃ V ∈ cands, colDet co (colVals w₁ V) ≠ 0)
    (hz : ∀ V ∈ cands, ∀ i, ∀ q ∈ V i, w₂ q.1.1 q.1.2 = 0) (v₁ v₂ : E) :
    sparseVal w₁ (solveTwo co w₁ w₂ S cands v₁ v₂) = v₁ ∧
      sparseVal w₂ (solveTwo co w₁ w₂ S cands v₁ v₂) = v₂ := by
  simp only [solveTwo, sparseVal_append]
  constructor
  · rw [solveOne_spec co w₁ h]
    ring
  · rw [sparseVal_eq_zero w₂ (es := solveOne co w₁ cands _) fun p hp => ?_, add_zero,
      sparseVal_comb]
    · exact solveE_spec co v₂ hS
    · obtain ⟨V, hV, i, q, hq, hqp⟩ := mem_solveOne co w₁ hp
      rw [← hqp]
      exact hz V hV i q hq

theorem mem_solveTwo (co : E → Fin 3 → K) (w₁ w₂ : ι → Y → E) {S : Cols ι Y K}
    {cands : List (Cols ι Y K)} {v₁ v₂ : E} {p : (ι × Y) × K}
    (hp : p ∈ solveTwo co w₁ w₂ S cands v₁ v₂) :
    (∃ i, ∃ q ∈ S i, q.1 = p.1) ∨ ∃ V ∈ cands, ∃ i, ∃ q ∈ V i, q.1 = p.1 := by
  simp only [solveTwo, List.mem_append] at hp
  rcases hp with hp | hp
  · exact Or.inl (mem_comb hp)
  · exact Or.inr (mem_solveOne co w₁ hp)

end Build

/-! ## The deployed weights on a few entries -/

section Weights

open QuotientSecurity.Hiding.Deployed

variable {E : Type} [Field E]

/-- `eq` on one coordinate: `a` at a one, `1 + a` at a zero. -/
def eqB (a : E) (b : Bool) : E := if b then a else 1 + a

theorem eqBits_nil (idx : ℕ) : eqBits ([] : List E) idx = 1 := by simp [eqBits]

/-- **`eqBits`, one coordinate off**: the first coordinate reads the index's low bit. -/
theorem eqBits_cons (a : E) (l : List E) (idx : ℕ) :
    eqBits (a :: l) idx = (if idx % 2 = 1 then a else 1 + a) * eqBits l (idx / 2) := by
  unfold eqBits
  rw [List.length_cons, Finset.prod_range_succ', mul_comm]
  congr 1
  · simp [Nat.testBit_zero]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [List.getD_cons_succ, Nat.testBit_succ]

/-- `eqBits` reads the index's low bits only. -/
theorem eqBits_mod (l : List E) (idx : ℕ) : eqBits l idx = eqBits l (idx % 2 ^ l.length) := by
  unfold eqBits
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Nat.testBit_mod_two_pow, decide_eq_true (Finset.mem_range.mp hk), Bool.true_and]

theorem eqBits_append (l₁ l₂ : List E) (idx : ℕ) :
    eqBits (l₁ ++ l₂) idx = eqBits l₁ idx * eqBits l₂ (idx / 2 ^ l₁.length) := by
  induction l₁ generalizing idx with
  | nil => simp [eqBits_nil]
  | cons a l ih =>
    rw [List.cons_append, eqBits_cons, eqBits_cons, ih, List.length_cons, mul_assoc,
      Nat.div_div_eq_div_mul, pow_succ, mul_comm (2 ^ l.length) 2]

/-- No coordinate is `1`. -/
def NZ (l : List E) : Prop := ∀ x ∈ l, 1 + x ≠ 0

theorem eqBits_zero_ne {l : List E} (hl : NZ l) : eqBits l 0 ≠ 0 := by
  induction l with
  | nil => simp [eqBits_nil]
  | cons a l ih =>
    rw [eqBits_cons]
    simp only [Nat.zero_mod, zero_ne_one, ↓reduceIte, Nat.zero_div]
    exact mul_ne_zero (hl a List.mem_cons_self) (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem NZ.take {l : List E} (h : NZ l) (n : ℕ) : NZ (l.take n) :=
  fun x hx => h x (List.mem_of_mem_take hx)

theorem NZ.drop {l : List E} (h : NZ l) (n : ℕ) : NZ (l.drop n) :=
  fun x hx => h x (List.mem_of_mem_drop hx)

theorem take_bits (n m y : ℕ) (hm : m ≤ n) : (bits n y : List E).take m = bits m y := by
  unfold bits
  rw [← List.map_take, List.take_range, min_eq_left hm]

theorem getD_map_of_lt {α β : Type} (f : α → β) (l : List α) {k : ℕ} (hk : k < l.length)
    (d : β) (d' : α) : (l.map f).getD k d = f (l.getD k d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk, List.getElem_map]

variable (h2 : (2 : E) = 0)
include h2

/-- `w / (1 + w)` is never `1` (characteristic 2; `w / 0 = 0`). -/
theorem one_add_div_ne (w : E) : 1 + w / (1 + w) ≠ 0 := by
  by_cases hw : 1 + w = 0
  · rw [hw, div_zero, add_zero]
    exact one_ne_zero
  · intro h
    have e : (1 + w / (1 + w)) * (1 + w) = 1 := by
      rw [add_mul, div_mul_cancel₀ w hw]
      linear_combination w * h2
    rw [h, zero_mul] at e
    exact zero_ne_one e

/-- `w / (1 + w) = w (1 + w / (1 + w))` when `1 + w ≠ 0`. -/
theorem div_eq_mul_one_add {w : E} (hw : 1 + w ≠ 0) : w / (1 + w) = w * (1 + w / (1 + w)) := by
  apply mul_right_cancel₀ hw
  rw [div_mul_cancel₀ w hw, mul_assoc, add_mul, one_mul, div_mul_cancel₀ w hw]
  linear_combination (-(w * w)) * h2

theorem nz_ofFn {n : ℕ} (f : Fin n → E) (hf : ∀ i, ∃ w, f i = w / (1 + w)) : NZ (List.ofFn f) := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  obtain ⟨w, hw⟩ := hf i
  rw [hw]
  exact one_add_div_ne h2 w

open QuotientSecurity.Hiding.Deployed.Layout

variable {L : Layout}

/-- **The weight on the overflow lane's held pieces**: `eq` of the point's first eight coordinates
at the entry's low byte, times the held piece's scale. -/
theorem claimW_ov (h : L.OK) {m : ℕ} (points : Fin m → List E) (c : Fin m)
    (y : Fin (2 ^ L.logLane)) (hy1 : 2 ^ 8 ≤ (y : ℕ))
    (hy2 : (y : ℕ) < (L.pieces.length + 1) * 2 ^ 8) :
    L.claimW points c ⟨32, h.n32⟩ y = eqBits ((points c).take 8) y *
      eqBits ((points c).drop 8) (L.pieces.getD ((y : ℕ) / 2 ^ 8 - 1) 0) := by
  have hs : L.logPiece = 8 := h.piece
  have hl8 : 8 < L.logLane := h.lane
  have hov : L.overflow = 32 := h.overflow
  have hat : L.lanes[32]? = some .overflow := h.at_ov
  set pt := points c
  set Yv := (y : ℕ) / 2 ^ 8 with hYdef
  have hy := y.isLt
  have hY1 : 1 ≤ Yv := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa using hy1)
  have hYH : Yv ≤ L.pieces.length := by
    have := (Nat.div_lt_iff_lt_mul (show 0 < 2 ^ 8 by norm_num)).mpr hy2
    omega
  have hfit : L.pieces.length + 1 ≤ 2 ^ (L.logLane - logPieceD) := by
    have hf := h.fits
    have hl := h.lane
    rw [show L.logLane = (L.logLane - logPieceD) + logPieceD by omega, pow_add] at hf
    exact le_of_mul_le_mul_right hf (by norm_num [logPieceD])
  change L.pieces.length + 1 ≤ 2 ^ (L.logLane - 8) at hfit
  have hYlt : Yv < 2 ^ (L.logLane - 8) := by omega
  have hb : (L.lanes.getD 32 .random).isBlock = false := by
    rw [List.getD_eq_getElem?_getD, hat]
    rfl
  have hpl : (L.part 1 pt).pieces.length = L.pieces.length := by simp [part, pieceScales]
  have hpt : piecesTerm 8 (bits L.logLane y) (L.part 1 pt) =
      eqBits (pt.drop 8) (L.pieces.getD (Yv - 1) 0) := by
    unfold piecesTerm
    rw [drop_bits, Nat.shiftRight_eq_div_pow, ← hYdef, Finset.sum_eq_single (Yv - 1)]
    · rw [eqBits_bits_eq h2 hYlt (by omega), if_pos (by omega), mul_one]
      show ((L.pieceScales pt).map (1 * ·)).getD (Yv - 1) 0 = _
      rw [getD_map_mul, one_mul]
      unfold pieceScales
      rw [hs]
      exact getD_map_of_lt _ _ (by omega) 0 0
    · intro k hk hne
      rw [hpl, Finset.mem_range] at hk
      rw [eqBits_bits_eq h2 hYlt (by omega), if_neg (by omega), mul_zero]
    · intro hni
      rw [hpl, Finset.mem_range] at hni
      omega
  simp only [claimW, claimTerm, hs]
  rw [onBlocks_zero h2 h _ h.n32 hb, hov, getD_laneEqAt_eq h2 h h.n32 h.n32, if_pos rfl, hpt]
  have hlow : (L.part 1 pt).low = pt.take L.logLane := rfl
  rw [hlow, List.take_take, min_eq_left hl8.le, take_bits _ _ _ hl8.le,
    eqZ_bits h2 (pt.take 8) 8 _ (List.length_take_le _ _)]
  ring

/-- **The weight on a block lane**, past the first piece: `eq` of the point's lane coordinates at
the entry, times the lane's block scale. -/
theorem claimW_block (h : L.OK) {m : ℕ} (points : Fin m → List E) (c : Fin m)
    (l : Fin L.lanes.length) {b : ℕ} (hb : L.lanes[(l : ℕ)]? = some (.block b))
    (y : Fin (2 ^ L.logLane)) (hy1 : 2 ^ 8 ≤ (y : ℕ)) :
    L.claimW points c l y = eqBits ((points c).take 8) y *
      eqBits (((points c).take L.logLane).drop 8) ((y : ℕ) / 2 ^ 8) *
      eqBits ((points c).drop L.logLane) b := by
  have hs : L.logPiece = 8 := h.piece
  have hl8 : 8 < L.logLane := h.lane
  have hov : L.overflow = 32 := h.overflow
  set pt := points c
  have hy := y.isLt
  have hl32 : (l : ℕ) ≠ 32 := by
    intro he
    have hat : L.lanes[32]? = some .overflow := h.at_ov
    rw [← he, hb] at hat
    simp at hat
  have hYlt : (y : ℕ) / 2 ^ 8 < 2 ^ (L.logLane - 8) := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_add, Nat.sub_add_cancel hl8.le]
    exact hy
  have hY1 : 1 ≤ (y : ℕ) / 2 ^ 8 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa using hy1)
  have hfp : onePlusProd ((bits L.logLane y : List E).drop 8) = 0 := by
    rw [onePlusProd_eq, drop_bits, Nat.shiftRight_eq_div_pow,
      eqBits_bits_eq h2 hYlt (Nat.two_pow_pos _), if_neg (by omega)]
  have hon : L.onBlocks (L.laneEqAt l) (L.part 1 pt) = eqBits (pt.drop L.logLane) b := by
    unfold onBlocks
    rw [Finset.sum_eq_single (l : ℕ)]
    · have hgb : L.lanes.getD l .random = .block b := by
        rw [List.getD_eq_getElem?_getD, hb]
        rfl
      rw [hgb, getD_laneEqAt_eq h2 h l.isLt l.isLt, if_pos rfl]
      simp only [Lane.isBlock, ↓reduceIte, mul_one]
      show ((L.laneScales pt).map (1 * ·)).getD l 0 = _
      rw [getD_map_mul, one_mul]
      unfold laneScales
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hb]
      rfl
    · intro k hk hne
      rw [getD_laneEqAt_eq h2 h l.isLt (Finset.mem_range.mp hk), if_neg hne]
      simp
    · intro hni
      exact absurd (Finset.mem_range.mpr l.isLt) hni
  simp only [claimW, claimTerm, hs]
  rw [hon, hfp, hov, getD_laneEqAt_eq h2 h l.isLt h.n32, if_neg (fun e => hl32 e.symm)]
  have hlow : (L.part 1 pt).low = pt.take L.logLane := rfl
  rw [hlow, List.take_take, min_eq_left hl8.le, take_bits _ _ _ hl8.le,
    eqZ_bits h2 (pt.take 8) 8 _ (List.length_take_le _ _), drop_bits, Nat.shiftRight_eq_div_pow,
    eqZ_bits h2 ((pt.take L.logLane).drop 8) (L.logLane - 8) _ (by simp; omega)]
  ring

/-- Entries of the overflow lane's held pieces are the table's. -/
theorem not_randPos_ov (h : L.OK) (y : Fin (2 ^ L.logLane)) (hy1 : 2 ^ 8 ≤ (y : ℕ))
    (hy2 : (y : ℕ) < (L.pieces.length + 1) * 2 ^ 8) :
    ¬ (L.toGadget h).randPos ⟨32, h.n32⟩ y := by
  intro hr
  unfold GadgetLayout.randPos GadgetLayout.AtGadget at hr
  rcases hr with hf | ⟨p, hp⟩ | hr | ⟨-, hh⟩
  · simp [toGadget, firstFree] at hf
    omega
  · have := (atPat_iff h p y).mp hp
    have := p.isLt
    omega
  · exact (L.toGadget h).not_rand_ov hr
  · apply hh
    show y ∈ L.heldSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy1, hy2⟩

/-- Entries of a block lane past the first piece are the table's. -/
theorem not_randPos_block (h : L.OK) (l : Fin L.lanes.length) {b : ℕ}
    (hb : L.lanes[(l : ℕ)]? = some (.block b)) (y : Fin (2 ^ L.logLane)) (hy1 : 2 ^ 8 ≤ (y : ℕ)) :
    ¬ (L.toGadget h).randPos l y := by
  intro hr
  unfold GadgetLayout.randPos GadgetLayout.AtGadget at hr
  rcases hr with hf | ⟨p, hp⟩ | hr | ⟨hl, -⟩
  · simp [toGadget, firstFree] at hf
    omega
  · have := (atPat_iff h p y).mp hp
    have := p.isLt
    omega
  · change L.lanes[(l : ℕ)]? = some .random at hr
    rw [hb] at hr
    simp at hr
  · have h32 : (l : ℕ) = 32 := congrArg Fin.val hl
    have hat : L.lanes[32]? = some .overflow := h.at_ov
    rw [← h32, hb] at hat
    simp at hat

end Weights

end Builder

end QuotientZk.Instance
