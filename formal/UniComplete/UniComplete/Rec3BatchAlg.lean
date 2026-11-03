-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The algebra of `Rec3Prover.lean`'s paired batch
-- (`crates/leanvm_univariate/src/prover/batch.rs`'s `prove_pairs`, `leanvm-rec` 4247e37).
import UniComplete.Rec3Prover
import UniComplete.BatchProof

/-!
# π1-rec3's batch prover computes the honest round polynomials

The prover's state after the point `r` is its initial tables folded by `r` (`stOf Z r`: the combined claims' weights
and stacks `Z`, each folded low coordinate first, `foldE`). Read as functions (`getD`), a folded table is
`UniSound.foldAll` of the table (`foldl_foldE_getD`), so the batch is the sum of products `prodOf λ V Z`
(`UniSound.ProdSum`: `Σ_k λ^k W_k C_k` over `V` variables, every table zero past its size), and:

* **the pair message is the honest pair polynomial** (`pairMsg_honest`): the nine coefficients `pairMsgOf` computes
  evaluate to `X ↦ (prodOf λ V Z).T (r ++ pairPoint b X)` (each quadruple folded at `pairPoint X` is `quadCoeffs`'
  polynomial, `ev5_quadCoeffs`; products and sums of coefficient lists evaluate to products and sums, `ev9_mul5`,
  `ev9_add9`, …; the weighted sum over the claims is `Σ_k λ^k`, `wsum_map_eq_sum`);
* **the plain message is the honest round polynomial** (`plainMsg_honest`): `[q₀, T(r) + q₂, q₂]` evaluates to
  `X ↦ (prodOf λ V Z).T (r ++ [X])` (characteristic two, `fold_pair_sum`);
* **at the end** (`prodOf_T_full`): at a full point `r` the partial sum is the main line's `terminalOf λ pairs none r`
  (`Σ_k λ^k W̃_k(r) C̃_k(r) Π_{j ≥ d_k} (1 + r_j)²`, `BatchProofSumcheck.foldE_run`), for tables of `2^(d_k)` entries.

Decision (recorded): the sums run over the batch's uniform counts (`2^(V − |r| − 2)` quadruples, `2^(V − |r| − 1)`
pairs), so that the prover's sums are `ProdSum.T`'s exactly, with no size bookkeeping.
-/

namespace UniComplete.Rec3

open UniStatement UniSound LeanVM.Parameters Finset

/-! ## Folds read as functions -/

/-- **A fold of an array, read with `getD`, is `foldT`** (zero past the array). -/
theorem foldE_getD_foldT (v : Array E) (x : E) (i : ℕ) :
    (foldE v x).getD i 0 = foldT (fun j ↦ v.getD j 0) x i := by
  by_cases hi : i < (v.size + 1) / 2
  · rw [foldE_getD v x hi]
    rfl
  · rw [getD_ge _ (by rw [foldE_size]; omega)]
    simp only [foldT]
    rw [getD_ge v (by omega), getD_ge v (by omega)]
    ring

/-- **An array folded by `r`, read with `getD`, is `foldAll` of it.** -/
theorem foldl_foldE_getD : ∀ (r : List E) (v : Array E) (i : ℕ),
    (r.foldl foldE v).getD i 0 = foldAll (fun j ↦ v.getD j 0) r i
  | [], _, _ => rfl
  | x :: r, v, i => by
    rw [List.foldl_cons, foldl_foldE_getD r (foldE v x) i]
    have h : (fun j ↦ (foldE v x).getD j 0) = foldT (fun j ↦ v.getD j 0) x := funext (foldE_getD_foldT v x)
    rw [h]
    rfl

/-! ## The batch as a sum of products -/

/-- **The batch's sum of products** over `V` variables: claim `k`'s weight and stack (`Z`'s `k`-th pair), at `λ^k`. -/
def prodOf (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) : ProdSum :=
  ⟨V, Z.length, fun k ↦ lambda ^ k, fun k i ↦ (Z.getD k (#[], #[])).1.getD i 0,
    fun k i ↦ (Z.getD k (#[], #[])).2.getD i 0⟩

/-- **The prover's state after the point `r`**: every table folded by `r`, no matrices. -/
def stOf (Z : List (Array E × Array E)) (r : List E) : BatchState :=
  ⟨(Z.map (·.1)).map (r.foldl foldE ·), (Z.map (·.2)).map (r.foldl foldE ·), none, 0, r⟩

theorem foldAt_stOf (Z : List (Array E × Array E)) (r : List E) (x : E) :
    foldAt (stOf Z r) x = stOf Z (r ++ [x]) := by
  simp only [foldAt, stOf, List.map_map, Function.comp_def, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The state's tables, zipped: each pair folded. -/
theorem stOf_zip (Z : List (Array E × Array E)) (r : List E) :
    (stOf Z r).weights.zip (stOf Z r).tabs = Z.map fun wc ↦ (r.foldl foldE wc.1, r.foldl foldE wc.2) := by
  simp only [stOf]
  induction Z with
  | nil => rfl
  | cons z Z ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- **A weighted sum is `Σ_k λ^k`.** -/
theorem wsum_map_eq_sum {α : Type} (lambda : E) (F : α → E) (d : α) : ∀ Z : List α,
    wsum lambda (Z.map F) = ∑ k ∈ range Z.length, lambda ^ k * F (Z.getD k d)
  | [] => by simp only [List.map_nil, wsum, List.length_nil, range_zero, sum_empty]
  | z :: Z => by
    have ih := wsum_map_eq_sum lambda F d Z
    simp only [List.map_cons, wsum, ih, List.length_cons]
    rw [sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul]
    rw [add_comm (F z)]
    exact congrArg (· + F z) (sum_congr rfl fun k _ ↦ by ring)

/-- `prodOf`'s partial sum, as `Σ_k λ^k`. -/
theorem prodOf_T (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) (r : List E) :
    (prodOf lambda V Z).T r = ∑ k ∈ range Z.length, lambda ^ k * ∑ i ∈ range (2 ^ (V - r.length)),
      foldAll (fun j ↦ (Z.getD k (#[], #[])).1.getD j 0) r i *
        foldAll (fun j ↦ (Z.getD k (#[], #[])).2.getD j 0) r i := rfl

/-- `prodOf`'s partial sum, as a weighted sum over the claims. -/
theorem prodOf_T_wsum (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) (r : List E) :
    (prodOf lambda V Z).T r = wsum lambda (Z.map fun wc ↦ ∑ i ∈ range (2 ^ (V - r.length)),
      foldAll (fun j ↦ wc.1.getD j 0) r i * foldAll (fun j ↦ wc.2.getD j 0) r i) := by
  rw [wsum_map_eq_sum lambda _ (#[], #[]) Z]
  rfl

/-! ## Polynomials of five and nine coefficients -/

/-- A polynomial of five coefficients, evaluated. -/
def ev5 (p : List E) (x : E) : E :=
  p.getD 0 0 + p.getD 1 0 * x + p.getD 2 0 * x ^ 2 + p.getD 3 0 * x ^ 3 + p.getD 4 0 * x ^ 4

/-- A polynomial of nine coefficients, evaluated. -/
def ev9 (p : List E) (x : E) : E :=
  p.getD 0 0 + p.getD 1 0 * x + p.getD 2 0 * x ^ 2 + p.getD 3 0 * x ^ 3 + p.getD 4 0 * x ^ 4 +
    p.getD 5 0 * x ^ 5 + p.getD 6 0 * x ^ 6 + p.getD 7 0 * x ^ 7 + p.getD 8 0 * x ^ 8

theorem polyEval_eq_ev9 (p : List E) (hp : p.length = 9) (x : E) : polyEval p x = ev9 p x := by
  rw [nine_eq p hp]
  simp only [polyEval, List.foldr_cons, List.foldr_nil, ev9, List.getD_cons_zero, List.getD_cons_succ]
  ring

theorem ev9_add9 (p q : List E) (x : E) : ev9 (add9 p q) x = ev9 p x + ev9 q x := by
  simp only [ev9, add9, List.getD_cons_zero, List.getD_cons_succ]
  ring

theorem ev9_smul9 (s : E) (p : List E) (x : E) : ev9 (smul9 s p) x = s * ev9 p x := by
  simp only [ev9, smul9, List.getD_cons_zero, List.getD_cons_succ]
  ring

theorem ev9_zero9 (x : E) : ev9 zero9 x = 0 := by
  simp only [ev9, zero9, List.getD_cons_zero, List.getD_cons_succ]
  ring

theorem ev9_mul5 (p q : List E) (x : E) : ev9 (mul5 p q) x = ev5 p x * ev5 q x := by
  simp only [ev9, ev5, mul5, List.getD_cons_zero, List.getD_cons_succ]
  ring

theorem length_add9 (p q : List E) : (add9 p q).length = 9 := rfl

/-- **A quadruple folded at `pairPoint x`** is `quadCoeffs`' polynomial at `x` (characteristic two:
`y₀ y₁ = (1 + b) x² + x³ + b x⁴`). -/
theorem ev5_quadCoeffs (b : E) (f : Array E) (i : ℕ) (x : E) :
    ev5 (quadCoeffs b f i) x = foldT (foldT (fun j ↦ f.getD j 0) (x + b * (x * x + x))) (x * x + x) i := by
  simp only [ev5, quadCoeffs, foldT, List.getD_cons_zero, List.getD_cons_succ]
  rw [show 2 * (2 * i) = 4 * i by ring, show 2 * (2 * i + 1) = 4 * i + 2 by ring,
    show 4 * i + 2 + 1 = 4 * i + 3 by ring]
  linear_combination (-(b * (f.getD (4 * i) 0 + f.getD (4 * i + 1) 0 + f.getD (4 * i + 2) 0 +
    f.getD (4 * i + 3) 0) * x ^ 3)) * two_eq_zero_E3

/-- Sums of nine-coefficient polynomials, evaluated. -/
theorem ev9_foldl_add9 (g : ℕ → List E) (x : E) : ∀ n : ℕ,
    ev9 ((List.range n).foldl (fun acc i ↦ add9 acc (g i)) zero9) x = ∑ i ∈ range n, ev9 (g i) x
  | 0 => by simp [ev9_zero9]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ev9_add9, ev9_foldl_add9 g x n,
      sum_range_succ]

theorem ev9_pairPolyOf (b : E) (nq : ℕ) (w c : Array E) (x : E) :
    ev9 (pairPolyOf b nq w c) x = ∑ i ∈ range nq, ev5 (quadCoeffs b w i) x * ev5 (quadCoeffs b c i) x := by
  unfold pairPolyOf
  rw [ev9_foldl_add9 (fun i ↦ mul5 (quadCoeffs b w i) (quadCoeffs b c i)) x nq]
  simp only [ev9_mul5]

/-- The claims' fold of `pairMsgOf`, evaluated. -/
theorem ev9_pairMsg_fold (b lambda : E) (nq : ℕ) (x : E) : ∀ (L : List (Array E × Array E)) (p : List E) (s : E),
    ev9 (L.foldl (fun (acc : List E × E) wc ↦
        (add9 acc.1 (smul9 acc.2 (pairPolyOf b nq wc.1 wc.2)), acc.2 * lambda)) (p, s)).1 x =
      ev9 p x + s * wsum lambda (L.map fun wc ↦ ev9 (pairPolyOf b nq wc.1 wc.2) x)
  | [], p, s => by simp [wsum]
  | wc :: L, p, s => by
    rw [List.foldl_cons, ev9_pairMsg_fold b lambda nq x L, ev9_add9, ev9_smul9, List.map_cons, wsum]
    ring

theorem length_pairMsg_fold (b lambda : E) (nq : ℕ) : ∀ (L : List (Array E × Array E)) (p : List E) (s : E),
    p.length = 9 → (L.foldl (fun (acc : List E × E) wc ↦
        (add9 acc.1 (smul9 acc.2 (pairPolyOf b nq wc.1 wc.2)), acc.2 * lambda)) (p, s)).1.length = 9
  | [], _, _, h => h
  | _ :: L, _, _, _ => length_pairMsg_fold b lambda nq L _ _ (length_add9 _ _)

/-- **The pair message has nine coefficients.** -/
theorem length_pairMsgOf (b lambda : E) (nq : ℕ) (weights tabs : List (Array E)) :
    (pairMsgOf b lambda nq weights tabs).length = 9 :=
  length_pairMsg_fold b lambda nq _ _ _ rfl

/-! ## The pair message is honest -/

/-- One claim's pair polynomial at the state after `r`, evaluated: its tables' quadruples folded at `pairPoint x`. -/
theorem pairPoly_one (b : E) (V : ℕ) (r : List E) (wc : Array E × Array E) (x : E) :
    ev9 (pairPolyOf b (2 ^ (V - r.length - 2)) (r.foldl foldE wc.1) (r.foldl foldE wc.2)) x =
      ∑ i ∈ range (2 ^ (V - (r ++ UniSound.pairPoint b x).length)),
        foldAll (fun j ↦ wc.1.getD j 0) (r ++ UniSound.pairPoint b x) i *
          foldAll (fun j ↦ wc.2.getD j 0) (r ++ UniSound.pairPoint b x) i := by
  rw [ev9_pairPolyOf, ProdSum.length_append_pairPoint, show V - (r.length + 2) = V - r.length - 2 by omega]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [ev5_quadCoeffs, ev5_quadCoeffs, ProdSum.foldAll_append_pairPoint, ProdSum.foldAll_append_pairPoint]
  have e1 : (fun j ↦ (r.foldl foldE wc.1).getD j 0) = foldAll (fun j ↦ wc.1.getD j 0) r :=
    funext (foldl_foldE_getD r wc.1)
  have e2 : (fun j ↦ (r.foldl foldE wc.2).getD j 0) = foldAll (fun j ↦ wc.2.getD j 0) r :=
    funext (foldl_foldE_getD r wc.2)
  rw [e1, e2]

/-- **The pair message is the honest pair polynomial**: at the state after `r` (`stOf Z r`), over the
`2^(V − |r| − 2)` quadruples, `pairMsgOf` evaluates to `X ↦ (prodOf λ V Z).T (r ++ pairPoint b X)`. -/
theorem pairMsg_honest (b lambda : E) (V : ℕ) (Z : List (Array E × Array E)) (r : List E) (x : E) :
    polyEval (pairMsgOf b lambda (2 ^ (V - r.length - 2)) (stOf Z r).weights (stOf Z r).tabs) x =
      (prodOf lambda V Z).T (r ++ UniSound.pairPoint b x) := by
  rw [polyEval_eq_ev9 _ (length_pairMsgOf _ _ _ _ _), pairMsgOf, ev9_pairMsg_fold, ev9_zero9, zero_add, one_mul,
    stOf_zip, List.map_map, prodOf_T_wsum]
  exact wsum_congr _ _ _ _ fun wc _ ↦ pairPoly_one b V r wc x

/-! ## The plain message is honest -/

/-- A fold of `halfSums` pairs: `Σ w₀ c₀` and `Σ (w₀ + w₁)(c₀ + c₁)`. -/
theorem halfSums_eq (nh : ℕ) (w c : Array E) :
    halfSums nh w c = (∑ i ∈ range nh, w.getD (2 * i) 0 * c.getD (2 * i) 0,
      ∑ i ∈ range nh, (w.getD (2 * i) 0 + w.getD (2 * i + 1) 0) * (c.getD (2 * i) 0 + c.getD (2 * i + 1) 0)) := by
  unfold halfSums
  have h := foldl_pair_add (fun i ↦ w.getD (2 * i) 0 * c.getD (2 * i) 0)
    (fun i ↦ (w.getD (2 * i) 0 + w.getD (2 * i + 1) 0) * (c.getD (2 * i) 0 + c.getD (2 * i + 1) 0)) nh 0 0
  simp only [zero_add] at h
  exact h

theorem plainMsg_fold (lambda : E) (nh : ℕ) : ∀ (L : List (Array E × Array E)) (a b s : E),
    L.foldl (fun (acc : E × E × E) wc ↦
        (acc.1 + acc.2.2 * (halfSums nh wc.1 wc.2).1, acc.2.1 + acc.2.2 * (halfSums nh wc.1 wc.2).2,
          acc.2.2 * lambda)) (a, b, s) =
      (a + s * wsum lambda (L.map fun wc ↦ (halfSums nh wc.1 wc.2).1),
        b + s * wsum lambda (L.map fun wc ↦ (halfSums nh wc.1 wc.2).2), s * lambda ^ L.length)
  | [], a, b, s => by simp [wsum]
  | wc :: L, a, b, s => by
    rw [List.foldl_cons, plainMsg_fold lambda nh L]
    simp only [List.map_cons, wsum, List.length_cons, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

theorem plainMsgOf_eq (lambda : E) (nh : ℕ) (weights tabs : List (Array E)) :
    plainMsgOf lambda nh weights tabs =
      (wsum lambda ((weights.zip tabs).map fun wc ↦ (halfSums nh wc.1 wc.2).1),
        wsum lambda ((weights.zip tabs).map fun wc ↦ (halfSums nh wc.1 wc.2).2)) := by
  unfold plainMsgOf
  rw [plainMsg_fold lambda nh _ 0 0 1]
  simp

/-- **One table's fold in characteristic two**: `Σ_i (a₀ + x (a₀ + a₁))(b₀ + x (b₀ + b₁)) =
S₀ + (S₀ + S₁ + S₂) x + S₂ x²`. -/
theorem fold_pair_sum (f g : ℕ → E) (N : ℕ) (x : E) :
    ∑ i ∈ range N, foldT f x i * foldT g x i =
      ∑ i ∈ range N, f (2 * i) * g (2 * i) +
        ((∑ i ∈ range N, (f (2 * i) * g (2 * i) + f (2 * i + 1) * g (2 * i + 1))) +
          ∑ i ∈ range N, (f (2 * i) + f (2 * i + 1)) * (g (2 * i) + g (2 * i + 1))) * x +
        (∑ i ∈ range N, (f (2 * i) + f (2 * i + 1)) * (g (2 * i) + g (2 * i + 1))) * x ^ 2 := by
  simp only [sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [foldT]
  linear_combination (-(f (2 * i + 1) * g (2 * i + 1) * x)) * two_eq_zero_E3

/-- The weighted sums of a quadratic, combined. -/
theorem comb_eq {α : Type} (lambda x : E) (L : List α) (f0 fT f2 F : α → E)
    (h : ∀ a ∈ L, f0 a + (fT a + f2 a) * x + f2 a * x ^ 2 = F a) :
    polyEval [wsum lambda (L.map f0), wsum lambda (L.map fT) + esum [wsum lambda (L.map f2)],
      wsum lambda (L.map f2)] x = wsum lambda (L.map F) := by
  simp only [polyEval, List.foldr_cons, List.foldr_nil, esum, List.foldl_cons, List.foldl_nil, zero_add, zero_mul]
  rw [← wsum_congr lambda _ _ L h, ← wsum_comb]
  ring

/-- One claim's plain round at the state after `r`. -/
theorem plain_one (V : ℕ) (r : List E) (hr : r.length < V) (wc : Array E × Array E) (x : E) :
    (halfSums (2 ^ (V - r.length - 1)) (r.foldl foldE wc.1) (r.foldl foldE wc.2)).1 +
        ((∑ i ∈ range (2 ^ (V - r.length)), foldAll (fun j ↦ wc.1.getD j 0) r i *
          foldAll (fun j ↦ wc.2.getD j 0) r i) +
          (halfSums (2 ^ (V - r.length - 1)) (r.foldl foldE wc.1) (r.foldl foldE wc.2)).2) * x +
        (halfSums (2 ^ (V - r.length - 1)) (r.foldl foldE wc.1) (r.foldl foldE wc.2)).2 * x ^ 2 =
      ∑ i ∈ range (2 ^ (V - (r ++ [x]).length)), foldAll (fun j ↦ wc.1.getD j 0) (r ++ [x]) i *
        foldAll (fun j ↦ wc.2.getD j 0) (r ++ [x]) i := by
  rw [List.length_append, List.length_singleton, show V - (r.length + 1) = V - r.length - 1 by omega,
    show 2 ^ (V - r.length) = 2 * 2 ^ (V - r.length - 1) by rw [← pow_succ']; congr 1; omega,
    ProdSum.sum_range_two_mul, halfSums_eq]
  simp only [foldl_foldE_getD, foldAll_append]
  rw [fold_pair_sum]

/-- **The plain message is the honest round polynomial**: at the state after `r` (`|r| < V`), over the
`2^(V − |r| − 1)` pairs, `[q₀, T(r) + q₂, q₂]` evaluates to `X ↦ (prodOf λ V Z).T (r ++ [X])`. -/
theorem plainMsg_honest (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) (r : List E) (hr : r.length < V)
    (x : E) :
    polyEval [(plainMsgOf lambda (2 ^ (V - r.length - 1)) (stOf Z r).weights (stOf Z r).tabs).1,
        (prodOf lambda V Z).T r + esum [(plainMsgOf lambda (2 ^ (V - r.length - 1)) (stOf Z r).weights
          (stOf Z r).tabs).2],
        (plainMsgOf lambda (2 ^ (V - r.length - 1)) (stOf Z r).weights (stOf Z r).tabs).2] x =
      (prodOf lambda V Z).T (r ++ [x]) := by
  rw [plainMsgOf_eq, stOf_zip, List.map_map, List.map_map, prodOf_T_wsum, prodOf_T_wsum]
  exact comb_eq lambda x Z _ _ _ _ fun wc _ ↦ plain_one V r hr wc x

/-! ## At the end -/

/-- **At a full point the partial sum is the main line's terminal** (`terminalOf λ pairs none r`), for tables of
`2^(d_k)` entries, `d_k ≤ V`. -/
theorem prodOf_T_full (lambda : E) (V : ℕ) (pairs : List (Array E × Array E × ℕ))
    (hwf : ∀ p ∈ pairs, p.1.size = 2 ^ p.2.2 ∧ p.2.1.size = 2 ^ p.2.2 ∧ p.2.2 ≤ V) (r : List E)
    (hr : r.length = V) :
    (prodOf lambda V (pairs.map fun p ↦ (p.1, p.2.1))).T r = terminalOf lambda pairs none r := by
  rw [prodOf_T_wsum, List.map_map, hr, Nat.sub_self, pow_zero]
  unfold terminalOf
  simp only [mul_zero, add_zero]
  refine wsum_congr _ _ _ _ fun p hp ↦ ?_
  have hw := hwf p hp
  obtain ⟨-, g1⟩ := foldE_run p.1 p.2.2 hw.1 r (by omega)
  obtain ⟨-, g2⟩ := foldE_run p.2.1 p.2.2 hw.2.1 r (by omega)
  simp only [Function.comp_apply, range_one, sum_singleton]
  rw [← foldl_foldE_getD, ← foldl_foldE_getD, g1, g2]
  ring

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.pairMsg_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.pairMsg_honest

/-- info: 'UniComplete.Rec3.plainMsg_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.plainMsg_honest

/-- info: 'UniComplete.Rec3.prodOf_T_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.prodOf_T_full
