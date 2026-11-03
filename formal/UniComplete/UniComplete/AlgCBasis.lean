-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Honest
import UniComplete.Domain
import UniComplete.Whir
import Bridge.Ntt

/-!
# The columns' polynomials and their values (milestone 4, the algebra, item 1(a))

The honest prover holds a column of `2^r` values `v` as the polynomial `colPolyK r v = ofNovel r d`, `d` its novel
coefficients (`PcsQuotient.Domain.coefficients`, the additive transform), and commits its basis-`B` coefficients
`bCoefficients r v = subsetSums r d` (`c_k = Σ_{j ⊆ k} d_j`, since `B_k = Σ_{j ⊇ k} X_j`). Here, for proofs, in
Mathlib's `Polynomial E` (CompPoly's `toPoly`):

* **`wPoly_toPoly`**: `wPoly l` is `Domain.wP l` (`w_0 = X`, `w_{l+1} = w_l² + w_l`).
* **`novP`**: the polynomial `Σ_k d_k X_k`, `X_k = Π_{l ∈ k} w_l`, split on the top variable as `ofNovelWith` is
  (`ofNovel_toPoly`); **`novP_eval`** its value `Σ_k d_k Π_{l : k_l} w_l(t)`; `novP_natDegree_lt`: degree `< 2^m`;
  **`novP_eq_zero_above`**: the coefficients above the degree vanish.
* **`toNovel_spec`**: `toNovel m p` has `2^m` entries and is `p`'s novel coefficients when `deg p < 2^m`
  (`Div`'s `toPoly_divM`, `toPoly_modM`).
* **The subset sums** (`ss_getD`): `(subsetSums r d)_k = Σ_{j ⊆ k} d_j` (any additive monoid; `subsetSumsE`,
  `UniStatement.subsetSums` are its instances), and **the multilinear extension** (`mle_eq_sum`): `multilinearEval`
  of `2^n` entries at a point is `Σ_x a_x Π_l (p_l if x_l else 1 + p_l)` (Whir's `foldl_foldOnce`).
* **`evalB_subsetSumsE`**: `evalB (subsetSumsE m d) m (digits t n) = pEval t (ofNovel m d)` (`m ≤ n`,
  `d.size = 2^m`): the basis-`B` coefficients at the digits are the novel polynomial at `t`. Hence
  **`evalB_bCoefficients`**: the verifier's reading of a committed column at `t` is the prover's polynomial at `t`.
* **`pEval_colPolyK_pointE`**: `colPolyK r v` interpolates `v` on `V_r`, `pEval (pointE i) (colPolyK r v) = ofK v_i`
  (`i < 2^r`, `r ≤ 28`), by `Bridge.Ntt` (the additive transform is the novel basis).

**Finding (recorded):** `PcsQuotient.Domain.coefficients` is the statement's transform of `crates/quotient`, over its
basis of `28` vectors (`betaAt k = 0` for `k ≥ 28`). `Shape.validate` admits heights up to `31`; at a height
`29 ≤ r ≤ 31` the transform's twiddles at the top stages collide (`point (2 j)` reads bit `28` of `2 j` as `0`), so
`colPolyK r v` does not interpolate `v` on `V_r` and the honest prover's constraint quotient does not divide. Every
statement here is at `r ≤ 28`; at those heights the stacks exceed WHIR's `2^28` words anyway.
-/

namespace UniComplete.AlgC

open UniStatement LeanVM.Parameters Polynomial Finset

/-! ### CompPoly to Mathlib -/

theorem tp_add (p q : Poly) : (p + q).toPoly = p.toPoly + q.toPoly := CompPoly.CPolynomial.toPoly_add p q

theorem tp_mul (p q : Poly) : (p * q).toPoly = p.toPoly * q.toPoly := CompPoly.CPolynomial.toPoly_mul p q

theorem tp_C (x : E) : (pC x).toPoly = C x := CompPoly.CPolynomial.C_toPoly x

theorem tp_X : pX.toPoly = X := CompPoly.CPolynomial.X_toPoly

theorem tp_one : (1 : Poly).toPoly = 1 := CompPoly.CPolynomial.toPoly_one

theorem tp_zero : (0 : Poly).toPoly = 0 := CompPoly.CPolynomial.toPoly_zero

theorem tp_pow (p : Poly) (n : ℕ) : (p ^ n).toPoly = p.toPoly ^ n := CompPoly.CPolynomial.toPoly_pow p n

/-- **`pEval` is Mathlib's evaluation** of `toPoly`. -/
theorem pEval_eq (t : E) (p : Poly) : pEval t p = p.toPoly.eval t := CompPoly.CPolynomial.eval_toPoly t p

/-- `s(x) = x² + x`, iterated. -/
abbrev sIter (l : ℕ) (t : E) : E := (fun x : E ↦ x * x + x)^[l] t

/-! ### The digits' polynomials -/

theorem wPolys_succ (n : ℕ) : wPolys (n + 1) =
    (match (wPolys n).back? with
      | some w => (wPolys n).push (w * w + w)
      | none => (wPolys n).push pX) := by
  unfold wPolys
  rw [List.range_succ, List.foldl_append]
  rfl

theorem wPolys_spec : ∀ n, (wPolys n).size = n ∧ ∀ l < n, ((wPolys n).getD l 0).toPoly = Domain.wP l
  | 0 => ⟨rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hs, hg⟩ := wPolys_spec n
    rw [wPolys_succ]
    rcases n with _ | n
    · have h0 : wPolys 0 = #[] := rfl
      rw [h0]
      refine ⟨rfl, fun l hl ↦ ?_⟩
      obtain rfl : l = 0 := by omega
      show pX.toPoly = Domain.wP 0
      rw [tp_X, Domain.wP_zero]
    · have hb : (wPolys (n + 1)).back? = some ((wPolys (n + 1)).getD n 0) := by
        rw [Array.back?_eq_getElem?, hs, Nat.add_sub_cancel, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem (by omega)]
        rfl
      rw [hb]
      refine ⟨by simp [hs], fun l hl ↦ ?_⟩
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
      by_cases h : l = (wPolys (n + 1)).size
      · have hl' : l = n + 1 := by rw [h, hs]
        rw [Domain.ite_pos_of h, Option.getD_some, hl', Domain.wP_succ, tp_add, tp_mul, hg n (by omega), pow_two]
      · rw [Domain.ite_neg_of h, ← Array.getD_eq_getD_getElem?]
        exact hg l (by omega)

/-- **`wPoly l` is `w_l`.** -/
theorem wPoly_toPoly (l : ℕ) : (wPoly l).toPoly = Domain.wP l := (wPolys_spec (l + 1)).2 l (by omega)

theorem wP_eval_eq (l : ℕ) (t : E) : (Domain.wP l).eval t = sIter l t := Domain.wP_eval t l

/-- `w_l` is monic, as a `Poly`. -/
theorem wPoly_monic (l : ℕ) : (wPoly l).toPoly.Monic := by rw [wPoly_toPoly]; exact Domain.wP_monic l

/-! ### The novel basis -/

/-- **The polynomial of novel coefficients** `Σ_{k < 2^m} d_k X_k`, split on the top variable. -/
noncomputable def novP : ℕ → (ℕ → E) → E[X]
  | 0, d => C (d 0)
  | m + 1, d => novP m d + Domain.wP m * novP m (fun k ↦ d (2 ^ m + k))

theorem novP_zero (d : ℕ → E) : novP 0 d = C (d 0) := rfl

theorem novP_succ (m : ℕ) (d : ℕ → E) :
    novP (m + 1) d = novP m d + Domain.wP m * novP m (fun k ↦ d (2 ^ m + k)) := rfl

theorem novP_congr : ∀ (m : ℕ) {d d' : ℕ → E}, (∀ k < 2 ^ m, d k = d' k) → novP m d = novP m d'
  | 0, d, d', h => by rw [novP_zero, novP_zero, h 0 (by norm_num)]
  | m + 1, d, d', h => by
    rw [novP_succ, novP_succ, novP_congr m (fun k hk ↦ h k (by rw [pow_succ]; omega)),
      novP_congr m (d := fun k ↦ d (2 ^ m + k)) (d' := fun k ↦ d' (2 ^ m + k))
        (fun k hk ↦ h _ (by rw [pow_succ]; omega))]

theorem novP_zero_fun : ∀ m : ℕ, novP m (fun _ ↦ 0) = 0
  | 0 => by
    show C (0 : E) = 0
    exact C_0
  | m + 1 => by
    show novP m (fun _ ↦ 0) + Domain.wP m * novP m (fun _ ↦ 0) = 0
    rw [novP_zero_fun m, mul_zero, add_zero]

theorem getD_extract' (d : Array E) (a b k : ℕ) (hk : k < b - a) : (d.extract a b).getD k 0 = d.getD (a + k) 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split_ifs with h
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]

theorem ofNovelWith_toPoly (ws : Array Poly) (M : ℕ) (hws : ∀ l < M, (ws.getD l 0).toPoly = Domain.wP l) :
    ∀ m ≤ M, ∀ d : Array E, (ofNovelWith ws m d).toPoly = novP m (fun k ↦ d.getD k 0)
  | 0, _, d => by
    show (pC (d.getD 0 0)).toPoly = _
    rw [tp_C, novP_zero]
  | m + 1, hm, d => by
    show (ofNovelWith ws m (d.extract 0 (2 ^ m)) +
      ws.getD m 0 * ofNovelWith ws m (d.extract (2 ^ m) (2 * 2 ^ m))).toPoly = _
    rw [tp_add, tp_mul, hws m (by omega), ofNovelWith_toPoly ws M hws m (by omega),
      ofNovelWith_toPoly ws M hws m (by omega), novP_succ,
      novP_congr m (d := fun k ↦ (d.extract 0 (2 ^ m)).getD k 0) (d' := fun k ↦ d.getD k 0)
        (fun k hk ↦ by rw [getD_extract' d 0 _ k (by omega), Nat.zero_add]),
      novP_congr m (d := fun k ↦ (d.extract (2 ^ m) (2 * 2 ^ m)).getD k 0) (d' := fun k ↦ d.getD (2 ^ m + k) 0)
        (fun k hk ↦ getD_extract' d _ _ k (by omega))]

/-- **`ofNovel m d` is `Σ_k d_k X_k`.** -/
theorem ofNovel_toPoly (m : ℕ) (d : Array E) : (ofNovel m d).toPoly = novP m (fun k ↦ d.getD k 0) :=
  ofNovelWith_toPoly (wPolys m) m (wPolys_spec m).2 m le_rfl d

/-- `X_k` at the digits `w`: `Π_{l < m, k_l} w_l`. -/
def novX (m k : ℕ) (w : ℕ → E) : E := ∏ l ∈ range m, if k.testBit l then w l else 1

theorem novX_low {m k : ℕ} (hk : k < 2 ^ m) (w : ℕ → E) : novX (m + 1) k w = novX m k w := by
  rw [novX, Finset.prod_range_succ, Nat.testBit_eq_false_of_lt hk]
  simp [novX]

theorem novX_high {m k : ℕ} (hk : k < 2 ^ m) (w : ℕ → E) : novX (m + 1) (2 ^ m + k) w = w m * novX m k w := by
  rw [novX, Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hk]
  simp only [Bool.not_false, ite_true]
  rw [mul_comm]
  refine congrArg (w m * ·) (Finset.prod_congr rfl fun l hl ↦ ?_)
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hl)]

/-- **The novel polynomial at `t`**: `Σ_k d_k Π_{l : k_l} w_l(t)`. -/
theorem novP_eval (t : E) : ∀ (m : ℕ) (d : ℕ → E),
    (novP m d).eval t = ∑ k ∈ range (2 ^ m), d k * novX m k (fun l ↦ (Domain.wP l).eval t)
  | 0, d => by simp [novP_zero, novX]
  | m + 1, d => by
    rw [novP_succ, Polynomial.eval_add, Polynomial.eval_mul, novP_eval t m, novP_eval t m, pow_succ, mul_two, Finset.sum_range_add,
      Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k hk ↦ ?_) (Finset.sum_congr rfl fun k hk ↦ ?_)
    · rw [novX_low (Finset.mem_range.mp hk)]
    · rw [novX_high (Finset.mem_range.mp hk)]
      ring

theorem novP_natDegree_lt : ∀ (m : ℕ) (d : ℕ → E), (novP m d).natDegree < 2 ^ m
  | 0, d => by rw [novP_zero, natDegree_C]; norm_num
  | m + 1, d => by
    rw [novP_succ]
    have h1 := novP_natDegree_lt m d
    have h2 := novP_natDegree_lt m (fun k ↦ d (2 ^ m + k))
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (by rw [pow_succ]; omega) ?_)
    refine lt_of_le_of_lt (natDegree_mul_le) ?_
    rw [Domain.wP_natDegree, pow_succ]
    omega

theorem novP_degree_lt (m : ℕ) (d : ℕ → E) : (novP m d).degree < (2 ^ m : ℕ) :=
  lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 (novP_natDegree_lt m d))

/-- **The novel coefficients above the degree vanish**: if `Σ d_k X_k` has degree `< N`, then `d_k = 0` for
`N ≤ k < 2^m` (`X_k` has degree `k`). -/
theorem novP_eq_zero_above : ∀ (m : ℕ) (d : ℕ → E) (N : ℕ), (novP m d).degree < N →
    ∀ k, N ≤ k → k < 2 ^ m → d k = 0
  | 0, d, N, h, k, hNk, hk => by
    obtain rfl : k = 0 := by omega
    obtain rfl : N = 0 := by omega
    rw [novP_zero] at h
    have : C (d 0) = 0 := by
      by_contra hne
      exact absurd h (not_lt.2 (by rw [degree_C (fun h0 ↦ hne (by rw [h0, C_0]))]; exact le_refl _))
    exact C_eq_zero.mp this
  | m + 1, d, N, h, k, hNk, hk => by
    rw [novP_succ] at h
    set A := novP m d
    set B := novP m (fun k ↦ d (2 ^ m + k))
    have hA := novP_degree_lt m d
    by_cases hB : B = 0
    · have hB0 : ∀ k', k' < 2 ^ m → d (2 ^ m + k') = 0 :=
        fun k' hk' ↦ novP_eq_zero_above m (fun k ↦ d (2 ^ m + k)) 0 (by
          show B.degree < (0 : ℕ)
          rw [hB, degree_zero]; exact WithBot.bot_lt_coe 0) k' (Nat.zero_le _) hk'
      rw [hB, mul_zero, add_zero] at h
      by_cases hkm : k < 2 ^ m
      · exact novP_eq_zero_above m d N h k hNk hkm
      · have := hB0 (k - 2 ^ m) (by rw [pow_succ] at hk; omega)
        rwa [Nat.add_sub_cancel' (by omega)] at this
    · have hdeg : (Domain.wP m * B).degree = (2 ^ m + B.natDegree : ℕ) := by
        have hne : Domain.wP m * B ≠ 0 := mul_ne_zero (Domain.wP_monic m).ne_zero hB
        rw [degree_eq_natDegree hne, (Domain.wP_monic m).natDegree_mul' hB, Domain.wP_natDegree]
      have hlt : A.degree < (Domain.wP m * B).degree := by
        rw [hdeg]
        exact lt_of_lt_of_le hA (by exact_mod_cast Nat.le_add_right _ _)
      rw [degree_add_eq_right_of_degree_lt hlt, hdeg] at h
      have hN : 2 ^ m + B.natDegree < N := by exact_mod_cast h
      have hk' : 2 ^ m ≤ k := by omega
      have hBd : B.degree < (N - 2 ^ m : ℕ) := by
        rw [degree_eq_natDegree hB]
        exact_mod_cast (show B.natDegree < N - 2 ^ m by omega)
      have := novP_eq_zero_above m (fun k ↦ d (2 ^ m + k)) (N - 2 ^ m) hBd (k - 2 ^ m) (by omega)
        (by rw [pow_succ] at hk; omega)
      rwa [Nat.add_sub_cancel' hk'] at this

/-- **`Σ d_k X_k` over `2^a` coefficients is over `2^b`** when the coefficients from `2^b` on vanish (`b ≤ a`). -/
theorem novP_of_zero_above {b : ℕ} : ∀ (a : ℕ) (d : ℕ → E), b ≤ a → (∀ k, 2 ^ b ≤ k → k < 2 ^ a → d k = 0) →
    novP a d = novP b d
  | a, d, hba, h => by
    induction a with
    | zero =>
      obtain rfl : b = 0 := by omega
      rfl
    | succ a ih =>
      rcases Nat.eq_or_lt_of_le hba with heq | hlt
      · rw [heq]
      · rw [novP_succ, ih (by omega) (fun k hk hka ↦ h k hk (by rw [pow_succ]; omega))]
        rw [novP_congr a (d' := fun _ ↦ 0) (fun k hk ↦ h _ (by
          have : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega) (by rw [pow_succ]; omega)), novP_zero_fun, mul_zero, add_zero]

/-! ### The novel coefficients of a polynomial -/

theorem getD_append_lt (A B : Array E) {k : ℕ} (hk : k < A.size) : (A ++ B).getD k 0 = A.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append_left hk]

theorem getD_append_ge (A B : Array E) {k : ℕ} (hk : A.size ≤ k) : (A ++ B).getD k 0 = B.getD (k - A.size) 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append_right hk]

theorem toNovelWith_spec (ws : Array Poly) (M : ℕ) (hws : ∀ l < M, (ws.getD l 0).toPoly = Domain.wP l) :
    ∀ m ≤ M, ∀ p : Poly, p.toPoly.natDegree < 2 ^ m →
      (toNovelWith ws m p).size = 2 ^ m ∧ novP m (fun k ↦ (toNovelWith ws m p).getD k 0) = p.toPoly
  | 0, _, p, hp => by
    refine ⟨rfl, ?_⟩
    show C ((#[p.coeff 0] : Array E).getD 0 0) = p.toPoly
    rw [show (#[p.coeff 0] : Array E).getD 0 0 = p.coeff 0 from rfl, CompPoly.CPolynomial.coeff_toPoly]
    exact (eq_C_of_natDegree_eq_zero (by omega)).symm
  | m + 1, hm, p, hp => by
    have hw := hws m (by omega)
    have hmon : (ws.getD m 0).toPoly.Monic := hw ▸ Domain.wP_monic m
    have hA := toNovelWith_spec ws M hws m (by omega) (modM p (ws.getD m 0)) (by
      rw [toPoly_modM _ _ hmon, hw]
      have h1 : (Domain.wP m) ≠ 1 := fun h1 ↦ by
        have := Domain.wP_natDegree m
        rw [h1, natDegree_one] at this
        exact absurd this (by positivity)
      have := natDegree_modByMonic_lt p.toPoly (Domain.wP_monic m) h1
      rwa [Domain.wP_natDegree] at this)
    have hB := toNovelWith_spec ws M hws m (by omega) (divM p (ws.getD m 0)) (by
      rw [toPoly_divM _ _ hmon, hw, natDegree_divByMonic _ (Domain.wP_monic m), Domain.wP_natDegree]
      rw [pow_succ] at hp
      omega)
    set A := toNovelWith ws m (modM p (ws.getD m 0)) with hAdef
    set B := toNovelWith ws m (divM p (ws.getD m 0)) with hBdef
    show (A ++ B).size = _ ∧ novP (m + 1) (fun k ↦ (A ++ B).getD k 0) = _
    refine ⟨by rw [Array.size_append, hA.1, hB.1, pow_succ]; ring, ?_⟩
    have e1 : novP m (fun k ↦ (A ++ B).getD k 0) = novP m (fun k ↦ A.getD k 0) :=
      novP_congr m fun k hk ↦ getD_append_lt A B (by rw [hA.1]; exact hk)
    have e2 : novP m (fun k ↦ (A ++ B).getD (2 ^ m + k) 0) = novP m (fun k ↦ B.getD k 0) :=
      novP_congr m fun k hk ↦ by rw [getD_append_ge A B (by rw [hA.1]; omega), hA.1, Nat.add_sub_cancel_left]
    rw [novP_succ, e1, e2, hA.2, hB.2, toPoly_modM _ _ hmon, toPoly_divM _ _ hmon, hw]
    exact modByMonic_add_div p.toPoly (Domain.wP m)

/-- **`toNovel m p`: `2^m` entries, `p`'s novel coefficients** (`deg p < 2^m`). -/
theorem toNovel_spec (m : ℕ) (p : Poly) (hp : p.toPoly.natDegree < 2 ^ m) :
    (toNovel m p).size = 2 ^ m ∧ novP m (fun k ↦ (toNovel m p).getD k 0) = p.toPoly :=
  toNovelWith_spec (wPolys m) m (wPolys_spec m).2 m le_rfl p hp

/-- **`toNovel` inverts `ofNovel`** below degree `2^m`. -/
theorem ofNovel_toNovel (m : ℕ) (p : Poly) (hp : p.toPoly.natDegree < 2 ^ m) : ofNovel m (toNovel m p) = p :=
  CompPoly.CPolynomial.toPoly_inj.mp (by rw [ofNovel_toPoly, (toNovel_spec m p hp).2])

/-! ### The subset sums -/

section SubsetSums

variable {M : Type*} [AddCommMonoid M]

/-- One step of the subset-sum transform, on bit `l`. -/
def ssStep (a : Array M) (l : ℕ) : Array M :=
  Array.ofFn (n := a.size) fun k ↦ if k.val.testBit l then a.getD k.val 0 + a.getD (k.val - 2 ^ l) 0
    else a.getD k.val 0

theorem ssStep_size (a : Array M) (l : ℕ) : (ssStep a l).size = a.size := by simp [ssStep]

theorem ssFold_size (d : Array M) (l : ℕ) : ((List.range l).foldl ssStep d).size = d.size := by
  induction l with
  | zero => rfl
  | succ l ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ssStep_size, ih]

theorem getD_ofFn_M {n : ℕ} (f : Fin n → M) {j : ℕ} (hj : j < n) : (Array.ofFn f).getD j 0 = f ⟨j, hj⟩ := by
  simp [Array.getD_eq_getD_getElem?, hj]

theorem testBit_of_mod_eq {x y l b : ℕ} (h : x % 2 ^ l = y % 2 ^ l) (hb : b < l) :
    x.testBit b = y.testBit b := by
  have hx := Nat.testBit_mod_two_pow x l b
  have hy := Nat.testBit_mod_two_pow y l b
  rw [h, hy] at hx
  simp only [hb, decide_true, Bool.true_and] at hx
  exact hx.symm

theorem sub_two_pow_mod {k l : ℕ} (hle : 2 ^ l ≤ k) : (k - 2 ^ l) % 2 ^ l = k % 2 ^ l := by
  conv_rhs => rw [show k = (k - 2 ^ l) + 2 ^ l by omega]
  rw [Nat.add_mod_right]

theorem mod_pow_succ_of_testBit {k l : ℕ} (hk : k.testBit l = true) : k % 2 ^ (l + 1) = k % 2 ^ l + 2 ^ l := by
  have h1 : k / 2 ^ l % 2 = 1 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hk
    exact of_decide_eq_true hk
  rw [Nat.mod_pow_succ, h1, mul_one]

theorem mod_pow_succ_of_not_testBit {k l : ℕ} (hk : ¬ k.testBit l = true) : k % 2 ^ (l + 1) = k % 2 ^ l := by
  have h1 : k / 2 ^ l % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hk
    have := Nat.mod_lt (k / 2 ^ l) (by norm_num : 0 < 2)
    simp only [decide_eq_true_eq] at hk
    omega
  rw [Nat.mod_pow_succ, h1, mul_zero, add_zero]

/-- **The subset sums after the bits below `l`**: entry `k` is the sum over the submasks `j` of `k`'s low `l`
bits, `k`'s high bits kept. -/
theorem ss_inv (d : Array M) : ∀ l, ∀ k < d.size, ((List.range l).foldl ssStep d).getD k 0 =
    ∑ j ∈ range (2 ^ l), if (∀ b < l, j.testBit b = true → k.testBit b = true) then
      d.getD (k - k % 2 ^ l + j) 0 else 0
  | 0, k, hk => by simp [Nat.mod_one]
  | l + 1, k, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ha : ((List.range l).foldl ssStep d).size = d.size := ssFold_size d l
    rw [ssStep, getD_ofFn_M _ (by rw [ha]; exact hk)]
    dsimp only
    have hlow : ∀ j ∈ range (2 ^ l), (∀ b < l + 1, j.testBit b = true → k.testBit b = true) ↔
        (∀ b < l, j.testBit b = true → k.testBit b = true) := by
      intro j hj
      constructor
      · intro h b hb
        exact h b (by omega)
      · intro h b hb hjb
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
        · exact h b hb hjb
        · rw [Nat.testBit_eq_false_of_lt (Finset.mem_range.mp hj)] at hjb
          exact absurd hjb (by simp)
    have hhigh : ∀ j ∈ range (2 ^ l), (∀ b < l + 1, (2 ^ l + j).testBit b = true → k.testBit b = true) ↔
        ((∀ b < l, j.testBit b = true → k.testBit b = true) ∧ k.testBit l = true) := by
      intro j hj
      constructor
      · intro h
        refine ⟨fun b hb hjb ↦ h b (by omega) (by rw [Nat.testBit_two_pow_add_gt hb]; exact hjb), h l (by omega) ?_⟩
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt (Finset.mem_range.mp hj)]
        rfl
      · rintro ⟨h, hkl⟩ b hb hjb
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
        · rw [Nat.testBit_two_pow_add_gt hb] at hjb
          exact h b hb hjb
        · exact hkl
    have hsplit : (∑ j ∈ range (2 ^ (l + 1)), if (∀ b < l + 1, j.testBit b = true → k.testBit b = true) then
        d.getD (k - k % 2 ^ (l + 1) + j) 0 else 0) =
        (∑ j ∈ range (2 ^ l), if (∀ b < l, j.testBit b = true → k.testBit b = true) then
          d.getD (k - k % 2 ^ (l + 1) + j) 0 else 0) +
        (∑ j ∈ range (2 ^ l), if ((∀ b < l, j.testBit b = true → k.testBit b = true) ∧ k.testBit l = true) then
          d.getD (k - k % 2 ^ (l + 1) + (2 ^ l + j)) 0 else 0) := by
      rw [show range (2 ^ (l + 1)) = range (2 ^ l + 2 ^ l) by rw [pow_succ, mul_two], Finset.sum_range_add]
      exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj ↦ if_congr (hlow j hj) rfl rfl)
        (Finset.sum_congr rfl fun j hj ↦ if_congr (hhigh j hj) rfl rfl)
    rw [hsplit]
    have hkm : k % 2 ^ l ≤ k := Nat.mod_le _ _
    have hkm' : k % 2 ^ (l + 1) ≤ k := Nat.mod_le _ _
    by_cases hkl : k.testBit l = true
    · rw [Domain.ite_pos_of hkl]
      have hmod := mod_pow_succ_of_testBit hkl
      have hle : 2 ^ l ≤ k := Nat.ge_two_pow_of_testBit hkl
      rw [ss_inv d l k hk, ss_inv d l (k - 2 ^ l) (by omega)]
      refine (add_comm _ _).trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ ↦ ?_)
        (Finset.sum_congr rfl fun j _ ↦ ?_))
      · have hm2 := sub_two_pow_mod hle
        have hcond : (∀ b < l, j.testBit b = true → (k - 2 ^ l).testBit b = true) ↔
            (∀ b < l, j.testBit b = true → k.testBit b = true) := by
          constructor
          · intro h b hb hjb
            rw [← testBit_of_mod_eq hm2 hb]
            exact h b hb hjb
          · intro h b hb hjb
            rw [testBit_of_mod_eq hm2 hb]
            exact h b hb hjb
        exact if_congr hcond (congrArg (d.getD · 0) (by rw [hm2, hmod]; omega)) rfl
      · exact if_congr (and_iff_left hkl).symm (congrArg (d.getD · 0) (by rw [hmod]; omega)) rfl
    · rw [Domain.ite_neg_of hkl]
      have hmod := mod_pow_succ_of_not_testBit hkl
      rw [ss_inv d l k hk]
      have hz : (∑ j ∈ range (2 ^ l), if ((∀ b < l, j.testBit b = true → k.testBit b = true) ∧ k.testBit l = true)
          then d.getD (k - k % 2 ^ (l + 1) + (2 ^ l + j)) 0 else 0) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ Domain.ite_neg_of fun h ↦ hkl h.2
      rw [hz, add_zero, hmod]

/-- **The subset sums** of `2^m` entries: `c_k = Σ_{j ⊆ k} d_j`. -/
theorem ss_getD (d : Array M) (m : ℕ) (hd : d.size = 2 ^ m) {k : ℕ} (hk : k < 2 ^ m) :
    ((List.range m).foldl ssStep d).getD k 0 =
      ∑ j ∈ range (2 ^ m), if (∀ b < m, j.testBit b = true → k.testBit b = true) then d.getD j 0 else 0 := by
  rw [ss_inv d m k (by omega), Nat.mod_eq_of_lt hk, Nat.sub_self]
  simp only [Nat.zero_add]

end SubsetSums

theorem subsetSumsE_eq (r : ℕ) (d : Array E) : subsetSumsE r d = (List.range r).foldl ssStep d := rfl

theorem subsetSums_eq (r : ℕ) (d : Array K) : UniStatement.subsetSums r d = (List.range r).foldl ssStep d := rfl

theorem subsetSumsE_size (r : ℕ) (d : Array E) : (subsetSumsE r d).size = d.size := by
  rw [subsetSumsE_eq, ssFold_size]

theorem bCoefficients_size (r : ℕ) (v : Array K) : (bCoefficients r v).size = v.size := by
  unfold bCoefficients
  rw [subsetSums_eq, ssFold_size, Bridge.Ntt.coefficients_size]

/-! ### The multilinear extension -/

theorem eqEval_boolPoint : ∀ (pt : List E) (x : ℕ),
    LeanVM.Protocol.Verifier.eqEval (LeanVM.Protocol.EndToEnd.boolPoint pt.length x) pt =
      ∏ l ∈ range pt.length, (if x.testBit l then pt.getD l 0 else 1 + pt.getD l 0)
  | [], x => by simp
  | q :: qs, x => by
    rw [List.length_cons, LeanVM.Protocol.Whir.Complete.boolPoint_succ, LeanVM.Protocol.Whir.Complete.eqEval_cons,
      eqEval_boolPoint qs (x / 2), Finset.prod_range_succ', mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun l _ ↦ ?_
      rw [Nat.testBit_div_two]
      rfl
    · have h2 : (1 : E) + 1 = 0 := CharTwo.add_self_eq_zero 1
      by_cases hb : x.testBit 0 = true
      · simp only [hb, ite_true, List.getD_cons_zero]
        rw [h2, zero_add]
      · simp only [hb, Bool.false_eq_true, ite_false, List.getD_cons_zero, add_zero]

/-- **The multilinear extension of `2^n` entries**, low coordinate first: `Σ_x a_x Π_l (p_l if x_l else 1 + p_l)`. -/
theorem mle_eq_sum (a : Array E) (pt : List E) (ha : a.size = 2 ^ pt.length) :
    multilinearEval a.toList pt = ∑ x ∈ range (2 ^ pt.length),
      a.getD x 0 * ∏ l ∈ range pt.length, (if x.testBit l then pt.getD l 0 else 1 + pt.getD l 0) := by
  unfold multilinearEval
  rw [Array.toArray_toList, UniComplete.foldl_foldOnce pt a ha]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqEval_boolPoint]

/-- `Σ_{x ⊇ j} Π_l (p_l if x_l else 1 + p_l) = Π_{l : j_l} p_l` (characteristic two). -/
theorem superset_sum (p : ℕ → E) : ∀ (r j : ℕ),
    ∑ x ∈ range (2 ^ r), (if (∀ b < r, j.testBit b = true → x.testBit b = true) then
      ∏ l ∈ range r, (if x.testBit l then p l else 1 + p l) else 0) =
    ∏ l ∈ range r, (if j.testBit l then p l else 1)
  | 0, j => by simp
  | r + 1, j => by
    rw [pow_succ, mul_two, Finset.sum_range_add, Finset.prod_range_succ]
    have hlo : ∀ x ∈ range (2 ^ r), (if (∀ b < r + 1, j.testBit b = true → x.testBit b = true) then
        ∏ l ∈ range (r + 1), (if x.testBit l then p l else 1 + p l) else 0) =
        (if j.testBit r = true then 0 else 1 + p r) *
          (if (∀ b < r, j.testBit b = true → x.testBit b = true) then
            ∏ l ∈ range r, (if x.testBit l then p l else 1 + p l) else 0) := by
      intro x hx
      have hxr : x.testBit r = false := Nat.testBit_eq_false_of_lt (Finset.mem_range.mp hx)
      rw [Finset.prod_range_succ, hxr]
      by_cases hjr : j.testBit r = true
      · have hn : ¬ (∀ b < r + 1, j.testBit b = true → x.testBit b = true) := by
          intro h
          have := h r (by omega) hjr
          rw [hxr] at this
          exact absurd this (by simp)
        rw [Domain.ite_pos_of hjr, zero_mul, Domain.ite_neg_of hn]
      · rw [Domain.ite_neg_of hjr]
        have hc : (∀ b < r + 1, j.testBit b = true → x.testBit b = true) ↔
            (∀ b < r, j.testBit b = true → x.testBit b = true) := by
          constructor
          · intro h b hb
            exact h b (by omega)
          · intro h b hb hjb
            rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
            · exact h b hb hjb
            · exact absurd hjb hjr
        rw [if_congr hc rfl rfl]
        by_cases hcr : (∀ b < r, j.testBit b = true → x.testBit b = true)
        · rw [Domain.ite_pos_of hcr, Domain.ite_pos_of hcr]
          simp [mul_comm]
        · rw [Domain.ite_neg_of hcr, Domain.ite_neg_of hcr, mul_zero]
    have hhi : ∀ x ∈ range (2 ^ r), (if (∀ b < r + 1, j.testBit b = true → (2 ^ r + x).testBit b = true) then
        ∏ l ∈ range (r + 1), (if (2 ^ r + x).testBit l then p l else 1 + p l) else 0) =
        p r * (if (∀ b < r, j.testBit b = true → x.testBit b = true) then
            ∏ l ∈ range r, (if x.testBit l then p l else 1 + p l) else 0) := by
      intro x hx
      have hxr : (2 ^ r + x).testBit r = true := by
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt (Finset.mem_range.mp hx)]
        rfl
      have hlow : ∀ l ∈ range r, (2 ^ r + x).testBit l = x.testBit l := fun l hl ↦
        Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hl) x
      have hc : (∀ b < r + 1, j.testBit b = true → (2 ^ r + x).testBit b = true) ↔
          (∀ b < r, j.testBit b = true → x.testBit b = true) := by
        constructor
        · intro h b hb hjb
          rw [← hlow b (Finset.mem_range.mpr hb)]
          exact h b (by omega) hjb
        · intro h b hb hjb
          rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
          · rw [hlow b (Finset.mem_range.mpr hb)]
            exact h b hb hjb
          · exact hxr
      rw [if_congr hc rfl rfl, Finset.prod_range_succ, hxr, Domain.ite_pos_of rfl,
        Finset.prod_congr rfl (fun l hl ↦ by rw [hlow l hl])]
      split_ifs <;> simp [mul_comm]
    rw [Finset.sum_congr rfl hlo, Finset.sum_congr rfl hhi, ← Finset.mul_sum, ← Finset.mul_sum,
      superset_sum p r j, ← add_mul]
    have h2 : p r + p r = 0 := CharTwo.add_self_eq_zero (p r)
    by_cases hjr : j.testBit r = true
    · rw [Domain.ite_pos_of hjr, Domain.ite_pos_of hjr, zero_add, mul_comm]
    · rw [Domain.ite_neg_of hjr, Domain.ite_neg_of hjr, add_assoc, h2, add_zero, one_mul, mul_one]

/-- **The multilinear extension of the subset sums is the novel sum** (characteristic two):
`Σ_x (Σ_{j ⊆ x} d_j) Π_l (p_l if x_l else 1 + p_l) = Σ_j d_j Π_{l : j_l} p_l`. -/
theorem mle_subsetSums (p : ℕ → E) (d : ℕ → E) (r : ℕ) :
    ∑ x ∈ range (2 ^ r), (∑ j ∈ range (2 ^ r),
        if (∀ b < r, j.testBit b = true → x.testBit b = true) then d j else 0) *
      ∏ l ∈ range r, (if x.testBit l then p l else 1 + p l) =
    ∑ j ∈ range (2 ^ r), d j * novX r j p := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [novX, ← superset_sum p r j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs <;> simp

theorem take_digits_getD (t : E) {m n l : ℕ} (hmn : m ≤ n) (hl : l < m) :
    ((digits t n).take m).getD l 0 = (Domain.wP l).eval t := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, Domain.ite_pos_of hl, ← List.getD_eq_getElem?_getD,
    Domain.wP_eval_digits t (n := n) (by omega)]

theorem length_take_digits (t : E) {m n : ℕ} (hmn : m ≤ n) : ((digits t n).take m).length = m := by
  rw [List.length_take, Domain.length_digits]
  omega

/-- **The basis-`B` coefficients at the digits are the novel polynomial at `t`**: `evalB (subsetSumsE m d) m
(digits t n) = pEval t (ofNovel m d)`, for `2^m` coefficients and `m ≤ n`. -/
theorem evalB_subsetSumsE (m n : ℕ) (d : Array E) (hd : d.size = 2 ^ m) (hmn : m ≤ n) (t : E) :
    evalB (subsetSumsE m d) m (digits t n) = pEval t (ofNovel m d) := by
  unfold evalB
  have hlen := length_take_digits t hmn
  rw [mle_eq_sum _ _ (by rw [hlen, subsetSumsE_size, hd]), hlen, pEval_eq, ofNovel_toPoly, novP_eval]
  rw [Finset.sum_congr rfl (fun x hx ↦ by
    rw [subsetSumsE_eq, ss_getD d m hd (Finset.mem_range.mp hx),
      Finset.prod_congr rfl (fun l hl ↦ by rw [take_digits_getD t hmn (Finset.mem_range.mp hl)])])]
  exact mle_subsetSums (fun l ↦ (Domain.wP l).eval t) (fun j ↦ d.getD j 0) m

theorem getD_map_ofK (a : Array K) (k : ℕ) : (a.map ofK).getD k 0 = ofK (a.getD k 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[k]? with
  | none => exact Domain.embed_zero.symm
  | some x => rfl

/-- **The committed coefficients, read in `E`, are the subset sums of the novel ones.** -/
theorem bCoefficients_map (r : ℕ) (v : Array K) (hv : v.size = 2 ^ r) :
    (bCoefficients r v).map ofK = subsetSumsE r (novelOfValuesK r v) := by
  have hc : (PcsQuotient.Domain.coefficients r 0 v).size = 2 ^ r := by
    rw [Bridge.Ntt.coefficients_size, hv]
  refine Bridge.Ntt.array_ext_getD_E (by
    rw [Array.size_map, bCoefficients_size, subsetSumsE_size, novelOfValuesK, Array.size_map, hc, hv]) fun k hk ↦ ?_
  rw [Array.size_map, bCoefficients_size, hv] at hk
  rw [getD_map_ofK, bCoefficients, subsetSums_eq, ss_getD _ r hc hk, subsetSumsE_eq,
    ss_getD _ r (by rw [novelOfValuesK, Array.size_map, hc]) hk, Domain.embed_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs
  · rw [novelOfValuesK, getD_map_ofK]
  · exact Domain.embed_zero

/-- **The verifier's value of a committed column at `t` is the prover's polynomial at `t`**: `evalB` of the column's
basis-`B` coefficients (in `E`) at the digits of `t` is `colPolyK r v` at `t` (`r ≤ n`, `2^r` values). -/
theorem evalB_bCoefficients (r n : ℕ) (v : Array K) (hv : v.size = 2 ^ r) (hrn : r ≤ n) (t : E) :
    evalB ((bCoefficients r v).map ofK) r (digits t n) = pEval t (colPolyK r v) := by
  rw [bCoefficients_map r v hv, evalB_subsetSumsE r n _ (by
    rw [novelOfValuesK, Array.size_map, Bridge.Ntt.coefficients_size, hv]) hrn]
  rfl

/-! ### Interpolation on `V_r` -/

/-- The statement's first `28` basis vectors are the verifier's: a Cantor basis (`Bridge.Ntt.CantorUpTo`). -/
theorem cantorUpTo {r : ℕ} (hr : r ≤ 28) : Bridge.Ntt.CantorUpTo r := by
  refine ⟨?_, fun k hk ↦ ?_⟩
  · rw [← Domain.beta_getD_eq_betaAt (by norm_num), Domain.beta_zero]
  · rw [← Domain.beta_getD_eq_betaAt (by omega), ← Domain.beta_getD_eq_betaAt (by omega)]
    exact Domain.beta_succ (by omega)

/-- **The statement's point is the verifier's** below `2^28`. -/
theorem Ppoint_eq {i : ℕ} (hi : i < 2 ^ 28) : PcsQuotient.Domain.point i = UniStatement.point i := by
  rw [Bridge.Ntt.point_eq_sum]
  unfold UniStatement.point
  rw [Domain.foldl_ite_eq_sum, show UniStatement.basisSize = 28 + 4 from rfl, Finset.sum_range_add]
  have hz : ∑ x ∈ range 4, (if i.testBit (28 + x) then UniStatement.beta.getD (28 + x) 0 else 0) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Domain.beta_getD_eq_betaAt (Finset.mem_range.mp hk)]

theorem iterate_ofK (x : K) : ∀ l : ℕ,
    (fun y : E ↦ y * y + y)^[l] (ofK x) = ofK (PcsQuotient.Domain.S^[l] x)
  | 0 => rfl
  | l + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_ofK x l]
    show ofK _ * ofK _ + ofK _ = ofK (_ * _ + _)
    rw [Domain.embed_add, Domain.embed_mul]

theorem embed_prod {ι : Type*} (s : Finset ι) (f : ι → K) : ofK (∏ i ∈ s, f i) = ∏ i ∈ s, ofK (f i) :=
  map_prod (algebraMap K E) f s

theorem novX_ofK (m k : ℕ) (x : K) :
    novX m k (fun l ↦ (Domain.wP l).eval (ofK x)) = ofK (Bridge.Ntt.X m k x) := by
  rw [novX, Bridge.Ntt.X, embed_prod]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Domain.wP_eval, iterate_ofK]
  split_ifs
  · rfl
  · exact Domain.embed_one.symm

/-- **`colPolyK r v` interpolates `v` on `V_r`**: `pEval (pointE i) (colPolyK r v) = ofK v_i`, `i < 2^r`, `r ≤ 28`. -/
theorem pEval_colPolyK_pointE {r : ℕ} (hr : r ≤ 28) (v : Array K) (hv : v.size = 2 ^ r) {i : ℕ} (hi : i < 2 ^ r) :
    pEval (pointE i) (colPolyK r v) = ofK (v.getD i 0) := by
  have hi28 : i < 2 ^ 28 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hr)
  have hc : (PcsQuotient.Domain.coefficients r 0 v).size = 2 ^ r := by rw [Bridge.Ntt.coefficients_size, hv]
  rw [pEval_eq, colPolyK, ofNovel_toPoly, novP_eval, pointE, ← Ppoint_eq hi28]
  conv_rhs => rw [← Bridge.Ntt.values_coefficients_K r 0 v hv,
    Bridge.Ntt.values_getD_K (cantorUpTo hr) hr 0 _ hc hi, zero_add, Domain.embed_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [novelOfValuesK, getD_map_ofK, novX_ofK, Domain.embed_mul, mul_comm]

/-- **`colPolyE r v` interpolates `v` on `V_r`** (an `E`-column). -/
theorem pEval_colPolyE_pointE {r : ℕ} (hr : r ≤ 28) (v : Array E) (hv : v.size = 2 ^ r) {i : ℕ} (hi : i < 2 ^ r) :
    pEval (pointE i) (colPolyE r v) = v.getD i 0 := by
  have hi28 : i < 2 ^ 28 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hr)
  have hc : (PcsQuotient.Domain.coefficients r 0 v).size = 2 ^ r := by rw [Bridge.Ntt.coefficients_size, hv]
  rw [pEval_eq, colPolyE, ofNovel_toPoly, novP_eval, pointE, ← Ppoint_eq hi28]
  conv_rhs => rw [← Bridge.Ntt.values_coefficients_E r 0 v hv,
    Bridge.Ntt.values_getD_E (cantorUpTo hr) hr 0 _ hc hi, zero_add]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [novelOfValuesE, novX_ofK, mul_comm]

/-- `colPolyK r v` has degree `< 2^r`. -/
theorem colPolyK_natDegree_lt (r : ℕ) (v : Array K) : (colPolyK r v).toPoly.natDegree < 2 ^ r := by
  rw [colPolyK, ofNovel_toPoly]
  exact novP_natDegree_lt r _

/-- `ofNovel m d` has degree `< 2^m`. -/
theorem ofNovel_natDegree_lt (m : ℕ) (d : Array E) : (ofNovel m d).toPoly.natDegree < 2 ^ m := by
  rw [ofNovel_toPoly]
  exact novP_natDegree_lt m _

end UniComplete.AlgC

/-- info: 'UniComplete.AlgC.wPoly_toPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.wPoly_toPoly

/-- info: 'UniComplete.AlgC.ofNovel_toPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.ofNovel_toPoly

/-- info: 'UniComplete.AlgC.toNovel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.toNovel_spec

/-- info: 'UniComplete.AlgC.evalB_subsetSumsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.evalB_subsetSumsE

/-- info: 'UniComplete.AlgC.evalB_bCoefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.evalB_bCoefficients

/-- info: 'UniComplete.AlgC.pEval_colPolyK_pointE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.pEval_colPolyK_pointE

/-- info: 'UniComplete.AlgC.pEval_colPolyE_pointE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.pEval_colPolyE_pointE
