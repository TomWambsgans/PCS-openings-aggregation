-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The evaluators are `formal/UniStatement`'s
-- (`UniStatement/{Basic, Flock, Mapping, Security}.lean`, transcribed from `crates/leanvm_flock_gas`), the
-- mathematical objects `formal/FlockSound`'s.
import FlockSoundUni.TxBasic

/-!
# The transcription lemmas: the code's evaluators are the soundness proof's objects

Flock's verifier (`UniStatement.Flock`) computes with `List`s, `Array`s and folds; the soundness proof
(`FlockSound`) speaks of `interp`, `lag`, `eqP`, `mle`, `matMle`. Here, symbolically (nothing evaluates
`E` in the kernel, nor builds a large array):

* **the skip** (item 1): `phi` is `F_2`-linear (`phi_xor`), the nodes `φ(0), …, φ(2^n − 1)` (`n ≤ 7`) are
  an `F_2`-subspace (`phi_add_mem`), so every node's denominator is the window's
  (`windowDenominator_eq`); `lagrangeWeights` are the Lagrange basis at the point (`lagrangeWeights_skip`),
  `lagrangeInterpolate` of zeros and the coset values is `interp` (`lagrangeInterpolate_skip`);
* **the constants** (item 2): `phi` is `φ_8` (`phi_eq`), `fixedChallenges` is `fixedPt`
  (`fixedChallenges_eq`, `ptOf_fixed_append`);
* **the cube forms** (item 3): `eqKernel`, `multilinearEval`, `eqEval`, `knownWeights`; hence the pending
  reduction's claim is `rlc + known` (`pending_claim`) and its terminal the product of extensions
  (`pending_terminal`);
* **the matrices** (item 4): the stacks' extension is `matMle` (`mleArr_flockMatrixStack`), so
  `PendingHolds` is the product-sum claim (`pendingHolds_iff`).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters Finset Polynomial

/-! ## Folds -/

theorem tx_foldl_add {α : Type*} (l : List α) (g : α → E) (a : E) :
    l.foldl (fun acc p ↦ acc + g p) a = a + (l.map g).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

theorem tx_foldl_mul {α : Type*} (l : List α) (g : α → E) (a : E) :
    l.foldl (fun acc p ↦ acc * g p) a = a * (l.map g).prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, ih, List.map_cons, List.prod_cons]; ring

theorem tx_foldl_mul_range' (f : ℕ → E) : ∀ (m s : ℕ) (a : E),
    (List.range' s m).foldl (fun acc k ↦ acc * f k) a = a * ∏ k ∈ range m, f (s + k)
  | 0, s, a => by simp
  | m + 1, s, a => by
    rw [List.range'_succ, List.foldl_cons, tx_foldl_mul_range' f m (s + 1), Finset.prod_range_succ']
    simp only [add_zero]
    rw [Finset.prod_congr rfl fun k _ ↦ show f (s + 1 + k) = f (s + (k + 1)) by congr 1; omega]
    ring

/-! ## The constants (item 2) -/

theorem tx_ofLane_phiFold (v : ℕ) : ∀ n : ℕ,
    K.ofLane ((List.range n).foldl (fun acc bit ↦
      if v.testBit bit then acc ^^^ Flock.phiBasis.getD bit 0 else acc) 0) =
      ∑ b ∈ range n, if v.testBit b then K.ofLane (Flock.phiBasis.getD b 0) else 0
  | 0 => by simp [ofLane_zero]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ,
      ← tx_ofLane_phiFold v n]
    split_ifs <;> simp [ofLane_xor]

/-- **`phi` is `φ_8`**: the code's `UInt64` xor of the basis words is the sum in `K`. -/
theorem phi_eq (v : ℕ) : Flock.phi v = ofK (Lv42.Parameters.Flock.phi8 v) := by
  rw [Flock.phi, eK_eq, tx_ofLane_phiFold, Lv42.Parameters.Flock.phi8, ← Fin.sum_univ_eq_sum_range]
  refine congrArg ofK (Finset.sum_congr rfl fun i _ ↦ ?_)
  by_cases h : v.testBit i
  · simp only [h, ↓reduceIte]
    fin_cases i <;> rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem mediumGenerator_eq : Flock.mediumGenerator = Lv42.Parameters.Flock.g0 := rfl

/-- **`fixedChallenges` is the fixed point** `fixedPt` (leanVM's: `φ_8` of three bytes, then
`g0^(2^j) / (1 + g0^(2^j))`). -/
theorem fixedChallenges_eq : Flock.fixedChallenges = List.ofFn fixedPt := by
  simp only [List.ofFn_succ, List.ofFn_zero]
  simp [fixedPt, Lv42.Parameters.Flock.fixedPoint, Lv42.Parameters.Flock.fixedBytes,
    Flock.fixedChallenges, phi_eq, epow_eq, mediumGenerator_eq, Lv42.Parameters.Flock.mediumCoord,
    div_eq_mul_inv]

/-- The zerocheck's point: the fixed coordinates, then the sampled ones (`fullPoint`). -/
theorem ptOf_fixed_append (sampled : List E) {n' ns : ℕ} (h : n' = 7 + ns) :
    ptOf (Flock.fixedChallenges ++ sampled) n' = fullPoint h fixedPt (ptOf sampled ns) := by
  subst h
  have h7 : Flock.fixedChallenges.length = 7 := by rw [fixedChallenges_eq, List.length_ofFn]
  rw [ptOf_append _ _ h7]
  funext i
  simp only [fullPoint, Fin.cast_eq_self]
  congr 1
  funext j
  simp only [ptOf, fixedChallenges_eq, List.ofFn_succ, List.ofFn_zero]
  fin_cases j <;> rfl

/-! ## The skip's nodes and weights (item 1) -/

theorem tx_ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-- **`phi` is `F_2`-linear.** -/
theorem phi_xor (a b : ℕ) : Flock.phi (a ^^^ b) = Flock.phi a + Flock.phi b := by
  rw [phi_eq, phi_eq, phi_eq, phi8_xor, tx_ofK_add]

/-- **The nodes `φ(0), …, φ(2^n − 1)` are an `F_2`-subspace**: the sum of two is the node of the xor
of their indices, again below `2^n`. -/
theorem phi_add_mem {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a ^^^ b < 2 ^ n ∧ Flock.phi a + Flock.phi b = Flock.phi (a ^^^ b) :=
  ⟨Nat.xor_lt_two_pow ha hb, (phi_xor a b).symm⟩

/-- The nodes below `128` are distinct (`phi8_injOn`). -/
theorem phi_injOn {a b : ℕ} (ha : a < 128) (hb : b < 128) (h : Flock.phi a = Flock.phi b) : a = b := by
  rw [phi_eq, phi_eq] at h
  exact phi8_injOn ha hb (ofK_injective h)

theorem tx_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have h' : a ^^^ (a ^^^ b) = a ^^^ 0 := by rw [h]
  rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero, eq_comm] at h'

/-- Every node's denominator `Π_{j ≠ i} (φ_i − φ_j)` is the window's `Π_{t ≠ 0} φ_t`: `j ↦ i xor j`. -/
theorem tx_prod_window {n i : ℕ} (hi : i < 2 ^ n) :
    ∏ j ∈ (range (2 ^ n)).erase i, (Flock.phi i - Flock.phi j) =
      ∏ t ∈ range (2 ^ n - 1), Flock.phi (1 + t) := by
  have hne : ∀ j, j ≠ i → i ^^^ j ≠ 0 := fun j hj h ↦ hj (tx_xor_eq_zero h).symm
  refine Finset.prod_nbij' (fun j ↦ (i ^^^ j) - 1) (fun t ↦ i ^^^ (t + 1)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj ⊢
    have h1 := Nat.xor_lt_two_pow hi hj.2
    have h2 := hne j hj.1
    omega
  · intro t ht
    simp only [Finset.mem_erase, Finset.mem_range] at ht ⊢
    refine ⟨fun h ↦ ?_, Nat.xor_lt_two_pow hi (by omega)⟩
    have h' : i ^^^ (i ^^^ (t + 1)) = i ^^^ i := by rw [h]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h'
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have h2 := hne j hj.1
    show i ^^^ ((i ^^^ j) - 1 + 1) = j
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h2), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro t _
    show (i ^^^ (i ^^^ (t + 1))) - 1 = t
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.add_sub_cancel]
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have h2 := hne j hj.1
    rw [sub_eq_add_E, ← phi_xor, Nat.add_sub_cancel' (Nat.one_le_iff_ne_zero.mpr h2)]

/-- **The window denominator** is every node's denominator. -/
theorem windowDenominator_eq {n i : ℕ} (hi : i < 2 ^ n) :
    Flock.windowDenominator (2 ^ n) =
      (∏ j ∈ (range (2 ^ n)).erase i, (Flock.phi i - Flock.phi j))⁻¹ := by
  rw [tx_prod_window hi, Flock.windowDenominator, tx_foldl_mul_range', one_mul]

/-- Prefix products pushed one by one. -/
theorem tx_foldl_push (d : ℕ → E) : ∀ n : ℕ,
    (List.range n).foldl (fun acc i ↦ acc.push (acc.back?.getD 1 * d i)) #[1] =
      ((List.range (n + 1)).map fun t ↦ ∏ j ∈ range t, d j).toArray
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, tx_foldl_push d n, List.foldl_cons, List.foldl_nil,
      @List.range_succ (n + 1), List.map_append]
    simp [Finset.prod_range_succ, List.getLast?_range]

theorem lagrangeWeights_length (count : ℕ) (pt : E) :
    (Flock.lagrangeWeights count pt).length = count := by
  simp [Flock.lagrangeWeights]

theorem tx_lagrangeWeights_getD {count i : ℕ} (hi : i < count) (pt : E) :
    (Flock.lagrangeWeights count pt).getD i 0 =
      (∏ j ∈ range i, (pt + Flock.phi j)) *
        (∏ j ∈ range (count - 1 - i), (pt + Flock.phi (count - 1 - j))) * Flock.windowDenominator count := by
  simp only [Flock.lagrangeWeights]
  simp only [tx_foldl_push]
  simp [List.getD_eq_getElem?_getD, hi, Array.getD_eq_getD_getElem?]
  left
  rw [List.getElem?_range (by omega), Option.map_some, Option.getD_some]
  congr 1
  · refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    simp [Array.getElem?_ofFn, show x < count by omega]
  · rw [show count - (i + 1) = count - 1 - i by omega]
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    simp [Array.getElem?_ofFn, show count - 1 - x < count by omega]

/-- `Π_{j ∈ [0, N) \ {i}} f j` as the prefix before `i` and the suffix after. -/
theorem tx_prod_erase (f : ℕ → E) {N i : ℕ} (hi : i < N) :
    ∏ j ∈ (range N).erase i, f j = (∏ j ∈ range i, f j) * ∏ j ∈ range (N - 1 - i), f (i + 1 + j) := by
  have hmem : i ∈ range N := Finset.mem_range.mpr hi
  have h1 := Finset.mul_prod_erase (range N) (fun j ↦ if j = i then 1 else f j) hmem
  simp only [if_true, one_mul] at h1
  rw [Finset.prod_congr rfl fun j hj ↦ show f j = (if j = i then 1 else f j) by
    rw [if_neg (Finset.ne_of_mem_erase hj)], h1]
  rw [show N = i + 1 + (N - 1 - i) by omega, Finset.prod_range_add, Finset.prod_range_succ, if_pos rfl,
    mul_one, show i + 1 + (N - 1 - i) - 1 - i = N - 1 - i by omega]
  congr 1
  · exact Finset.prod_congr rfl fun j hj ↦ by rw [if_neg (by rw [Finset.mem_range] at hj; omega)]
  · exact Finset.prod_congr rfl fun j _ ↦ by rw [if_neg (by omega)]

/-- **The code's weight at node `i`** is the Lagrange basis polynomial's value:
`Π_{j ≠ i} (z − φ_j) / (φ_i − φ_j)` over the nodes `φ(0), …, φ(2^n − 1)`. -/
theorem lagrangeWeights_getD {n i : ℕ} (hi : i < 2 ^ n) (z : E) :
    (Flock.lagrangeWeights (2 ^ n) z).getD i 0 =
      ∏ j ∈ (range (2 ^ n)).erase i, (Flock.phi i - Flock.phi j)⁻¹ * (z - Flock.phi j) := by
  rw [tx_lagrangeWeights_getD hi, windowDenominator_eq hi, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, tx_prod_erase (fun j ↦ z - Flock.phi j) hi]
  have hB : ∏ j ∈ range (2 ^ n - 1 - i), (z + Flock.phi (2 ^ n - 1 - j)) =
      ∏ j ∈ range (2 ^ n - 1 - i), (z - Flock.phi (i + 1 + j)) := by
    rw [← Finset.prod_range_reflect (fun j ↦ z - Flock.phi (i + 1 + j))]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [sub_eq_add_E]
    congr 2
    omega
  rw [hB]
  simp only [sub_eq_add_E]
  ring

/-- **A Lagrange basis polynomial at `z`**, its nodes indexed through `e : ι ≃ Fin N` by numbers. -/
theorem tx_basis_eval {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} (e : ι ≃ Fin N) (w : ℕ → E)
    (p : ι) (z : E) :
    (Lagrange.basis univ (fun q ↦ w (e q)) p).eval z =
      ∏ j ∈ (range N).erase (e p), (w (e p) - w j)⁻¹ * (z - w j) := by
  rw [Lagrange.basis, Polynomial.eval_prod]
  refine Finset.prod_nbij' (fun q ↦ (e q : ℕ)) (fun j ↦ if h : j < N then e.symm ⟨j, h⟩ else p)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_range] at hq ⊢
    exact ⟨fun h ↦ hq (e.injective (Fin.ext h)), (e q).isLt⟩
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_univ, and_true] at hj ⊢
    rw [dif_pos hj.2]
    intro h
    apply hj.1
    rw [← h, Equiv.apply_symm_apply]
  · intro q _
    simp only [dif_pos (e q).isLt, Fin.eta, Equiv.symm_apply_apply]
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    simp only [dif_pos hj.2, Equiv.apply_symm_apply]
  · intro q _
    simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]

/-- The Lagrange basis over nodes `φ ∘ e` is the code's weight. -/
theorem tx_lag_eval_code {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin (2 ^ n)) (p : ι)
    (z : E) :
    (Lagrange.basis univ (fun q ↦ Flock.phi (e q)) p).eval z =
      (Flock.lagrangeWeights (2 ^ n) z).getD (e p) 0 := by
  rw [tx_basis_eval e Flock.phi, lagrangeWeights_getD (e p).isLt]

/-- **The skip's weights**: `lagrangeWeights (2^k) z` at a cube point's number is `lag` at `z`. -/
theorem lagrangeWeights_skip (k : ℕ) (hk : k ≤ 6) (z : E) (b : Cube k) :
    (Flock.lagrangeWeights (2 ^ k) z).getD (cubeFin k b) 0 = (lag (skipNodes k hk) b).eval z := by
  have hv : (fun j ↦ skipNodes k hk (false, j)) = fun q ↦ Flock.phi (cubeFin k q) := by
    funext q
    simp [skipNodes, Lv42.Parameters.Flock.skipNode, phi_eq]
  rw [lag, hv, tx_lag_eval_code]

/-- The skip's domain and coset as numbers: `(b, i) ↦ b·2^k + i`. -/
noncomputable def tx_skipIdx (k : ℕ) : Bool × Cube k ≃ Fin (2 ^ (k + 1)) :=
  Equiv.ofBijective (fun p ↦ ⟨(if p.1 then 2 ^ k else 0) + (cubeFin k p.2 : ℕ), by
    have h := (cubeFin k p.2).isLt
    rw [pow_succ]
    split <;> omega⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [Fintype.card_prod, Fintype.card_fun, pow_succ, mul_comm]⟩
    rintro ⟨b, i⟩ ⟨b', i'⟩ h
    simp only [Fin.mk.injEq] at h
    have hi := (cubeFin k i).isLt
    have hi' := (cubeFin k i').isLt
    have hb : b = b' := by
      cases b <;> cases b' <;> first | rfl | (simp at h; omega)
    subst hb
    have : (cubeFin k i : ℕ) = cubeFin k i' := by split at h <;> omega
    exact Prod.ext rfl ((cubeFin k).injective (Fin.ext this)))

theorem tx_skipIdx_val (k : ℕ) (p : Bool × Cube k) :
    (tx_skipIdx k p : ℕ) = (if p.1 then 2 ^ k else 0) + (cubeFin k p.2 : ℕ) := rfl

theorem tx_skipNodes_eq (k : ℕ) (hk : k ≤ 6) :
    skipNodes k hk = fun q ↦ Flock.phi (tx_skipIdx k q) := by
  funext q
  simp [skipNodes, Lv42.Parameters.Flock.skipNode, phi_eq, tx_skipIdx_val]

/-- `dot` is the sum of the products, the second list read by `getD`. -/
theorem tx_dot_foldl : ∀ (w v : List E) (a : E),
    (w.zip v).foldl (fun acc (x, y) ↦ acc + x * y) a =
      a + ∑ i ∈ range w.length, w.getD i 0 * v.getD i 0
  | [], _, a => by simp
  | x :: w, [], a => by simp
  | x :: w, y :: v, a => by
    rw [List.zip_cons_cons, List.foldl_cons, tx_dot_foldl w v, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem tx_dot_eq (w v : List E) : dot w v = ∑ i ∈ range w.length, w.getD i 0 * v.getD i 0 := by
  rw [dot, tx_dot_foldl, zero_add]

/-- **The zerocheck's starting claim**: `lagrangeInterpolate` of `2^k` zeros and the coset values is
the interpolant `interp` at `z`. -/
theorem lagrangeInterpolate_skip (k : ℕ) (hk : k ≤ 6) (coset : List E) (z : E) :
    Flock.lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ coset) z =
      (interp (skipNodes k hk) (fun b ↦ coset.getD (cubeFin k b) 0)).eval z := by
  rw [interp, Lagrange.interpolate_apply, Polynomial.eval_finsetSum, tx_skipNodes_eq k hk]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, tx_lag_eval_code (tx_skipIdx k)]
  rw [Flock.lagrangeInterpolate, tx_dot_eq, lagrangeWeights_length, ← Fin.sum_univ_eq_sum_range,
    ← (tx_skipIdx k).sum_comp]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [mul_comm]
  congr 1
  rw [tx_skipIdx_val]
  have h := (cubeFin k p.2).isLt
  rcases p with ⟨_ | _, i⟩
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · simp only [↓reduceIte]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

end FlockSound.Uni
