-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The evaluators are `formal/UniStatement`'s
-- (`UniStatement/{Basic, Flock, Mapping, Security}.lean`, transcribed from `crates/leanvm_flock_gas`), the
-- mathematical objects `formal/FlockSound`'s.
import FlockSoundUni.Tower

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
  `PendingHolds`' sum is the product sum (`pending_sum`, `pendingHolds_iff`);
* **the main line** (`k = l = 3`, points as `List.ofFn`): `tx_fixedChallenges_getD`, `tx_interp`,
  `tx_claim`, `tx_sum`, the forms `Catch.lean` consumes;
* **the ring switch** (items 5 and 6, `Tower.lean`): `towerCoefficients` gives the ring claim's value
  (`ringClaim_code`) and `towerTarget` the target `Σ_i x^i Φ_tower(s_i)` (`towerTarget_eq_target`);
* **`FlockTx`**, all of them at the main line, in the form `lean-flock-link`'s `Tx` takes; **`flockTx`**.

The skip's lemmas hold for any `k ≤ 6`, the pending reduction's for any `k + l = 6` (`k = 0` included:
its one Lagrange weight is `1`, `tx_lag_zero`).
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

/-! ## The cube forms (item 3) -/

theorem tx_array_getD (a : Array E) (i : ℕ) (d : E) : a.getD i d = a.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem tx_cubeEq_snoc (ps : List E) (r : E) (x : ℕ) :
    cubeEq (ps ++ [r]) (ps.length + 1) x =
      cubeEq ps ps.length x * (1 + r + if x.testBit ps.length then 1 else 0) := by
  rw [cubeEq, cubeEq, Finset.prod_range_succ, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
    List.getD_cons_zero]
  rw [Finset.prod_congr rfl fun k hk ↦ by rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hk)]]

theorem tx_cubeEq_two_pow_add (ps : List E) (n x : ℕ) :
    cubeEq ps n (2 ^ n + x) = cubeEq ps n x := by
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [Nat.testBit_two_pow_add_gt hk]

/-- **`eqKernel`** lists `eq(p, x)` (`cubeEq`) at every number `x < 2^len`. -/
theorem eqKernel_toList (p : List E) :
    (eqKernel p).toList = (List.range (2 ^ p.length)).map (cubeEq p p.length) := by
  induction p using List.reverseRecOn with
  | nil => simp [eqKernel, cubeEq]
  | append_singleton ps r ih =>
    rw [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil, ← eqKernel, Array.toList_append,
      Array.toList_map, Array.toList_map, ih, List.length_append, List.length_singleton, pow_succ,
      mul_two, List.range_add, List.map_append, List.map_map, List.map_map, List.map_map]
    congr 1
    · refine List.map_congr_left fun x hx ↦ ?_
      rw [List.mem_range] at hx
      simp [tx_cubeEq_snoc, Nat.testBit_lt_two_pow hx]
    · refine List.map_congr_left fun x hx ↦ ?_
      rw [List.mem_range] at hx
      simp only [Function.comp, tx_cubeEq_snoc, tx_cubeEq_two_pow_add, Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hx, Bool.not_false, ↓reduceIte]
      linear_combination (-cubeEq ps ps.length x) * two_eq_zero_E

theorem eqKernel_size (p : List E) : (eqKernel p).size = 2 ^ p.length := by
  rw [← Array.length_toList, eqKernel_toList, List.length_map, List.length_range]

/-- **`eqKernel`**'s entry `i` is `eq(p, i)`. -/
theorem eqKernel_getD (p : List E) {i : ℕ} (hi : i < 2 ^ p.length) :
    (eqKernel p).getD i 0 = cubeEq p p.length i := by
  rw [tx_array_getD, eqKernel_toList, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  rfl

/-- **`eqKernel`** at a cube point's number is `eqP`. -/
theorem eqKernel_cube (p : List E) {n : ℕ} (hp : p.length = n) (b : Cube n) :
    (eqKernel p).getD (cubeFin n b) 0 = eqP (ptOf p n) b := by
  subst hp
  rw [eqKernel_getD p (cubeFin _ b).isLt, cubeEq_cubeFin]

theorem tx_foldOnce_size (cur : Array E) (r : E) : (foldOnce cur r).size = cur.size / 2 := by
  simp [foldOnce]

theorem tx_foldOnce_getD (cur : Array E) (r : E) {i : ℕ} (hi : i < cur.size / 2) :
    (foldOnce cur r).getD i 0 =
      cur.getD (2 * i) 0 + r * (cur.getD (2 * i) 0 + cur.getD (2 * i + 1) 0) := by
  simp [foldOnce, Array.getD, hi]

theorem tx_sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ m : ℕ,
    ∑ i ∈ range (2 * m), f i = ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1))
  | 0 => by simp
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      tx_sum_range_two_mul f m, Finset.sum_range_succ, add_assoc]

theorem tx_cubeEq_cons (r : E) (ps : List E) (n i : ℕ) :
    cubeEq (r :: ps) (n + 1) i = cubeEq ps n (i / 2) * (1 + r + if i.testBit 0 then 1 else 0) := by
  rw [cubeEq, cubeEq, Finset.prod_range_succ']
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [List.getD_cons_succ, Nat.testBit_add_one]

theorem tx_fold_mle : ∀ (p : List E) (A : Array E), A.size = 2 ^ p.length →
    (p.foldl foldOnce A).getD 0 0 = ∑ i ∈ range (2 ^ p.length), A.getD i 0 * cubeEq p p.length i
  | [], A, h => by simp [cubeEq]
  | r :: ps, A, h => by
    have h' : A.size = 2 * 2 ^ ps.length := by rw [h, List.length_cons, pow_succ, mul_comm]
    rw [List.foldl_cons, tx_fold_mle ps (foldOnce A r) (by rw [tx_foldOnce_size, h']; omega),
      List.length_cons, pow_succ, mul_comm, tx_sum_range_two_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [tx_foldOnce_getD _ _ (by rw [h']; omega), tx_cubeEq_cons, tx_cubeEq_cons]
    have e0 : (2 * i).testBit 0 = false := by simp [Nat.testBit_zero]
    have e1 : (2 * i + 1).testBit 0 = true := by simp [Nat.testBit_zero]
    rw [e0, e1, show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    linear_combination (-(A.getD (2 * i + 1) 0 * cubeEq ps ps.length i)) * two_eq_zero_E

/-- **`multilinearEval`** is the multilinear extension `mle` (low coordinate first). -/
theorem multilinearEval_eq (t p : List E) {n : ℕ} (hp : p.length = n) (ht : t.length = 2 ^ n) :
    multilinearEval t p = mle (fun b : Cube n ↦ t.getD (cubeFin n b) 0) (ptOf p n) := by
  subst hp
  rw [multilinearEval, tx_fold_mle p t.toArray (by simpa using ht), sum_range_eq_sum_cube, mle]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [cubeEq_cubeFin, tx_array_getD]

theorem tx_eqEval_foldl : ∀ (x y : List E) (a : E), x.length = y.length →
    (x.zip y).foldl (fun acc (u, v) ↦ acc * (1 + u + v)) a =
      a * ∏ i ∈ range x.length, (1 + x.getD i 0 + y.getD i 0)
  | [], [], a, _ => by simp
  | u :: x, v :: y, a, h => by
    rw [List.zip_cons_cons, List.foldl_cons, tx_eqEval_foldl x y _ (by simpa using h),
      List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- **`eqEval`** is `FlockSound.eqEval` (`Π (x y + (1 − x)(1 − y))`, characteristic two). -/
theorem eqEval_eq (x y : List E) {n : ℕ} (hx : x.length = n) (hy : y.length = n) :
    UniStatement.eqEval x y = FlockSound.eqEval (ptOf x n) (ptOf y n) := by
  rw [UniStatement.eqEval, tx_eqEval_foldl x y 1 (hx.trans hy.symm), one_mul, FlockSound.eqEval, hx,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [ptOf]
  linear_combination (x.getD i 0 + y.getD i 0 - x.getD i 0 * y.getD i 0) * two_eq_zero_E

/-- The constant position (`512`): packing index `0`, slot `8`. -/
theorem tx_cpos {k l : ℕ} (hkl : k + l = 6) :
    (posFin hkl).symm Lv42.Parameters.Flock.constPos =
      ((cube64 hkl).symm ⟨0, by norm_num⟩, (cubeFin 8).symm ⟨8, by norm_num⟩) := by
  rw [Equiv.symm_apply_eq]
  simp only [posFin, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.apply_symm_apply,
    LeanVM.Protocol.cubeSplit_apply]
  rfl

theorem tx_cpos_fst {k l : ℕ} (hkl : k + l = 6) :
    ((cubeFin (k + l) ((posFin hkl).symm Lv42.Parameters.Flock.constPos).1 : Fin _) : ℕ) = 0 := by
  rw [tx_cpos, ← cube64_val hkl, Equiv.apply_symm_apply]

theorem tx_cpos_snd {k l : ℕ} (hkl : k + l = 6) (j : Fin 8) :
    ((posFin hkl).symm Lv42.Parameters.Flock.constPos).2 j = (8 : ℕ).testBit j := by
  rw [tx_cpos]
  exact cubeFin_symm_apply _ _

/-- **`knownWeights`**: `α² eq(chi_in, chi_in')` and `α³ eq(chi_in', cpos.2)`. -/
theorem knownWeights_eq {k l : ℕ} (hkl : k + l = 6) (α : E) (chiIn chiInPrime : List E)
    (h8 : chiIn.length = 8) (h8' : chiInPrime.length = 8) :
    Flock.knownWeights α chiIn chiInPrime =
      (α ^ 2 * FlockSound.eqEval (ptOf chiIn 8) (ptOf chiInPrime 8),
        α ^ 3 * eqP (ptOf chiInPrime 8) ((posFin hkl).symm Lv42.Parameters.Flock.constPos).2) := by
  have hc : ((List.range Flock.lincheckRounds).map
      (bitE (Flock.constantColumn / Flock.kBits))).length = 8 := by
    simp [Flock.lincheckRounds, blake2sR1csLogSize]
  simp only [Flock.knownWeights, epow_eq]
  rw [eqEval_eq _ _ h8 h8', eqEval_eq _ _ hc h8']
  refine Prod.ext rfl (congrArg (α ^ 3 * ·) ?_)
  rw [FlockSound.eqEval, eqP]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [tx_cpos_snd]
  have hj := j.isLt
  have hget : ptOf ((List.range Flock.lincheckRounds).map
      (bitE (Flock.constantColumn / Flock.kBits))) 8 j = if (8 : ℕ).testBit j then 1 else 0 := by
    simp [ptOf, List.getD_eq_getElem?_getD, Flock.lincheckRounds, blake2sR1csLogSize, hj, bitE,
      Flock.constantColumn, Flock.kBits]
  rw [hget]
  cases (8 : ℕ).testBit j <;> simp

theorem tx_flatMap_getD (S : List E) {A : ℕ} (hS : S.length = A) : ∀ (M : List E) {a b : ℕ}, a < A →
    b < M.length → (M.flatMap fun m ↦ S.map fun x ↦ x * m).getD (a + A * b) 0 = S.getD a 0 * M.getD b 0
  | [], _, _, _, hb => by simp at hb
  | m :: M, a, 0, ha, _ => by
    rw [List.flatMap_cons, mul_zero, add_zero, List.getD_append _ _ _ _ (by simpa [hS] using ha)]
    simp [List.getD_eq_getElem?_getD, hS, ha]
  | m :: M, a, b + 1, ha, hb => by
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by simp [hS]; nlinarith)]
    simp only [List.length_map, hS, List.getD_cons_succ]
    rw [show a + A * (b + 1) - A = a + A * b by rw [Nat.mul_succ]; omega]
    exact tx_flatMap_getD S hS M ha (by simpa using hb)

theorem tx_length_flatMap (S M : List E) :
    (M.flatMap fun m ↦ S.map fun x ↦ x * m).length = S.length * M.length := by
  induction M with
  | nil => simp
  | cons m M ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]
    ring

/-- A cube point of `k + l` coordinates as a number: its low `k` and high `l` blocks. -/
theorem tx_cubeFin_split {k l : ℕ} (cy : Cube (k + l)) :
    ((cubeFin (k + l) cy : Fin _) : ℕ) = cubeFin k (lowPart cy) + 2 ^ k * cubeFin l (highPart cy) := by
  conv_lhs => rw [← append_lowPart_highPart cy]
  exact cubeFin_append_val _ _

/-- **The pending reduction's claim** is the lincheck's terminal plus the two known terms, as the
soundness proof has them (`Front.matClaim`'s `rlc + known`, at `C = setupOf …`). -/
theorem pending_claim {k l : ℕ} (hkl : k + l = 6) (hk : k ≤ 6) (z α rLc : E)
    (rowLow chiIn chiInPrime s : List E) (hl : rowLow.length = l) (h8 : chiIn.length = 8)
    (h8' : chiInPrime.length = 8) :
    (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some s)).claim =
      rLc + (α ^ 2 * FlockSound.eqEval (ptOf chiIn 8) (ptOf chiInPrime 8) *
          ∑ cy, lowW (skipNodes k hk) z (ptOf rowLow l) cy * sliceOf s cy +
        α ^ 3 * eqP (ptOf chiInPrime 8) ((posFin hkl).symm Lv42.Parameters.Flock.constPos).2 *
          sliceOf s ((posFin hkl).symm Lv42.Parameters.Flock.constPos).1) := by
  have hpk : Flock.packing - rowLow.length = k := by simp only [Flock.packing, hl]; omega
  simp only [Flock.Pending.new, Flock.rowLowWeights, knownWeights_eq hkl α chiIn chiInPrime h8 h8',
    Option.map_some, Option.getD_some, hpk]
  have hS : (Flock.lagrangeWeights (2 ^ k) z).length = 2 ^ k := lagrangeWeights_length _ _
  have hM : (eqKernel rowLow).toList.length = 2 ^ l := by
    rw [Array.length_toList, eqKernel_size, hl]
  have hdot : dot (List.flatMap (fun m ↦ List.map (fun l ↦ l * m) (Flock.lagrangeWeights (2 ^ k) z))
      (eqKernel rowLow).toList) s = ∑ cy, lowW (skipNodes k hk) z (ptOf rowLow l) cy * sliceOf s cy := by
    rw [tx_dot_eq, tx_length_flatMap, hS, hM, ← pow_add, sum_range_eq_sum_cube]
    refine Finset.sum_congr rfl fun cy _ ↦ ?_
    rw [tx_cubeFin_split, tx_flatMap_getD _ hS _ (cubeFin k (lowPart cy)).isLt
      (by rw [hM]; exact (cubeFin l (highPart cy)).isLt), lagrangeWeights_skip k hk, ← tx_array_getD,
      eqKernel_cube rowLow hl, ← tx_cubeFin_split]
    unfold lowW sliceOf
    rfl
  have hpin : s.getD (Flock.constantColumn % Flock.kBits) 0 =
      sliceOf s ((posFin hkl).symm Lv42.Parameters.Flock.constPos).1 := by
    rw [sliceOf, tx_cpos_fst]
    norm_num [Flock.constantColumn, Flock.kBits]
  rw [hdot, hpin]

/-- **The pending reduction's fields**: `k` skipped row bits, `k + 6` rounds, the points and `α` as given,
the skip's weights `lagrangeWeights (2^k) z`. -/
theorem pending_fields {k l : ℕ} (hkl : k + l = 6) (z α rLc : E) (rowLow chiIn chiInPrime : List E)
    (sl : Option (List E)) (hl : rowLow.length = l) :
    (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc sl).k = k ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc sl).rounds = k + 6 ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc sl).rowLow = rowLow ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc sl).chiIn = chiIn ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc sl).chiInPrime = chiInPrime ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc sl).alpha = α ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc sl).skipWeights =
        Flock.lagrangeWeights (2 ^ k) z ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc sl).slices = sl := by
  have hpk : 6 - rowLow.length = k := by rw [hl]; omega
  simp only [Flock.Pending.new, Flock.rowLowWeights, Flock.Pending.rounds, Flock.packing, hpk,
    and_self]

/-- Without a skip (`k = 0`), the one Lagrange weight is `1`. -/
theorem tx_lag_zero (hk : 0 ≤ 6) (b : Cube 0) (z : E) : (lag (skipNodes 0 hk) b).eval z = 1 := by
  have h0 : ((cubeFin 0 b : Fin (2 ^ 0)) : ℕ) = 0 := by simpa using (cubeFin 0 b).isLt
  rw [← lagrangeWeights_skip 0 hk, lagrangeWeights_getD (cubeFin 0 b).isLt, h0]
  simp

/-- The skip's weights' extension at a point of `k` coordinates (`1` without a skip). -/
theorem tx_skipAt {k : ℕ} (hk : k ≤ 6) (z : E) (rho : List E) (hrho : rho.length = k) :
    (if k > 0 then multilinearEval (Flock.lagrangeWeights (2 ^ k) z) rho else 1) =
      mle (fun bx ↦ (lag (skipNodes k hk) bx).eval z) (ptOf rho k) := by
  split_ifs with hk0
  · rw [multilinearEval_eq _ _ hrho (lagrangeWeights_length _ _)]
    simp only [lagrangeWeights_skip k hk]
  · obtain rfl : k = 0 := by omega
    rw [mle, Fintype.sum_unique, eqP, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      tx_lag_zero hk]

/-- **The pending reduction's terminal** at the batch's point: `(a + α b) L̂(ρ) ŝ(σ)`, `ρ` the point's first
`k` coordinates and `σ` the next six. -/
theorem pending_terminal {k l : ℕ} (hkl : k + l = 6) (hk : k ≤ 6) (z α rLc a b : E)
    (rowLow chiIn chiInPrime s point : List E) (hl : rowLow.length = l) (hs : s.length = 64)
    (hpt : k + 6 ≤ point.length) :
    ((Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some s)).terminal point a b).1 =
      (a + α * b) * mle (fun bx ↦ (lag (skipNodes k hk) bx).eval z) (ptOf (point.take k) k) *
        mle (sliceOf s) (ptOf ((point.take (k + 6)).drop k) (k + l)) := by
  obtain ⟨h1, h2, -, -, -, h6, h7, h8⟩ :=
    pending_fields hkl z α rLc rowLow chiIn chiInPrime (some s) hl
  have hσ : ((point.take (k + 6)).drop k).length = k + l := by simp; omega
  have hρ : (point.take k).length = k := by simp; omega
  simp only [Flock.Pending.terminal, Flock.Pending.skipAt, h1, h2, h6, h7, h8, Option.getD_some,
    List.take_take, min_eq_left (show k ≤ k + 6 by omega)]
  rw [tx_skipAt hk z _ hρ, multilinearEval_eq s _ hσ (by rw [hs, hkl]; rfl)]
  rfl

/-! ## The matrices (item 4) -/

/-- `mleArr` as the cube's `mle`. -/
theorem tx_mleArr_eq (a : Array K) (n : ℕ) (p : List E) :
    mleArr a n p = mle (fun c : Cube n ↦ ofK (a.getD (cubeFin n c) 0)) (ptOf p n) := by
  rw [mleArr, Fin.sum_univ_eq_sum_range (fun x ↦ cubeEq p n x * ofK (a.getD x 0)),
    sum_range_eq_sum_cube, mle]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [cubeEq_cubeFin, mul_comm]

theorem tx_mle_append2 {a b : ℕ} (t : Cube (a + b) → E) (X : Fin a → E) (Y : Fin b → E) :
    mle t (Fin.append X Y) =
      ∑ bx : Cube a, ∑ by' : Cube b, t (Fin.append bx by') * (eqP X bx * eqP Y by') := by
  rw [mle, sum_cube_append]
  simp only [eqP_append]

theorem tx_mle_append5 {a b c d e : ℕ} (t : Cube (a + b + c + d + e) → E) (X1 : Fin a → E)
    (X2 : Fin b → E) (X3 : Fin c → E) (X4 : Fin d → E) (X5 : Fin e → E) :
    mle t (Fin.append (Fin.append (Fin.append (Fin.append X1 X2) X3) X4) X5) =
      ∑ b1 : Cube a, ∑ b2 : Cube b, ∑ b3 : Cube c, ∑ b4 : Cube d, ∑ b5 : Cube e,
        t (Fin.append (Fin.append (Fin.append (Fin.append b1 b2) b3) b4) b5) *
          (eqP X1 b1 * eqP X2 b2 * eqP X3 b3 * eqP X4 b4 * eqP X5 b5) := by
  rw [mle]
  simp only [sum_cube_append, eqP_append]

/-- An entry of a matrix stack: word `r + 2^14 c` is `M r c`. -/
theorem tx_matrixStack_getD (M : Fin (2 ^ 14) → Fin (2 ^ 14) → Bool) (r c : Fin (2 ^ 14)) {w : ℕ}
    (hw : w = (r : ℕ) + 2 ^ 14 * (c : ℕ)) : ofK ((matrixStack M).getD w 0) = bit (M r c) := by
  subst hw
  have hr := r.isLt
  have hc := c.isLt
  have hlt : (r : ℕ) + 2 ^ 14 * c < 2 ^ 28 := by
    have h28 : (2 : ℕ) ^ 28 = 2 ^ 14 * 2 ^ 14 := by norm_num
    rw [h28]
    nlinarith
  have e1 : ((r : ℕ) + 2 ^ 14 * c) % 2 ^ 14 = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have e2 : ((r : ℕ) + 2 ^ 14 * c) / 2 ^ 14 % 2 ^ 14 = c := by
    rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hr, zero_add, Nat.mod_eq_of_lt hc]
  rw [matrixStack, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hlt, Option.getD_some]
  have key : ∀ (i j : Fin (2 ^ 14)), (i : ℕ) = r → (j : ℕ) = c → M i j = M r c := by
    intro i j hi hj
    rw [Fin.ext hi, Fin.ext hj]
  rw [key _ _ e1 e2]
  cases M r c <;> simp [bit]

theorem tx_posFin_val {k l : ℕ} (hkl : k + l = 6) (cy : Cube (k + l)) (ch : Cube 8) :
    ((posFin hkl (cy, ch) : Fin _) : ℕ) = cubeFin (k + l) cy + 2 ^ 6 * cubeFin 8 ch := by
  simp only [posFin, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    LeanVM.Protocol.cubeSplit_apply, LeanVM.Protocol.cubeIndex]
  rfl

/-- **A matrix stack's extension** at `(x, r_l, r_h, y, χ')` is `matMle`: the row's coordinates
`(x, r_l, r_h)`, the column's `(y, χ')`, word `row + 2^14 col`. -/
theorem mleArr_matrixStack (M : Fin (2 ^ 14) → Fin (2 ^ 14) → Bool) {k l : ℕ} (hkl : k + l = 6)
    (x rl rh y χ' : List E) (hx : x.length = k) (hrl : rl.length = l) (hrh : rh.length = 8)
    (hy : y.length = k + l) :
    mleArr (matrixStack M) matrixVars (x ++ rl ++ rh ++ y ++ χ') =
      matMle (ptOf rl l) (ptOf rh 8) (ptOf χ' 8) (cubeMat hkl M) (ptOf x k) (ptOf y (k + l)) := by
  have hN : matrixVars = k + l + 8 + (k + l) + 8 := by
    simp only [matrixVars, blake2sR1csLogSize]
    omega
  rw [hN, tx_mleArr_eq, ptOf_append _ _ (by simp only [List.length_append, hx, hrl, hrh, hy]),
    ptOf_append _ _ (by simp only [List.length_append, hx, hrl, hrh]),
    ptOf_append _ _ (by simp only [List.length_append, hx, hrl]), ptOf_append _ _ hx,
    tx_mle_append5, matMle, tx_mle_append2]
  refine Finset.sum_congr rfl fun bx _ ↦ ?_
  simp only [matTab, lowPart_append, highPart_append, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun bl _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun bh _ ↦ Finset.sum_congr rfl fun by' _ ↦
    Finset.sum_congr rfl fun ch _ ↦ ?_
  have hw : ((cubeFin (k + l + 8 + (k + l) + 8)
      (Fin.append (Fin.append (Fin.append (Fin.append bx bl) bh) by') ch) : Fin _) : ℕ) =
      (posFin hkl (Fin.append bx bl, bh) : ℕ) + 2 ^ 14 * (posFin hkl (by', ch) : ℕ) := by
    rw [cubeFin_append_val, cubeFin_append_val, cubeFin_append_val, cubeFin_append_val, tx_posFin_val,
      tx_posFin_val, cubeFin_append_val]
    generalize ((cubeFin k bx : Fin _) : ℕ) = A
    generalize ((cubeFin l bl : Fin _) : ℕ) = B
    generalize ((cubeFin 8 bh : Fin _) : ℕ) = C
    generalize ((cubeFin (k + l) by' : Fin _) : ℕ) = D
    generalize ((cubeFin 8 ch : Fin _) : ℕ) = F
    rw [hkl]
    ring
  rw [tx_matrixStack_getD M _ _ hw, cubeMat]
  ring

/-- **The stacks of `A0` and `B0`** (`flockMatrixStack`): their extension at `(x, r_l, r_h, y, χ')` is
`matMle` of the BLAKE2s R1CS's matrix on the cube. -/
theorem mleArr_flockMatrixStack (left : Bool) {k l : ℕ} (hkl : k + l = 6) (x rl rh y χ' : List E)
    (hx : x.length = k) (hrl : rl.length = l) (hrh : rh.length = 8) (hy : y.length = k + l) :
    mleArr (flockMatrixStack left) matrixVars (x ++ rl ++ rh ++ y ++ χ') =
      matMle (ptOf rl l) (ptOf rh 8) (ptOf χ' 8)
        (cubeMat hkl (if left then Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A
          else Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B)) (ptOf x k) (ptOf y (k + l)) := by
  simp only [flockMatrixStack]
  rw [mleArr_matrixStack _ hkl x rl rh y χ' hx hrl hrh hy]
  cases left <;> rfl

theorem tx_ptOf_bitsE {n : ℕ} (b : Cube n) : ptOf (bitsE (cubeFin n b) n) n = cube b := by
  funext i
  simp only [ptOf, bitsE, cube, bit]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt, Option.map_some,
    Option.getD_some, testBit_cubeFin]

theorem tx_bitsE_length (u n : ℕ) : (bitsE u n).length = n := by simp [bitsE]

theorem tx_matMle_cube {k l m : ℕ} (rl : Fin l → E) (rh χ' : Fin m → E)
    (M' : Pos k l m → Pos k l m → Bool) (b : Cube (k + (k + l))) :
    matMle rl rh χ' M' (cube (lowPart b)) (cube (highPart b)) = matTab rl rh χ' M' b := by
  rw [matMle, ← cube_append, append_lowPart_highPart, mle_cube]

/-- **The pending reduction's sum** (`PendingHolds`' right side) is the product sum
`Σ_cy matPart(cy) ŝ(cy)` of the soundness proof. -/
theorem pending_sum {k l : ℕ} (hkl : k + l = 6) (hk : k ≤ 6) (z α rLc : E)
    (rowLow chiIn chiInPrime s : List E) (hl : rowLow.length = l) (h8 : chiIn.length = 8) :
    ∑ u ∈ range (2 ^ (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some s)).rounds),
        Pending.G (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some s)) u *
          Pending.L (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some s)) u =
      ∑ cy, matPart (cubeMat hkl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A)
        (cubeMat hkl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B) (skipNodes k hk) z
        (ptOf rowLow l) (ptOf chiIn 8) (ptOf chiInPrime 8) α cy * sliceOf s cy := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8'⟩ :=
    pending_fields hkl z α rLc rowLow chiIn chiInPrime (some s) hl
  rw [← cubeSum_matFun]
  simp only [cubeSum, eqW_none, one_mul, matFun, mle_cube]
  rw [h2, show k + 6 = k + (k + l) by omega, sum_range_eq_sum_cube]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hu := tx_cubeFin_split b
  have hmod : (cubeFin (k + (k + l)) b : ℕ) % 2 ^ k = cubeFin k (lowPart b) := by
    rw [hu, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (cubeFin k _).isLt]
  have hdiv : (cubeFin (k + (k + l)) b : ℕ) / 2 ^ k = cubeFin (k + l) (highPart b) := by
    rw [hu, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (cubeFin k _).isLt, zero_add]
  have hL : (if k > 0 then (Flock.lagrangeWeights (2 ^ k) z).getD (cubeFin k (lowPart b)) 0 else 1) =
      (lag (skipNodes k hk) (lowPart b)).eval z := by
    split_ifs with hk0
    · exact lagrangeWeights_skip k hk z _
    · obtain rfl : k = 0 := by omega
      rw [tx_lag_zero hk]
  have hp : Flock.packing = k + l := by simp [Flock.packing, hkl]
  simp only [Pending.G, Pending.L, h1, h3, h4, h5, h6, h7, h8', hmod, hdiv, Option.getD_some, hp, hL]
  rw [mleArr_flockMatrixStack true hkl _ _ _ _ _ (tx_bitsE_length _ _) hl h8 (tx_bitsE_length _ _),
    mleArr_flockMatrixStack false hkl _ _ _ _ _ (tx_bitsE_length _ _) hl h8 (tx_bitsE_length _ _),
    tx_ptOf_bitsE, tx_ptOf_bitsE]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [tx_matMle_cube, tx_matMle_cube, lsTab, gTab]
  unfold sliceOf
  ring

/-- **`PendingHolds` is the product-sum claim** of the soundness proof (`flock_front`'s
`matClaim = Σ_cy matPart(cy) ŝ(cy)`, with `pending_claim` for its left side). -/
theorem pendingHolds_iff {k l : ℕ} (hkl : k + l = 6) (hk : k ≤ 6) (z α rLc : E)
    (rowLow chiIn chiInPrime s : List E) (hl : rowLow.length = l) (h8 : chiIn.length = 8) :
    PendingHolds (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some s)) ↔
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some s)).claim =
        ∑ cy, matPart (cubeMat hkl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A)
          (cubeMat hkl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B) (skipNodes k hk) z
          (ptOf rowLow l) (ptOf chiIn 8) (ptOf chiInPrime 8) α cy * sliceOf s cy := by
  rw [PendingHolds, pending_sum hkl hk z α rLc rowLow chiIn chiInPrime s hl h8]

/-! ## The main line's forms (`k = l = 3`, the points as `List.ofFn`) -/

theorem tx_ptOf_ofFn {n : ℕ} (f : Fin n → E) : ptOf (List.ofFn f) n = f := by
  funext i
  simp [ptOf, List.getD_eq_getElem?_getD, List.getElem?_ofFn]

theorem tx_getD_ofFn {n : ℕ} (f : Fin n → E) {i : ℕ} (hi : i < n) :
    (List.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]

theorem tx_sliceOf_ofFn (s : Cube (3 + 3) → E) :
    sliceOf (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)) = s := by
  funext cy
  rw [sliceOf, tx_getD_ofFn _ (cubeFin (3 + 3) cy).isLt]
  show s ((cubeFin (3 + 3)).symm (cubeFin (3 + 3) cy)) = s cy
  rw [Equiv.symm_apply_apply]

/-- `fixedChallenges` entry by entry. -/
theorem tx_fixedChallenges_getD : ∀ i : Fin 7, Flock.fixedChallenges.getD i 0 = fixedPt i := by
  intro i
  rw [fixedChallenges_eq, tx_getD_ofFn _ i.isLt]

/-- The zerocheck's starting claim at the main line's skip (`k = 3`). -/
theorem tx_interp : ∀ (cv : Cube 3 → E) (z : E),
    Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ List.ofFn fun i : Fin 8 ↦ cv ((cubeFin 3).symm i)) z =
      (FlockSound.interp (skipNodes 3 (by decide)) cv).eval z := by
  intro cv z
  have h := lagrangeInterpolate_skip 3 (by decide) (List.ofFn fun i : Fin 8 ↦ cv ((cubeFin 3).symm i)) z
  have hcv : (fun b : Cube 3 ↦
      (List.ofFn fun i : Fin 8 ↦ cv ((cubeFin 3).symm i)).getD (cubeFin 3 b) 0) = cv := by
    funext b
    rw [tx_getD_ofFn _ (cubeFin 3 b).isLt]
    show cv ((cubeFin 3).symm (cubeFin 3 b)) = cv b
    rw [Equiv.symm_apply_apply]
  rw [hcv] at h
  exact h

/-- The pending reduction's claim at the main line (`k = l = 3`). -/
theorem tx_claim : ∀ (z α rLc : E) (rl : Fin 3 → E) (rh χ' : Fin 8 → E) (s : Cube (3 + 3) → E),
    (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
        (some (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)))).claim =
      rLc + (α ^ 2 * FlockSound.eqEval rh χ' * ∑ cy, lowW (skipNodes 3 (by decide)) z rl cy * s cy +
        α ^ 3 * eqP χ' ((posFin (k := 3) (l := 3) rfl).symm Lv42.Parameters.Flock.constPos).2 *
          s ((posFin (k := 3) (l := 3) rfl).symm Lv42.Parameters.Flock.constPos).1) := by
  intro z α rLc rl rh χ' s
  rw [pending_claim (k := 3) (l := 3) rfl (by decide) z α rLc _ _ _ _ List.length_ofFn
    List.length_ofFn List.length_ofFn, tx_ptOf_ofFn, tx_ptOf_ofFn, tx_ptOf_ofFn, tx_sliceOf_ofFn]

/-- The pending reduction's sum at the main line (`k = l = 3`): the product sum. -/
theorem tx_sum : ∀ (z α rLc : E) (rl : Fin 3 → E) (rh χ' : Fin 8 → E) (s : Cube (3 + 3) → E),
    ∑ u ∈ range (2 ^ (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
        (some (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)))).rounds),
      Pending.G (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
          (some (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)))) u *
        Pending.L (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
          (some (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)))) u =
      ∑ cy, matPart (cubeMat (k := 3) (l := 3) rfl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A)
        (cubeMat (k := 3) (l := 3) rfl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B)
        (skipNodes 3 (by decide)) z rl rh χ' α cy * s cy := by
  intro z α rLc rl rh χ' s
  rw [pending_sum (k := 3) (l := 3) rfl (by decide) z α rLc _ _ _ _ List.length_ofFn List.length_ofFn,
    tx_ptOf_ofFn, tx_ptOf_ofFn, tx_ptOf_ofFn, tx_sliceOf_ofFn]

/-! ## `FlockTx`: the transcription, bundled -/

/-- **The evaluator transcription Flock's soundness needs** (items 1–6), at the main line (`k = l = 3`,
the lists the code reads being `List.ofFn` of the cube forms' functions): the evaluators
`Flock.verifyDeferred` calls, and those `FlockEndHolds` and `PendingHolds` read, equal `FlockSound`'s
objects at every input. Field by field the form `lean-flock-link`'s `Tx κ` (`FlockSoundUni/Catch.lean`)
takes, with its `sliceList s` and `towerShifts` unfolded (`List.ofFn fun i : Fin 64 ↦ s ((cubeFin 6).symm i)`
and `[1, 2, 4, 8, 16, 32]`, both by definition). -/
structure FlockTx (κ : ℕ) : Prop where
  /-- `fixed_challenges()` are leanVM's seven fixed coordinates (item 2). -/
  fixed : ∀ i : Fin 7, Flock.fixedChallenges.getD i 0 = fixedPt i
  /-- `E::pow` is the power. -/
  epow : ∀ (x : E) (n : ℕ), UniStatement.epow x n = x ^ n
  /-- The skip's start is the interpolant over the nodes `φ_8(0..15)` (item 1). -/
  interp : ∀ (cv : Cube 3 → E) (z : E),
    Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ List.ofFn fun i : Fin 8 ↦ cv ((cubeFin 3).symm i)) z =
      (FlockSound.interp (skipNodes 3 (by decide)) cv).eval z
  /-- **The ring switch's target** in tower order is `Σ_cy x^cy Φ_tower(s_cy)` (item 6). -/
  target : ∀ (s : Cube (3 + 3) → E) (f : Fin 6 → E),
    Flock.towerTarget (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)) (List.ofFn f) =
      ∑ cy, packW (k := 3) (l := 3) rfl cy * stagedMap [1, 2, 4, 8, 16, 32] f (s cy)
  /-- **The ring claim's weight** (`towerCoefficients` on the 64 twists) is `Φ_tower(eq(p, ·))` against
  the column (item 5). -/
  ring : ∀ (qf : LeanVM.Protocol.Column (8 + κ)) (p : Fin (8 + κ) → E) (f : Fin 6 → E),
    ∑ k ∈ range 64, (Flock.towerCoefficients (List.ofFn f)).getD k 0 * mleE qf (twist (List.ofFn p) k) =
      ∑ u, stagedMap [1, 2, 4, 8, 16, 32] f (eqP p u) * colWord qf u
  /-- **The pending claim** is `r_lc` plus the terminal's two known terms (item 3). -/
  claim : ∀ (z α rLc : E) (rl : Fin 3 → E) (rh χ' : Fin 8 → E) (s : Cube (3 + 3) → E),
    (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
        (some (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)))).claim =
      rLc + (α ^ 2 * FlockSound.eqEval rh χ' * ∑ cy, lowW (skipNodes 3 (by decide)) z rl cy * s cy +
        α ^ 3 * eqP χ' ((posFin (k := 3) (l := 3) rfl).symm Lv42.Parameters.Flock.constPos).2 *
          s ((posFin (k := 3) (l := 3) rfl).symm Lv42.Parameters.Flock.constPos).1)
  /-- **The pending sum** on the setup stacks is the matrices' part against the slices (item 4). -/
  sum : ∀ (z α rLc : E) (rl : Fin 3 → E) (rh χ' : Fin 8 → E) (s : Cube (3 + 3) → E),
    ∑ u ∈ range (2 ^ (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
        (some (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)))).rounds),
      Pending.G (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
          (some (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)))) u *
        Pending.L (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
          (some (List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)))) u =
      ∑ cy, matPart (cubeMat (k := 3) (l := 3) rfl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A)
        (cubeMat (k := 3) (l := 3) rfl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B)
        (skipNodes 3 (by decide)) z rl rh χ' α cy * s cy

/-- **The transcription holds**, for every `κ`. -/
theorem flockTx (κ : ℕ) : FlockTx κ where
  fixed := tx_fixedChallenges_getD
  epow := epow_eq
  interp := tx_interp
  target := tower_tx_target
  ring := tower_tx_ring κ
  claim := tx_claim
  sum := tx_sum

end FlockSound.Uni

/-! The guards below fail the build if a lemma's axioms grow beyond Lean's three. -/

/-- info: 'FlockSound.Uni.phi_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.phi_eq
/-- info: 'FlockSound.Uni.fixedChallenges_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.fixedChallenges_eq
/-- info: 'FlockSound.Uni.phi_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.phi_xor
/-- info: 'FlockSound.Uni.phi_add_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.phi_add_mem
/-- info: 'FlockSound.Uni.windowDenominator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.windowDenominator_eq
/-- info: 'FlockSound.Uni.lagrangeWeights_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.lagrangeWeights_getD
/-- info: 'FlockSound.Uni.lagrangeWeights_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.lagrangeWeights_skip
/-- info: 'FlockSound.Uni.lagrangeInterpolate_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.lagrangeInterpolate_skip
/-- info: 'FlockSound.Uni.ptOf_fixed_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.ptOf_fixed_append
/-- info: 'FlockSound.Uni.eqKernel_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.eqKernel_getD
/-- info: 'FlockSound.Uni.eqKernel_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.eqKernel_cube
/-- info: 'FlockSound.Uni.multilinearEval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.multilinearEval_eq
/-- info: 'FlockSound.Uni.eqEval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.eqEval_eq
/-- info: 'FlockSound.Uni.knownWeights_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.knownWeights_eq
/-- info: 'FlockSound.Uni.pending_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.pending_claim
/-- info: 'FlockSound.Uni.pending_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.pending_fields
/-- info: 'FlockSound.Uni.pending_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.pending_terminal
/-- info: 'FlockSound.Uni.mleArr_matrixStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.mleArr_matrixStack
/-- info: 'FlockSound.Uni.mleArr_flockMatrixStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.mleArr_flockMatrixStack
/-- info: 'FlockSound.Uni.pending_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.pending_sum
/-- info: 'FlockSound.Uni.pendingHolds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.pendingHolds_iff
/-- info: 'FlockSound.Uni.tx_fixedChallenges_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.tx_fixedChallenges_getD
/-- info: 'FlockSound.Uni.tx_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.tx_interp
/-- info: 'FlockSound.Uni.tx_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.tx_claim
/-- info: 'FlockSound.Uni.tx_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.tx_sum


/-! ## Axiom guards -/

/-- info: 'FlockSound.Uni.flockTx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flockTx
