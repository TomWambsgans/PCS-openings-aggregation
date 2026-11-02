-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The evaluators are `formal/UniStatement`'s
-- (`UniStatement/Flock.lean`, transcribed from `crates/leanvm_flock_gas/src/ring_tower.rs`); the staged map
-- is `FlockSound.Frobenius`'s.
import FlockSoundUni.TxBasic

/-!
# The ring switch in tower order: the code's evaluators are `Φ_tower`

The ring switch's map in tower order is `Φ = Φ_5 ∘ … ∘ Φ_0`, `Φ_j(a) = a + f_j a^(2^(2^j))`
(`stagedMap [1, 2, 4, 8, 16, 32]`, here `phiT f 6`, built stage by stage: `phiT_eq`). The verifier
evaluates it two ways (`ring_tower.rs`):

* **its coefficients** (`towerCoefficients`): `Φ(a) = Σ_{k<64} d_k a^(2^k)`; `phiT_expand` gives `Φ`'s
  coefficients in closed form (`coefD`), and the code's recursion `d_k = d_(k − 2^j) f_j^(2^(k − k mod
  2^(j+1)))` (`j` the lowest set bit of `k`) computes them (`towerCoefficients_getD`). Hence the claim
  the verifier pushes on `q_flock` is the ring claim's value (`ringClaim_code`):
  `Σ_k d_k q̂(φ^k(p)) = Σ_u Φ(eq(p, u)) q(u)`.
* **the target** (`towerTarget`): `Σ_i x^i Φ(s_i)` through `K`'s subfields
  `F_j = GF(2^(2^j))` (`InF j`): `θ_j ∈ F_(j+1) \ F_j` (`theta_inF`, `theta_notInF`, from
  `orderOf_g = 2^64 − 1`); `towerLeaves` decomposes `x^i` over the tower, each part
  `c = c' + θ_j c''` with `c', c'' ∈ F_j` (`split_spec`), down to `GF(2)`: `x^i = Σ_w ε_(i,w) Θ_w`,
  `Θ_w = Π_{j : bit j of w} θ_j` (`leafParts_spec`); level `j` of the target computes
  `Φ_j(a) + θ_j Φ_j(b)`, and `Φ_j` is `F_j`-linear (`stage_mul`), so the levels give
  `Σ_w Θ_w Φ(L_w)` (`targetLevels_spec`), `L_w = Σ_i ε_(i,w) s_i` the leaves: **`towerTarget_eq`**.

The loops (`Id.run` with `for` and arrays) are first rewritten as folds with every closed constant
generalized (`towerLeaves_eq`, `towerTarget_eq_model`, `towerCoefficients_eq_model`), so that the kernel
never evaluates `E` nor a loop; the folds are then read through invariants.
-/

namespace FlockSound.Uni

open UniStatement UniStatement.Flock UniSound LeanVM.Parameters Finset

/-! ## The loops as folds -/

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem range_size_zero (n : ℕ) : [:n].size = n := by
  simp [Std.Legacy.Range.size]

theorem range_size_one (n : ℕ) : [1:n].size = n - 1 := by
  simp [Std.Legacy.Range.size]

/-- One level of `towerLeaves`' decomposition, over `F_j`: part `w` to `2w` (its part in `F_j`) and
`2w + 1` (`θ_j`'s). -/
def leafSplit (T : List E) (j : ℕ) (parts : Array E) : Array E :=
  (List.range parts.size).foldl (fun b a ↦
    (b.set! (2 * a) (parts.getD a 0 + T.getD j 0 * ((parts.getD a 0 + conjugate (parts.getD a 0) j) *
      (T.getD j 0 + conjugate (T.getD j 0) j)⁻¹))).set! (2 * a + 1)
      ((parts.getD a 0 + conjugate (parts.getD a 0) j) * (T.getD j 0 + conjugate (T.getD j 0) j)⁻¹))
    (Array.replicate (2 * parts.size) 0)

/-- The decomposition of `x` over the tower, `ns` levels, `F_(ns−1)` first. -/
def leafParts (ns : ℕ) (T : List E) (x : E) : Array E :=
  (List.range ns).foldl (fun parts jj ↦ leafSplit T (ns - 1 - jj) parts) #[x]

/-- Mark slice `i` in the leaves whose part is `1`. -/
def leafMark (i : ℕ) (parts : Array E) (leaves : Array ℕ) : Array ℕ :=
  (List.range parts.size).foldl (fun leaves w ↦
    if (parts.getD w 0 == 1) = true then leaves.modify w (· ||| 2 ^ i) else leaves) leaves

/-- `towerLeaves` as folds. -/
def leavesModel (nb ns : ℕ) (T : List E) (gg : E) : Array ℕ :=
  (List.range nb).foldl (fun leaves i ↦ leafMark i (leafParts ns T (epow gg i)) leaves)
    (Array.replicate nb 0)

theorem towerLeaves_eq : towerLeaves = leavesModel kBits towerStages towerTheta gen := by
  unfold towerLeaves leavesModel leafMark leafParts leafSplit
  generalize kBits = nb
  generalize towerStages = ns
  generalize towerTheta = T
  generalize gen = gg
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size_zero, ite_pure_yield,
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, ← List.range_eq_range']

/-- One level of `towerTarget`: the pairs `(2q, 2q + 1)` to `(a + θ_j b) + f_j (a^(|F_j|) + θ_j b^(|F_j|))`. -/
def targetLevel (T map : List E) (nodes : Array E) (j : ℕ) : Array E :=
  Array.ofFn (n := nodes.size / 2) fun q ↦
    nodes.getD (2 * q.val) 0 + T.getD j 0 * nodes.getD (2 * q.val + 1) 0 +
      map.getD j 0 * (sqn (nodes.getD (2 * q.val) 0) (2 ^ j) +
        T.getD j 0 * sqn (nodes.getD (2 * q.val + 1) 0) (2 ^ j))

/-- The leaves' sums of slices. -/
def leafNodes (nb : ℕ) (L : Array ℕ) (s : List E) : Array E :=
  Array.ofFn (n := nb) fun w ↦
    (List.range nb).foldl (fun acc i ↦ if (L.getD w.val 0).testBit i = true then acc + s.getD i 0 else acc) 0

/-- `towerTarget` as folds. -/
def targetModel (nb ns : ℕ) (L : Array ℕ) (T s map : List E) : E :=
  ((List.range ns).foldl (targetLevel T map) (leafNodes nb L s)).getD 0 0

theorem towerTarget_eq_model (s map : List E) :
    towerTarget s map = targetModel kBits towerStages towerLeaves towerTheta s map := by
  unfold towerTarget targetModel targetLevel leafNodes
  generalize kBits = nb
  generalize towerStages = ns
  generalize towerTheta = T
  generalize towerLeaves = L
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size_zero,
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, ← List.range_eq_range']

/-- One step of `towerCoefficients`. -/
def coefStep (map : List E) (d : Array E) (k : ℕ) : Array E :=
  d.set! k (d.getD (k - 2 ^ trailingZeros k) 1 *
    sqn (map.getD (trailingZeros k) 0) (k - k % 2 ^ (trailingZeros k + 1)))

theorem towerCoefficients_eq_model (map : List E) :
    towerCoefficients map = ((List.range' 1 (kBits - 1)).foldl (coefStep map)
      (Array.replicate kBits 1)).toList := by
  unfold towerCoefficients coefStep
  generalize kBits = nb
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size_one,
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure]

theorem kBits_eq : kBits = 64 := by unfold kBits; rfl

theorem towerStages_eq : towerStages = 6 := by unfold towerStages; rfl

/-! ## Arrays -/

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) :
    (Array.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split <;> rfl

theorem getD_set! {α : Type} (a : Array α) (i j : ℕ) (v d : α) :
    (a.set! i v).getD j d = if i = j ∧ i < a.size then v else a.getD j d := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.getD_eq_getD_getElem?]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem size_set! {α : Type} (a : Array α) (i : ℕ) (v : α) : (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem getD_modify {α : Type} (a : Array α) (i j : ℕ) (f : α → α) (d : α) (hj : j < a.size) :
    (a.modify i f).getD j d = if i = j then f (a.getD j d) else a.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hj]
  split <;> rfl

theorem getD_replicate {α : Type} (n i : ℕ) (v d : α) :
    (Array.replicate n v).getD i d = if i < n then v else d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem toList_getD {α : Type} (a : Array α) (i : ℕ) (d : α) : a.toList.getD i d = a.getD i d := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-! ## Sums -/

theorem sum_range_double {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ∑ w ∈ range (2 * n), f w = ∑ w ∈ range n, (f (2 * w) + f (2 * w + 1))
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_double f n, sum_range_succ, add_assoc]

theorem foldl_ite_sum (c : ℕ → Prop) [DecidablePred c] (s : ℕ → E) :
    ∀ n, (List.range n).foldl (fun acc i ↦ if c i then acc + s i else acc) 0 =
      ∑ i ∈ range n, if c i then s i else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_ite_sum c s n, sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split <;> simp

/-! ## Characteristic two: the Frobenius -/

theorem frob_add (a b : E) (m : ℕ) : (a + b) ^ 2 ^ m = a ^ 2 ^ m + b ^ 2 ^ m := by
  rw [add_pow_char_pow]

theorem frob_sum {ι : Type*} (s : Finset ι) (a : ι → E) (m : ℕ) :
    (∑ i ∈ s, a i) ^ 2 ^ m = ∑ i ∈ s, a i ^ 2 ^ m :=
  sum_pow_char_pow 2 m s a

theorem ofK_pow' (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

/-! ## The stages of the map -/

/-- **Stage `j`** of the map in tower order, its challenge `c`: `v ↦ v + c v^(2^(2^j))`. -/
def stage (c : E) (j : ℕ) (v : E) : E := v + c * v ^ 2 ^ 2 ^ j

/-- **`Φ_{<n}`**: the first `n` stages, stage `0` first (the map is `phiT f 6`). -/
def phiT (f : ℕ → E) : ℕ → E → E
  | 0, a => a
  | n + 1, a => stage (f n) n (phiT f n a)

theorem stage_add (c : E) (j : ℕ) (a b : E) : stage c j (a + b) = stage c j a + stage c j b := by
  unfold stage
  rw [frob_add]
  ring

theorem stage_zero (c : E) (j : ℕ) : stage c j 0 = 0 := by
  simp [stage]

theorem stage_sum {ι : Type*} (c : E) (j : ℕ) (s : Finset ι) (a : ι → E) :
    stage c j (∑ i ∈ s, a i) = ∑ i ∈ s, stage c j (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [stage_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, stage_add, ih]

theorem phiT_add (f : ℕ → E) : ∀ (n : ℕ) (a b : E), phiT f n (a + b) = phiT f n a + phiT f n b
  | 0, _, _ => rfl
  | n + 1, a, b => by simp only [phiT, phiT_add f n, stage_add]

theorem phiT_zero (f : ℕ → E) : ∀ n, phiT f n 0 = 0
  | 0 => rfl
  | n + 1 => by simp only [phiT, phiT_zero f n, stage_zero]

theorem phiT_sum {ι : Type*} (f : ℕ → E) (n : ℕ) (s : Finset ι) (a : ι → E) :
    phiT f n (∑ i ∈ s, a i) = ∑ i ∈ s, phiT f n (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phiT_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, phiT_add, ih]

/-! ## The staged map in tower order, stage by stage -/

/-- The staged map with its challenges read off a function of the stage. -/
def smap (L : List ℕ) (f : ℕ → E) (a : E) : E := stagedMap L (fun i ↦ f i.val) a

theorem smap_snoc : ∀ (L : List ℕ) (s : ℕ) (f : ℕ → E) (a : E),
    smap (L ++ [s]) f a = smap L f a + f L.length * smap L f a ^ 2 ^ s
  | [], _, _, _ => rfl
  | t :: L, s, f, a => smap_snoc L s (fun n ↦ f (n + 1)) (a + f 0 * a ^ 2 ^ t)

theorem smap_range (f : ℕ → E) (a : E) :
    ∀ n, smap ((List.range n).map (2 ^ ·)) f a = phiT f n a
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_singleton, smap_snoc, smap_range f a n,
      List.length_map, List.length_range, phiT, stage]

/-- **The staged map in tower order is `phiT f 6`.** -/
theorem stagedMap_tower (f : ℕ → E) (a : E) :
    stagedMap [1, 2, 4, 8, 16, 32] (fun i ↦ f i.val) a = phiT f 6 a := by
  have h : ([1, 2, 4, 8, 16, 32] : List ℕ) = (List.range 6).map (2 ^ ·) := by decide
  change smap [1, 2, 4, 8, 16, 32] f a = _
  rw [h, smap_range]

/-! ## The map's coefficients -/

/-- **`Φ_{<n}`'s coefficient of `a^(2^K)`**: `Π_{t : bit t of K} f_t^(2^(K with its bits ≤ t cleared))`. -/
def coefD (f : ℕ → E) (n K : ℕ) : E :=
  ∏ t ∈ range n, if K.testBit t then f t ^ 2 ^ (K / 2 ^ (t + 1) * 2 ^ (t + 1)) else 1

theorem coefD_low (f : ℕ → E) (n K : ℕ) (hK : K < 2 ^ n) : coefD f (n + 1) K = coefD f n K := by
  rw [coefD, prod_range_succ, Nat.testBit_lt_two_pow hK, if_neg (by simp), mul_one, coefD]

theorem coefD_high (f : ℕ → E) (n K : ℕ) (hK : K < 2 ^ n) :
    coefD f (n + 1) (2 ^ n + K) = f n * coefD f n K ^ 2 ^ 2 ^ n := by
  rw [coefD, prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hK, coefD,
    ← Finset.prod_pow]
  have hdiv : (2 ^ n + K) / 2 ^ (n + 1) = 0 := Nat.div_eq_of_lt (by rw [pow_succ]; omega)
  rw [hdiv]
  simp only [Bool.not_false, if_true, zero_mul, pow_zero, pow_one]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun t ht ↦ ?_
  have ht' : t < n := mem_range.mp ht
  rw [Nat.testBit_two_pow_add_gt ht']
  split_ifs
  · rw [← pow_mul, ← pow_add]
    congr 2
    -- `(2^n + K) / 2^(t+1) · 2^(t+1) = K / 2^(t+1) · 2^(t+1) + 2^n`.
    obtain ⟨d, hd⟩ : ∃ d, n = t + 1 + d := ⟨n - (t + 1), by omega⟩
    rw [hd, pow_add, Nat.mul_add_div (Nat.two_pow_pos _), add_mul, Nat.mul_comm (2 ^ d)]
    ring
  · simp

/-- **`Φ_{<n}` by its coefficients**: `phiT f n a = Σ_{K < 2^n} coefD f n K · a^(2^K)`. -/
theorem phiT_expand (f : ℕ → E) (a : E) :
    ∀ n, phiT f n a = ∑ K ∈ range (2 ^ n), coefD f n K * a ^ 2 ^ K
  | 0 => by
    rw [pow_zero, Finset.sum_range_one, coefD, Finset.prod_range_zero, one_mul, pow_zero, pow_one]
    rfl
  | n + 1 => by
    rw [phiT, phiT_expand f a n, stage, frob_sum, show (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n by ring,
      sum_range_add, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun K hK ↦ ?_
      rw [coefD_low f n K (mem_range.mp hK)]
    · refine Finset.sum_congr rfl fun K hK ↦ ?_
      rw [coefD_high f n K (mem_range.mp hK), mul_pow, ← pow_mul, ← pow_add, add_comm (2 ^ n) K]
      ring

/-! ## `trailingZeros` and the code's recursion -/

theorem trailingZeros_spec (K : ℕ) (h0 : 0 < K) (h64 : K < 64) :
    trailingZeros K < 6 ∧ K.testBit (trailingZeros K) = true ∧
      ∀ t < trailingZeros K, K.testBit t = false := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.mp h0)
  have hi6 : i < 6 := by
    by_contra hge
    have := Nat.ge_two_pow_of_testBit hi
    have : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold trailingZeros
  rw [if_neg (by omega)]
  cases hf : (List.range 64).find? (fun k ↦ K.testBit k) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf i (List.mem_range.mpr (by omega))
    simp [hi] at this
  | some j =>
    obtain ⟨hpj, idx, hidx, hlj, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hf
    rw [List.getElem_range] at hlj
    subst hlj
    simp only [Option.getD_some]
    refine ⟨?_, hpj, fun t ht ↦ ?_⟩
    · by_contra hge
      have := Nat.ge_two_pow_of_testBit hpj
      have : 2 ^ 6 ≤ 2 ^ idx := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have := hbefore t ht
      rw [List.getElem_range] at this
      simpa using this

/-- **The code's recursion holds of the closed form**: `d_K = d_(K − 2^j) f_j^(2^(K − K mod 2^(j+1)))`,
`j` the lowest set bit of `K`. -/
theorem coefD_rec (f : ℕ → E) (K : ℕ) (h0 : 0 < K) (h64 : K < 64) :
    coefD f 6 K = coefD f 6 (K - 2 ^ trailingZeros K) *
      f (trailingZeros K) ^ 2 ^ (K - K % 2 ^ (trailingZeros K + 1)) := by
  obtain ⟨hj6, hjb, hlow⟩ := trailingZeros_spec K h0 h64
  set j := trailingZeros K with hj
  -- `K = 2^(j+1) c + 2^j`.
  have hmod : K % 2 ^ (j + 1) = 2 ^ j := by
    refine Nat.eq_of_testBit_eq fun i ↦ ?_
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases hij : i < j
    · simp [hlow i hij, show i < j + 1 by omega, show j ≠ i by omega]
    · by_cases hji : i = j
      · subst hji; simp [hjb]
      · simp [show ¬ i < j + 1 by omega, show j ≠ i by omega]
  have hdm := Nat.div_add_mod K (2 ^ (j + 1))
  have hexp : K / 2 ^ (j + 1) * 2 ^ (j + 1) = K - K % 2 ^ (j + 1) := by
    rw [Nat.mul_comm]; omega
  set c := K / 2 ^ (j + 1) with hc
  have hK : K = 2 ^ (j + 1) * c + 2 ^ j := by
    rw [hmod] at hdm
    omega
  have hK' : K - 2 ^ j = 2 ^ (j + 1) * c + 0 := by omega
  have hlt : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hbits : ∀ t, t ≠ j → (K - 2 ^ j).testBit t = K.testBit t := by
    intro t ht
    rw [hK', Nat.testBit_two_pow_mul_add _ (by positivity), hK,
      Nat.testBit_two_pow_mul_add _ hlt]
    split_ifs
    · rw [Nat.testBit_two_pow]; simp [Nat.zero_testBit, Ne.symm ht]
    · rfl
  have hdiv : ∀ t, j < t → (K - 2 ^ j) / 2 ^ (t + 1) = K / 2 ^ (t + 1) := by
    intro t ht
    have e : 2 ^ (t + 1) = 2 ^ (j + 1) * 2 ^ (t - j) := by
      rw [← pow_add]; congr 1; omega
    rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hK', hK,
      Nat.mul_add_div (Nat.two_pow_pos _), Nat.mul_add_div (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hlt, Nat.zero_div]
  have hj6' : j ∈ range 6 := mem_range.mpr hj6
  rw [coefD, coefD, ← Finset.mul_prod_erase _ _ hj6', ← Finset.mul_prod_erase _ _ hj6',
    if_pos hjb, show (K - 2 ^ j).testBit j = false by
      rw [hK', Nat.testBit_two_pow_mul_add _ (by positivity)]; simp,
    if_neg (by simp), one_mul, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun t ht ↦ ?_
    have htj : t ≠ j := Finset.ne_of_mem_erase ht
    rw [hbits t htj]
    split_ifs with hb
    · rcases lt_or_gt_of_ne htj with h | h
      · rw [hlow t h] at hb; exact absurd hb (by simp)
      · rw [hdiv t h]
    · rfl
  · rw [hexp]

/-- **`towerCoefficients` computes the map's coefficients.** -/
theorem towerCoefficients_getD (map : List E) (k : ℕ) (hk : k < 64) :
    (towerCoefficients map).getD k 0 = coefD (fun j ↦ map.getD j 0) 6 k := by
  set f : ℕ → E := fun j ↦ map.getD j 0 with hf
  have inv : ∀ m ≤ 63, ((List.range' 1 m).foldl (coefStep map) (Array.replicate 64 1)).size = 64 ∧
      ∀ t < 64, ((List.range' 1 m).foldl (coefStep map) (Array.replicate 64 1)).getD t 1 =
        if t ≤ m then coefD f 6 t else 1 := by
    intro m hm
    induction m with
    | zero =>
      simp only [List.range'_zero, List.foldl_nil]
      refine ⟨by simp, fun t ht ↦ ?_⟩
      rw [getD_replicate, if_pos ht]
      split_ifs with h0
      · have : t = 0 := by omega
        subst this
        simp [coefD]
      · rfl
    | succ m ih =>
      obtain ⟨hsize, hget⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set d := (List.range' 1 m).foldl (coefStep map) (Array.replicate 64 1)
      refine ⟨by rw [coefStep, size_set!, hsize], fun t ht ↦ ?_⟩
      rw [coefStep, getD_set!, hsize]
      have hk0 : 0 < 1 + 1 * m := by omega
      obtain ⟨hj6, hjb, _⟩ := trailingZeros_spec (1 + 1 * m) hk0 (by omega)
      have hpow := Nat.ge_two_pow_of_testBit hjb
      have hpos : 0 < 2 ^ trailingZeros (1 + 1 * m) := Nat.two_pow_pos _
      set p := 2 ^ trailingZeros (1 + 1 * m) with hp
      by_cases htk : 1 + 1 * m = t
      · rw [if_pos ⟨htk, by omega⟩, hget _ (by omega), if_pos (by omega), sqn_eq, ← htk,
          if_pos (by omega)]
        exact (coefD_rec f (1 + 1 * m) hk0 (by omega)).symm
      · rw [if_neg (fun h ↦ htk h.1), hget t ht]
        split_ifs <;> first | rfl | omega
  rw [towerCoefficients_eq_model, kBits_eq, toList_getD, show (64 : ℕ) - 1 = 63 from rfl]
  obtain ⟨hsz, hget⟩ := inv 63 le_rfl
  have h := hget k hk
  rw [if_pos (by omega)] at h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)] at h
  simpa using h

end FlockSound.Uni
