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

/-- leanVM's generator `x` of `K^×` (`LeanVM.Parameters.g`). -/
local notation "gK" => LeanVM.Parameters.g

/-! ## The loops as folds -/

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem range_size_zero (n : ℕ) : [:n].size = n := by
  simp [Std.Legacy.Range.size]

theorem range_size_one (n : ℕ) : [1:n].size = n - 1 := by
  simp [Std.Legacy.Range.size]

/-- `c''`, `θ_j`'s part of `c` over `F_j`: `(c + c^(|F_j|)) / (θ_j + θ_j^(|F_j|))`. -/
def splitSecond (T : List E) (j : ℕ) (c : E) : E :=
  (c + conjugate c j) * (T.getD j 0 + conjugate (T.getD j 0) j)⁻¹

/-- `c'`, `c`'s part in `F_j`: `c + θ_j c''`. -/
def splitFirst (T : List E) (j : ℕ) (c : E) : E := c + T.getD j 0 * splitSecond T j c

/-- One level of `towerLeaves`' decomposition, over `F_j`: part `w` to `2w` (its part in `F_j`) and
`2w + 1` (`θ_j`'s). -/
def leafSplit (T : List E) (j : ℕ) (parts : Array E) : Array E :=
  (List.range parts.size).foldl (fun b a ↦
    (b.set! (2 * a) (splitFirst T j (parts.getD a 0))).set! (2 * a + 1) (splitSecond T j (parts.getD a 0)))
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
  unfold towerLeaves leavesModel leafMark leafParts leafSplit splitFirst splitSecond
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

/-- `stagedMap_tower` with the challenges read off a list (the verifier's `map`). -/
theorem stagedMap_tower_list (map : List E) (a : E) :
    stagedMap [1, 2, 4, 8, 16, 32] (fun i ↦ map.getD i.val 0) a = phiT (fun n ↦ map.getD n 0) 6 a :=
  stagedMap_tower (fun n ↦ map.getD n 0) a

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

/-! ## The tower's subfields -/

/-- **`c ∈ F_j = GF(2^(2^j))`**: `c` is fixed by `x ↦ x^(2^(2^j))`. -/
def InF (j : ℕ) (c : E) : Prop := c ^ 2 ^ 2 ^ j = c

theorem conjugate_eq (c : E) (j : ℕ) : conjugate c j = c ^ 2 ^ 2 ^ j := sqn_eq c (2 ^ j)

theorem pow_pow_fixed {c : E} {q : ℕ} (hc : c ^ q = c) : ∀ m, c ^ q ^ m = c
  | 0 => by simp
  | m + 1 => by rw [pow_succ, pow_mul, pow_pow_fixed hc m, hc]

theorem InF.mono {j j' : ℕ} (h : j ≤ j') {c : E} (hc : InF j c) : InF j' c := by
  unfold InF at hc ⊢
  have e : (2 : ℕ) ^ 2 ^ j' = (2 ^ 2 ^ j) ^ 2 ^ (j' - j) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' h]
  rw [e, pow_pow_fixed hc]

theorem inF_zero_iff (c : E) : InF 0 c ↔ c = 0 ∨ c = 1 := by
  unfold InF
  constructor
  · intro h
    have h' : c ^ 2 = c := by simpa using h
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h', sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · rintro (rfl | rfl) <;> simp

theorem inF_one (j : ℕ) : InF j 1 := by simp [InF]

theorem InF.mul {j : ℕ} {a b : E} (ha : InF j a) (hb : InF j b) : InF j (a * b) := by
  unfold InF at *
  rw [mul_pow, ha, hb]

theorem inF_prod {ι : Type*} (j : ℕ) (s : Finset ι) (a : ι → E) (h : ∀ i ∈ s, InF j (a i)) :
    InF j (∏ i ∈ s, a i) := by
  unfold InF at *
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl h

theorem frob_frob {j : ℕ} {x : E} (hx : InF (j + 1) x) : (x ^ 2 ^ 2 ^ j) ^ 2 ^ 2 ^ j = x := by
  rw [← pow_mul, ← pow_add, ← two_mul, ← pow_succ']
  exact hx

/-- **One level of the decomposition**: for `θ ∈ F_(j+1) \ F_j` and `c ∈ F_(j+1)`, `c = c' + θ c''` with
`c'' = (c + c^(|F_j|)) / (θ + θ^(|F_j|))` and `c' = c + θ c''` both in `F_j`. -/
theorem split_spec {j : ℕ} {θ c : E} (hθ : InF (j + 1) θ) (hθ' : θ + θ ^ 2 ^ 2 ^ j ≠ 0)
    (hc : InF (j + 1) c) :
    InF j (c + θ * ((c + c ^ 2 ^ 2 ^ j) * (θ + θ ^ 2 ^ 2 ^ j)⁻¹)) ∧
      InF j ((c + c ^ 2 ^ 2 ^ j) * (θ + θ ^ 2 ^ 2 ^ j)⁻¹) ∧
      c = (c + θ * ((c + c ^ 2 ^ 2 ^ j) * (θ + θ ^ 2 ^ 2 ^ j)⁻¹)) +
        θ * ((c + c ^ 2 ^ 2 ^ j) * (θ + θ ^ 2 ^ 2 ^ j)⁻¹) := by
  have h2 := two_eq_zero_E
  have hs : InF j ((c + c ^ 2 ^ 2 ^ j) * (θ + θ ^ 2 ^ 2 ^ j)⁻¹) := by
    unfold InF
    rw [mul_pow, inv_pow, frob_add, frob_add, frob_frob hc, frob_frob hθ, add_comm (c ^ 2 ^ 2 ^ j),
      add_comm (θ ^ 2 ^ 2 ^ j)]
  refine ⟨?_, hs, ?_⟩
  · unfold InF at hs ⊢
    rw [frob_add, mul_pow, hs]
    have key : (θ + θ ^ 2 ^ 2 ^ j) * ((c + c ^ 2 ^ 2 ^ j) * (θ + θ ^ 2 ^ 2 ^ j)⁻¹) =
        c + c ^ 2 ^ 2 ^ j := by
      rw [mul_left_comm, mul_inv_cancel₀ hθ', mul_one]
    linear_combination key + (c ^ 2 ^ 2 ^ j - θ * ((c + c ^ 2 ^ 2 ^ j) * (θ + θ ^ 2 ^ 2 ^ j)⁻¹)) * h2
  · linear_combination (-(θ * ((c + c ^ 2 ^ 2 ^ j) * (θ + θ ^ 2 ^ 2 ^ j)⁻¹))) * h2

/-! ## `θ_j`: a generator of `F_(j+1)`, not in `F_j` -/

/-- The exponent of `θ_j`, `(2^64 − 1) / (2^(2^(j+1)) − 1)`. -/
def thetaExp (j : ℕ) : ℕ := (2 ^ 64 - 1) / (2 ^ 2 ^ (j + 1) - 1)

theorem thetaExp_mul (j : ℕ) (hj : j < 6) : thetaExp j * (2 ^ 2 ^ (j + 1) - 1) = 2 ^ 64 - 1 := by
  interval_cases j <;> norm_num [thetaExp]

theorem theta_K_fixed (j : ℕ) (hj : j < 6) : (gK ^ thetaExp j) ^ 2 ^ 2 ^ (j + 1) = gK ^ thetaExp j := by
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ 2 ^ (j + 1) = Q + 1 :=
    ⟨2 ^ 2 ^ (j + 1) - 1, by have := Nat.one_le_two_pow (n := 2 ^ (j + 1)); omega⟩
  have hm := thetaExp_mul j hj
  rw [hQ, Nat.add_sub_cancel] at hm
  rw [hQ, pow_succ, ← pow_mul, hm, g_pow_card_sub_one, one_mul]

theorem theta_K_not_fixed (j : ℕ) (hj : j < 6) : (gK ^ thetaExp j) ^ 2 ^ 2 ^ j ≠ gK ^ thetaExp j := by
  intro h
  have hne : gK ^ thetaExp j ≠ 0 := pow_ne_zero _ g_ne_zero
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ 2 ^ j = Q + 1 :=
    ⟨2 ^ 2 ^ j - 1, by have := Nat.one_le_two_pow (n := 2 ^ j); omega⟩
  rw [hQ, pow_succ, ← pow_mul] at h
  have h1 : gK ^ (thetaExp j * Q) = 1 := mul_right_cancel₀ hne (h.trans (one_mul _).symm)
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_g] at hdvd
  rcases Nat.eq_zero_or_pos (thetaExp j * Q) with h0 | hpos
  · interval_cases j <;> norm_num [thetaExp] at hQ h0 <;> omega
  · have hle := Nat.le_of_dvd hpos hdvd
    interval_cases j <;> norm_num [thetaExp] at hQ hle <;> omega

theorem towerTheta_getD (j : ℕ) (hj : j < 6) : towerTheta.getD j 0 = ofK (gK ^ thetaExp j) := by
  unfold towerTheta
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by rw [towerStages_eq]; exact hj)]
  simp only [Option.map_some, Option.getD_some]
  unfold intoSubfield
  by_cases h5 : j = 5
  · rw [if_pos (by rw [towerStages_eq]; omega), h5, gen_eq, show thetaExp 5 = 1 by norm_num [thetaExp],
      pow_one]
  · rw [if_neg (by rw [towerStages_eq]; omega), epow_eq, gen_eq, ← ofK_pow']
    rfl

/-- **`θ_j ∈ F_(j+1)`.** -/
theorem theta_inF (j : ℕ) (hj : j < 6) : InF (j + 1) (towerTheta.getD j 0) := by
  rw [towerTheta_getD j hj, InF, ← ofK_pow', theta_K_fixed j hj]

/-- **`θ_j ∉ F_j`**: `θ_j + θ_j^(|F_j|) ≠ 0`, from `orderOf_g = 2^64 − 1`. -/
theorem theta_conj_ne (j : ℕ) (hj : j < 6) :
    towerTheta.getD j 0 + conjugate (towerTheta.getD j 0) j ≠ 0 := by
  rw [conjugate_eq, towerTheta_getD j hj, ← ofK_pow']
  intro h
  exact theta_K_not_fixed j hj (ofK_injective ((FlockSound.add_eq_zero_iff_eq'.mp h).symm))

theorem epow_gen_eq (i : ℕ) : epow gen i = ofK (gK ^ i) := by
  rw [epow_eq, gen_eq, ofK_pow']

/-- `x^i ∈ F_6 = K`. -/
theorem epow_gen_inF (i : ℕ) : InF 6 (epow gen i) := by
  rw [epow_gen_eq, InF, ← ofK_pow', show (2 : ℕ) ^ 2 ^ 6 = 2 ^ 64 by norm_num,
    FlockSound.K.pow_two_pow_sixtyFour]

/-! ## `towerLeaves`: the decomposition of `x^i` over the tower -/

theorem leafSplit_inv (T : List E) (j : ℕ) (parts : Array E) : ∀ m ≤ parts.size,
    ((List.range m).foldl (fun b a ↦ (b.set! (2 * a) (splitFirst T j (parts.getD a 0))).set! (2 * a + 1)
        (splitSecond T j (parts.getD a 0))) (Array.replicate (2 * parts.size) 0)).size = 2 * parts.size ∧
      ∀ t < 2 * parts.size,
        ((List.range m).foldl (fun b a ↦ (b.set! (2 * a) (splitFirst T j (parts.getD a 0))).set! (2 * a + 1)
          (splitSecond T j (parts.getD a 0))) (Array.replicate (2 * parts.size) 0)).getD t 0 =
        if t < 2 * m then (if t % 2 = 0 then splitFirst T j (parts.getD (t / 2) 0)
          else splitSecond T j (parts.getD (t / 2) 0)) else 0
  | 0, _ => by
    refine ⟨by simp, fun t ht ↦ ?_⟩
    simp only [List.range_zero, List.foldl_nil, getD_replicate, if_pos ht, Nat.mul_zero,
      Nat.not_lt_zero, if_false]
  | m + 1, hm => by
    obtain ⟨hsize, hget⟩ := leafSplit_inv T j parts m (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [size_set!, size_set!, hsize], fun t ht ↦ ?_⟩
    rw [getD_set!, getD_set!, size_set!, hsize]
    by_cases h1 : 2 * m + 1 = t
    · rw [if_pos ⟨h1, by omega⟩, if_pos (by omega), if_neg (by omega),
        show t / 2 = m by omega]
    · rw [if_neg (fun h ↦ h1 h.1)]
      by_cases h0 : 2 * m = t
      · rw [if_pos ⟨h0, by omega⟩, if_pos (by omega), if_pos (by omega), show t / 2 = m by omega]
      · rw [if_neg (fun h ↦ h0 h.1), hget t ht]
        split_ifs <;> first | rfl | omega

theorem leafSplit_size (T : List E) (j : ℕ) (parts : Array E) :
    (leafSplit T j parts).size = 2 * parts.size :=
  (leafSplit_inv T j parts parts.size le_rfl).1

theorem leafSplit_getD (T : List E) (j : ℕ) (parts : Array E) (t : ℕ) (ht : t < 2 * parts.size) :
    (leafSplit T j parts).getD t 0 = if t % 2 = 0 then splitFirst T j (parts.getD (t / 2) 0)
      else splitSecond T j (parts.getD (t / 2) 0) := by
  have := (leafSplit_inv T j parts parts.size le_rfl).2 t ht
  rw [if_pos ht] at this
  exact this

/-- The parts after `t` levels of the decomposition. -/
def partsAt (T : List E) (x : E) (t : ℕ) : Array E :=
  (List.range t).foldl (fun parts jj ↦ leafSplit T (6 - 1 - jj) parts) #[x]

theorem partsAt_succ (T : List E) (x : E) (t : ℕ) :
    partsAt T x (t + 1) = leafSplit T (6 - 1 - t) (partsAt T x t) := by
  rw [partsAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← partsAt]

/-- `Θ^(t)_w`: after `t` levels, bit `u` of the part's index took `θ_(6 − t + u)`. -/
def basisAt (T : List E) (t w : ℕ) : E :=
  ∏ u ∈ range t, if w.testBit u then T.getD (6 - t + u) 0 else 1

theorem basisAt_even (T : List E) (t w : ℕ) (ht : t < 6) :
    basisAt T (t + 1) (2 * w) = basisAt T t w := by
  rw [basisAt, prod_range_succ', basisAt]
  rw [show (2 * w).testBit 0 = false by simp [Nat.testBit_zero], if_neg (by simp), mul_one]
  refine prod_congr rfl fun u _ ↦ ?_
  rw [Nat.testBit_add_one, show 2 * w / 2 = w by omega, show 6 - (t + 1) + (u + 1) = 6 - t + u by omega]

theorem basisAt_odd (T : List E) (t w : ℕ) (ht : t < 6) :
    basisAt T (t + 1) (2 * w + 1) = T.getD (6 - 1 - t) 0 * basisAt T t w := by
  rw [basisAt, prod_range_succ', basisAt, mul_comm]
  rw [show (2 * w + 1).testBit 0 = true by simp [Nat.testBit_zero], if_pos rfl,
    show 6 - (t + 1) + 0 = 6 - 1 - t by omega]
  congr 1
  refine prod_congr rfl fun u _ ↦ ?_
  rw [Nat.testBit_add_one, show (2 * w + 1) / 2 = w by omega,
    show 6 - (t + 1) + (u + 1) = 6 - t + u by omega]

/-- **The decomposition**: after `t` levels, `2^t` parts in `F_(6−t)`, and
`x = Σ_w part_w Θ^(t)_w`. -/
theorem leafParts_spec (T : List E) (hT1 : ∀ j < 6, InF (j + 1) (T.getD j 0))
    (hT2 : ∀ j < 6, T.getD j 0 + conjugate (T.getD j 0) j ≠ 0) (x : E) (hx : InF 6 x) :
    ∀ t ≤ 6, (partsAt T x t).size = 2 ^ t ∧ (∀ w < 2 ^ t, InF (6 - t) ((partsAt T x t).getD w 0)) ∧
      x = ∑ w ∈ range (2 ^ t), (partsAt T x t).getD w 0 * basisAt T t w
  | 0, _ => by
    refine ⟨rfl, fun w hw ↦ ?_, ?_⟩
    · have : w = 0 := by simpa using hw
      subst this
      exact hx
    · simp [partsAt, basisAt]
  | t + 1, ht => by
    obtain ⟨hsize, hin, hsum⟩ := leafParts_spec T hT1 hT2 x hx t (by omega)
    have hj : 6 - 1 - t < 6 := by omega
    have hθ := hT1 (6 - 1 - t) hj
    have hθ' := hT2 (6 - 1 - t) hj
    rw [conjugate_eq] at hθ'
    have hpart : ∀ w < 2 ^ t, InF (6 - 1 - t) (splitFirst T (6 - 1 - t) ((partsAt T x t).getD w 0)) ∧
        InF (6 - 1 - t) (splitSecond T (6 - 1 - t) ((partsAt T x t).getD w 0)) ∧
        (partsAt T x t).getD w 0 = splitFirst T (6 - 1 - t) ((partsAt T x t).getD w 0) +
          T.getD (6 - 1 - t) 0 * splitSecond T (6 - 1 - t) ((partsAt T x t).getD w 0) := by
      intro w hw
      have hc := hin w hw
      rw [show 6 - t = 6 - 1 - t + 1 by omega] at hc
      have := split_spec hθ hθ' hc
      simpa only [splitFirst, splitSecond, conjugate_eq] using this
    rw [partsAt_succ]
    refine ⟨by rw [leafSplit_size, hsize, pow_succ, mul_comm], fun w hw ↦ ?_, ?_⟩
    · rw [leafSplit_getD _ _ _ _ (by rw [hsize, ← pow_succ']; omega)]
      have hw2 : w / 2 < 2 ^ t := by rw [pow_succ] at hw; omega
      rw [show 6 - (t + 1) = 6 - 1 - t by omega]
      split_ifs
      · exact (hpart _ hw2).1
      · exact (hpart _ hw2).2.1
    · rw [pow_succ', sum_range_double]
      conv_lhs => rw [hsum]
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      have hw' := mem_range.mp hw
      rw [leafSplit_getD _ _ _ _ (by rw [hsize]; omega), leafSplit_getD _ _ _ _ (by rw [hsize]; omega),
        if_pos (by omega), if_neg (by omega), show 2 * w / 2 = w by omega,
        show (2 * w + 1) / 2 = w by omega, basisAt_even T t w (by omega), basisAt_odd T t w (by omega)]
      conv_lhs => rw [(hpart w hw').2.2]
      ring

theorem leafMark_inv (i : ℕ) (parts : Array E) (leaves : Array ℕ) (hsz : leaves.size = parts.size) :
    ∀ m ≤ parts.size,
      ((List.range m).foldl (fun leaves w ↦
        if (parts.getD w 0 == 1) = true then leaves.modify w (· ||| 2 ^ i) else leaves) leaves).size =
          leaves.size ∧
      ∀ w < parts.size, ((List.range m).foldl (fun leaves w ↦
        if (parts.getD w 0 == 1) = true then leaves.modify w (· ||| 2 ^ i) else leaves) leaves).getD w 0 =
        if w < m ∧ parts.getD w 0 = 1 then leaves.getD w 0 ||| 2 ^ i else leaves.getD w 0
  | 0, _ => ⟨rfl, fun w _ ↦ by simp⟩
  | m + 1, hm => by
    obtain ⟨hsize, hget⟩ := leafMark_inv i parts leaves hsz m (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hp : parts.getD m 0 = 1
    · rw [if_pos (by simpa using hp)]
      refine ⟨by rw [Array.size_modify, hsize], fun w hw ↦ ?_⟩
      rw [getD_modify _ _ _ _ _ (by rw [hsize, hsz]; exact hw)]
      by_cases hmw : m = w
      · subst hmw
        rw [if_pos rfl, hget m hw, if_neg (by omega), if_pos ⟨by omega, hp⟩]
      · rw [if_neg hmw, hget w hw]
        by_cases hwm : w < m
        · by_cases hpw : parts.getD w 0 = 1
          · rw [if_pos ⟨hwm, hpw⟩, if_pos ⟨by omega, hpw⟩]
          · rw [if_neg (fun h ↦ hpw h.2), if_neg (fun h ↦ hpw h.2)]
        · rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by simpa using hp)]
      refine ⟨hsize, fun w hw ↦ ?_⟩
      rw [hget w hw]
      by_cases hmw : m = w
      · subst hmw
        rw [if_neg (by omega), if_neg (fun h ↦ hp h.2)]
      · by_cases hwm : w < m
        · by_cases hpw : parts.getD w 0 = 1
          · rw [if_pos ⟨hwm, hpw⟩, if_pos ⟨by omega, hpw⟩]
          · rw [if_neg (fun h ↦ hpw h.2), if_neg (fun h ↦ hpw h.2)]
        · rw [if_neg (by omega), if_neg (by omega)]

theorem leafMark_spec (i : ℕ) (parts : Array E) (leaves : Array ℕ) (hsz : leaves.size = parts.size) :
    (leafMark i parts leaves).size = leaves.size ∧ ∀ w < parts.size,
      (leafMark i parts leaves).getD w 0 =
        if parts.getD w 0 = 1 then leaves.getD w 0 ||| 2 ^ i else leaves.getD w 0 := by
  obtain ⟨h1, h2⟩ := leafMark_inv i parts leaves hsz parts.size le_rfl
  refine ⟨h1, fun w hw ↦ ?_⟩
  rw [leafMark, h2 w hw]
  by_cases hp : parts.getD w 0 = 1
  · rw [if_pos ⟨hw, hp⟩, if_pos hp]
  · rw [if_neg (fun h ↦ hp h.2), if_neg hp]

/-- **The leaves**: bit `i` of leaf `w` is set exactly when `x^i`'s part `w` is `1`. -/
theorem leaves_spec (P : ℕ → Array E) (hP : ∀ i, (P i).size = 64) :
    ∀ I ≤ 64, ((List.range I).foldl (fun leaves i ↦ leafMark i (P i) leaves) (Array.replicate 64 0)).size = 64 ∧
      ∀ w < 64, ∀ i, (((List.range I).foldl (fun leaves i ↦ leafMark i (P i) leaves)
        (Array.replicate 64 0)).getD w 0).testBit i = (decide (i < I) && decide ((P i).getD w 0 = 1))
  | 0, _ => by
    refine ⟨by simp, fun w hw i ↦ ?_⟩
    simp [hw]
  | I + 1, hI => by
    obtain ⟨hsize, hget⟩ := leaves_spec P hP I (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2⟩ := leafMark_spec I (P I) _ (by rw [hsize, hP])
    refine ⟨by rw [h1, hsize], fun w hw i ↦ ?_⟩
    rw [h2 w (by rw [hP]; exact hw)]
    by_cases hp : (P I).getD w 0 = 1
    · rw [if_pos hp, Nat.testBit_or, hget w hw i, Nat.testBit_two_pow]
      by_cases hiI : i = I
      · subst hiI; simp [hp]
      · have : I ≠ i := Ne.symm hiI
        simp only [this, decide_false, Bool.or_false]
        by_cases hlt : i < I
        · simp [hlt, show i < I + 1 by omega]
        · simp [hlt, show ¬ i < I + 1 by omega]
    · rw [if_neg hp, hget w hw i]
      by_cases hiI : i = I
      · subst hiI
        simp only [lt_irrefl, decide_false, Bool.false_and, Nat.lt_succ_self, decide_true, Bool.true_and]
        exact (decide_eq_false hp).symm
      · by_cases hlt : i < I
        · simp [hlt, show i < I + 1 by omega]
        · simp [hlt, show ¬ i < I + 1 by omega]

/-! ## `towerTarget`: the levels -/

/-- `Θ_r` on the low `j` bits: `Π_{t < j, bit t of r} θ_t`. -/
def basisLow (T : List E) (j r : ℕ) : E := ∏ t ∈ range j, if r.testBit t then T.getD t 0 else 1

theorem basisLow_inF (T : List E) (hT1 : ∀ j < 6, InF (j + 1) (T.getD j 0)) (j r : ℕ) (hj : j ≤ 6) :
    InF j (basisLow T j r) := by
  refine inF_prod j _ _ fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  split_ifs
  · exact (hT1 t (by omega)).mono (by omega)
  · exact inF_one j

theorem basisLow_low (T : List E) (j r : ℕ) (hr : r < 2 ^ j) : basisLow T (j + 1) r = basisLow T j r := by
  rw [basisLow, prod_range_succ, Nat.testBit_lt_two_pow hr, if_neg (by simp), mul_one, basisLow]

theorem basisLow_high (T : List E) (j r : ℕ) (hr : r < 2 ^ j) :
    basisLow T (j + 1) (2 ^ j + r) = T.getD j 0 * basisLow T j r := by
  rw [basisLow, prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr, mul_comm,
    basisLow]
  simp only [Bool.not_false, if_true]
  congr 1
  refine prod_congr rfl fun t ht ↦ ?_
  rw [Nat.testBit_two_pow_add_gt (mem_range.mp ht)]

/-- `Φ_j` is `F_j`-linear. -/
theorem stage_mul (c : E) (j : ℕ) {Θ : E} (hΘ : InF j Θ) (v : E) : stage c j (Θ * v) = Θ * stage c j v := by
  unfold stage
  rw [mul_pow, hΘ]
  ring

/-- The nodes after `j` levels. -/
def levelsAt (T map : List E) (N0 : Array E) (j : ℕ) : Array E := (List.range j).foldl (targetLevel T map) N0

/-- **The levels**: after `j` levels, node `q` is `Σ_{r < 2^j} Θ_r Φ_{<j}(leaf_(q 2^j + r))`. -/
theorem targetLevels_spec (T map : List E) (hT1 : ∀ j < 6, InF (j + 1) (T.getD j 0)) (N0 : Array E)
    (hN0 : N0.size = 64) : ∀ j ≤ 6, (levelsAt T map N0 j).size = 2 ^ (6 - j) ∧ ∀ q < 2 ^ (6 - j),
      (levelsAt T map N0 j).getD q 0 = ∑ r ∈ range (2 ^ j),
        basisLow T j r * phiT (fun n ↦ map.getD n 0) j (N0.getD (q * 2 ^ j + r) 0)
  | 0, _ => by
    refine ⟨hN0, fun q _ ↦ ?_⟩
    simp [levelsAt, basisLow, phiT]
  | j + 1, hj => by
    obtain ⟨hsize, hget⟩ := targetLevels_spec T map hT1 N0 hN0 j (by omega)
    have hpow : 2 ^ (6 - j) = 2 * 2 ^ (6 - (j + 1)) := by
      rw [← pow_succ']; congr 1; omega
    have hlev : levelsAt T map N0 (j + 1) = targetLevel T map (levelsAt T map N0 j) j := by
      rw [levelsAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← levelsAt]
    rw [hlev]
    refine ⟨by rw [targetLevel, Array.size_ofFn, hsize, hpow]; omega, fun q hq ↦ ?_⟩
    rw [targetLevel, getD_ofFn, dif_pos (by rw [hsize, hpow]; omega)]
    simp only
    rw [hget (2 * q) (by rw [hpow]; omega), hget (2 * q + 1) (by rw [hpow]; omega), sqn_eq, sqn_eq]
    have hst : ∀ a b : E, a + T.getD j 0 * b + map.getD j 0 * (a ^ 2 ^ 2 ^ j + T.getD j 0 * b ^ 2 ^ 2 ^ j) =
        stage (map.getD j 0) j a + T.getD j 0 * stage (map.getD j 0) j b := by
      intro a b; unfold stage; ring
    rw [hst, stage_sum, stage_sum, show (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j by ring, sum_range_add,
      Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hr' := mem_range.mp hr
      rw [stage_mul _ _ (basisLow_inF T hT1 j r (by omega)), basisLow_low T j r hr', phiT,
        show q * (2 ^ j + 2 ^ j) + r = 2 * q * 2 ^ j + r by ring]
    · refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hr' := mem_range.mp hr
      rw [stage_mul _ _ (basisLow_inF T hT1 j r (by omega)), basisLow_high T j r hr', phiT,
        show q * (2 ^ j + 2 ^ j) + (2 ^ j + r) = (2 * q + 1) * 2 ^ j + r by ring]
      ring

/-! ## The target -/

theorem basisAt_six (T : List E) (w : ℕ) : basisAt T 6 w = basisLow T 6 w := by
  unfold basisAt basisLow
  refine prod_congr rfl fun u _ ↦ ?_
  rw [show 6 - 6 + u = u by omega]

/-- **`towerTarget` is the ring switch's target** `Σ_{i<64} x^i Φ(s_i)`, `Φ = Φ_5 ∘ … ∘ Φ_0`. -/
theorem towerTarget_eq (s map : List E) :
    towerTarget s map = ∑ i ∈ range 64, ofK (gK ^ i) * phiT (fun n ↦ map.getD n 0) 6 (s.getD i 0) := by
  set f : ℕ → E := fun n ↦ map.getD n 0 with hf
  set P : ℕ → Array E := fun i ↦ leafParts 6 towerTheta (epow gen i) with hP
  have hPat : ∀ i, P i = partsAt towerTheta (epow gen i) 6 := fun i ↦ rfl
  have hspec := fun i ↦
    leafParts_spec towerTheta theta_inF theta_conj_ne (epow gen i) (epow_gen_inF i) 6 le_rfl
  have hPsize : ∀ i, (P i).size = 64 := fun i ↦ by rw [hPat]; exact (hspec i).1
  have hPbit : ∀ i, ∀ w < 64, (P i).getD w 0 = 0 ∨ (P i).getD w 0 = 1 := fun i w hw ↦
    (inF_zero_iff _).mp (by rw [hPat]; simpa using (hspec i).2.1 w (by simpa using hw))
  obtain ⟨hLsize, hLbit⟩ := leaves_spec P hPsize 64 le_rfl
  have hL : towerLeaves = (List.range 64).foldl (fun leaves i ↦ leafMark i (P i) leaves)
      (Array.replicate 64 0) := by
    rw [towerLeaves_eq, kBits_eq, towerStages_eq]
    rfl
  rw [towerTarget_eq_model, kBits_eq, towerStages_eq]
  set N0 := leafNodes 64 towerLeaves s with hN0
  have hN0size : N0.size = 64 := by simp [hN0, leafNodes]
  obtain ⟨_, hlev⟩ := targetLevels_spec towerTheta map theta_inF N0 hN0size 6 le_rfl
  have hmodel : targetModel 64 6 towerLeaves towerTheta s map = (levelsAt towerTheta map N0 6).getD 0 0 :=
    rfl
  rw [hmodel, hlev 0 (by norm_num)]
  -- The leaves' sums: `N0[r] = Σ_i ε_(i,r) s_i`.
  have hleaf : ∀ r < 64, phiT f 6 (N0.getD r 0) =
      ∑ i ∈ range 64, (P i).getD r 0 * phiT f 6 (s.getD i 0) := by
    intro r hr
    rw [hN0, leafNodes, getD_ofFn, dif_pos hr]
    simp only
    rw [foldl_ite_sum, phiT_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hL, hLbit r hr i]
    simp only [mem_range.mp hi, decide_true, Bool.true_and, decide_eq_true_eq]
    rcases hPbit i r hr with h0 | h1
    · rw [if_neg (by rw [h0]; exact zero_ne_one), h0, zero_mul, phiT_zero]
    · rw [if_pos h1, h1, one_mul]
  have hx : ∀ i, epow gen i = ∑ r ∈ range 64, (P i).getD r 0 * basisLow towerTheta 6 r := by
    intro i
    have := (hspec i).2.2
    simp only [basisAt_six] at this
    rw [hPat]
    simpa using this
  simp only [zero_mul, zero_add]
  rw [Finset.sum_congr rfl fun r hr ↦ by rw [hleaf r (mem_range.mp hr)], Finset.sum_congr rfl
    fun r _ ↦ Finset.mul_sum _ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← epow_gen_eq, hx i, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  ring

/-- **The target, on the cube**: `towerTarget s map = Σ_cy x^cy Φ_tower(ŝ(cy))`, `Front.target`'s form. -/
theorem towerTarget_eq_target {k l : ℕ} (hkl : k + l = 6) (s map : List E) :
    towerTarget s map = ∑ cy, packW hkl cy *
      stagedMap [1, 2, 4, 8, 16, 32] (fun i ↦ map.getD i.val 0) (sliceOf s cy) := by
  rw [towerTarget_eq, show (64 : ℕ) = 2 ^ (k + l) by rw [hkl]; rfl, sum_range_eq_sum_cube]
  refine Finset.sum_congr rfl fun cy _ ↦ ?_
  rw [stagedMap_tower_list, packW, cube64_val, sliceOf]

/-! ## The ring claim the verifier pushes on `q_flock` -/

theorem cubeEq_twist (p : List E) (n x k : ℕ) : cubeEq (twist p k) n x = cubeEq p n x ^ 2 ^ k := by
  unfold cubeEq
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  have h0 : (0 : E) = sqn 0 k := by rw [sqn_eq, zero_pow (by positivity)]
  rw [twist, h0, List.getD_map, ← h0, sqn_eq, frob_add, frob_add, one_pow]
  split_ifs
  · rw [one_pow]
  · rw [zero_pow (by positivity)]

theorem wordFin_eq (κ : ℕ) (u : Cube (8 + κ)) : wordFin κ (lowPart u, highPart u) = cubeFin (8 + κ) u := by
  apply Fin.ext
  simp only [wordFin, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, LeanVM.Protocol.cubeSplit_apply,
    LeanVM.Protocol.cubeIndex]
  rw [← cubeFin_append_val, append_lowPart_highPart]

/-- **The ring claim the verifier pushes on `q_flock`** (`FlockEndHolds`: the 64 twisted terms
`Σ_k d_k q̂(φ^k(p))`, `d = towerCoefficients map`) **is `hring`'s left side**,
`Σ_u Φ_tower(eq(p, u)) q(u)`. -/
theorem ringClaim_code (κ : ℕ) (qf : LeanVM.Protocol.Column (8 + κ)) (p map : List E) :
    ∑ k ∈ range 64, (towerCoefficients map).getD k 0 * mleE qf (twist p k) =
      ∑ u, stagedMap [1, 2, 4, 8, 16, 32] (fun i ↦ map.getD i.val 0) (eqP (ptOf p (8 + κ)) u) *
        colWord qf u := by
  simp only [mleE, cubeEq_twist, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← (cubeFin (8 + κ)).sum_comp]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [stagedMap_tower_list, phiT_expand, show (2 : ℕ) ^ 6 = 64 by norm_num, Finset.sum_mul, cubeEq_cubeFin,
    colWord, wordFin_eq]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [towerCoefficients_getD map k (mem_range.mp hk)]
  ring

end FlockSound.Uni

/-! ## Axiom guards -/

/-- info: 'FlockSound.Uni.epow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.epow_eq

/-- info: 'FlockSound.Uni.sqn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.sqn_eq

/-- info: 'FlockSound.Uni.cubeEq_cubeFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.cubeEq_cubeFin

/-- info: 'FlockSound.Uni.ptOf_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.ptOf_append

/-- info: 'FlockSound.Uni.towerLeaves_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.towerLeaves_eq

/-- info: 'FlockSound.Uni.towerTarget_eq_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.towerTarget_eq_model

/-- info: 'FlockSound.Uni.towerCoefficients_eq_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.towerCoefficients_eq_model

/-- info: 'FlockSound.Uni.stagedMap_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.stagedMap_tower

/-- info: 'FlockSound.Uni.phiT_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.phiT_expand

/-- info: 'FlockSound.Uni.coefD_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.coefD_rec

/-- info: 'FlockSound.Uni.towerCoefficients_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.towerCoefficients_getD

/-- info: 'FlockSound.Uni.theta_inF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.theta_inF

/-- info: 'FlockSound.Uni.theta_conj_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.theta_conj_ne

/-- info: 'FlockSound.Uni.split_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.split_spec

/-- info: 'FlockSound.Uni.leafParts_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.leafParts_spec

/-- info: 'FlockSound.Uni.leaves_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.leaves_spec

/-- info: 'FlockSound.Uni.targetLevels_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.targetLevels_spec

/-- info: 'FlockSound.Uni.towerTarget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.towerTarget_eq

/-- info: 'FlockSound.Uni.towerTarget_eq_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.towerTarget_eq_target

/-- info: 'FlockSound.Uni.cubeEq_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.cubeEq_twist

/-- info: 'FlockSound.Uni.ringClaim_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.ringClaim_code
