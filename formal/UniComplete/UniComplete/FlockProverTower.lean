-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Copied from `formal/FlockSound` (branches
-- `lean-flock-tx`, commit 5adde3c, `FlockSoundUni/Tower.lean` and `FlockSoundUni/TxBasic.lean`; `lean-flock-sound`,
-- `FlockSound/Fields.lean`, `FlockSound/R1CS.lean`), unchanged but for the namespace and the linter options: the
-- tower decomposition of the ring switch's target, `towerTarget_eq` (`towerTarget s map = Σ_i x^i Φ_tower(s_i)`),
-- and what it rests on (`K.eq_sum_bits`, `ofK_eq_sum_cellBit`, the powers). Fields.lean is itself ported from
-- leanerVM `mumbai` f0393df4 (MIT OR Apache-2.0).
import UniComplete.FlockProverMle
import LeanVM.Parameters.Generator
import Mathlib.FieldTheory.Finite.Basic

/-!
# The ring switch in tower order: `towerTarget` is `Σ_i x^i Φ(s_i)` (copied)

`towerTarget_eq`: the verifier's `towerTarget s map` (64 leaves of slices, six levels through `K`'s subfields) is
`Σ_{i<64} x^i Φ(s_i)`, `Φ = Φ_5 ∘ … ∘ Φ_0`, `Φ_j(a) = a + f_j a^(2^(2^j))` (`phiT`). The proof (`θ_j ∈ F_(j+1) \ F_j`,
the leaves the `GF(2)` coordinates of `x^i` over the tower, each level `F_j`-linear) is `formal/FlockSound`'s
(`FlockSoundUni/Tower.lean` at `lean-flock-tx` 5adde3c), copied rather than imported: that library is not part of
this workspace's `UniComplete` build. Also copied: `K.eq_sum_bits`, `ofK_eq_sum_cellBit` (a cell is its bits packed
by the powers of `x`), `K.pow_two_pow_sixtyFour`, `add_eq_zero_iff_eq'`, `epow_eq`, `sqn_eq`, `eK_eq`, `gen_eq`.

Decision: the copies keep their proofs; the deprecation and unused-argument linters are off here (the originals are
built without `warningAsError`).
-/

namespace UniComplete.FlockP.Tower

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Protocol Finset CompPoly


set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

/-- leanVM's generator `x` of `K^×` (`LeanVM.Parameters.g`). -/
local notation "gK" => LeanVM.Parameters.g

theorem sub_eq_add_E (a b : E) : a - b = a + b := CharTwo.sub_eq_add a b

theorem add_eq_zero_iff_eq' {a b : E} : a + b = 0 ↔ a = b := by
  rw [← CharTwo.sub_eq_add, sub_eq_zero]

/-! ## Powers -/

theorem epowAux_eq : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, h => by
    have : n = 0 := by simpa using h
    simp [epowAux, this]
  | fuel + 1, base, out, n, h => by
    unfold epowAux
    split_ifs with h0 h1
    · simp [h0]
    · rw [epowAux_eq fuel _ _ _ (by rw [pow_succ] at h; omega), ← pow_two, ← pow_mul, mul_assoc,
        ← pow_succ']
      congr 2
      omega
    · rw [epowAux_eq fuel _ _ _ (by rw [pow_succ] at h; omega), ← pow_two, ← pow_mul]
      congr 2
      omega

/-- **Square and multiply is the power.** -/
theorem epow_eq (x : E) (n : ℕ) : epow x n = x ^ n := by
  rw [epow, epowAux_eq _ _ _ _ (Nat.lt_log2_self), one_mul]

/-- **`k` squarings are the `2^k`-th power.** -/
theorem sqn_eq : ∀ (x : E) (k : ℕ), sqn x k = x ^ 2 ^ k
  | x, 0 => by simp [sqn]
  | x, k + 1 => by
    rw [sqn, sqn_eq (x * x) k, ← pow_two, ← pow_mul, pow_succ']

theorem eK_eq (c : UInt64) : eK c = ofK (K.ofLane c) := by
  rw [ofK_eq_ofLimbs]
  rfl

theorem gen_eq : gen = ofK g := by
  rw [gen, eK_eq]
  rfl

/-! ## `K` -/

/-- Every `a : K` satisfies `a ^ 2 ^ 64 = a`. -/
theorem K.pow_two_pow_sixtyFour (a : K) : a ^ 2 ^ 64 = a := by
  have h := FiniteField.pow_card a
  -- `simp only`, not `rw`: a goal mentioning `Fintype.card K` makes the elaborator enumerate `K`.
  simp only [BF64.card_bf64] at h
  exact h


theorem K.eq_sum_bits (a : K) :
    a = ∑ i : Fin 64, if a.toBitVec.getLsbD i then g ^ (i : ℕ) else 0 := by
  apply BF64.toQuot_injective
  have hg : BF64.toQuot g = AdjoinRoot.root BF64.basePoly := by
    rw [BF64.toQuot, BF64.toPolyBF64, g, K.ofBits, BF64.toBitVec_ofBitVec,
      show BitVec.ofNat 64 2 = (1 <<< 1 : BitVec 64) by decide,
      BinaryField.toPoly_one_shiftLeft 1 (by norm_num), pow_one, AdjoinRoot.mk_X]
  have hsum : ∀ (s : Finset (Fin 64)) (f : Fin 64 → K),
      BF64.toQuot (∑ i ∈ s, f i) = ∑ i ∈ s, BF64.toQuot (f i) := fun s f ↦ by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BF64.toQuot_add, ih]
  rw [hsum]
  conv_lhs => rw [BF64.toQuot, BF64.toPolyBF64, BinaryField.toPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [BitVec.getLsb, BitVec.getLsbD]
  split
  · rw [map_pow, AdjoinRoot.mk_X, BF64.toQuot_npow, hg]
  · rw [map_zero, BF64.toQuot_zero]

/-- The embedding of a cell in `E` is its bits packed by the powers of `x`. -/
theorem ofK_eq_sum_cellBit (a : K) :
    ofK a = ∑ i : Fin (2 ^ Lv42.Parameters.Flock.kSkip), ofK (g ^ i.val) * Lv42.Protocol.cellBit a i := by
  conv_lhs => rw [K.eq_sum_bits a]
  change algebraMap K E _ = _
  rw [map_sum (algebraMap K E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Lv42.Protocol.cellBit]
  split <;> simp_all


/-! ## The loops as folds (Tower.lean) -/

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
  exact theta_K_not_fixed j hj (ofK_injective ((add_eq_zero_iff_eq'.mp h).symm))

theorem epow_gen_eq (i : ℕ) : epow gen i = ofK (gK ^ i) := by
  rw [epow_eq, gen_eq, ofK_pow']

/-- `x^i ∈ F_6 = K`. -/
theorem epow_gen_inF (i : ℕ) : InF 6 (epow gen i) := by
  rw [epow_gen_eq, InF, ← ofK_pow', show (2 : ℕ) ^ 2 ^ 6 = 2 ^ 64 by norm_num,
    K.pow_two_pow_sixtyFour]


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


end UniComplete.FlockP.Tower
