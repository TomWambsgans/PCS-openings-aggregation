-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The potential follows leanerVM's birthday bound (`prEvent_cacheHasCollision_le`,
-- `lean_vm/LeanVM/Protocol/ToVCVio/Rom/Bounds.lean`, https://github.com/Verified-zkEVM/leanerVM,
-- commit 6175f1a0, MIT OR Apache-2.0), on its budgeted potentials (`Rom/Potential.lean`:
-- `IsBudgetedPotential`, `prEvent_run_randomOracle_le_of_budgeted`); the invariant of the logged
-- run follows `Coupling.lean`'s `consistent_run_loggedKC`.
import Compose.Final128Defs
import LeanVM.Protocol.ToVCVio.Rom.Potential

/-!
# A pair of Keccak-256 answers: at most `2 Q² / 2^256`

`PairTr tag tr` (`Final128Defs.lean`): two answers of the transcript, the first `tag` followed by
the second's first `32 − |tag|` bytes. For a 16-byte tag, a run of `Q` queries makes one with
probability at most `Q² / 2^256` (**`prEvent_pairTr_le_sq`**; **`prEvent_pairTr_le`** states
`2 Q² / 2^256`), so `prEvent_pairTr_expL_le` for the run with its whole transcript.

The proof is a budgeted potential on the lazily sampled oracle (leanerVM's
`prEvent_run_randomOracle_le_of_budgeted`), on the **set of Keccak-256 answer values** of the cache
(`ansV`, a finite set of 32-byte strings): with `W` that set, `k` the values starting with `tag`,
and `n` queries left,

  `Φ n = [a pair in W] + n k / 2^128 + n |W| / 2^256 + n² / 2^256` (`pairPot`, `potN`).

A fresh answer `u` makes a new pair as the first element (`u = tag ‖` the first 16 bytes of a value
of `W` or of itself: at most `|W| + 1` values of `2^256`) or as the second (`u`'s first 16 bytes are
the last 16 of a value of `W` starting with `tag`: at most `k · 2^128` values, `pairBad`,
`card_pairBad_le`); it raises `k` with probability `2^-128` and `|W|` by at most one. So the
expectation of `Φ n` after a fresh Keccak-256 query is at most `Φ (n + 1)` (exactly, on the bounds:
`sum_potN_le`); a Keccak-f query changes nothing. From the empty cache, `Φ Q ∅ = Q² / 2^256`.

The transcript's entries are the cache's answers on every outcome (`trIn_run_loggedKC`), so a pair
of the transcript is a pair of the cache's values (`pairV_of_trIn`).
-/

set_option linter.unusedSectionVars false
-- Membership in finsets of 32-byte strings needs deep recursion (as `ListChainU.lean`'s
-- `card_tag_le`), and the constructor-name linter runs out of it on these proofs.
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Pairs of values -/

section Values

variable (tag : List UInt8)

/-- **Two values, the first `tag ‖` the second's first `32 − |tag|` bytes.** -/
def PairV (W : Finset Bytes32) : Prop :=
  ∃ v ∈ W, ∃ v' ∈ W, v.toList = tag ++ v'.toList.take (32 - tag.length)

variable {tag} in
theorem PairV.mono {W W' : Finset Bytes32} (h : W ⊆ W') (hp : PairV tag W) : PairV tag W' := by
  obtain ⟨v, hv, v', hv', he⟩ := hp
  exact ⟨v, h hv, v', h hv', he⟩

/-- The values starting with `tag`. -/
def taggedV (W : Finset Bytes32) : Finset Bytes32 :=
  W.filter fun v => v.toList.take tag.length = tag

open Classical in
/-- **The fresh values that make a new pair with `W`**: as the first element (with a value of `W`
or itself), or as the second. -/
noncomputable def pairBad (W : Finset Bytes32) : Finset Bytes32 :=
  Finset.univ.filter fun u => (∃ v' ∈ W, u.toList = tag ++ v'.toList.take (32 - tag.length)) ∨
    u.toList = tag ++ u.toList.take (32 - tag.length) ∨
    ∃ v ∈ W, v.toList = tag ++ u.toList.take (32 - tag.length)

theorem mem_pairBad {W : Finset Bytes32} {u : Bytes32} :
    u ∈ pairBad tag W ↔ (∃ v' ∈ W, u.toList = tag ++ v'.toList.take (32 - tag.length)) ∨
      u.toList = tag ++ u.toList.take (32 - tag.length) ∨
      ∃ v ∈ W, v.toList = tag ++ u.toList.take (32 - tag.length) := by
  simp only [pairBad, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **A new pair needs a bad fresh value.** -/
theorem pairV_insert {W : Finset Bytes32} {u : Bytes32} (h : PairV tag (insert u W)) :
    PairV tag W ∨ u ∈ pairBad tag W := by
  obtain ⟨v, hv, v', hv', he⟩ := h
  rcases Finset.mem_insert.mp hv with hv | hv <;> rcases Finset.mem_insert.mp hv' with hv' | hv'
  · right
    rw [mem_pairBad]
    right
    left
    rw [hv, hv'] at he
    exact he
  · right
    rw [mem_pairBad]
    left
    rw [hv] at he
    exact ⟨v', hv', he⟩
  · right
    rw [mem_pairBad]
    right
    right
    rw [hv'] at he
    exact ⟨v, hv, he⟩
  · left
    exact ⟨v, hv, v', hv', he⟩

/-- **At most `|W| + 1 + k · 2^128` bad fresh values**, `k` the values of `W` starting with the
16-byte `tag`. -/
theorem card_pairBad_le (htag : tag.length = 16) (W : Finset Bytes32) :
    (pairBad tag W).card ≤ W.card + 1 + (taggedV tag W).card * 2 ^ 128 := by
  classical
  have hk : 32 - tag.length = tag.length := by omega
  let S1 := W.biUnion fun v' => Finset.univ.filter fun u : Bytes32 =>
    u.toList = tag ++ v'.toList.take (32 - tag.length)
  let S2 := Finset.univ.filter fun u : Bytes32 => u.toList = tag ++ u.toList.take (32 - tag.length)
  let S3 := (taggedV tag W).biUnion fun v => Finset.univ.filter fun u : Bytes32 =>
    u.toList.take (v.toList.drop tag.length).length = v.toList.drop tag.length
  have hsub : pairBad tag W ⊆ S1 ∪ S2 ∪ S3 := by
    intro u hu
    rcases (mem_pairBad tag).mp hu with ⟨v', hv', he⟩ | he | ⟨v, hv, he⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨v', hv', Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩))
    · have ht : v.toList.take tag.length = tag := by
        rw [he]
        exact List.take_left' rfl
      have hd : v.toList.drop tag.length = u.toList.take (32 - tag.length) := by
        rw [he]
        exact List.drop_left' rfl
      have hl : (u.toList.take (32 - tag.length)).length = 32 - tag.length := by
        simp only [List.length_take, Vector.length_toList]
        omega
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩)
      · exact Finset.mem_filter.mpr ⟨hv, ht⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hd, hl]
  have hS1 : S1.card ≤ W.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ v' ∈ W, (Finset.univ.filter fun u : Bytes32 =>
          u.toList = tag ++ v'.toList.take (32 - tag.length)).card
        ≤ ∑ _v' ∈ W, 1 := Finset.sum_le_sum fun v' _ => Finset.card_le_one.mpr fun a ha b hb =>
          Vector.toList_inj.mp ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
      _ = W.card := by simp
  have hS2 : S2.card ≤ 1 := by
    have key : ∀ x : Bytes32, x.toList = tag ++ x.toList.take (32 - tag.length) →
        x.toList = tag ++ tag := by
      intro x hx
      have h1 : x.toList.take tag.length = tag := by
        rw [hx]
        exact List.take_left' rfl
      have h2 : x.toList.take (32 - tag.length) = tag := by
        rw [hk]
        exact h1
      rw [h2] at hx
      exact hx
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    exact Vector.toList_inj.mp ((key a (Finset.mem_filter.mp ha).2).trans
      (key b (Finset.mem_filter.mp hb).2).symm)
  have hS3 : S3.card ≤ (taggedV tag W).card * 2 ^ 128 := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (2 ^ 128) fun v _ => ?_).trans (le_of_eq (smul_eq_mul _ _))
    have hl : (v.toList.drop tag.length).length = 16 := by
      simp [htag]
    refine (card_tag_le (v.toList.drop tag.length)).trans ?_
    rw [hl]
    norm_num
  calc (pairBad tag W).card ≤ (S1 ∪ S2 ∪ S3).card := Finset.card_le_card hsub
    _ ≤ S1.card + S2.card + S3.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ W.card + 1 + (taggedV tag W).card * 2 ^ 128 := Nat.add_le_add (Nat.add_le_add hS1 hS2) hS3

/-- At most `2^128` 32-byte strings start with the 16-byte `tag`. -/
theorem card_tagged_le (htag : tag.length = 16) :
    (Finset.univ.filter fun u : Bytes32 => u.toList.take tag.length = tag).card ≤ 2 ^ 128 := by
  refine (card_tag_le tag).trans (le_of_eq ?_)
  rw [htag]
  norm_num

theorem card_taggedV_insert_le (v : Bytes32) (W : Finset Bytes32) :
    (taggedV tag (insert v W)).card ≤
      (taggedV tag W).card + (if v.toList.take tag.length = tag then 1 else 0) := by
  unfold taggedV
  rw [Finset.filter_insert]
  by_cases a : v.toList.take tag.length = tag
  · simp only [a, ite_true]
    exact Finset.card_insert_le _ _
  · simp only [a, ite_false, Nat.add_zero, le_refl]

open Classical in
/-- `1` if the values make a pair, `0` otherwise. -/
noncomputable def pairInd (W : Finset Bytes32) : ℕ := if PairV tag W then 1 else 0

theorem pairInd_of {W : Finset Bytes32} (h : PairV tag W) : pairInd tag W = 1 := by
  unfold pairInd
  simp only [h, ite_true]

theorem pairInd_empty : pairInd tag ∅ = 0 := by
  have h : ¬ PairV tag ∅ := by
    rintro ⟨v, hv, -⟩
    simp at hv
  unfold pairInd
  simp only [h, ite_false]

theorem pairInd_mono {W W' : Finset Bytes32} (h : W ⊆ W') : pairInd tag W ≤ pairInd tag W' := by
  unfold pairInd
  by_cases a : PairV tag W
  · simp only [a, a.mono h, ite_true, le_refl]
  · simp only [a, ite_false]
    exact Nat.zero_le _

theorem pairInd_insert_le (v : Bytes32) (W : Finset Bytes32) :
    pairInd tag (insert v W) ≤ pairInd tag W + (if v ∈ pairBad tag W then 1 else 0) := by
  by_cases a : PairV tag (insert v W)
  · rw [pairInd_of tag a]
    rcases pairV_insert tag a with b | b
    · rw [pairInd_of tag b]
      exact Nat.le_add_right _ _
    · simp only [b, ite_true]
      exact Nat.le_add_left _ _
  · unfold pairInd
    simp only [a, ite_false]
    exact Nat.zero_le _

/-- **The potential's numerator**, over `2^256`: `2^256 [pair] + n k 2^128 + n |W| + n²`. -/
noncomputable def potN (n : ℕ) (W : Finset Bytes32) : ℕ :=
  2 ^ 256 * pairInd tag W + n * (taggedV tag W).card * 2 ^ 128 + n * W.card + n ^ 2

theorem potN_mono (n : ℕ) {W W' : Finset Bytes32} (h : W ⊆ W') : potN tag n W ≤ potN tag n W' := by
  unfold potN
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul_left _ (pairInd_mono tag h))
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (Finset.card_le_card (Finset.filter_subset_filter _ h)))))
    (Nat.mul_le_mul_left _ (Finset.card_le_card h))) le_rfl

theorem potN_le_succ (n : ℕ) (W : Finset Bytes32) : potN tag n W ≤ potN tag (n + 1) W := by
  unfold potN
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ n))))
    (Nat.mul_le_mul_right _ (Nat.le_succ n))) (Nat.pow_le_pow_left (Nat.le_succ n) 2)

/-- **The supermartingale step, on the values**: the sum over the fresh value of the potential
with `n` queries left is at most `2^256` times the potential with `n + 1` left. -/
theorem sum_potN_le (htag : tag.length = 16) (n : ℕ) (W : Finset Bytes32) :
    ∑ v : Bytes32, potN tag n (insert v W) ≤ 2 ^ 256 * potN tag (n + 1) W := by
  have hpt : ∀ v : Bytes32, potN tag n (insert v W) ≤
      (2 ^ 256 * pairInd tag W + n * (taggedV tag W).card * 2 ^ 128 + n * (W.card + 1) + n ^ 2) +
        2 ^ 256 * (if v ∈ pairBad tag W then 1 else 0) +
        n * 2 ^ 128 * (if v.toList.take tag.length = tag then 1 else 0) := by
    intro v
    have h1 := pairInd_insert_le tag v W
    have h2 := card_taggedV_insert_le tag v W
    have h3 : (insert v W).card ≤ W.card + 1 := Finset.card_insert_le _ _
    calc potN tag n (insert v W)
        ≤ 2 ^ 256 * (pairInd tag W + (if v ∈ pairBad tag W then 1 else 0)) +
            n * ((taggedV tag W).card + (if v.toList.take tag.length = tag then 1 else 0)) *
              2 ^ 128 + n * (W.card + 1) + n ^ 2 :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h1)
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2))) (Nat.mul_le_mul_left _ h3))
            le_rfl
      _ = _ := by ring
  have hB := card_pairBad_le tag htag W
  have hT := card_tagged_le tag htag
  calc ∑ v : Bytes32, potN tag n (insert v W)
      ≤ ∑ v : Bytes32, ((2 ^ 256 * pairInd tag W + n * (taggedV tag W).card * 2 ^ 128 +
          n * (W.card + 1) + n ^ 2) + 2 ^ 256 * (if v ∈ pairBad tag W then 1 else 0) +
          n * 2 ^ 128 * (if v.toList.take tag.length = tag then 1 else 0)) :=
        Finset.sum_le_sum fun v _ => hpt v
    _ = 2 ^ 256 * (2 ^ 256 * pairInd tag W + n * (taggedV tag W).card * 2 ^ 128 +
          n * (W.card + 1) + n ^ 2) + 2 ^ 256 * (pairBad tag W).card +
          n * 2 ^ 128 *
            (Finset.univ.filter fun u : Bytes32 => u.toList.take tag.length = tag).card := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          card_bytes32, smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.card_filter,
          ← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ ≤ 2 ^ 256 * (2 ^ 256 * pairInd tag W + n * (taggedV tag W).card * 2 ^ 128 +
          n * (W.card + 1) + n ^ 2) + 2 ^ 256 * (W.card + 1 + (taggedV tag W).card * 2 ^ 128) +
          n * 2 ^ 128 * 2 ^ 128 :=
        Nat.add_le_add (Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ hB))
          (Nat.mul_le_mul_left _ hT)
    _ = 2 ^ 256 * potN tag (n + 1) W := by
        unfold potN
        ring

end Values

/-! ## The potential on the oracle's cache -/

section Cache

open Classical in
/-- **The Keccak-256 answer values a cache holds**, as 32 bytes. -/
noncomputable def ansV (c : KeccakCalls.QueryCache) : Finset Bytes32 :=
  Finset.univ.filter fun v => ∃ (x : List UInt8) (d : Digest), c (.inl x) = some d ∧ toB d = v

theorem mem_ansV {c : KeccakCalls.QueryCache} {v : Bytes32} :
    v ∈ ansV c ↔ ∃ (x : List UInt8) (d : Digest), c (.inl x) = some d ∧ toB d = v := by
  simp only [ansV, Finset.mem_filter, Finset.mem_univ, true_and]

theorem ansV_empty : ansV (∅ : KeccakCalls.QueryCache) = ∅ := by
  ext v
  rw [mem_ansV]
  simp

theorem ansV_cacheQuery_inl (c : KeccakCalls.QueryCache) (x : List UInt8)
    (hc : c (.inl x) = none) (u : KeccakCalls.Range (.inl x)) :
    ansV (c.cacheQuery (.inl x) u) ⊆ insert (toB u) (ansV c) := by
  intro v hv
  obtain ⟨y, d, hyd, hdv⟩ := mem_ansV.mp hv
  rw [Finset.mem_insert]
  by_cases hyx : y = x
  · subst hyx
    rw [QueryCache.cacheQuery_self] at hyd
    left
    rw [← hdv, ← Option.some.inj hyd]
  · right
    rw [QueryCache.cacheQuery_of_ne (t' := Sum.inl y) (t := Sum.inl x) c u
      (by simpa using hyx)] at hyd
    exact mem_ansV.mpr ⟨y, d, hyd, hdv⟩

theorem ansV_cacheQuery_inr (c : KeccakCalls.QueryCache) (s : KeccakState)
    (u : KeccakCalls.Range (.inr s)) : ansV (c.cacheQuery (.inr s) u) ⊆ ansV c := by
  intro v hv
  obtain ⟨y, d, hyd, hdv⟩ := mem_ansV.mp hv
  rw [QueryCache.cacheQuery_of_ne (t' := Sum.inl y) (t := Sum.inr s) c u Sum.inl_ne_inr] at hyd
  exact mem_ansV.mpr ⟨y, d, hyd, hdv⟩

/-- **The potential**: `potN` of the cache's values, over `2^256`. -/
noncomputable def pairPot (tag : List UInt8) (n : ℕ) (c : KeccakCalls.QueryCache) : ℝ≥0∞ :=
  (potN tag n (ansV c) : ℝ≥0∞) / 2 ^ 256

/-- Averaging over a type of `2^256` elements a function bounded by `g / 2^256`. -/
theorem avg_le_of_equiv {R : Type} [Fintype R] (e : R ≃ Bytes32) (f : R → ℝ≥0∞)
    (g : Bytes32 → ℕ) (hf : ∀ u, f u ≤ (g (e u) : ℝ≥0∞) / 2 ^ 256) (N : ℕ)
    (hg : ∑ v, g v ≤ 2 ^ 256 * N) :
    (∑ u, f u) / (Fintype.card R : ℝ≥0∞) ≤ (N : ℝ≥0∞) / 2 ^ 256 := by
  have hcard : (Fintype.card R : ℝ≥0∞) = 2 ^ 256 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_eq_fintype_card, card_bytes32,
      Nat.cast_pow, Nat.cast_ofNat]
  have h1 : ∑ u, f u ≤ ((∑ v, g v : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    calc ∑ u, f u ≤ ∑ u, (g (e u) : ℝ≥0∞) / 2 ^ 256 := Finset.sum_le_sum fun u _ => hf u
      _ = ∑ v, (g v : ℝ≥0∞) / 2 ^ 256 := Equiv.sum_comp e (fun v => (g v : ℝ≥0∞) / 2 ^ 256)
      _ = ((∑ v, g v : ℕ) : ℝ≥0∞) / 2 ^ 256 := by rw [Nat.cast_sum, ENNReal.sum_div]
  rw [hcard]
  refine (ENNReal.div_le_div_right h1 _).trans (ENNReal.div_le_div_right ?_ _)
  refine ENNReal.div_le_of_le_mul ?_
  have h2 : ((∑ v, g v : ℕ) : ℝ≥0∞) ≤ ((2 ^ 256 * N : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr hg
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] at h2
  exact h2

/-- Averaging a function bounded by `a`. -/
theorem avg_le_const {R : Type} [Fintype R] (f : R → ℝ≥0∞) (a : ℝ≥0∞) (hf : ∀ u, f u ≤ a) :
    (∑ u, f u) / (Fintype.card R : ℝ≥0∞) ≤ a := by
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ u, f u ≤ ∑ _u : R, a := Finset.sum_le_sum fun u _ => hf u
    _ = a * Fintype.card R := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **`pairPot` is a budgeted potential of the lazily sampled oracle**, for a 16-byte tag. -/
theorem isBudgetedPotential_pairPot (tag : List UInt8) (htag : tag.length = 16) :
    LeanVM.Protocol.Rom.IsBudgetedPotential (spec := KeccakCalls) (pairPot tag) where
  mono n c := ENNReal.div_le_div_right (Nat.cast_le.mpr (potN_le_succ tag n _)) _
  fresh n c t hc := by
    cases t with
    | inl x =>
      exact avg_le_of_equiv LeanVM.Rpm.digestEquiv _
        (fun v => potN tag n (insert v (ansV c)))
        (fun u => ENNReal.div_le_div_right (Nat.cast_le.mpr
          (potN_mono tag n (ansV_cacheQuery_inl c x hc u))) _)
        _ (sum_potN_le tag htag n (ansV c))
    | inr s =>
      exact avg_le_const _ _ fun u => ENNReal.div_le_div_right (Nat.cast_le.mpr
        ((potN_mono tag n (ansV_cacheQuery_inr c s u)).trans (potN_le_succ tag n _))) _

end Cache

/-! ## The transcript's answers are the cache's -/

section Log

/-- Every entry of the transcript is a Keccak-256 answer of the cache. -/
def TrIn (tr : Transcript) (c : KeccakCalls.QueryCache) : Prop :=
  ∀ e ∈ tr, ∃ d : Digest, c (.inl e.1) = some d ∧ toB d = e.2

/-- One query keeps the transcript's entries the cache's answers. -/
theorem trIn_step {tr : Transcript} {c : KeccakCalls.QueryCache} (hc : TrIn tr c)
    (t : List UInt8 ⊕ KeccakState) (u : KeccakCalls t) {c' : KeccakCalls.QueryCache}
    (hc' : (c t = some u ∧ c' = c) ∨ (c t = none ∧ c' = c.cacheQuery t u)) :
    TrIn (tr ++ (inlEntry ⟨t, u⟩).toList) c' := by
  cases t with
  | inr s =>
    intro e he
    have he' : e ∈ tr := by simpa [inlEntry] using he
    obtain ⟨d, hd, hde⟩ := hc e he'
    refine ⟨d, ?_, hde⟩
    rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hd
    · rw [QueryCache.cacheQuery_of_ne _ _ Sum.inl_ne_inr]
      exact hd
  | inl x =>
    have hle : ∀ (y : List UInt8) (d : Digest), c (.inl y) = some d → c' (.inl y) = some d := by
      intro y d hy
      rcases hc' with ⟨-, rfl⟩ | ⟨hn, rfl⟩
      · exact hy
      · by_cases hyx : y = x
        · subst hyx
          rw [hn] at hy
          simp at hy
        · rw [QueryCache.cacheQuery_of_ne (t' := Sum.inl y) (t := Sum.inl x) c u
            (by simpa using hyx)]
          exact hy
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨d, hd, hde⟩ := hc e he
      exact ⟨d, hle _ _ hd, hde⟩
    · simp only [inlEntry, Option.toList_some, List.mem_singleton] at he
      subst he
      refine ⟨u, ?_, rfl⟩
      rcases hc' with ⟨h, rfl⟩ | ⟨-, rfl⟩
      · exact h
      · exact QueryCache.cacheQuery_self _ _ _

/-- **On every outcome of the logged run, the transcript's entries are the cache's answers**,
when they were so at the start. -/
theorem trIn_run_loggedKC {α : Type} (v : OracleComp KeccakCalls α) :
    ∀ (tr : Transcript) (c : KeccakCalls.QueryCache), TrIn tr c →
      ∀ z ∈ support ((simulateQ randomOracle ((simulateQ logImplKC v).run tr)).run c),
        TrIn z.1.2 z.2 := by
  induction v using OracleComp.inductionOn with
  | pure a =>
    intro tr c hc z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hc
  | query_bind t k ih =>
    intro tr c hc z hz
    rw [loggedKC_run_query_bind, LeanVM.Protocol.Rom.run_simulateQ_bind,
      simulateQ_spec_query, randomOracle.run_eq] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    cases hct : c t with
    | some u =>
      rw [hct] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ih u _ _ (trIn_step hc t u (Or.inl ⟨hct, rfl⟩)) z hz
    | none =>
      rw [hct] at hp
      rw [mem_support_bind_iff] at hp
      obtain ⟨u, -, hu⟩ := hp
      simp only [support_pure, Set.mem_singleton_iff] at hu
      subst hu
      exact ih u _ _ (trIn_step hc t u (Or.inr ⟨hct, rfl⟩)) z hz

/-- A pair of the transcript is a pair of the cache's values. -/
theorem pairV_of_trIn (tag : List UInt8) {tr : Transcript} {c : KeccakCalls.QueryCache}
    (hc : TrIn tr c) (h : PairTr tag tr) : PairV tag (ansV c) := by
  obtain ⟨e, he, e', he', hee⟩ := h
  obtain ⟨d, hd, hde⟩ := hc e he
  obtain ⟨d', hd', hde'⟩ := hc e' he'
  exact ⟨e.2, mem_ansV.mpr ⟨e.1, d, hd, hde⟩, e'.2, mem_ansV.mpr ⟨e'.1, d', hd', hde'⟩, hee⟩

end Log

/-! ## The bound -/

/-- **A pair of answers in the transcript of a run of `Q` queries: at most `Q² / 2^256`.** -/
theorem prEvent_pairTr_le_sq {α : Type} (X : OracleComp KeccakCalls α) (Q : ℕ)
    (hQ : IsTotalQueryBound X Q) (tag : List UInt8) (htag : tag.length = 16) :
    Pr{let z ← (simulateQ randomOracle ((simulateQ logImplKC X).run [])).run' ∅}[PairTr tag z.2] ≤
      ((Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hYQ := isTotalQueryBound_loggedKC_run X Q [] hQ
  rw [StateT.run'_eq, prEvent_map]
  refine (prEvent_mono_of_support _ _ (fun w => PairV tag (ansV w.2)) fun w hw h =>
    pairV_of_trIn tag (trIn_run_loggedKC X [] ∅ (fun e he => by simp at he) w hw) h).trans ?_
  refine (LeanVM.Protocol.Rom.prEvent_run_randomOracle_le_of_budgeted
    (isBudgetedPotential_pairPot tag htag) _ Q hYQ ∅ (fun _ c => PairV tag (ansV c))
    fun z _ hz => ?_).trans (le_of_eq ?_)
  · have h0 : potN tag 0 (ansV z.2) = 2 ^ 256 := by
      simp [potN, pairInd_of tag hz]
    have h1 : pairPot tag 0 z.2 = 1 := by
      rw [pairPot, h0, Nat.cast_pow, Nat.cast_ofNat]
      exact ENNReal.div_self (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    exact le_of_eq h1.symm
  · have h0 : potN tag Q (ansV (∅ : KeccakCalls.QueryCache)) = Q ^ 2 := by
      rw [ansV_empty]
      simp [potN, pairInd_empty, taggedV]
    rw [pairPot, h0]

/-- **A pair of answers in the transcript of a run of `Q` queries: at most `2 Q² / 2^256`**
(`prEvent_pairTr_le_sq` proves `Q² / 2^256`). -/
theorem prEvent_pairTr_le {α : Type} (X : OracleComp KeccakCalls α) (Q : ℕ)
    (hQ : IsTotalQueryBound X Q) (tag : List UInt8) (htag : tag.length = 16) :
    Pr{let z ← (simulateQ randomOracle ((simulateQ logImplKC X).run [])).run' ∅}[PairTr tag z.2] ≤
      ((2 * Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  (prEvent_pairTr_le_sq X Q hQ tag htag).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _)

private theorem isTotalQueryBound_opsRun_seed {F St M Pf : Type} [SampleableType F]
    (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)),
      IsTotalQueryBound (opsRun view ops π ch) (ops.map fun o => o.S.QO).sum
  | [], _, _ => trivial
  | o :: os, π, ch => by
    simp only [opsRun, List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind (o.S.queries _) fun _ =>
      (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_opsRun_seed view os π ch)

/-- **A pair of answers in the whole run's transcript** (`expL`, its queries `QX + Σ_k QO_k`):
at most `2 (QX + Σ_k QO_k)² / 2^256`. -/
theorem prEvent_pairTr_expL_le {F St M Pf : Type} [SampleableType F]
    (view : Pf → St × List (RMsg F)) (X : OracleComp KeccakCalls (PreK Pf F))
    (ops : List (WhirOp Pf F M)) (QX : ℕ) (hX : IsTotalQueryBound X QX) (tag : List UInt8)
    (htag : tag.length = 16) :
    Pr{let z ← (simulateQ randomOracle (expL view X ops)).run' ∅}[PairTr tag z.2] ≤
      ((2 * (QX + (ops.map fun o => o.S.QO).sum) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold expL
  exact prEvent_pairTr_le _ _ (isTotalQueryBound_bind hX fun x =>
    (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_opsRun_seed view ops x.1 x.2.1))
    tag htag

end Compose

/-- info: 'Compose.prEvent_pairTr_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_pairTr_le_sq

/-- info: 'Compose.prEvent_pairTr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_pairTr_le

/-- info: 'Compose.prEvent_pairTr_expL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_pairTr_expL_le
