-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `Pi2TFresh.lean` (`t`'s freshness by counting
-- cached inputs that hold a fresh answer) and `formal/UniComplete/UniComplete/ProbTFresh.lean` (`CacheBound`,
-- `cacheBound_run`, `sum_hit_le`); uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls`, their lazy random oracles, the pure run `runAt`.
import RecCompose.Pi2TFresh

/-!
# `α`'s input is fresh: the chain from π2's `σ` hash

`α`'s input is the state after the seed, π1's public data and `W`'s root (`536` bytes, beginning with the seed's
`32`). Nothing before it is provably fresh by itself: π1-rec3's prover (stage A) hashes inputs of many lengths. But
π2's IV begins with the hash of `σ`'s `4 · 2^24 = 2^26` bytes, longer than anything hashed before it (`Pi2AlphaLen`),
so its answer is uniform; then each hash of π2's IV and seed holds the previous answer at a fixed offset:

`σd = H(σ)`, `κd = H(κ)`, `d = H(enc ‖ σd ‖ κd)` (`σd` at `25184`, `25248` bytes), `iv = H(… ‖ d ‖ …)` (`d` at `80`,
`208` bytes), `seed = H(name ‖ iv ‖ input)` (`iv` at `16`, `80` bytes), then `W`'s tree (no `536`-byte input) and
`α`'s input (`seed` at `0`, `536` bytes).

A query holding a fresh answer `u` at offset `o` is cached only if an input cached before `u` (at most `K + 4`) holds
`u` there: a uniform `u` does with probability at most `(K + 4) / 2^256` (**`sum_hitAt_le`**). Four links:

* **`chain_le`**: from a cache of at most `K` hashed inputs not holding `σ`'s, the chain's run caches a `536`-byte
  `α` input with probability at most `4 · (K + 4) / 2^256`.
* **`runAt_of_mem_support`**: an outcome of a run against the lazy oracles is the pure run at any functions extending
  its final cache (so the code's facts at pure functions hold on every outcome).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK cache_of_hashOK prEvent_fresh ro_run_fresh ro_run_cached length_digestBytes
  simulateQ_callKeccak256 runAt)
open UniComplete.Prob (prEvent_query_le sum_const_div)
open UniComplete.Prob.TFresh (CacheBound sum_hit_le)
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.Pi2C

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Hits -/

/-- **A hit at `u`**: a cached input of `L` bytes holds `u`'s bytes at offset `o`. -/
def HitAt (L o : ℕ) (c : Cache) (u : Digest) : Prop :=
  ∃ m, c (.inl m) ≠ none ∧ m.length = L ∧ (m.drop o).take 32 = digestBytes u

open Classical in
/-- **At most `K` answers are hit** by a cache of at most `K` hashed inputs. -/
theorem sum_hitAt_le (L o : ℕ) {c : Cache} {K : ℕ} (hc : CacheBound c K) :
    (∑ u : Digest, (if HitAt L o c u then 1 else 0 : ℝ≥0∞)) ≤ K := by
  obtain ⟨S, hS, hm⟩ := hc
  refine (sum_hit_le (S.image (List.drop o)) (HitAt L o c) fun u ⟨m, hmc, _, ht⟩ ↦
    ⟨m.drop o, Finset.mem_image_of_mem _ (hm m hmc), ht⟩).trans ?_
  exact_mod_cast Finset.card_image_le.trans hS

/-- A hash query, then a continuation, simulated. -/
theorem run_H_bind {γ : Type} (x : Bytes) (k : Digest → OracleComp KeccakCalls γ) (c : Cache) :
    (simulateQ ro (callKeccak256 x >>= k)).run c =
      (ro (.inl x)).run c >>= fun q ↦ (simulateQ ro (k q.1)).run q.2 := by
  rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind]
  rfl

theorem cacheQuery_of_eq (c : Cache) (x : Bytes) {v : Digest} (h : c (.inl x) = some v) :
    c.cacheQuery (.inl x) v = c := by
  refine QueryCache.ext fun t ↦ ?_
  by_cases ht : t = .inl x
  · subst ht
    rw [QueryCache.cacheQuery_self, h]
  · rw [QueryCache.cacheQuery_of_ne _ _ ht]

/-- **A query, fresh or not**: a bound on the continuation at every answer bounds the event. -/
theorem prEvent_query_any {δ : Type} (x : Bytes) (c : Cache) (K : Digest × Cache → ProbComp δ) (q : δ → Prop)
    (b : ℝ≥0∞) (hK : ∀ u, Pr{let z ← K (u, c.cacheQuery (.inl x) u)}[q z] ≤ b) :
    Pr{let z ← ((ro (.inl x)).run c >>= K)}[q z] ≤ b := by
  rcases hcx : c (.inl x) with _ | v
  · rw [prEvent_fresh _ _ hcx]
    calc (∑ u : Digest, Pr{let z ← K (u, c.cacheQuery (.inl x) u)}[q z]) / 2 ^ 256
        ≤ (∑ _u : Digest, b) / 2 ^ 256 := ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hK u) _
      _ = b := sum_const_div b
  · rw [ro_run_cached _ _ hcx, pure_bind]
    have h := hK v
    rwa [cacheQuery_of_eq c x hcx] at h

/-- A count of at most `K'` hits, averaged, is at most `(K + 4) / 2^256` for `K' ≤ K + 4`. -/
theorem avg_hit_le {K K' : ℕ} (h : K' ≤ K + 4) (S : ℝ≥0∞) (hS : S ≤ K') :
    S / 2 ^ 256 ≤ ((K + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  ENNReal.div_le_div_right (hS.trans (by exact_mod_cast h)) _

/-! ## The last link: `W`'s tree after a fresh seed -/

/-- **After the seed**: a computation `T` hashing nothing of `536` bytes whose `α` input, when of `536` bytes, begins
with the seed's: from the cache with the seed's query added, the input is cached only if a cached `536`-byte input began
with the seed (a hit). -/
theorem chain_last {β : Type} (xs : Bytes) (hxs : xs.length ≠ 536) (T : Digest → OracleComp KeccakCalls β)
    (inpOf : β → Bytes) (hT : ∀ s, HashOK (fun m ↦ m.length ≠ 536) (T s))
    (hTinp : ∀ s (c : Cache) (z : β × Cache), z ∈ support ((simulateQ ro (T s)).run c) →
      (inpOf z.1).length = 536 → (inpOf z.1).take 32 = digestBytes s) (c : Cache)
    (s : Digest) (hnh : ¬ HitAt 536 0 c s) :
    Pr{let z ← (simulateQ ro (T s)).run (c.cacheQuery (.inl xs) s)}[
      z.2 (.inl (inpOf z.1)) ≠ none ∧ (inpOf z.1).length = 536] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hev ↦ hnh ?_
  rcases cache_of_hashOK (hT s) _ hz _ hev.1 with h | h
  · have hne : (Sum.inl (inpOf z.1) : Bytes ⊕ KeccakState) ≠ .inl xs := fun e ↦
      hxs ((congrArg List.length (Sum.inl_injective e)).symm.trans hev.2)
    rw [QueryCache.cacheQuery_of_ne _ _ hne] at h
    exact ⟨_, h, hev.2, by rw [List.drop_zero]; exact hTinp s _ z hz hev.2⟩
  · exact absurd hev.2 h

/-! ## The chain -/

set_option maxHeartbeats 800000 in
/-- **The chain from `σ`**: from a cache of at most `K` hashed inputs not holding `σ`'s input, the run of `σ`'s, `κ`'s,
the digest's, the IV's and the seed's hashes (each later input holding the previous answer at its offset), then a
computation hashing nothing of `536` bytes whose `α` input of `536` bytes begins with the seed, caches that input with
probability at most `4 · (K + 4) / 2^256`. -/
theorem chain_le {β : Type} (xσ xκ : Bytes) (fd : Digest → Digest → Bytes) (fiv fs : Digest → Bytes)
    (hκ : xκ.length ≠ 25248) (hσ : xσ.length ≠ 25248)
    (hfd : ∀ σ κ, (fd σ κ).length = 25248 ∧ ((fd σ κ).drop 25184).take 32 = digestBytes σ)
    (hfiv : ∀ d, (fiv d).length = 208 ∧ ((fiv d).drop 80).take 32 = digestBytes d)
    (hfs : ∀ iv, (fs iv).length = 80 ∧ ((fs iv).drop 16).take 32 = digestBytes iv)
    (T : Digest → OracleComp KeccakCalls β) (inpOf : β → Bytes) (hT : ∀ s, HashOK (fun m ↦ m.length ≠ 536) (T s))
    (hTinp : ∀ s (c : Cache) (z : β × Cache), z ∈ support ((simulateQ ro (T s)).run c) →
      (inpOf z.1).length = 536 → (inpOf z.1).take 32 = digestBytes s)
    (c : Cache) {K : ℕ} (hc : CacheBound c K) (h0 : c (.inl xσ) = none) :
    Pr{let z ← (simulateQ ro (callKeccak256 xσ >>= fun σd ↦ callKeccak256 xκ >>= fun κd ↦
        callKeccak256 (fd σd κd) >>= fun d ↦ callKeccak256 (fiv d) >>= fun iv ↦
        callKeccak256 (fs iv) >>= T)).run c}[
      z.2 (.inl (inpOf z.1)) ≠ none ∧ (inpOf z.1).length = 536] ≤
      4 * (((K + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  classical
  set B : ℝ≥0∞ := ((K + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256
  rw [run_H_bind]
  -- `σ`: fresh; its answer is hit by the digest's length at most `K` times.
  refine (prEvent_query_le xσ c False (fun _ ↦ h0) _ _
    (fun σd ↦ (if HitAt 25248 25184 c σd then 1 else 0) + 3 * B) fun σd ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    calc _ ≤ B + 3 * B := add_le_add (avg_hit_le (by omega) _ (sum_hitAt_le _ _ hc)) le_rfl
      _ = 4 * B := by ring
  dsimp only
  rw [run_H_bind]
  -- `κ`: whatever its answer.
  refine prEvent_query_any xκ _ _ _ _ fun κd ↦ ?_
  dsimp only
  rw [run_H_bind]
  set c₂ := (c.cacheQuery (.inl xσ) σd).cacheQuery (.inl xκ) κd with hc₂
  have hc₂b : CacheBound c₂ (K + 2) := (hc.cacheQuery_inl _ _).cacheQuery_inl _ _
  -- the digest: fresh unless a cached `25248`-byte input held `σd`.
  refine (prEvent_query_le (fd σd κd) c₂ (HitAt 25248 25184 c σd) (fun hn ↦ ?_) _ _
    (fun d ↦ (if HitAt 208 80 c₂ d then 1 else 0) + 2 * B) fun d ↦ ?_).trans ?_
  · rcases hcd : c₂ (.inl (fd σd κd)) with _ | v
    · rfl
    · exfalso
      refine hn ⟨fd σd κd, ?_, (hfd σd κd).1, (hfd σd κd).2⟩
      have h1 : (Sum.inl (fd σd κd) : Bytes ⊕ KeccakState) ≠ .inl xκ := fun e ↦
        hκ ((congrArg List.length (Sum.inl_injective e)).symm.trans (hfd σd κd).1)
      have h2 : (Sum.inl (fd σd κd) : Bytes ⊕ KeccakState) ≠ .inl xσ := fun e ↦
        hσ ((congrArg List.length (Sum.inl_injective e)).symm.trans (hfd σd κd).1)
      rw [hc₂, QueryCache.cacheQuery_of_ne _ _ h1, QueryCache.cacheQuery_of_ne _ _ h2] at hcd
      rw [hcd]
      exact Option.some_ne_none _
  rotate_left
  · refine add_le_add le_rfl ?_
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    calc _ ≤ B + 2 * B := add_le_add (avg_hit_le (by omega) _ (sum_hitAt_le _ _ hc₂b)) le_rfl
      _ = 3 * B := by ring
  dsimp only
  rw [run_H_bind]
  set c₃ := c₂.cacheQuery (.inl (fd σd κd)) d with hc₃
  have hc₃b : CacheBound c₃ (K + 3) := hc₂b.cacheQuery_inl _ _
  -- the IV: fresh unless a cached `208`-byte input held `d`.
  refine (prEvent_query_le (fiv d) c₃ (HitAt 208 80 c₂ d) (fun hn ↦ ?_) _ _
    (fun iv ↦ (if HitAt 80 16 c₃ iv then 1 else 0) + B) fun iv ↦ ?_).trans ?_
  · rcases hcd : c₃ (.inl (fiv d)) with _ | v
    · rfl
    · exfalso
      refine hn ⟨fiv d, ?_, (hfiv d).1, (hfiv d).2⟩
      have h1 : (Sum.inl (fiv d) : Bytes ⊕ KeccakState) ≠ .inl (fd σd κd) := fun e ↦ by
        have := congrArg List.length (Sum.inl_injective e)
        rw [(hfiv d).1, (hfd σd κd).1] at this
        omega
      rw [hc₃, QueryCache.cacheQuery_of_ne _ _ h1] at hcd
      rw [hcd]
      exact Option.some_ne_none _
  rotate_left
  · refine add_le_add le_rfl ?_
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    calc _ ≤ B + B := add_le_add (avg_hit_le (by omega) _ (sum_hitAt_le _ _ hc₃b)) le_rfl
      _ = 2 * B := by ring
  dsimp only
  rw [run_H_bind]
  set c₄ := c₃.cacheQuery (.inl (fiv d)) iv with hc₄
  have hc₄b : CacheBound c₄ (K + 4) := hc₃b.cacheQuery_inl _ _
  -- the seed: fresh unless a cached `80`-byte input held `iv`; then `α`'s input is cached only at a hit.
  refine (prEvent_query_le (fs iv) c₄ (HitAt 80 16 c₃ iv) (fun hn ↦ ?_) _ _
    (fun s ↦ if HitAt 536 0 c₄ s then 1 else 0) fun s ↦ ?_).trans ?_
  · rcases hcd : c₄ (.inl (fs iv)) with _ | v
    · rfl
    · exfalso
      refine hn ⟨fs iv, ?_, (hfs iv).1, (hfs iv).2⟩
      have h1 : (Sum.inl (fs iv) : Bytes ⊕ KeccakState) ≠ .inl (fiv d) := fun e ↦ by
        have := congrArg List.length (Sum.inl_injective e)
        rw [(hfs iv).1, (hfiv d).1] at this
        omega
      rw [hc₄, QueryCache.cacheQuery_of_ne _ _ h1] at hcd
      rw [hcd]
      exact Option.some_ne_none _
  · by_cases hh : HitAt 536 0 c₄ s
    · simp only [hh, ↓reduceIte]
      exact prEvent_le_one _
    · simp only [hh, ↓reduceIte]
      exact le_of_eq (chain_last (fs iv) (by rw [(hfs iv).1]; omega) T inpOf hT hTinp c₄ s hh)
  · exact add_le_add le_rfl (avg_hit_le le_rfl _ (sum_hitAt_le _ _ hc₄b))

/-! ## Outcomes are pure runs -/

/-- `c` is extended by `c'`. -/
def CacheLE (c c' : Cache) : Prop := ∀ t v, c t = some v → c' t = some v

theorem CacheLE.trans {c c' c'' : Cache} (h : CacheLE c c') (h' : CacheLE c' c'') : CacheLE c c'' :=
  fun t v hv ↦ h' t v (h t v hv)

/-- **A query's outcome**: its answer is cached, and the cache only grows. -/
theorem ro_run_support {t : Bytes ⊕ KeccakState} {c : Cache} {q} (hq : q ∈ support ((ro t).run c)) :
    q.2 t = some q.1 ∧ CacheLE c q.2 := by
  rw [randomOracle.run_eq] at hq
  rcases h : c t with _ | v
  · simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hq
    obtain ⟨w, -, rfl⟩ := hq
    refine ⟨QueryCache.cacheQuery_self _ _ _, fun t' v' h' ↦ ?_⟩
    by_cases ht : t' = t
    · subst ht
      rw [h] at h'
      cases h'
    · rw [QueryCache.cacheQuery_of_ne _ _ ht]
      exact h'
  · simp only [h, support_pure, Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨h, fun _ _ h' ↦ h'⟩

/-- **The cache only grows along a run.** -/
theorem cacheLE_run {α : Type} (X : OracleComp KeccakCalls α) :
    ∀ (c : Cache) (z : α × Cache), z ∈ support ((simulateQ ro X).run c) → CacheLE c z.2 := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro c z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun _ _ h ↦ h
  | query_bind t k ih =>
    intro c z hz
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, OracleQuery.cont_query,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    exact (ro_run_support hq).2.trans (ih q.1 q.2 z hz)

/-- **An outcome is the pure run** at any hash function and permutation extending its final cache. -/
theorem runAt_of_mem_support {α : Type} (X : OracleComp KeccakCalls α) :
    ∀ (c : Cache) (z : α × Cache), z ∈ support ((simulateQ ro X).run c) →
      ∀ (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState),
        (∀ x v, z.2 (.inl x) = some v → Ht x = v) → (∀ s v, z.2 (.inr s) = some v → Ft s = v) →
        runAt Ht Ft X = z.1 := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro c z hz Ht Ft _ _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  | query_bind t k ih =>
    intro c z hz Ht Ft hH hF
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, OracleQuery.cont_query,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    have ht : z.2 t = some q.1 := cacheLE_run (k q.1) q.2 z hz t q.1 (ro_run_support hq).1
    have hans : LeanVM.Protocol.Compile.totalImpl Ht Ft t = q.1 := by
      rcases t with x | s
      · exact hH x q.1 ht
      · exact hF s q.1 ht
    unfold runAt
    rw [simulateQ_query_bind]
    show simulateQ (LeanVM.Protocol.Compile.totalImpl Ht Ft) (k (LeanVM.Protocol.Compile.totalImpl Ht Ft t)) = z.1
    rw [hans]
    exact ih q.1 q.2 z hz Ht Ft hH hF

/-- The functions reading a cache (`default` off it). -/
def readH (c : Cache) (x : Bytes) : Digest := (c (.inl x)).getD default

/-- The permutation reading a cache (`default` off it). -/
def readF (c : Cache) (s : KeccakState) : KeccakState := (c (.inr s)).getD default

/-- **An outcome is the pure run at its final cache's answers.** -/
theorem runAt_read {α : Type} {X : OracleComp KeccakCalls α} {c : Cache} {z : α × Cache}
    (hz : z ∈ support ((simulateQ ro X).run c)) : runAt (readH z.2) (readF z.2) X = z.1 :=
  runAt_of_mem_support X c z hz _ _ (fun x v h ↦ by simp [readH, h]) (fun s v h ↦ by simp [readF, h])

end RecCompose.Pi2C

/-- info: 'RecCompose.Pi2C.chain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2C.chain_le

/-- info: 'RecCompose.Pi2C.runAt_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2C.runAt_read
