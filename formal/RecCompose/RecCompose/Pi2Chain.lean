-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Generalizes `Pi2Prob.lean`'s `prEvent_staged3_triple_le`
-- (itself following `formal/UniComplete/UniComplete/ProbChain.lean`), with `ProbTFresh.lean`'s counting of hashed
-- inputs (`HC`, `hc_of_qc`, `CacheBound`, `cacheBound_run`, `sum_hit_le`); uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, their lazy random oracles, `rpmError`, `DuplexVm`, `hashBlocks`, `Common.QueryCostAtMost.of_bind`.
import RecCompose.Pi2P1
import Common.Rerun

/-!
# π2's chain `α, β, γ` when stage A hashes `32`-byte inputs

**The finding.** `Pi2Staged.Holds.hashA` asks stage A (π2's experiment up to `α`'s query) to hash nothing of `32`
(or `536`) bytes (`HashOK (GoodL 536)`), and `Pi2ProbStaged`'s named `Pi2HashBeforeAlpha` states it of `pi2Staged`.
**At π1-rec3's honest prover it is false**: stage A runs π1-rec3's prover (`p1k`), whose second bus answer is
`s₂ = H(s₁)` on `s₁`'s `32` bytes (`UniComplete.Rec3.staged2`). So `α`'s chain is restated here without it:

* **`prEvent_staged3_triple_le2`**: for a computation of the chain's shape (`staged3`) whose stage A makes at most
  `KA` Keccak-256 queries (`HC`), from a cache of at most `K₀` hashed inputs, the first input of length `L ≠ 32`, if
  `α`'s input is already cached after A with probability at most `εα`, the triple lands in a bad set of at most
  `M · |E|²` with probability at most `εα + (2K + 1) / 2^256 + M / 2^192`, `K = K₀ + KA`: `s₂`'s input (`s₁`'s
  bytes) is cached only if one of the `K` cached inputs is `s₁`'s bytes, `s₃`'s only if `s₂ = s₁` or one is `s₂`'s
  (at `K = 0` and `εα = 0`, `prEvent_staged3_triple_le`'s `1 / 2^256 + M / 2^192`).
* **`Pi2Staged.Holds2`**: `Holds` with `hashA` replaced by **`alphaFresh`** (`α`'s input cached after A from the
  empty cache with probability at most `εα`); every other field is `Holds`' (`experiment`, `duplex`, `cost`, `L_ne`,
  `inp_length`, `badCard`, `badTCard`, `tFresh`, `rejectGood`). `Holds.toHolds2` (at `εα = 0`, through
  `HashOK (GoodL L)`).
* **`recCompleteness2_of_staged2`**: `RecCompleteness2 D P1 P2 (deltaStaged2 M ct N εα εt εpow)`,
  `deltaStaged2 = (εα + (2N + 1) / 2^256 + M / 2^192) + (εt + ct / 2^192) + εpow + rpmError N` (stage A's hashed
  inputs bounded by the run's `N` block calls, `hc_of_qc`).
* **`delta2'`**, **`delta2'_le`**: π2's numbers (`M = 2^25 + 36`, `ct = 2^27`); below `2^-164` at `N ≤ 2^50`,
  `εα, εt ≤ 2^-200`, `εpow ≤ 2^-300`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK cache_of_hashOK prEvent_fresh prEvent_final_le Regular length_digestBytes
  simulateQ_callKeccak256)
open UniComplete.Prob (GoodL prEvent_query_le sum_const_div sum_mem_le)
open UniComplete.Prob.TFresh (HC hc_of_qc CacheBound cacheBound_empty cacheBound_run sum_hit_le take_digestBytes')
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.Pi2P

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Counting -/

/-- **The digests whose bytes are a cached input**: at most the cache's count. -/
theorem sum_cached_le {c : Cache} {K : ℕ} (hc : CacheBound c K) :
    (∑ u : Digest, (if c (.inl (digestBytes u)) ≠ none then 1 else 0 : ℝ≥0∞)) ≤ K := by
  classical
  obtain ⟨L, hL, hm⟩ := hc
  refine (sum_hit_le L (fun u ↦ c (.inl (digestBytes u)) ≠ none) fun u hu ↦
    ⟨digestBytes u, hm _ hu, take_digestBytes' u⟩).trans ?_
  exact_mod_cast hL

theorem ite_or_le (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∨ Q then (1 : ℝ≥0∞) else 0) ≤ (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-! ## The chain -/

set_option exponentiation.threshold 1024 in
/-- **`α, β, γ` in the random-oracle model, stage A hashing anything** (`prEvent_staged3_triple_le` without
`HashOK (GoodL L)`): stage A of at most `KA` Keccak-256 queries, from a cache of at most `K₀` hashed inputs, `α`'s
input (`L ≠ 32` bytes) cached after A with probability at most `εα`; bad sets of at most `M · |E|²` triples. -/
theorem prEvent_staged3_triple_le2 {α ρ γ : Type} (chal : Digest → E) (hreg : Regular chal) {L : ℕ} (hL : L ≠ 32)
    (Bad : ρ → Finset (E × E × E)) (M : ℕ) (hM : ∀ p, (Bad p).card ≤ M * 2 ^ 384)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = L) (pr : α → ρ) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → OracleComp KeccakCalls γ) {KA K₀ : ℕ} (hA : HC A KA) (c₀ : Cache)
    (hc₀ : CacheBound c₀ K₀) (εα : ℝ≥0∞)
    (hα : Pr{let p ← (simulateQ ro A).run c₀}[p.2 (.inl (inp p.1)) ≠ none] ≤ εα) :
    Pr{let z ← (simulateQ ro (staged3 chal inp pr A C)).run c₀}[z.1.2.2 ∈ Bad z.1.2.1] ≤
      εα + (((2 * (K₀ + KA) + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) := by
  classical
  rw [run_staged3]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun p ↦ p.2 (.inl (inp p.1)) ≠ none) _
    fun p hp hpα ↦ ?_).trans (add_le_add hα le_rfl)
  have hfα : p.2 (.inl (inp p.1)) = none := not_not.mp hpα
  have hcp : CacheBound p.2 (K₀ + KA) := cacheBound_run hA hc₀ hp
  set K := K₀ + KA with hK
  set c := p.2 with hc
  set T := Bad (pr p.1) with hT
  set I : Digest → Digest → Digest → ℝ≥0∞ := fun s₁ s₂ s₃ ↦ if (chal s₁, chal s₂, chal s₃) ∈ T then 1 else 0
    with hI
  -- a state's bytes are never `α`'s input
  have hne : ∀ s : Digest, (Sum.inl (digestBytes s) : Bytes ⊕ KeccakState) ≠ .inl (inp p.1) := fun s h ↦
    hL ((hinp p.1).symm.trans (by rw [← Sum.inl_injective h, length_digestBytes]))
  -- `s₁`: fresh.
  refine (prEvent_query_le _ _ False (fun _ ↦ hfα) _ _
    (fun s₁ ↦ (if c (.inl (digestBytes s₁)) ≠ none then 1 else 0) +
      (((K + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (∑ s₂ : Digest, ∑ s₃ : Digest, I s₁ s₂ s₃) / 2 ^ 256 / 2 ^ 256))
    fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    have h1 : (∑ u : Digest, (if c (.inl (digestBytes u)) ≠ none then 1 else 0 : ℝ≥0∞)) / 2 ^ 256 ≤
        (K : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (sum_cached_le hcp) _
    have h2 : (∑ s₁ : Digest, (∑ s₂ : Digest, ∑ s₃ : Digest, I s₁ s₂ s₃) / 2 ^ 256 / 2 ^ 256) / 2 ^ 256 ≤
        (M : ℝ≥0∞) / 2 ^ 192 := by
      rw [← ENNReal.sum_div, ← ENNReal.sum_div]
      refine ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul ?_))
      have e : (M : ℝ≥0∞) / 2 ^ 192 * 2 ^ 256 * 2 ^ 256 * 2 ^ 256 = 2 ^ 192 * ((M : ℝ≥0∞) * 2 ^ 384) := by
        rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add,
          show (2 : ℝ≥0∞) ^ (256 + (256 + 256)) = 2 ^ 192 * (2 ^ 192 * 2 ^ 384) by rw [← pow_add, ← pow_add],
          ← mul_assoc, ENNReal.div_mul_cancel (by simp) (by simp)]
        ring
      rw [e]
      refine (sum_triples_le chal hreg T).trans ?_
      gcongr
      exact_mod_cast hM (pr p.1)
    calc _ ≤ (K : ℝ≥0∞) / 2 ^ 256 + (((K + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) :=
          add_le_add h1 (add_le_add le_rfl h2)
      _ = _ := by
          rw [← add_assoc, ← ENNReal.add_div]
          congr 2
          push_cast
          ring
  -- `s₂`: fresh unless `s₁`'s bytes were cached.
  refine (prEvent_query_le _ _ (c (.inl (digestBytes s₁)) ≠ none)
    (fun hs ↦ by rw [QueryCache.cacheQuery_of_ne _ _ (hne s₁)]; exact not_not.mp hs) _ _
    (fun s₂ ↦ (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0) +
      (∑ s₃ : Digest, I s₁ s₂ s₃) / 2 ^ 256) fun s₂ ↦ ?_).trans ?_
  rotate_left
  · refine add_le_add le_rfl ?_
    rw [Finset.sum_add_distrib, ENNReal.add_div, ← ENNReal.sum_div]
    refine add_le_add (ENNReal.div_le_div_right ?_ _) le_rfl
    calc (∑ s₂ : Digest, (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0 : ℝ≥0∞))
        ≤ ∑ s₂ : Digest, ((if s₂ ∈ [s₁] then 1 else 0) + (if c (.inl (digestBytes s₂)) ≠ none then 1 else 0)) :=
          Finset.sum_le_sum fun s₂ _ ↦ by
            simpa only [List.mem_singleton] using ite_or_le (s₂ = s₁) (c (.inl (digestBytes s₂)) ≠ none)
      _ ≤ (([s₁].length : ℕ) : ℝ≥0∞) + K := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (sum_mem_le _) (sum_cached_le hcp)
      _ = ((K + 1 : ℕ) : ℝ≥0∞) := by simp only [List.length_singleton, Nat.cast_one]; push_cast; ring
  -- `s₃`: fresh unless `s₂ = s₁` or `s₂`'s bytes were cached.
  refine (prEvent_query_le _ _ (s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none) (fun hs ↦ ?_) _ _
    (fun s₃ ↦ I s₁ s₂ s₃) fun s₃ ↦ ?_).trans le_rfl
  · rw [not_or] at hs
    have h12 : (Sum.inl (digestBytes s₂) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₁) := fun h ↦
      hs.1 (E2ECompleteness.digestBytes_injective (Sum.inl_injective h))
    rw [QueryCache.cacheQuery_of_ne _ _ h12, QueryCache.cacheQuery_of_ne _ _ (hne s₂)]
    exact not_not.mp hs.2
  exact prEvent_final_le _ (pr p.1, chal s₁, chal s₂, chal s₃) (fun v ↦ v.2 ∈ Bad v.1)

/-! ## The staged experiment, `α`'s input fresh but with probability `εα` -/

/-- **The code-level bridge without `hashA`**: `Pi2Staged.Holds`' fields but `hashA`, replaced by `alphaFresh`
(`α`'s input already hashed after stage A with probability at most `εα`). -/
structure Pi2Staged.Holds2 (S : Pi2Staged) (D : RecStatement.RecDeployment) (P1 : RecStatement.Pi1Prover D)
    (P2 : RecStatement.Pi2Prover) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (L : ℕ) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop) (M ct N : ℕ) (εα εt εpow : ℝ≥0∞) : Prop where
  /-- (as `Holds`) The experiment's event is at most the two-call run's against the random permutation. -/
  experiment : Pr{let v ← RecStatement.recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = true ∧ v.2 = false] ≤
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1.1 = true ∧ z.1.1.2 = false]
  /-- (as `Holds`) The duplex discipline. -/
  duplex : DuplexVm S.run []
  /-- (as `Holds`) At most `N` block calls. -/
  cost : Common.QueryCostAtMost S.run hashBlocks N
  /-- (as `Holds`) `α`'s input has `L ≠ 32` bytes. -/
  L_ne : L ≠ 32
  inp_length : ∀ a, (S.inp a).length = L
  /-- **New** (replaces `hashA`): `α`'s input is already hashed after stage A with probability at most `εα`. -/
  alphaFresh : Pr{let p ← (simulateQ ro S.A).run ∅}[p.2 (.inl (S.inp p.1)) ≠ none] ≤ εα
  /-- (as `Holds`) The copy argument's bad triples' count. -/
  badCard : ∀ p, (Bad p).card ≤ M * 2 ^ 384
  /-- (as `Holds`) At most `ct` bad values of `t` for each prior. -/
  badTCard : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ t, badT fp t → t ∈ T
  /-- (as `Holds`) `t`'s input is already hashed before its query with probability at most `εt`. -/
  tFresh : Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none] ≤ εt
  /-- (as `Holds`) The grinding. -/
  rejectGood : Pr{let z ← (simulateQ ro S.run).run' ∅}[
    z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ Bad z.2.1 ∧ ¬ badT z.1.2.1 z.1.2.2] ≤ εpow

/-- **`Holds` gives `Holds2` at `εα = 0`** (`α`'s input fresh by its length). -/
theorem Pi2Staged.Holds.toHolds2 {S : Pi2Staged} {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {input : Vector UInt8 32} {rows : List ℕ} {q : D.pi1.Stack rows} {L : ℕ}
    {Bad : S.ρ → Finset (E × E × E)} {badT : S.τ → E → Prop} {M ct N : ℕ} {εt εpow : ℝ≥0∞}
    (h : S.Holds D P1 P2 input rows q L Bad badT M ct N εt εpow) :
    S.Holds2 D P1 P2 input rows q L Bad badT M ct N 0 εt εpow where
  experiment := h.experiment
  duplex := h.duplex
  cost := h.cost
  L_ne := h.L_ne
  inp_length := h.inp_length
  alphaFresh := by
    refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun p hp hc ↦ ?_)
    rcases cache_of_hashOK h.hashA ∅ hp _ hc with h' | h'
    · exact h' rfl
    · exact h'.2 (h.inp_length p.1)
  badCard := h.badCard
  badTCard := h.badTCard
  tFresh := h.tFresh
  rejectGood := h.rejectGood

/-- π2's completeness error from the staged experiment's numbers, `α`'s input fresh but with probability `εα`. -/
noncomputable def deltaStaged2 (M ct N : ℕ) (εα εt εpow : ℝ≥0∞) : ℝ≥0∞ :=
  (εα + (((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192)) + (εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow +
    rpmError N

/-- **Stage A's Keccak-256 queries**: at most the run's block calls. -/
theorem Pi2Staged.hc_A (S : Pi2Staged) {N : ℕ} (h : Common.QueryCostAtMost S.run hashBlocks N) : HC S.A N := by
  unfold Pi2Staged.run staged3 at h
  exact hc_of_qc (Common.QueryCostAtMost.of_bind h)

/-- **One statement**, `Holds2`'s: the graph accepting and the contract rejecting has probability at most
`deltaStaged2`. -/
theorem prEvent_staged_bad_le2 (S : Pi2Staged) {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {input : Vector UInt8 32} {rows : List ℕ} {q : D.pi1.Stack rows} {L : ℕ}
    {Bad : S.ρ → Finset (E × E × E)} {badT : S.τ → E → Prop} {M ct N : ℕ} {εα εt εpow : ℝ≥0∞}
    (h : S.Holds2 D P1 P2 input rows q L Bad badT M ct N εα εt εpow) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1.1 = true ∧ z.1.1.2 = false] ≤
      deltaStaged2 M ct N εα εt εpow := by
  refine E2ECompleteness.rpm_le_rom S.run h.duplex h.cost (fun z ↦ z.1.1.1 = true ∧ z.1.1.2 = false) ?_
  have hab : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.2.2 ∈ Bad z.2.1] ≤
      εα + (((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) := by
    rw [StateT.run'_eq, prEvent_map]
    have := prEvent_staged3_triple_le2 chalP E2ECompleteness.challengeOf_regular h.L_ne Bad M h.badCard S.inp
      h.inp_length S.pr S.A S.tail (S.hc_A h.cost) ∅ cacheBound_empty εα h.alphaFresh
    rw [zero_add] at this
    exact this
  have ht : Pr{let z ← (simulateQ ro S.run).run' ∅}[badT z.1.2.1 z.1.2.2] ≤ εt + (ct : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map, S.run_eq_pre]
    refine (prEvent_tquery_le' chalP E2ECompleteness.challengeOf_regular badT ct h.badTCard S.pre
      (fun x ↦ S.tin x.1) (fun x ↦ S.prT x.1) (fun x st ↦ S.C x.1 st)
      (fun x st z ↦ ((z, (S.prT x.1, chalP st)), x.2)) (fun w ↦ badT w.1.2.1 w.1.2.2) (fun _ _ _ hw ↦ hw)
      ∅).trans ?_
    exact add_le_add h.tFresh le_rfl
  have hsplit : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ z.1.1.2 = false] ≤
      Pr{let z ← (simulateQ ro S.run).run' ∅}[z.2.2 ∈ Bad z.2.1] +
        (Pr{let z ← (simulateQ ro S.run).run' ∅}[badT z.1.2.1 z.1.2.2] +
          Pr{let z ← (simulateQ ro S.run).run' ∅}[
            z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ Bad z.2.1 ∧ ¬ badT z.1.2.1 z.1.2.2]) := by
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _
      (fun z : ((Bool × Bool) × (S.τ × E)) × (S.ρ × E × E × E) ↦ z.2.2 ∈ Bad z.2.1)).trans
        (add_le_add le_rfl ?_)
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _
      (fun z : ((Bool × Bool) × (S.τ × E)) × (S.ρ × E × E × E) ↦ badT z.1.2.1 z.1.2.2)).trans
        (add_le_add le_rfl (le_of_eq ?_))
    simp only [and_assoc]
  refine hsplit.trans ?_
  calc _ ≤ (εα + (((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192)) +
        ((εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow) := add_le_add hab (add_le_add ht h.rejectGood)
    _ = _ := by ac_rfl

/-- **`RecCompleteness2` from `Holds2`.** -/
theorem recCompleteness2_of_staged2 {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {L M ct N : ℕ} {εα εt εpow : ℝ≥0∞}
    (hS : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
      D.pi1.HonestRelation rows input q →
      ∃ (S : Pi2Staged) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop),
        S.Holds2 D P1 P2 input rows q L Bad badT M ct N εα εt εpow) :
    RecStatement.RecCompleteness2 D P1 P2 (deltaStaged2 M ct N εα εt εpow) := by
  intro input rows q hfit hrel
  obtain ⟨S, Bad, badT, h⟩ := hS input rows q hfit hrel
  exact h.experiment.trans (prEvent_staged_bad_le2 S h)

/-! ## π2's numbers -/

/-- **π2's completeness error**, `α`'s input fresh but with probability `εα`: the copy argument's `(2^25 + 36) |E|²`
bad triples, `t`'s `2^27`. -/
noncomputable def delta2' (N : ℕ) (εα εt εpow : ℝ≥0∞) : ℝ≥0∞ := deltaStaged2 (2 ^ 25 + 36) (2 ^ 27) N εα εt εpow

/-- **`δ2` in bits**: below `2^-164` at `N ≤ 2^50`, `εα, εt ≤ 2^-200`, `εpow ≤ 2^-300`. -/
theorem delta2'_le {N : ℕ} {εα εt εpow : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 200)
    (ht : εt ≤ (2 : ℝ≥0∞)⁻¹ ^ 200) (hp : εpow ≤ (2 : ℝ≥0∞)⁻¹ ^ 300) :
    delta2' N εα εt εpow ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 := by
  set x : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 170 with hx
  have hsmall : ∀ k, 170 ≤ k → (2 : ℝ≥0∞)⁻¹ ^ k ≤ x := fun k hk ↦ E2ECompleteness.inv_pow_le_inv_pow hk
  have h0 : εα ≤ x := ha.trans (hsmall 200 (by norm_num))
  have ha' : ((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ x := by
    calc ((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 ^ 52 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (204 + 52) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          exact_mod_cast (show 2 * N + 1 ≤ 2 ^ 52 by omega)
      _ = (2 : ℝ≥0∞)⁻¹ ^ 204 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact E2ECompleteness.two_pow_mul_inv_pow 52 204
      _ ≤ x := hsmall 204 (by norm_num)
  have hb : ((2 ^ 25 + 36 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 4 * x := by
    calc ((2 ^ 25 + 36 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 26 * (2 : ℝ≥0∞)⁻¹ ^ (166 + 26) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 166 := E2ECompleteness.two_pow_mul_inv_pow 26 166
      _ = 2 ^ 4 * x := (E2ECompleteness.two_pow_mul_inv_pow 4 166).symm
  have hc : ((2 ^ 27 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 5 * x := by
    refine le_of_eq ?_
    calc ((2 ^ 27 : ℕ) : ℝ≥0∞) / 2 ^ 192 = 2 ^ 27 * (2 : ℝ≥0∞)⁻¹ ^ (165 + 27) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 165 := E2ECompleteness.two_pow_mul_inv_pow 27 165
      _ = 2 ^ 5 * x := (E2ECompleteness.two_pow_mul_inv_pow 5 165).symm
  have hd : εt ≤ x := ht.trans (hsmall 200 (by norm_num))
  have he : εpow ≤ x := hp.trans (hsmall 300 (by norm_num))
  have hf : rpmError N ≤ x := by
    calc rpmError N ≤ rpmError (2 ^ 50) := by
          unfold rpmError
          gcongr
      _ = 2 ^ (50 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (408 + 50 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 408 := E2ECompleteness.two_pow_mul_inv_pow _ 408
      _ ≤ x := hsmall 408 (by norm_num)
  unfold delta2' deltaStaged2
  calc _ ≤ (x + (x + 2 ^ 4 * x)) + (x + 2 ^ 5 * x) + x + x :=
        add_le_add (add_le_add (add_le_add (add_le_add h0 (add_le_add ha' hb)) (add_le_add hd hc)) he) hf
    _ = 53 * x := by ring
    _ ≤ 2 ^ 6 * x := by gcongr; norm_num
    _ = (2 : ℝ≥0∞)⁻¹ ^ 164 := by rw [hx]; exact E2ECompleteness.two_pow_mul_inv_pow 6 164

end RecCompose.Pi2P

/-- info: 'RecCompose.Pi2P.prEvent_staged3_triple_le2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged3_triple_le2

/-- info: 'RecCompose.Pi2P.Pi2Staged.Holds.toHolds2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.Pi2Staged.Holds.toHolds2

/-- info: 'RecCompose.Pi2P.recCompleteness2_of_staged2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.recCompleteness2_of_staged2

/-- info: 'RecCompose.Pi2P.delta2'_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.delta2'_le
