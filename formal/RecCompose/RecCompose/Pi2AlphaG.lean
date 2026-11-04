-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Pi2Chain.lean`'s `prEvent_staged3_triple_le2`,
-- `prEvent_staged_bad_le2`, `Pi2Prob.lean`'s `prEvent_tquery_le'` and `Pi2TFresh.lean`'s `TF.tFresh_of`, with the
-- freshness conditioned on a predicate off which the verdict rejects; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, their lazy random oracles, `rpmError`, `DuplexVm`, `hashBlocks`; VCVio's `support`.
import RecCompose.Pi2TFreshPi2

/-!
# π2's chain, its freshness conditioned on the graph's acceptance

`Holds2` asks `α`'s input to be fresh after stage A on every outcome (but with probability `εα`). On π2's staged run
that fails off the graph's acceptance: when π1's prover returns none, or the witness π2 takes is not honest, `α`'s
input is `fixLen`'s `536` zeros, which nothing keeps π1-rec3's prover from hashing. There the verdict's first component
(π1-rec3's graph's) is `false`, so the experiment's event cannot happen. So:

* **`Pi2Staged.Holds3`**: `Holds2` with a predicate `G` of stage A's output and `Gβ` of stage B's, `alphaFresh` and
  `tFresh` conditioned on them (`… ∧ G p.1`, `… ∧ Gβ p.1.1`), and **`accA`**, **`accB`**: off `G` (resp. `Gβ`) every
  outcome of the rest of the run (`S.tail`, resp. `S.C`) has the first component `false`.
* **`prEvent_staged3_triple_leG`**, **`prEvent_tquery_leG`**, **`TF.tFresh_ofG`**: the three lemmas, conditioned.
* **`recCompleteness2_of_staged3`**: `RecCompleteness2 D P1 P2 (deltaStaged2 M ct N εα εt εpow)` from `Holds3`, the
  same error as `recCompleteness2_of_staged2`.
* **`Pi2G.pi2TFresh_ofG`**: `t`'s freshness at π2's staged run conditioned on `G b.a`, from the run's cost and `α`'s
  conditioned freshness, the bound `tFreshBound2 N εα` of `pi2TFresh_of`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK cache_of_hashOK prEvent_fresh prEvent_final_le Regular length_digestBytes
  simulateQ_callKeccak256)
open UniComplete.Prob (GoodL prEvent_query_le sum_const_div sum_mem_le sum_bad_le)
open UniComplete.Prob.TFresh (HC hc_of_qc CacheBound cacheBound_empty cacheBound_run sum_hit_le take_digestBytes'
  run_frame)
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.Pi2P

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## `α, β, γ`, conditioned -/

set_option exponentiation.threshold 1024 in
/-- **`α, β, γ` in the random-oracle model, conditioned** (`prEvent_staged3_triple_le2` with `α`'s input fresh but on
`G`): off `G` no outcome of the rest is `Acc`; the event `Acc ∧ triple ∈ Bad` has probability at most
`εα + (2K + 1) / 2^256 + M / 2^192`. -/
theorem prEvent_staged3_triple_leG {α ρ γ : Type} (chal : Digest → E) (hreg : Regular chal) {L : ℕ} (hL : L ≠ 32)
    (Bad : ρ → Finset (E × E × E)) (M : ℕ) (hM : ∀ p, (Bad p).card ≤ M * 2 ^ 384)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = L) (pr : α → ρ) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → OracleComp KeccakCalls γ) (G : α → Prop) (Acc : γ → Prop)
    (hacc : ∀ a, ¬ G a → ∀ (s₁ s₂ s₃ : Digest) (c : Cache) z,
      z ∈ support ((simulateQ ro (C a s₁ s₂ s₃)).run c) → ¬ Acc z.1)
    {KA K₀ : ℕ} (hA : HC A KA) (c₀ : Cache) (hc₀ : CacheBound c₀ K₀) (εα : ℝ≥0∞)
    (hα : Pr{let p ← (simulateQ ro A).run c₀}[p.2 (.inl (inp p.1)) ≠ none ∧ G p.1] ≤ εα) :
    Pr{let z ← (simulateQ ro (staged3 chal inp pr A C)).run c₀}[Acc z.1.1 ∧ z.1.2.2 ∈ Bad z.1.2.1] ≤
      εα + (((2 * (K₀ + KA) + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) := by
  classical
  rw [run_staged3]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun p ↦ p.2 (.inl (inp p.1)) ≠ none ∧ G p.1) _
    fun p hp hpα ↦ ?_).trans (add_le_add hα le_rfl)
  by_cases hG : G p.1
  swap
  · refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hev ↦ ?_)).trans zero_le
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₁, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₂, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₃, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨z, hz, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hacc p.1 hG _ _ _ _ z hz hev.1
  have hfα : p.2 (.inl (inp p.1)) = none := not_not.mp fun h ↦ hpα ⟨h, hG⟩
  refine (prEvent_mono _ _ (fun w ↦ w.1.2.2 ∈ Bad w.1.2.1) fun w hw ↦ hw.2).trans ?_
  have hcp : CacheBound p.2 (K₀ + KA) := cacheBound_run hA hc₀ hp
  set K := K₀ + KA with hK
  set c := p.2 with hc
  set T := Bad (pr p.1) with hT
  set I : Digest → Digest → Digest → ℝ≥0∞ := fun s₁ s₂ s₃ ↦ if (chal s₁, chal s₂, chal s₃) ∈ T then 1 else 0
    with hI
  have hne : ∀ s : Digest, (Sum.inl (digestBytes s) : Bytes ⊕ KeccakState) ≠ .inl (inp p.1) := fun s h ↦
    hL ((hinp p.1).symm.trans (by rw [← Sum.inl_injective h, length_digestBytes]))
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
  refine (prEvent_query_le _ _ (s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none) (fun hs ↦ ?_) _ _
    (fun s₃ ↦ I s₁ s₂ s₃) fun s₃ ↦ ?_).trans le_rfl
  · rw [not_or] at hs
    have h12 : (Sum.inl (digestBytes s₂) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₁) := fun h ↦
      hs.1 (E2ECompleteness.digestBytes_injective (Sum.inl_injective h))
    rw [QueryCache.cacheQuery_of_ne _ _ h12, QueryCache.cacheQuery_of_ne _ _ (hne s₂)]
    exact not_not.mp hs.2
  exact prEvent_final_le _ (pr p.1, chal s₁, chal s₂, chal s₃) (fun v ↦ v.2 ∈ Bad v.1)

/-! ## `t`, conditioned -/

/-- **The point challenge `t`, conditioned** (`prEvent_tquery_le'` with `t`'s input fresh but on `Gx`): off `Gx` no
outcome of the rest makes the event; the event is at most `t`'s input cached on `Gx`, plus `ct / 2^192`. -/
theorem prEvent_tquery_leG {β γ ω τ : Type} (chal : Digest → E) (hreg : Regular chal) (badT : τ → E → Prop)
    (ct : ℕ) (hct : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ b, badT fp b → b ∈ T)
    (X : OracleComp KeccakCalls β) (tin : β → Bytes) (pr : β → τ)
    (K : β → Digest → OracleComp KeccakCalls γ) (h : β → Digest → γ → ω) (ev : ω → Prop)
    (hev : ∀ x st z, ev (h x st z) → badT (pr x) (chal st)) (Gx : β → Prop)
    (hacc : ∀ x, ¬ Gx x → ∀ (st : Digest) (c : Cache) z, z ∈ support ((simulateQ ro (K x st)).run c) →
      ¬ ev (h x st z.1)) (c₀ : Cache) :
    Pr{let z ← (simulateQ ro (X >>= fun x ↦ callKeccak256 (tin x) >>= fun st ↦ K x st >>= fun z ↦
        pure (h x st z))).run c₀}[ev z.1] ≤
      Pr{let p ← (simulateQ ro X).run c₀}[p.2 (.inl (tin p.1)) ≠ none ∧ Gx p.1] + (ct : ℝ≥0∞) / 2 ^ 192 := by
  classical
  simp only [simulateQ_bind, simulateQ_callKeccak256, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  refine prEvent_bind_le_prEvent_add_of_support _ _ _ _ fun p _ hp ↦ ?_
  by_cases hG : Gx p.1
  swap
  · refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hw' ↦ ?_)).trans zero_le
    rw [mem_support_bind_iff] at hw
    obtain ⟨q, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨z, hz, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hacc p.1 hG _ _ z hz hw'
  have hfresh : p.2 (.inl (tin p.1)) = none := not_not.mp fun h' ↦ hp ⟨h', hG⟩
  rw [prEvent_fresh _ _ hfresh]
  refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _)
    (sum_bad_le chal hreg (badT (pr p.1)) ct (hct _))
  by_cases hb : badT (pr p.1) (chal u)
  · simp only [hb, ↓reduceIte]
    exact prEvent_le_one _
  · simp only [hb, ↓reduceIte]
    refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_)
    rw [mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun he ↦ hb (hev _ _ _ he)

/-! ## The staged experiment, conditioned -/

/-- **The code-level bridge, conditioned**: `Holds2`'s fields, `α`'s and `t`'s freshness on `G` and `Gβ`, and off them
the verdict's first component is `false` (`accA`, `accB`). -/
structure Pi2Staged.Holds3 (S : Pi2Staged) (D : RecStatement.RecDeployment) (P1 : RecStatement.Pi1Prover D)
    (P2 : RecStatement.Pi2Prover) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (L : ℕ) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop) (G : S.α → Prop) (Gβ : S.β → Prop)
    (M ct N : ℕ) (εα εt εpow : ℝ≥0∞) : Prop where
  /-- (as `Holds2`) The experiment's event is at most the two-call run's against the random permutation. -/
  experiment : Pr{let v ← RecStatement.recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = true ∧ v.2 = false] ≤
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1.1 = true ∧ z.1.1.2 = false]
  /-- (as `Holds2`) The duplex discipline. -/
  duplex : DuplexVm S.run []
  /-- (as `Holds2`) At most `N` block calls. -/
  cost : Common.QueryCostAtMost S.run hashBlocks N
  /-- (as `Holds2`) `α`'s input has `L ≠ 32` bytes. -/
  L_ne : L ≠ 32
  inp_length : ∀ a, (S.inp a).length = L
  /-- `α`'s input is already hashed after stage A, on `G`, with probability at most `εα`. -/
  alphaFresh : Pr{let p ← (simulateQ ro S.A).run ∅}[p.2 (.inl (S.inp p.1)) ≠ none ∧ G p.1] ≤ εα
  /-- Off `G` the rest of the run's verdict has the first component `false`. -/
  accA : ∀ a, ¬ G a → ∀ (s₁ s₂ s₃ : Digest) (c : Cache) z,
    z ∈ support ((simulateQ ro (S.tail a s₁ s₂ s₃)).run c) → z.1.1.1 = false
  /-- Off `Gβ` stage C's verdict has the first component `false`. -/
  accB : ∀ b, ¬ Gβ b → ∀ (st : Digest) (c : Cache) z, z ∈ support ((simulateQ ro (S.C b st)).run c) → z.1.1 = false
  /-- (as `Holds2`) The copy argument's bad triples' count. -/
  badCard : ∀ p, (Bad p).card ≤ M * 2 ^ 384
  /-- (as `Holds2`) At most `ct` bad values of `t` for each prior. -/
  badTCard : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ t, badT fp t → t ∈ T
  /-- `t`'s input is already hashed before its query, on `Gβ`, with probability at most `εt`. -/
  tFresh : Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none ∧ Gβ p.1.1] ≤ εt
  /-- (as `Holds2`) The grinding. -/
  rejectGood : Pr{let z ← (simulateQ ro S.run).run' ∅}[
    z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ Bad z.2.1 ∧ ¬ badT z.1.2.1 z.1.2.2] ≤ εpow

/-- **One statement**, `Holds3`'s: the graph accepting and the contract rejecting has probability at most
`deltaStaged2`. -/
theorem prEvent_staged_bad_le3 (S : Pi2Staged) {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {input : Vector UInt8 32} {rows : List ℕ} {q : D.pi1.Stack rows} {L : ℕ}
    {Bad : S.ρ → Finset (E × E × E)} {badT : S.τ → E → Prop} {G : S.α → Prop} {Gβ : S.β → Prop} {M ct N : ℕ}
    {εα εt εpow : ℝ≥0∞} (h : S.Holds3 D P1 P2 input rows q L Bad badT G Gβ M ct N εα εt εpow) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1.1 = true ∧ z.1.1.2 = false] ≤
      deltaStaged2 M ct N εα εt εpow := by
  refine E2ECompleteness.rpm_le_rom S.run h.duplex h.cost (fun z ↦ z.1.1.1 = true ∧ z.1.1.2 = false) ?_
  have hab : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ z.2.2 ∈ Bad z.2.1] ≤
      εα + (((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) := by
    rw [StateT.run'_eq, prEvent_map]
    have := prEvent_staged3_triple_leG chalP E2ECompleteness.challengeOf_regular h.L_ne Bad M h.badCard S.inp
      h.inp_length S.pr S.A S.tail G (fun y ↦ y.1.1 = true)
      (fun a ha s₁ s₂ s₃ c z hz hz' ↦ Bool.false_ne_true ((h.accA a ha s₁ s₂ s₃ c z hz).symm.trans hz'))
      (S.hc_A h.cost) ∅ cacheBound_empty εα h.alphaFresh
    rw [zero_add] at this
    exact this
  have ht : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ badT z.1.2.1 z.1.2.2] ≤
      εt + (ct : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map, S.run_eq_pre]
    refine (prEvent_tquery_leG chalP E2ECompleteness.challengeOf_regular badT ct h.badTCard S.pre
      (fun x ↦ S.tin x.1) (fun x ↦ S.prT x.1) (fun x st ↦ S.C x.1 st)
      (fun x st z ↦ ((z, (S.prT x.1, chalP st)), x.2)) (fun w ↦ w.1.1.1 = true ∧ badT w.1.2.1 w.1.2.2)
      (fun _ _ _ hw ↦ hw.2) (fun x ↦ Gβ x.1)
      (fun x hx st c z hz hz' ↦ Bool.false_ne_true ((h.accB x.1 hx st c z hz).symm.trans hz'.1)) ∅).trans ?_
    exact add_le_add h.tFresh le_rfl
  have hsplit : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ z.1.1.2 = false] ≤
      Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ z.2.2 ∈ Bad z.2.1] +
        (Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ badT z.1.2.1 z.1.2.2] +
          Pr{let z ← (simulateQ ro S.run).run' ∅}[
            z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ Bad z.2.1 ∧ ¬ badT z.1.2.1 z.1.2.2]) := by
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _
      (fun z : ((Bool × Bool) × (S.τ × E)) × (S.ρ × E × E × E) ↦ z.1.1.1 = true ∧ z.2.2 ∈ Bad z.2.1)).trans
        (add_le_add le_rfl ?_)
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _
      (fun z : ((Bool × Bool) × (S.τ × E)) × (S.ρ × E × E × E) ↦ z.1.1.1 = true ∧ badT z.1.2.1 z.1.2.2)).trans
        (add_le_add le_rfl ?_)
    exact prEvent_mono _ _ _ fun z hz ↦
      ⟨hz.1.1.1, hz.1.1.2, fun hb ↦ hz.1.2 ⟨hz.1.1.1, hb⟩, fun hb ↦ hz.2 ⟨hz.1.1.1, hb⟩⟩
  refine hsplit.trans ?_
  calc _ ≤ (εα + (((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192)) +
        ((εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow) := add_le_add hab (add_le_add ht h.rejectGood)
    _ = _ := by ac_rfl

/-- **`RecCompleteness2` from `Holds3`.** -/
theorem recCompleteness2_of_staged3 {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {L M ct N : ℕ} {εα εt εpow : ℝ≥0∞}
    (hS : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
      D.pi1.HonestRelation rows input q → ∃ (S : Pi2Staged) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop)
        (G : S.α → Prop) (Gβ : S.β → Prop), S.Holds3 D P1 P2 input rows q L Bad badT G Gβ M ct N εα εt εpow) :
    RecStatement.RecCompleteness2 D P1 P2 (deltaStaged2 M ct N εα εt εpow) := by
  intro input rows q hfit hrel
  obtain ⟨S, Bad, badT, G, Gβ, h⟩ := hS input rows q hfit hrel
  exact h.experiment.trans (prEvent_staged_bad_le3 S h)

/-! ## `t`'s freshness, conditioned -/

namespace TF

/-- **`t`'s query is fresh on `Gβ`** (`tFresh_of`, conditioned): `α`'s input cached after A on `G` with probability at
most `εα`, `Gβ` of stage B's output implying `G` of stage A's; `t`'s input is cached when asked, on `Gβ`, with
probability at most `εα + (4 KA + 6 + NT) / 2^256`. -/
theorem tFresh_ofG (S : Pi2Staged) {δ : Type} (T : S.α → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (g : S.α → Digest → Digest → Digest → δ → S.β)
    (hB : ∀ a s₁ s₂ s₃, S.B a s₁ s₂ s₃ = T a s₁ s₂ s₃ >>= fun d ↦ pure (g a s₁ s₂ s₃ d))
    (hTap : ∀ a s₁ s₂ s₃, APq (fun _ _ ↦ True) [default] (T a s₁ s₂ s₃))
    (hT32 : ∀ a s₁ s₂ s₃, HashOK (fun m ↦ m.length ≠ 32) (T a s₁ s₂ s₃))
    {NT : ℕ} (hTc : ∀ a s₁ s₂ s₃, HC (T a s₁ s₂ s₃) NT)
    (htin : ∀ a s₁ s₂ s₃ d, (S.tin (g a s₁ s₂ s₃ d)).length = 64 ∧
      (S.tin (g a s₁ s₂ s₃ d)).take 32 = digestBytes s₃)
    {L : ℕ} (hL : L ≠ 32) (hinp : ∀ a, (S.inp a).length = L) {KA : ℕ} (hA : HC S.A KA)
    (G : S.α → Prop) (Gβ : S.β → Prop) (hg : ∀ a s₁ s₂ s₃ d, Gβ (g a s₁ s₂ s₃ d) → G a) {εα : ℝ≥0∞}
    (hα : Pr{let p ← (simulateQ ro S.A).run ∅}[p.2 (.inl (S.inp p.1)) ≠ none ∧ G p.1] ≤ εα) :
    Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none ∧ Gβ p.1.1] ≤
      εα + ((4 * KA + 6 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  rw [run_pre_tree S T g hB]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun p ↦ p.2 (.inl (S.inp p.1)) ≠ none ∧ G p.1) _
    fun p hp hpα ↦ ?_).trans (add_le_add hα le_rfl)
  by_cases hG : G p.1
  swap
  · refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hev ↦ ?_)).trans zero_le
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₁, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₂, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₃, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨z, -, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hG (hg _ _ _ _ _ hev.2)
  have hfα : p.2 (.inl (S.inp p.1)) = none := not_not.mp fun h ↦ hpα ⟨h, hG⟩
  refine (prEvent_mono _ _ (fun w ↦ w.2 (.inl (S.tin w.1.1)) ≠ none) fun w hw ↦ hw.1).trans ?_
  have hcp : CacheBound p.2 KA := by simpa using cacheBound_run hA cacheBound_empty hp
  set c := p.2 with hc
  have hne : ∀ s : Digest, (Sum.inl (digestBytes s) : Bytes ⊕ KeccakState) ≠ .inl (S.inp p.1) := fun s h ↦
    hL ((hinp p.1).symm.trans (by rw [← Sum.inl_injective h, length_digestBytes]))
  -- `s₁`: fresh.
  refine (prEvent_query_le _ _ False (fun _ ↦ hfα) _ _
    (fun s₁ ↦ (if c (.inl (digestBytes s₁)) ≠ none then 1 else 0) +
      ((KA + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((2 * KA + 5 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256)
    fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_add_distrib, ENNReal.add_div, sum_const_div,
      sum_const_div]
    refine (add_le_add (add_le_add (ENNReal.div_le_div_right (sum_cached_le hcp) _) le_rfl) le_rfl).trans
      (le_of_eq ?_)
    rw [← ENNReal.add_div, ← ENNReal.add_div]
    congr 1
    push_cast
    ring
  -- `s₂`: fresh unless `s₁`'s bytes were cached.
  refine (prEvent_query_le _ _ (c (.inl (digestBytes s₁)) ≠ none)
    (fun hs ↦ by rw [QueryCache.cacheQuery_of_ne _ _ (hne s₁)]; exact not_not.mp hs) _ _
    (fun s₂ ↦ (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0) +
      ((2 * KA + 5 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256) fun s₂ ↦ ?_).trans ?_
  rotate_left
  · refine le_trans ?_ (le_of_eq (add_assoc _ _ _).symm)
    refine add_le_add le_rfl ?_
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    refine add_le_add (ENNReal.div_le_div_right ?_ _) le_rfl
    calc (∑ s₂ : Digest, (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0 : ℝ≥0∞))
        ≤ ∑ s₂ : Digest, ((if s₂ ∈ [s₁] then 1 else 0) + (if c (.inl (digestBytes s₂)) ≠ none then 1 else 0)) :=
          Finset.sum_le_sum fun s₂ _ ↦ by
            simpa only [List.mem_singleton] using ite_or_le (s₂ = s₁) (c (.inl (digestBytes s₂)) ≠ none)
      _ ≤ (([s₁].length : ℕ) : ℝ≥0∞) + KA := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (sum_mem_le _) (sum_cached_le hcp)
      _ = ((KA + 1 : ℕ) : ℝ≥0∞) := by simp only [List.length_singleton, Nat.cast_one]; push_cast; ring
  -- the cache before `s₃`
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Cache,
      (c.cacheQuery (.inl (S.inp p.1)) s₁).cacheQuery (.inl (digestBytes s₁)) s₂ = c₂ := ⟨_, rfl⟩
  have hc₂b : CacheBound c₂ (KA + 2) := by
    rw [← hc₂]
    exact (hcp.cacheQuery_inl _ _).cacheQuery_inl _ _
  dsimp only
  rw [hc₂]
  -- `s₃`: fresh unless `s₂ = s₁` or `s₂`'s bytes were cached.
  refine (prEvent_query_le _ _ (s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none) (fun hs ↦ ?_) _ _
    (fun u ↦ (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0) + (NT : ℝ≥0∞) / 2 ^ 256)
    fun u ↦ ?_).trans (add_le_add le_rfl ?_)
  · rw [not_or] at hs
    have h12 : (Sum.inl (digestBytes s₂) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₁) := fun h ↦
      hs.1 (E2ECompleteness.digestBytes_injective (Sum.inl_injective h))
    rw [← hc₂, QueryCache.cacheQuery_of_ne _ _ h12, QueryCache.cacheQuery_of_ne _ _ (hne s₂)]
    exact not_not.mp hs.2
  · -- the tree after `u = s₃`
    by_cases hbad : u = default ∨ Ans c₂ u ∨ Hit64 c₂ u
    · simp only [hbad, ↓reduceIte]
      exact (prEvent_le_one _).trans le_self_add
    simp only [hbad, ↓reduceIte, zero_add]
    rw [not_or, not_or] at hbad
    have hT2 : HashOK (fun m ↦ m ≠ digestBytes s₂) (T p.1 s₁ s₂ u) :=
      UniComplete.Prob.HashOK.mono (P := fun m ↦ m.length ≠ 32) (Q := fun m ↦ m ≠ digestBytes s₂)
        (fun m hm he ↦ hm (by rw [he]; exact length_digestBytes s₂)) (hT32 _ _ _ _)
    try dsimp only
    rw [run_frame _ u _ hT2 c₂]
    refine (prEvent_map_bind_pure _ _ _ _ (fun z ↦ Hit64 z.2 u) fun z hz ↦ ?_).trans ?_
    · obtain ⟨hl, ht⟩ := htin p.1 s₁ s₂ u z.1
      have hn : (Sum.inl (S.tin (g p.1 s₁ s₂ u z.1)) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₂) := fun h ↦ by
        have := congrArg List.length (Sum.inl_injective h)
        rw [hl, length_digestBytes] at this
        omega
      dsimp only at hz
      rw [QueryCache.cacheQuery_of_ne _ _ hn] at hz
      exact ⟨_, hz, hl, ht⟩
    · exact prHit64_le (hTap p.1 s₁ s₂ u) (hTc _ _ _ _) c₂ u
        (fun hm ↦ hbad.1 (List.mem_singleton.mp hm)) hbad.2.1 hbad.2.2
  · -- the average over `u`
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    have hsum : (∑ u : Digest, (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0 : ℝ≥0∞)) ≤
        ((2 * KA + 5 : ℕ) : ℝ≥0∞) := by
      calc (∑ u : Digest, (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0 : ℝ≥0∞))
          ≤ ∑ u : Digest, ((if u ∈ [default] then 1 else 0) + ((if Ans c₂ u then 1 else 0) +
              (if Hit64 c₂ u then 1 else 0))) :=
            Finset.sum_le_sum fun u _ ↦ (ite_or_le _ _).trans (add_le_add (by simp) (ite_or_le _ _))
        _ ≤ (([default].length : ℕ) : ℝ≥0∞) + (((KA + 2 : ℕ) : ℝ≥0∞) + ((KA + 2 : ℕ) : ℝ≥0∞)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            exact add_le_add (sum_mem_le _) (add_le_add (sum_ans_le hc₂b) (sum_hit64_le hc₂b))
        _ = ((2 * KA + 5 : ℕ) : ℝ≥0∞) := by
            simp only [List.length_singleton, Nat.cast_one]
            push_cast
            ring
    refine (add_le_add (ENNReal.div_le_div_right hsum _) le_rfl).trans (le_of_eq ?_)
    rw [← ENNReal.add_div]
    congr 1
    push_cast
    ring

end TF

end RecCompose.Pi2P

namespace RecCompose.Pi2G

open RecStatement LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open Pi2S Pi2K Pi2P Pi2E

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-- **`t`'s freshness at π2's staged run, conditioned on `G` of stage B's `a`** (`pi2TFresh_of`, conditioned): from the
run's cost and `α`'s freshness on `G`. -/
theorem pi2TFresh_ofG {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (input : Vector UInt8 32) {N : ℕ}
    (hcost : Common.QueryCostAtMost (pi2Staged D C Fa P1k input).run hashBlocks N) (G : StA → Prop) {εα : ℝ≥0∞}
    (hα : Pr{let p ← (simulateQ ro (pi2Staged D C Fa P1k input).A).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa P1k input).inp p.1)) ≠ none ∧ G p.1] ≤ εα) :
    Pr{let p ← (simulateQ ro (pi2Staged D C Fa P1k input).pre).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa P1k input).tin p.1.1)) ≠ none ∧ G p.1.1.a] ≤ tFreshBound2 N εα := by
  refine TF.tFresh_ofG (pi2Staged D C Fa P1k input) (fun a s₁ s₂ s₃ ↦ treeB C a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ qT ↦ outB C a s₁ s₂ s₃ qT) (fun a s₁ s₂ s₃ ↦ stageB_eq D C a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ ↦ TF.apq_commitWithH _ _ _ (List.mem_singleton_self _))
    (fun a s₁ s₂ s₃ ↦ UniComplete.Prob.HashOK.mono (fun m h ↦ h.1) (E2ECompleteness.hashOK_commitWithH _ _))
    (NT := E2ECompleteness.Cost.treeCost muQ)
    (fun a s₁ s₂ s₃ ↦ by
      unfold treeB E2ECompleteness.Cost.treeCost
      rw [logN_G Fa]
      exact hc_of_qc (E2ECompleteness.Cost.qc_commitWithH _ _))
    (fun a s₁ s₂ s₃ qT ↦ tin_stageB_length C a s₁ s₂ s₃ qT) (by norm_num : (536 : ℕ) ≠ 32)
    (fun a ↦ fixLen_length 536 _) ((pi2Staged D C Fa P1k input).hc_A hcost) G (fun b : StB ↦ G b.a)
    (fun _ _ _ _ _ h ↦ h) hα |>.trans (le_of_eq ?_)
  unfold tFreshBound2
  rfl

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2P.prEvent_staged3_triple_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged3_triple_leG

/-- info: 'RecCompose.Pi2P.prEvent_tquery_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_tquery_leG

/-- info: 'RecCompose.Pi2P.prEvent_staged_bad_le3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged_bad_le3

/-- info: 'RecCompose.Pi2P.recCompleteness2_of_staged3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.recCompleteness2_of_staged3

/-- info: 'RecCompose.Pi2P.TF.tFresh_ofG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.TF.tFresh_ofG

/-- info: 'RecCompose.Pi2G.pi2TFresh_ofG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.pi2TFresh_ofG
