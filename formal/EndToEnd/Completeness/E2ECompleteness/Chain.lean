-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the two calls `KeccakCalls` (Keccak-256 and Keccak-f[1600]) and their
-- random oracles, `|Digest| = 2^256`; and VCVio's lazy random oracle.
import LeanVM.Protocol.WithHash
import LeanVM.Protocol.Compile.Rom.Encoding
import PcsQuotient.Transcript
import Common.Lanes

/-!
# The reduction's challenges in the random-oracle model

The reduction's Fiat–Shamir chain (`PcsQuotient.Transcript`, `transcript.rs`) draws its challenges
as Keccak-256 answers: after the witness table's root, `s₁ = H(s₀ ‖ r₁)` (96 bytes: the state and
the root's two scalars), `s₂ = H(s₁)`, `s₃ = H(s₂)` (32 bytes each), the challenges
`α, β, γ` their low 192 bits (`challengeOf`); after the quotient table's root, `s₄ = H(s₃ ‖ r₂)`
(96 bytes), `t` its low 192 bits. In the two-call random-oracle model (`KeccakCalls`, both calls
lazily sampled random functions, the model the random-permutation model transfers to) these
answers are uniform as long as the queries are fresh, and they are fresh **by their lengths**:
everything the prover hashes before them (the Merkle trees: 512-byte leaves, 64-byte nodes; the
112-byte label) has another length, so

* the `α` query is the first of 96 bytes, the `β` query the first of 32 bytes;
* the `γ` query repeats the `β` query only if `s₂ = s₁`, the `t` query repeats the `α` query only
  if `s₃ = s₀` (each `2^-256`).

**`prEvent_staged_le`**: for a computation of this shape (`staged A B C`: `A` up to the state
`s₀` and the witness root, `B` from the three challenges to the quotient root, `C` anything) whose
`A` and `B` hash only inputs of another length than `32` and `96` (`HashOK`), from a cache with no
such input, the triple `(α, β, t)` lies in a set `Bad` with probability at most

  `|Bad| / |E|^3 + 2 / 2^256`,

for any challenge map whose fibres have at most `2^64` digests (`Regular`; the low 192 bits of a
256-bit digest).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-- The two calls' lazy random oracles. -/
noncomputable abbrev ro : QueryImpl KeccakCalls (StateT KeccakCalls.QueryCache ProbComp) :=
  KeccakCalls.randomOracle

/-- The cache of the two calls. -/
abbrev Cache : Type := KeccakCalls.QueryCache

/-! ## Hash queries of a computation -/

/-- A query is allowed when it is a permutation call, or a hash of an input satisfying `P`. -/
def hashOK (P : Bytes → Prop) : (Bytes ⊕ KeccakState) → Unit → Prop
  | .inl x, _ => P x
  | .inr _, _ => True

/-- **Every hash query of `oa` satisfies `P`**, along every path. -/
def HashOK (P : Bytes → Prop) {α : Type} (oa : OracleComp KeccakCalls α) : Prop :=
  oa.IsQueryBound () (hashOK P) (fun _ _ ↦ ())

theorem HashOK.pure (P : Bytes → Prop) {α : Type} (a : α) :
    HashOK P (pure a : OracleComp KeccakCalls α) := trivial

theorem HashOK.bind {P : Bytes → Prop} {α β : Type} {oa : OracleComp KeccakCalls α}
    {f : α → OracleComp KeccakCalls β} (h₁ : HashOK P oa) (h₂ : ∀ a, HashOK P (f a)) :
    HashOK P (oa >>= f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using h₂ a
  | query_bind t k ih =>
    rw [bind_assoc]
    exact (isQueryBound_query_bind_iff _ _ _ _ _).2
      ⟨((isQueryBound_query_bind_iff _ _ _ _ _).1 h₁).1,
        fun u ↦ ih u (((isQueryBound_query_bind_iff _ _ _ _ _).1 h₁).2 u)⟩

theorem HashOK.map {P : Bytes → Prop} {α β : Type} {oa : OracleComp KeccakCalls α} (f : α → β)
    (h : HashOK P oa) : HashOK P (f <$> oa) :=
  (isQueryBound_map_iff oa f _ _ _).2 h

theorem hashOK_callKeccak256 {P : Bytes → Prop} {x : Bytes} (hx : P x) :
    HashOK P (callKeccak256 x) :=
  (isQueryBound_query_iff (spec := KeccakCalls) (.inl x) () _ _).2 hx

theorem hashOK_callKeccakF1600 (P : Bytes → Prop) (s : KeccakState) :
    HashOK P (callKeccakF1600 s) :=
  (isQueryBound_query_iff (spec := KeccakCalls) (.inr s) () _ _).2 trivial

/-! ## What a run adds to the cache -/

theorem mem_support_ro_run {t : Bytes ⊕ KeccakState} {c : Cache} {z}
    (hz : z ∈ support ((ro t).run c)) :
    z.2 = c ∨ ∃ v, z.2 = c.cacheQuery t v := by
  rw [randomOracle.run_eq] at hz
  rcases h : c t with _ | v
  · simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Or.inr ⟨w, rfl⟩
  · simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl

/-- **A run hashes only what it queries**: after a run of a computation whose hash queries satisfy
`P`, every hash input the cache answers was answered before or satisfies `P`. -/
theorem cache_of_hashOK {P : Bytes → Prop} {α : Type} {oa : OracleComp KeccakCalls α}
    (h : HashOK P oa) (c : Cache) {z : α × Cache} (hz : z ∈ support ((simulateQ ro oa).run c))
    (m : Bytes) (hm : z.2 (.inl m) ≠ none) : c (.inl m) ≠ none ∨ P m := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hm
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self,
      OracleQuery.cont_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, c₁⟩, hu', hz⟩ := hz
    rcases ih u (hk u) c₁ hz with h₁ | h₁
    · rcases mem_support_ro_run hu' with e | ⟨v, e⟩
      · exact Or.inl (e ▸ h₁)
      · simp only at e
        subst e
        by_cases htm : (Sum.inl m : Bytes ⊕ KeccakState) = t
        · subst htm
          exact Or.inr ht
        · rw [QueryCache.cacheQuery_of_ne _ _ htm] at h₁
          exact Or.inl h₁
    · exact Or.inr h₁

/-! ## Lengths -/

/-- The chain's challenge queries hash `32` or `96` bytes; everything else has another length. -/
def Good (m : Bytes) : Prop := m.length ≠ 32 ∧ m.length ≠ 96

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  have : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [this, LeanVM.Rpm.length_lanesBytes]
  simp

theorem digestBytes_injective : Function.Injective digestBytes := by
  intro d d' h
  have e : ∀ x : Digest, digestBytes x = LeanVM.Rpm.lanesBytes x.toList := fun _ ↦ rfl
  rw [e, e] at h
  apply Vector.toList_inj.mp
  apply List.ext_getElem (by simp)
  intro i hi hi'
  rw [← LeanVM.Rpm.leLane_lanesBytes _ i hi, ← LeanVM.Rpm.leLane_lanesBytes _ i hi', h]

theorem length_scalarBytes (x : E) : (PcsQuotient.Transcript.scalarBytes x).length = 32 := by
  simp [PcsQuotient.Transcript.scalarBytes, PcsQuotient.Transcript.beBytes, wordBytes]

/-- The chain's input after a root: the state, then the root's two scalars (`transcript.rs`). -/
def chainIn (s : Digest) (r : E × E) : Bytes :=
  digestBytes s ++ [r.1, r.2].flatMap PcsQuotient.Transcript.scalarBytes

theorem length_chainIn (s : Digest) (r : E × E) : (chainIn s r).length = 96 := by
  simp [chainIn, length_digestBytes, length_scalarBytes]

theorem chainIn_left {s s' : Digest} {r r' : E × E} (h : chainIn s r = chainIn s' r') :
    s = s' := by
  apply digestBytes_injective
  have h1 := congrArg (List.take 32) h
  simp only [chainIn] at h1
  rwa [List.take_left' (length_digestBytes s), List.take_left' (length_digestBytes s')] at h1

theorem not_good_chainIn (s : Digest) (r : E × E) : ¬ Good (chainIn s r) :=
  fun h ↦ h.2 (length_chainIn s r)

theorem not_good_digestBytes (s : Digest) : ¬ Good (digestBytes s) :=
  fun h ↦ h.1 (length_digestBytes s)

theorem chainIn_ne_digestBytes (s s' : Digest) (r : E × E) : chainIn s r ≠ digestBytes s' := by
  intro h
  have := congrArg List.length h
  rw [length_chainIn, length_digestBytes] at this
  omega

/-! ## The chain's shape -/

variable {α β γ : Type}

/-- **The chain's shape**: `A` up to the seeded state `s₀` and the witness root `r₁` (its two
scalars); `s₁ = H(s₀ ‖ r₁)`, `s₂ = H(s₁)`, `s₃ = H(s₂)`; `B` from the three states to the quotient
root `r₂`; `s₄ = H(s₃ ‖ r₂)`; `C` the rest. Its output carries `(chal s₁, chal s₂, chal s₄)`, the
`(α, β, t)` of `transcript.rs` when `chal` is `challengeOf`. -/
def staged (chal : Digest → E) (A : OracleComp KeccakCalls (α × Digest × (E × E)))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × (E × E)))
    (C : α → β → Digest → Digest → Digest → Digest → OracleComp KeccakCalls γ) :
    OracleComp KeccakCalls (γ × (E × E × E)) := do
  let x ← A
  let s₁ ← callKeccak256 (chainIn x.2.1 x.2.2)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let y ← B x.1 s₁ s₂ s₃
  let s₄ ← callKeccak256 (chainIn s₃ y.2)
  let z ← C x.1 y.1 s₁ s₂ s₃ s₄
  return (z, (chal s₁, chal s₂, chal s₄))

theorem simulateQ_callKeccak256 (x : Bytes) :
    simulateQ ro (callKeccak256 x) = ro (.inl x) := by
  unfold callKeccak256
  exact simulateQ_spec_query _ _

theorem run_staged (chal : Digest → E) (A : OracleComp KeccakCalls (α × Digest × (E × E)))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × (E × E)))
    (C : α → β → Digest → Digest → Digest → Digest → OracleComp KeccakCalls γ) (c₀ : Cache) :
    (simulateQ ro (staged chal A B C)).run c₀ =
      (simulateQ ro A).run c₀ >>= fun p ↦
      (ro (.inl (chainIn p.1.2.1 p.1.2.2))).run p.2 >>= fun q₁ ↦
      (ro (.inl (digestBytes q₁.1))).run q₁.2 >>= fun q₂ ↦
      (ro (.inl (digestBytes q₂.1))).run q₂.2 >>= fun q₃ ↦
      (simulateQ ro (B p.1.1 q₁.1 q₂.1 q₃.1)).run q₃.2 >>= fun y ↦
      (ro (.inl (chainIn q₃.1 y.1.2))).run y.2 >>= fun q₄ ↦
      (simulateQ ro (C p.1.1 y.1.1 q₁.1 q₂.1 q₃.1 q₄.1)).run q₄.2 >>= fun z ↦
      pure ((z.1, (chal q₁.1, chal q₂.1, chal q₄.1)), z.2) := by
  simp only [staged, simulateQ_bind, simulateQ_pure, simulateQ_callKeccak256, StateT.run_bind,
    StateT.run_pure]
  rfl

/-! ## One query -/

theorem card_digest_ennreal : (Fintype.card Digest : ℝ≥0∞) = 2 ^ 256 := by
  rw [LeanVM.Protocol.Compile.Rom.card_digest]
  norm_num

theorem two_pow_256_ne_zero : (2 : ℝ≥0∞) ^ 256 ≠ 0 := by simp

theorem two_pow_256_ne_top : (2 : ℝ≥0∞) ^ 256 ≠ ⊤ := by simp

/-- A fresh hash query is answered uniformly. -/
theorem ro_run_fresh (x : Bytes) (c : Cache) (hc : c (.inl x) = none) :
    (ro (.inl x)).run c = ($ᵗ Digest) >>= fun u ↦ pure (u, c.cacheQuery (.inl x) u) := by
  rw [randomOracle.run_eq, hc]
  rfl

/-- A cached hash query is answered from the cache. -/
theorem ro_run_cached (x : Bytes) (c : Cache) {u : Digest} (hc : c (.inl x) = some u) :
    (ro (.inl x)).run c = pure (u, c) := by
  rw [randomOracle.run_eq, hc]

/-- **A fresh hash query**: the event after it is the average over the uniform answer. -/
theorem prEvent_fresh {δ : Type} (x : Bytes) (c : Cache) (hc : c (.inl x) = none)
    (f : Digest × Cache → ProbComp δ) (q : δ → Prop) :
    Pr{let z ← (ro (.inl x)).run c >>= f}[q z] =
      (∑ u : Digest, Pr{let z ← f (u, c.cacheQuery (.inl x) u)}[q z]) / 2 ^ 256 := by
  rw [ro_run_fresh x c hc, bind_assoc]
  simp only [pure_bind]
  rw [prEvent_bind_eq_sum_fintype]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, card_digest_ennreal]
  rw [← Finset.mul_sum, ENNReal.div_eq_inv_mul]

/-- The event on a value fixed before the last steps. -/
theorem prEvent_final_le {γ' δ : Type} (X : ProbComp (γ' × Cache)) (v : δ) (S : δ → Prop)
    [Decidable (S v)] :
    Pr{let z ← X >>= fun z ↦ pure ((z.1, v), z.2)}[S z.1.2] ≤ if S v then 1 else 0 := by
  split_ifs with h
  · exact prEvent_le_one _
  · refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_)
    rw [mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h

/-- `∑ (if u = a then 1 else 0 + b) / 2^256 = 1 / 2^256 + b`. -/
theorem sum_ite_add_div (a : Digest) (b : ℝ≥0∞) :
    (∑ u : Digest, ((if u = a then 1 else 0) + b)) / 2 ^ 256 = 1 / 2 ^ 256 + b := by
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_digest_ennreal, ENNReal.add_div,
    mul_comm, ENNReal.mul_div_cancel_right two_pow_256_ne_zero two_pow_256_ne_top]

/-! ## The bound -/

section Bound

variable (chal : Digest → E) (Bad : Finset (E × E × E))

/-- The answers `s₄` that put `(chal s₁, chal s₂, chal s₄)` in `Bad`. -/
noncomputable def slice (s₁ s₂ : Digest) : ℝ≥0∞ :=
  ((Finset.univ.filter fun s₄ : Digest ↦ (chal s₁, chal s₂, chal s₄) ∈ Bad).card : ℝ≥0∞)

/-- The `t` query, fresh: the event is the slice's fraction. -/
theorem bound_t (s₁ s₂ s₃ : Digest) (r₂ : E × E) (c : Cache) (hc : c (.inl (chainIn s₃ r₂)) = none)
    (K : Digest → Cache → ProbComp (γ × Cache)) :
    Pr{let z ← ((ro (.inl (chainIn s₃ r₂))).run c >>= fun q₄ ↦ (K q₄.1 q₄.2 >>= fun z ↦
        pure ((z.1, (chal s₁, chal s₂, chal q₄.1)), z.2)))}[z.1.2 ∈ Bad] ≤
      slice chal Bad s₁ s₂ / 2 ^ 256 := by
  rw [prEvent_fresh _ _ hc]
  refine ENNReal.div_le_div_right ?_ _
  calc ∑ u : Digest, Pr{let z ← (K u (c.cacheQuery (.inl (chainIn s₃ r₂)) u) >>= fun w ↦
          pure ((w.1, (chal s₁, chal s₂, chal u)), w.2))}[z.1.2 ∈ Bad]
      ≤ ∑ u : Digest, (if (chal s₁, chal s₂, chal u) ∈ Bad then 1 else 0) :=
        Finset.sum_le_sum fun u _ ↦ prEvent_final_le _ _ (· ∈ Bad)
    _ = slice chal Bad s₁ s₂ := by
        rw [Finset.sum_boole]
        rfl

/-- The quotient root and the `t` query: fresh unless `s₃ = s₀`. -/
theorem bound_B (s₀ s₁ s₂ s₃ : Digest) (c₄ : Cache) (Y : ProbComp ((β × (E × E)) × Cache))
    (hY : ∀ y ∈ support Y, ∀ m, y.2 (.inl m) ≠ none → c₄ (.inl m) ≠ none ∨ Good m)
    (hc₄ : ∀ r₂, c₄ (.inl (chainIn s₃ r₂)) ≠ none → s₃ = s₀)
    (K : β × (E × E) → Digest → Cache → ProbComp (γ × Cache)) :
    Pr{let z ← (Y >>= fun y ↦ ((ro (.inl (chainIn s₃ y.1.2))).run y.2 >>= fun q₄ ↦
        (K y.1 q₄.1 q₄.2 >>= fun w ↦
          pure ((w.1, (chal s₁, chal s₂, chal q₄.1)), w.2))))}[z.1.2 ∈ Bad] ≤
      (if s₃ = s₀ then 1 else 0) + slice chal Bad s₁ s₂ / 2 ^ 256 := by
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun y hy ↦ ?_
  by_cases h : s₃ = s₀
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact (prEvent_le_one _).trans le_self_add
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), zero_add]
    have hfresh : y.2 (.inl (chainIn s₃ y.1.2)) = none := by
      by_contra hne
      rcases hY y hy _ hne with h' | h'
      · exact h (hc₄ _ h')
      · exact not_good_chainIn _ _ h'
    exact bound_t chal Bad s₁ s₂ s₃ y.1.2 y.2 hfresh (K y.1)

/-- The `γ` query: fresh unless `s₂ = s₁`. -/
theorem bound_γ (s₀ s₁ s₂ : Digest) (c₃ : Cache)
    (hfresh : s₂ ≠ s₁ → c₃ (.inl (digestBytes s₂)) = none)
    (K : Digest × Cache → ProbComp ((γ × (E × E × E)) × Cache))
    (hK : ∀ s₃, Pr{let z ← K (s₃, c₃.cacheQuery (.inl (digestBytes s₂)) s₃)}[z.1.2 ∈ Bad] ≤
      (if s₃ = s₀ then 1 else 0) + slice chal Bad s₁ s₂ / 2 ^ 256) :
    Pr{let z ← ((ro (.inl (digestBytes s₂))).run c₃ >>= K)}[z.1.2 ∈ Bad] ≤
      (if s₂ = s₁ then 1 else 0) + (1 / 2 ^ 256 + slice chal Bad s₁ s₂ / 2 ^ 256) := by
  by_cases h : s₂ = s₁
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact (prEvent_le_one _).trans le_self_add
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), zero_add, prEvent_fresh _ _ (hfresh h), ← sum_ite_add_div s₀]
    exact ENNReal.div_le_div_right (Finset.sum_le_sum fun s₃ _ ↦ hK s₃) _

/-- `∑ (if u = a then 1 else 0 + (1/2^256 + f u / 2^256)) / 2^256`. -/
theorem sum_β_div (a : Digest) (f : Digest → ℝ≥0∞) :
    (∑ u : Digest, ((if u = a then 1 else 0) + (1 / 2 ^ 256 + f u / 2 ^ 256))) / 2 ^ 256 =
      2 / 2 ^ 256 + (∑ u : Digest, f u) / 2 ^ 256 / 2 ^ 256 := by
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_add_distrib]
  simp only [Finset.mem_univ, ite_true]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_digest_ennreal,
    ENNReal.mul_div_cancel two_pow_256_ne_zero two_pow_256_ne_top, ← ENNReal.sum_div,
    ← add_assoc, one_add_one_eq_two, ENNReal.add_div]

/-- The `β` query: fresh. -/
theorem bound_β (s₁ : Digest) (c₂ : Cache) (hc₂ : c₂ (.inl (digestBytes s₁)) = none)
    (K : Digest × Cache → ProbComp ((γ × (E × E × E)) × Cache))
    (hK : ∀ s₂, Pr{let z ← K (s₂, c₂.cacheQuery (.inl (digestBytes s₁)) s₂)}[z.1.2 ∈ Bad] ≤
      (if s₂ = s₁ then 1 else 0) + (1 / 2 ^ 256 + slice chal Bad s₁ s₂ / 2 ^ 256)) :
    Pr{let z ← ((ro (.inl (digestBytes s₁))).run c₂ >>= K)}[z.1.2 ∈ Bad] ≤
      2 / 2 ^ 256 + (∑ s₂, slice chal Bad s₁ s₂) / 2 ^ 256 / 2 ^ 256 := by
  rw [prEvent_fresh _ _ hc₂, ← sum_β_div s₁]
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun s₂ _ ↦ hK s₂) _

/-- `∑ (2/2^256 + g u / 2^256 / 2^256) / 2^256`. -/
theorem sum_α_div (g : Digest → ℝ≥0∞) :
    (∑ u : Digest, (2 / 2 ^ 256 + g u / 2 ^ 256 / 2 ^ 256)) / 2 ^ 256 =
      2 / 2 ^ 256 + (∑ u : Digest, g u) / 2 ^ 256 / 2 ^ 256 / 2 ^ 256 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_digest_ennreal, ENNReal.mul_div_cancel two_pow_256_ne_zero two_pow_256_ne_top,
    ← ENNReal.sum_div, ← ENNReal.sum_div, ENNReal.add_div]

/-- The `α` query: fresh. -/
theorem bound_α (x : Bytes) (c₁ : Cache) (hc₁ : c₁ (.inl x) = none)
    (K : Digest × Cache → ProbComp ((γ × (E × E × E)) × Cache))
    (hK : ∀ s₁, Pr{let z ← K (s₁, c₁.cacheQuery (.inl x) s₁)}[z.1.2 ∈ Bad] ≤
      2 / 2 ^ 256 + (∑ s₂, slice chal Bad s₁ s₂) / 2 ^ 256 / 2 ^ 256) :
    Pr{let z ← ((ro (.inl x)).run c₁ >>= K)}[z.1.2 ∈ Bad] ≤
      2 / 2 ^ 256 + (∑ s₁, ∑ s₂, slice chal Bad s₁ s₂) / 2 ^ 256 / 2 ^ 256 / 2 ^ 256 := by
  rw [prEvent_fresh _ _ hc₁, ← sum_α_div]
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun s₁ _ ↦ hK s₁) _

end Bound

/-! ## Counting -/

/-- **A regular challenge map**: each challenge is the image of at most `2^64` digests (the low
192 bits of a 256-bit digest). -/
def Regular (chal : Digest → E) : Prop :=
  ∀ e : E, (Finset.univ.filter fun d : Digest ↦ chal d = e).card ≤ 2 ^ 64

theorem card_triples_le (chal : Digest → E) (hreg : Regular chal) (Bad : Finset (E × E × E)) :
    (Finset.univ.filter fun x : Digest × Digest × Digest ↦
      (chal x.1, chal x.2.1, chal x.2.2) ∈ Bad).card ≤ 2 ^ 192 * Bad.card := by
  classical
  set S := Finset.univ.filter fun x : Digest × Digest × Digest ↦
    (chal x.1, chal x.2.1, chal x.2.2) ∈ Bad
  let f : Digest × Digest × Digest → E × E × E := fun x ↦ (chal x.1, chal x.2.1, chal x.2.2)
  have himg : S.image f ⊆ Bad := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hx).2
  refine (Finset.card_le_mul_card_image S (2 ^ 192) fun e _ ↦ ?_).trans
    (Nat.mul_le_mul_left _ (Finset.card_le_card himg))
  have hsub : S.filter (fun x ↦ f x = e) ⊆
      (Finset.univ.filter fun d : Digest ↦ chal d = e.1) ×ˢ
        ((Finset.univ.filter fun d : Digest ↦ chal d = e.2.1) ×ˢ
          (Finset.univ.filter fun d : Digest ↦ chal d = e.2.2)) := by
    intro x hx
    have hfx := (Finset.mem_filter.mp hx).2
    simp only [f, Prod.ext_iff] at hfx
    simp [hfx.1, hfx.2.1, hfx.2.2]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_product]
  calc _ ≤ 2 ^ 64 * (2 ^ 64 * 2 ^ 64) :=
        Nat.mul_le_mul (hreg _) (Nat.mul_le_mul (hreg _) (hreg _))
    _ = 2 ^ 192 := by norm_num

theorem sum_slice_le (chal : Digest → E) (hreg : Regular chal) (Bad : Finset (E × E × E)) :
    (∑ s₁ : Digest, ∑ s₂ : Digest, slice chal Bad s₁ s₂) ≤ 2 ^ 192 * (Bad.card : ℝ≥0∞) := by
  classical
  have hN : (∑ s₁ : Digest, ∑ s₂ : Digest,
      (Finset.univ.filter fun s₄ : Digest ↦ (chal s₁, chal s₂, chal s₄) ∈ Bad).card) =
      (Finset.univ.filter fun x : Digest × Digest × Digest ↦
        (chal x.1, chal x.2.1, chal x.2.2) ∈ Bad).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s₁ _ ↦ ?_
    rw [Fintype.sum_prod_type]
  have h := card_triples_le chal hreg Bad
  rw [← hN] at h
  unfold slice
  exact_mod_cast h

/-! ## The bound on the chain's challenges -/

/-- **The reduction's challenges in the random-oracle model.** For a computation of the chain's
shape (`staged`) whose stages before `α` and between `γ` and `t` hash only inputs of other
lengths than `32` and `96` (`HashOK Good`), run from a cache holding no such input, with a regular
challenge map: the triple `(α, β, t)` lies in `Bad` with probability at most
`2 / 2^256 + |Bad| / 2^576`. -/
theorem prEvent_staged_le (chal : Digest → E) (hreg : Regular chal) (Bad : Finset (E × E × E))
    (A : OracleComp KeccakCalls (α × Digest × (E × E)))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × (E × E)))
    (C : α → β → Digest → Digest → Digest → Digest → OracleComp KeccakCalls γ)
    (hA : HashOK Good A) (hB : ∀ a s₁ s₂ s₃, HashOK Good (B a s₁ s₂ s₃)) (c₀ : Cache)
    (hc₀ : ∀ m, c₀ (.inl m) ≠ none → Good m) :
    Pr{let z ← (simulateQ ro (staged chal A B C)).run c₀}[z.1.2 ∈ Bad] ≤
      2 / 2 ^ 256 + (Bad.card : ℝ≥0∞) / 2 ^ 576 := by
  have hfin : (∑ s₁ : Digest, ∑ s₂ : Digest, slice chal Bad s₁ s₂) / 2 ^ 256 / 2 ^ 256 / 2 ^ 256 ≤
      (Bad.card : ℝ≥0∞) / 2 ^ 576 := by
    have e : (Bad.card : ℝ≥0∞) / 2 ^ 576 * 2 ^ 256 * 2 ^ 256 * 2 ^ 256 =
        2 ^ 192 * (Bad.card : ℝ≥0∞) := by
      rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add,
        show (2 : ℝ≥0∞) ^ (256 + (256 + 256)) = 2 ^ 576 * 2 ^ 192 by rw [← pow_add], ← mul_assoc,
        ENNReal.div_mul_cancel (by simp) (by simp), mul_comm]
    refine ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul ?_))
    rw [e]
    exact sum_slice_le chal hreg Bad
  refine le_trans ?_ (add_le_add le_rfl hfin)
  rw [run_staged]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  have hc₁ : ∀ m, p.2 (.inl m) ≠ none → Good m := fun m hm ↦
    (cache_of_hashOK hA c₀ hp m hm).elim (hc₀ m) id
  have f₁ : p.2 (.inl (chainIn p.1.2.1 p.1.2.2)) = none := by
    by_contra h
    exact not_good_chainIn _ _ (hc₁ _ h)
  refine bound_α chal Bad _ p.2 f₁ _ fun s₁ ↦ ?_
  have f₂ : (p.2.cacheQuery (.inl (chainIn p.1.2.1 p.1.2.2)) s₁) (.inl (digestBytes s₁)) =
      none := by
    rw [QueryCache.cacheQuery_of_ne _ _
      (Sum.inl_injective.ne (chainIn_ne_digestBytes _ _ _).symm)]
    by_contra h
    exact not_good_digestBytes _ (hc₁ _ h)
  refine bound_β chal Bad s₁ _ f₂ _ fun s₂ ↦ ?_
  refine bound_γ chal Bad p.1.2.1 s₁ s₂ _ (fun hne ↦ ?_) _ fun s₃ ↦ ?_
  · rw [QueryCache.cacheQuery_of_ne _ _
        (Sum.inl_injective.ne fun h ↦ hne (digestBytes_injective h)),
      QueryCache.cacheQuery_of_ne _ _
        (Sum.inl_injective.ne (chainIn_ne_digestBytes _ _ _).symm)]
    by_contra h
    exact not_good_digestBytes _ (hc₁ _ h)
  · refine bound_B chal Bad p.1.2.1 s₁ s₂ s₃ _ _
      (fun y hy m hm ↦ cache_of_hashOK (hB _ _ _ _) _ hy m hm) (fun r₂ h ↦ ?_)
      (fun yb s₄ c ↦ (simulateQ ro (C p.1.1 yb.1 s₁ s₂ s₃ s₄)).run c)
    rw [QueryCache.cacheQuery_of_ne _ _
        (Sum.inl_injective.ne (chainIn_ne_digestBytes _ _ _)),
      QueryCache.cacheQuery_of_ne _ _
        (Sum.inl_injective.ne (chainIn_ne_digestBytes _ _ _))] at h
    by_cases hx : chainIn s₃ r₂ = chainIn p.1.2.1 p.1.2.2
    · exact chainIn_left hx
    · rw [QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at h
      exact absurd (hc₁ _ h) (not_good_chainIn _ _)

end E2ECompleteness
