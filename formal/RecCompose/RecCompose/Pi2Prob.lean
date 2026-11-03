-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `formal/UniComplete/UniComplete/ProbChain.lean`
-- (`staged5`, `prEvent_staged5_le`) and `ProbStaged.lean` (`UniStaged`, `UniStaged.Holds`, `prEvent_run_false_le`) for
-- π2's transcript (`crates/leanvm_rec/src/pi2/prover.rs`: `α, β, γ` after `W`'s root, `t` after `Q`'s); uses their hash
-- discipline (`HashOK`, `GoodL`, `prEvent_query_le`, `sum_bad_le`, `prEvent_tquery_le`), `E2ECompleteness`'s transfer
-- (`rpm_le_rom`) and leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0): the two calls `KeccakCalls`, their lazy random oracles, `rpmError`, `DuplexVm`, `hashBlocks`.
import UniComplete.ProbStaged
import RecStatement.Security

/-!
# π2's challenges in the random-oracle model, and its completeness from the staged experiment

π2's honest prover (and the contract, `reduceWith`) draws `α, β, γ` right after `W`'s root as three chained Keccak-256
answers: `s₁ = H(x)` with `x` the state and everything read since the seed (π1's public data and `W`'s root: `536`
bytes on the real circuit, `2 · 32 + 17 · 24 + 32` after the `32`-byte state), then `s₂ = H(s₁)`, `s₃ = H(s₂)`
(`32` bytes each); `α = chal s₁`, `β = chal s₂`, `γ = chal s₃`. Then `Q`'s root and `t = chal(H(s₃ ‖ Q's root))`
(`64` bytes, a Merkle node's length). The copy argument's bad challenges (a vanishing pull, push or public denominator,
`RecPiop.Circuit.dPull`, `dPush`, `dPub`) are of three kinds: values of `α` (a denominator whose tag is `ω_0 = 0`),
values of `β` given `α`, values of `γ` given `α, β` (a four-limb port's fingerprint is linear in `γ`); `t`'s
(`t ∈ V_{m+2}`, `c_h + c_q = 0`) depend on everything before `t`.

* **`prEvent_staged3_le`**: for a computation of the chain's shape (`staged3`) whose stage before the first input
  hashes only inputs of other lengths than `32` and `L` (`HashOK (GoodL L)`), the first input of length `L ≠ 32`, and
  bad sets of at most `N₁` values of `α`, `N₂` of `β` for each `α`, `N₃` of `γ` for each `α, β` (all depending on a
  prior `pr a` of the first stage, the witness and the public data), the bad event has probability at most
  `1 / 2^256 + (N₁ + N₂ + N₃) / 2^192`: `s₁` and `s₂` are fresh by their lengths, `s₃` but for `s₂ = s₁`.
* **`Pi2Staged`, `Pi2Staged.Holds`**: π2's completeness experiment as a two-call computation of that shape, then `t`,
  then the rest, its output the experiment's pair (π1-rec3's graph's verdict, the contract's); the code-level bridge
  (`experiment`, `duplex`, `cost`, `hashA`), the bad sets' counts, `t`'s cache hit `εt` and the rejection at good
  challenges `εpow` (the proofs of work).
* **`prEvent_staged_bad_le`**, **`recCompleteness2_of_staged`**: `RecCompleteness2 D P1 P2 δ2` with
  `δ2 = (N₁ + N₂ + N₃) / 2^192 + 1 / 2^256 + (ct / 2^192 + εt) + εpow + rpmError N`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK hashOK cache_of_hashOK prEvent_fresh prEvent_final_le Regular
  card_digest_ennreal two_pow_256_ne_zero two_pow_256_ne_top length_digestBytes simulateQ_callKeccak256)
open UniComplete.Prob (GoodL prEvent_query_le sum_const_div sum_mem_le sum_bad_le Inv fresh_first inv_first fresh_inv
  inv_cons prEvent_tquery_le)
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.Pi2P

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The chain's shape -/

section Shape

variable {α ρ γ : Type}

/-- **`α, β, γ`'s shape**: `A` up to the first input `inp a`; `s₁ = H(inp a)`, `s₂ = H(s₁)`, `s₃ = H(s₂)`; `C` the
rest. Its output carries the prior `pr a` and `(chal s₁, chal s₂, chal s₃)`. -/
def staged3 (chal : Digest → E) (inp : α → Bytes) (pr : α → ρ) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → OracleComp KeccakCalls γ) :
    OracleComp KeccakCalls (γ × (ρ × E × E × E)) := do
  let a ← A
  let s₁ ← callKeccak256 (inp a)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let z ← C a s₁ s₂ s₃
  return (z, (pr a, chal s₁, chal s₂, chal s₃))

theorem run_staged3 (chal : Digest → E) (inp : α → Bytes) (pr : α → ρ) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → OracleComp KeccakCalls γ) (c₀ : Cache) :
    (simulateQ ro (staged3 chal inp pr A C)).run c₀ =
      (simulateQ ro A).run c₀ >>= fun p ↦
      (ro (.inl (inp p.1))).run p.2 >>= fun q₁ ↦
      (ro (.inl (digestBytes q₁.1))).run q₁.2 >>= fun q₂ ↦
      (ro (.inl (digestBytes q₂.1))).run q₂.2 >>= fun q₃ ↦
      (simulateQ ro (C p.1 q₁.1 q₂.1 q₃.1)).run q₃.2 >>= fun z ↦
      pure ((z.1, (pr p.1, chal q₁.1, chal q₂.1, chal q₃.1)), z.2) := by
  simp only [staged3, simulateQ_bind, simulateQ_pure, simulateQ_callKeccak256, StateT.run_bind,
    StateT.run_pure]
  rfl

end Shape

/-! ## The bound -/

/-- **A bad challenge's step**: the average over the answer of its bad set's indicator plus the rest. -/
theorem sum_bad_step_le (chal : Digest → E) (hreg : Regular chal) (bad : E → Prop) [DecidablePred bad] (N : ℕ)
    (hbad : ∃ T : Finset E, T.card ≤ N ∧ ∀ b, bad b → b ∈ T) (f : Digest → ℝ≥0∞) (B : ℝ≥0∞)
    (hf : ∀ u, f u ≤ B) :
    (∑ u : Digest, ((if bad (chal u) then 1 else 0) + f u)) / 2 ^ 256 ≤ (N : ℝ≥0∞) / 2 ^ 192 + B := by
  rw [Finset.sum_add_distrib, ENNReal.add_div]
  refine add_le_add (sum_bad_le chal hreg bad N hbad) ?_
  calc (∑ u : Digest, f u) / 2 ^ 256 ≤ (∑ _u : Digest, B) / 2 ^ 256 :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hf u) _
    _ = B := sum_const_div B

/-- **`α, β, γ` in the random-oracle model.** For a computation of the chain's shape (`staged3`) whose stage before
the first input hashes only inputs of other lengths than `32` and `L` (`HashOK (GoodL L)`), the first input of length
`L ≠ 32`, run from a cache holding no such input, with a regular challenge map and bad sets of at most `N₁` values of
`α`, `N₂` of `β` for each `α`, `N₃` of `γ` for each `(α, β)` (each depending on the prior): the bad event has
probability at most `1 / 2^256 + (N₁ + N₂ + N₃) / 2^192`. -/
theorem prEvent_staged3_le {α ρ γ : Type} (chal : Digest → E) (hreg : Regular chal) {L : ℕ} (hL : L ≠ 32)
    (bad1 : ρ → E → Prop) (bad2 : ρ → E → E → Prop) (bad3 : ρ → E → E → E → Prop) (N₁ N₂ N₃ : ℕ)
    (h1 : ∀ p, ∃ T : Finset E, T.card ≤ N₁ ∧ ∀ a, bad1 p a → a ∈ T)
    (h2 : ∀ p a, ∃ T : Finset E, T.card ≤ N₂ ∧ ∀ b, bad2 p a b → b ∈ T)
    (h3 : ∀ p a b, ∃ T : Finset E, T.card ≤ N₃ ∧ ∀ c, bad3 p a b c → c ∈ T)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = L) (pr : α → ρ) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → OracleComp KeccakCalls γ)
    (hA : HashOK (GoodL L) A) (c₀ : Cache) (hc₀ : ∀ m, c₀ (.inl m) ≠ none → GoodL L m) :
    Pr{let z ← (simulateQ ro (staged3 chal inp pr A C)).run c₀}[
      bad1 z.1.2.1 z.1.2.2.1 ∨ bad2 z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 ∨
        bad3 z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2] ≤
      1 / 2 ^ 256 + ((N₁ + N₂ + N₃ : ℕ) : ℝ≥0∞) / 2 ^ 192 := by
  classical
  rw [run_staged3]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  have hc₁ : ∀ m, p.2 (.inl m) ≠ none → GoodL L m := fun m hm ↦
    (cache_of_hashOK hA c₀ hp m hm).elim (hc₀ m) id
  set P := pr p.1
  -- the bounds after each answer
  set B₃ : ℝ≥0∞ := (N₃ : ℝ≥0∞) / 2 ^ 192
  set B₂ : ℝ≥0∞ := 1 / 2 ^ 256 + ((N₂ : ℝ≥0∞) / 2 ^ 192 + B₃)
  -- `s₁`: fresh.
  refine (prEvent_query_le _ _ False (fun _ ↦ fresh_first hc₁ (hinp p.1)) _ _
    (fun s₁ ↦ (if bad1 P (chal s₁) then 1 else 0) + B₂) fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    refine (sum_bad_step_le chal hreg (bad1 P) N₁ (h1 P) (fun _ ↦ B₂) B₂ fun _ ↦ le_rfl).trans (le_of_eq ?_)
    simp only [B₂, B₃, Nat.cast_add, ENNReal.add_div]
    ring
  have i₁ := inv_first hc₁ (inp p.1) (hinp p.1) s₁
  by_cases hb1 : bad1 P (chal s₁)
  · simp only [hb1, ↓reduceIte]
    exact (prEvent_le_one _).trans le_self_add
  simp only [hb1, ↓reduceIte, zero_add]
  -- `s₂`: fresh (`s₁ ∉ []`).
  refine (prEvent_query_le _ _ (s₁ ∈ ([] : List Digest)) (fun hs ↦ fresh_inv hL i₁ hs) _ _
    (fun s₂ ↦ (if s₂ ∈ [s₁] then 1 else 0) + ((if bad2 P (chal s₁) (chal s₂) then 1 else 0) + B₃))
    fun s₂ ↦ ?_).trans ?_
  rotate_left
  · simp only [List.not_mem_nil, ↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div]
    refine add_le_add ((ENNReal.div_le_div_right (sum_mem_le [s₁]) _).trans (le_of_eq (by simp))) ?_
    exact sum_bad_step_le chal hreg (bad2 P (chal s₁)) N₂ (h2 P _) (fun _ ↦ B₃) B₃ fun _ ↦ le_rfl
  have i₂ := inv_cons i₁ s₁ s₂
  by_cases hs : s₂ ∈ [s₁]
  · simp only [hs, ↓reduceIte]
    exact (prEvent_le_one _).trans le_self_add
  simp only [hs, ↓reduceIte, zero_add]
  by_cases hb2 : bad2 P (chal s₁) (chal s₂)
  · simp only [hb2, ↓reduceIte]
    exact (prEvent_le_one _).trans le_self_add
  simp only [hb2, ↓reduceIte, zero_add]
  -- `s₃`: fresh unless `s₂ = s₁`; then `γ` lands in its bad set with probability `≤ N₃ / 2^192`.
  refine (prEvent_query_le _ _ (s₂ ∈ [s₁]) (fun hs' ↦ fresh_inv hL i₂ hs') _ _
    (fun s₃ ↦ if bad3 P (chal s₁) (chal s₂) (chal s₃) then 1 else 0) fun s₃ ↦ ?_).trans ?_
  rotate_left
  · simp only [hs, ↓reduceIte, zero_add]
    exact sum_bad_le chal hreg _ N₃ (h3 P _ _)
  refine (prEvent_final_le _ (P, chal s₁, chal s₂, chal s₃)
    (fun v ↦ bad1 v.1 v.2.1 ∨ bad2 v.1 v.2.1 v.2.2.1 ∨ bad3 v.1 v.2.1 v.2.2.1 v.2.2.2)).trans ?_
  by_cases hb3 : bad3 P (chal s₁) (chal s₂) (chal s₃) <;> simp [hb1, hb2, hb3]

/-! ## `t` -/

/-- **The point challenge `t` in the random-oracle model** (`UniComplete.Prob.prEvent_tquery_le` for a prior of any
type): an event forcing `t = chal(answer)` into a bad set of at most `ct` values for each prior has probability at most
the probability that `t`'s input is already cached, plus `ct / 2^192`. -/
theorem prEvent_tquery_le' {β γ ω τ : Type} (chal : Digest → E) (hreg : Regular chal) (badT : τ → E → Prop)
    (ct : ℕ) (hct : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ b, badT fp b → b ∈ T)
    (X : OracleComp KeccakCalls β) (tin : β → Bytes) (pr : β → τ)
    (K : β → Digest → OracleComp KeccakCalls γ) (h : β → Digest → γ → ω) (ev : ω → Prop)
    (hev : ∀ x st z, ev (h x st z) → badT (pr x) (chal st)) (c₀ : Cache) :
    Pr{let z ← (simulateQ ro (X >>= fun x ↦ callKeccak256 (tin x) >>= fun st ↦ K x st >>= fun z ↦
        pure (h x st z))).run c₀}[ev z.1] ≤
      Pr{let p ← (simulateQ ro X).run c₀}[p.2 (.inl (tin p.1)) ≠ none] + (ct : ℝ≥0∞) / 2 ^ 192 := by
  classical
  simp only [simulateQ_bind, simulateQ_callKeccak256, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  refine prEvent_bind_le_prEvent_add_of_support _ _ _ _ fun p _ hp ↦ ?_
  have hfresh : p.2 (.inl (tin p.1)) = none := not_not.mp hp
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

/-! ## `α, β, γ` against a set of triples -/

/-- The answers' triples landing in `T`, counted. -/
theorem sum_triples_le (chal : Digest → E) (hreg : Regular chal) (T : Finset (E × E × E)) :
    (∑ s₁ : Digest, ∑ s₂ : Digest, ∑ s₃ : Digest,
      (if (chal s₁, chal s₂, chal s₃) ∈ T then 1 else 0 : ℝ≥0∞)) ≤ 2 ^ 192 * (T.card : ℝ≥0∞) := by
  classical
  have h := E2ECompleteness.card_triples_le chal hreg T
  have hN : ((Finset.univ.filter fun x : Digest × Digest × Digest ↦
      (chal x.1, chal x.2.1, chal x.2.2) ∈ T).card : ℝ≥0∞) =
      ∑ s₁ : Digest, ∑ s₂ : Digest, ∑ s₃ : Digest, (if (chal s₁, chal s₂, chal s₃) ∈ T then 1 else 0 : ℝ≥0∞) := by
    rw [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s₁ _ ↦ ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s₂ _ ↦ Finset.sum_congr rfl fun s₃ _ ↦ ?_
    split_ifs <;> simp
  rw [← hN]
  exact_mod_cast h

set_option exponentiation.threshold 1024 in
/-- **`α, β, γ` in the random-oracle model, against a set of triples**: for a computation of the chain's shape
(`staged3`) whose stage before the first input hashes only inputs of other lengths than `32` and `L`, the first input
of length `L ≠ 32`, and bad sets of at most `M · |E|²` triples (each depending on the prior), the triple is bad with
probability at most `1 / 2^256 + M / 2^192` (`s₃`'s query repeats `s₂`'s only if `s₂ = s₁`). -/
theorem prEvent_staged3_triple_le {α ρ γ : Type} (chal : Digest → E) (hreg : Regular chal) {L : ℕ} (hL : L ≠ 32)
    (Bad : ρ → Finset (E × E × E)) (M : ℕ) (hM : ∀ p, (Bad p).card ≤ M * 2 ^ 384)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = L) (pr : α → ρ) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → OracleComp KeccakCalls γ)
    (hA : HashOK (GoodL L) A) (c₀ : Cache) (hc₀ : ∀ m, c₀ (.inl m) ≠ none → GoodL L m) :
    Pr{let z ← (simulateQ ro (staged3 chal inp pr A C)).run c₀}[z.1.2.2 ∈ Bad z.1.2.1] ≤
      1 / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192 := by
  classical
  rw [run_staged3]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  have hc₁ : ∀ m, p.2 (.inl m) ≠ none → GoodL L m := fun m hm ↦
    (cache_of_hashOK hA c₀ hp m hm).elim (hc₀ m) id
  set T := Bad (pr p.1) with hT
  set I : Digest → Digest → Digest → ℝ≥0∞ := fun s₁ s₂ s₃ ↦ if (chal s₁, chal s₂, chal s₃) ∈ T then 1 else 0
    with hI
  -- `s₁`: fresh.
  refine (prEvent_query_le _ _ False (fun _ ↦ fresh_first hc₁ (hinp p.1)) _ _
    (fun s₁ ↦ 1 / 2 ^ 256 + (∑ s₂ : Digest, ∑ s₃ : Digest, I s₁ s₂ s₃) / 2 ^ 256 / 2 ^ 256) fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    refine add_le_add le_rfl ?_
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
  have i₁ := inv_first hc₁ (inp p.1) (hinp p.1) s₁
  -- `s₂`: fresh (`s₁ ∉ []`).
  refine (prEvent_query_le _ _ (s₁ ∈ ([] : List Digest)) (fun hs ↦ fresh_inv hL i₁ hs) _ _
    (fun s₂ ↦ (if s₂ ∈ [s₁] then 1 else 0) + (∑ s₃ : Digest, I s₁ s₂ s₃) / 2 ^ 256) fun s₂ ↦ ?_).trans ?_
  rotate_left
  · simp only [List.not_mem_nil, ↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div, ← ENNReal.sum_div]
    exact add_le_add ((ENNReal.div_le_div_right (sum_mem_le [s₁]) _).trans (le_of_eq (by simp))) le_rfl
  have i₂ := inv_cons i₁ s₁ s₂
  by_cases hs : s₂ ∈ [s₁]
  · simp only [hs, ↓reduceIte]
    exact (prEvent_le_one _).trans le_self_add
  simp only [hs, ↓reduceIte, zero_add]
  -- `s₃`: fresh unless `s₂ = s₁`.
  refine (prEvent_query_le _ _ (s₂ ∈ [s₁]) (fun hs' ↦ fresh_inv hL i₂ hs') _ _
    (fun s₃ ↦ I s₁ s₂ s₃) fun s₃ ↦ ?_).trans ?_
  rotate_left
  · simp only [hs, ↓reduceIte, zero_add]
    exact le_rfl
  exact prEvent_final_le _ (pr p.1, chal s₁, chal s₂, chal s₃) (fun v ↦ v.2 ∈ Bad v.1)

/-! ## The staged experiment -/

/-- The challenge map of π2's transcript (`UniStatement.sample`, `PcsQuotient.Transcript.challengeOf`). -/
abbrev chalP (d : Digest) : E := PcsQuotient.Transcript.challengeOf d

/-- **π2's completeness experiment's stages** (no coins): `A` up to `α`'s input (`inp`; the setup, π1's prover,
π1-rec3's graph's check, π2's prover up to `W`'s root; `pr` the prior the copy argument's bad sets depend on), the
three chained answers, `B` up to `t`'s input (`tin`; `prT` the prior `t`'s bad set depends on), `t`'s answer, `C` the
rest (π2's tail and openings, the contract), its output the experiment's pair: π1-rec3's graph's verdict, the
contract's. -/
structure Pi2Staged where
  α : Type
  β : Type
  ρ : Type
  τ : Type
  inp : α → Bytes
  pr : α → ρ
  A : OracleComp KeccakCalls α
  B : α → Digest → Digest → Digest → OracleComp KeccakCalls β
  tin : β → Bytes
  prT : β → τ
  C : β → Digest → OracleComp KeccakCalls (Bool × Bool)

/-- After `α, β, γ`: `B`, `t`'s query, `C`; the pair and `(prT b, t)`. -/
def Pi2Staged.tail (S : Pi2Staged) (a : S.α) (s₁ s₂ s₃ : Digest) :
    OracleComp KeccakCalls ((Bool × Bool) × (S.τ × E)) := do
  let b ← S.B a s₁ s₂ s₃
  let st ← callKeccak256 (S.tin b)
  let z ← S.C b st
  return (z, (S.prT b, chalP st))

/-- The two-call run: the pair with `t`'s stage, and `(pr a, α, β, γ)`. -/
def Pi2Staged.run (S : Pi2Staged) :
    OracleComp KeccakCalls (((Bool × Bool) × (S.τ × E)) × (S.ρ × E × E × E)) :=
  staged3 chalP S.inp S.pr S.A S.tail

/-- **The run up to `t`'s query**: `B`'s output and `(pr a, α, β, γ)`. -/
def Pi2Staged.pre (S : Pi2Staged) : OracleComp KeccakCalls (S.β × (S.ρ × E × E × E)) := do
  let a ← S.A
  let s₁ ← callKeccak256 (S.inp a)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let b ← S.B a s₁ s₂ s₃
  return (b, (S.pr a, chalP s₁, chalP s₂, chalP s₃))

/-- **The run, cut at `t`.** -/
theorem Pi2Staged.run_eq_pre (S : Pi2Staged) :
    S.run = S.pre >>= fun x ↦ callKeccak256 (S.tin x.1) >>= fun st ↦ S.C x.1 st >>= fun z ↦
      pure ((z, (S.prT x.1, chalP st)), x.2) := by
  simp only [Pi2Staged.run, staged3, Pi2Staged.tail, Pi2Staged.pre, bind_assoc, pure_bind]

/-- **The code-level bridge** of π2's completeness experiment for `(input, rows, q)`: `α`'s input of `L ≠ 32` bytes,
bad sets of at most `M · |E|²` triples `(α, β, γ)` and `ct` values of `t` (each per prior), `N` block calls, `t`'s
cache-hit probability `εt` and the rejection at good challenges `εpow`. -/
structure Pi2Staged.Holds (S : Pi2Staged) (D : RecStatement.RecDeployment) (P1 : RecStatement.Pi1Prover D)
    (P2 : RecStatement.Pi2Prover) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (L : ℕ) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop) (M ct N : ℕ) (εt εpow : ℝ≥0∞) : Prop where
  /-- The experiment is the pair of the two-call run against the random permutation. -/
  experiment : RecStatement.recCompletenessExperiment2 D P1 P2 input rows q =
    (fun z ↦ z.1.1) <$> (simulateQ keccakCallsOverRandomPermutation S.run).run' []
  /-- Every permutation call continues a duplex or starts one (`DuplexVm`). -/
  duplex : DuplexVm S.run []
  /-- At most `N` block calls (`hashBlocks`). -/
  cost : Common.QueryCostAtMost S.run hashBlocks N
  /-- `α`'s input has `L` bytes, `L ≠ 32`. -/
  L_ne : L ≠ 32
  inp_length : ∀ a, (S.inp a).length = L
  /-- Before it, nothing of the chain's lengths (`32`, `L`) is hashed. -/
  hashA : HashOK (GoodL L) S.A
  /-- The copy argument's bad triples' count. -/
  badCard : ∀ p, (Bad p).card ≤ M * 2 ^ 384
  /-- At most `ct` bad values of `t` for each prior. -/
  badTCard : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ t, badT fp t → t ∈ T
  /-- `t`'s input is already hashed before its query with probability at most `εt`. -/
  tFresh : Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none] ≤ εt
  /-- **Grinding**: in the two-call random-oracle model, π1-rec3's graph accepting, the contract rejects π2's honest
  proof at good challenges with probability at most `εpow`. -/
  rejectGood : Pr{let z ← (simulateQ ro S.run).run' ∅}[
    z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ Bad z.2.1 ∧ ¬ badT z.1.2.1 z.1.2.2] ≤ εpow

/-- π2's completeness error from the staged experiment's numbers. -/
noncomputable def deltaStaged (M ct N : ℕ) (εt εpow : ℝ≥0∞) : ℝ≥0∞ :=
  (1 / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) + (εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow + rpmError N

/-- **One statement**: the graph accepting and the contract rejecting has probability at most the copy argument's,
`t`'s, the grinding's and the transfer's errors. -/
theorem prEvent_staged_bad_le (S : Pi2Staged) {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {input : Vector UInt8 32} {rows : List ℕ} {q : D.pi1.Stack rows} {L : ℕ}
    {Bad : S.ρ → Finset (E × E × E)} {badT : S.τ → E → Prop} {M ct N : ℕ} {εt εpow : ℝ≥0∞}
    (h : S.Holds D P1 P2 input rows q L Bad badT M ct N εt εpow) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1.1 = true ∧ z.1.1.2 = false] ≤
      deltaStaged M ct N εt εpow := by
  refine E2ECompleteness.rpm_le_rom S.run h.duplex h.cost (fun z ↦ z.1.1.1 = true ∧ z.1.1.2 = false) ?_
  -- `α, β, γ`.
  have hab : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.2.2 ∈ Bad z.2.1] ≤ 1 / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_staged3_triple_le chalP E2ECompleteness.challengeOf_regular h.L_ne Bad M h.badCard S.inp
      h.inp_length S.pr S.A S.tail h.hashA ∅ fun m hm ↦ absurd rfl hm
  -- `t`.
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
  calc _ ≤ (1 / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) + ((εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow) :=
        add_le_add hab (add_le_add ht h.rejectGood)
    _ = _ := by ac_rfl

/-- **`RecCompleteness2` in the random-permutation model, from the staged experiment**: if for every honest statement
π2's completeness experiment is the pair of a two-call computation of `α, β, γ`'s and `t`'s shape (`Pi2Staged.Holds`),
then `RecCompleteness2 D P1 P2 (deltaStaged …)`. -/
theorem recCompleteness2_of_staged {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {L M ct N : ℕ} {εt εpow : ℝ≥0∞}
    (hS : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
      D.pi1.HonestRelation rows input q →
      ∃ (S : Pi2Staged) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop),
        S.Holds D P1 P2 input rows q L Bad badT M ct N εt εpow) :
    RecStatement.RecCompleteness2 D P1 P2 (deltaStaged M ct N εt εpow) := by
  intro input rows q hfit hrel
  obtain ⟨S, Bad, badT, h⟩ := hS input rows q hfit hrel
  rw [h.experiment, prEvent_map]
  exact prEvent_staged_bad_le S h

end RecCompose.Pi2P

/-- info: 'RecCompose.Pi2P.prEvent_staged3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged3_le

/-- info: 'RecCompose.Pi2P.prEvent_staged3_triple_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged3_triple_le

/-- info: 'RecCompose.Pi2P.prEvent_staged_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged_bad_le

/-- info: 'RecCompose.Pi2P.recCompleteness2_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.recCompleteness2_of_staged
