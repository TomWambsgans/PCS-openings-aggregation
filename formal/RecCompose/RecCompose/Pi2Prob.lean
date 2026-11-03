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

end RecCompose.Pi2P

/-- info: 'RecCompose.Pi2P.prEvent_staged3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged3_le
