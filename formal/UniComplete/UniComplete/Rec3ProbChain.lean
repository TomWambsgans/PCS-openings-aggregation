-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's analogue of `ProbChain.lean`'s
-- `prEvent_staged5_le` (the main line's five chained bus answers), for π1-rec3's two; uses `ProbChain.lean`'s lemmas
-- and `formal/EndToEnd/Completeness/E2ECompleteness/Chain.lean`'s (`prEvent_final_le`, `cache_of_hashOK`), and leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls` and their lazy random oracles.
import UniComplete.ProbChain

/-!
# π1-rec3's bus challenges in the random-oracle model

Right after `C1`'s root π1-rec3's prover (`drawRunW … 4`, `sampleW`) and verifier (`drawRunH .rec3 4`) draw the bus
challenges as **two** chained Keccak-256 answers: `s₁ = H(x)` with `x` the state, the six row counts and `C1`'s root
word (`88` bytes), `α = squares (chal s₁) 4 = (c, c², c⁴, c⁸)`; then `s₂ = H(s₁)` (`32` bytes), `β = chal s₂`.

**`prEvent_staged2_le`**: for a computation of this shape (`staged2 chal alphaOf inp A C`: `A` up to the first input
`inp a` of length `L ≠ 32`, the two answers, `C` anything) whose `A` hashes only inputs of other lengths than `32`
and `L` (`GoodL L`), from a cache with no such input, and a bad set with at most `Nbad` values of `β` for each `α`,
the bad event has probability at most

  `Nbad / 2^192`,

for any challenge map whose fibres have at most `2^64` digests (`Regular`). **No repetition term**: `s₂`'s input is
`32` bytes and the cache before it holds only inputs of other lengths (`GoodL L`) and the first input (`L ≠ 32`), so
it is always fresh; the main line's `6 / 2^256` came from `s₃, s₄, s₅`'s inputs possibly repeating an earlier
`32`-byte one.

Decisions: `α` is any function `alphaOf` of the first answer (π1-rec3's is `squares (chal s₁) 4`, `Rec3ProbStaged`);
the bad event and its count are `ProbChain.lean`'s (`bad : List E → E → Prop`, `∃ T, |T| ≤ Nbad` for every `α`); the
first query's freshness is used only to carry the cache's invariant (`Inv`, `inv_first`) to `s₂`'s query.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK cache_of_hashOK prEvent_final_le Regular simulateQ_callKeccak256)
open UniComplete.Prob (GoodL prEvent_query_le sum_const_div sum_bad_le fresh_first inv_first fresh_inv)
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Rec3

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The chain's shape -/

section Shape

variable {α γ : Type}

/-- **π1-rec3's bus challenges' shape**: `A` up to the first input `inp a`; `s₁ = H(inp a)`, `s₂ = H(s₁)`; `C` the
rest. Its output carries `(alphaOf s₁, chal s₂)`, π1-rec3's `(α, β)` when `alphaOf s = squares (chal s) 4`. -/
def staged2 (chal : Digest → E) (alphaOf : Digest → List E) (inp : α → Bytes) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → OracleComp KeccakCalls γ) : OracleComp KeccakCalls (γ × (List E × E)) := do
  let a ← A
  let s₁ ← callKeccak256 (inp a)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let z ← C a s₁ s₂
  return (z, (alphaOf s₁, chal s₂))

theorem run_staged2 (chal : Digest → E) (alphaOf : Digest → List E) (inp : α → Bytes)
    (A : OracleComp KeccakCalls α) (C : α → Digest → Digest → OracleComp KeccakCalls γ) (c₀ : Cache) :
    (simulateQ ro (staged2 chal alphaOf inp A C)).run c₀ =
      (simulateQ ro A).run c₀ >>= fun p ↦
      (ro (.inl (inp p.1))).run p.2 >>= fun q₁ ↦
      (ro (.inl (digestBytes q₁.1))).run q₁.2 >>= fun q₂ ↦
      (simulateQ ro (C p.1 q₁.1 q₂.1)).run q₂.2 >>= fun z ↦
      pure ((z.1, (alphaOf q₁.1, chal q₂.1)), z.2) := by
  simp only [staged2, simulateQ_bind, simulateQ_pure, simulateQ_callKeccak256, StateT.run_bind,
    StateT.run_pure]
  rfl

end Shape

/-! ## The bound -/

/-- **π1-rec3's bus challenges in the random-oracle model.** For a computation of the two-answer chain's shape
(`staged2`) whose stage before the first input hashes only inputs of other lengths than `32` and `L`
(`HashOK (GoodL L)`), the first input of length `L ≠ 32`, run from a cache holding no such input, with a regular
challenge map and a bad set of at most `Nbad` values of `β` for each `α`: the bad event has probability at most
`Nbad / 2^192` (`s₂`'s `32`-byte query is always fresh). -/
theorem prEvent_staged2_le {α γ : Type} (chal : Digest → E) (hreg : Regular chal) (alphaOf : Digest → List E)
    {L : ℕ} (hL : L ≠ 32) (bad : List E → E → Prop) (Nbad : ℕ)
    (hbad : ∀ as, ∃ T : Finset E, T.card ≤ Nbad ∧ ∀ b, bad as b → b ∈ T)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = L) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → OracleComp KeccakCalls γ)
    (hA : HashOK (GoodL L) A) (c₀ : Cache) (hc₀ : ∀ m, c₀ (.inl m) ≠ none → GoodL L m) :
    Pr{let z ← (simulateQ ro (staged2 chal alphaOf inp A C)).run c₀}[bad z.1.2.1 z.1.2.2] ≤
      (Nbad : ℝ≥0∞) / 2 ^ 192 := by
  classical
  set B : ℝ≥0∞ := (Nbad : ℝ≥0∞) / 2 ^ 192
  rw [run_staged2]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  have hc₁ : ∀ m, p.2 (.inl m) ≠ none → GoodL L m := fun m hm ↦
    (cache_of_hashOK hA c₀ hp m hm).elim (hc₀ m) id
  -- `s₁`: fresh (by its length); every answer leaves a bound of `B`.
  refine (prEvent_query_le _ _ False (fun _ ↦ fresh_first hc₁ (hinp p.1)) _ _ (fun _ ↦ B)
    fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    exact le_of_eq (sum_const_div B)
  have i₁ := inv_first hc₁ (inp p.1) (hinp p.1) s₁
  -- `s₂`: fresh (a `32`-byte input after inputs of other lengths); its challenge bad with probability `≤ B`.
  refine (prEvent_query_le _ _ False (fun _ ↦ fresh_inv hL i₁ List.not_mem_nil) _ _
    (fun s₂ ↦ if bad (alphaOf s₁) (chal s₂) then 1 else 0) fun s₂ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    exact sum_bad_le chal hreg _ Nbad (hbad _)
  exact prEvent_final_le _ (alphaOf s₁, chal s₂) (fun v ↦ bad v.1 v.2)

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.prEvent_staged2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.prEvent_staged2_le
