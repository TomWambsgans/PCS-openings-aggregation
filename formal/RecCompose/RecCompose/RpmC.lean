-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The eager form of the random-permutation model is
-- `formal/EndToEnd/ZK/ProverBridgeEager.lean`'s (`prEvent_runWithRandomPermutation`).
import ZK.ProverBridgeEager

/-!
# The random-permutation model, eagerly: comparisons permutation by permutation

`runWithRandomPermutation` draws `π` lazily; by `PcsQuotient.EndToEnd.Eager.prEvent_runWithRandomPermutation` every
event's probability is the average over the permutations `π` of the game answered by `π` (`permImpl π`), which keeps
no state: a computation whose result is unused drops out, and the same computation run twice answers alike.

* `eager_eq`, `eager_le_add`: comparisons of games, permutation by permutation;
* `support_simulateQ_subset`: answering the queries can only shrink the support;
* `prEvent_eq_one_of_support`: an event every possible output satisfies has probability one.
-/

namespace RecCompose.RpmC

open OracleComp OracleSpec Common
open PcsQuotient.EndToEnd.Eager
open scoped ENNReal

/-- **Equal games, permutation by permutation.** -/
theorem eager_eq {α β : Type} (X : OracleComp RandomPermutationOracles α)
    (Y : OracleComp RandomPermutationOracles β) (p : α → Prop) (q : β → Prop)
    (h : ∀ π : Equiv.Perm St, Pr{let a ← simulateQ (permImpl π) X}[p a] =
      Pr{let b ← simulateQ (permImpl π) Y}[q b]) :
    Pr{let a ← runWithRandomPermutation X}[p a] = Pr{let b ← runWithRandomPermutation Y}[q b] := by
  rw [prEvent_runWithRandomPermutation, prEvent_runWithRandomPermutation, Finset.sum_congr rfl fun π _ ↦ h π]

/-- **A game bounded by two others, permutation by permutation.** -/
theorem eager_le_add {α β γ : Type} (X : OracleComp RandomPermutationOracles α)
    (Y : OracleComp RandomPermutationOracles β) (Z : OracleComp RandomPermutationOracles γ)
    (p : α → Prop) (q : β → Prop) (r : γ → Prop)
    (h : ∀ π : Equiv.Perm St, Pr{let a ← simulateQ (permImpl π) X}[p a] ≤
      Pr{let b ← simulateQ (permImpl π) Y}[q b] + Pr{let c ← simulateQ (permImpl π) Z}[r c]) :
    Pr{let a ← runWithRandomPermutation X}[p a] ≤
      Pr{let b ← runWithRandomPermutation Y}[q b] + Pr{let c ← runWithRandomPermutation Z}[r c] := by
  rw [prEvent_runWithRandomPermutation, prEvent_runWithRandomPermutation, prEvent_runWithRandomPermutation,
    ← mul_add, ← Finset.sum_add_distrib]
  exact mul_le_mul' le_rfl (Finset.sum_le_sum fun π _ ↦ h π)

/-- **Answering the queries can only shrink the support.** -/
theorem support_simulateQ_subset {ι : Type} {spec : OracleSpec ι} {α : Type} (impl : QueryImpl spec ProbComp)
    (oa : OracleComp spec α) : support (simulateQ impl oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    intro x hx
    simp only [simulateQ_bind, simulateQ_spec_query, support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨u, -, hu⟩ := hx
    simp only [support_bind, Set.mem_iUnion, exists_prop]
    exact ⟨u, by simp, ih u hu⟩

/-- **An event every possible output satisfies has probability one** (an oracle computation never fails). -/
theorem prEvent_eq_one_of_support {ι : Type} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] {α : Type}
    (X : OracleComp spec α) (p : α → Prop) (h : ∀ a ∈ support X, p a) : Pr{let a ← X}[p a] = 1 := by
  rw [prEvent_congr_of_support X p (fun _ ↦ True) fun a ha ↦ ⟨fun _ ↦ trivial, fun _ ↦ h a ha⟩]
  exact OracleComp.prEvent_true_eq_one X

/-- **A coin-free event of a game answered by `π`**: every possible output of the game (whatever the oracles answer)
satisfies it, so its probability with `π` is one. -/
theorem prEvent_perm_eq_one {α : Type} (π : Equiv.Perm St) (X : OracleComp RandomPermutationOracles α)
    (p : α → Prop) (h : ∀ a ∈ support X, p a) : Pr{let a ← simulateQ (permImpl π) X}[p a] = 1 :=
  prEvent_eq_one_of_support _ p fun a ha ↦ h a (support_simulateQ_subset _ X ha)

end RecCompose.RpmC

/-- info: 'RecCompose.RpmC.eager_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.RpmC.eager_le_add

/-- info: 'RecCompose.RpmC.prEvent_perm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.RpmC.prEvent_perm_eq_one
