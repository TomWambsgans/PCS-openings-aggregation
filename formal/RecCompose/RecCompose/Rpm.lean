-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The model is leanerVM `mumbai`'s
-- (`Statement/RandomPermutation.lean`: `loggedOracles`, `runWithRandomPermutation`, `QueryCostAtMost`); eager sampling
-- is `formal/EndToEnd/ZK/ProverBridgeEager.lean`'s `prEvent_runWithRandomPermutation`.
import RecStatement
import ZK.ProverBridgeEager

/-!
# The random-permutation model's lemmas the couplings use

* **Logging** (`loggedOracles`): a run from a log appends to it (`logged_run_append`); logging changes nothing of the
  computation (`fst_logged_run`) nor of its query cost (`queryCost_logged_iff`); logging a logged computation logs the
  same queries (`logged_logged_run`), so an adversary that runs another, logged, then computes from its output and
  transcript, has the other's transcript (`logged_post`).
* **Eager sampling** (`prEvent_le_of_perm`): an event of one game is at most another's when it is so for every fixed
  permutation, the queries answered by it (`permImpl π`): then the games are stateless, and binds compare pointwise.
* `runWithRandomPermutation_map`: the model's run commutes with a map of the output.
-/

namespace RecCompose.Rpm

open OracleComp OracleSpec Common
open scoped ENNReal

section Logging

variable {α β : Type}

/-- **A logged run from a log appends to it.** -/
theorem logged_run_append (X : OracleComp RandomPermutationOracles α) (s : OracleQueryLog) :
    (simulateQ loggedOracles X).run s = (fun p ↦ (p.1, s ++ p.2)) <$> (simulateQ loggedOracles X).run [] := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, loggedOracles, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, StateT.run_modify, StateT.run_monadLift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun u ↦ ?_
    conv_lhs => rw [ih u]
    conv_rhs => rw [ih u, Functor.map_map]
    simp [List.append_assoc]

/-- **Logging changes nothing of the computation.** -/
theorem fst_logged_run (X : OracleComp RandomPermutationOracles α) (s : OracleQueryLog) :
    Prod.fst <$> (simulateQ loggedOracles X).run s = X := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, loggedOracles, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, StateT.run_modify, StateT.run_monadLift, bind_assoc, pure_bind, map_bind]
    exact bind_congr fun u ↦ ih u _

/-- **Logging changes nothing of the query cost.** -/
theorem queryCost_logged_iff (X : OracleComp RandomPermutationOracles α) (s : OracleQueryLog) (Q : ℕ) :
    QueryCostAtMost ((simulateQ loggedOracles X).run s) permutationCallCost Q ↔
      QueryCostAtMost X permutationCallCost Q :=
  isQueryBound_iff_of_map_eq (fst_logged_run X s) _ _

/-- **Logging a logged computation logs the same queries.** -/
theorem logged_logged_run (X : OracleComp RandomPermutationOracles α) (s s' : OracleQueryLog) :
    (simulateQ loggedOracles ((simulateQ loggedOracles X).run s)).run s' =
      (fun p ↦ ((p.1, s ++ p.2), s' ++ p.2)) <$> (simulateQ loggedOracles X).run [] := by
  induction X using OracleComp.inductionOn generalizing s s' with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, loggedOracles, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, StateT.run_modify, StateT.run_monadLift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun u ↦ ?_
    conv_lhs => rw [ih u]
    conv_rhs => rw [logged_run_append (k u), Functor.map_map]
    simp [List.append_assoc]

/-- **An adversary that runs another, logged, then computes from its output and transcript** has, logged, the other's
transcript. -/
theorem logged_post (X : OracleComp RandomPermutationOracles α)
    (k : α × OracleQueryLog → OracleComp RandomPermutationOracles β) (g : α × OracleQueryLog → β)
    (hk : ∀ p, k p = pure (g p)) :
    (simulateQ loggedOracles ((simulateQ loggedOracles X).run [] >>= k)).run [] =
      (fun p ↦ (g p, p.2)) <$> (simulateQ loggedOracles X).run [] := by
  have hk' : k = fun p ↦ pure (g p) := funext hk
  subst hk'
  rw [simulateQ_bind, StateT.run_bind, logged_logged_run, bind_map_left]
  simp only [simulateQ_pure, StateT.run_pure, List.nil_append]
  rw [map_eq_bind_pure_comp]
  rfl

/-- The query cost of an adversary that runs another, logged, then computes from its output and transcript. -/
theorem queryCost_post (X : OracleComp RandomPermutationOracles α)
    (k : α × OracleQueryLog → OracleComp RandomPermutationOracles β) (g : α × OracleQueryLog → β)
    (hk : ∀ p, k p = pure (g p)) (Q : ℕ) (hX : QueryCostAtMost X permutationCallCost Q) :
    QueryCostAtMost ((simulateQ loggedOracles X).run [] >>= k) permutationCallCost Q := by
  have hk' : k = fun p ↦ pure (g p) := funext hk
  subst hk'
  rw [bind_pure_comp]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr ((queryCost_logged_iff X [] Q).mpr hX)

end Logging

section Eager

open PcsQuotient.EndToEnd.Eager

/-- **Eager sampling**: an event of one game is at most another's when it is so for every fixed permutation. -/
theorem prEvent_le_of_perm {α β : Type} (X : OracleComp RandomPermutationOracles α)
    (Y : OracleComp RandomPermutationOracles β) (p : α → Prop) (q : β → Prop)
    (h : ∀ π, Pr{let a ← simulateQ (permImpl π) X}[p a] ≤ Pr{let b ← simulateQ (permImpl π) Y}[q b]) :
    Pr{let a ← runWithRandomPermutation X}[p a] ≤ Pr{let b ← runWithRandomPermutation Y}[q b] := by
  rw [prEvent_runWithRandomPermutation, prEvent_runWithRandomPermutation]
  exact mul_le_mul_right (Finset.sum_le_sum fun π _ ↦ h π) _

end Eager

/-- Events of pure computations are ordered by implication. -/
theorem prEvent_pure_le {α β : Type} (a : α) (b : β) (p : α → Prop) (q : β → Prop) (h : p a → q b) :
    Pr{let x ← (pure a : ProbComp α)}[p x] ≤ Pr{let y ← (pure b : ProbComp β)}[q y] := by
  classical
  rw [prEvent_pure, prEvent_pure]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h h1) h2
  · exact zero_le
  · exact le_rfl

/-- The model's run commutes with a map of the output. -/
theorem runWithRandomPermutation_map {α β : Type} (f : α → β) (X : OracleComp RandomPermutationOracles α) :
    f <$> runWithRandomPermutation X = runWithRandomPermutation (f <$> X) := by
  unfold runWithRandomPermutation
  simp [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

end RecCompose.Rpm
