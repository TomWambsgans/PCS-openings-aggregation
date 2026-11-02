-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Rom.FS

/-!
# The challenges drawn in advance

`implFresh` draws each Fiat–Shamir answer when it is asked; `implUp σ` reads it from `σ`, drawn
before the prover runs. Nothing reads a challenge before it is asked (the messages and rows read
`σ` only up to the challenges so far), so the two have the same distribution
(`tape_evalDistEq`).
-/

open OracleComp OracleSpec

namespace QuotientZk

set_option linter.unusedSectionVars false

variable {S I O M K X Pf : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
variable (P : Proto S I O M K X)

theorem getD_append_length {α : Type} (l : List α) (w : α) (x : List α) (d : α) :
    (l ++ w :: x).getD l.length d = w := by
  simp [List.getD_eq_getElem?_getD]

/-- Off the Fiat–Shamir steps, the up-front prover is the fresh one, whatever follows the
challenges so far. -/
theorem implUp_eq_fresh (s : S) (st : St I O K X) (τ : List O) (t : Op I K X)
    (ht : ∀ u, t = .chal u → P.n ≤ st.hist.length) :
    (implUp P (st.hist ++ τ) s t).run st = (implFresh P s t).run st := by
  cases t with
  | pub t => rfl
  | msg => simp [implUp, implFresh, StateT.run]
  | leaf k x =>
    simp only [implUp, implFresh, StateT.run, Proto.rows]
    split_ifs with h
    · rfl
    · rw [List.take_append_of_le_length (by omega)]
  | chal t =>
    have h := ht t rfl
    simp only [implUp, implFresh, StateT.run, show ¬ st.hist.length < P.n by omega, ite_false]

/-- Off the Fiat–Shamir steps, the challenges so far do not change. -/
theorem implFresh_hist (s : S) (st : St I O K X) (t : Op I K X)
    (ht : ∀ u, t = .chal u → P.n ≤ st.hist.length) :
    ∀ z ∈ support ((implFresh P s t).run st), z.2.hist = st.hist := by
  intro z hz
  cases t with
  | pub t => exact (roStep_fs t st z hz).2
  | msg =>
    simp only [implFresh, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  | leaf k x =>
    simp only [implFresh, StateT.run] at hz
    split_ifs at hz with h
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl
    · exact (roStep_fs _ st z hz).2
  | chal t =>
    have h := ht t rfl
    simp only [implFresh, StateT.run, show ¬ st.hist.length < P.n by omega, ite_false] at hz
    exact (roStep_fs t st z hz).2

/-- **The challenges drawn in advance.** From any state with at most `n` challenges, the fresh
prover is the up-front prover whose remaining challenges are drawn uniformly before it runs. -/
theorem tape_evalDistEq (s : S) {α : Type} (oa : OracleComp (OpSpec I O M K X) α) :
    ∀ st : St I O K X, st.hist.length ≤ P.n →
      (simulateQ (implFresh P s) oa).run st =ᵈ
        (do let τ ← uniformList O (P.n - st.hist.length)
            (simulateQ (implUp P (st.hist ++ τ) s) oa).run st) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st _
    simp only [simulateQ_pure, StateT.run_pure]
    exact (EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    intro st hst
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    by_cases hc : ∃ u, t = .chal u ∧ st.hist.length < P.n
    · obtain ⟨u, rfl, hlt⟩ := hc
      obtain ⟨m, hm⟩ : ∃ m, P.n - st.hist.length = m + 1 := ⟨P.n - st.hist.length - 1, by omega⟩
      rw [hm]
      simp only [implFresh, implUp, StateT.run, hlt, ite_true, uniformList, bind_assoc, pure_bind]
      refine EvalDistEq.bind_congr_of_support _ fun w _ => ?_
      simp only [progStep, pure_bind, getD_append_length]
      have hlen : (st.hist ++ [w]).length ≤ P.n := by simp; omega
      have h2 := ih w { st with
        cache := st.cache.cacheQuery u w
        hist := st.hist ++ [w]
        log := u :: st.log
        fs := st.fs || (st.cache u).isSome } hlen
      have hm' : P.n - (st.hist ++ [w]).length = m := by simp; omega
      rw [hm'] at h2
      refine h2.trans ?_
      simp only [List.append_assoc, List.singleton_append]
      exact EvalDistEq.rfl
    · have ht : ∀ u, t = .chal u → P.n ≤ st.hist.length := fun u hu => by
        by_contra h
        exact hc ⟨u, hu, by omega⟩
      have heq : ∀ τ : List O, (implUp P (st.hist ++ τ) s t).run st = (implFresh P s t).run st :=
        fun τ => implUp_eq_fresh P s st τ t ht
      simp only [heq]
      refine (EvalDistEq.bind_congr_of_support _ fun z hz => ?_).trans
        (EvalDistEq.bind_bind_swap _ _ _).symm
      have hh := implFresh_hist P s st t ht z hz
      have := ih z.1 z.2 (by rw [hh]; exact hst)
      rw [hh] at this
      exact this

end QuotientZk
