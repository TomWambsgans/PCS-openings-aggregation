-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s identical-until-bad lemma (`Common.prEvent_run_le_add_bad`,
-- `Common.prEvent_run_bad_eq`).
import QuotientZk.Rom.Defs
import Common.Prob

/-!
# Fiat–Shamir: the challenges drawn first

Two steps from the real prover (`implReal`) to the prover whose challenges are drawn before it
runs (`implUp`):

* `implReal` and `implFresh` differ only at a Fiat–Shamir query whose input the oracle already
  answered (the real one returns the old answer, the fresh one a new one), and both raise the flag
  `fs` there: **identical until the flag** (`prEvent_real_le_fresh`, `prEvent_fresh_le_real`);
* `implFresh` draws each challenge when asked, `implUp σ` reads it from `σ` drawn in advance:
  **the same distribution** (`tape_evalDistEq`), because nothing reads a challenge before it is
  asked.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

variable {S I O M K X Pf : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
variable (P : Proto S I O M K X)

/-! ## Steps that do not depend on the implementation -/

theorem roStep_fs (t : I) (st : St I O K X) :
    ∀ z ∈ support (roStep (K := K) (X := X) t st), z.2.fs = st.fs ∧ z.2.hist = st.hist := by
  intro z hz
  unfold roStep at hz
  cases h : st.cache t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl⟩
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨rfl, rfl⟩

/-! ## Identical until the flag -/

/-- The flag never goes down, in the real prover. -/
theorem implReal_mono (s : S) (t : Op I K X) (st : St I O K X) (hst : st.fs = true) :
    ∀ z ∈ support ((implReal P s t).run st), z.2.fs = true := by
  intro z hz
  cases t with
  | pub t => exact (roStep_fs t st z hz).1.trans hst
  | msg =>
    simp only [implReal, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hst
  | leaf k x =>
    simp only [implReal, StateT.run] at hz
    split_ifs at hz with h
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hst
    · exact (roStep_fs _ st z hz).1.trans hst
  | chal t =>
    simp only [implReal, StateT.run] at hz
    split_ifs at hz with h
    · cases hc : st.cache t with
      | some u =>
        simp only [hc, support_pure, Set.mem_singleton_iff] at hz
        subst hz; rfl
      | none =>
        simp only [hc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨u, -, rfl⟩ := hz
        exact hst
    · exact (roStep_fs t st z hz).1.trans hst

/-- The flag never goes down, with fresh challenges. -/
theorem implFresh_mono (s : S) (t : Op I K X) (st : St I O K X) (hst : st.fs = true) :
    ∀ z ∈ support ((implFresh P s t).run st), z.2.fs = true := by
  intro z hz
  cases t with
  | pub t => exact (roStep_fs t st z hz).1.trans hst
  | msg =>
    simp only [implFresh, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hst
  | leaf k x =>
    simp only [implFresh, StateT.run] at hz
    split_ifs at hz with h
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hst
    · exact (roStep_fs _ st z hz).1.trans hst
  | chal t =>
    simp only [implFresh, StateT.run] at hz
    split_ifs at hz with h
    · simp only [progStep, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      simp [hst]
    · exact (roStep_fs t st z hz).1.trans hst

/-- Off the flag, the real and the fresh steps agree. -/
theorem implReal_agree (s : S) (t : Op I K X) (st : St I O K X) (hst : ¬ st.fs = true)
    (q : (OpSpec I O M K X).Range t × St I O K X → Prop) :
    Pr{let z ← (implReal P s t).run st}[q z ∧ ¬ z.2.fs = true] =
      Pr{let z ← (implFresh P s t).run st}[q z ∧ ¬ z.2.fs = true] := by
  cases t with
  | pub t => rfl
  | msg => rfl
  | leaf k x => rfl
  | chal t =>
    simp only [implReal, implFresh, StateT.run]
    split_ifs with h
    · cases hc : st.cache t with
      | some u =>
        rw [prEvent_eq_zero_of_forall_mem_support _ _ ?_,
          prEvent_eq_zero_of_forall_mem_support _ _ ?_]
        · intro z hz
          simp only [progStep, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨u', -, rfl⟩ := hz
          simp [hc]
        · intro z hz
          simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          simp
      | none =>
        have hf : st.fs = false := by simpa using hst
        simp only [progStep, hc, Option.isSome_none, Bool.or_false, hf]
    · rfl

/-- **Identical until the flag**, one way. -/
theorem prEvent_real_le_fresh {α : Type} (s : S) (oa : OracleComp (OpSpec I O M K X) α)
    (st : St I O K X) (p : α → Prop) :
    Pr{let z ← (simulateQ (implReal P s) oa).run st}[p z.1] ≤
      Pr{let z ← (simulateQ (implFresh P s) oa).run st}[p z.1] +
        Pr{let z ← (simulateQ (implReal P s) oa).run st}[z.2.fs = true] := by
  have h := Common.prEvent_run_le_add_bad (implReal P s) (implFresh P s) (fun st => st.fs = true)
    (implReal_agree P s) (implReal_mono P s) (implFresh_mono P s) oa st p
  rwa [← Common.prEvent_run_bad_eq (implReal P s) (implFresh P s) (fun st => st.fs = true)
    (implReal_agree P s) (implReal_mono P s) (implFresh_mono P s) oa st] at h

/-- **Identical until the flag**, the other way. -/
theorem prEvent_fresh_le_real {α : Type} (s : S) (oa : OracleComp (OpSpec I O M K X) α)
    (st : St I O K X) (p : α → Prop) :
    Pr{let z ← (simulateQ (implFresh P s) oa).run st}[p z.1] ≤
      Pr{let z ← (simulateQ (implReal P s) oa).run st}[p z.1] +
        Pr{let z ← (simulateQ (implReal P s) oa).run st}[z.2.fs = true] :=
  Common.prEvent_run_le_add_bad (implFresh P s) (implReal P s) (fun st => st.fs = true)
    (fun t st hst q => (implReal_agree P s t st hst q).symm) (implFresh_mono P s)
    (implReal_mono P s) oa st p

end QuotientZk
