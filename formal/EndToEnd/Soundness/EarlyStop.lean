-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.F1Step

/-!
# The verifier with early stops accepts at most as often as the composed verifier

The Statement's verifier stops at the first failure: a malformed root, a vanishing denominator, an
opening that rejects (`verifyES`, `VerifierBridge`); the composed verifier of `Compose/Rpm.lean`
(`verifyD`) runs the chain and the three openings whatever happens, and accepts (`AcceptedV`) when
its own check and the three openings do. Both run against the same lazily sampled permutation:

* **`es_le`**: from any state of the permutation, `verifyES` accepts with probability at most that
  of `verifyD` accepting, at the deployed claim maps: where `verifyES` goes on it makes the same
  queries as `verifyD`, and it stops only where `verifyD` rejects (the reduction's own check holds
  when `reduce` does not reject, `reductionCheck_of_reduce`);
* **`verifier_malformed`**: on a proof whose roots' scalars are not digests, the Statement's
  verifier rejects, whatever the permutation;
* the generic steps: a comparison of continuations survives a common simulated prefix
  (`mono_bind`), and an event no output of a computation meets has probability zero under any
  stateful simulation (`zero_of_support`).
-/

set_option linter.unusedSectionVars false
set_option simprocs false

open OracleSpec OracleComp
open scoped ENNReal

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge

/-! ## Simulated computations -/

section Sim

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ : Type}
  (impl : QueryImpl spec (StateT σ ProbComp))

theorem run'_bind {α β : Type} (oa : OracleComp spec α) (k : α → OracleComp spec β) (s : σ) :
    (simulateQ impl (oa >>= k)).run' s =
      (simulateQ impl oa).run s >>= fun p => (simulateQ impl (k p.1)).run' p.2 := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- **A comparison of continuations survives a common simulated prefix.** -/
theorem mono_bind {α β γ : Type} (oa : OracleComp spec α) (k₁ : α → OracleComp spec β)
    (k₂ : α → OracleComp spec γ) (E₁ : β → Prop) (E₂ : γ → Prop)
    (h : ∀ x s, Pr{let y ← (simulateQ impl (k₁ x)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ impl (k₂ x)).run' s}[E₂ y]) (s : σ) :
    Pr{let y ← (simulateQ impl (oa >>= k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ impl (oa >>= k₂)).run' s}[E₂ y] := by
  rw [run'_bind, run'_bind]
  exact prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p => h p.1 p.2

theorem run'_pure {α : Type} (x : α) (s : σ) :
    (simulateQ impl (pure x : OracleComp spec α)).run' s = pure x := by
  rw [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]

/-- An event the returned value misses has probability zero. -/
theorem zero_pure {α : Type} (x : α) (E : α → Prop) (hx : ¬ E x) (s : σ) :
    Pr{let y ← (simulateQ impl (pure x : OracleComp spec α)).run' s}[E y] = 0 := by
  rw [run'_pure]
  exact prEvent_eq_zero_of_forall_mem_support _ _ fun y hy => by
    rw [support_pure, Set.mem_singleton_iff] at hy
    exact hy ▸ hx

/-- Pure continuations are ordered by their events. -/
theorem le_pure {α β : Type} (x : α) (y : β) (E₁ : α → Prop) (E₂ : β → Prop)
    (h : E₁ x → E₂ y) (s : σ) :
    Pr{let z ← (simulateQ impl (pure x : OracleComp spec α)).run' s}[E₁ z] ≤
      Pr{let z ← (simulateQ impl (pure y : OracleComp spec β)).run' s}[E₂ z] := by
  classical
  rw [run'_pure, run'_pure, prEvent_pure, prEvent_pure]
  split_ifs with h1 h2 <;> simp_all

/-- **An event no output of a computation meets has probability zero**, under any stateful
simulation. -/
theorem zero_of_support {α : Type} (oa : OracleComp spec α) (E : α → Prop)
    (h : ∀ x ∈ support oa, ¬ E x) (s : σ) :
    Pr{let y ← (simulateQ impl oa).run' s}[E y] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => exact zero_pure impl a E (h a (by rw [support_pure]; rfl)) s
  | query_bind t k ih =>
    rw [run'_bind]
    refine le_antisymm (prEvent_bind_le_of_forall_le _ _ _ fun p => ?_) bot_le
    refine (ih p.1 (fun x hx => h x ?_) p.2).le
    rw [mem_support_bind_iff]
    exact ⟨p.1, mem_support_query t p.1, hx⟩

end Sim

/-! ## The verifier with early stops -/

open LeanVM.Protocol in
/-- The two calls over the lazily sampled permutation. -/
noncomputable abbrev kcLazy := keccakCallsOverRandomPermutation

/-- The opening with its first stop accepts at most as often as the opening, from any state, for
continuations ordered as accepting implies accepting. -/
theorem early_le {β γ : Type} (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof)
    (k₁ : Bool → OracleComp KeccakCalls β) (k₂ : Bool → OracleComp KeccakCalls γ)
    (E₁ : β → Prop) (E₂ : γ → Prop) (h0 : ∀ s, Pr{let y ← (simulateQ kcLazy (k₁ false)).run' s}[E₁ y] = 0)
    (h1 : ∀ s, Pr{let y ← (simulateQ kcLazy (k₁ true)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ kcLazy (k₂ true)).run' s}[E₂ y]) (s : _) :
    Pr{let y ← (simulateQ kcLazy (ourVerifierEarly L R w >>= k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ kcLazy (ourVerifier L R w >>= k₂)).run' s}[E₂ y] := by
  have hk : ∀ b s, Pr{let y ← (simulateQ kcLazy (k₁ b)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ kcLazy (k₂ b)).run' s}[E₂ y] := by
    intro b s
    cases b
    · rw [h0 s]; exact bot_le
    · exact h1 s
  unfold ourVerifierEarly
  split
  · exact mono_bind kcLazy _ _ _ _ _ hk s
  · rw [pure_bind, h0 s]
    exact bot_le

/-- **The verifier with early stops accepts at most as often as the composed verifier**, from any
state of the lazily sampled permutation, at the deployed claim maps and parameters matching
`reduce` (`Matches`). -/
theorem es_le (c : Consts) {P : Params E} {B : P.Bounds} (W : Wire P B) (hM : Matches P c 22)
    (po : RootProof E × OpenProofs) (s : _) :
    Pr{let b ← (simulateQ kcLazy (verifyES W c po)).run' s}[b = true] ≤
      Pr{let v ← (simulateQ kcLazy (verifyD W (deployD c 22) po)).run' s}[
        AcceptedV (P := P) (po, v)] := by
  unfold verifyES verifyD
  refine mono_bind kcLazy _ _ _ _ _ (fun ch s => ?_) s
  by_cases hok : (reduceOf c 22 po.1 ch).isSome
  swap
  · rw [ite_eq_right hok, zero_pure kcLazy false _ (by simp) s]
    exact bot_le
  rw [ite_eq_left hok]
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hok
  have hrc := reductionCheck_of_reduce c hM po.1 ch hx
  refine early_le _ _ _ _ _ _ _ (fun s => ?_) (fun s => ?_) s
  · rw [ite_eq_right (by simp), zero_pure kcLazy false _ (by simp) s]
  rw [ite_eq_left rfl]
  refine early_le _ _ _ _ _ _ _ (fun s => ?_) (fun s => ?_) s
  · rw [ite_eq_right (by simp), zero_pure kcLazy false _ (by simp) s]
  rw [ite_eq_left rfl]
  have e : ∀ L R w, ourVerifierEarly L R w = ourVerifierEarly L R w >>= fun b => pure b :=
    fun _ _ _ => (bind_pure _).symm
  rw [e]
  refine early_le _ _ _ _ _ _ _ (fun s => zero_pure kcLazy false _ (by simp) s) (fun s => ?_) s
  refine le_pure kcLazy true (ch, true, true, true) (fun b => b = true)
    (fun v => AcceptedV (P := P) (po, v)) (fun _ => ?_) s
  exact ⟨hrc, rfl, rfl, rfl⟩

/-! ## A malformed proof is rejected -/

/-- **On a proof whose roots' scalars are not two digests, the Statement's verifier rejects**,
whatever the permutation answers. -/
theorem verifier_malformed (ir : Digest) (stmt : PcsQuotient.Statement)
    (proof : PcsQuotient.Proof)
    (hm : digestOfScalars proof.reduction.witnessRoot = none ∨
      digestOfScalars proof.reduction.quotientRoot = none) :
    ∀ b ∈ support (PcsQuotient.verifier Common.queryPermutation ir stmt proof), b = false := by
  have hS : PcsQuotient.Supported PcsQuotient.logRows := ⟨by decide, by decide⟩
  have hred : ∀ r ∈ support (PcsQuotient.reduceWith Common.queryPermutation PcsQuotient.logRows ir
      stmt proof.reduction), r = none := by
    intro r hr
    unfold PcsQuotient.reduceWith at hr
    rw [ite_eq_right (not_not.mpr hS), mem_support_bind_iff] at hr
    obtain ⟨c0, -, hr⟩ := hr
    rcases hw : digestOfScalars proof.reduction.witnessRoot with _ | wr
    · simp only [hw] at hr
      exact (Set.mem_singleton_iff.mp (by simpa using hr))
    · have hq : digestOfScalars proof.reduction.quotientRoot = none := by
        rcases hm with h | h
        · rw [hw] at h; cases h
        · exact h
      simp only [hw, mem_support_bind_iff] at hr
      obtain ⟨_, -, _, -, _, -, hr⟩ := hr
      simp only [hq] at hr
      exact (Set.mem_singleton_iff.mp (by simpa using hr))
  intro b hb
  unfold PcsQuotient.verifier PcsQuotient.verifyWith at hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨r, hr, hb⟩ := hb
  rw [hred r hr] at hb
  simpa using hb

end Soundness
