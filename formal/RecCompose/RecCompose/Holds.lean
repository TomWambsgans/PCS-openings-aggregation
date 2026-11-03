-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Basic

/-!
# Postconditions in any monad

`Holds X P`: every output of `X` satisfies `P`, as an equation of the monad: `X` with each output paired with `P` of it
is `X` with each paired with `True`. It needs no semantics of the monad, is proved through binds whatever the effects
answer (`holds_bind`: the continuation needs `P` only where the first part's postcondition holds), passes through monad
maps (`simulateQ`, a `StateT` run) and gives, in a monad with a support, `P` on the support (`holds_support`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open OracleComp

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **Every output of `X` satisfies `P`.** -/
def Holds {α : Type} (X : m α) (P : α → Prop) : Prop :=
  (fun x ↦ (x, P x)) <$> X = (fun x ↦ (x, True)) <$> X

theorem holds_pure {α : Type} {a : α} {P : α → Prop} (h : P a) : Holds (pure a : m α) P := by
  unfold Holds
  simp only [map_pure, eq_true h]

/-- **A bind's continuations agree where the first part's postcondition holds.** -/
theorem bind_congr_of_holds {α β : Type} {X : m α} {Q : α → Prop} (hX : Holds X Q) {h h' : α → m β}
    (hh : ∀ a, Q a → h a = h' a) : X >>= h = X >>= h' := by
  classical
  calc X >>= h = ((fun a ↦ (a, True)) <$> X) >>= fun p ↦ (if p.2 then h p.1 else h' p.1) := by
        rw [bind_map_left]; simp
    _ = ((fun a ↦ (a, Q a)) <$> X) >>= fun p ↦ (if p.2 then h p.1 else h' p.1) := by
        unfold Holds at hX; rw [hX]
    _ = X >>= fun a ↦ if Q a then h a else h' a := by rw [bind_map_left]
    _ = X >>= h' := by
        congr 1
        funext a
        split_ifs with hq
        · exact hh a hq
        · rfl

theorem holds_bind {α β : Type} {X : m α} {k : α → m β} {Q : α → Prop} {P : β → Prop} (hX : Holds X Q)
    (hk : ∀ a, Q a → Holds (k a) P) : Holds (X >>= k) P := by
  unfold Holds
  rw [map_bind, map_bind]
  exact bind_congr_of_holds hX fun a ha ↦ hk a ha

theorem holds_true {α : Type} (X : m α) : Holds X fun _ ↦ True := rfl

theorem holds_mono {α : Type} {X : m α} {P P' : α → Prop} (hX : Holds X P) (h : ∀ a, P a → P' a) :
    Holds X P' := by
  have e : X = X >>= pure := (bind_pure X).symm
  rw [e]
  exact holds_bind hX fun a ha ↦ holds_pure (h a ha)

theorem holds_map {α β : Type} {X : m α} {f : α → β} {Q : α → Prop} {P : β → Prop} (hX : Holds X Q)
    (h : ∀ a, Q a → P (f a)) : Holds (f <$> X) P := by
  rw [map_eq_bind_pure_comp]
  exact holds_bind hX fun a ha ↦ holds_pure (h a ha)

theorem holds_and {α : Type} {X : m α} {P Q : α → Prop} (hP : Holds X P) (hQ : Holds X Q) :
    Holds X fun a ↦ P a ∧ Q a := by
  unfold Holds
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  calc X >>= (pure ∘ fun x ↦ (x, P x ∧ Q x)) = X >>= (pure ∘ fun x ↦ (x, Q x)) :=
        bind_congr_of_holds hP fun a ha ↦ by simp [ha]
    _ = X >>= (pure ∘ fun x ↦ (x, True)) := by
        rw [← map_eq_bind_pure_comp, ← map_eq_bind_pure_comp]; exact hQ

/-- A postcondition passes through any map of monads that commutes with `<$>`. -/
theorem holds_of_map_comm {n : Type → Type} [Monad n] {α : Type} {X : m α} {P : α → Prop} (hX : Holds X P)
    (φ : {γ : Type} → m γ → n γ) (hφ : ∀ {γ δ : Type} (f : γ → δ) (Y : m γ), φ (f <$> Y) = f <$> φ Y) :
    Holds (φ X) P := by
  unfold Holds at hX ⊢
  rw [← hφ, ← hφ, hX]

end Generic

/-- **`simulateQ` keeps a postcondition.** -/
theorem holds_simulateQ {ι : Type} {spec : OracleSpec ι} {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) {α : Type} {X : OracleComp spec α} {P : α → Prop} (hX : Holds X P) :
    Holds (simulateQ impl X) P := by
  unfold Holds at hX ⊢
  rw [← simulateQ_map, ← simulateQ_map, hX]

/-- **A `StateT` run keeps a postcondition.** -/
theorem holds_run' {σ : Type} {r : Type → Type} [Monad r] [LawfulMonad r] {α : Type} {X : StateT σ r α}
    {P : α → Prop} (hX : Holds X P) (s : σ) : Holds (X.run' s) P := by
  unfold Holds at hX ⊢
  have e : ∀ {γ δ : Type} (f : γ → δ) (Y : StateT σ r γ), f <$> Y.run' s = (f <$> Y).run' s := by
    intro γ δ f Y
    simp [StateT.run'_eq, StateT.run_map]
  rw [e, e, hX]

/-- **A postcondition holds on the support.** -/
theorem holds_support {α : Type} {X : ProbComp α} {P : α → Prop} (hX : Holds X P) :
    ∀ x ∈ support X, P x := by
  intro x hx
  have h : (x, P x) ∈ support ((fun x ↦ (x, P x)) <$> X) := by
    rw [support_map]; exact ⟨x, hx, rfl⟩
  unfold Holds at hX
  rw [hX, support_map] at h
  obtain ⟨y, -, hy⟩ := h
  have := congrArg Prod.snd hy
  simp only at this
  exact this ▸ trivial

end RecCompose
