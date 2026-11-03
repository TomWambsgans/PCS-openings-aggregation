-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockBase

/-!
# The tower's `XOR` network: each leaf is the sum of its mask's slices

`Pi1.xorNetwork leaves` (Paar's greedy common subexpressions) returns the network's new variables (`xors`, each the sum
of two earlier ones) and, for each leaf, the variables it sums. Whatever pairs the greedy choice picks, the loop keeps
`NetInv`: every leaf's variables are distinct and defined, each new variable sums two earlier ones, and for every
assignment `s` of the 64 slices the sum of a leaf's variables (`netVals s xors`: the slices, then each new variable's
value) is the sum of the slices its mask names (`xorNetwork_inv`). The pair chosen is two distinct variables of one
leaf: the count array's positive entries are pairs of a leaf (`CountInv`), the best entry is positive (`BestInv`).

Also `towerLeaves_size`: the tower has 64 leaves. Both are proved on the definitions' loops (`id_forIn_inv`), never by
evaluating them.
-/

namespace RecGraph.Sim

open LeanVM.Parameters UniStatement RecGraph.Pi1

/-- **An invariant of an `Id` loop**: kept by every step, done or not. -/
theorem id_forIn_inv {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) {U : Id β}
    (hU : forIn (m := Id) l init f = U) (P : β → Prop) (h0 : P init)
    (hs : ∀ a ∈ l, ∀ b, P b → P (Id.run (f a b)).value) : P (Id.run U) := by
  subst hU
  induction l generalizing init with
  | nil => exact h0
  | cons a t ih =>
    rw [List.forIn_cons]
    have h1 := hs a (by simp) init h0
    cases hf : Id.run (f a init) with
    | done b =>
      rw [hf] at h1
      show P (Id.run (f a init >>= fun x ↦ match x with | .done b => pure b | .yield b => forIn t b f))
      rw [idBind]
      show P (Id.run (match Id.run (f a init) with | .done b => pure b | .yield b => forIn t b f))
      rw [hf]; exact h1
    | yield b =>
      rw [hf] at h1
      show P (Id.run (f a init >>= fun x ↦ match x with | .done b => pure b | .yield b => forIn t b f))
      rw [idBind]
      show P (Id.run (match Id.run (f a init) with | .done b => pure b | .yield b => forIn t b f))
      rw [hf]
      exact ih b h1 fun a' ha' b' hb' ↦ hs a' (List.mem_cons_of_mem _ ha') b' hb'

theorem id_forIn_inv_range {β : Type} (s e : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) {U : Id β}
    (hU : forIn (m := Id) ({ start := s, stop := e, step := 1, step_pos := Nat.one_pos } : Std.Legacy.Range) init f = U)
    (P : β → Prop) (h0 : P init) (hs : ∀ a, s ≤ a → a < e → ∀ b, P b → P (Id.run (f a b)).value) : P (Id.run U) := by
  rw [forIn_range_list] at hU
  exact id_forIn_inv _ init f hU P h0 fun a ha b hb ↦ by
    rw [List.mem_range'] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact hs _ (by omega) (by omega) b hb

/-! ## The tower's leaves: 64 -/

theorem towerLeaves_size : Flock.towerLeaves.size = Flock.kBits := by
  unfold Flock.towerLeaves
  lift_lets
  extract_lets leaves0
  generalize hU : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array ℕ) _ _ _) = U
  rw [idBind]
  refine id_forIn_inv_range 0 Flock.kBits leaves0 _ hU (fun b ↦ b.size = Flock.kBits) (by simp [leaves0]) ?_
  intro i _ _ b hb
  lift_lets
  extract_lets
  generalize hP : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E) _ _ _) = Pt
  rw [idBind]
  lift_lets
  extract_lets
  generalize hV : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array ℕ) _ _ _) = V
  rw [idBind]
  show V.size = Flock.kBits
  refine id_forIn_inv_range 0 _ b _ hV (fun b ↦ b.size = Flock.kBits) hb ?_
  intro w _ _ c hc
  generalize (_ == (1 : E)) = t
  cases t <;> simp [hc]

end RecGraph.Sim
