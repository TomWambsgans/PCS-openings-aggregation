-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Lemmas.Arith

/-!
# The pushes' sum and the public side, as sums

* **The accumulated fractions** (`accStep`): `(a, b) ↦ (a d + b x, b d)` from the first `(x, d)` gives
  `b = Π d_i` and `a/b = Σ x_i/d_i` (`accFold_some`, `accFold_none`); `pushSums` is two of them, over every group
  (`(N_g X_g, D_g)`) and over the pull-less groups (`(N_g, D_g)`) (`pushSums_eq`; a one-pair group's `N_g` is `1`).
* **The walk** (`walkDens_eq`): `β ω_τ` updated by the bits that differ is `β ω_τ`, for tags below `2^28` and `ω`
  additive in the bits (`betaTagNext_eq`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset

variable {F : Type} [Field F]

/-! ## Accumulated fractions -/

/-- One step of an accumulated fraction: `(a, b) + x/d = (a d + b x, b d)`, from `(x, d)`. -/
def accStep (acc : Option (F × F)) (xd : F × F) : Option (F × F) :=
  match acc with
  | some (a, b) => some (a * xd.2 + b * xd.1, b * xd.2)
  | none => some (xd.1, xd.2)

theorem accFold_some (xs : List (F × F)) (a b : F) (hb : b ≠ 0) (hd : ∀ xd ∈ xs, xd.2 ≠ 0) :
    ∃ a' b', xs.foldl accStep (some (a, b)) = some (a', b') ∧ b' = b * (xs.map (·.2)).prod ∧
      a' = b' * (a / b + (xs.map fun xd ↦ xd.1 / xd.2).sum) := by
  induction xs generalizing a b with
  | nil => exact ⟨a, b, rfl, by simp, by field_simp; simp⟩
  | cons xd xs ih =>
    have hd0 : xd.2 ≠ 0 := hd xd List.mem_cons_self
    obtain ⟨a', b', h1, h2, h3⟩ := ih (a * xd.2 + b * xd.1) (b * xd.2) (mul_ne_zero hb hd0)
      fun y hy ↦ hd y (List.mem_cons_of_mem _ hy)
    refine ⟨a', b', h1, by rw [h2]; simp [List.prod_cons, mul_assoc], ?_⟩
    rw [h3]
    simp only [List.map_cons, List.sum_cons]
    field_simp
    ring

/-- **An accumulated fraction**: from nothing, over nonzero `d`'s, the product and the sum of the `x/d`. -/
theorem accFold_none (xs : List (F × F)) (h : xs ≠ []) (hd : ∀ xd ∈ xs, xd.2 ≠ 0) :
    ∃ a' b', xs.foldl accStep none = some (a', b') ∧ b' = (xs.map (·.2)).prod ∧
      a' = b' * (xs.map fun xd ↦ xd.1 / xd.2).sum := by
  cases xs with
  | nil => exact absurd rfl h
  | cons xd xs =>
    have hd0 : xd.2 ≠ 0 := hd xd List.mem_cons_self
    obtain ⟨a', b', h1, h2, h3⟩ := accFold_some xs xd.1 xd.2 hd0 fun y hy ↦ hd y (List.mem_cons_of_mem _ hy)
    exact ⟨a', b', h1, by rw [h2]; simp, by rw [h3]; simp [List.map_cons, List.sum_cons]⟩

/-- The pushes' terms `(N_g X_g, D_g)`. -/
def pushTerm (gs cells : List F) (v0 : F) (gf : GroupF F × (F × F)) : F × F :=
  (gf.2.1 * (gf.1.formula.eval gs (fun c ↦ cells.getD (c ^^^ gf.1.role) 0) + v0), gf.2.2)

/-- A one-pair group's fraction is `(1, d)` (`fraction_singleton`). -/
def SingleOne (L : List (GroupF F × (F × F))) : Prop := ∀ gf ∈ L, gf.1.pairs.length = 1 → gf.2.1 = 1

theorem pushStep_fst (gs cells : List F) (v0 : F) (ab s : Option (F × F)) (g : GroupF F) (nd : F × F)
    (h1 : g.pairs.length = 1 → nd.1 = 1) :
    (pushStep gs cells v0 (ab, s) (g, nd)).1 = accStep ab (pushTerm gs cells v0 (g, nd)) := by
  unfold pushStep accStep pushTerm
  by_cases hs : g.pairs.length = 1
  · have h := h1 hs
    cases ab <;> simp [hs, h]
  · cases ab <;> simp [hs]

theorem pushStep_snd (gs cells : List F) (v0 : F) (ab s : Option (F × F)) (g : GroupF F) (nd : F × F)
    (h1 : g.pairs.length = 1 → nd.1 = 1) :
    (pushStep gs cells v0 (ab, s) (g, nd)).2 = if g.pulls then s else accStep s nd := by
  unfold pushStep accStep
  by_cases hs : g.pairs.length = 1
  · have h := h1 hs
    cases s <;> by_cases hp : g.pulls <;> simp [hs, hp, h]
  · cases s <;> by_cases hp : g.pulls <;> simp [hs, hp]

theorem pushStep_fold (gs cells : List F) (v0 : F) :
    ∀ (L : List (GroupF F × (F × F))) (ab s : Option (F × F)), SingleOne L →
      L.foldl (pushStep gs cells v0) (ab, s) =
        ((L.map (pushTerm gs cells v0)).foldl accStep ab,
          ((L.filter fun gf ↦ !gf.1.pulls).map (·.2)).foldl accStep s)
  | [], ab, s, _ => rfl
  | (g, nd) :: L, ab, s, h => by
    have h1 : g.pairs.length = 1 → nd.1 = 1 := h (g, nd) List.mem_cons_self
    have hL : SingleOne L := fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    rw [List.foldl_cons]
    have e : pushStep gs cells v0 (ab, s) (g, nd) =
        ((pushStep gs cells v0 (ab, s) (g, nd)).1, (pushStep gs cells v0 (ab, s) (g, nd)).2) := rfl
    rw [e, pushStep_fold gs cells v0 L _ _ hL, pushStep_fst gs cells v0 ab s g nd h1,
      pushStep_snd gs cells v0 ab s g nd h1, List.map_cons, List.foldl_cons]
    by_cases hp : g.pulls
    · simp [hp]
    · simp [hp]

/-- **`pushSums`** is the two accumulated fractions: over every group, `(N_g X_g, D_g)`; over the pull-less ones,
`(N_g, D_g)`. -/
theorem pushSums_eq (S : CoreSpec F) (gs cells : List F) (v0 : F) (fracs : List (F × F))
    (h : SingleOne (S.groups.zip fracs)) :
    pushSums S gs cells v0 fracs =
      ((((S.groups.zip fracs).map (pushTerm gs cells v0)).foldl accStep none).map (·.1) |>.getD 0,
        (((S.groups.zip fracs).map (pushTerm gs cells v0)).foldl accStep none).map (·.2) |>.getD 1,
        ((((S.groups.zip fracs).filter fun gf ↦ !gf.1.pulls).map (·.2)).foldl accStep none).map (·.1) |>.getD 0,
        ((((S.groups.zip fracs).filter fun gf ↦ !gf.1.pulls).map (·.2)).foldl accStep none).map (·.2)
          |>.getD 1) := by
  unfold pushSums
  rw [pushStep_fold gs cells v0 _ none none h]

/-! ## The walk -/

theorem foldl_ite_add {α : Type} (P : α → Prop) [DecidablePred P] (g : α → F) :
    ∀ (L : List α) (init : F), L.foldl (fun acc b ↦ if P b then acc + g b else acc) init =
      init + (L.map fun b ↦ if P b then g b else 0).sum
  | [], init => by simp
  | b :: L, init => by
    rw [List.foldl_cons, foldl_ite_add P g L]
    by_cases hb : P b <;> simp [hb, add_assoc]

variable [CharP F 2]

/-- **`β ω_τ` along the walk**: from `β ω_{τ'}`, adding `β ω(2^b)` for the bits in which the tags differ gives `β ω_τ`
(`ω` additive in the bits, both tags below `2^28`). -/
theorem betaTagNext_eq (ω : ℕ → F) (hxor : ∀ a b, ω (a ^^^ b) = ω a + ω b)
    (hbits : ∀ d < 2 ^ 28, ω d = ((List.range 28).map fun b ↦ if d.testBit b then ω (2 ^ b) else 0).sum) (β : F)
    {lt tag : ℕ}
    (hlt : lt < 2 ^ 28) (htag : tag < 2 ^ 28) : betaTagNext ω β (some (lt, β * ω lt)) tag = β * ω tag := by
  dsimp only [betaTagNext]
  rw [foldl_ite_add (fun b ↦ (lt ^^^ tag).testBit b = true) (fun b ↦ β * ω (2 ^ b))]
  have hd : lt ^^^ tag < 2 ^ 28 := Nat.xor_lt_two_pow hlt htag
  have e : ((List.range 28).map fun b ↦ if (lt ^^^ tag).testBit b = true then β * ω (2 ^ b) else 0).sum =
      β * ω (lt ^^^ tag) := by
    rw [hbits _ hd, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun b _ ↦ ?_
    split_ifs <;> simp
  rw [e, hxor, mul_add, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The public term `j`'s denominator `α + F_j + β ω_τ`. -/
def termDen (S : CoreSpec F) (gs pubs : List F) (α β : F) (j : ℕ) : F :=
  let term := S.publicTerms.getD j (0, ⟨[], none⟩)
  α + term.2.eval gs (fun c ↦ pubs.getD c 0) + β * S.ω term.1

/-- **The walk's denominators** are the terms' `α + F_J + β ω_τ`, in the walk's order (tags below `2^28`). -/
theorem walkDens_eq (S : CoreSpec F) (gs pubs : List F) (α β : F) (hxor : ∀ a b, S.ω (a ^^^ b) = S.ω a + S.ω b)
    (hbits : ∀ d < 2 ^ 28, S.ω d = ((List.range 28).map fun b ↦ if d.testBit b then S.ω (2 ^ b) else 0).sum)
    (htags : ∀ j ∈ S.walk, (S.publicTerms.getD j (0, ⟨[], none⟩)).1 < 2 ^ 28) :
    walkDens S gs pubs α β = S.walk.map (termDen S gs pubs α β) := by
  let f := fun (acc : List F × Option (ℕ × F)) (j : ℕ) ↦
    let term := S.publicTerms.getD j (0, ⟨[], none⟩)
    let bt := betaTagNext S.ω β acc.2 term.1
    (acc.1 ++ [α + term.2.eval gs (fun c ↦ pubs.getD c 0) + bt], some (term.1, bt))
  have key : ∀ (L : List ℕ) (acc : List F) (last : Option (ℕ × F)),
      (last = none ∨ ∃ lt, last = some (lt, β * S.ω lt) ∧ lt < 2 ^ 28) →
      (∀ j ∈ L, (S.publicTerms.getD j (0, ⟨[], none⟩)).1 < 2 ^ 28) →
      (L.foldl f (acc, last)).1 = acc ++ L.map (termDen S gs pubs α β) := by
    intro L
    induction L with
    | nil => intro acc last _ _; simp
    | cons j L ih =>
      intro acc last hlast hL
      have hj := hL j List.mem_cons_self
      have hbt : betaTagNext S.ω β last (S.publicTerms.getD j (0, ⟨[], none⟩)).1 =
          β * S.ω (S.publicTerms.getD j (0, ⟨[], none⟩)).1 := by
        rcases hlast with rfl | ⟨lt, rfl, hlt⟩
        · rfl
        · exact betaTagNext_eq S.ω hxor hbits β hlt hj
      rw [List.foldl_cons]
      have e : f (acc, last) j = (acc ++ [termDen S gs pubs α β j],
          some ((S.publicTerms.getD j (0, ⟨[], none⟩)).1, β * S.ω (S.publicTerms.getD j (0, ⟨[], none⟩)).1)) := by
        dsimp only [f]
        rw [hbt]
        rfl
      rw [e, ih _ _ (Or.inr ⟨_, rfl, hj⟩) fun x hx ↦ hL x (List.mem_cons_of_mem _ hx)]
      simp
  show (S.walk.foldl f ([], none)).1 = _
  rw [key S.walk [] none (Or.inl rfl) htags, List.nil_append]

end RecStatement
