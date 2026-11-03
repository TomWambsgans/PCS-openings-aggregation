-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecPiop.Copy

/-!
# The ports' fingerprints bind the limbs

`PI2.md` §4.2: a three-limb port (an element, a zero check, a padding port) is
`L₀ + Y L₁ + Y² L₂` (`elemLimbs`), the element itself, with no `γ`; a four-limb port (the
statement, a root) is `(L₀ + Y L₁) + γ (L₂ + Y L₃)` (`rootLimbs`), a root's two 16-byte halves.
With the limbs in a subfield `K` over which `1, Y, Y²` are independent (`Indep`; `E = K[Y]` of
degree three), the first is injective (`fpList_elem_inj`: **no** `γ` is bad) and the second
agrees on different limbs at **at most one** `γ` (`card_fpList_root_eq_le`). At a port of a valid
circuit the push is the fingerprint of its limbs' values (`push_port`), so these give the
copy argument's binding hypothesis `hbind` with `d_j = 0` and `d_j = 1` (`bind_elem`,
`bind_root`).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-- **A three-limb port**: `1, Y, Y²`. -/
def elemLimbs (c₀ c₁ c₂ : ℕ) (Y : F) : List (Limb F) := [⟨c₀, [1]⟩, ⟨c₁, [Y]⟩, ⟨c₂, [Y ^ 2]⟩]

/-- **A four-limb port**: `1, Y, γ, γY`. -/
def rootLimbs (c₀ c₁ c₂ c₃ : ℕ) (Y : F) : List (Limb F) :=
  [⟨c₀, [1]⟩, ⟨c₁, [Y]⟩, ⟨c₂, [0, 1]⟩, ⟨c₃, [0, Y]⟩]

/-- **`1, Y, Y²` are independent over `K`.** -/
def Indep (K : Subfield F) (Y : F) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, a + Y * b + Y ^ 2 * c = 0 → a = 0 ∧ b = 0 ∧ c = 0

theorem fpList_elem (c₀ c₁ c₂ : ℕ) (Y γ v₀ v₁ v₂ : F) :
    fpList (elemLimbs c₀ c₁ c₂ Y) γ [v₀, v₁, v₂] = v₀ + Y * v₁ + Y ^ 2 * v₂ := by
  simp [fpList, elemLimbs, horner]
  ring

theorem fpList_root (c₀ c₁ c₂ c₃ : ℕ) (Y γ v₀ v₁ v₂ v₃ : F) :
    fpList (rootLimbs c₀ c₁ c₂ c₃ Y) γ [v₀, v₁, v₂, v₃] = (v₀ + Y * v₁) + γ * (v₂ + Y * v₃) := by
  simp [fpList, rootLimbs, horner]
  ring

theorem list_three {u : List F} (h : u.length = 3) : ∃ a b c, u = [a, b, c] := by
  match u, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

theorem list_four {u : List F} (h : u.length = 4) : ∃ a b c d, u = [a, b, c, d] := by
  match u, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- **A three-limb fingerprint is injective** on limbs in `K`. -/
theorem fpList_elem_inj {K : Subfield F} {Y : F} (hY : Indep K Y) (c₀ c₁ c₂ : ℕ) (γ : F)
    {u v : List F} (hu : u.length = 3) (hv : v.length = 3) (huK : ∀ x ∈ u, x ∈ K)
    (hvK : ∀ x ∈ v, x ∈ K)
    (h : fpList (elemLimbs c₀ c₁ c₂ Y) γ u = fpList (elemLimbs c₀ c₁ c₂ Y) γ v) : u = v := by
  obtain ⟨a, b, c, rfl⟩ := list_three hu
  obtain ⟨a', b', c', rfl⟩ := list_three hv
  rw [fpList_elem, fpList_elem] at h
  obtain ⟨h1, h2, h3⟩ := hY (a - a') (K.sub_mem (huK a (by simp)) (hvK a' (by simp)))
    (b - b') (K.sub_mem (huK b (by simp)) (hvK b' (by simp)))
    (c - c') (K.sub_mem (huK c (by simp)) (hvK c' (by simp))) (by linear_combination h)
  rw [sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3]

/-- **A four-limb fingerprint agrees on different limbs in `K` at at most one `γ`.** -/
theorem card_fpList_root_eq_le [Fintype F] {K : Subfield F} {Y : F}
    (hY : Indep K Y) (c₀ c₁ c₂ c₃ : ℕ) {u v : List F} (hu : u.length = 4) (hv : v.length = 4)
    (huK : ∀ x ∈ u, x ∈ K) (hvK : ∀ x ∈ v, x ∈ K) (hne : u ≠ v) :
    (univ.filter fun γ : F =>
      fpList (rootLimbs c₀ c₁ c₂ c₃ Y) γ u = fpList (rootLimbs c₀ c₁ c₂ c₃ Y) γ v).card ≤ 1 := by
  obtain ⟨a, b, c, d, rfl⟩ := list_four hu
  obtain ⟨a', b', c', d', rfl⟩ := list_four hv
  have mK : ∀ x y : F, x ∈ K → y ∈ K → x - y ∈ K := fun x y hx hy => K.sub_mem hx hy
  have ha := mK a a' (huK a (by simp)) (hvK a' (by simp))
  have hb := mK b b' (huK b (by simp)) (hvK b' (by simp))
  have hc := mK c c' (huK c (by simp)) (hvK c' (by simp))
  have hd := mK d d' (huK d (by simp)) (hvK d' (by simp))
  set e₀ := (a - a') + Y * (b - b')
  set e₁ := (c - c') + Y * (d - d')
  have he : ∀ γ : F, fpList (rootLimbs c₀ c₁ c₂ c₃ Y) γ [a, b, c, d] =
      fpList (rootLimbs c₀ c₁ c₂ c₃ Y) γ [a', b', c', d'] ↔ e₀ + γ * e₁ = 0 := by
    intro γ
    rw [fpList_root, fpList_root, ← sub_eq_zero]
    constructor <;> intro h <;> linear_combination h
  by_cases h1 : e₁ = 0
  · -- Then `e₀ ≠ 0`: no `γ` at all.
    obtain ⟨hc0, hd0, -⟩ := hY (c - c') hc (d - d') hd 0 K.zero_mem
      (by rw [mul_zero, add_zero]; exact h1)
    have h0 : e₀ ≠ 0 := by
      intro h0
      obtain ⟨ha0, hb0, -⟩ := hY (a - a') ha (b - b') hb 0 K.zero_mem
        (by rw [mul_zero, add_zero]; exact h0)
      apply hne
      rw [sub_eq_zero.mp ha0, sub_eq_zero.mp hb0, sub_eq_zero.mp hc0, sub_eq_zero.mp hd0]
    rw [Finset.filter_false_of_mem fun γ _ hγ => h0 (by rw [he, h1, mul_zero, add_zero] at hγ; exact hγ)]
    exact Nat.zero_le _
  · refine (Finset.card_le_card (t := {-e₀ / e₁}) fun γ hγ => ?_).trans (Finset.card_singleton _).le
    rw [Finset.mem_filter, he] at hγ
    rw [Finset.mem_singleton]
    field_simp
    linear_combination hγ.2

namespace Circuit

variable (G : Circuit F)

theorem fpEval_eq_fpList (ls : List (Limb F)) (γ : F) (cell : ℕ → F) :
    fpEval ls γ cell = fpList ls γ (ls.map fun l => cell l.cell) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [fpEval, fpList, List.map_cons, List.zip_cons_cons, List.sum_cons] at ih ⊢
    rw [ih]
    rfl

variable {G}

/-- **At a port, the push is its limbs' fingerprint** (no `κ` at a port). -/
theorem push_port (hV : G.Valid) {j : ℕ} (hj : j < G.nP) (w : ℕ → F) (γ : F) :
    G.push w γ (G.port j) = fpList (G.limbs j) γ (G.limbVals w j) := by
  have hpj := (G.port_lt hV hj)
  have hk : G.kappa (G.port j) = 0 := by
    by_contra hk
    have := hV.kappa_expr _ hpj.1 hk
    have hh := hpj.2
    unfold IsHole at hh
    cases hr : G.role (G.port j) <;> rw [hr] at this hh <;> simp [Role.isExpr, Role.isPort] at this hh
  unfold push limbVals limbs
  rw [hk, add_zero]
  have hh := hpj.2
  unfold IsHole at hh
  cases hr : G.role (G.port j) with
  | forward => rw [hr] at hh; simp [Role.isPort] at hh
  | expr p => rw [hr] at hh; simp [Role.isPort] at hh
  | port ls => exact fpEval_eq_fpList ls γ (fun c => w (G.base (G.port j) + c))

/-- **The binding hypothesis at a three-limb port** (`d_j = 0`): limbs in `K` (the witness's and
the public ones, three) with different values never have equal fingerprints. -/
theorem bind_elem [Fintype F] (hV : G.Valid) {K : Subfield F} {Y : F}
    (hY : Indep K Y) {j : ℕ} (hj : j < G.nP) {c₀ c₁ c₂ : ℕ}
    (hl : G.limbs j = elemLimbs c₀ c₁ c₂ Y) (w : ℕ → F) (pub : ℕ → List F)
    (hwK : ∀ x ∈ G.limbVals w j, x ∈ K) (hpK : ∀ x ∈ pub j, x ∈ K) (hpl : (pub j).length = 3)
    (hne : G.limbVals w j ≠ pub j) :
    (univ.filter fun γ : F => G.push w γ (G.port j) = G.pubFp γ pub j).card ≤ 0 := by
  have : (univ.filter fun γ : F => G.push w γ (G.port j) = G.pubFp γ pub j) = ∅ :=
    Finset.filter_false_of_mem fun γ _ h => hne (by
      rw [push_port hV hj, pubFp, hl] at h
      exact fpList_elem_inj hY c₀ c₁ c₂ γ (by rw [limbVals, List.length_map, hl]; rfl) hpl hwK hpK h)
  rw [this, Finset.card_empty]

/-- **The binding hypothesis at a four-limb port** (`d_j = 1`). -/
theorem bind_root [Fintype F] (hV : G.Valid) {K : Subfield F} {Y : F}
    (hY : Indep K Y) {j : ℕ} (hj : j < G.nP) {c₀ c₁ c₂ c₃ : ℕ}
    (hl : G.limbs j = rootLimbs c₀ c₁ c₂ c₃ Y) (w : ℕ → F) (pub : ℕ → List F)
    (hwK : ∀ x ∈ G.limbVals w j, x ∈ K) (hpK : ∀ x ∈ pub j, x ∈ K) (hpl : (pub j).length = 4)
    (hne : G.limbVals w j ≠ pub j) :
    (univ.filter fun γ : F => G.push w γ (G.port j) = G.pubFp γ pub j).card ≤ 1 := by
  have e : (univ.filter fun γ : F => G.push w γ (G.port j) = G.pubFp γ pub j) =
      univ.filter fun γ : F => fpList (rootLimbs c₀ c₁ c₂ c₃ Y) γ (G.limbVals w j) =
        fpList (rootLimbs c₀ c₁ c₂ c₃ Y) γ (pub j) := by
    ext γ
    rw [Finset.mem_filter, Finset.mem_filter, push_port hV hj, pubFp, hl]
  rw [e]
  refine card_fpList_root_eq_le hY c₀ c₁ c₂ c₃ ?_ hpl hwK hpK hne
  rw [limbVals, List.length_map, hl]
  rfl

end Circuit

end RecPiop
